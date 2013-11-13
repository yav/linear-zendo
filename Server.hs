{-# LANGUAGE RecordWildCards #-}
import Data.Integer.SAT
import Data.Maybe(fromMaybe)
import Control.Monad(guard)
import System.IO(hFlush,stdout)
import Text.Read(readMaybe)
import Text.Show.Pretty(ppShow)

getVal :: Prop -> Maybe Value
getVal p = do sat <- checkSat (assert p noProps)
              return $ V $ fromMaybe 0 $ lookup 0 sat

accepts :: Prop -> Value -> Bool
accepts p (V x) =
  case checkSat $ assert p $ assert (Var (toName 0) :== K x) noProps of
    Just _  -> True
    Nothing -> False

--------------------------------------------------------------------------------

newtype Model = Model { trueProp  :: Prop }

check :: Model -> Value -> Bool
check Model { .. } x = accepts trueProp x

checkRule :: Model -> Prop -> Answer
checkRule Model { .. } p =
  case getVal (trueProp :&& Not p) of
    Just v -> RejectedValid v
    Nothing  ->
      case getVal (Not trueProp :&& p) of
        Just v   -> AcceptedInvalid v
        Nothing  -> OK



instance Show Model where
  show _ = "Model"

data Answer = OK
            | RejectedValid Value
            | AcceptedInvalid Value
              deriving Show

newtype Value  = V Integer
              deriving (Show,Eq)

--------------------------------------------------------------------------------

data ServerState = ServerState
  { serverModel   :: Model
  , serverPlayers :: Players
  , serverBoard   :: Board
  } deriving Show


newServerState :: Model -> Maybe ServerState
newServerState serverModel@Model { .. } =
  do good <- getVal trueProp
     bad  <- getVal (Not trueProp)
     let (_,serverPlayers) = newPlayers
     return ServerState { serverBoard = newBoard good bad, .. }

nextTurn :: ServerState -> ServerState
nextTurn ServerState { .. } =
         ServerState { serverPlayers = nextPlayer serverPlayers, .. }

addExample :: Value -> ServerState -> Maybe (Bool, ServerState)
addExample v ServerState { .. } =
  do guard $ not $ knownValue v serverBoard
     return (isOK, ServerState { serverBoard = serverBoard', .. })
  where
  isOK         = check serverModel v
  Board { .. } = serverBoard
  serverBoard'
    | isOK      = Board { boardKnownGood = v : boardKnownGood, .. }
    | otherwise = Board { boardKnownBad  = v : boardKnownBad, .. }


playerAsk :: Value -> ServerState -> Maybe ServerState
playerAsk v s = do (_,s') <- addExample v s
                   return $ nextTurn s'

playerGuess :: Value -> [(PlayerId,Bool)] -> ServerState -> Maybe ServerState
playerGuess v guesses s =
  do (isOK, ServerState { .. }) <- addExample v s
     let checkGuess p = case lookup (playerId p) guesses of
                          Just ans | ans == isOK -> addGuessPoint p
                          _                      -> p
     let players' = updatePlayers checkGuess serverPlayers
     return $ nextTurn ServerState { serverPlayers = players', .. }


playerGuessRule :: Prop -> ServerState -> Maybe ServerState
playerGuessRule p ServerState { .. } =
  do let Players { .. } = serverPlayers
     guessedPlayer <- playerCanGuess playersCur
     guard $ isNewProp p serverBoard
     let serverPlayers' = Players { playersCur = guessedPlayer, .. }
     serverBoard' <- addTheory p (checkRule serverModel p) serverBoard
     return $ nextTurn $ ServerState { serverBoard = serverBoard'
                                     , serverPlayers = serverPlayers'
                                     , .. }






--------------------------------------------------------------------------------

data Players = Players
  { playersPrev   :: [Player]
  , playersCur    :: Player
  , playersNext   :: [Player]
  , playersNextId :: Integer
  } deriving Show

newPlayers :: (Player, Players)
newPlayers = (p, Players { playersPrev   = []
                         , playersCur    = p
                         , playersNext   = []
                         , playersNextId = 1
                         })
  where p = newPlayer (PlayerId 0)

addPlayer :: Players -> (Player, Players)
addPlayer Players { .. } = (p, Players { playersPrev   = p : playersPrev
                                       , playersNextId = 1 + playersNextId
                                       , .. })
  where
  p = newPlayer (PlayerId playersNextId)

dropPlayer :: PlayerId -> Players -> Maybe Players
dropPlayer i Players { .. }
  | playerId playersCur == i
    = case playersNext of
        p : ps -> Just Players { playersCur = p, playersNext = ps, .. }
        [] -> case reverse playersPrev of
                p : ps -> Just Players { playersCur = p, playersNext = ps
                                       , playersPrev = [], .. }
                [] -> Nothing
  | otherwise = Just $ case dropFromList playersPrev of
                         Just ps -> Players { playersPrev = ps, .. }
                         Nothing ->
                           case dropFromList playersNext of
                             Just ps -> Players { playersNext = ps, .. }
                             Nothing -> Players { .. }

  where
  dropFromList [] = Nothing
  dropFromList (Player { .. } : ps)
    | playerId == i = Just ps
    | otherwise     = fmap (Player { .. } :) (dropFromList ps)


nextPlayer :: Players -> Players
nextPlayer Players { .. } =
  case playersNext of
    p : ps -> Players { playersPrev = playersCur : playersPrev
                      , playersCur  = p
                      , playersNext = ps
                      , ..
                      }
    [] -> case reverse playersPrev of
            p : ps -> Players { playersPrev = []
                              , playersCur  = p
                              , playersNext = ps
                              , ..
                              }
            []     -> Players { .. }

updatePlayers :: (Player -> Player) -> Players -> Players
updatePlayers f Players { .. } = Players { playersPrev = map f playersPrev
                                         , playersCur  = f playersCur
                                         , playersNext = map f playersNext
                                         , ..
                                         }


--------------------------------------------------------------------------------
newtype PlayerId = PlayerId Integer
                    deriving (Show,Eq)

data Player = Player
  { playerId         :: PlayerId
  , playerGuessScore :: Integer
  , playerWins       :: Integer
  } deriving Show

newPlayer :: PlayerId -> Player
newPlayer playerId = Player { playerGuessScore = 0, playerWins = 0, .. }

addGuessPoint :: Player -> Player
addGuessPoint Player { .. } = Player { playerGuessScore = playerGuessScore + 1
                                     , .. }
addWin :: Player -> Player
addWin Player { .. } = Player { playerWins = playerWins + 1, .. }

playerCanGuess :: Player -> Maybe Player
playerCanGuess Player { .. } =
  do guard (playerGuessScore > 0)
     return Player { playerGuessScore = playerGuessScore - 1, .. }


--------------------------------------------------------------------------------

data Board = Board
  { boardKnownGood  :: [Value]
  , boardKnownBad   :: [Value]
  , boardTheories   :: [ (Prop, Answer) ]
  } deriving Show

newBoard :: Value -> Value -> Board
newBoard good bad = Board
  { boardKnownGood = [good]
  , boardKnownBad  = [bad]
  , boardTheories  = []
  }

addTheory :: Prop -> Answer -> Board -> Maybe Board
addTheory _ OK _ = Nothing
addTheory p a Board { .. } = Just
  Board { boardTheories  = (p,a) : boardTheories
        , boardKnownGood = newGood ++ boardKnownGood
        , boardKnownBad  = newBad  ++ boardKnownBad
        }
  where (newGood, newBad) = case a of
                              AcceptedInvalid v -> ([],[v])
                              RejectedValid   v -> ([v],[])
                              OK -> error "Can't happen"

knownValue :: Value -> Board -> Bool
knownValue v Board { .. } = v `elem` boardKnownGood || v `elem` boardKnownBad

isNewProp :: Prop -> Board -> Bool
isNewProp p Board { .. } = all (accepts p) boardKnownGood &&
                           all (not . accepts p) boardKnownBad




--------------------------------------------------------------------------------

example :: IO ()
example = go initSt
  where
  model = Model { trueProp = Mod (Var (toName 0)) 7 :== K 0 }

  Just initSt = newServerState model

  go st = do putStrLn $ ppShow st
             putStr "> "
             hFlush stdout
             xs <- getLine
             case readMaybe xs of
               Nothing -> putStrLn "Bad input" >> go st
               Just n  -> 
                case playerGuessRule n st of
                  Just st1 -> go st1
                  Nothing  -> putStrLn "You win"



