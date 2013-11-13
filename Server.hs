{-# LANGUAGE RecordWildCards #-}
import Data.Integer.SAT
import Data.Maybe(fromMaybe)
import Control.Monad(guard)
import System.IO(hFlush,stdout)
import Text.Read(readMaybe)
import Text.Show.Pretty(ppShow)


data Model = Model
  { trueProp  :: Prop
  }

check :: Model -> Value -> Bool
check Model { .. } (V x) =
  case checkSat $ assert (Var (toName 0) :== K x) $ assert trueProp noProps of
    Just _  -> True
    Nothing -> False

checkRule :: Model -> Prop -> Answer
checkRule Model { .. } p =
  case checkSat $ assert trueProp $ assert (Not p) noProps of
    Just sat -> RejectedValid $ V $ fromMaybe 0 $ lookup 0 sat
    Nothing  ->
      case checkSat $ assert (Not trueProp) $ assert p noProps of
        Just sat -> AcceptedInvalid $ V $ fromMaybe 0 $ lookup 0 sat
        Nothing  -> OK


instance Show Model where
  show _ = "Model"

data Answer = OK
            | RejectedValid Value
            | AcceptedInvalid Value
              deriving Show

data Value  = V Integer
              deriving Show

--------------------------------------------------------------------------------

data ServerState = ServerState
  { serverModel   :: Model
  , serverPlayers :: Players
  , serverBoard   :: Board
  } deriving Show


newServerState :: Model -> Value -> Value -> Maybe ServerState
newServerState serverModel goodExample badExample =
  do guard (check serverModel goodExample)
     guard (not (check serverModel badExample))
     let (_,serverPlayers) = newPlayers
     return ServerState { serverBoard = newBoard goodExample badExample, .. }

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
  where p = newPlayer 0

addPlayer :: Players -> (Player, Players)
addPlayer Players { .. } = (p, Players { playersPrev   = p : playersPrev
                                       , playersNextId = 1 + playersNextId
                                       , .. })
  where
  p = newPlayer playersNextId

dropPlayer :: Integer -> Players -> Maybe Players
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
data Player = Player
  { playerId         :: Integer
  , playerGuessScore :: Integer
  , playerWins       :: Integer
  } deriving Show

newPlayer :: Integer -> Player
newPlayer playerId = Player { playerGuessScore = 0, playerWins = 0, .. }

addGuessPoint :: Player -> Player
addGuessPoint Player { .. } = Player { playerGuessScore = playerGuessScore + 1
                                     , .. }
addWin :: Player -> Player
addWin Player { .. } = Player { playerWins = playerWins + 1, .. }


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

addExample :: Value -> ServerState -> (Bool, ServerState)
addExample v ServerState { .. } =
  (isOK, ServerState { serverBoard = serverBoard', .. })
  where
  isOK         = check serverModel v
  Board { .. } = serverBoard
  serverBoard'
    | isOK      = Board { boardKnownGood = v : boardKnownGood, .. }
    | otherwise = Board { boardKnownBad  = v : boardKnownBad, .. }

addTheory :: Prop -> Answer -> Board -> Maybe Board
addTheory p OK _ = Nothing
addTheory p a Board { .. } = Just
  Board { boardTheories  = (p,a) : boardTheories
        , boardKnownGood = newGood ++ boardKnownGood
        , boardKnownBad  = newBad  ++ boardKnownBad
        }
  where (newGood, newBad) = case a of
                              AcceptedInvalid v -> ([],[v])
                              RejectedValid   v -> ([v],[])
                              OK -> error "Can't happen"

nextTurn :: ServerState -> ServerState
nextTurn ServerState { .. } =
         ServerState { serverPlayers = nextPlayer serverPlayers, .. }



playerAsk :: Value -> ServerState -> ServerState
playerAsk v = nextTurn . snd . addExample v

playerGuess :: Value -> [(Integer,Bool)] -> ServerState -> ServerState
playerGuess v guesses s =
  nextTurn
    ServerState { serverPlayers = updatePlayers checkGuess serverPlayers
                , .. }
  where
  (isOK, ServerState { .. }) = addExample v s

  checkGuess p = case lookup (playerId p) guesses of
                   Just ans | ans == isOK -> addGuessPoint p
                   _                      -> p


playerGuessRule :: Prop -> ServerState -> Maybe ServerState
playerGuessRule p ServerState { .. } =
  do serverBoard' <- addTheory p (checkRule serverModel p) serverBoard
     return $ nextTurn $ ServerState { serverBoard = serverBoard', .. }




--------------------------------------------------------------------------------

example = go initSt
  where
  good  = V 0
  bad   = V (-100)
  model = Model { trueProp = Mod (Var (toName 0)) 7 :== K 0 }

  Just initSt = newServerState model good bad

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



