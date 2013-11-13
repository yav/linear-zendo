{-# LANGUAGE RecordWildCards #-}
import Data.Integer.SAT
import Data.Maybe(fromMaybe)
import Control.Monad(guard)
import qualified Data.Map as Map
import Data.Map(Map)

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
  { serverModel   :: Maybe Model
  , serverPlayers :: Players
  , serverBoard   :: Board
  } deriving Show

newServerState :: ServerState
newServerState = ServerState { serverBoard   = newBoard
                             , serverPlayers = newPlayers
                             , serverModel   = Nothing
                             }

newGame :: Model -> ServerState -> Maybe ServerState
newGame m@Model { .. } ServerState { .. } =
  do good <- getVal trueProp
     bad  <- getVal (Not trueProp)
     return ServerState
              { serverModel   = Just m
              , serverBoard   = newBoard { boardKnownGood = [good]
                                         , boardKnownBad = [bad] }
              , serverPlayers = updatePlayers (\_ -> resetPlayer) serverPlayers
              }

addExample :: Value -> ServerState -> Maybe (Bool, ServerState)
addExample v ServerState { .. } =
  do m <- serverModel
     let isOK         = check m v
         Board { .. } = serverBoard
         serverBoard'
           | isOK      = Board { boardKnownGood = v : boardKnownGood, .. }
           | otherwise = Board { boardKnownBad  = v : boardKnownBad, .. }
     guard $ not $ knownValue v serverBoard
     return (isOK, ServerState { serverBoard = serverBoard', .. })

playerAsk :: Value -> ServerState -> Maybe ServerState
playerAsk v s = do (_,s') <- addExample v s
                   return s'

playerGuess :: Value -> [(PlayerId,Bool)] -> ServerState -> Maybe ServerState
playerGuess v guesses s =
  do (isOK, ServerState { .. }) <- addExample v s
     let checkGuess i p = case lookup i guesses of
                            Just ans | ans == isOK -> addGuessPoint p
                            _                      -> p
         players' = updatePlayers checkGuess serverPlayers
     return ServerState { serverPlayers = players', .. }


playerGuessRule :: PlayerId -> Prop -> ServerState -> Maybe ServerState
playerGuessRule who p ServerState { .. } =
  do m <- serverModel
     guessedPlayer <- playerCanGuess =<< getPlayer who serverPlayers
     guard $ isNewProp p serverBoard
     let serverBoard' = addTheory p (checkRule m p) serverBoard
     return $
       if boardFinished serverBoard'
          then ServerState
                 { serverBoard    = serverBoard'
                 , serverModel    = Nothing
                 , serverPlayers  = setPlayer who (addWin guessedPlayer)
                                                              serverPlayers }
          else ServerState
                 { serverBoard    = serverBoard'
                 , serverPlayers  = setPlayer who guessedPlayer serverPlayers
                 , ..
                 }





--------------------------------------------------------------------------------

data Players = Players
  { playersMap    :: Map PlayerId Player
  , playersNextId :: Integer
  } deriving Show

newPlayers :: Players
newPlayers = Players { playersMap = Map.empty, playersNextId = 0 }

addPlayer :: Players -> (PlayerId, Players)
addPlayer Players { .. } =
  (newId, Players { playersMap    = Map.insert newId newPlayer playersMap
                  , playersNextId = 1 + playersNextId })
  where
  newId = PlayerId playersNextId

dropPlayer :: PlayerId -> Players -> Players
dropPlayer i Players { .. } =
             Players { playersMap = Map.delete i playersMap, .. }

getPlayer :: PlayerId -> Players -> Maybe Player
getPlayer i Players { .. } = Map.lookup i playersMap

setPlayer :: PlayerId -> Player -> Players -> Players
setPlayer i p Players { .. } =
              Players { playersMap = Map.adjust (\_ -> p) i playersMap, .. }

updatePlayers :: (PlayerId -> Player -> Player) -> Players -> Players
updatePlayers f Players { .. } =
                Players { playersMap = Map.mapWithKey f playersMap, ..  }


--------------------------------------------------------------------------------
newtype PlayerId = PlayerId Integer
                    deriving (Show,Eq,Ord)

data Player = Player
  { playerGuessScore :: Integer
  , playerWins       :: Integer
  } deriving Show

newPlayer :: Player
newPlayer = Player { playerGuessScore = 0, playerWins = 0 }

addGuessPoint :: Player -> Player
addGuessPoint Player { .. } = Player { playerGuessScore = playerGuessScore + 1
                                     , .. }
addWin :: Player -> Player
addWin Player { .. } = Player { playerWins = playerWins + 1, .. }

playerCanGuess :: Player -> Maybe Player
playerCanGuess Player { .. } =
  do guard (playerGuessScore > 0)
     return Player { playerGuessScore = playerGuessScore - 1, .. }

resetPlayer :: Player -> Player
resetPlayer Player { .. } =
            Player { playerGuessScore = 0, .. }


--------------------------------------------------------------------------------

data Board = Board
  { boardKnownGood  :: [Value]
  , boardKnownBad   :: [Value]
  , boardTheories   :: [ (Prop, Answer) ]
  } deriving Show

newBoard :: Board
newBoard = Board
  { boardKnownGood = []
  , boardKnownBad  = []
  , boardTheories  = []
  }

boardFinished :: Board -> Bool
boardFinished Board { .. } =
  case boardTheories of
    (_,OK) : _ -> True
    _          -> False

addTheory :: Prop -> Answer -> Board -> Board
addTheory p a Board { .. } =
  Board { boardTheories  = (p,a) : boardTheories
        , boardKnownGood = newGood ++ boardKnownGood
        , boardKnownBad  = newBad  ++ boardKnownBad
        }
  where (newGood, newBad) = case a of
                              AcceptedInvalid v -> ([],[v])
                              RejectedValid   v -> ([v],[])
                              OK                -> ([],[])

knownValue :: Value -> Board -> Bool
knownValue v Board { .. } = v `elem` boardKnownGood || v `elem` boardKnownBad

isNewProp :: Prop -> Board -> Bool
isNewProp p Board { .. } = all (accepts p) boardKnownGood &&
                           all (not . accepts p) boardKnownBad




