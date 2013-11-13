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
  { serverModel   :: Model
  , serverPlayers :: Players
  , serverBoard   :: Board
  } deriving Show


newServerState :: Model -> Maybe ServerState
newServerState serverModel@Model { .. } =
  do good <- getVal trueProp
     bad  <- getVal (Not trueProp)
     return ServerState { serverBoard = newBoard good bad
                        , serverPlayers = newPlayers, .. }

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
  do guessedPlayer <- playerCanGuess =<< getPlayer who serverPlayers
     let serverPlayers' = setPlayer who guessedPlayer serverPlayers
     guard $ isNewProp p serverBoard
     serverBoard' <- addTheory p (checkRule serverModel p) serverBoard
     return ServerState { serverBoard = serverBoard'
                        , serverPlayers = serverPlayers', .. }






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




