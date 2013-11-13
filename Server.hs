{-# LANGUAGE RecordWildCards #-}
import Protocol
import Data.Integer.SAT
import Data.List(delete)
import Data.Maybe(fromMaybe)
import Control.Monad(guard,when,forM_)
import qualified Data.Map as Map
import Data.Map(Map)
import NetworkedGame.Server
import Network(PortID)

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


getPlayers :: ServerState -> [(ConnectionId,Player)]
getPlayers ServerState { .. } = Map.toList (playersMap serverPlayers)

playerIds :: ServerState -> [ConnectionId]
playerIds = map fst . getPlayers



playerAsk :: Value -> ServerState -> Maybe ServerState
playerAsk v s = do (_,s') <- addExample v s
                   return s'

playerGuess :: Value -> [(ConnectionId,Bool)] -> ServerState -> Maybe ServerState
playerGuess v guesses s =
  do (isOK, ServerState { .. }) <- addExample v s
     let checkGuess i p = case lookup i guesses of
                            Just ans | ans == isOK -> addGuessPoint p
                            _                      -> p
         players' = updatePlayers checkGuess serverPlayers
     return ServerState { serverPlayers = players', .. }


playerGuessRule :: ConnectionId -> Prop -> ServerState -> Maybe ServerState
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

newtype Players = Players { playersMap :: Map ConnectionId Player }
                  deriving Show

newPlayers :: Players
newPlayers = Players { playersMap = Map.empty }

addPlayer :: ConnectionId -> Players -> Players
addPlayer newId Players { .. } =
                Players { playersMap = Map.insert newId newPlayer playersMap }

dropPlayer :: ConnectionId -> Players -> Players
dropPlayer i Players { .. } =
             Players { playersMap = Map.delete i playersMap, .. }

getPlayer :: ConnectionId -> Players -> Maybe Player
getPlayer i Players { .. } = Map.lookup i playersMap

setPlayer :: ConnectionId -> Player -> Players -> Players
setPlayer i p Players { .. } =
              Players { playersMap = Map.adjust (\_ -> p) i playersMap, .. }

updatePlayers :: (ConnectionId -> Player -> Player) -> Players -> Players
updatePlayers f Players { .. } =
                Players { playersMap = Map.mapWithKey f playersMap, ..  }


--------------------------------------------------------------------------------
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



--------------------------------------------------------------------------------
data ServerStatus
  = Ready
  | GuessRound Float Value [ConnectionId] (Map ConnectionId Bool)




netServer :: PortID -> IO ()
netServer serverPort = serverMain NetworkServer { .. } (Ready, newServerState)
  where
  eventsPerSecond = 1

  onTick _ _ w@(Ready, _) = return w
  onTick hs elapsed (GuessRound remaining val todo done, s)
    | elapsed < remaining =
        do let newTime = remaining - elapsed
           announce hs (GuessTimeRemaining newTime)
           return (GuessRound newTime val todo done, s)
    | otherwise = doGuess hs val done s

  onConnect hs c (r,ServerState { .. }) =
    do announceOne hs c (Update serverBoard)
       return (r, ServerState { serverPlayers = addPlayer c serverPlayers, .. })

  onDisconnect _ c (r,ServerState { .. }) =
      return (r,ServerState { serverPlayers = dropPlayer c serverPlayers, .. })

  onCommand hs c cmd w@(Ready,s) =
    case cmd of

      MoveAsk v ->
        case playerAsk v s of
          Nothing -> announceOne hs c InvalidRequest >> return w
          Just w1 -> announce hs (Update (serverBoard w1)) >> return (Ready,w1)

      MoveGuess v ->
        do announce hs (NeedGuess v)
           let guessTime = 10 -- seconds
           announce hs (GuessTimeRemaining guessTime)
           return (GuessRound guessTime v (playerIds s) Map.empty, s)

      MoveProp p ->
        case playerGuessRule c p s of
          Nothing -> do announceOne hs c InvalidRequest
                        return w
          Just s1 ->
            do when (boardFinished (serverBoard s1)) $
                 forM_ (getPlayers s1) $ \(c1,p) ->
                   announceOne hs c1 $ EndGame (c == c1) $ playerWins p

               return (Ready, s1)

      SubmitGuess {} -> do announceOne hs c InvalidRequest
                           return w

      NewGame p ->
        case newGame (Model p) s of
          Just s1 -> do announce hs (Update $ serverBoard s1)
                        return (Ready, s1)
          Nothing -> do announceOne hs c InvalidRequest
                        return w


  onCommand hs c cmd w@(GuessRound t v todo done,s) =

    case cmd of
      SubmitGuess b ->
        let done' = Map.insert c b done
        in case delete c todo of
             []    -> doGuess hs v done' s
             todo' -> return (GuessRound t v todo' done', s)

      _ -> do announceOne hs c InvalidRequest
              return w


  doGuess hs val done s =
    do s1 <- case playerGuess val (Map.toList done) s of
               Just s1 -> do announce hs (Update (serverBoard s1))
                             return s1
               Nothing -> return s
       forM_ (getPlayers s1) $ \(c1,p) ->
          announceOne hs c1 $ GuessingDone $ playerGuessScore p
       return (Ready, s1)


