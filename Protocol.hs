module Protocol where

import Data.Integer.SAT(Prop)
import Data.Binary

newtype Value  = V Integer
              deriving (Show,Read,Eq)

data Board = Board
  { boardKnownGood  :: [Value]
  , boardKnownBad   :: [Value]
  , boardTheories   :: [ (Prop, Answer) ]
  } deriving (Read,Show)

data Answer = OK
            | RejectedValid Value
            | AcceptedInvalid Value
              deriving (Read,Show)

--------------------------------------------------------------------------------


data ClientReq
  = MoveAsk   Value             -- ^ Player move: ask if satisfies
  | MoveGuess Value             -- ^ Player move: start a guessing round
  | MoveProp  Prop              -- ^ Player move: try to guess the rule

  | SubmitGuess Bool            -- ^ Response to guessing round

  | NewGame Prop                -- ^ Start a new gameusing this porperty
  deriving (Read,Show)


data ServerResp
  = Update Board                -- ^ Current state of the board
  | NeedGuess Value             -- ^ Ask the client to submit a guess
  | GuessTimeRemaining Float    -- ^ This much time remains ot guess
  | GuessingDone                -- ^ Guessing round ended
  | EndGame Bool Integer        -- ^ Game ended, bool is if you won, curr. score
  | InvalidRequest              -- ^ The client request was not OK
    deriving (Read,Show)


instance Binary ClientReq where
  put = put . show
  get = fmap read get

instance Binary ServerResp where
  put = put . show
  get = fmap read get




