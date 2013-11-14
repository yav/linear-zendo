module Prop where

import Protocol(Value(..))
import Data.Integer.SAT
import Data.Maybe(fromMaybe)

getVal :: Prop -> Maybe Value
getVal p = do sat <- checkSat (assert p noProps)
              return $ V $ fromMaybe 0 $ lookup 0 sat

accepts :: Prop -> Value -> Bool
accepts p (V x) =
  case checkSat $ assert p $ assert (Var (toName 0) :== K x) noProps of
    Just _  -> True
    Nothing -> False

-- Returns `Nothing` if the answer depends on other variables than the input
acceptsMaybe :: Prop -> Value -> Maybe Bool
acceptsMaybe p (V x) =
  let letX = assert (Var (toName 0) :== K x) noProps
  in case checkSat (assert p letX) of
       Nothing -> Just False
       Just _  ->
         case checkSat (assert (Not p) letX) of
           Nothing -> Just True
           Just _  -> Nothing


