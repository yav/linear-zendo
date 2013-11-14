{-# LANGUAGE PatternGuards #-}
module Main where


import Data.List
import Data.Char (isDigit, isSymbol)

import Graphics.Vty
import Control.Exception
import Control.Lens
import Control.Concurrent

import Data.Integer.SAT
import Data.Tree
import Control.Monad.State
import Data.Maybe
import Text.Read (readMaybe)

import Protocol
import NetworkedGame.Packet
import Network (connectTo, PortID(..))
import System.IO
import System.Environment

data Language = Language String [Constructor]

data Constructor
  = Integer
  | Constructor String [Language]

propLanguage = Language "prop"
                        [ Constructor "true" []
                        , Constructor "false" []
                        , Constructor "not" [propLanguage]
                        , Constructor "||"  [propLanguage,propLanguage]
                        , Constructor "&&"  [propLanguage,propLanguage]
                        , Constructor "=="  [exprLanguage,exprLanguage]
                        , Constructor "/="  [exprLanguage,exprLanguage]
                        , Constructor "<="  [exprLanguage,exprLanguage]
                        , Constructor ">="  [exprLanguage,exprLanguage]
                        , Constructor "<"   [exprLanguage,exprLanguage]
                        , Constructor ">"   [exprLanguage,exprLanguage]
                        ]

exprLanguage = Language "expr"
                        [ Integer
                        , Constructor "+" [exprLanguage,exprLanguage]
                        , Constructor "-" [exprLanguage,exprLanguage]
                        , Constructor "*" [integerLanguage,exprLanguage]
                        , Constructor "negate" [exprLanguage]
                        , Constructor "x" []
                        , Constructor "if" [propLanguage, exprLanguage, exprLanguage]
                        , Constructor "/" [exprLanguage, integerLanguage]
                        , Constructor "%" [exprLanguage, integerLanguage]
                        ]

integerLanguage = Language "integer" [ Integer ]

matchLanguage :: [(Int,Language)] -> [String] -> [(Int, Bool, String, String)]
matchLanguage [] xs = [(0, False, "error", x) | x <- xs]
matchLanguage ((depth,Language langName _):ls) [] = (depth, False, langName, "") : matchLanguage ls []
matchLanguage ((depth,l@(Language langName _)):ls) (x:xs) =
  case matchConstructor l x of
    Nothing -> (depth, False, langName, x) : matchLanguage ls xs
    Just subl -> (depth, True, langName, x) : matchLanguage ([(depth+1, x) | x <- subl] ++ ls) xs

matchConstructor (Language _ cs) x = case find match1 cs of
                                     Just (Constructor _ xs) -> Just xs
                                     Just Integer            -> Just []
                                     Nothing                 -> Nothing
  where
  match1 Integer = all isDigit x
  match1 (Constructor n _) = n == x

driver xs = unlines [mark m ++ indent n x | (n,m,l,x) <- matchLanguage [(0,propLanguage)] xs]
  where
  mark True = "  "
  mark False = "x "


indent n x = replicate (4*n) ' ' ++ x

data GameEvent = ServerEvent ServerResp | Event Event
data GameState = GameState
  { gameVty :: Vty
  , gameHandle :: Handle
  , gameEvents :: Chan GameEvent
  , gameBoard :: Board
  , gameQuestion :: Maybe Value
  , selectedLine :: Int
  , numberLine :: String
  , propLines :: [String]
  , guessScore :: Integer
  , gameMessage :: String
  }

processArgs = do
  args <- getArgs
  case args of
    [h] -> return h
    _   -> fail "Please specify hostname on command line"

main = do
  host <- processArgs
  events <- newChan
  let board = Board [] [] []
  h <- connectTo host (PortNumber 16000)
  bracket mkVty shutdown $ \vty ->
    do inputThread <- forkIO (forever (writeChan events . Event =<< next_event vty))
       serverThread <- forkIO (forever (writeChan events . ServerEvent =<< hGetPacketed h))
       inputLoop (GameState vty h events board Nothing 0 "" [""] 0 "")
         `finally` (killThread inputThread >>
                    killThread serverThread)

cleanTrailing selected xs = a ++ dropWhileEnd isJunk b
  where
  (a,b) = splitAt (selected+1) xs

  isJunk (_,_,"error","") = True
  isJunk _ = False

say h x = hPutPacket h (mkPacket x)

inputLoop :: GameState -> IO ()
inputLoop g = do
  let parsedXs = cleanTrailing (selectedLine g) (matchLanguage [(0,propLanguage)] (propLines g))
  let xs' = map (view _4) parsedXs -- insert empty end-lines
  update (gameVty g) (pic_for_image $
              messageImage (gameMessage g)
          <-> pointsImage (guessScore g)
          <-> boardImage (gameBoard g)
          <-> string def_attr " "
          <-> questionImage (gameQuestion g)
          <-> string def_attr " "
          <-> guessImage (selectedLine g) (numberLine g)
          <-> string def_attr " "
          <-> inputImage (selectedLine g) parsedXs)
  ev <- readChan (gameEvents g)
  case ev of
    Event (EvKey KEsc _) -> return ()

    Event (EvKey (KASCII 'p') [MCtrl])
      | Just p <- runParse xs' ->
      do say (gameHandle g) (MoveProp p)
         inputLoop g { propLines = xs' }

    Event (EvKey (KASCII 'h') [MCtrl])
      | Just p <- runParse xs' ->
      do say (gameHandle g) (NewGame p)
         inputLoop g { propLines = xs' }

    Event (EvKey (KASCII 'a') [MCtrl])
      | Just v <- readMaybe (numberLine g) ->
      do say (gameHandle g) (MoveAsk (V v))
         inputLoop g { propLines = xs', numberLine = "" }

    Event (EvKey (KASCII 'g') [MCtrl])
      | Just v <- readMaybe (numberLine g) ->
      do say (gameHandle g) (MoveGuess (V v))
         inputLoop g { propLines = xs', numberLine = "" }

    Event (EvKey (KASCII 'y') [MCtrl]) ->
      do say (gameHandle g) (SubmitGuess True)
         inputLoop g { propLines = xs' }

    Event (EvKey (KASCII 'n') [MCtrl]) ->
      do say (gameHandle g) (SubmitGuess False)
         inputLoop g { propLines = xs' }

    Event (EvKey k _) ->
      do let (selected',num', xs'') = handleKeyPress k (selectedLine g) (numberLine g) xs'
         inputLoop g { selectedLine = selected', numberLine = num', propLines = xs'' }

    ServerEvent (Update b score) ->
      do inputLoop g { propLines = xs', gameBoard = b, guessScore = score }

    ServerEvent (NeedGuess v) ->
      do inputLoop g { propLines = xs', gameQuestion = Just v }

    ServerEvent GuessingDone ->
      do inputLoop g { propLines = xs', gameQuestion = Nothing, gameMessage = "Guessing over" }

    ServerEvent other ->
      do inputLoop g { propLines = xs', gameMessage = show other }

    _ ->
      do inputLoop g { propLines = xs' }

handleKeyPress (KASCII '\t') i num xs
  | i+1 < length xs = (i+1,num,xs)
  | otherwise = (i,num,xs)
handleKeyPress KBS (-1) "" xs = (-1, "", xs)
handleKeyPress KBS (-1) num xs = (-1, init num, xs)

handleKeyPress (KASCII c) (-1) num xs = (-1,num++[c],xs)

handleKeyPress KBS i num xs
  | i == 0 && null (head xs) = (i,num,xs)
  | i >= 0 && null (xs !! i) = (i-1, num, let (a,b) = splitAt i xs in a ++ drop 1 b)
  | otherwise                = (i, num, over (ix i) init xs)
handleKeyPress KUp i num xs
  | i == (-1) = (i,num,xs)
  | otherwise = (i-1,num,xs)
handleKeyPress KDown i num xs
  | i+1 < length xs = (i+1,num,xs)
  | otherwise = (i,num,xs)
handleKeyPress KEnter i num xs   = (i+1,num, let (a,b) = splitAt (i+1) xs in a ++ [""] ++ b)
handleKeyPress KDel i num xs
  | length xs == 1 = (0,num,[""])
  | i + 1 == length xs = (i-1,num, init xs)
  | otherwise = (i, num, let (a,b) = splitAt i xs in (a ++ drop 1 b))
handleKeyPress (KASCII c) i num xs = (i, num, over (ix i) (++[c]) xs)
handleKeyPress _ i num xs = (i,num,xs)

foregray = with_fore_color def_attr (Color240 213)

inputImage :: Int -> [(Int, Bool, String, String)] -> Image
inputImage selected xs =
      hintAttr "prop" "props: true false not && || == /= <= >= < >"
  <-> hintAttr "expr" "exprs: x + - * / % negate if integer"
  <-> string def_attr " "
  <-> string foregray "current: "
      <|> string def_attr (showExprPrec 0 (fillErrors (snd (languageToTree (map (^._4) xs) propLanguage))) "")
  <-> string def_attr " "
  <-> vert_cat (imap image1 xs)
  where

  selectedLang = xs ^? ix selected . _3

  hintAttr lang hint
    | Just lang == selectedLang = string def_attr hint
    | otherwise                 = string foregray hint

  image1 i (depth, correct, lang, txt) =
    selectionMarker
    <|> string def_attr (replicate (4*depth) ' ')
    <|> string foregray "["
    <|> string attr txt
    <|> cursor
    <|> string foregray ("] : " ++ lang)
    where
    selectionMarker
      | i == selected = string def_attr "> "
      | otherwise     = string def_attr "  "
    attr | i == selected = def_attr
         | correct    = with_fore_color def_attr (Color240 27)
         | otherwise  = with_back_color def_attr bright_red
    cursor
      | i == selected = cursorImage
      | otherwise     = empty_image

cursorImage = char (with_fore_color def_attr blue) '_'

structuredToTree :: [String] -> [Constructor] -> ([String], Tree (Maybe String))
structuredToTree (str:strs) (Integer:cons)
  | not (null str) && all isDigit str = (strs, Node (Just str) [])
structuredToTree (str:strs) (Constructor name fields:cons)
  | str == name = let (strs1, fields') = mapAccumL languageToTree strs fields
                  in (strs1, Node (Just str) fields')
structuredToTree (str:strs) (_:cons)
  = structuredToTree (str:strs) cons
structuredToTree (str:strs) [] = (strs, Node Nothing [])
structuredToTree [] _ = ([], Node Nothing [])

languageToTree strs (Language _ cons) = structuredToTree strs cons

fillErrors :: Tree (Maybe String) -> Tree String
fillErrors = fmap (fromMaybe "_")

isOperator x = x `elem` "+-*/%=<>|&"

showExprPrec p (Node str [])
  = showString str
showExprPrec p (Node str [x,y])
  | all isOperator str = showParen (p > strPrec)
                     $ showExprPrec strPrec x
                     . showChar ' '
                     . showString   str
                     . showChar ' '
                     . showExprPrec (strPrec+1) y
  where
  strPrec = case str of
              "||" -> 2
              "&&" -> 3
              "+" -> 6
              "-" -> 6
              "*" -> 7
              "/" -> 7
              "%" -> 6
              "==" -> 4
              "/=" -> 4
              "<" -> 4
              ">" -> 4
              ">=" -> 4
              "<=" -> 4
showExprPrec p (Node str xs)
  = showParen (p > 10)
  $ showString str
  . flip (foldr (\x -> showChar ' '.showExprPrec 11 x)) xs


guessImage selected num
  = string promptAttr "Guess input: "
      <|> string foregray "["
      <|> string def_attr num
      <|> cursor
      <|> string foregray "] : integer"
  where
  cursor
    | selected == (-1) = cursorImage
    | otherwise = empty_image
  promptAttr
    | selected == (-1) = def_attr
    | otherwise = foregray

pointsImage :: Integer -> Image
pointsImage n = string foregray "Guessing points: "
            <|> string def_attr (show n)

messageImage :: String -> Image
messageImage msg = string foregray "Server message: "
               <|> string def_attr msg

boardImage :: Board -> Image
boardImage board
  =   string (with_fore_color def_attr blue) "Good examples: "
       <|> string def_attr (intercalate ", " (map (show . unvalue) (boardKnownGood board)))
  <-> string (with_fore_color def_attr red) "Bad examples: "
       <|> string def_attr (intercalate ", " (map (show . unvalue) (boardKnownBad board)))
  <-> string (with_fore_color def_attr green) "Theories:"
  <-> string def_attr "   " <|> vert_cat (map (uncurry theoryImage) (boardTheories board))

theoryImage prop answer = string def_attr (answerStr ++ " <- " ++ showExprPrec 0 (propToTree prop) "")
  where
  answerStr = case answer of
                RejectedValid (V v) -> "rejected " ++ show v
                AcceptedInvalid (V v) -> "accepted " ++ show v
                OK                    -> "correct!"

questionImage :: Maybe Value -> Image
questionImage Nothing = string foregray "No question pending"
questionImage (Just v) = string (with_fore_color def_attr red) "QUESTION! Is "
                       <|> string def_attr (show (unvalue v))
                       <|> string (with_fore_color def_attr red) " accepted? Yes(F5) No(F6)"

unvalue :: Value -> Integer
unvalue (V v) = v


type Parse = StateT [String] Maybe

runParse = evalStateT $
  do r <- parse
     [] <- get
     return r

class Parsable a where
  parse :: Parse a

next = do
  x:xs <- get
  put xs
  return x

instance Parsable Integer where
  parse = do
    x <- next
    guard (not (null x) && all isDigit x)
    return (read x)

instance Parsable Prop where
  parse = do
    x <- next
    case x of
      "==" -> liftM2 (:==) parse parse
      "/=" -> liftM2 (:/=) parse parse
      "&&" -> liftM2 (:&&) parse parse
      "||" -> liftM2 (:||) parse parse
      "<=" -> liftM2 (:<=) parse parse
      ">=" -> liftM2 (:>=) parse parse
      "<"  -> liftM2 (:<) parse parse
      ">"  -> liftM2 (:>) parse parse
      "true" -> return PTrue
      "false" -> return PFalse
      "not" -> liftM Not parse

instance Parsable Expr where
  parse = do
    x <- next
    case x of
      _ | not (null x) && all isDigit x -> return (K (read x))
      "+" -> liftM2 (:+) parse parse
      "-" -> liftM2 (:-) parse parse
      "*" -> liftM2 (:*) parse parse
      "/" -> liftM2 Div parse parse
      "%" -> liftM2 Mod parse parse
      "negate" -> liftM Negate parse
      "if" -> liftM3 If parse parse parse
      "x" -> return (Var (toName 0))

propToTree PTrue  = Node "true"  []
propToTree PFalse = Node "false" []
propToTree (Not p) = Node "not" [propToTree p]
propToTree (x :< y) = Node "<" [exprToTree x, exprToTree y]
propToTree (x :<= y) = Node "<=" [exprToTree x, exprToTree y]
propToTree (x :> y) = Node ">" [exprToTree x, exprToTree y]
propToTree (x :>= y) = Node ">=" [exprToTree x, exprToTree y]
propToTree (x :== y) = Node "==" [exprToTree x, exprToTree y]
propToTree (x :/= y) = Node "/=" [exprToTree x, exprToTree y]
propToTree (p :|| q) = Node "||" [propToTree p, propToTree q]
propToTree (p :&& q) = Node "&&" [propToTree p, propToTree q]

exprToTree (K i) = Node (show i) []
exprToTree (Var _) = Node "x" []
exprToTree (x :+ y) = Node "+" [exprToTree x, exprToTree y]
exprToTree (x :- y) = Node "-" [exprToTree x, exprToTree y]
exprToTree (x :* y) = Node "*" [exprToTree (K x), exprToTree y]
exprToTree (Div x y) = Node "/" [exprToTree x, exprToTree (K y)]
exprToTree (Mod x y) = Node "%" [exprToTree x, exprToTree (K y)]
exprToTree (Negate x) = Node "negate" [exprToTree x]
