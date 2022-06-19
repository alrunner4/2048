module AGameOf2048
import Control.Monad.State
import Data.Either
import Data.List
import Data.String
import Data.String.Parser
import Data.Vect
import System.File
import System.Random

%default total

-------------------------
-- Data Representation --

data GameBoard: Nat -> Nat -> Type where
   BoardCols: Vect width  (Vect height (Maybe Integer)) -> GameBoard width height
   BoardRows: Vect height (Vect width  (Maybe Integer)) -> GameBoard width height

(.rows): {h: Nat} -> GameBoard w h -> Vect h (Vect w (Maybe Integer))
(.rows) (BoardCols cols) = transpose cols
(.rows) (BoardRows rows) = rows

(.cols): {w: Nat} -> GameBoard w h -> Vect w (Vect h (Maybe Integer))
(.cols) (BoardCols cols) = cols
(.cols) (BoardRows rows) = transpose rows

data GameInput
   = Move ({w,h: Nat} -> GameBoard w h -> GameBoard w h)
   | Quit

move: ({w,h: Nat} -> GameBoard w h -> GameBoard w h) -> GameInput
move = Move

empty: {w,h: Nat} -> GameBoard w h
empty = BoardRows (replicate h (replicate w Nothing))

contains: Integer -> GameBoard w h -> Bool
contains target (BoardRows rows) = any (elem (Just target)) rows
contains target (BoardCols cols) = any (elem (Just target)) cols

padRight: (n: Nat) -> List a -> Vect n (Maybe a)
padRight    n   Nil    = replicate n Nothing
padRight (S n) (x::xs) = Just x :: padRight n xs
padRight  Z     _      = Nil

mergePairs: Num a => Eq a => List a -> List a
mergePairs xx@(x1::x2::xs) = if x1 == x2
   then x1+x2 :: mergePairs xs
   else x1    :: mergePairs (assert_smaller xx (x2::xs))
mergePairs xs = xs

mergePairsToFront: Num a => Eq a => {k: Nat} -> Vect k (Maybe a) -> Vect k (Maybe a)
mergePairsToFront v = padRight k (mergePairs (catMaybes (toList v)))

slideLeft: {w,h: Nat} -> GameBoard w h -> GameBoard w h
slideLeft board = BoardRows (map mergePairsToFront board.rows)

slideRight: {w,h: Nat} -> GameBoard w h -> GameBoard w h
slideRight board = BoardRows$ map (reverse . mergePairsToFront . reverse) board.rows

slideUp: {w,h: Nat} -> GameBoard w h -> GameBoard w h
slideUp board = BoardCols (map mergePairsToFront board.cols)

slideDown: {w,h: Nat} -> GameBoard w h -> GameBoard w h
slideDown board = BoardCols$ map (reverse . mergePairsToFront . reverse) board.cols

availabilities: {w,h: Nat} -> GameBoard w h -> List (Fin w, Fin h)
availabilities (BoardRows rows) =
   concat$ toList$ zip range rows <&>
      \(y,row) => map (,y) (findIndices isNothing row)
availabilities (BoardCols cols) =
   concat$ toList$ zip range cols <&>
      \(x,col) => map (x,) (findIndices isNothing col)

------------------------
-- Text and Constants --

emptyNothing: Show a => Maybe a -> String
emptyNothing Nothing  = ""
emptyNothing (Just i) = show i

{w: Nat} -> {h: Nat} -> Show (GameBoard w h) where
   show board = fastUnlines$
      toList board.rows <&> \r =>
         fastConcat$ ("| " ::) $ (++ [" |"]) $intersperse " | "
                     $map (padLeft 4 ' ' . emptyNothing)
                          (toList r)

maxHeight: Nat; maxHeight = 5
maxWidth:  Nat; maxWidth  = 5
minHeight: Nat; minHeight = 2
minWidth:  Nat; minWidth  = 2

Interpolation Nat where interpolate = show

newGamePrompt: String
newGamePrompt = """
   Welcome to 2048! To start a new game, first specify the game board size:
    > <width:\{minWidth}-\{maxWidth}> <height:\{minHeight}-\{maxHeight}>
    > 
   """

---------------------------------------------------
-- Game Driver: IO and Other Non-Total Functions --

%default covering

placeRandom: HasIO io => {w,h: Nat} -> GameBoard w h -> Maybe (io (GameBoard w h))
placeRandom b = case availabilities b of
   [] => Nothing
   o::opts => Just $do
      val <- rndSelect [2,4]
      (x,y) <- rndSelect (o::opts)
      pure$ case b of
         BoardRows rows => BoardRows $updateAt y (replaceAt x (Just val)) rows
         BoardCols cols => BoardCols $updateAt x (replaceAt y (Just val)) cols

between: Interpolation n => Num n => Ord n => n -> n -> Parser n
between low high = do
   i <- map fromInteger integer
   if i < low || i > high
      then fail "expected an integer between \{low} and \{high}"
      else pure i

getLineOrEnd: IO (Maybe String)
getLineOrEnd = do
   l <- getLine
   pure$ if null l && !(fEOF stdin)
      then Nothing
      else Just l

abort: String -> a
abort s = assert_total$ idris_crash s

newGame: IO (w ** h ** GameBoard w h)
newGame = do
   putStr newGamePrompt
   let parseDims = parse $ do
      w <- spaces *> between minWidth  maxWidth
      h <- spaces *> between minHeight maxHeight
      _ <- spaces *> eos
      pure (w,h)
   getLineOrEnd <&> map parseDims >>= \case
      Nothing                => abort "end of input"
      Just (Left   e       ) => putStrLn ("Error: " ++ e) >> newGame
      Just (Right ((w,h),_)) => do
         let Just p1 = placeRandom empty | _ => abort "impossible: failed to place starter numbers"
         Just p2 <- map placeRandom p1   | _ => abort "impossible: failed to place starter numbers"
         pure (w ** h ** !p2)

getMoveInput: IO GameInput
getMoveInput = do
   putStr "Next Move [W/A/S/D]: "
   let parseMove = parse $do
      case toUpper !(spaces *> letter <* spaces <* eos) of
          'W' => pure $move slideUp
          'A' => pure $move slideLeft
          'S' => pure $move slideDown
          'D' => pure $move slideRight
          'Q' => pure Quit
          _   => fail "invalid move input (Q to quit)"
   getLineOrEnd <&> map parseMove >>= \case
      Nothing            => pure Quit
      Just (Left   e   ) => putStrLn ("Error: " ++ e) >> getMoveInput
      Just (Right (m,_)) => pure m

||| The main game loop.
runGame: {w,h: Nat} -> StateT (GameBoard w h) IO Bool
runGame = do
   Move m <- lift getMoveInput | Quit => lift (putStr "Quitting.\n") >> pure False
   b <- get
   let b = m b
   let False = contains 2048 b | True => pure True
   case placeRandom b of
      Nothing => pure False
      Just place => do
         b <- place
         print b
         put b
         runGame

main: IO ()
main = do
   (w ** h ** initialBoard) <- newGame
   print initialBoard
   if !(evalStateT initialBoard runGame)
      then putStr "Winner!\n"
      else putStr "Loser!\n"

