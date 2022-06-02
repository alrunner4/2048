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

data Orientation = ColumnMajor | RowMajor
transposed: Orientation -> Orientation
transposed = \case
   ColumnMajor => RowMajor
   RowMajor    => ColumnMajor

data GameBoard: Orientation -> Nat -> Nat -> Type where
   BoardCols: Vect width  (Vect height (Maybe Integer)) -> GameBoard ColumnMajor width height
   BoardRows: Vect height (Vect width  (Maybe Integer)) -> GameBoard RowMajor    width height

data GameInput
   = Move ({o: Orientation} -> {w,h: Nat} -> GameBoard o w h -> (o' ** GameBoard o' w h))
   | Quit

move: {o': Orientation} ->
   ({o: Orientation} -> {w,h: Nat} -> GameBoard o w h -> GameBoard o' w h) -> GameInput
move f = Move (\b => let b' = f b in (_ ** b'))

empty: {o: Orientation} -> {w,h: Nat} -> GameBoard o w h
empty {o = ColumnMajor} = BoardCols (replicate w (replicate h Nothing))
empty {o = RowMajor}    = BoardRows (replicate h (replicate w Nothing))

transpose: {o: Orientation} -> {w,h: Nat} -> GameBoard o w h -> GameBoard (transposed o) w h
transpose {h = Z} = const empty
transpose {w = Z} = const empty
transpose {w = S w', h = S h'} = \case
   BoardCols xs =>
      let BoardRows tails = transpose (BoardCols$ map tail xs)
      in BoardRows$ map head xs :: tails
   BoardRows xs =>
      let BoardCols tails = transpose (BoardRows$ map tail xs)
      in BoardCols$ map head xs :: tails

contains: Integer -> GameBoard o w h -> Bool
contains target (BoardRows rows) = any (elem (Just target)) rows
contains target (BoardCols cols) = any (elem (Just target)) cols

toVect: (n: Nat) -> List a -> Vect n (Maybe a)
toVect    n   Nil    = replicate n Nothing
toVect (S n) (x::xs) = Just x :: toVect n xs
toVect  Z     _      = Nil

mergePairs: Num a => Eq a => List a -> List a
mergePairs xx@(x1::x2::xs) = if x1 == x2
   then x1+x2 :: mergePairs xs
   else x1    :: mergePairs (assert_smaller xx (x2::xs))
mergePairs xs = xs

mergePairsToFront: Num a => Eq a => {k: Nat} -> Vect k (Maybe a) -> Vect k (Maybe a)
mergePairsToFront v = toVect k (mergePairs (catMaybes (toList v)))

slideLeft: {w,h: Nat} -> GameBoard o w h -> GameBoard RowMajor w h
slideLeft (BoardRows rows) = BoardRows (map mergePairsToFront rows)
slideLeft (BoardCols cols) = BoardRows (map mergePairsToFront (transpose cols))

slideRight: {w,h: Nat} -> GameBoard o w h -> GameBoard RowMajor w h
slideRight (BoardRows rows) =
   let BoardRows mirrored = slideLeft (BoardRows (map reverse rows))
   in BoardRows (map reverse mirrored)
slideRight (BoardCols cols) =
   let BoardRows mirrored = slideLeft (BoardRows (map reverse (transpose cols)))
   in BoardRows (map reverse mirrored)

slideUp: {w,h: Nat} -> GameBoard o w h -> GameBoard ColumnMajor w h
slideUp (BoardCols cols) = BoardCols (map mergePairsToFront cols)
slideUp (BoardRows rows) = BoardCols (map mergePairsToFront (transpose rows))

slideDown: {o: Orientation} -> {w,h: Nat} -> GameBoard o w h -> GameBoard ColumnMajor w h
slideDown (BoardCols cols) =
   let BoardCols flipped = slideUp (BoardCols (map reverse cols))
   in BoardCols (map reverse flipped)
slideDown (BoardRows rows) =
   let BoardCols flipped = slideUp (BoardCols (map reverse (transpose rows)))
   in BoardCols (map reverse flipped)

availabilities: {w,h: Nat} -> GameBoard o w h -> List (Fin w, Fin h)
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

[fromRows] Show (GameBoard RowMajor w h) where
   show (BoardRows rows) = fastUnlines$
      toList rows <&> \r =>
         fastConcat$ ("| " ::) $ (++ [" |"]) $intersperse " | "
                     $map (padLeft 4 ' ' . emptyNothing)
                          (toList r)

[fromCols] {w: Nat} -> {h: Nat} -> Show (GameBoard ColumnMajor w h) where
   show bcols = show @{fromRows} (transpose bcols)

{w: Nat} -> {h: Nat} -> Show (GameBoard o w h) where
   show (BoardRows rows) = show @{fromRows} (BoardRows rows)
   show (BoardCols cols) = show @{fromCols} (BoardCols cols)

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

placeRandom: HasIO io => {w,h: Nat} -> GameBoard o w h -> Maybe (io (GameBoard o w h))
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

newGame: IO (w ** h ** GameBoard RowMajor w h)
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
          'Q' => pure  Quit
          _   => fail "invalid move input (Q to quit)"
   getLineOrEnd <&> map parseMove >>= \case
      Nothing            => pure Quit
      Just (Left   e   ) => putStrLn ("Error: " ++ e) >> getMoveInput
      Just (Right (m,_)) => pure m

||| The main game loop.
runGame: {w,h: Nat} -> StateT (o ** GameBoard o w h) IO Bool
runGame = do
   Move m <- lift getMoveInput | Quit => lift (putStr "Quitting.\n") >> pure False
   (_ ** b) <- get
   let (o ** b) = m b
   let False = contains 2048 b | True => pure True
   case placeRandom b of
      Nothing => pure False
      Just place => do
         b <- place
         print b
         put (_ ** b)
         runGame

main: IO ()
main = do
   (w ** h ** initialBoard) <- newGame
   print initialBoard
   if !(evalStateT (_ ** initialBoard) runGame)
      then putStr "Winner!\n"
      else putStr "Loser!\n"

