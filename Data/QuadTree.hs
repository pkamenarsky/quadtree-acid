{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Data.QuadTree where

import Control.DeepSeq
import Control.Applicative
import Control.Monad
import Control.Monad.State.Class
import Control.Monad.IO.Class
import Control.Monad.Reader.Class
import Control.Applicative

import Data.Data
import Data.Conduit
import Data.Acid
import Data.SafeCopy
import qualified Data.IxSet as IS

import Test.QuickCheck.Arbitrary
import qualified Test.QuickCheck as QC

import Text.Regex

import System.Random
import System.CPUTime

import Network.Wai
import Network.Wai.Handler.Warp
import Network.HTTP.Types.Status

import qualified Data.ByteString.Lazy.Char8 as B

data Point = Point Double Double
    deriving (Eq, Ord, Read, Show, Data, Typeable)

data Rectangle = Rectangle Double Double Double Double
    deriving (Eq, Ord, Read, Show, Data, Typeable)

data Bubble = Bubble {
    position :: Point,
    message :: String
} deriving (Eq, Ord, Read, Show, Data, Typeable)

data QuadTree a = Node {
    rect :: Rectangle,
    q1, q2, q3, q4 :: QuadTree a,
    elementCount :: Int
} | Leaf {
    elements :: [a],
    elementCount :: Int
} deriving (Eq, Ord, Read, Show, Data, Typeable)

emptyTree = Node {
    rect = worldRect,
    q1 = Leaf [] 0, 
    q2 = Leaf [] 0, 
    q3 = Leaf [] 0, 
    q4 = Leaf [] 0, 
    elementCount = 0
}

-- use lenses
sq1 n v = n {q1 = v}
sq2 n v = n {q2 = v}
sq3 n v = n {q3 = v}
sq4 n v = n {q4 = v}

overlaps :: Rectangle -> Rectangle -> Bool
overlaps (Rectangle x y w h) (Rectangle x' y' w' h') =
    let ox = x + w
        oy = y + h
        ox' = x' + w'
        oy' = y' + h'
    in not $ ox < x' || x > ox' || oy < y' || y > oy'

searchMax :: Positionable a => QuadTree a -> Rectangle -> Int -> [a]
searchMax n@(Node {rect = r', elementCount = cnt}) r max =
    if cnt > 0 && overlaps r r'
        then search' q1 ++ search' q2 ++ search' q3 ++ search' q4
        else []
    where
        search' f =
            let child = f n
                fi = fromIntegral
                frac = (fi (elementCount child)) / (fi cnt)
            in searchMax child r (round $ (fi max) * frac)
searchMax (Leaf {elements = es}) (Rectangle x y w h) max =
    take max $ flip filter es (\p -> let (Point px py) = pos p in
        px > x && px <= x + w && py > y && py <= y + h)

search :: Positionable a => QuadTree a -> Rectangle -> [a]
search n@(Node {rect = r', elementCount = cnt}) r =
    if cnt > 0 && overlaps r r'
        then search' q1 ++ search' q2 ++ search' q3 ++ search' q4
        else []
    where
        search' f = search (f n) r
-- search (Leaf {elements = es}) (Rectangle x y w h) = es
search (Leaf {elements = es}) (Rectangle x y w h) =
    flip filter es (\p -> let (Point px py) = pos p in
        px > x && px <= x + w && py > y && py <= y + h)

class Positionable a where
    pos :: a -> Point

instance Positionable Point where
    pos = id

instance Positionable Bubble where
    pos = position

worldRect = Rectangle 0 0 100 100
treeDepth = 5

insert :: Positionable a => QuadTree a -> a -> QuadTree a
insert = insert' treeDepth where
    insert' 0 (Leaf {elements = es, elementCount = cnt}) e =
        Leaf {elements = e:es, elementCount = cnt + 1}
    insert' d (Leaf [] _) p = insert' d emptyTree p
    insert' d n@(Node {rect = r, elementCount = cnt}) p =
        let (Rectangle x y w h) = r
            (Point px py) = pos p
            eps = 0.0001
            w' = w / 2
            h' = h / 2
            x' = x + w'
            y' = y + h'
        in
            if px < x - eps || py < y - eps ||
               px > x + w + eps || py > y + h + eps
                then n
                else if px > x - eps && px < x' + eps
                    then if py > y - eps && py < y' + eps
                        then node sq2 q2 $ Rectangle x y w' h'
                        else node sq3 q3 $ Rectangle x y' w' h'
                    else if py > y - eps && py < y' + eps
                        then node sq1 q1 $ Rectangle x' y w' h'
                        else node sq4 q4 $ Rectangle x' y' w' h'
        where
            node' s g r = s (n {elementCount = cnt + 1})
                            (insert' (d - 1) (g n) p)
            node s g r = case g n of
                Leaf es _ -> if d > 1
                    then s (n {elementCount = cnt + 1})
                           (insert' (d - 1) (emptyTree {rect = r}) p)
                    else node' s g r
                _ -> node' s g r

insertQT :: Positionable a => a -> Update (QuadTree a) ()
insertQT = modify . flip insert

searchQT :: Positionable a => Rectangle -> Query (QuadTree a) [a]
searchQT = reader . flip search

searchMaxQT :: Positionable a => Rectangle -> Int -> Query (QuadTree a) [a]
searchMaxQT r max = reader (\q -> searchMax q r max)

data World = World {
    bubbles :: IS.IxSet Bubble
} deriving (Data, Typeable)

emptyWorld = World {bubbles = IS.empty}

newtype QuantizedPoint = QuantizedPoint Int
    deriving (Eq, Ord, Read, Show, Data, Typeable)

quantizeGPS :: Point -> QuantizedPoint
quantizeGPS = undefined

instance IS.Indexable Bubble where
    empty = IS.ixSet [IS.ixFun ((:[]) . quantizeGPS . position)]

$(deriveSafeCopy 0 'base ''Point)
$(deriveSafeCopy 0 'base ''Bubble)
$(deriveSafeCopy 0 'base ''World)
$(deriveSafeCopy 0 'base ''Rectangle)
$(deriveSafeCopy 0 'base ''QuadTree)

$(makeAcidic '' Bubble [])
$(makeAcidic '' World [])
$(makeAcidic '' QuadTree ['insertQT, 'searchQT, 'searchMaxQT])

instance Arbitrary Point where
    arbitrary = do
        x <- arbitrary
        y <- arbitrary
        return $ Point (min 100 $ max 0 x) (min 100 $ max 0 y)

instance NFData Point where
    rnf (Point x y) = x `seq` y `seq` ()

instance NFData a => NFData (QuadTree a) where
    rnf (Leaf es _) = rnf es
    rnf n@(Node {}) = rnf (q1 n) `seq` rnf (q2 n) `seq` rnf (q3 n) `seq` rnf (q4 n)

app acid req = do
    ps <- liftIO $ do
        x <- randomRIO (13, 14 :: Double)
        y <- randomRIO (40, 48 :: Double)
        w <- randomRIO (0.1, 2 :: Double)
        h <- randomRIO (0.1, 20 :: Double)

        -- query acid (SearchQT $ Rectangle x y w h)
        query acid (SearchMaxQT (Rectangle 0 0 1000 1000) 100)

    return $ responseLBS ok200 [] (B.pack $ "__jsonCB(\"" ++ show ps ++ "\");")

main = do
    poiData <- readFile "pois.csv"

    let pois = map (\(x:y:rs) -> Point (read x) (read y))
                (map (splitRegex $ mkRegex ", ") (lines poiData))

    -- let qt = foldl insert emptyTree pois

    acid <- openLocalState emptyTree
    ds <- forM_ pois (update acid . InsertQT)

    start <- ds `deepseq` getCPUTime

    r <- replicateM 1000 $ do
        x <- randomRIO (13, 14 :: Double)
        y <- randomRIO (46, 48 :: Double)
        w <- randomRIO (0.1, 2 :: Double)
        h <- randomRIO (0.1, 2 :: Double)
        query acid (SearchQT $ Rectangle x y w h)

    {--
    r <- replicateM 1000 $ do
        x <- randomRIO (13, 14 :: Double)
        y <- randomRIO (46, 48 :: Double)
        w <- randomRIO (0.1, 2 :: Double)
        h <- randomRIO (0.1, 2 :: Double)
        return $ search qt $ Rectangle x y w h
    --}
    
    end <- r `deepseq` getCPUTime
    print $ (end - start) `div` 1000000000

    -- print $ insert emptyTree (Point 0 0)
    {--
    QC.quickCheck (\p@(Point x y) ->
        let qt = insert emptyTree p
            in elem p $ search qt $ Rectangle (x - 1) (y - 1) 2 2)
    acid <- openLocalState emptyWorld
    --}
    
    run 9090 (app acid)

    createCheckpoint acid
    closeAcidState acid
