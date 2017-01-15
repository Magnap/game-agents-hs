{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeApplications #-}
module Game where

import Control.Monad.Trans.Class (lift)
import qualified Control.Concurrent.STM as STM
import Control.Concurrent.STM (STM, atomically)
import Control.Monad.Random.Class (MonadRandom, uniform, interleave)
import Control.Monad.Random.Lazy (RandT, evalRandT, execRandT)
import System.Random (RandomGen, mkStdGen, getStdGen, split)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (mapMaybe, fromJust)
import Data.List (sortBy, groupBy, unfoldr)
import Data.Tree (Tree, unfoldTree)
import qualified Data.Tree as T
import Data.Tuple (swap)
import Control.DeepSeq
import GHC.Generics (Generic)
import Data.Ord (comparing, Down(..))
import Control.Monad (replicateM_, unless)
import qualified Control.Concurrent as Co
import System.IO.Unsafe (unsafePerformIO)
import Control.Exception.Base (evaluate)

class (Eq (State g), Eq (Player g), Ord (Score g)) => PerfectInformation g where
  data State g :: *
  data Move g :: *
  data Score g :: *
  data Player g :: *
  initialState :: State g
  legalMoves :: State g -> [Move g]
  score :: Player g -> State g -> Score g
  currentPlayer :: State g -> Player g
  applyMove :: Move g -> State g -> State g

instance PerfectInformation Int where
  newtype State Int = St (Int,Bool) deriving (Eq, Show, Ord, NFData)
  newtype Move Int = M Int deriving (Eq, Show, NFData)
  newtype Score Int = Sc Double deriving (Eq, Ord, Show, Num, Floating, Fractional, Real, RealFrac, RealFloat, NFData)
  newtype Player Int = P Bool deriving (Eq, Show, Ord, Bounded, Enum, NFData)
  initialState = St (50,True)
  legalMoves (St (x,_)) = if x > 0 then fmap M [1..9] else mempty
  score (P p) (St (x,t)) = Sc (if x > 0 then 0 else if p == t then 1 else -1)
  currentPlayer (St (_,b)) = P b
  applyMove (M y) (St (x,b)) = St (x-y,not b)

mctsWeights :: (PerfectInformation g, RealFloat (Score g), Ord (State g), Show (Score g), Show (Move g), Show (State g), NFData (Move g), NFData (Score g)) => Map (State g) (Score g, Int) -> State g -> [(Move g, Score g)]
mctsWeights m s = go . mapMaybe (\ move -> sequence . (move,) . flip M.lookup m . flip applyMove s $ move) . legalMoves $ s
  where go xs = let t = fromIntegral . sum . fmap (snd . snd) $ xs in (fmap . fmap) (\ (w,n) -> w / fromIntegral n + sqrt ((2*log t) / fromIntegral n)) $ xs

groupEqualsBy :: (a -> a -> Ordering) -> [a] -> [[a]]
groupEqualsBy f = groupBy (fmap (== EQ) . f) . sortBy f

mctsChoose :: (PerfectInformation g, RealFloat (Score g), Ord (State g), MonadRandom m, Show (Move g), Show (Score g), Show (State g), NFData (Move g), NFData (Score g)) => Map (State g) (Score g, Int) -> State g -> m (Move g)
mctsChoose m = uniform . fmap fst . head . groupEqualsBy (comparing (Down . snd)) . (fmap . fmap) (replaceWhen isNaN (1/0)) . mctsWeights m

replaceWhen :: (a -> Bool) -> a -> a -> a
replaceWhen p x y = if p y then x else y

type MCT g = Tree (State g, (Maybe (Move g), STM.TVar (Map (Player g) (Score g), Int)))

allGames :: (PerfectInformation g, Show (Move g), Show (State g), NFData (State g), NFData (Move g)) => Tree (State g, Maybe (Move g))
allGames = fmap snd . unfoldTree (\ (m,s) -> ((m,(s,m)),fmap (\ m' -> (Just m', applyMove m' s)) . legalMoves $ s)) $ (Nothing, initialState)

mctsGameTree :: (PerfectInformation g, Num (Score g), Ord (Player g), Bounded (Player g), Enum (Player g), Show (Move g), Show (State g), NFData (State g), NFData (Move g), NFData (Score g), NFData (Player g)) => MCT g
mctsGameTree = (fmap . fmap) (\ m -> (m,(unsafePerformIO $ STM.newTVarIO (seq m . M.fromList . zip allValues . repeat $ 0,0)))) $ allGames


mctsMakeMap :: (PerfectInformation g, Ord (State g), Ord (Player g), Show (State g), NFData (State g), NFData (Score g), NFData (Player g)) => MCT g -> STM (Map (State g) (Score g, Int))
mctsMakeMap (T.Node rl fs) = fmap (foldr (uncurry M.insert . (\ (s,m) -> (s,swap . fmap (flip (M.!) . currentPlayer . fst $ rl) . swap $ m))) mempty) . traverse (sequenceA . fmap STM.readTVar . fmap snd) . fmap T.rootLabel $ fs

mctsPlayout :: (PerfectInformation g, Eq (Move g), RealFloat (Score g), Ord (State g), Bounded (Player g), Enum (Player g), Ord (Player g), RandomGen g', Show (Move g), Show (Score g), Show (State g), Show (Player g), NFData (Score g), NFData (Player g), NFData (Move g), NFData (State g)) => MCT g -> RandT g' STM (Map (Player g) (Score g))
mctsPlayout (T.Node (s,(_,tv)) []) = do
  old <- lift $ STM.readTVar tv
  new <- return $ M.fromList . fmap (fmap (flip score s) . dup) $ allValues
  lift . deepWrite tv . fmap (+1) . swap . fmap (M.unionWith (+) new) . swap $ old
  return new
mctsPlayout t@(T.Node (s,(_,tv)) ms) = do
  map' <- lift . mctsMakeMap $ t
  old <- lift . STM.readTVar $ tv
  m <- mctsChoose map' s
  new <- mctsPlayout (fromJust . lookup m . fmap (swap . fmap (fromJust . fst . snd . T.rootLabel) . dup) $ ms)
  lift . deepWrite tv . fmap (+1) . swap . fmap (M.unionWith (+) new) . swap $!! old
  return new

deepWrite v x = x `deepseq` STM.writeTVar v x

allValues :: (Bounded a, Enum a) => [a]
allValues = enumFromTo minBound maxBound

dup a = (a,a)

main' p n = do
  g <- getStdGen
  let gt = mctsGameTree @Int
  dones <- atomically $ STM.newTVar 0
  --let x g = atomically . flip execRandT g . mctsPlayout $ gt
  let worker = mapM_ (\ g -> atomically . flip execRandT g . mctsPlayout $ gt) . take 100 . unfoldr (Just . split) $ (if p then mkStdGen 0 else g)
  replicateM_ 30 worker
  (>>= print) . atomically $ (mapM . mapM) STM.readTVar (T.rootLabel $ gt)
  (>>= print) . atomically $ (mapM . mapM) STM.readTVar (T.rootLabel . head . T.subForest $ gt)

main = main' False 0 >> return ()

drawTrunc :: (Maybe Int) -> Tree String -> String
drawTrunc Nothing = T.drawTree
drawTrunc (Just n) = T.drawTree . truncateTree n

truncateTree :: Int -> Tree a -> Tree a
truncateTree 0 (T.Node rl _) = T.Node rl []
truncateTree _ t@(T.Node _ []) = t
truncateTree n (T.Node rl sf) = T.Node rl (fmap (truncateTree (n-1)) sf)
