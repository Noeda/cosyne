{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes #-}

module Numeric.COSYNE
  (
  -- * Running the algorithm
    cosyne
  , Stop(..)
  , SubPopulationSize
  -- * Utilities
  , shuffle
  , cauchyMutate
  , cauchy )
  where

import Control.DeepSeq
import Control.Lens
import Control.Monad.ST
import Control.Monad.State.Strict
import Data.Data
import Data.Foldable
import Data.Monoid
import Data.List ( sortBy )
import Data.Ord
import Data.Traversable
import GHC.Generics
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as VM
import qualified Data.IntMap.Strict as IM

-- | Type for the size of a subpopulation.
type SubPopulationSize = Int

-- | Should I stop or not?
data Stop stop
  = Stop stop
  | Continue
  deriving ( Eq, Ord, Show, Read, Typeable, Data, Generic, Functor, Foldable, Traversable )

data Itemizing item i
  = JustUserItem !item
  | JustVector   !(V.Vector i)
  | Both         !item !(V.Vector i)
  deriving ( Eq, Ord, Show, Read, Typeable, Data, Generic )

instance (NFData item, NFData i) => NFData (Itemizing item i)

data Individual promise score item i = Individual
  { _item   :: !(Itemizing item i)
  , _score  :: !(Maybe (promise score)) }
  deriving ( Eq, Ord, Show, Read, Typeable, Data, Generic )

instance (NFData item, NFData i, NFData (promise score)) => NFData (Individual promise score item i)

data Cosyne m promise score item stop i = Cosyne
  { _runningIndex               :: !Int
  , _individuals                :: !(IM.IntMap (Individual promise score item i))
  , _evaluate                   :: !(item -> m (promise score))
  , _forcePromise               :: !(forall c. promise c -> m c)
  , _stopper                    :: !(item -> score -> m (Stop stop))
  , _logger                     :: !(String -> m ())
  , _mutate                     :: !(i -> m i)
  , _shuffleFun                 :: !(forall c. V.Vector c -> m (V.Vector c))
  , _fromVector                 :: !(V.Vector i -> m item)
  , _toVector                   :: !(item -> m (V.Vector i)) }
makeLenses ''Individual
makeLenses ''Cosyne

nextIndex :: Monad m => StateT (Cosyne m promise score item stop i) m Int
nextIndex = do
  old_index <- use runningIndex
  runningIndex .= (old_index+1)
  return old_index

getItem :: Monad m => Int -> StateT (Cosyne m promise score item stop i) m item
getItem idx = do
  Just individual <- use (individuals.at idx)
  from_vec <- use fromVector
  case individual^.item of
    JustUserItem i -> return i
    Both i _ -> return i
    JustVector vec -> do
      i <- lift $ from_vec vec
      individuals.at idx .= Just (individual & item .~ (Both i vec))
      return i
{-# INLINE getItem #-}

getVector :: Monad m => Int -> StateT (Cosyne m promise score item stop i) m (V.Vector i)
getVector idx = do
  Just individual <- use (individuals.at idx)
  to_vec <- use toVector
  case individual^.item of
    JustVector i -> return i
    Both _ i -> return i
    JustUserItem i -> do
      vec <- lift $ to_vec i
      individuals.at idx .= Just (individual & item .~ (Both i vec))
      return vec
{-# INLINE getVector #-}

getScore :: Monad m => Int -> StateT (Cosyne m promise score item stop i) m score
getScore idx = do
  Just individual <- use (individuals.at idx)
  evaluation <- use evaluate
  fp <- use forcePromise
  lift . fp =<< case individual^.score of
    Nothing -> do
      i <- getItem idx
      scoring <- lift $ evaluation i
      individuals.at idx .= Just (individual & score .~ Just scoring)
      return scoring
    Just scr -> return scr
{-# INLINE getScore #-}

promiseScores :: Monad m => StateT (Cosyne m promise score item stop i) m ()
promiseScores = do
  current_individuals <- IM.keys <$> use individuals
  ev <- use evaluate
  for_ current_individuals $ \idx -> do
    individual <- use (individuals.at idx)
    case individual^?_Just.score of
      Nothing -> do
        item <- getItem idx
        promising <- lift $ ev item
        individuals.at idx._Just.score .= Just promising
      Just _ -> return ()

logLine :: Monad m => String -> StateT (Cosyne m promise score item stop i) m ()
logLine str = do
  lg <- use logger
  lift $ lg str
{-# INLINE logLine #-}

generation :: (Monad m, NFData i, Ord score) => StateT (Cosyne m promise score item stop i) m (Stop stop)
generation = do
  logLine "Obtaining promises for scores..."
  promiseScores
  inds <- use individuals
  logLine $ "Fetching scores for " <> show (IM.size inds) <> " individuals."
  unsorted_scores <- for (IM.assocs inds) $ \(idx, _) ->
    (,) <$> getScore idx <*> pure idx

  logLine "Making offspring..."
  result <- makeOffspring unsorted_scores
  logLine "Generation done."
  return result
{-# INLINE generation #-}

makeOffspring :: (Monad m, NFData i, Ord score)
              => [(score, Int)]
              -> StateT (Cosyne m promise score item stop i) m (Stop stop)
makeOffspring unsorted_scores = do
  st <- use stopper
  i <- getItem (snd $ head sorted_scores)
  result <- lift $ st i (fst $ head sorted_scores)

  for_ (take (num_scores `div` 4) sorted_scores) $ \(_, idx) ->
    makeMutatedIndividual idx

  for_ dropped_scores $ \drop_idx -> removeIndividual drop_idx

  shuffleIndividuals
  return result
 where
  sorted_scores  = sortBy (comparing fst) unsorted_scores
  parent_scores  = take (num_scores `div` 4) sorted_scores
  dropped_scores = fmap snd $ drop (num_scores - length parent_scores) sorted_scores

  num_scores    = length sorted_scores

removeIndividual :: Monad m => Int -> StateT (Cosyne m promise score item stop i) m ()
removeIndividual idx = individuals.at idx .= Nothing

shuffleIndividuals :: (Monad m, NFData i) => StateT (Cosyne m promise score item stop i) m ()
shuffleIndividuals = do
  inds <- use individuals
  if IM.null inds
    then return ()
    else do let (first_individual_index, _) = IM.findMin inds
            vec <- getVector first_individual_index
            let num_features = V.length vec

            shuffleFeatures num_features

shuffleFeatures :: forall m promise score item stop i. (NFData i, Monad m) => Int -> StateT (Cosyne m promise score item stop i) m ()
shuffleFeatures num_features = do
  shuf <- use shuffleFun

  inds <- use individuals
  vecs <- ifor inds $ \idx _ -> getVector idx

  let keys = V.fromList $ IM.keys inds

  shufflings <- V.replicateM num_features $ lift $ shuf keys
  let _ = shufflings :: (V.Vector (V.Vector Int))

  let new_inds = IM.fromList $ (zip (IM.keys inds) [0..]) <&> \(idx, nidx) ->
                 let vec = V.generate num_features $ \vidx ->
                                  let item_index = (shufflings V.! vidx) V.! nidx
                                      Just vec = IM.lookup item_index vecs
                                      value = vec V.! vidx
                                   in value
                  in vec `deepseq` (idx, Individual { _item = JustVector vec
                                                    , _score = Nothing })


  let _ = new_inds :: IM.IntMap (Individual promise score item i)
  individuals .= new_inds

makeMutatedIndividual :: Monad m => Int -> StateT (Cosyne m promise score item stop i) m Int
makeMutatedIndividual idx = do
  mut <- use mutate
  vec <- getVector idx
  new_vec <- for vec $ lift . mut

  let new_individual = Individual
                       { _score = Nothing
                       , _item  = JustVector new_vec }

  idx <- nextIndex
  individuals.at idx .= (new_vec `seq` Just new_individual)
  return idx

-- | Runs Cosyne evolutionary algorithm for a model with `Floating` components.
--
-- Components of the structure are mutated by using cauchy distribution.
cosyne :: (Monad m, NFData a, Traversable f, Ord score)
       => f a                                -- ^ Seed individual, the initial population is replicated from this individual.
       -> SubPopulationSize                  -- ^ How large subpopulations should be for each element.
       -> (f a -> score -> m (Stop stop))    -- ^ Stop hook. Returns an individual and its score. Return if you want `cosyne` to return.
       -> (f a -> m (promise score))         -- ^ Loss function. Make a promise of a score. Returning a promise instead of score directly lets you run the computation asynchronously (maybe even send the computation somewhere else). The score won't (usually) be demanded immediately.
       -> (forall c. promise c -> m c)       -- ^ Force a promise.
       -> (a -> m a)                         -- ^ A mutator. You can use `cauchy` if you want.
       -> (forall c. V.Vector c -> m (V.Vector c))     -- ^ A shuffler function. This is used for subpopulation shuffling part of Cosyne. You can use `shuffle` from this module if you want.
       -> (String -> m ())                   -- ^ Logging. If you want to see human-readable diagnostics then supply this function and do something with the string.
       -> m stop
cosyne adam sub_pop_size stopper scorer promiser mutator shuffler logger = do
  evalStateT generationLoop Cosyne
    { _runningIndex   = sub_pop_size
    , _individuals    = IM.fromList $ zip [0..] $ replicate sub_pop_size $
                            Individual { _score = Nothing
                                       , _item = JustUserItem adam }
    , _evaluate       = scorer
    , _logger         = logger
    , _stopper        = stopper
    , _forcePromise   = promiser
    , _mutate         = mutator
    , _shuffleFun     = shuffler
    , _fromVector     = \vec -> return $ flip evalState (V.toList vec) $ for adam $ \_ -> do
                                (x:rest) <- get
                                put rest
                                return x
    , _toVector       = return . V.fromList . toList }
 where
  generationLoop = do
    result <- generation
    case result of
      Stop x -> return x
      Continue -> generationLoop
{-# INLINE cosyne #-}

-- | Given a function that returns random numbers in a range, shuffles the
-- elements of a vector.
shuffle :: Monad m => (Int -> Int -> m Int) -> V.Vector a -> m (V.Vector a)
shuffle random_rio vec = do
  random_list <- make_random_list (V.length vec)
  return $ V.fromList $ runST $ do
    modifiable <- V.thaw vec
    make_shuffled_vector modifiable random_list (V.length vec-1)
 where
  make_random_list 0 = return []
  make_random_list num_items = do
    x <- random_rio 0 (num_items-1)
    (x:) <$> make_random_list (num_items-1)

  make_shuffled_vector _ [] _ = return []
  make_shuffled_vector modifiable (x:rest) windex = do
    tmp <- VM.read modifiable x
    replacement <- VM.read modifiable windex
    VM.write modifiable x replacement
    (tmp:) <$> make_shuffled_vector modifiable rest (windex-1)

-- | Mutates a `Traversable` structure by adding a cauchy distributed value to
-- each element.
cauchyMutate :: (Floating a, Monad m, Traversable f)
             => m a      -- ^ Random number generator that returns an element between 0 and 1 uniformly.
             -> a        -- ^ Scale the standard cauchy distribution with this value.
             -> f a      -- ^ Traversable structure to mutate.
             -> m (f a)
cauchyMutate rng multiple structure = for structure $ \item -> do
  x <- rng
  return $ item + (multiple * (tan $ pi * (x-0.5)))
{-# INLINE cauchyMutate #-}

-- | Mutates a `Floating` value by adding a cauchy distributed value to it.
cauchy :: (Floating a, Monad m)
       => m a    -- ^ Random number generator, return value between 0 and 1 uniformly.
       -> a      -- ^ Scale the standard cauchy distribution with this value.
       -> a      -- ^ Value to mutate.
       -> m a
cauchy rng multiple x = do
  t <- rng
  return $ x + (multiple * (tan $ pi * (t - 0.5)))

