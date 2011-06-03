{-# LANGUAGE NoMonomorphismRestriction #-}
module MyList
  ( monotonicMap
  , monotonicCross
  , takeN
  , takeWhileM
  , takeNLthenN
  , takeWhileThen
  , takeC
  , dropC
  , takeWhileC
  , dropWhileC
  , diff
  ) where

import qualified Data.List as List

-- monotonicUnion :: Ord a => [[a]] -> [a]
-- monotonicUnion ((x:xs):ys) = x : foo

takeN n p (x:xs)
   | not (p x) = x:takeN n p xs
   | n <= 0    = []
   | otherwise = x: (takeN $! n - 1) p xs

takeNLthenN n p m [] = []
takeNLthenN n p m (x:xs)
  | not (p (x:xs)) = x : takeNLthenN n p m xs
  | n > 0          = x : (takeNLthenN $! n - 1) p m xs
  | True           = List.genericTake m (x:xs)

takeWhileM :: (Monad m) => (a -> m Bool) -> [a] -> m [a]
takeWhileM p = loop
  where
    loop [] = return []
    loop (x:xs) = do
      b <- p x
      if b
       then do
         xs' <- loop xs
         return (x:xs')
       else do
         return []

takeWhileThen p n = takeWhileC (take n) p

takeC cont = loop
  where
    loop n xs     | n <= 0  = cont xs
    loop n []               = []
    loop n (x:xs)           = x : loop (n-1) xs

dropC cont = loop
  where
    loop n xs     | n <= 0  = cont xs
    loop n []               = []
    loop n (x:xs)           = loop (n-1) xs

dropWhileC cont p = loop
  where
    loop [] = []
    loop (x:xs)
      | p x        = loop xs
      | otherwise  = cont xs

takeWhileC cont p = loop
  where
    loop [] = []
    loop (x:xs)
      | p x        = x : takeWhileC cont p xs
      | otherwise  = cont (x:xs)

distrib p xs = distrib_c p xs (0,0)

distrib_c p [] c = c
distrib_c p (x:xs) (t,f)
    | p x = distrib_c p xs (((,) $! t+1) f)
    | otherwise = distrib_c p xs ((,) t $! f+1)

monotonicCross :: (a -> b -> Bool) -> [a] -> [b] -> [(a,b)]
monotonicCross f [] _  = []
monotonicCross f _  [] = []
monotonicCross f xs ys = cross xs ys
  where
     cross  (a:as) []     = cross' as ys
     cross  (a:as) (b:bs)
        | f a b           = (a,b) : cross (a:as) bs
        | otherwise       = cross' as ys
     cross' []     _      = []
     cross' (a:as) (b:bs)
        | f a b           = (a,b) : cross (a:as) bs
        | otherwise       = []

monotonicMap :: (a -> b -> Maybe c) -> [a] -> [b] -> [c]
monotonicMap f [] _  = []
monotonicMap f _  [] = []
monotonicMap f xs ys = cross xs ys
  where
     cross  (a:as) []     = cross' as ys
     cross  (a:as) (b:bs)
        = case f a b of
          Just c  -> c : cross (a:as) bs
          Nothing -> cross' as ys
     cross' []     _      = []
     cross' (a:as) (b:bs)
        = case f a b of
	  Just c  -> c : cross (a:as) bs
          Nothing -> []

{-
-- This doesn't really do anything useful... if the second argument is a Bag,
-- then only duplicates that have an element in the first argument are removed.
union [] ys  = removeDups ys
union xs []  = xs
union (x:xs) (y:ys)
    = case compare x y of
      LT -> x : union xs (y:ys)
      EQ -> union (x:xs) ys
      GT -> y : union (x:xs) ys
-}


diff xs [] = (xs,[])
diff [] ys = ([],ys)
diff (x:xs) (y:ys)
   = case compare x y of
     LT -> let (xs', ys') = diff xs (y:ys) in (x:xs', ys')
     EQ -> diff xs ys
     GT -> let (xs', ys') = diff (x:xs) ys in (xs', y:ys')

{-
insertSetM ::(Ord a, Monad m) => a -> [a] -> m [a]
insertSetM a [] = return [a]
insertSetM a (x:xs)
   = case compare a x of
     LT -> do { xs' <- insertSetM a xs; return (x:xs') }
     EQ -> fail "Already in set"
     GT -> return (a:x:xs)

insertSetMaybe :: (Ord a) => a -> [a] -> Maybe [a]
insertSetMaybe x = insertSetM x
-}