{-# OPTIONS -fglasgow-exts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-
module NumberTheory
  ( egcd         --Extended Euclidean algorithm
  , gof          --Greatest Odd Factor
  , inverse      --inverse p q   = multiplicative inverse of p (mod q)
  , expmod       --expmod  a b z =
  , primes       --sequential list of all primes, fast up to 10^6, accurate up to 10^13
  , carmicheals  --list of carmicheal numbers up to 10^16
  , factored_carmicheals --a list of pairs of carmicheal numbers paired with a list of prime numbers that is it's factorization, up to 10^16
  , factor       --factors a number into a list of prime numbers.
  , covers       --covers (x,y) xs = does the list xs hit every element e, x <= e <= y
  , sqrts        --
-}
module NumberTheory
  ( primes
  , expmod, expmod2
  , factor, factorn
  , phi2, phi, phi_factored, factor_phi, factor_phi_factored
  , crt
  , gcrt, gcrt'
  , egcd
  , gof
  , gofpow
  , inverse
  , isSPP
  , millerPows
  , millerFactor
  , splitFactors
  , factorCarmichael
  , isPrime
  , isPrimeSlow
  , isPrimRoot, isPrimRoot_factored
  , primRoots
  , fails, fails'
  , index_carms
  , sqrts
  , isPP
  , covers
  , allArray
  , countArray
  , satFermat
  , factors
  , printgen
  , satKorselt, satKorselt'
  , isCarmichael, isCarmichael2
  , primeTrips
  , carmichaels
  , chain_prime
  , summod
  , prodmod
  , principleRoots
  , isPrincipleRoot
  , orbit
  , showStream
  , show_list
  , distinctEltsInRange
  , eltStats
  , choose
  ) where


import System.IO.Unsafe(unsafePerformIO)
import qualified Data.List as List
import qualified Control.Monad.ST as ST
import qualified Data.Array.ST as ST
import Data.List(foldl')
import MyList(takeNLthenN, takeWhileThen)
import Data.List.Ordered(merge,nub)
import Data.Array.MArray as MArray
import Data.Array.IArray
import Control.Monad as Monad
import qualified Math.Sieve.ONeill as ONeill

primesFile = "primes.txt"
carmichaelsFile = "carmichael-16.txt"

-- A list of prime numbers
-- it reads prime numbers out of a file, and then filters through
-- the rest of the integers using the strong psuedo-prime test
-- Thus, this table may contain errors for primes greater than 10^13
-- But, it's going to take a long time to get there, and if you do,
-- you'll definitely want a data structure that isn't a list!

newSTUArray :: (Ix i, MArray (ST.STUArray s) a (ST.ST s)) => (i,i) -> a -> ST.ST s (ST.STUArray s i a)
newSTUArray = MArray.newArray

newSTArray :: (Ix i, MArray (ST.STArray s) a (ST.ST s)) => (i,i) -> a -> ST.ST s (ST.STArray s i a)
newSTArray = MArray.newArray

{-
primes :: [Integer]
primes = parse 0 (unsafePerformIO (readFile primesFile))
	 where
	      parse n str = case (reads str) of
			    [(prime, str')] -> prime : parse prime str'
{-                            []              -> []  -}
			    []              -> [ x | x <- [n+2, n+4..], isSPP x (take 5 primes)]
-}

primes :: [Integer]
primes = ONeill.primes

--Modular Exponentiation
--expmod a p n = (a ^ p) `mod` n

expmod, expmod2 :: Integral a => a -> a -> a -> a
expmod a p n
    | p > 0     =
	let
	a' = a `rem` n
        f _ 0 y = y
	f x p y = g x p
	    where
	    g x p
		| even p    = g (x*x `rem` n) (p `quot` 2)
		| otherwise = f x (p-1) (x * y `rem` n)
	in  f a' (p-1) a'
    | p == 0    = 1
    | otherwise = expmod (inverse a n) (-p) n


expmod2 a p n
    | p >= 0     = expmod' 1 (a `rem` n) p
    | otherwise  = expmod' 1 (inverse a n) (-p)
    where
    expmod' x a p
       | p == 0         = if x <= 0 then x + n else x
       | p `rem` 2 == 0 = expmod' x (a*a `rem` n) (p `quot` 2)
       | otherwise      = expmod' (x * a `rem` n) (a * a `rem` n) (p `quot` 2)

--Factors numbers into primes
--e.g.
--factor  360 = [2,2,2,3,3,5]
--factorn 360 = [(2,3),(3,2),(5,1)]

--factor :: Integral a => a -> [a]
factor n
    | n >= 1 = factor' primes n
-- the prime factorization of n
	where
		factor' _      1 = []
		factor' (p:ps) n
			| n `rem` p == 0 = p : factor' (p:ps) (n `quot` p)
			| otherwise      = factor' ps n

factorn n
    | n == 1 = []
    | n >= 2 = factor' primes 0 n
    where
    factor' (p:ps) k 1 = [(p,k)]
    factor' (p:ps) k n
	| n `rem` p == 0 = (factor' (p:ps) $! (k+1)) $! (n `quot` p)
	| k > 0          = (p,k) : factor' ps 0 n
	| otherwise      = factor' ps 0 n


phi2 :: Integer -> Integer
phi2 n = phi' primes 1 n
   where
      phi'  ps@(p:tl) pphi n
         | n == 1         = pphi
	 | n `rem` p == 0 = phi'' ps (pphi * (p-1)) (n `quot` (p::Integer))
         | otherwise      = phi'  tl pphi n
      phi'' ps@(p:tl) pphi n
         | n == 1         = pphi
         | n `rem` p == 0 = phi'' ps (pphi * p) (n `quot` p)
         | otherwise      = phi'  tl pphi n

phi = phi_factored . factor

-- The Euler Phi function

phi_factored =  foldl f 1 . List.group
	where
		f n (p:ps) = n * (p - 1) * p ^ List.genericLength ps

factor_phi = factor_phi_factored . factor

factor_phi_factored = foldl f [] . List.group
        where
	        f n (p:ps) = (merge n (factor (p-1) ++ ps))


-- The Chinese Remainder Theorem

crt :: Integral a => a -> a -> a -> a -> a
crt a m b n = ans
  where
  ans = b + n*t
  t   = (a - b) * (inverse m n) `mod` m

-- Generalized Chinese Remainder Theorem

gcrt' :: Integral a => a -> a -> a -> a -> [a]
gcrt' a p b q
  | common   == 1        = [crt a p b q]
  | a_offset == b_offset = [i * modulus + offset | i <- [0 .. common - 1]]
  | otherwise            = []
  where
    common = gcd p q
    (a', a_offset) = a `divMod` common
    (b', b_offset) = b `divMod` common
    p' = p `div` common
    q' = q `div` common
    modulus = p'  * q' * common
    offset  = common * crt a' p' b' q' + a_offset

prop_gcrt' a b c = (a `mod` (b * c)) `elem` gcrt' (a `mod` b) b (a `mod` c) c

-- Generalized Chinese Remainder Theorem

gcrt :: Integral a => a -> a -> a -> a -> Maybe (a,a)
gcrt a p b q
  | common   == 1        = Just (crt a p b q, p*q)
  | a_offset == b_offset = Just (offset, modulus)
  | otherwise            = Nothing
  where
    common = gcd p q
    (a', a_offset) = a `divMod` common
    (b', b_offset) = b `divMod` common
    p' = p `div` common
    q' = q `div` common
    modulus = p'  * q' * common
    offset  = common * crt a' p' b' q' + a_offset


-- The Extended Euclidean Algorithm
-- egcd x y = (a, b, gcd x y)
--   where
--     a*x + b*y == gcd x y

egcd :: Integral a => a -> a -> (a,a,a)
egcd x y
	| x <= y     = egcd' (1,0,x) (0,1,y)
	| otherwise  = egcd' (0,1,y) (1,0,x)
	where
		egcd' p (_,_,0) = p
		egcd' (a,b,x) p@(c,d,y) = egcd' p (a - c * q, b - d * q, r)
			where
				(q,r) = x `quotRem` y

-- Greatest Odd Factor
-- gof (2^k * x) = x
-- where
--   not (even x)

gof :: Integral a => a -> a
gof n = head (dropWhile even (iterate (`quot` 2) n))

gofpow :: (Integral a, Num b) => a -> (a, b)
gofpow n = until (odd . fst) (\(x,i) -> (x `quot` 2, i + 1)) (n, 0)

-- Modular Inverse
-- inverse p x = y
-- where
--    x * y `mod` p == 1

inverse :: Integral a => a -> a -> a
inverse p x = inv (0,p) (1, x `rem` p)
	where
		inv (a,gcd) (c,0)
			| gcd == 1    = a
			| otherwise = error ("inverse: inverse of " ++
					     show x ++ " mod " ++ show p ++ " does not exist.")
		inv (a,x) p@(c,y) = inv p (a - c * q, r)
			where
				(q,r) = x `quotRem` y


-- The Miller-Rabin  Strong Pseudoprime test
-- isSPP is very (but not completely) effective at determining composite-ness
-- (isSPP n xs == False)                        implies n is composite.
-- isSPP n (x:xs) == isSPP n [x] && isSPP n xs
-- isSPP n [x] && isSPP [y]                     implies isSPP n [x*y]
-- this example is accurate for 'n' up to 10^13:
-- isSPP n [2, 3, 5, 7, 11]

isSPP :: Integral a => a -> [a] -> Bool
isSPP n bases = n > 1 && and [ i == 1 || f i pow | b <- bases, b /= n, i <- return (expmod b gof n)]
	where
		(gof, pow) = gofpow (n-1)
		f x 0 = False
		f x p
			| x == n-1  = True
			| otherwise = f ((x*x)`rem`n) (p-1)


millerPows b n = take pow (iterate (\x -> x * x `mod` n) (expmod b gof n))
   where
		(gof, pow) = gofpow (n-1)

millerFactor   :: Integral a => [a] -> a -> [(a, a)]
millerFactor bases n = concat [examine (take pow (iterate (\x -> x * x `mod` n) (expmod b gof n))) | b <- bases]
	where
		(gof, pow) = gofpow (n-1)
		examine (x:y:xs)
			| y == n - 1 = []
			| y == 1     = [(gcd (x-1) n,  gcd (x+1) n)]
			| True       = examine (y:xs)
		examine _       = []


splitFactors :: Integral a => [a] -> (a,a) -> [a]
splitFactors [] (a, b) = []
splitFactors (x:xs) (a, b)
  | gcd_x_a == 1 || gcd_x_a == x = x : splitFactors xs (a,b)
  | otherwise   = gcd_x_a : x `quot` gcd_x_a : splitFactors xs (a,b)
    where
      gcd_x_a = gcd x a

factorCarmichael :: Integral a => [a] -> a -> [a]
factorCarmichael ps n = foldl splitFactors [n] (millerFactor ps n)

small_primes = take 10 primes
max_small_prime = last small_primes
max_small_number = max_small_prime * max_small_prime


isPrime n
  | n <= max_small_number = if n <= max_small_prime
                            then elem n small_primes
                            else not (any (\p -> n `mod` p == 0) small_primes)
  | otherwise = not (any (\p -> n `mod` p == 0) small_primes) && isSPP n small_primes


isPrimeSlow :: Integral a => a -> Bool
isPrimeSlow n = all (\d -> n `rem` d /= 0) (2:[3,5..(floor (sqrt (fromIntegral n)))])

-- isPrimRoot :: Integral a => a -> a -> Bool
isPrimRoot p
   | isSPP p (take 10 primes) =
         let
	    tests = map ((p-1) `quot`) (nub (factor (p-1)))
         in
            \n -> all (\t -> expmod n t p /= 1) tests
   | otherwise =
         let
            phi_p = phi p
            tests = map (phi_p `quot`) (nub (factor phi_p))
         in
            \n -> gcd n p == 1 && all (\t -> expmod n t p /= 1) tests

isPrimRoot_factored (p, factors) =
    let
      factored_phi_p = factor_phi_factored factors
      phi_p          = product factored_phi_p
      tests = map (phi_p `quot`) (nub (factored_phi_p))
    in
      \n -> gcd n p == 1 && all (\t -> expmod n t p /= 1) tests

primRoots p = filter (isPrimRoot p) [1..p-1]


fails :: Integer -> [(Integer, Integer)]
-- a subset of the bases that fail the strong pseudo-prime test
fails p =
	[ (b, y) |
		b <- [1..p],
		y <- return (expmod b (gof (p-1)) p),
		y /= 1,
		(y * y) `mod` p == 1   ]

index_carms :: [(Integer, Integer)]
index_carms = map f factored_carmichaels
	where
		f (cn,factors) = (cn, List.genericLength (filter p [1..cn-1]))
			where
				p n = expmod n (gcd (gof (cn-1)) phi) cn == 1
				phi = product (map (\x -> x - 1) factors)


fails' :: Integer -> [(Integer, Integer)]
-- a subset of the bases that fail the strong pseudo-prime test
fails' p =
	[ (b, y) |
		b <- [1..p],
		y <- return (expmod b ((p-1)`quot`2) p), y /= 1,
		(y * y) `mod` p == 1   ]



sqrts :: Integer -> [Integer]
sqrts p = filter (\b -> b * b `mod` p == 1) [1..p]

isPP :: Integral a => a -> a -> Bool
isPP n base = expmod base n n == base

{-
isSPP :: Integral a => a -> a -> Bool
isSPP n base = head powers == 1 || any ((n-1)==) powers
	where
		fact_pow2 (factor, power)
			| even factor = fact_pow2 (factor `quot` 2, power + 1)
			| otherwise   = (factor,power)
		(factor,power) = fact_pow2 (n-1, 0)
		powers = take (power + 1) (iterate (\x -> x * x `rem` n) (expmod base factor n))
-}

covers :: forall a. (Ix a) => (a,a) -> [a] -> Bool
covers (low,high) list = ST.runST (do
	a <- newSTUArray (low, high) False
	Monad.foldM (\() i -> if low <= i && i <= high then writeArray a i True else return ()) () list
	allArray id a)

allArray :: (MArray array elt m, Ix ix) => (elt -> Bool) -> array ix elt -> m Bool
allArray pred array = do
                        bounds <- getBounds array
                        allArray' (range bounds)
   where
	 allArray' []       = return True
         allArray' (ix:ixs) = do
             elt <- MArray.readArray array ix
             if pred elt then allArray' ixs else return False

countArray :: (MArray array elt m, Ix ix, Integral i) => (elt -> Bool) -> array ix elt -> m i
countArray pred array = do
        bounds <- getBounds array
	Monad.foldM
		(\count ix ->
			do
				elt <- MArray.readArray array ix
				if pred elt
					then return $! count + 1
					else return count
		) 0 (range bounds)



-- and [ head ps == 1 || any ((n-1)==) ps | b <- bases, ps <- return (powers b)]
--		powers base = take (power + 1) (iterate (\x -> x * x `rem` n) (expmod base factor n))

-- satFermat :: Integral a => a -> Bool
-- does the argument satisfy the conclusion of Fermat's little theorem?
satFermat p = all (isPP p) [2..p-1]

-- factors :: Integral a => a -> [a]
factors x = factors' (factor x, [1])
-- all the factors of n
	where
		factors' ([],xs) = xs
		factors' (ps,xs) = factors' (ps',[ x * n | x <- xs, n <- (scanl (*) 1 p)])
			where
				(p, ps') = span (head ps ==) ps

-- These are the composite numbers whose multiplicative group of units is cyclic
-- cyclic_groups = [ p | p <- [1..10046], primRoots p /= [] ]
-- observation... these numbers are 2, 4,  2 * p^k, or p^k,
-- obviously these numbers will contain only one square root of one.

printgen n
    = Monad.sequence_
          [ do
	    putStr "<"
	    putStr (show w)
	    putStr "> = "
	    print  (orbit w n)
	  | w <- [1..n-1]
	  , gcd n w == 1 ]

--satKorselt :: Integral a => a -> Bool
-- By Korselt's theorem, satKorselt is the same function as satFermat
satKorselt n
	=   and [ x /= y | (x,y) <- zip factors (tail factors) ]
	 && all (\p -> (n - 1) `rem` (p - 1) == 0) factors
	 where
	   factors = factor n

satKorselt' factors
	=   and [ x /= y | (x,y) <- zip factors (tail factors) ]
	 && all (\p -> (n - 1) `rem` (p - 1) == 0) factors
	 where
	   n = product factors

--isCarmichael, isCarmichael2 :: Integral a => a -> Bool
-- is a number a Carmichael number?
-- the first  tests using Korselt's Theorem (usually faster) and
-- the second tests using the definition directly
isCarmichael n
	=   and [ x /= y | (x,y) <- zip factors (tail factors) ]
	 && all (\p -> (n - 1) `rem` (p - 1) == 0) factors
	 && not (null (tail factors))
	where
		factors = factor n

isCarmichael2 n = satFermat n && not (isPrime n)

primeTrips =
	[ [x,y,z]
	| t <- [1..],
	  [x,y,z] <- return [6 * t + 1, 12 * t + 1, 18 * t + 1],
	  isPrime x && isPrime y && isPrime z                      ]
-- The product of x y and z will be Carmicheal numbers.  This list is believed to be infinite.

carmichaels :: [Integer]
carmichaels = map fst factored_carmichaels

factored_carmichaels :: [(Integer, [Integer])]
factored_carmichaels = (form . parse) (unsafePerformIO (readFile carmichaelsFile))
	where
		parse str = case (reads str) of
			[(pp, str')] -> pp : parse str'
			[]           -> []
		form [] = []
		form (x:xs) = (x,factors) : form rest
			where (factors,rest) = span (< x) xs

-- 561 : 1105 : 1729 : 2465 : 2821 : filter isCarmicheal [3000..]

chain_prime n p
   | n <= 1    = if isPrime p then Just p else Nothing
   | otherwise = if isPrime p then chain_prime (n-1) (2*p+1) else Nothing


summod  n = foldl' (\total bit -> (total + bit) `mod` n) 0
prodmod n = foldl' (\prod  bit -> (prod  * bit) `mod` n) 1

principleRoots :: Integral a => a -> [a]
principleRoots n = [ i | i <- [2..n-1], isPrincipleRoot n i ]

isPrincipleRoot n i
  =  gcd n i == 1
  && summod n (orbit i n) == 0

{-  isPrime p /\ isPrimRoot p n  ->  isPrincipleRoot p n   (obvious)
    isPrimRoot p n -> isPrincipleRoot p n  ?     (observed on p <= 5000)
-}

orbit p n = p : takeWhile (p /=)  (iterate (\x -> x * p `mod` n) (p*p `mod` n))

showStream []  = putStr "[]"
showStream (x:xs) = putStr "[" >> putStr (show x) >> showStream' xs
  where
    showStream' [] = putStr "]"
    showStream' (x:xs) = putStr ", " >> putStr (show x) >> showStream' xs

show_list (x:xs)  = print x >> show_list xs
show_list []      = return ()

distinctEltsInRange :: (Ix a, Integral b) => (a,a) -> [a] -> b
distinctEltsInRange range list = snd (eltStats range list)


eltStats :: forall a b. (Ix a, Integral b) => (a,a) -> [a] -> (b,b)
eltStats (low, high) xs = ST.runST (do
    array  <- newSTUArray (low, high) False
    length <- Monad.foldM (\len i -> markoff array i >> (return $! len + 1)) 0 xs
    count  <- countArray id array
    return (length,count))
  where
    markoff a i
      | low <= i && i <= high   = writeArray a i True
      | otherwise               = return ()


-- Directly Computes the number of residues of an MR function

residues f
--  | symmetric f = \n -> distinctEltsInRange (0, n-1) (map (evalmod f n) [0 .. period f n `div` 2])
  | otherwise   = \n -> distinctEltsInRange (0, n-1) (map (evalmod f n) [0 .. period f n - 1])

qcrCoverDirect n
	= distinctEltsInRange
		(0, n-1)
		(scanl
			(\x y -> (x + y) `mod` n)
			0
			[0.. if even n then n else (n + 1) `div` 2]
		)

qcrCover = product . map qcrCoverPrimePower . factorn

qcrCoverPrimePower (2,k) = 2^k
qcrCoverPrimePower (p,k) = (p^(k+1)) `div` (2 * (p + 1)) + 1

isMultFun f n = f n == (product . map (f . uncurry (^)) . factort) n

deriv n (x:y:xs) = y - n*x : deriv n (y:xs)
deriv n xs = []

splits :: Int -> [a] -> [[a]]
splits n [] = []
splits n xs = take n xs : splits n (drop n xs)

texFactors :: (String -> IO ()) -> [[(Integer, Integer)]] -> IO ()
texFactors pr fs = Monad.mapM_ (\(line@(xs:_)) -> pr (show (product (map (uncurry (^)) xs))) >> pr "&" >> texLine line >> pr " \\\\\n") (splits 10 fs)
  where
    texLine (((p,k):ps):ns) = pr " {" >> pr (show p) >> pr "} ^ {" >> pr (show k) >> pr "} \\cdot " >> texLine (ps:ns)
    texLine ([]:ns) = pr " & " >> texLine ns
    texLine [] = return ()

factort = blookup table
   where
     table = btable factorn

data MR
   = Choose Integer
   | Exp    Integer
   | Sum    MR
   | Diff   MR MR
   | Add    MR MR
   | Mul    MR MR
   | Comp   MR MR
   | Const  Integer
   | Id


period Id         n = n
period (Const _)  n = 1
period (Choose 0) n = 1
period (Choose 1) n = n
period (Choose 2) n = gcd 2 n * n
period (Choose 3) n = gcd 6 n * n
period (Choose c) n = l * kn
   where
      kn = period (Choose (c-1)) n
      s  = evalmod (Choose c) n kn
      l  = n `div` gcd s n
period (Exp c)    n = n
period (Add f g)  n = lcm (period f n) (period g n)
period (Mul f g)  n = lcm (period f n) (period g n)
period (Comp f g) n = period f (period g n)
period (Sum f)    n = l * kn
   where
      kn = period f n
      s  = evalmod (Sum f) n kn
      l  = n `div` gcd s n

eval Id           x = x
eval (Const  c)   x = c
eval (Choose c)   x = choose x c
eval (Exp    c)   x = x^c
eval (Add    f g) x = eval f x + eval g x
eval (Mul    f g) x = eval f x * eval g x
eval (Comp   f g) x = eval f (eval g x)
eval (Sum    f)   x = sum [eval f i | i <- [0..x-1]]

evalmod Id           n x = x `mod` n
evalmod (Const  c)   n x = c `mod` n
evalmod (Choose c)   n x = choose x c `mod` n
evalmod (Exp    c)   n x = expmod x c n
evalmod (Add    f g) n x = (evalmod f n x + evalmod g n x) `mod` n
evalmod (Mul    f g) n x = (evalmod f n x * evalmod g n x) `mod` n
evalmod (Comp   f g) n x = evalmod f n (evalmod g (period f n) x)
evalmod (Sum    f)   n x = summod n [evalmod f n i | i <- [0..x-1]]

data BTable a = Node a (BTable a) (BTable a)


btable :: (Integral a) => (a -> b) -> BTable b
btable f = foo 1 (iterate (2*) 1)
   where
     foo n (p1:ps@(p2:_)) = Node (f n) ((foo $! n+p1) ps) ((foo $! n+p2) ps)

blookup :: (Integral a) => BTable b -> a -> b
blookup (Node b l r) n
   | n == 1 = b
   | even n = blookup l (n `div` 2)
   | True   = blookup r (n `div` 2)

olookup :: (Ord a) => [(a, b)] -> a -> b
olookup ((a,b):abs) ax
  | a <  ax = olookup abs ax
  | a == ax = b

choosepow c p
  | c == 0 = repeat 1
  | c == 1 = [1..]
  | c == 2 = map (\k -> qcrCoverPrimePower (p,k)) [0..]
  | c >= 3 = olookup (table !! (c - 3)) p
  where
    table = [[(p,1:[residues (Choose c) (p^k) | k <- [1..]]) | p <- primes] | c <- [3..]]


exppow c p
  | c == 0 = repeat 1
  | c == 1 = [1..]  | c == 2 = if p == 2 then
               1 : map (\k -> ((2^k) `div` 6) + 2) [1..]
	     else
               1 : map (\k -> qcrCoverPrimePower (p,k)) [1..]
  | c >= 3 = olookup (table !! (c - 3)) p
  where
    table = [[(p,1:[residues (Exp c) (p^k) | k <- [1..]]) | p <- primes] | c <- [3..]]

symmetric :: MR -> Bool
-- This is all wrong!
-- If the function "f" is not symmetric,  i.e.  for some x, n
--       evalmod f n x  /= evalmod f n (n - x)
-- Then "symmetric f" returns false

symmetric Id         = False
symmetric (Const  c) = True
symmetric (Choose c) = even c
symmetric (Exp    c) = even c
symmetric (Add f g)  = symmetric f && symmetric g
symmetric (Mul f g)  = symmetric f && symmetric g
symmetric (Comp f g) = symmetric f || symmetric g

assert :: (a -> Bool) -> a -> Maybe a
assert p x
  | p x       = Just x
  | otherwise = Nothing

choose x y
  | 0 <= y && y <= x = c' x 1 1
  | otherwise        = 0
  where
    lim = min y (x - y)
    c' x y a
      | y > lim   = a
      | otherwise = ((c'  $! (x - 1)) $! (y + 1)) $! ((a * x) `div` y)

checkperiod f n periods
  = [k | p <- [period f n],  k <- [0..p-1],  fk <- [evalmod f n k],  any (\c -> fk /= evalmod f n (k + c*p)) [1..periods]]


resfibt n = blookup table n
  where
    table = btable (resfib (0,1))

resfib start n
  = let
      period = periodfibs start n
     in
      eltStats (0,n-1) period


fibs (a,b) n = fibs
  where
    fibs = mod a n : mod b n : zipWith (\x y -> (x + y) `mod` n) fibs (tail fibs)

periodfibs (a,b) n = takeNLthenN 1 (and . zipWith (==) [a `mod` n, b `mod` n]) 0 (fibs (a,b) n)

periodfibs' (a,b) n = takeNLthenN 1 (and . zipWith (==) [a `mod` n, b `mod` n]) 1 (fibs (a,b) n)


-- fibclasses :: Integer -> [(Integer, Integer)]
fibclasses n = ST.runST (do
    a <- newSTArray myBounds (0,0)
    markout a (tail (range myBounds))
    Monad.filterM (fixedPoint a) (range myBounds))
   where
    myBounds = ((0,0),(n-1,n-1))
    markout a [] = return ()
    markout a (x:xs) = do
       covered <- readArray a x
       if covered /= (0,0) then
            markout a xs
        else let
            period = periodfibs' x n
            list   = zip period (tail period)
          in do
            Monad.mapM_ (\ind -> writeArray a ind x) list
            markout a xs

    fixedPoint a x = do
        mx <- readArray a x
        return (mx == x)


-- Somos-k Sequence

somos k | k < 7 = list
   where
     tn = k `div` 2
     dn = (k - 1) `div` 2
     calc (d:xs) =  sum products `div` d : calc xs
        where
           products = zipWith (*) (reverse (take tn xs)) (drop dn xs)
     list = (take k (repeat 1)) ++ calc list

proddiv = [1,2,3,8,5,36,7,64,27,100,11,1728,13,196,225,1024,17,5832,19,
           8000,441,484,23,331776,125,676,729,21952,29,810000,31,32768,
           1089,1156,1225,10077696,37,1444,1521,2560000,41,3111696,43,
           85184,91125,2116,47]

tseq = [2,2,6,6,10,20,28,46,78,122,198,324,520,842,1366,2206,3570,
           5780,9348,15126,24478,39602,64078,103684,167760,271442,
           439206,710646,1149850,1860500,3010348,4870846,7881198,
           12752042,20633238,33385284,54018520]

choosemod _ 0 p = 1
choosemod 0 _ p = 0
choosemod m n p = (choose (m `mod` p) (n `mod` p) `mod` p
                    * choosemod (m `div` p) (n `div` p) p
                       ) `mod` p

-- altchoose  m n p = foldl' (\x y ->  (x * y)  [ (m' `mod` p) (n' `mod` p) | (m', n')  <- zip (iterate (`div` p) m)  (takeWhile (/= 0) (iterate (`div` p) n)) ]


primesSubset x y
  | x == 1       = True
  | gcd_x_y == 1 = False
  | otherwise    = primesSubset (x `div` gcd_x_y) y
    where
      gcd_x_y = gcd x y


deriv_list f n = map (\p -> take n (deriv p $1:(map (residues f . (p^)) [1..]))) primes


residuesChoose3 n =
     distinctEltsInRange (0,n-1) (f (f [1..period (Choose 3) n]))
   where
     f = scanl (\x y -> (x + y) `mod` n) 0

applyN :: Integral a => a -> (b -> b) -> (b -> b)
applyN n f b
  | n > 0 = applyN (n-1) f (f b)
  | True  = b

residuesChoose k n =
     distinctEltsInRange (0,n-1) (applyN k f [1..period (Choose 3) n])
   where
     f = scanl (\x y -> (x + y) `mod` n) 0

{-
next [x] =

residuesChoose3' n =
    ( distinctEltsinRange (0,n-1)
      . take (period (Choose 3))
      . map fst
      . iterate (\(_,xs) ->
-}

smarandache_squares = 1 : 2 : f (tail smarandache_squares)
  where
    f (x:xs) = x*x + 1 : merge (map (\y -> x*x + y*y) (takeWhile (< x) (tail smarandache_squares))) (f xs)


eltCounts :: (Ix a, Integral b) => (a,a) -> [a] -> Array a b
eltCounts (low, high) xs = ST.runST (do
    array  <- newSTArray (low, high) 0
    length <- Monad.mapM_ (change array) xs
    MArray.unsafeFreeze array)
  where
    change array i | low <= i && i <= high = do
       count <- readArray array i
       writeArray array i $! count + 1
    change _ _ = return ()

base  b x
	=   reverse
	  . map snd
	  . MyList.takeWhileThen ((/=0) . fst) 1
	  . tail
	  . iterate ((`quotRem` b) . fst)
	  $ (x,0)
{-
chooseDistrib row p
	= let
		digits = base p row
		counts = eltCounts digits
		root   = head (primRoots p)
	-}

alternating_residues f g
  = \n -> distinctEltsInRange (0, n-1) (map (evalmod f n) [0 .. period f n - 1] ++ map (evalmod g n) [0..period g n - 1])

cycleZipWith f orig_xs orig_ys = cycle orig_xs orig_ys
  where
    cycle [] [] = []
    cycle xs [] = cycle xs orig_ys
    cycle [] ys = cycle orig_xs ys
    cycle (x:xs) (y:ys) = f x y : cycle xs ys

cycleZip nm = cycleZipWith (\x y -> (x,y)) nm

main = return ()
