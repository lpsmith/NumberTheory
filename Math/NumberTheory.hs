{-# LANGUAGE BangPatterns  #-}
{-# LANGUAGE PatternGuards #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Math.NumberTheory
-- Copyright   :  (c) 2000-2010 Leon P Smith
-- License     :  BSD3
--
-- Maintainer  :  leon@melding-monads.com
-- Stability   :  experimental
-- Portability :  BangPatterns, PatternGuards
--
-----------------------------------------------------------------------------

module Math.NumberTheory where

-- | Modular exponentiation:  @'modexp' n a b@ computes @a ^ b `mod` n@.
-- Handles negative exponents, although an exception is thrown if the
-- modular inverse doesn't exist.  Arguments of type 'Integer' are recommended,
-- this implementation can overflow and arrive at an incorrect answer if
-- arbitrary precision 'Integer's are not used.

{-# SPECIALIZE modexp :: Integer -> Integer -> Integer -> Integer #-}
modexp :: Integral a => a -> a -> a -> a
modexp n a b = maybe (error msg) id (safeModexp n a b)
  where
    msg = "Math.NumberTheory.modexp:  modular inverse does not exist"


-- | Modular Exponentiation:  @'safeModexp' n a b@ returns 'Nothing' if the
-- exponent @b@ is negative and the modular inverse doesn't exist.  Otherwise,
-- it returns @'Just' ('modexp' n a b)@

{-# SPECIALIZE safeModexp :: Integer -> Integer -> Integer -> Maybe Integer #-}
safeModexp :: Integral a => a -> a -> a -> Maybe a
safeModexp n a b
    | b >= 0                     =  loop a b 1
    | Just a' <- safeModinv n a  =  loop a' (-b) 1
    | otherwise                  =  Nothing
  where
    loop !a !b !c
      | b == 0    = if c <= 0 then Just $! c + n else Just c
      | even b    = loop (a*a `rem` n) (b `quot` 2) c
      | otherwise = loop (a*a `rem` n) (b `quot` 2) (a*c `rem` n)


-- | The Chinese Remainder Theorem

crt :: Integral a => a -> a -> a -> a -> a
crt m n 
  = case safeModinv m n of
      Nothing  -> error "Math.NumberTheory.crt:  moduli are not coprime"
      Just n'  -> \a b -> let t = (a - b) * n' `mod` m
                           in b + n * t 

safeCrt :: Integral a => a -> a -> a -> a -> Maybe a
safeCrt m n
  = case safeModinv m n of
      Nothing  -> \_ _ -> Nothing
      Just n'  -> \a b -> let t = (a - b) * n' `mod` m
                           in Just (b + n * t)

-- | Generalized Chinese Remainder Theorem

-- FIXME:  if this function is worth keeping around,  the implementation
-- can be improved. 
gcrt :: Integral a => a -> a -> a -> a -> [a]
gcrt p q a b
  | common   == 1        = [crt p q a b]
  | a_offset == b_offset = [i * modulus + offset | i <- [0 .. common - 1]]
  | otherwise            = []
  where
    common = gcd p q
    (a', a_offset) = a `divMod` common
    (b', b_offset) = b `divMod` common
    p' = p `div` common
    q' = q `div` common
    modulus = p'  * q' * common
    offset  = common * crt p' q' a' b' + a_offset

-- | The Extended Euclidean Algorithm
-- @
-- egcd x y = (a, b, gcd x y)
--   where
--     a*x + b*y == gcd x y
-- @
egcd :: Integral a => a -> a -> (a,a,a)
egcd x y
    | x <= y     = loop (1,0,x) (0,1,y)
    | otherwise  = loop (0,1,y) (1,0,x)
  where
    loop p         (_ ,_ , 0) = p
    loop (a,b,x) p@(!c,!d,!y) = loop p (a - c*q, b - d*q, r)
      where (q,r) = x `quotRem` y


modinv :: Integral a => a -> a -> a
modinv n a = maybe (error msg) id (safeModinv n a)
  where
    msg = "Math.NumberTheory.modinv:  modular inverse does not exist"

safeModinv :: Integral a => a -> a -> Maybe a
safeModinv n a = loop (0,n) (1, a `rem` n)
  where
    loop (a,gcd) (c,0)
      | gcd == 1  = Just a
      | otherwise = Nothing
    loop (a,x) p@(!c,!y) = loop p (a - c*q, r)
      where (q,r) = x `quotRem` y
