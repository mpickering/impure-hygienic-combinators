{-# LANGUAGE NoMonomorphismRestriction, FlexibleContexts, TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- The faulty power generation, see the warm-up section

module TSPower where

import TSCore
import Control.Applicative

-- an example with nested lambdas
exS2 :: (SSym repr, LamPure repr) => repr (Int->Int->Int)
exS2 = lamS(\x -> lamS (\y -> addS `appS` x `appS` y))
exS2c = "\\x_0 -> \\x_1 -> (GHC.Num.+) x_0 x_1" == runCS exS2


-- The regular, cliche power
-- It is partial, as usual
power :: Int -> Int -> Int
power 0 x = 1
power n x = x * power (n-1) x

power27 = 128 == power 7 2

-- staged power, specialized to n
--   present stage: Haskell
--   future stage: our EDSL
-- Since the present stage is Haskell, we get to use the nice
-- pattern-matching and built-in recursion

spower :: SSym repr => Int -> repr Int -> repr Int
spower 0 x = intS 1
spower n x = mulS `appS` x `appS` spower (n-1) x


-- Specialize to the known n
-- The signature has been inferred
spowern :: (SSym repr, LamPure repr) =>
     Int -> repr (Int -> Int)
spowern n = lamS (spower n)

spower7 = spowern 7

spower72_r = 128 == unR spower7 2

spower7_c =
 "\\x_0 -> (GHC.Num.*) x_0 ((GHC.Num.*) x_0 ((GHC.Num.*) x_0 " ++
    "((GHC.Num.*) x_0 ((GHC.Num.*) x_0 " ++
    "((GHC.Num.*) x_0 ((GHC.Num.*) x_0 1))))))"
    == runCS spower7

-- However:

spower1_c = runCS (spowern (-1))
-- Non-termination!

-- Faulty power

type ErrMsg = String

-- The explicit version
powerF' :: Int -> Int -> Either ErrMsg Int
powerF' 0 x = Right 1
powerF' n x | n > 0 = fmap (x *) (powerF' (n-1) x)
powerF' _ _ = Left "negative exponent"

powerF :: (ErrT m ~ ErrMsg, ErrorA m) => Int -> Int -> m Int
powerF 0 x = pure 1
powerF n x | n > 0 = fmap (x *) (powerF (n-1) x)
powerF _ _ = throwA "negative exponent"

powerFr1 = (Right 128 ==) $ powerF 7 2
powerFr2 = (Left "negative exponent" ==) $ powerF (-1) 2

-- staged, as before

-- The more explicit version
spowerF' :: (SSym repr) =>
     Int -> repr Int -> Either ErrMsg (repr Int)
spowerF' 0 x = Right (intS 1)
spowerF' n x | n > 0 = fmap (mulS `appS` x `appS`) (spowerF' (n-1) x)
spowerF' _ _ = Left "negative exponent"

-- The version with syntactic sugar
spowerF :: (SSym repr, ErrT m ~ ErrMsg, ErrorA m) =>
     Int -> m (repr Int) -> m (repr Int)
spowerF 0 x = int 1
spowerF n x | n > 0 = x *: spowerF (n-1) x
spowerF _ _ = throwA "negative exponent"

-- But the following won't type!
-- spowerFn n = lamS (\x -> spowerF n x)

-- future-stage function
spowerFn :: (LamPure repr, SSym repr, AppLiftable i, ErrorA m,
             ErrT m ~ String) =>
     Int -> (m :. i) (repr (Int -> Int))
spowerFn n = lam (spowerF n . var)

-- The `negative exponent' error is reported when the specialization
-- is performed -- not when the function is applied!
test_spowerF n =
    case runR $ spowerFn n of
      Left e  -> Left (e::String)
      Right f -> Right (f 2, f 3)

tsp1 = Right (128,2187) == test_spowerF 7

tsp2 = Left "negative exponent" == test_spowerF (-1)

tsp1c =
   Right ("\\x_0 -> (GHC.Num.*) x_0 ((GHC.Num.*) x_0 "++
          "((GHC.Num.*) x_0 ((GHC.Num.*) x_0 ((GHC.Num.*) x_0 "++
    "((GHC.Num.*) x_0 ((GHC.Num.*) x_0 1))))))")
   == runC (spowerFn 7)
tsp2c = Left "negative exponent" == runC (spowerFn  (-1))
