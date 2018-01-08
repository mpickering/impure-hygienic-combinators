{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}

-- Code generation with code movements via reference cells

module Anaphora where

import TSCore

import Data.IORef
import Control.Applicative
import Control.Monad (liftM2)

-- We can use STRef, IORef or any other reference cells
-- We chose IORef, as most undisciplined and so posing
-- the most danger for generating bad code.
-- We could have used STRef


-- For the sake of abstraction, we define the following three
-- operations for working with mutable variables
-- In note_ref, |IO| is used as an applicative. However, with_ref
-- really requires |IO| to be a monad. Why?

with_ref :: (Applicative i, m ~ (IO :. i)) => 
            (IORef (Maybe b) -> m (repr a)) -> m (repr a)
with_ref f = J (newIORef Nothing >>= unJ . f)

get_ref :: (Applicative i, m ~ (IO :. i)) => 
           IORef (Maybe (m (repr b))) -> m (repr b)
get_ref r = J (readIORef r >>= (\ (Just v) -> unJ v))

-- Store the code value, and return it too
note_ref :: (Applicative i, m ~ (IO :. i)) => 
            IORef (Maybe (m (repr a))) -> m (repr a) -> m (repr a)
note_ref r m = liftJ (writeIORef r (Just m)) *> m

-- Illustrating why creating IORef requires monadic, not just applicative
-- effects
tioref1 :: SSym repr => IO (IORef (repr Int))
tioref1 = newIORef (intS 1)

-- Lift to the generating applicative (IO . i)
tioref2 :: (SSym repr, Applicative i) => (IO :. i) (IORef (repr Int))
tioref2 = liftJ $ newIORef (intS 1)

-- But how to read from the cell? The only operation to read from
-- the cell is readIORef, and the only way to apply it, using
-- applicative interface, is
tioref3 :: (SSym repr, Applicative i) => (IO :. i) (IO (repr Int))
tioref3 = readIORef <$> tioref2

-- What we need however is (IO :. i) (repr Int), the code generator
-- for Int code

-- Faulty attempt
tioref3' = join . tr $ tioref3
 where
   tr :: Applicative i =>
         (IO :. i) (IO (repr Int)) -> (IO :. i) ((IO :. i) (repr Int))
   tr = fmap liftJ
   join :: (IO :. i) ((IO :. i) (repr Int)) -> ((IO :. i) (repr Int))
   join = undefined -- No way to implement it in general, since
                    -- (IO :. i) is not a monad

-- The working attempt
tiorefWith :: (SSym repr, Applicative i) =>
   a -> (IORef a -> (IO :. i) (repr w)) -> (IO :. i) (repr w)
tiorefWith v k = J $ do
  r <- newIORef v
  unJ $ k r

tioref4 :: (SSym repr, Applicative i) => (IO :. i) (repr Int)
tioref4 = tiorefWith (intS 1) $ \r -> J $ do
  v <- readIORef r
  return $ pure v

tioref5 :: (LamPure repr, SSym repr, AppLiftable i) =>
           (IO :. i) (repr (Int -> Int -> Int))
tioref5 =
  lam (\x ->
     tiorefWith x (\r -> 
      lam (\y -> var y +: (weaken . J $ readIORef r))))

tioref5C = fmap ("\\x_0 -> \\x_1 -> (GHC.Num.+) x_1 x_0" ==) $ runC tioref5

-- Atempting to leak the binding of x leads to  type error
{-
tioref6 =
  lam (\x ->
     tiorefWith x (\r -> 
      lam (\y -> var y +: (weaken . J $ do
                           v <- readIORef r
                           writeIORef r y
                           return v))))
-}
{-
/home/oleg/papers/MetaFX/hybrid/Anaphora.hs:95:41:
    Occurs check: cannot construct the infinite type: i ~ i :. j
    Expected type: (:.) i j (repr Int)
      Actual type: (:.) (i :. j) j1 (repr Int)
    Relevant bindings include
      v :: (:.) i j (repr Int)
        (bound at /home/oleg/papers/MetaFX/hybrid/Anaphora.hs:94:28)
      y :: (:.) (i :. j) j1 (repr Int)
        (bound at /home/oleg/papers/MetaFX/hybrid/Anaphora.hs:93:13)
      r :: IORef ((:.) i j (repr Int))
        (bound at /home/oleg/papers/MetaFX/hybrid/Anaphora.hs:92:21)
      x :: (:.) i j (repr Int)
        (bound at /home/oleg/papers/MetaFX/hybrid/Anaphora.hs:91:9)
      tioref6 :: (:.) IO i (repr (Int -> Int -> Int))
        (bound at /home/oleg/papers/MetaFX/hybrid/Anaphora.hs:90:1)
    In the second argument of ‘writeIORef’, namely ‘y’
    In a stmt of a 'do' block: writeIORef r y
-}

{-
    Couldn't match expected type 'a0'
                with actual type '(:.) i j (repr Int)'
      because type variable 'j' would escape its scope
    This (rigid, skolem) type variable is bound by
      a type expected by the context:
        AppLiftable j =>
        (:.) i j (repr Int) -> (:.) IO (i :. j) (repr Int)
    Relevant bindings include
      x :: (:.) i j (repr Int)
        (bound at /home/oleg/papers/MetaFX/hybrid/Anaphora.hs:75:15)
      r :: IORef a0
        (bound at /home/oleg/papers/MetaFX/hybrid/Anaphora.hs:74:3)
    In the second argument of 'writeIORef', namely 'x'
-}


an1 = with_ref (\r -> (note_ref r (int 1)) +: get_ref r)

-- Store open code
an2 = lam (\x -> with_ref (\r -> (note_ref r (var x)) +: get_ref r))

-- store open code and let the effect cross the binder
an3 = lam (\x -> with_ref (\r -> 
          lam (\y -> weaken (note_ref r (var x)) +: var y) $$ get_ref r))

-- Attempting to leak a variable
{-
an4 = lam (\x -> with_ref (\r -> 
          lam (\y -> (note_ref r (var y)) +: var y)))
    Couldn't match type `b0' with `(:.) IO ((i :. j) :. j1) (repr Int)'
      because type variable `j1' would escape its scope
    This (rigid, skolem) type variable is bound by
      a type expected by the context:
        AppLiftable j1 =>
        (:.) (i :. j) j1 (repr Int) -> (:.) IO ((i :. j) :. j1) (repr Int)
    The following variables have types that mention b0
      r :: IORef (Maybe b0) (bound at /home/oleg/temp/Anaphora.hs:48:29)
    Expected type: IORef (Maybe ((:.) IO ((i :. j) :. j1) (repr Int)))
      Actual type: IORef (Maybe b0)
    In the first argument of `lam', namely
      `(\ y -> (note_ref r (var y)) +: var y)'
    In the expression: lam (\ y -> (note_ref r (var y)) +: var y)
    In the first argument of `with_ref', namely
      `(\ r -> lam (\ y -> (note_ref r (var y)) +: var y))'
-}

an1r = fmap (2 == ) $ runR an1

an1c = fmap ("(GHC.Num.+) 1 1" ==) $ runC an1


an2r = fmap (42 == ) . fmap ($ 21) $ runR an2

an2c = fmap ("\\x_0 -> (GHC.Num.+) x_0 x_0" ==) $ runC an2

an3r = fmap (42 == ) . fmap ($ 21) $ runR an3

an3c = fmap ("\\x_0 -> (\\x_1 -> (GHC.Num.+) x_0 x_1) x_0" ==) $ runC an3

-- Illustrating why we need to precisely annotate code types
-- with the variables that may be free in the corresponding code values.

writeGood :: (SSym repr, LamPure repr, AppLiftable i) =>
             (IO :. i) (repr (Int -> Int))
writeGood = lam (\x ->
  J $ do
    r <- newIORef (int 0)
    c <- unJ $ lam (\y -> J $ do
                       writeIORef r $ var x +: int 2
                       return $ int 1)
    z <- readIORef r
    unJ $ (var c $$ z)
  )

twriteGood =
  fmap ("\\x_0 -> (\\x_1 -> 1) ((GHC.Num.+) x_0 2)" ==) $
  runC writeGood

-- Does not type-check
{-
writeBad :: (SSym repr, LamPure repr, AppLiftable i) =>
             (IO :. i) (repr (Int -> Int))
writeBad = lam (\x ->
  J $ do
    r <- newIORef (int 0)
    c <- unJ $ lam (\y -> J $ do
                       writeIORef r (var y)
                       return $ int 1)
    z <- readIORef r
    unJ $ (var c $$ z)
  )
-}

-- Assertion insertion
-- A simpler version of the example from our PEPM09 paper

guarded_div1 :: (Applicative m, SSym repr, SymDIV repr, AssertPos repr) =>
     m (repr Int) -> m (repr Int) -> m (repr Int)
guarded_div1 x y = assertPos y (x /: y)

-- A supposedly complex computation
complex_exp :: (Applicative m, SSym repr) => m (repr Int)
complex_exp = int 100 *: int 200


exdiv1 = lam (\y -> complex_exp +: guarded_div1 (int 10) (var y))

exdiv1c = 
 "\\x_0 -> (GHC.Num.+) ((GHC.Num.*) 100 200) "++
 "(GHC.Base.assert (x_0 GHC.Classes.> 0) (GHC.Real.div 10 x_0))"
 == runCI exdiv1


-- Assertion-insertion locus
-- Generate the code and then apply the transformer being
-- accumulated in the reference cell
{-
assert_locus :: (m ~ (IO :. i), Applicative i) =>
  (IORef (m (repr a -> repr a)) -> m (repr a)) -> m (repr a)
assert_locus fm = J (newIORef (pure id) >>= unJ . go)
  where
  go assert_code_ref = 
      (\x f -> f x) <$> fm assert_code_ref <*> 
                         (J (readIORef assert_code_ref >>= unJ))
-}

assert_locus :: (m ~ (IO :. i), Applicative i) =>
  (IORef (m (repr a) -> m (repr a)) -> m (repr a)) -> m (repr a)
assert_locus f = J $ do
  assert_code_ref <- newIORef id
  mv <- unJ $ f assert_code_ref
  transformer <- readIORef assert_code_ref
  unJ $ transformer (var mv)

-- Add the code transformer, to apply to the result of the generation
add_assert :: (Applicative m, m' ~ (IO :. i), Applicative i) =>
   IORef (m a -> m a) -> (m a -> m a) -> m' ()
add_assert locus transformer =
  liftJ $ modifyIORef locus ( . transformer)

guarded_div2 :: (m ~ (IO :. i), Applicative i, 
                 SSym repr, AssertPos repr, SymDIV repr) =>
     IORef (m (repr a) -> m (repr a))
     -> m (repr Int) -> m (repr Int) -> m (repr Int)
guarded_div2 locus x y = 
    add_assert locus (assertPos y) *> x /: y

exdiv2 = lam (\y -> assert_locus $ \locus ->
       complex_exp +: guarded_div2 locus (int 10) (var y))


exdiv2c = 
    fmap ("\\x_0 -> GHC.Base.assert (x_0 GHC.Classes.> 0) "++
    "((GHC.Num.+) ((GHC.Num.*) 100 200) (GHC.Real.div 10 x_0))" ==) $
    runC exdiv2


guarded_div3 :: (m' ~ (IO :. i), Applicative i, SSym repr, 
                 AssertPos repr, Extends m m', SymDIV repr) =>
     IORef (m (repr a) -> m (repr a))
     -> m' (repr Int) -> m (repr Int) -> m' (repr Int)
guarded_div3 locus x y =
    add_assert locus (assertPos y) *>
    x /: weakens y

exdiv2' = lam (\y -> assert_locus $ \locus ->
       complex_exp +: 
         guarded_div3 locus (int 10) (vr y))

exdiv2c' = 
    fmap ("\\x_0 -> GHC.Base.assert (x_0 GHC.Classes.> 0) "++
    "((GHC.Num.+) ((GHC.Num.*) 100 200) (GHC.Real.div 10 x_0))" ==) $
    runC exdiv2'


exdiv3 = lam (\y -> assert_locus $ \locus ->
     lam (\x ->
       complex_exp +: 
         guarded_div3 locus (vr x) (vr y)))


exdiv3c = 
    fmap ("\\x_0 -> GHC.Base.assert (x_0 GHC.Classes.> 0) "++
   "(\\x_1 -> (GHC.Num.+) ((GHC.Num.*) 100 200) (GHC.Real.div x_1 x_0))"
    ==) $
    runC exdiv3

-- If we make a mistake and attempt to leak a binding
{-
exdiv3f = lam (\x -> assert_locus $ \locus ->
     lam (\y ->
       complex_exp +: 
         guarded_div3 locus (vr x) (vr y)))

-}
{-
/home/oleg/papers/MetaFX/hybrid/Anaphora.hs:238:43:
    Could not deduce (Extends
                        (IO :. ((i :. j) :. j1)) (IO :. (i :. j)))
      arising from a use of 'vr'
    In the third argument of 'guarded_div3', namely '(vr y)'
-}

-- Moving from differently nested environments

exdiv4 = lam (\y -> assert_locus $ \locus ->
     lam (\x ->
       complex_exp +: 
         guarded_div3 locus (var x) (var y)) $$
     complex_exp +: guarded_div3 locus (int 5) (var y +: int (-1)))

exdiv4c = 
    fmap ("\\x_0 -> GHC.Base.assert (x_0 GHC.Classes.> 0) "++
    "(GHC.Base.assert ((GHC.Num.+) x_0 (-1) GHC.Classes.> 0) "++
    "((\\x_1 -> (GHC.Num.+) ((GHC.Num.*) 100 200) "++
          "(GHC.Real.div x_1 x_0)) "++
    "((GHC.Num.+) ((GHC.Num.*) 100 200) "++
    "(GHC.Real.div 5 ((GHC.Num.+) x_0 (-1))))))" ==) $
    runC exdiv4

main = foldr (liftM2 (&&)) (return True) [
       an1r, an1c,
       an2r, an2c,
       an3r, an3c,
       tioref5C,
       twriteGood,
       return exdiv1c,
       exdiv2c, exdiv2c',
       exdiv3c,
       exdiv4c
       ]
