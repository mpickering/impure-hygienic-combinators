{-# LANGUAGE TypeOperators, TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}

-- Gibonacci example
-- The code for the talks at FP subgroup seminar, May 13 and 19, 2014

module Gib1 where

import TSCore
import TSCPST
import qualified Control.Monad.State as S
import qualified Data.Map as M
import Control.Monad.Identity
import Control.Applicative
import Data.IORef

-- Unstaged Gibonacci:
--   compute the n-th element of the Fibonacci sequence whose
--   first two elements are x and y
--
-- The code below is contrived and can be written (much) simpler
-- but we stick with it for the sake of the example.

gib :: Int -> Int -> Int -> Int
gib x y n = loop n
 where loop 0 = x
       loop 1 = y
       loop n = loop (n-1) + loop (n-2)

test1 = 8 == gib 1 1 5

-- Staged Gibonacci
-- First, we use the Staging DSL with no effects

gibS :: (SSym repr) => repr Int -> repr Int -> Int -> repr Int
gibS x y n = loop n
 where loop 0 = x
       loop 1 = y
       loop n = (addS `appS` loop (n-1)) `appS` loop (n-2)

gibSn :: (LamPure repr, SSym repr) => Int -> repr (Int -> (Int -> Int))
gibSn n = lamS (\x -> lamS (\y -> gibS x y n))

--  Recall types:
--    lamS :: (repr a -> repr b) -> repr (a->b)
--    lamS (\y -> gibS x y n) :: repr (Int->Int)

test1S = 8 == unR (gibSn 5) 1 1

test2S = runCS (gibSn 5)
-- Generated code shows lots of duplication: x_0 + x_1 appears three times
-- The generated code reveals that the original gib did lots of duplicated
-- work. That's why gib 1 1 30 takes a lot of time

{-
"\\x_0 -> \\x_1 ->
   (GHC.Num.+)
    ((GHC.Num.+)
       ((GHC.Num.+) ((GHC.Num.+) x_1 x_0) x_1)
       ((GHC.Num.+) x_1 x_0))
    ((GHC.Num.+) ((GHC.Num.+) x_1 x_0) x_1)"
-}

-- We need to add memoization. We need an effect: storage for the memo table

type Memo = M.Map Int Int

gibM :: Int -> Int -> Int -> S.State Memo Int
gibM x y n = loop n
 where loop n = do
        memo <- S.get
        case M.lookup n memo of
          Just v   -> return v
          Nothing  -> do
            v <- loop' n
            memo <- S.get               -- It is very easy to overlook this!
                                        -- drop this for an exercise, see what
                                        -- happens
            S.put $ M.insert n v memo
            return v
       loop' 0 = return x
       loop' 1 = return y
       loop' n = do
            v1 <- loop (n-1)
            v2 <- loop (n-2)
            return $ v1 + v2


test5M =  8 == S.evalState (gibM 1 1 5) M.empty
-- check how long it takes to compute gib 1 1 30 without memoization
test30M = 1346269 == S.evalState (gibM 1 1 30) M.empty

-- Staging the memoized code
-- Change the signature (add repr to indicate staging) and then
-- try to type check gibSM. Fix the problems pointed out by the
-- typechecker
type MemoS repr = M.Map Int (repr Int)

gibSM :: SSym repr =>
         repr Int -> repr Int -> Int -> S.State (MemoS repr) (repr Int)
gibSM x y n = loop n
 where loop n = do
        memo <- S.get
        case M.lookup n memo of
          Just v   -> return v
          Nothing  -> do
            v <- loop' n
            memo <- S.get               -- It is very easy to overlook this!
            S.put $ M.insert n v memo
            return v
       loop' 0 = return x
       loop' 1 = return y
       loop' n = do
            v1 <- loop (n-1)
            v2 <- loop (n-2)
            return ((addS `appS` v1) `appS` v2)

gibSMn :: (LamPure repr, SSym repr) => Int -> repr (Int -> (Int -> Int))
gibSMn n = lamS (\x -> lamS (\y -> S.evalState (gibSM x y n) M.empty))

-- But the generated code shows lots of duplication!
-- So, we staged the fast code and obtained the slow code.
-- What went wrong?

gibSM5 = runCS $ gibSMn 5
{-
"\\x_0 -> \\x_1 -> (GHC.Num.+) ((GHC.Num.+) ((GHC.Num.+) ((GHC.Num.+) x_1 x_0) x_1) ((GHC.Num.+) x_1 x_0)) ((GHC.Num.+) ((GHC.Num.+) x_1 x_0) x_1)"
-}

-- Diagnosis: we made the generator run faster rather than the generated code.
-- Although the MemoS table shared the expressions like (x_0 + x_1),
-- when we print the code, we break the sharing and get the exponential
-- explosion.
-- Cure: we need to introduce sharing explicitly in the _generated_ code
-- We need an explicit let

-- See the CPS version in the last half of the present file for the intuition
-- of let-insertion

-- Let's start with the explicit let without memoization
-- The problem with let-insertion is that it is non-compositional
-- The types are all inferred! And the syntax is quite nice.

{- Inferred type
gibSL
  :: (SSym repr, SymLet repr, AppLiftable i0,
      Control.Applicative.Applicative m, Num a, Eq a) =>
     (CPSA (i0 (repr Int)) m :. i0) (repr Int)
     -> (CPSA (i0 (repr Int)) m :. i0) (repr Int)
     -> a
     -> (CPSA (i0 (repr Int)) m :. i0) (repr Int)
-}
gibSL x y n = loop n
 where loop 0 = x
       loop 1 = y
       loop n = genlet (loop (n-1) +: loop (n-2))

-- If we forget resetJ, we get a type error.
-- What does the error message actually say?
gibSLn n = runJCPSA $ lam (\x -> lam (\y ->
                            resetJ $ gibSL (weaken (var x)) (var y) n))

-- The generated code looks like that in the A-normal form
-- Arguments of all applications (additions) are variables.
gibSL5  = runCI $ gibSLn 5
{-
"\\x_0 -> \\x_1 -> let z_2 =
    let z_2 =
      let z_2 =
        let z_2 = (GHC.Num.+) x_1 x_0
        in (GHC.Num.+) z_2 x_1
      in
        let z_3 = (GHC.Num.+) x_1 x_0
        in (GHC.Num.+) z_2 z_3
    in let z_3 = let z_3 = (GHC.Num.+) x_1 x_0
    in (GHC.Num.+) z_3 x_1
    in (GHC.Num.+) z_2 z_3
    in z_2"
 -}

-- Adding memo table

-- At first blush, it seems trivial: just add memo to gibSL
gibF0 x y n = loop n
 where loop n = do
        memo <- S.get
        case M.lookup n memo of
          Just v   -> return v
          Nothing  -> do
            v <- loop' n
            memo <- S.get               -- It is very easy to overlook this!
            S.put $ M.insert n v memo
            return v
       loop' 0 = x
       loop' 1 = y
       loop' n = genlet (loop (n-1) +: loop (n-2))

-- But look at the inferred type, especially the constraint
--   S.MonadState (M.Map k (repr Int)) (CPSA (i0 (repr Int)) m :. i0)


-- First challenge: CPSA w m is not a monad, let alone CPSA w m .: i

-- We can try to get around it (S.put line is commented out!)

gibF1 :: forall repr i m.
        (SSym repr, SymLet repr, AppLiftable i,
         m ~ S.State (M.Map Int (i (repr Int)))) =>
  (CPSA (i (repr Int)) m :. i) (repr Int)
  -> (CPSA (i (repr Int)) m :. i) (repr Int)
  -> Int
  -> (CPSA (i (repr Int)) m :. i) (repr Int)
gibF1 x y n = loop n
 where loop n = J $ CPSA $ \k -> J $ do
        memo <- S.get
        case M.lookup n memo of
          Just v   -> unJ $ throw k (return v)
          Nothing  -> unJ $ unCPSA (unJ (loop' n)) $ \mv ->
            (J $ J $ do
                memo <- S.get
                -- v :: hw (h (i (repr Int)))
                v <- unJ $ unJ mv
                -- S.put $ M.insert n undefined (memo :: (M.Map Int (i (repr Int))))
                return (pure (pure ()))
            ) *> k mv

       loop' 0 = x
       loop' 1 = y
       loop' n = genlet $ loop (n-1) +: loop (n-2)

-- First problem: if we uncomment the S.put line, we get a type problem:
-- what we want to store in the memo table is 'z' bound to 'x+y'.
-- But that 'z' comes into a richer environment. It seems each value
-- in the memo table will have different type. We need sort of heterogeneous
-- map. Even if we had it, it won't work anyway: see below.


-- The error message says that x and y bindings escape. Indeed they are:
-- we can't access the Memo table outside lam, because bindings may
-- escape. See the type of gibF1, especially the part
--   S.State (M.Map Int (i (repr Int)))
-- Here, i is the environment in which gibF1 is run, which is the
-- environment that includes the bindings x and y.
-- The type of gibF1n cannot contain S.State (M.Map Int (i (repr Int)))
-- since otherwise the bindings will escape.
-- So, we need local state!
-- gibF1n n = runJCPSA $ lam (\x -> lam (\y ->
--                             resetJ $ gibF1 (weaken (var x)) (var y) n))



-- ------------------------------------------------------------------------
-- Let's go back the unstaged Gibonacci and be explicit about all the
-- effects. We will use CPS

-- Re-write gib in CPS

gibK0 :: Int -> Int -> Int -> Int
gibK0 x y n = loop n id
 where loop :: Int -> (Int -> w) -> w
       loop 0 k = k x
       loop 1 k = k y
       loop n k = loop (n-1) $ \v1 ->
                  loop (n-2) $ \v2 ->
                  k $ v1 + v2

-- Tests
testK00 = gibK0 1 1 5

-- But the following takes quite a bit of type
testK01 = gibK0 1 1 30


-- To speed-up, we use memoization

gibK1 :: Int -> Int -> Int -> Int
gibK1 x y n = loop n M.empty (\v s -> v)
 where loop :: Int -> Memo -> (Int -> Memo -> w) -> w
       loop n s k = case M.lookup n s of
         Just v  -> k v s
         Nothing -> loop' n s $ \v s ->
           k v $ M.insert n v s

       loop' :: Int -> Memo -> (Int -> Memo -> w) -> w
       loop' 0 s k = k x s
       loop' 1 s k = k y s
       loop' n s k = loop (n-1) s $ \v1 s ->
                     loop (n-2) s $ \v2 s ->
                     k (v1 + v2) s

testK10 = gibK1 1 1 5

-- Now, computing the 30th Gibonacci number is instantaneous
testK11 = gibK1 1 1 30

-- But we don't want to evaluate Gibonacci. Our goal is to generate
-- code for it. Actually, we want to generate efficient code
-- that computes gib x y n for a statically known value of n.

-- First, we change the signature to reflect which arguments
-- of gib are known now (at the generation time), and which
-- will be known later (when the generated code is compiled and the
-- resulting function is applied to some values).
-- After changing the signature, we try to type check the body
-- and fix the problems pointed out by the type checker.
-- There are only few.

gibK2 :: forall repr. SSym repr => repr Int -> repr Int -> Int -> repr Int
gibK2 x y n = loop n M.empty (\v s -> v)
 where loop :: Int -> MemoS repr -> (repr Int -> MemoS repr -> w) -> w
       loop n s k = case M.lookup n s of
         Just v  -> k v s
         Nothing -> loop' n s $ \v s ->
           k v $ M.insert n v s

       loop' :: Int -> MemoS repr -> (repr Int -> MemoS repr -> w) -> w
       loop' 0 s k = k x s
       loop' 1 s k = k y s
       loop' n s k = loop (n-1) s $ \v1 s ->
                     loop (n-2) s $ \v2 s ->
                     k ((addS `appS` v1)  `appS` v2) s

gibK2n :: (LamPure repr, SSym repr) => Int -> repr (Int -> (Int -> Int))
gibK2n n = lamS (\x -> lamS (\y -> gibK2 x y n))

--  Recall types:
--    lamS :: (repr a -> repr b) -> repr (a->b)
--    lamS (\y -> gibS x y n) :: repr (Int->Int)

test1K = 8 == unR (gibK2n 5) 1 1

-- The generated code shows lots of duplication: x_0 + x_1 repeats three times
-- That was the problem we saw with gibSM above

test2K = runCS (gibK2n 5)
{-
"\\x_0 -> \\x_1 -> (GHC.Num.+) ((GHC.Num.+) ((GHC.Num.+) ((GHC.Num.+) x_1 x_0) x_1) ((GHC.Num.+) x_1 x_0)) ((GHC.Num.+) ((GHC.Num.+) x_1 x_0) x_1)"
-}

-- We need let insertion
-- Goal: add let_S somewhere
-- Before: <1+2> -> Memo; retrieve <1+2>; retrieve again <1+2>
-- Want:   let z = <1+2>; <z> -> Memo; retrieve <z>; retrieve again <z>
-- Not:   <let z = 1+2 in z> -> Memo; retrieve <let z = 1+2 in z>
-- Wanted:   <let z = 1+2 ...> outside;  <z> -> Memo; retrieve <z>


gibK3 :: forall repr. (SymLet repr, SSym repr) =>
         repr Int -> repr Int -> Int -> repr Int
gibK3 x y n = loop n M.empty (\v s -> v)
 where loop :: Int -> MemoS repr -> (repr Int -> MemoS repr -> repr Int) -> repr Int
       loop n s k = case M.lookup n s of
         Just v  -> k v s
         Nothing -> loop' n s $ \v s ->
           let_S v $ \z ->
           k z $ M.insert n z s

       loop' :: Int -> MemoS repr -> (repr Int -> MemoS repr -> repr Int) -> repr Int
       loop' 0 s k = k x s
       loop' 1 s k = k y s
       loop' n s k = loop (n-1) s $ \v1 s ->
                     loop (n-2) s $ \v2 s ->
                     k ((addS `appS` v1)  `appS` v2) s

-- Note that the answer-type is no longer w: it is repr Int
-- The continuation is no longer polymorphic in the answer-type:
-- we encountered a control effect.

gibK3n :: (LamPure repr, SSym repr, SymLet repr) => Int -> repr (Int -> (Int -> Int))
gibK3n n = lamS (\x -> lamS (\y -> gibK3 x y n))

test3K = runCS (gibK3n 5)
{-
"\\x_0 -> \\x_1 ->
  let z_2    = x_1
  in let z_3 = x_0
  in let z_4 = (GHC.Num.+) z_2 z_3
  in let z_5 = (GHC.Num.+) z_4 z_2
  in let z_6 = (GHC.Num.+) z_5 z_4
  in let z_7 = (GHC.Num.+) z_6 z_5
  in z_7"
-}
-- Everything works! The mission accomplished
-- (see our PEPM 2006 paper for the CPS version and our JFP 2012 paper
-- for the direct version, using shift)


-- Goal: add printing as we generate the code (e.g., print every cache hit
-- or cache miss (the memo table is like a cache))
-- So, we need to add print somehow
-- With print, the generator cannot have the type repr Int
-- It should be like IO (repr Int)
-- But there is a problem:
-- before
--  lamS (\x -> lamS (\y -> (gibK3 x y n) :: repr Int))
-- now we want IO, so now (gibK3 x y n) :: IO (repr Int)
--  lamS (\x -> lamS (\y -> (gibK3 x y n) :: repr Int))
-- but lamS has the type
--  lamS :: LamPure repr => (repr a -> repr b) -> repr (a -> b)
-- the body of lamS has to be pure: repr b. So, we can't print when generating
-- the body of the function.
-- Maybe we need a combinator with the type
--  lam :: (Monad m, LamPure repr) => (repr a -> m (repr b)) -> m (repr (a -> b))
-- This will solve the problem. But is this a good idea?

-- Suppose we have this combinator, call it
lamI :: (Monad m, LamPure repr) => (repr a -> m (repr b)) -> m (repr (a -> b))
lamI = undefined

-- We can print as we generate code

testI0 :: (SSym repr, LamPure repr) => IO (repr (Int -> Int))
testI0 = lamI (\x -> print "OK" >> return ((addS `appS` x) `appS` (intS 1)))

-- This will generate <\x -> x + 1> and print "OK"

-- but only if we know how to implement lamI ....
-- lamI seems to be what we need

-- But we can also write this code

testBad :: (SSym repr, LamPure repr) => IO (repr Int)
testBad = do
  r <- newIORef (intS 0)
  lamI (\x -> writeIORef r x >> return ((addS `appS` x) `appS` (intS 1)))
  readIORef r

-- What does this code do?
--  we attempted to generate the code <x> with x just a free variable

-- I was writing the code, remembered I need IORef, went to the top of the
-- file, inserted import, and came back. Writing code is discontinuous,
-- code generation is often discontinuous. We need control effects
-- to go back and forth.

-- So, the problem with lamI is that we can type check lots of useful
-- code (like printing trace messages). Unfortunately, we can type check
-- lots of bad code, like testBad.

-- the BIG problem: how to write something like lamI so that only the good
-- code is type checked. We want testIO to type check but testBad give a type error.
-- In our PEPM 2014 paper we solved it.
-- We have the combinator called lam

-- lam :: (Applicative m, AppLiftable i, SSym repr, LamPure repr) =>
--        (forall j. AppLiftable j =>
--         (i :. j) (repr a) -> (m :. (i :. j)) (repr b))
--        -> (m :. i) (repr (a->b))

-- although it sort of looks like the type of lamI: lamI returned m (repr (a->b)
-- and lam returns (m :. i) (repr (a->b))...
-- But 'm' was a monad in lamI; in lam, 'm' is just an Applicative
-- moreover, (m :. i) is in general an Applicative, not a monad.

testL0 :: (SSym repr, LamPure repr) => (IO :. Identity) (repr (Int -> Int))
testL0 = lam (\x -> vr x +: (int 1))

testL0C = runC $ testL0
-- "\\x_0 -> (GHC.Num.+) x_0 1"

testL1 :: (SSym repr, LamPure repr) => (IO :. Identity) (repr (Int -> Int))
testL1 = lam (\x -> liftJ (print "OK") *> (vr x +: (int 1)))

testL1C = runC $ testL1
-- We see the code and we see "OK" printed.  So, now we can do side-effects
-- when generating code


testBad' :: forall repr. (SSym repr, LamPure repr) => (IO :. Identity) (repr Int)
testBad' = J $ do
  r <- newIORef (int 0)
  (unJ (lam (\x -> liftJ(writeIORef r ((int 0):: Identity (repr Int))) *> (vr x +: (int 1))))) :: IO (Identity (repr (Int -> Int)))
  readIORef r

{- But the following gives a type error:

testBad'' :: forall repr. (SSym repr, LamPure repr) => (IO :. Identity) (repr Int)
testBad'' = J $ do
  r <- newIORef _h
  (unJ (lam (\x -> liftJ(writeIORef r x) *> (vr x +: (int 1))))) :: IO (Identity (repr (Int -> Int)))
  return (int 0)
  -- readIORef r
-}

{-
telling that the variable x is escaping...
    Couldn't match expected type ‘a0’
                with actual type ‘(:.) Identity j (repr Int)’
      because type variable ‘j’ would escape its scope
    This (rigid, skolem) type variable is bound by
      a type expected by the context:
        AppLiftable j =>
        (:.) Identity j (repr Int) -> (:.) IO (Identity :. j) (repr Int)
      at /home/oleg/papers/MetaFX/hybrid/Gib1.hs:507:9-62
    Relevant bindings include
      x :: (:.) Identity j (repr Int)
        (bound at /home/oleg/papers/MetaFX/hybrid/Gib1.hs:507:15)
      r :: IORef a0
        (bound at /home/oleg/papers/MetaFX/hybrid/Gib1.hs:506:3)
-}


-- The problem for the next time:
-- We can generate code, and we can print when we generate.
-- Can we print when generating gib code?

-- BIG problem
