{-# LANGUAGE TypeOperators, TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}

-- Gibonacci example

module Gib where

import TSCore
import TSCPST
import qualified Control.Monad.State as S
import qualified Data.Map as M
-- import Control.Monad.Identity
import Control.Applicative

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
-- try to typecheck gibSM. Fix the problems pointed out by the
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
-- environment that incluides the bindings x and y.
-- The type of gibF1n cannot contain S.State (M.Map Int (i (repr Int)))
-- since otherwise the bindings will escape.
-- So, we need local state!
-- gibF1n n = runJCPSA $ lam (\x -> lam (\y ->
--                             resetJ $ gibF1 (weaken (var x)) (var y) n))


get :: S.MonadState s m => CPSA w m s
get = undefined
put :: S.MonadState s m => s -> CPSA w m ()
put = undefined

bindCPSA :: Applicative i =>
            CPSA m w a -> (i a -> CPSA m w (i b)) -> CPSA m w (i b)
bindCPSA = undefined

-- state changes in s2 are disregarded
mapState ::
  (s1 -> s2) -> S.State (M.Map Int s2) a -> S.State (M.Map Int s1) a
mapState f m2 = S.state $ \s1 -> (S.evalState m2 (M.map f s1), s1)

-- mapCPSA :: CPSA m1 w a -> CPSA m2 w a
-- mapCPSA cm1 = CPSA $ \k ->

{-
gibF :: forall repr i m.
        (SSym repr, SymLet repr, AppLiftable i,
         m ~ S.State (M.Map Int (i (repr Int)))) =>
  (CPSA (i (repr Int)) m :. i) (repr Int)
  -> (CPSA (i (repr Int)) m :. i) (repr Int)
  -> Int
  -> (CPSA (i (repr Int)) m :. i) (repr Int)
gibF x y n = loop n
 where loop n = J $ CPSA $ \k -> J $ do
        memo <- S.get
        case M.lookup n memo of
          Just v   -> unJ $ throw k (return v)
          Nothing  -> unJ $ unCPSA (unJ (loop' n)) $ \mv ->
            J $ J $ do
                memo <- S.get
                -- v :: hw (h (i (repr Int)))
                v <- unJ $ unJ mv
                S.put $ M.insert n v memo
                mapState undefined (unJ (unJ (k mv)))

       loop' 0 = x
       loop' 1 = y
       loop' n = genlet $ loop (n-1) +: loop (n-2)


-- The error message says that x and y bindings escape. Indeed they are:
-- we can't access the Memo table outside lam, because bindings may
-- escape. So, we need local state!
-- gibFn n = runJCPSA $ lam (\x -> lam (\y ->
--                             resetJ $ gibF (weaken (var x)) (var y) n))

-- gibF5  = runCI $ gibFn 5

Need indexed Applicative (parameterized Applicative)?
Or need generalized CPSA
  (forall m'. (m->m',m'->m) -> (m' a -> m' w)) -> m w

data T repr i where
  TN :: M.Map Int (i (repr Int)) -> T repr i
  TS :: M.Map Int (j (i (repr Int))) -> T repr i -> T repr (j i)
-}

-- Try an explicit pure version first, then generalize

gibK0 :: Int -> Int -> Int -> Int
gibK0 x y n = loop M.empty n (\v s -> v)
 where
   loop s 0 k = k x s
   loop s 1 k = k y s
   loop s n k = loop s (n-1) $ \v1 s ->
                loop s (n-2) $ \v2 s ->
                k (v1+v2) s

tk0 = 8 == gibK0 1 1 5

gibK1 :: (SSym repr) => repr Int -> repr Int -> Int -> repr Int
gibK1 x y n = loop M.empty n (\v s -> v)
 where
   loop s 0 k = k x s
   loop s 1 k = k y s
   loop s n k = loop s (n-1) $ \v1 s ->
                loop s (n-2) $ \v2 s ->
                k ((addS `appS` v1) `appS` v2) s

gibK1n n = lamS (\x -> lamS (\y -> gibK1 x y n))
t1n = runCS $ gibK1n 5
-- The same as before
{-
"\\x_0 -> \\x_1 -> (GHC.Num.+) ((GHC.Num.+) ((GHC.Num.+) ((GHC.Num.+) x_1 x_0) x_1) ((GHC.Num.+) x_1 x_0)) ((GHC.Num.+) ((GHC.Num.+) x_1 x_0) x_1)"
-}

gibK2 :: (SSym repr) => repr Int -> repr Int -> Int -> repr Int
gibK2 x y n = loop M.empty n (\v s -> v)
 where
   loop s n k = case M.lookup n s of
     Just v  -> k v s
     Nothing -> loop' s n $ \v s ->
        k v (M.insert n v s)

   loop' s 0 k = k x s
   loop' s 1 k = k y s
   loop' s n k = loop s (n-1) $ \v1 s ->
                 loop s (n-2) $ \v2 s ->
                 k ((addS `appS` v1) `appS` v2) s

gibK2n n = lamS (\x -> lamS (\y -> gibK2 x y n))
t2n = runCS $ gibK2n 5
-- As before: speeding the generator

-- Let's try let-insertion, using pure let_S for now

gibK3 :: (SSym repr, SymLet repr) =>
         repr Int -> repr Int -> Int -> repr Int
gibK3 x y n = loop M.empty n (\v s -> v)
 where
   loop s n k = case M.lookup n s of
     Just v  -> k v s
     Nothing -> loop' s n $ \v s ->
        let_S v $ \z ->
        k z (M.insert n z s)

   loop' s 0 k = k x s
   loop' s 1 k = k y s
   loop' s n k = loop s (n-1) $ \v1 s ->
                 loop s (n-2) $ \v2 s ->
                 k ((addS `appS` v1) `appS` v2) s

gibK3n n = lamS (\x -> lamS (\y -> gibK3 x y n))
t3n = runCS $ gibK3n 5
-- As desired
{-
"\\x_0 -> \\x_1 -> let z_2 = x_1\n                 in let z_3 = x_0\n                     in let z_4 = (GHC.Num.+) z_2 z_3\n                         in let z_5 = (GHC.Num.+) z_4 z_2\n                             in let z_6 = (GHC.Num.+) z_5 z_4\n                                 in let z_7 = (GHC.Num.+) z_6 z_5\n                                     in z_7"
-}

-- But let_S and lamS are useable only with the pure code. What if we want
-- to print a trace? (or move the code beyond the binder)

gibK4 :: (SSym repr, SymLet repr, Applicative m) =>
         m (repr Int) -> m (repr Int) -> Int -> m (repr Int)
gibK4 x y n = loop M.empty n (\v s -> v)
 where
   loop s n k = case M.lookup n s of
     Just v  -> k v s
     Nothing -> loop' s n $ \v s ->
        k v (M.insert n v s)

   loop' s 0 k = k x s
   loop' s 1 k = k y s
   loop' s n k = loop s (n-1) $ \v1 s ->
                 loop s (n-2) $ \v2 s ->
                 k (v1 +: v2) s

-- Add tracing, for cache hits

-- Can no longer use the single map
{-
gibK4' :: (SSym repr, SymLet repr, Applicative m) =>
         m (repr Int) -> m (repr Int) -> Int -> m (repr Int)
gibK4' x y n = loop M.empty n (\v s -> v)
 where
   loop s n k = case M.lookup n s of
     Just v  -> k v s
     Nothing -> loop' s n $ \v s ->
        let_ v $ \z ->
        k z (M.insert n z s)

   loop' s 0 k = k x s
   loop' s 1 k = k y s
   loop' s n k = loop s (n-1) $ \v1 s ->
                 loop s (n-2) $ \v2 s ->
                 k (v1 +: v2) s
-}

{-
gibK5 :: forall m repr i0.
         (SSym repr, SymLet repr, Applicative m, Applicative i0) =>
         (m :. i0) (repr Int) -> (m :. i0) (repr Int) -> Int ->
         (m :. i0) (repr Int)
gibK5 x y n = loop M.empty n (\v s -> v)
 where
   loop :: forall i. (Extends i0 i) =>
            M.Map Int ((m :. i) (repr Int)) -> Int ->
            (forall j. Extends i j =>
             (m :. j) (repr Int) -> M.Map Int ((m :. j) (repr Int)) ->
             (m :. j) (repr Int)) -> (m :. i) (repr Int)
   loop s n k = case M.lookup n s of
     Just v  -> k (weakens v) undefined
     Nothing -> loop' undefined n $ \v s ->
        let_ v $ \z ->
        undefined -- k z undefined -- (M.insert n z undefined)

   -- Subtle answer-type modification
   loop' :: forall i. (Extends i0 i) =>
            M.Map Int ((m :. i) (repr Int)) -> Int ->
            ((forall j. Extends i j =>
              (m :. j) (repr Int) -> M.Map Int ((m :. j) (repr Int)) ->
              (m :. j) (repr Int)) ->
             (m :. i) (repr Int))
   loop' s 0 k = k (weakensJ x) s
   loop' s 1 k = k (weakensJ y) s
   loop' s n k = loop s (n-1) $ \ (v1 :: (m :. j) (repr Int)) s ->
                 let tr = (trans (undefined :: (m :. i0) (repr Int))
                                       (undefined :: (m :. i) (repr Int)))
                     s' = M.map tr s
                     v1' = tr v1 in
                 J . fmap unTr . unJ $ loop s' (n-2) $ \ (v2 :: (m :. j1) (repr Int)) s ->
                 let v1'' = weakensJ v1'
                     v = v1'' +: v2
                     v' = trans (undefined :: (m :. i) (repr Int)) v1 v
                 in J . fmap unTr . unJ $ k v' undefined
-}

weakensJ:: (Functor m, Extends i j) => (m :. i) a -> (m :. j) a
weakensJ = J . fmap weakens . unJ

{-
trans:: forall m i j0 j a. (Functor m, Extends i j0, Extends j0 j) =>
        (m :. i) a -> (m :. j0) a -> (m :. j) a -> (m :. Tr i j0 j) a
trans _ _ = J . fmap (\x -> Tr x :: Tr i j0 j a)  . unJ
-}


gibL1 :: (SSym repr, SymLet repr, Applicative m0, AppLiftable i,
         m ~ (CPSA (i (repr Int)) m0)) =>
         (m :. i) (repr Int) -> (m :. i) (repr Int) -> Int ->
         (m :. i) (repr Int)
gibL1 x y n = loop n
 where loop 0 = x
       loop 1 = y
       loop n = genlet (loop (n-1) +: loop (n-2))

{-
gibL2 :: (SSym repr, SymLet repr, Applicative m0, AppLiftable i,
         m ~ (CPSA (i (repr Int)) m0)) =>
         (m :. i) (repr Int) -> (m :. i) (repr Int) -> Int ->
         (m :. i) (repr Int)
gibL2 x y n = loop M.empty n
 where loop s n = case M.lookup n s of
         Just v -> J $ return (v,s)

       -- loop' s 0 = (\v -> (v,s)) <$> x
       -- loop' s 1 = (\v -> (v,s)) <$> y
       loop' s n = J $ do
         (v1,s) <- unJ $ loop s (n-1) in
                   let (v2,s) = loop s (n-2) in
                   (v1 +: v2,s)
-}

-- ------------------------------------------------------------------------
-- A simpler Gibonacci

-- Naive code
gibX0 :: (SSym repr) => repr Int -> repr Int -> Int -> repr Int
gibX0 x y 0 = x
gibX0 x y 1 = y
gibX0 x y n = gibX0 y ((addS `appS` x) `appS` y) (n-1)

gibX0n n = lamS (\x -> lamS (\y -> gibX0 x y n))
tX0n = runCS $ gibX0n 5
{-
"\\x_0 -> \\x_1 ->
 (GHC.Num.+) ((GHC.Num.+) x_1 ((GHC.Num.+) x_0 x_1)) ((GHC.Num.+) ((GHC.Num.+) x_0 x_1) ((GHC.Num.+) x_1 ((GHC.Num.+) x_0 x_1)))"
-}

gibX1 x y 0 = x
gibX1 x y 1 = y
gibX1 x y n = let_S ((addS `appS` x) `appS` y) $ \z -> gibX1 y z (n-1)

gibX1n n = lamS (\x -> lamS (\y -> gibX1 x y n))
tX1n = runCS $ gibX1n 5

-- Effectful
gibX2 :: (SSym repr, Applicative i) =>
         (IO :. i) (repr Int)  -> (IO :. i) (repr Int) -> Int ->
         (IO :. i) (repr Int)
gibX2 x y 0 = x
gibX2 x y 1 = y
gibX2 x y n = gibX2 y (Gib.addt x y) (n-1)

gibX2n n = lam (\x -> lam (\y -> gibX2 (vr x) (vr y) n))
tX2n = runC $ gibX2n 5
-- generating add
-- is printed 7 times

gibX5 :: (SSym repr, SymLet repr, Applicative m, Applicative i) =>
         (m :. i) (repr Int)  -> (m :. i) (repr Int) -> Int ->
         (m :. i) (repr Int)
gibX5 x y 0 = x
gibX5 x y 1 = y
gibX5 x y n = let_ (x +: y) $ \z -> gibX5 (weaken y) (var z) (n-1)

gibX5n n = lam (\x -> lam (\y -> gibX5 (vr x) (vr y) n))
tX5n = runCI $ gibX5n 5

trace :: Applicative i => String -> (IO :. i) a -> (IO :. i) a
trace msg m = liftJ (putStrLn msg) *> m

addt :: (SSym repr, Applicative i) =>
     (IO :. i) (repr Int) -> (IO :. i) (repr Int) -> (IO :. i) (repr Int)
addt x y = trace "generating add" (x +: y)

-- Polymorphic recursion: signature is needed
gibXT :: (SSym repr, SymLet repr, Applicative i) =>
         (IO :. i) (repr Int)  -> (IO :. i) (repr Int) -> Int ->
         (IO :. i) (repr Int)
gibXT x y 0 = x
gibXT x y 1 = y
gibXT x y n = let_ (Gib.addt x y) $ \z -> gibXT (weaken y) (var z) (n-1)

gibXTn n = lam (\x -> lam (\y -> gibXT (vr x) (vr y) n))
tXTn = runC $ gibXTn 5
-- We see only four additions are generated: the code is linear
{-
generating add
generating add
generating add
generating add
"\\x_0 -> \\x_1 -> let z_2 = (GHC.Num.+) x_0 x_1\n                 in let z_3 = (GHC.Num.+) x_1 z_2\n                     in let z_4 = (GHC.Num.+) z_2 z_3\n                         in let z_5 = (GHC.Num.+) z_3 z_4\n                             in z_5"
-}

