{-# LANGUAGE FlexibleContexts, TypeOperators, TypeFamilies #-}

-- Generating imperative code with loops and arrays
-- This code is a safer version of the loop-tiling
-- matrix-vector--multiplication example of talk-problems.ml. 
-- See the latter file for the motivation and explanation.

module TSLoop where

import TSCore
import TSCPST

import Control.Applicative
import Data.Array.MArray
import Data.Array.IO
import Control.Monad (forM_, liftM2)

-- A sample matrix
sample_a :: IO (IOUArray (Int,Int) Int)
sample_a = do
  a <- newArray ((0,0),(4,9)) 0
  sequence [writeArray a (i,j) (i+j) |
      i <- [0..4], j <- [0..9]]
  return a

test_a = sample_a >>= getAssocs >>= print

-- A sample vector
sample_v :: IO (IOUArray Int Int)
sample_v = do
  v <- newArray (0,9) 0
  sequence [writeArray v i (i+1) | i <- [0..9]]
  return v

-- The text-book matrix-vector multiplication:
-- two nested loops

{-
Let's estimate the number of loads, assuming that the cache line is
8*sizeof(Int) and the arrays is approriately aligned.
At the iteration j=0, i=0, v_0 and (hence v_1 through v_8, in the same
cache line) are loaded in cache. a_00 through a_07 are loaded in cache,
and v'_0 through v'_7. Then i increments, and a_10 through a_17 loaded,
v'_1 is in cache, v_0 is in cache. Overall, the i iteration will have
n loads for a, 1 load for v_0, and n/8 loads for v'.

Since v_0 has been accessed all the time, its cache line stays put.
Therefore, when j becomes 1, v_1 is already in cache. However, if
n is long, a_01 (loaded when j=0, i=0) is probably evicted, ans has to be loaded
again. Likewise, v'_0 is evicted. So, j=1, i=iteration need
n loads for a, 0 loads for v_1 and n/8 loads for v'.
Overall,
  n*m (loads for a) + m/8 (loads for v) + nm/8 (loads for v')

Compare with ../metaocaml/loop_tiling.ml for the case when the loop over i
is outermost.
-}

mvmul_textbook :: (Num e, MArray IOUArray e IO) =>
  Int -> Int -> 
  IOUArray (Int,Int) e -> IOUArray Int e -> IOUArray Int e -> IO ()
mvmul_textbook n m a v v' = 
 vec_clear_ n v' >>
 forM_ [0,1..m-1] (\j ->
  forM_ [0,1..n-1] (\i ->
   vec_addto_ v' i =<<
     mat_get_ a i j `mulPM` vec_get_ v j))

mulPM :: (Num a, Monad m) => m a -> m a -> m a
mulPM = liftM2 (*)

-- Run the code now, to test it
tmstbr = do
  a  <- sample_a
  v  <- sample_v
  v' <- newArray (0,4) 100
  mvmul_textbook 5 10 a v v'
  -- getAssocs v' >>= print  
  getAssocs v' >>= 
   return .  (== [(0,330),(1,385),(2,440),(3,495),(4,550)])

-- Hand-written tiled code
mvmul_tiled :: (Num e, MArray IOUArray e IO) =>
  Int -> Int -> Int -> IOUArray (Int,Int) e ->
  IOUArray Int e -> IOUArray Int e -> IO ()
mvmul_tiled b n m a v v' =
 vec_clear_ n v' >>
 forM_ [0,b..m-1] (\jj ->
 forM_ [0,b..n-1] (\ii ->
  forM_ [jj,jj+1..min (jj+b-1) (m-1)] (\j ->
   forM_ [ii,ii+1..min (ii+b-1) (n-1)] (\i ->
    vec_addto_ v' i =<<
      mat_get_ a i j `mulPM` vec_get_ v j))))

{-
Analysis:
Let's consider the first tile: jj=0, ii=0.
The j=0, i=0 iteration loads v_0 through v_7 and a_00 through a07 and
v'_0 through v'_7. Then i increments, we need to keep loading a_i0
but v' can be loaded b/8 times. Thus i iteration needs
b loads of a, 1 load of v and b/8 loads of v'.
If the amount of loaded a data is small, v' stays in cache, and so is v.
So, overall, a tile needs
b*b/8 (loads for a) + b/8 (loads for v) + b/8 (loads for v')
For the next tile, v may still be in cache. But even if it is evicted,
we obtain overall
mn (1/8 + 1/(8b) + 1/(8b)), about 8-times improvement.
-}

ttiledr1 = do
  a  <- sample_a
  v  <- sample_v
  v' <- newArray (0,4) 100
  mvmul_tiled 2 5 10 a v v'
  -- getAssocs v' >>= print  
  getAssocs v' >>= 
   return .  (== [(0,330),(1,385),(2,440),(3,495),(4,550)])

ttiledr2 = do
  a  <- sample_a
  v  <- sample_v
  v' <- newArray (0,4) 100
  mvmul_tiled 3 5 10 a v v'
  -- getAssocs v' >>= print  
  getAssocs v' >>= 
   return .  (== [(0,330),(1,385),(2,440),(3,495),(4,550)])

-- monadic version of *:
mulM :: (SSym repr, SymBind repr, Applicative p, Monad p, Applicative m) => 
  m (repr (p Int)) -> m (repr (p Int)) -> m (repr (p Int))
mulM x y = (\x y -> gretS mulS `apS` x `apS` y) <$> x <*> y


-- Generator of matrix-vector multiplication
-- For simplicity, we assume the dimensions n and m are assumed
-- known statically (the same assumption was made om talk-problems.ml)
-- (although it is a small simplicity: the general case is just a bit harder,
-- but we have to do subtraction by 1 occasionally, and we have to let-bind
-- the n and m code, to avoid repetitions).
-- We use weakens all throughout (we need a signature though)
-- We assume the input vector is long.
mvmul0 :: (SymMat repr, SymVec repr, SymBind repr, SSym repr, LamPure repr,
     SymLoop repr, Applicative m, AppLiftable i) =>
     Int -> Int
     -> (m :. i) (repr (IOUArray (Int, Int) Int))
     -> (m :. i) (repr (IOUArray Int Int))
     -> (m :. i) (repr (IOUArray Int Int))
     -> (m :. i) (repr (IO ()))
mvmul0 n m a v v' =
 vec_clear (int n) v' >>:
 loop (int 0) (int (m-1)) (int 1) (lam $ \j ->
  loop (int 0) (int (n-1)) (int 1) (lam $ \i ->
   vec_addto (weakens v') (vr i) =<<:
      (mat_get (weakens a) (vr i) (vr j) `mulM`
       vec_get (weakens v) (vr j))
  ))

tms0c = "\\x_0 -> \\x_1 -> \\x_2 -> "++
 "(GHC.Base.>>) (TSCore.vec_clear_ 5 x_2) "++
 "(Control.Monad.forM_ (GHC.Enum.enumFromThenTo 0 (0 GHC.Num.+ 1) 9) "++
 "(\\x_3 -> "++
    "Control.Monad.forM_ (GHC.Enum.enumFromThenTo 0 (0 GHC.Num.+ 1) 4) "++
    "(\\x_4 -> "++
       "(GHC.Base.>>=) ((GHC.Base.return (GHC.Num.*) Control.Applicative.<*>"++
       " TSCore.mat_get_ x_0 x_4 x_3) Control.Applicative.<*>"++
       " TSCore.vec_get_ x_1 x_3) "++
      "(TSCore.vec_addto_ x_2 x_4))))"
 ==
 (runCI (lam $ \a -> (lam $ \vin -> (lam $ \v' ->
   mvmul0 5 10 (vr a) (vr vin) (vr v')))))


-- Run the code now, to test it
tms0r = do
  a  <- sample_a
  v  <- sample_v
  v' <- newArray (0,4) 100
  runRI (lam $ \a -> (lam $ \vin -> (lam $ \v' ->
    mvmul0 5 10 (weaken (weaken (var a))) (weaken (var vin)) (var v'))))
   a v v'
  -- getAssocs v' >>= print  
  getAssocs v' >>= 
   return .  (== [(0,330),(1,385),(2,440),(3,495),(4,550)])


-- Strip-mining, split-factor b, statically known
loop_nested :: (SSym repr, LamPure repr, SymLoop repr, SymMin repr,
    Applicative m, AppLiftable i) =>
     Int
     -> Int
     -> Int
     -> (m :. i) (repr (Int -> IO ()))
     -> (m :. i) (repr (IO ()))
loop_nested b lb ub body =
    loop (int lb) (int ub) (int b) (lam $ \ii ->
     loop (var ii) (min_ (var ii +: int (b-1)) (int ub)) (int 1)
      (weakens body))


-- The body remains the same; the use of weakens is crucial!

mvmul1 :: (SymMat repr, SymVec repr, SymBind repr, SSym repr, LamPure repr,
     SymMin repr, SymLoop repr, Applicative m, AppLiftable i) =>
     Int -> Int -> Int
     -> (m :. i) (repr (IOUArray (Int, Int) Int))
     -> (m :. i) (repr (IOUArray Int Int))
     -> (m :. i) (repr (IOUArray Int Int))
     -> (m :. i) (repr (IO ()))
mvmul1 b n m a v v' =
 vec_clear (int n) v' >>:
 loop_nested b 0 (m-1) (lam $ \j ->
  loop_nested b 0 (n-1) (lam $ \i ->
   vec_addto (weakens v') (vr i) =<<:
     (mat_get (weakens a) (vr i) (vr j) `mulM`
      vec_get (weakens v) (vr j))
  ))

{-
tms1c = "\\x_0 -> \\x_1 -> \\x_2 -> "++
 "(GHC.Base.>>) "++
 "(TSCore.loop_ 0 ((GHC.Num.+) 5 (-1)) 1 (\\x_3 -> "++
   "TSCore.vec_set_ x_2 x_3 0)) "++
 "(TSCore.loop_ 0 9 2 (\\x_3 -> "++
  "TSCore.loop_ x_3 (GHC.Classes.min ((GHC.Num.+) x_3 1) 9) 1 (\\x_4 -> "++
  "TSCore.loop_ 0 4 2 (\\x_5 -> "++
  "TSCore.loop_ x_5 (GHC.Classes.min ((GHC.Num.+) x_5 1) 4) 1 (\\x_6 -> "++
  "(GHC.Base.>>=) (Control.Monad.ap (Control.Monad.ap (GHC.Base.return (GHC.Num.+)) (TSCore.vec_get_ x_2 x_6)) (Control.Monad.ap (Control.Monad.ap (GHC.Base.return (GHC.Num.*)) (TSCore.mat_get_ x_0 x_6 x_4)) (TSCore.vec_get_ x_1 x_4))) (TSCore.vec_set_ x_2 x_6))))))"
 ==
-}
tms1c = "\\x_0 -> \\x_1 -> \\x_2 -> "++
  "(GHC.Base.>>) (TSCore.vec_clear_ 5 x_2) "++
  "(Control.Monad.forM_ (GHC.Enum.enumFromThenTo 0 (0 GHC.Num.+ 2) 9) "++
  "(\\x_3 -> "++
  "Control.Monad.forM_ (GHC.Enum.enumFromThenTo x_3 "++
           "(x_3 GHC.Num.+ 1) (GHC.Classes.min ((GHC.Num.+) x_3 1) 9)) "++
  "(\\x_4 -> "++
  "Control.Monad.forM_ (GHC.Enum.enumFromThenTo 0 (0 GHC.Num.+ 2) 4) "++
    "(\\x_5 -> "++
    "Control.Monad.forM_ (GHC.Enum.enumFromThenTo x_5 "++
              "(x_5 GHC.Num.+ 1) (GHC.Classes.min ((GHC.Num.+) x_5 1) 4)) "++
    "(\\x_6 -> "++
    "(GHC.Base.>>=) ((GHC.Base.return (GHC.Num.*) Control.Applicative.<*> "++
     "TSCore.mat_get_ x_0 x_6 x_4) Control.Applicative.<*> "++
     "TSCore.vec_get_ x_1 x_4) "++
    "(TSCore.vec_addto_ x_2 x_6))))))"
 ==
 (runCI (lam $ \a -> (lam $ \v -> (lam $ \v' ->
   mvmul1 2 5 10 (weaken (weaken (var a))) (weaken (var v)) (var v')))))

-- run it for testing
tms1r = do
  a  <- sample_a
  v  <- sample_v
  v' <- newArray (0,4) 100
  runRI (lam $ \a -> (lam $ \v -> (lam $ \v' ->
    mvmul1 2 5 10 (weaken (weaken (var a))) (weaken (var v)) (var v'))))
   a v v'
  getAssocs v' >>= 
   return .  (== [(0,330),(1,385),(2,440),(3,495),(4,550)])

-- A loop-insertion primitive
-- (quite analogous to genlet)
insloop :: (Applicative i, Applicative m, AppLiftable i0, 
            SSym repr, SymLet repr, SymLoop repr, LamPure repr, Extends i0 i) =>
          (CPSA (i0 (repr Int)) m :. i0) (repr Int) ->
          (CPSA (i0 (repr Int)) m :. i0) (repr Int) ->
          (CPSA (i0 (repr Int)) m :. i0) (repr Int) ->
          (CPSA (i0 (repr (IO ()))) m :. i) (repr Int)
insloop lb ub step = J $ CPSA (\k ->
               (cnv3 $ loop (wreset lb) (wreset ub) (wreset step) $
                 lam (\z -> cnv1 $ k (cnv2 z))) )
 where 
 cnv1 :: (AppLiftable i0, Applicative m, Applicative hw, Applicative j) =>
        ((m :. hw) :. j) (i0 (repr x)) -> 
        (CPSA ((hw :. i0) (repr x)) m :. ((hw :. i0) :. j)) (repr x)
 cnv1 m = J $ CPSA $ \k -> 
          throw k (fmap J . fmap J . unJ . fmap app_pull $ unJ m)
 cnv2 :: (Applicative hw, Applicative m, Applicative i, AppLiftable j,
         Extends i0 i) => 
         ((hw :. i0) :. j) (repr a) -> ((m :. hw) :. j) (i (repr a))
 cnv2 = J . J . pure . fmap app_pull . fmap weakens . unJ . unJ
 -- This is essentially reset, around shift's body, so to speak
 cnv3 :: (Applicative m, Applicative hw, Applicative i0) => 
         (CPSA ((hw :. i0) a) m :. (hw :. i0)) a -> (m :. hw) (i0 a)
 cnv3 = J . fmap unJ . runCPSA . unJ

{-
tk1 = "\\x_0 -> TSCore.loop_ 1 2 3 (\\x_1 -> let z_2 = x_1\n"++
       "                                     in TSCore.mat_set_ x_0 z_2 z_2 0)"
 ==
-}
tk1 = "\\x_0 -> "++
      "Control.Monad.forM_ (GHC.Enum.enumFromThenTo 1 (1 GHC.Num.+ 3) 2) "++
      "(\\x_1 -> let z_2 = x_1\n"++
      "                                                                   "++
      "                 in TSCore.mat_set_ x_0 z_2 z_2 0)"
  ==
 (runCI (runJCPSA 
  (lam $ \a ->
    resetJ $ let_ (insloop (int 1) (int 2) (int 3))
             (\i -> mat_set (weaken (var a)) (var i) (var i) (int 0)))))


-- Like loop_nested, but lift up the first loop
-- The blocking factor is static (as it should be)
-- If we want it to be `dynamic' (that is, int code)
-- we have to make the type higher-rank since b is used in
-- different contexts (in the inner and outer loops)
loop_nested_exch :: (SSym repr, SymLet repr, LamPure repr,
         SymLoop repr, SymMin repr, Applicative m,
                     Extends i0 i, AppLiftable i0) =>
     Int -> Int -> Int ->
     (CPSA (i0 (repr (IO ()))) m :. i) (repr (Int-> IO ())) ->
     (CPSA (i0 (repr (IO ()))) m :. i) (repr (IO ()))
loop_nested_exch b lb ub body =
    let_ (insloop (int lb) (int ub) (int b)) (\ii ->
     loop (var ii) (min_ (var ii +: int (b-1)) (int ub)) (int 1)
      (weakens body))


-- The signature tells all the features we use
mvmul2 :: (SymMat repr, SymVec repr, SymBind repr, SSym repr, LamPure repr,
     SymMin repr, SymLoop repr, SymLet repr,
           Applicative m', AppLiftable i,
           m ~ CPSA (i (repr (IO ()))) m') =>
     Int -> Int -> Int
     -> (m :. i) (repr (IOUArray (Int, Int) Int))
     -> (m :. i) (repr (IOUArray Int Int))
     -> (m :. i) (repr (IOUArray Int Int))
     -> (m :. i) (repr (IO ()))
mvmul2 b n m a v v' =
 vec_clear (int n) v' >>:
 (resetJ $
 loop_nested_exch b 0 (m-1) (lam $ \j ->
  loop_nested_exch b 0 (n-1) (lam $ \i ->
   vec_addto (weakens v') (vr i) =<<:
     (mat_get (weakens a) (vr i) (vr j) `mulM`
      vec_get (weakens v) (vr j))
  )))

{-
tms2c = "\\x_0 -> \\x_1 -> \\x_2 -> "++
  "(GHC.Base.>>) "++
  "(TSCore.loop_ 0 ((GHC.Num.+) 5 (-1)) 1 (\\x_3 -> "++
  "TSCore.vec_set_ x_2 x_3 0)) "++
  "(TSCore.loop_ 0 9 2 (\\x_3 -> "++
   "TSCore.loop_ 0 4 2 (\\x_4 -> let z_5 = x_3\n                                                                                                                                                                            in "++
   "TSCore.loop_ z_5 (GHC.Classes.min ((GHC.Num.+) z_5 1) 9) 1 (\\x_6 -> "++
   "let z_7 = x_4\n                                                                                                                                                                                                                                                    in "++
   "TSCore.loop_ z_7 (GHC.Classes.min ((GHC.Num.+) z_7 1) 4) 1 (\\x_8 -> "++
    "(GHC.Base.>>=) (Control.Monad.ap (Control.Monad.ap (GHC.Base.return (GHC.Num.+)) (TSCore.vec_get_ x_2 x_8)) (Control.Monad.ap (Control.Monad.ap (GHC.Base.return (GHC.Num.*)) (TSCore.mat_get_ x_0 x_8 x_6)) (TSCore.vec_get_ x_1 x_6))) (TSCore.vec_set_ x_2 x_8))))))"
  ==
-}
tms2c = "\\x_0 -> \\x_1 -> \\x_2 -> "++
  "(GHC.Base.>>) (TSCore.vec_clear_ 5 x_2) "++
  "(Control.Monad.forM_ (GHC.Enum.enumFromThenTo 0 (0 GHC.Num.+ 2) 9) "++
  "(\\x_3 -> "++
  "Control.Monad.forM_ (GHC.Enum.enumFromThenTo 0 (0 GHC.Num.+ 2) 4) "++
  "(\\x_4 -> let z_5 = x_3\n                                                                                                                                                                                                                        in Control.Monad.forM_ (GHC.Enum.enumFromThenTo z_5 (z_5 GHC.Num.+ 1) (GHC.Classes.min ((GHC.Num.+) z_5 1) 9)) (\\x_6 -> let z_7 = x_4\n                                                                                                                                                                                                                                                                                                                                                 in Control.Monad.forM_ (GHC.Enum.enumFromThenTo z_7 (z_7 GHC.Num.+ 1) (GHC.Classes.min ((GHC.Num.+) z_7 1) 4)) (\\x_8 -> (GHC.Base.>>=) ((GHC.Base.return (GHC.Num.*) Control.Applicative.<*> TSCore.mat_get_ x_0 x_8 x_6) Control.Applicative.<*> TSCore.vec_get_ x_1 x_6) (TSCore.vec_addto_ x_2 x_8))))))"
 ==
 (runCI (runJCPSA (lam $ \a -> (lam $ \v -> (lam $ \v' ->
  resetJ $ mvmul2 2 5 10
    (weaken (weaken (var a))) (weaken (var v)) (var v'))))))

tms2r = do
  a  <- sample_a
  v  <- sample_v
  v' <- newArray (0,4) 100
  runRI (runJCPSA (lam $ \a -> (lam $ \v -> (lam $ \v' ->
    resetJ $ mvmul2 2 5 10 (weaken (weaken (var a))) 
                                             (weaken (var v)) (var v')))))
   a v v'
  getAssocs v' >>= 
   return .  (== [(0,330),(1,385),(2,440),(3,495),(4,550)])


main = sequence [tmstbr, ttiledr1, ttiledr2, 
                    return tms0c, tms0r, 
                    return tms1c, tms1r, 
     return tk1,
     return tms2c, tms2r] 
        >>= print . and
