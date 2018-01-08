{-# LANGUAGE RankNTypes, NoMonomorphismRestriction, TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- Code generation with control effects reaching beyond the
-- closest binder. Far-reaching let-insertion.
-- The implementation of the CPSA applicative hierarchy.

module TSCPST where

import TSCore
import Control.Applicative
import Control.Monad.Identity
-- import Control.Monad.Trans (MonadTrans(..))


-- The CPSA Applicative

{- A better way to understand CPSA below is as a specialization
of the following

newtype CPSA w m a = 
    CPSA{unCPSA :: 
      forall m1. Extends m m1 =>
             (forall m2. Extends m1 m2 => m2 a -> m2 w) -> m1 w}

However, to make an instance of Applicative we need transitivity
of Extends, which requires ugly workarounds to convince the type
checker of.
-}

-- The parameters may be understood as:
--  w, the answer type
--  m, the `base' applicative of the generator (often a monad),
--     or: the binding environment of 'w'
--  a, the value produced by CPSA

newtype CPSA w m a = 
    CPSA{unCPSA :: 
      forall hw. AppLiftable hw =>
             (forall h. AppLiftable h => 
              ((m :. hw) :. h) a -> ((m :. hw) :. h) w)
      -> (m :. hw) w}

-- Instantiate h to Identity
throw :: (Applicative m, Applicative hw) =>
         (forall h. AppLiftable h => 
          ((m :. hw) :. h) a -> ((m :. hw) :. h) w) -> m a -> (m :. hw) w
throw k x = fmap runIdentity $ unJ (k (liftJ $ liftJ x))

-- newtype CPSA w m a = 
--     CPSA{unCPSA :: 
--      forall hw. AppLiftable hw =>
--              (forall h. AppLiftable h => 
--               ((m :. hw) :. h) a -> ((m :. hw) :. h) w)
--      -> (m :. hw) w}

-- How I HATE having to write this instance!!
instance (Applicative m) => Functor (CPSA w m) where
    fmap f m = pure f <*> m

instance (Applicative m) => Applicative (CPSA w m) where
    pure x = CPSA $ \k -> throw k (pure x)
    CPSA f <*> CPSA m = CPSA $ \k ->    -- produce (m :. hw) w, poly hw
      f (\fv ->                         -- produce ((m :. hw) :. hf) w
                                        -- fv :: ((m :. hw) :. hf) (a->b)
        unpack $                        -- choose hwm = (hw :. hf)
         m (\mv ->                      -- produce ((m :. hwm) :. hm) w
                                        -- mv :: ((m :. hwm) :. hm) a
            unpack2 (k (pack (liftJ fv) <*> pack2 mv))))


-- Applicative composition is associative. The following are the witnesses
pack :: Functor m => ((m :. i1) :. i2) a -> (m :. (i1 :. i2)) a
pack (J (J mi1i2)) = J (fmap J mi1i2)
unpack :: Functor m => (m :. (i1 :. i2)) a -> ((m :. i1) :. i2) a
unpack (J mJi1i2) = J . J $ (fmap unJ mJi1i2)

pack2 :: (Functor m, Functor i1) => 
         ((m :. (i1 :. i2)) :. i3) a -> ((m :. i1) :. (i2 :. i3)) a
pack2 (J (J mJi1i2i3)) = J (J ((fmap (fmap J)) (fmap unJ mJi1i2i3)))

unpack2 :: (Functor m, Functor i1) => 
         ((m :. i1) :. (i2 :. i3)) a -> ((m :. (i1 :. i2)) :. i3) a 
unpack2 (J (J mi1Ji2i3)) = J (J (fmap J (fmap (fmap unJ) mi1Ji2i3)))

star2 :: (Applicative i, Applicative j) =>
         i (j (a ->b)) -> i (j a) -> i (j b)
star2 f x = (<*>) <$> f <*> x


-- It turns out that throw is essentially a lift
{-
liftCA :: (Applicative m, Monad m) => m a -> CPSA w m a
liftCA m = CPSA $ \k -> J (m >>= unJ . throw k . pure)
-}
liftCA :: (Applicative m) => m a -> CPSA w m a
liftCA m = CPSA $ \k -> throw k m

-- To grow the hierarchy
liftJA :: Applicative m => (m :. j) a -> (CPSA w m :. j) a
liftJA = J . liftCA . unJ

reset :: (Applicative m) => CPSA a m a -> CPSA w m a
reset m  = CPSA $ \k -> throw k $ runCPSA m 

resetJ :: (Applicative m, Applicative i) => 
          (CPSA (i a) m :. i) a -> (CPSA w m :. i) a
resetJ = J . reset . unJ

-- Instantiating hw to Identity
runCPSA :: (Applicative m) => CPSA a m a -> m a
runCPSA m = fmap runIdentity . unJ $ unCPSA m id

runJCPSA :: Applicative m => (CPSA (i a) m :. i) a -> (m :. i) a
runJCPSA = J . runCPSA . unJ


exA2 = lam(\x -> lam(\y -> weaken (var x) +: (var y)))
exA2c = "\\x_0 -> \\x_1 -> (GHC.Num.+) x_0 x_1" == 
  (runCI . runJCPSA $ exA2)


-- First examples
addt :: (SSym repr, Applicative i) => (CPSA w IO :. i) (repr (Int -> Int -> Int))
addt = liftJ $ liftCA (putStrLn "generating add" *> pure addS)

ex0' :: (LamPure repr, SSym repr, AppLiftable i) =>
   (CPSA w IO :. i) (repr (Int -> Int))
ex0' = lam(\x -> addt $$ int 1 $$ var x)
ex0'c = fmap ("\\x_0 -> (GHC.Num.+) 1 x_0" ==) $ 
        runC (runJCPSA ex0')


-- Developing genlet, let-insertion combinator, in small steps

-- Warm-up:
-- write glet00 that inserts "let z = e10 in ... " where e10 is as follows:
-- First we assume that e10 is top-level (CPSA type)
e10 :: (SSym repr) => (CPSA w IO :. Identity) (repr Int)
e10 = addt $$ int 2 $$ int 3

-- So, the expression has the form expected for let-insertion.
-- It is only that various conversion functions that challenging.
-- reset e10 makes the result answer-type polymorphic.
-- we need that polymorphism to implement cnv3 below.

-- To test the inferred type
-- t = let__ (weaken (reset e10)) (\z -> undefined)

-- Just like weaken . reset, which however
-- has a slightly different type:
-- (CPSA (i a) m :. i) a -> (CPSA w m :. (i :. hw)) a
wreset :: (Applicative m, Applicative hw, Applicative i) => 
      (CPSA (i a) m :. i) a -> (CPSA w m :. (hw :. i)) a
wreset m = J $ CPSA $ \k -> throw k . fmap (J . pure) $ runCPSA (unJ m)
-- weakenhw :: (Applicative m, Applicative hw, Applicative i) => 
--       (CPSA w m :. i) a -> (CPSA w m :. (hw :. i)) a
-- weakenhw = J . fmap (J . pure) . unJ

{-
If we are to use let_ rather than let__, we need AppIdempotent
rather than AppLiftable

glet00 :: (Applicative i, SSym repr, SymLet repr) =>
          (CPSA (Identity (repr Int)) IO :. i) (repr Int)
glet00 = J $ CPSA (\k ->
               (cnv3 $ let_ (wreset e10) (\z -> cnv1 $ k (cnv2 z))) )
 where 
 cnv1 :: (AppLiftable i0, Applicative m, Applicative hw, Applicative j) =>
        ((m :. hw) :. j) (i0 (repr x)) -> 
        (CPSA ((hw :. i0) (repr x)) m :. ((hw :. i0) :. j)) (repr x)
 cnv1 m = J $ CPSA $ \k -> throw k (fmap J . fmap J . unJ . fmap app_pull $ unJ m)
 cnv2 :: (Applicative hw, Applicative m, Applicative i, AppLiftable j) => 
         ((hw :. i0) :. j) (repr a) -> ((m :. hw) :. (i0 :. j)) (i (repr a))
 cnv2 = undefined
 -- This is essentially reset, around shift's body, so to speak
 cnv3 :: (Applicative m, Applicative hw, Applicative i0) => 
         (CPSA ((hw :. i0) a) m :. (hw :. i0)) a -> (m :. hw) (i0 a)
 cnv3 = J . fmap unJ . runCPSA . unJ
-}

glet00 :: (Applicative i, SSym repr, SymLet repr) =>
          (CPSA (Identity (repr Int)) IO :. i) (repr Int)
glet00 = J $ CPSA (\k ->
               (cnv3 $ let__ (wreset e10) (\z -> cnv1 $ k (cnv2 z))) )
 where 
 cnv1 :: (AppLiftable i0, Applicative m, Applicative hw, Applicative j) =>
        ((m :. hw) :. j) (i0 (repr x)) -> 
        (CPSA ((hw :. i0) (repr x)) m :. ((hw :. i0) :. j)) (repr x)
 cnv1 m = J $ CPSA $ \k -> throw k (fmap J . fmap J . unJ . fmap app_pull $ unJ m)
 cnv2 :: (Applicative hw, Applicative m, Applicative i, Applicative j) => 
         j (repr a) -> ((m :. hw) :. j) (i (repr a))
 cnv2 = J . pure . fmap pure
 -- This is essentially reset, around shift's body, so to speak
 cnv3 :: (Applicative m, Applicative hw, Applicative i0) => 
         (CPSA ((hw :. i0) a) m :. (hw :. i0)) a -> (m :. hw) (i0 a)
 cnv3 = J . fmap unJ . runCPSA . unJ

ex4010 =  int 1 +: glet00
ex4010c = fmap ("let z_0 = (GHC.Num.+) 2 3\n in (GHC.Num.+) 1 z_0" ==)
           (runC (runJCPSA ex4010))

-- Another Warm-up:
-- write glet0 that inserts "let z = e1 in ... " where e1 is an
-- arbitrarily weakened e1 (that is, not necessarili a top-level
-- expression)
e1 :: (Applicative i, SSym repr) => (CPSA w IO :. i) (repr Int)
e1 = addt $$ int 2 $$ int 3

glet0 :: (Applicative i, AppLiftable i0, SSym repr, SymLet repr) =>
          (CPSA (i0 (repr w)) IO :. i) (repr Int)
glet0 = J $ CPSA (\k ->
               (cnv3 $ let__ (wreset e1) (\z -> cnv1 $ k (cnv2 z))) )
 where 
 cnv1 :: (AppLiftable i0, Applicative m, Applicative hw, Applicative j) =>
        ((m :. hw) :. j) (i0 (repr x)) -> 
        (CPSA ((hw :. i0) (repr x)) m :. ((hw :. i0) :. j)) (repr x)
 cnv1 m = J $ CPSA $ \k -> 
          throw k (fmap J . fmap J . unJ . fmap app_pull $ unJ m)
 cnv2 :: (Applicative hw, Applicative m, Applicative i, Applicative j) => 
         j (repr a) -> ((m :. hw) :. j) (i (repr a))
 cnv2 = J . pure . fmap pure
 -- This is essentially reset, around shift's body, so to speak
 cnv3 :: (Applicative m, Applicative hw, Applicative i0) => 
         (CPSA ((hw :. i0) a) m :. (hw :. i0)) a -> (m :. hw) (i0 a)
 cnv3 = J . fmap unJ . runCPSA . unJ


ex401 =  int 1 +: glet0
ex401c = fmap ("let z_0 = (GHC.Num.+) 2 3\n in (GHC.Num.+) 1 z_0" ==)
        (runC (runJCPSA ex401))


ex411 = lam (\x -> int 1 +: glet0)
ex411c = fmap ("let z_0 = (GHC.Num.+) 2 3\n in \\x_1 -> (GHC.Num.+) 1 z_0" ==)
        (runC (runJCPSA ex411))


-- Finally, the general genlet, taking the expression to
-- let-bind as an argument

genlet :: (Applicative i, Applicative m,
           AppLiftable i0, SSym repr, SymLet repr) =>
          (CPSA (i0 (repr a)) m :. i0) (repr a) ->
          (CPSA (i0 (repr w)) m :. i) (repr a)
genlet e = J $ CPSA (\k ->
               (cnv3 $ let__ (wreset e) (\z -> cnv1 $ k (cnv2 z))) )
 where 
 cnv1 :: (AppLiftable i0, Applicative m, Applicative hw, Applicative j) =>
        ((m :. hw) :. j) (i0 (repr x)) -> 
        (CPSA ((hw :. i0) (repr x)) m :. ((hw :. i0) :. j)) (repr x)
 cnv1 m = J $ CPSA $ \k -> 
          throw k (fmap J . fmap J . unJ . fmap app_pull $ unJ m)
 cnv2 :: (Applicative hw, Applicative m, Applicative i, Applicative j) => 
         j (repr a) -> ((m :. hw) :. j) (i (repr a))
 cnv2 = J . pure . fmap pure
 -- This is essentially reset, around shift's body, so to speak
 cnv3 :: (Applicative m, Applicative hw, Applicative i0) => 
         (CPSA ((hw :. i0) a) m :. (hw :. i0)) a -> (m :. hw) (i0 a)
 cnv3 = J . fmap unJ . runCPSA . unJ


tt0 = int 1 +: genlet e1
tt0c = runC (runJCPSA tt0)
{-
generating add
"let z_0 = (GHC.Num.+) 2 3\n in (GHC.Num.+) 1 z_0"
-}

ex43 = resetJ $ lam (\x -> var x +: genlet (int 2 +: int 3))
ex43c = "let z_0 = (GHC.Num.+) 2 3\n in \\x_1 -> (GHC.Num.+) x_1 z_0"
        == runCI (runJCPSA ex43)
ex43r = 105 == runRI (runJCPSA ex43) 100

-- Can't leak a variable
-- ex4f1 = lam (\x -> int 1 +: genlet (var x))
{-
    Expected type: (:.) m (i :. j) (repr Int)
      Actual type: (:.)
                     (CPSA ((:.) i j (repr w0)) m0) (i :. j) (repr Int)
    In the return type of a call of `genlet'
    In the second argument of `(+:)', namely `genlet (var x)'
    In the expression: int 1 +: genlet (var x)
-}

-- Let-insertion through several binders
ex44 = resetJ $ lam (\x -> lam (\y -> var y +: weaken (var x) +:
        genlet (int 2 +: int 3)))
ex44c = "let z_0 = (GHC.Num.+) 2 3\n "++
        "in \\x_1 -> \\x_2 -> (GHC.Num.+) ((GHC.Num.+) x_2 x_1) z_0"
        == runCI (runJCPSA ex44)
ex44r = 405 == runRI (runJCPSA ex44) 300 100


{-
ex450 = resetJ $ lam (\x -> (lam (\y -> var y +: weaken (var x) +:
        genlet (var x +: int 3))))

    Occurs check: cannot construct the infinite type: i0 = i0 :. j
    Expected type: i0 (repr0 Int)
      Actual type: (:.) i0 j (repr0 Int)
    In the first argument of `var', namely `x'
    In the first argument of `genlet', namely `(var x +: int 3)'
-}

ex45 = lam (\x -> resetJ (lam (\y -> var y +: weaken (var x) +:
        genlet (var x +: int 3))))

ex45c = "\\x_0 -> let z_1 = (GHC.Num.+) x_0 3\n         in "++
        "\\x_2 -> (GHC.Num.+) ((GHC.Num.+) x_2 x_0) z_1"
  == runCI (runJCPSA ex45)
ex45r = 123 == runRI (runJCPSA ex45) 10 100

-- More complex examples: inserting several let

ex46 = int 1 +: genlet (int 2 +: genlet (int 3 +: int 4))
       +: genlet (int 5 +: int 6)

ex47 = lam (\x -> int 1 +: genlet (int 2 +: genlet (int 3 +: int 4))
       +: genlet (int 5 +: int 6))

-- the first example of a nested genlet!

tt1 = int 1 +: genlet (liftJA $ glet0)
tt1c = fmap ("let z_0 = (GHC.Num.+) 2 3\n in let z_1 = z_0\n"++
       "     in (GHC.Num.+) 1 z_1" ==)
       $ runC (runJCPSA (runJCPSA tt1))

ex48 = lam (\x -> resetJ (lam (\y -> genlet (int 3 +: int 4))))
ex48c = ("\\x_0 -> let z_1 = (GHC.Num.+) 3 4\n"++
   "         in \\x_2 -> z_1") 
  == runCI (runJCPSA ex48)

-- The example from TSCPS.hs
ex49 = lam (\x -> resetJ (lam (\y ->
         int 1 +: genlet (var x +: genlet (int 3 +: int 4))
       +: genlet (int 5 +: int 6))))

{-
ex49c = ("\\x_0 -> let z_1 = (GHC.Num.+) 3 4\n"++
   "         in let z_2 = (GHC.Num.+) x_0 z_1\n"++
   "             in let z_3 = (GHC.Num.+) 5 6\n"++
   "                 in \\x_4 -> (GHC.Num.+) ((GHC.Num.+) 1 z_2) z_3") 
  == runCI (runJCPSA ex49)
-}

ex49c = ("\\x_0 -> let z_1 = let z_1 = (GHC.Num.+) 3 4\n"++
         "                   in (GHC.Num.+) x_0 z_1\n"++
         "         in let z_2 = (GHC.Num.+) 5 6\n"++
         "             in \\x_3 -> (GHC.Num.+) ((GHC.Num.+) 1 z_1) z_2")
  == runCI (runJCPSA ex49)


-- Now we add two liftJA

{-
ex50
  :: (Applicative m, AppLiftable i, AppLiftable i0, SymLet repr,
      LamPure repr, SSym repr) =>
     (:.) (CPSA w (CPSA (i0 (repr w1)) m)) i (repr (Int -> a -> Int))
-}
ex50 = lam (\x -> resetJ (lam (\y ->
         int 1 +: genlet (var x +: (liftJA $ genlet (int 3 +: int 4)))
       +: (liftJA $ genlet (int 5 +: int 6)))))


-- And two let appear on the outside the binder!
-- So, several let-insertion each crosses the different number of
-- binders (including the binders of the previous let)
ex50c = ("let z_0 = (GHC.Num.+) 3 4\n"++
   " in let z_1 = (GHC.Num.+) 5 6\n"++
   "     in \\x_2 -> let z_3 = (GHC.Num.+) x_2 z_0\n"++
   "                 in \\x_4 -> (GHC.Num.+) ((GHC.Num.+) 1 z_3) z_1"==)
   $ runCI (runJCPSA (runJCPSA ex50))


-- ------------------------------------------------------------------------
{- Old code, for comparison
-- A bizarre answer-type changing, sort of, CPS type
-- which happens to be applicative!
newtype CPSA w m a = 
    CPSA{unCPSA :: 
      forall hw. (forall h1. m (h1->hw->a) -> m (h1->hw->w))
      -> m (hw -> w)}

-- Instantiate h1 to ()
throw :: Functor m =>
   (forall h1. m (h1->hw-> a) -> m (h1 -> hw->w)) -> m a -> m (hw->w)
throw k x = fmap ($ ()) $ k (fmap (\xv () _ -> xv) x)

instance Applicative m => Applicative (CPSA w m) where
    pure x = CPSA $ \k -> throw k (pure x)
    CPSA f <*> CPSA m = CPSA $ \k ->
      f (\fv -> fmap (\mr hf kw -> mr (hf,kw)) $ m (\mv -> 
       fmap (\kr hm (hf,kw) -> kr (hm,hf) kw) 
         (k (comb <$> fv <*> mv))))
      where comb fvb mvb = \ (hm,hf) kw -> (fvb hf kw) (mvb hm (hf,kw))

glet0 = J (CPSA (\k -> 
  (unCPSA . unJ $ let_ e1 (\x -> 
       J (CPSA (\k0 -> 
       throw k0 $
                   fmap (\kr -> J(\ (h1,(hw,h)) -> unJ (kr h1 hw) h))
         (k (pure (\h1 _ -> J(\h -> unJ x (h1,())))))))
           ))
        (\x -> fmap (\xv h1 hw -> J(\h -> unJ (xv h1 hw) (hw,h))) x)))


ex401 =  int 1 +: glet0
ex401c = fmap ("let z_0 = (GHC.Num.+) 2 3\n in (GHC.Num.+) 1 z_0" ==)
        (runC (runJCPSA ex401))

ex411 = resetJ $ lam (\x -> int 1 +: glet0)
ex411c = fmap ("let z_0 = (GHC.Num.+) 2 3\n in \\x_1 -> (GHC.Num.+) 1 z_0" ==)
        (runC (runJCPSA ex411))


genlet :: (SSym repr, SymLet repr, Applicative m) =>
     J (CPSA (HV hw repr w) m) (HV hw repr) a
     -> J (CPSA (HV hw repr w) m) (HV ha repr) a
genlet e = J (CPSA (\k -> 
  (unCPSA . unJ $ let_ (weaken e) (\x -> 
       J (CPSA (\k0 -> 
       throw k0 $
                   fmap (\kr -> J(\ (h1,(hw,h)) -> unJ (kr h1 hw) h))
         (k (pure (\h1 _ -> J(\h -> unJ x (h1,())))))))
           ))
        (\x -> fmap (\xv h1 hw -> J(\h -> unJ (xv h1 hw) (hw,h))) x)
  ))

tt0:: (SSym repr, SymLet repr) =>
     J (CPSA (HV hw repr w) IO) (HV ha repr) Int
tt0 = int 1 +: genlet e1
tt0c = (runC (runJCPSA tt0))

tt1:: (SSym repr, SymLet repr) =>
     J (CPSA (HV hw repr w) (CPSA (HV hw1 repr w1) IO)) (HV ha repr) Int
tt1 = int 1 +: genlet (liftJA glet0)

tt1c = fmap ("let z_0 = (GHC.Num.+) 2 3\n in let z_1 = z_0\n"++
       "     in (GHC.Num.+) 1 z_1" ==)
       $ runC (runJCPSA (runJCPSA tt1))

-- The example from TSCPS.hs
ex49 = lam (\x -> resetJ (lam (\y ->
         int 1 +: genlet (var x +: genlet (int 3 +: int 4))
       +: genlet (int 5 +: int 6))))


-- Now we add two liftJA

-- The type is now lifted....
-- ex50  :: (SSym repr, Applicative m, SymLet repr, LamPure repr) =>
--      J (CPSA w1 (CPSA (HV hw repr w) m)) (HV h repr) (Int -> a -> Int)

ex50 = lam (\x -> resetJ (lam (\y ->
         int 1 +: genlet (var x +: (liftJA $ genlet (int 3 +: int 4)))
       +: (liftJA $ genlet (int 5 +: int 6)))))


-- And two let appear on the outside the binder!
-- So, several let-insertion each crosses the different number of
-- binders (including the binders of the previous let)
ex50c = ("let z_0 = (GHC.Num.+) 3 4\n"++
   " in let z_1 = (GHC.Num.+) 5 6\n"++
   "     in \\x_2 -> let z_3 = (GHC.Num.+) x_2 z_0\n"++
   "                 in \\x_4 -> (GHC.Num.+) ((GHC.Num.+) 1 z_3) z_1"==)
   $ runCI (runJCPSA (runJCPSA ex50))
-}
