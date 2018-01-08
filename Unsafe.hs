{-# LANGUAGE NoMonomorphismRestriction, Rank2Types, FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}

-- Checking to see what could go wrong if we don't have the
-- quantification over s

module Unsafe where

import TSCore
import Unsafe.Coerce
import Control.Applicative
import Data.IORef

-- The unsafe version of lam without the quantification over i.
-- `Bad examples' in this file won't type check in our framework.
-- We have to deliberately break it, introducing unsafeLam:

-- The commented signature is nicer. Alas, it breaks type inference
-- in exKYC1
{-
unsafeLam :: (Applicative m, AppLiftable i, SSym repr, LamPure repr) =>
       (forall j. (j ~ (->) (repr a))) => 
        (i :. j) (repr a) -> (m :. (i :. j)) (repr b))
       -> (m :. i) (repr (a->b))
-}
unsafeLam :: (Applicative m, AppLiftable i, SSym repr, LamPure repr) =>
        ((i :. (->) (repr a)) (repr a) -> (m :. (i :. (->) (repr a))) (repr b))
       -> (m :. i) (repr (a->b))
unsafeLam f = fmap lamS (J . fmap unJ . unJ $ f  (J . pure $ v))
 where
 -- instantiate applicative j to be a Reader: repr a -> w
 v = \repra -> repra                    -- bound variable


{-
unsafeLamL :: (Functor m, Monad m, SSym repr, LamLPure repr) =>
       (HV (H repr s a,h) repr a 
  -> J (State Label m) (HV (H repr s a,h) repr) b)
       -> J (State Label m) (HV h repr) (a->b)
unsafeLamL f = lamL (\x -> (unsafeCoerce (f (unsafeCoerce x))))

-- Simple illustration of well-labelling
ex0 = lamL(\x -> lamL(\y -> weaken (var x) +: var y))
ex0c = "\\x_0_0 -> \\x_1_1 -> (GHC.Num.+) x_0_0 x_1_1" == runCLI ex0
-}

-- ------------------------------------------------------------------------
-- Illustration that well-scoped de Bruijn indices 
-- do not statically determine lexical scope

-- Example from Sec 3.3 (p822) of 
--   Chiyan Chen and Hongwei Xi
--   Meta-Programming Through Typeful Code Representation
--   JFP, 2005
-- We translate the example to our framework and embellish a bit
-- We must use unsafeLam to write the example illustrating the
-- problem. We cannot write the example in our framework without
-- breaking it, fortunately.

-- Inferred type
-- exCX1 :: (Applicative m, SSym repr, LamPure repr) =>
--      (J m (HV (H repr s1 b, (H repr s a, h)) repr) b
--       -> J m (HV (H repr s1 b, (H repr s a, h)) repr) c)
--      -> J m (HV h repr) (a -> b -> c)

exCX1 :: (Applicative m, LamPure repr, SSym repr, AppLiftable i,
         j1 ~ (->) (repr a), j2 ~ (->) (repr b)) =>
     ((m :. ((i :. j1) :. j2)) (repr b) -> (m :.((i :. j1) :. j2)) (repr c))
     -> (m :.i) (repr (a -> b -> c))

exCX1 f = unsafeLam(\y ->unsafeLam (\x -> f (var x)))

-- We demonstrate that depending on the argument of exCX1, we
-- obtain the code with the different mappings between
-- binding and reference occurrences of the variable.
-- Thus the mapping -- the scoping -- cannot be statically determined
-- just by looking at the exCX1 code, or its type.

exCX1_c1 = "\\x_0 -> \\x_1 -> x_1" == runCI (exCX1 id)

permute_env :: (Functor m, Functor i, Applicative j, AppLiftable j1) =>
     (m :. ((i :. j) :. j1)) a -> (m :. ((i :. j1) :. j)) a
permute_env = mapJ2 (\ (J (J iabb)) -> J $ J $ fmap app_pull iabb)
exCX1_c2 = "\\x_0 -> \\x_1 -> x_0" ==
     runCI (exCX1 permute_env)


-- To write exCX1 without unsafeLam, we have to give f a higher-rank
-- type

-- For example
exCX2 :: (Applicative m, SSym repr, LamPure repr, AppLiftable i) =>
      (forall j. Extends (m :. i) (m :. j) =>
       (m :. j) (repr b) -> (m :. j) (repr c))
      -> (m :. i) (repr (a -> b -> c))
exCX2 f = lam(\y -> lam (\x -> f (var x)))

exCX2_c1 = "\\x_0 -> \\x_1 -> x_1" == runCI (exCX2 id)


-- But exCX2_c2 would not type. Indeed, the signature of
-- exCX2 promised that the function f maps one piece of the
-- future-stage code to another piece, in exactly the same
-- environment. Moreover, the function f won't even look
-- at that environment. The argument to exCX2_c2 below certainly
-- fails that promise.
-- exCX2_c2 = runCI (exCX2 permute_env)
{-
    Could not deduce (j ~ ((i0 :. j10) :. j10))
    from the context (Extends (Identity :. Identity) (Identity :. j))

    Expected type: (:.) Identity j (C b0) -> (:.) Identity j (C b0)
      Actual type: (:.) Identity ((i0 :. j10) :. j10) (C b0)
                   -> (:.) Identity ((i0 :. j10) :. j10) (C b0)
    In the first argument of `exCX2', namely `permute_env'
-}

-- We could try giving exCX a more precise type. We still have to
-- use the quantification, to prevent 'j1' and 'j2' from escaping
exCX3 :: (Applicative m, SSym repr, LamPure repr, AppLiftable i) =>
      (forall j1 j2. (Applicative j1, Applicative j2) =>
       (m :. ((i :. j1) :. j2)) (repr b) ->
       (m :. ((i :. j1) :. j2)) (repr c))
      -> (m :. i) (repr (a -> b -> c))
exCX3 f = lam(\y -> lam (\x -> f (var x)))

exCX3_c1 = "\\x_0 -> \\x_1 -> x_1" == runCI (exCX3 id)

-- Now the signature anticipates that f transforms two pieces
-- of future-stage code in the environment that has at least two
-- slots. The signature says that f will keep the order of these
-- slots. But the argument of exCX3 certainly does not.
-- The type-checker complains, with a precise error message.
-- exCX3_c2 = runCI (exCX3 permute_env)
{-

    Could not deduce (j1 ~ j2)
    Expected type: (:.) Identity ((Identity :. j1) :. j2) (C b0)
                   -> (:.) Identity ((Identity :. j1) :. j2) (C b0)
      Actual type: (:.) Identity ((Identity :. j1) :. j2) (C b0)
                   -> (:.) Identity ((Identity :. j2) :. j1) (C b0)
    In the first argument of `exCX2', namely `permute_env'
-}

-- Finally, we try to give exCX signature to specifically permit
-- the argument function f to shuffle the environment
-- It won't type then, because the `names', the quantified variable
-- associated with y and the quantified variable associated with x
-- got mixed up.
{-
exCX4 :: (Applicative m, SSym repr, LamPure repr, AppLiftable i) =>
      (forall j1 j2. (Applicative j1, Applicative j2) =>
       (m :. ((i :. j1) :. j2)) (repr b) ->
       (m :. ((i :. j2) :. j1)) (repr c))
      -> (m :. i) (repr (a -> b -> c))
exCX4 f = lam(\y -> lam (\x -> f (var x)))
    Could not deduce (j1 ~ j)
      `j' is a rigid type variable bound by
          a type expected by the context:
            AppLiftable j =>
            (:.) i j (repr a) -> (:.) m (i :. j) (repr (b -> c))
          at /home/oleg/papers/MetaFX/hybrid/Unsafe.hs:149:11
      `j1' is a rigid type variable bound by
           a type expected by the context:
             AppLiftable j1 =>
             (:.) (i :. j) j1 (repr b) -> (:.) m ((i :. j) :. j1) (repr c)
           at /home/oleg/papers/MetaFX/hybrid/Unsafe.hs:149:21
    Expected type: (:.) (i :. j1) j (repr b)
      Actual type: (:.) (i :. j) j1 (repr b)
    In the first argument of `var', namely `x'
    In the first argument of `f', namely `(var x)'
-}

-- The following type-checks though
-- since applying f twice restores the order
exCX5 :: (Applicative m, SSym repr, LamPure repr, AppLiftable i) =>
      (forall j1 j2. (Applicative j1, AppLiftable j2) =>
       (m :. ((i :. j1) :. j2)) (repr a) ->
       (m :. ((i :. j2) :. j1)) (repr a))
      -> (m :. i) (repr (a -> a -> a))
exCX5 f = lam(\y -> lam (\x -> f (f (var x))))

-- But now the following won't type. We promised that the argument of
-- exCX5 shall swap the two slots in the environment.
-- exCX5_c1 = runCI (exCX5 id)
{-
    Could not deduce (j2 ~ j1)

    Expected type: (:.) Identity ((Identity :. j1) :. j2) (C a0)
                   -> (:.) Identity ((Identity :. j2) :. j1) (C a0)
      Actual type: (:.) Identity ((Identity :. j1) :. j2) (C a0)
                   -> (:.) Identity ((Identity :. j1) :. j2) (C a0)
    In the first argument of `exCX5', namely `id'
-}

-- The following types, but the result shows that the variable reference
-- corresponds to the inner binding, which has been apparent from exCX5
-- code. No surprises here.
exCX5_c2 = "\\x_0 -> \\x_1 -> x_1" == runCI (exCX5 permute_env)

{-
-- The following type-checks too
exCX6 :: (Applicative m, SSym repr, LamPure repr) =>
     (forall h1 h2 h3 h4. 
      J m (HV (h1,(h2,h)) repr) a  -> J m (HV (h3,(h4,h)) repr) a)
     -> J m (HV h repr) (a -> a -> a)
exCX6 f = lam(\y -> lam (\x -> f (var x)))

-- but it can only mean that f does not depend on the first two
-- slots in the environment. The function f certainly can be a constant
-- function. There would not be any variable references in the generated
-- code then, regardless of the particular argument we pass to exCX6.
-- Again, we determine the scope just by looking at the types.

exCX6_c3  = "\\x_0 -> \\x_1 -> 5" ==
      runCI (exCX6 (const (int 5)))


-- Recall exCX1 again; let's apply it to a particular function f
-- as below. The result may be given the shown type

exCX11 :: (Applicative m, SSym repr, LamPure repr) =>
     J m (HV h repr) (Int -> Int -> Int)
exCX11 = exCX1 permute_env

-- Let's beta-expand, introducing a beta-redex into a generated code
exCX7 f = unsafeLam(\y ->
        unsafeLam (\dummy ->    {- beta-redex -}
             unsafeLam (\x -> f (var x))) $$ 
       (unsafeLam (\z -> var z))) {- beta-redex -}

-- Unexpectedly, that has changed the type of the application!
{-
exCX71 :: (Applicative m, SSym repr, LamPure repr) =>
     J m (HV t repr) (Int -> Int -> Int)
exCX71 = exCX7 permute_env

    Couldn't match expected type `Int' against inferred type `a -> a'
     Expected type: 
     J m (HV (H repr s2 Int, (H repr s1 (a -> a), (H repr s Int, t))) repr) Int
     Inferred type:
     J m (J ((->) (H repr s2 (a -> a), 
                  (H repr s1 Int, (H repr s Int, t)))) repr) Int
-}


-- Now check what happens with labelling
exCXL1 f = unsafeLamL(\y ->unsafeLamL (\x -> f (var x)))

exCX1L_c1 = "\\x_0_0 -> \\x_1_1 -> x_1_1" == runCLI (exCXL1 id)

-- The following typechecks
exCXL1_c2 = runCLI (exCXL1 permute_env)
-- But running fails the run-time well-labellness test
{-
*Unsafe> exCXL1_c2
"*** Exception: Ill-labeled: got varname x_0_0  but expected the label 1
-}
-}

-- ------------------------------------------------------------------------
-- Reproducing the example from Sec 6.4 of 
--  Ik-Soon Kim, Kwangkeun Yi, Cristiano Calcagno
--  A Polymorphic Modal Type System for Lisp-Like Multi-staged Languages
--  POPL 2006
-- let val a = ref `1
--     val f = `(fn x -> fn y -> ,(a := `(x + y); `2))
--     val g = `(fn y -> fn z -> ,(!a))


-- Again we have to use unsafeLam to type check the example.
-- Our type system does not permit such a blatant scope extrusion
exKYC1 :: forall repr i. (SSym repr, LamPure repr, AppLiftable i) => 
           (IO :. i) (repr (Int -> Int -> Int))
exKYC1 = J $ do
  a <- unJ (int 1) >>= newIORef
  f <- unJ $ unsafeLam (\x -> unsafeLam (\y -> J (
        unJ ((weaken (var x) +: var y)) >>= writeIORef a >> unJ (int 2))))
  g <- unJ $ unsafeLam (\y -> unsafeLam (\z -> J $ readIORef a))
  return g

exKYC1_c = fmap ("\\x_0 -> \\x_1 -> (GHC.Num.+) x_0 x_1" ==) $ runC exKYC1


-- Indeed, inserting just one safe lam triggers the ire of the type checker
{-
exKYC2 = J $ do
  a <- unJ (int 1) >>= newIORef
  f <- unJ $ lam (\x -> unsafeLam (\y -> J (
        unJ ((weaken (var x) +: var y)) >>= writeIORef a >> unJ (int 2))))
  g <- unJ $ unsafeLam (\y -> unsafeLam (\z -> J $ readIORef a))
  return g

    Expected type: (:.) (j0 :. j1) j2 (repr Int)
      Actual type: (:.)
                     (j :. (->) (repr a)) ((->) (repr a1)) (repr Int)
    In the first argument of `unsafeLam', namely
      `(\ y
          -> J (unJ ((weaken (var x) +: var y)) >>= writeIORef a
                >> unJ (int 2)))'
-}


-- The obvious problem with exKYC1 is that inserting a beta-redex
-- breaks the code
-- That is, exKYC3 still type-checks

-- but its inferred type is different:
-- exKYC3:: (LamPure repr, SSym repr, AppLiftable j) =>
--      (IO :. (j :. (->) (repr Int))) (repr (Int -> Int -> Int))
{-
exKYC3 = J $ do
  a <- unJ (int 1) >>= newIORef
  f <- unJ $ unsafeLam (\x -> 
        unsafeLam (\dummy -> {- beta-redex -}
       unsafeLam (\y -> J (
        unJ ((weaken (weaken (var x)) +: var y)) 
  >>= writeIORef a >> unJ (int 2))))
  $$ int 100)          {- beta-redex -}
  g <- unJ $ unsafeLam (\y -> unsafeLam (\z -> J $ readIORef a))
  return g

-}

-- and so the whole program, which includes the running of the generator,
-- breaks.
-- exKYC3_c = runC exKYC3
{-
    Couldn't match expected type `Identity'
                with actual type `j0 :. (->) (repr0 Int)'
    Expected type: (:.) IO Identity (C a0)
      Actual type: (:.)
                     IO (j0 :. (->) (repr0 Int)) (repr0 (Int -> Int -> Int))
    In the first argument of `runC', namely `exKYC3'

-}

{-
-- Checking labelling
exKYCL :: (SSym repr, LamLPure repr) => 
    J (State Label IO) (HV h repr) (Int -> Int -> Int)
exKYCL = J $ do
  a <- unJ (int 1) >>= liftState . newIORef
  f <- unJ $ unsafeLamL (\x -> unsafeLamL (\y -> J (
        unJ ((weaken (var x) +: var y)) >>= 
  liftState . writeIORef a >> unJ (int 2))))
  g <- unJ $ unsafeLamL (\y -> unsafeLamL (\z -> J $ liftState $ readIORef a))
  return g

-- So, exKYCL is indeed ill-labelled 
exKYCL_c = runCL exKYCL
{-
"*** Exception: Ill-labeled: got varname x_1_3  but expected the label 1
-}


-- ------------------------------------------------------------------------
-- Insidious scope extrusion due to exceptions / delimited control
-- Although the body of `abort' (see uxs8) may be within the
-- apparent scope of lam, in the generated code it will be outside
-- the scope. 

-- The following example from TSCPS didn't type
{-
exs8 = reset (lam (\x -> int 1 +: abort (var x))
      $$ int 100)
-}

-- and it still doesn't type, for a different reason: the structure
-- of the environment differs (the outside of lam has a shorter env)
-- Even the system with well-scoped de Bruijn indices would have
-- caught this: x has the index 0 but appears as the result of
-- an expression that has the context -1 (no binding lambda)
{-
uxs80 = reset (unsafeLam (\x -> int 1 +: abort (var x))
      $$ int 100)
-}

-- However, if we use the leaked x under another lambda (in the environment
-- where the index 0 is valid again), no problems are detected

-- uxs8 :: (SSym repr, LamPure repr) => J (CPS w) (HV h repr) (Int -> Int)
uxs8 = reset (unsafeLam (\x -> int 1 +: abort (unsafeLam (\u -> (var x)))))



-- The code is well-typed and well-formed, but not intended since the
-- variable 'x' got `renamed' into the variable 'u' when it was smuggled out
uxs8c = "\\x_0 -> x_0" == runCCPS uxs8


-- without unsafeLam, we get the very precise error telling us that
-- although two environments are structurally the same,
-- (H repr s1 Int, h2) and (H repr s Int, h2)
-- they contain variables bound at different sites. Therefore,
-- these environments can't be mixed!
{-
uxs8' = reset (lam (\x -> int 1 +: abort (lam (\_ -> (var (x))))
      ))
    Couldn't match expected type `s1' against inferred type `s'
      Expected type: HV (H repr2 s1 Int, h2) repr2 Int
      Inferred type: HV (H repr2 s Int, h2) repr2 Int
-}


-- The example uxs8 is brittle in the same way as exKYC
-- If we introduce a seemingly innocuous beta-redex (beta-expand the code)

-- we break the code
{-
uxs83 = reset (unsafeLam (\x -> 
   int 1 +: abort (
                unsafeLam (\dummy -> {- beta-redex -}
                     unsafeLam (\u -> (var x)))
                $$ unsafeLam (\y-> var y)           {- beta-redex -}
               )))

    Occurs check: cannot construct the infinite type:
      h = (H repr s (a -> a), h)
      Expected type: J (CPS (J ((->) h) repr (a1 -> a1)))
                       (J ((->) h) repr)
                       (a1 -> a1)
      Inferred type: J (CPS (J ((->) h) repr (a1 -> a1)))
                       (HV (H repr s (a -> a), h) repr)
                       (a1 -> Int)
-}

-- One may think that we need weaken (although the beta-expansion
-- was introduced *outside* lam (\x -> ...), and so, no
-- weaken should be necessary
-- it breaks for a different, seemingly bizarre reason
 
{-
uxs84 = reset (unsafeLam (\x -> 
   int 1 +: abort (
                unsafeLam (\dummy -> {- beta-redex -}
                     unsafeLam (\u -> weaken (var x)))
                $$ unsafeLam (\y-> var y)           {- beta-redex -}
               )))
    Couldn't match expected type `a -> a' against inferred type `Int'
      Expected type: J (CPS (J ((->) h) repr ((a -> a) -> a -> a)))
                       (J ((->) h) repr)
                       ((a -> a) -> a -> a)
      Inferred type: J (CPS (J ((->) h) repr ((a -> a) -> a -> a)))
                       (HV h repr)
                       ((a -> a) -> Int)
-}

-- We understand the reason if we change the type of the beta-redex
-- It shouldn't matter. But it does.
-- It now type-checks

uxs85 = reset (unsafeLam (\x -> 
   int 1 +: abort (
                unsafeLam (\dummy -> {- beta-redex -}
                     unsafeLam (\u -> weaken (var x)))
                $$ int 100           {- beta-redex -}
               )))

-- but the generated code has a totally different binding structure
-- No wonder changing the type of dummy had such an effect
uxs85c = "(\\x_0 -> \\x_1 -> x_0) 100" == runCCPS uxs85

-- The following attempt to let-bind x outside its lam is prevented
-- by the s-quantification
-- ex4f1 = lam (\x -> int 1 +: genlet (var x))

-- without s, the attempt succeeds
ux4f1 = unsafeLam (\x -> int 1 +: genlet (var x))

-- The inferred type is nonsense: the answer-type is the richer environment

{-
ux4f1
  :: (SSym repr, SymLet repr, LamPure repr) =>
     J (CPS (HV (H repr s Int, h) repr w)) (HV h repr) (Int -> Int)
-}


-- So, the error will be detected eventually. But the error message would
-- be cryptic and the error will be detected far from the place it is
-- committed

-- ux4f1c = runCCPS ux4f1

-- Still, with contrivance, the type could be made sense of
ux4f2 = reset $ weaken $ unsafeLam (\x -> int 1 +: genlet (var x))

-- Again, the problem is using a term in a unrelated environment,
-- albeit with the same structure
ux4f2c = "\\x_0 -> let z_1 = x_0\n         in \\x_2 -> (GHC.Num.+) 1 z_1"
         == runCCPS (lam (\u -> ux4f2))

-- The code is well-typed and well-formed, but not intended since the
-- variable 'x' got `renamed' into the variable 'u' when it was smuggled


-- Errors like these become subtle if we use mutation, real or emulated,
-- to move the code around. Without the protection of 's', we move the
-- code with and unwittingly `rename' the variables.
-}
