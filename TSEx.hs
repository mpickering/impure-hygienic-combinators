{-# LANGUAGE Rank2Types, NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts, TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables, TypeFamilies #-}

-- Various examples of Tagless-staged, in particular
-- staged eta (the example from our PEPM08 paper) and staged twice-eta

module TSEx where

import TSCore
import Control.Applicative


ex0 = lam(\x -> int 1 +: var x)
ex0c = "\\x_0 -> (GHC.Num.+) 1 x_0" == runCI ex0

exA2:: (Applicative m, AppLiftable i, LamPure repr, SSym repr) =>
      (m :. i) (repr (Int -> Int -> Int))
exA2 = lam(\x -> lam(\y -> weaken (var x) +: var y))
exA2c = "\\x_0 -> \\x_1 -> (GHC.Num.+) x_0 x_1" == runCI exA2


-- Checking of printing and sharing

-- ex11 :: (Applicative m, Applicative i, LamPure repr, SSym repr) =>
--      (m :. i) (repr (Int -> Int -> Int))
ex11 = lam (\x -> lam (\y -> (weaken (var x) *: weaken (var x)) +: 
                       (var y *: var y)))

ex11r = 25 == runRI ex11 3 4
ex11c = 
 "\\x_0 -> \\x_1 -> (GHC.Num.+) ((GHC.Num.*) x_0 x_0) ((GHC.Num.*) x_1 x_1)"
 == runCI ex11

-- Naming of variables: we indeed use levels rather than the global
-- counter
ex12 = "(\\x_0 -> x_0) (\\x_0 -> x_0)" 
       == runCI (lam (\x -> var x) $$ lam (\x -> var x))

-- Attemping scope extrusion in a pure setting

-- tse1 :: R (R b -> b)
tse1 = lamS (\x -> unR x)
-- The code type-checks but the inferred type shows it is not a generator:
-- it is not polymorphic in repr.

-- tse2 = lam (\x -> runRI x)
{-
/home/oleg/papers/MetaFX/hybrid/TSEx.hs:46:25:
    Could not deduce (j ~ Identity)
    from the context (Applicative m)
      bound by the inferred type of
               tse2 :: Applicative m => (:.) m Identity (R (a -> b))
      at /home/oleg/papers/MetaFX/hybrid/TSEx.hs:46:1-26
    or from (AppLiftable j)
      bound by a type expected by the context:
                 AppLiftable j =>
                 (:.) Identity j (R a) -> (:.) m (Identity :. j) (R b)
      at /home/oleg/papers/MetaFX/hybrid/TSEx.hs:46:8-26
      `j' is a rigid type variable bound by
          a type expected by the context:
            AppLiftable j =>
            (:.) Identity j (R a) -> (:.) m (Identity :. j) (R b)
          at /home/oleg/papers/MetaFX/hybrid/TSEx.hs:46:8
    Expected type: (:.)
                     Identity Identity (R ((:.) m (Identity :. j) (R b)))
      Actual type: (:.) Identity j (R a)
    Relevant bindings include
      x :: (:.) Identity j (R a)
    In the first argument of `runRI', namely `x'
-}


-- The ef example from our PEPM08 paper
{-
ef = \z -> <\x -> ~z + x>
ef1 = ef <1>
ef2 = <\x y -> ~(ef <x *  y>)>

ef1 evaluates to <\x -> 1 + x> whereas ef2 evaluates to
<\x y -> \x' ->  x * y + x'>. In the latter result,
we need to distinguish two later-stage variables named x.
To maintain hygiene and \alpha-equivalence, we must lexically
link each use of a variable to its binding occurrence and
rename variables if their names clash.
-}


ef :: (Applicative m, AppLiftable i, SSym repr, LamPure repr) =>
      (m :. i) (repr Int) -> (m :. i) (repr (Int -> Int))
ef z = lam (\x -> weaken z +: var x)


ef1 = ef (int 1)

ef2 :: (Applicative m, AppLiftable i, LamPure repr, SSym repr) =>
     (m :. i) (repr (Int -> Int -> Int -> Int))
ef2 = lam (\x -> lam (\y -> ef (weaken (var x) *: var y)))

-- Check to see what ef1 and ef2 actually do.

-- instantiate repr to R

ef2r = 10 == runRI ef2 2 3 4
-- -- 10, which is 2*3 + 4 

ef1c = "\\x_0 -> (GHC.Num.+) 1 x_0" == runCI ef1

ef2c = "\\x_0 -> \\x_1 -> \\x_2 -> (GHC.Num.+) ((GHC.Num.*) x_0 x_1) x_2"
       == runCI ef2


-- Effectful code generation
-- First example: printing when generating pure functions
-- addt is the `version' of add that prints trace at the generation time

trace :: Applicative i => String -> (IO :. i) a -> (IO :. i) a
trace msg m = liftJ (putStrLn msg) *> m


addt :: (SSym repr, Applicative i) =>
     (IO :. i) (repr Int) -> (IO :. i) (repr Int) -> (IO :. i) (repr Int)
addt x y = trace "generating add" (x +: y)


ex1 :: (LamPure repr, SSym repr, AppLiftable i) => 
       (IO :. i) (repr (Int -> Int))
ex1 = trace "generating lam" $ 
      lam (\x -> var x `addt` int 1)

-- "generating add"  is printed only once, before "Generation is complete"!
ex1r = do
       f <- runR ex1
       putStrLn "Generation is complete"
       print (f 1)
       print (f 2)

ex1c = runC ex1


-- the placement of weaken below is type-directed

ex2 :: (LamPure repr, SSym repr, AppLiftable i) =>
     (IO :. i) (repr (Int -> Int -> Int))
ex2 = lam (\x -> lam (\y -> weaken (var x) `addt` var y))

-- plusM is printed only once!
ex2r = do
       f <- runR ex2
       putStrLn "Generation is complete"
       print (f 1 2)
       print (f 3 4)
{-
generating add
Generation is complete
3
7
-}

ex2c = runC ex2

{-
generating add
\x_0 -> \x_1 -> (GHC.Num.+) x_0 x_1
-}

ex2' :: (LamPure repr, SSym repr, AppLiftable i) =>
     (IO :. i) (repr (Int -> Int -> Int))
ex2' = lam (\x -> lam (\y -> vr x `addt` vr y))

ex2'c = runC ex2'
{-
generating add
"\\x_0 -> \\x_1 -> (GHC.Num.+) x_0 x_1"
(0.01 secs, 4187096 bytes)
-}

-- Cannot leak out a variable
-- ex3 = lam (\x -> weaken x)
{-
    Could not deduce (i ~ j)
      `i' is a rigid type variable bound by
          the inferred type of
          ex3 :: (Applicative m, LamPure repr, SSym repr, AppLiftable i) =>
                 (:.) m i (repr (a -> a))
          at /home/oleg/papers/MetaFX/hybrid/TSEx.hs:146:1
      `j' is a rigid type variable bound by
          a type expected by the context:
            AppLiftable j => (:.) i j (repr a) -> (:.) m (i :. j) (repr a)
          at /home/oleg/papers/MetaFX/hybrid/TSEx.hs:146:7
    Expected type: (:.) m i (repr a)
      Actual type: (:.) i j (repr a)
    In the first argument of `weaken', namely `x'
    In the expression: weaken x
-}



-- The eta example

-- All functions from code -> code have to have rank-2 type (because of the
-- parameter s marking the variables)
-- Therefore, we have to write signatures
eta :: (Applicative m, AppLiftable i, SSym repr, LamPure repr) => 
       (forall j. AppLiftable j => 
         (m :. (i :. j)) (repr a) -> (m :. (i :. j)) (repr b))
       -> (m :. i) (repr (a->b))
eta f = lam (\x -> f (var x))


teta0 = eta (\z -> int 1 +: z)
teta0c = "\\x_0 -> (GHC.Num.+) 1 x_0" 
   == runCI teta0


teta1 = lam (\y -> eta (\z -> z +: vr y))
teta1c = "\\x_0 -> \\x_1 -> (GHC.Num.+) x_1 x_0"
   == runCI teta1
teta1r = 5 == runRI teta1 2 3


-- Instantiating eta with an effectful function, which has the effect
-- at the generation time!
teta1RIO = do
     teta <- runR $ lam (\y -> eta (\z -> z `addt` vr y))
     putStrLn "Generation complete"
     print $ teta 2 3
{-
*TaglessStaged> teta1RIO
generating add
Generation complete
5
-}



-- .< fun y -> fun w -> 
--              .~(eta (fun z -> .< .~z + y*w >.)) >.)

teta2 = lam (\y -> lam (\w -> eta (\z -> 
            z +: (weaken (weaken (var y))) *: weaken (var w))))
teta2c = "\\x_0 -> \\x_1 -> \\x_2 -> (GHC.Num.+) x_2 ((GHC.Num.*) x_0 x_1)"
   == runCI teta2

teta2r = 10 == runRI teta2 2 3 4  -- 10

-- Use generic weaking
teta2' = lam (\y -> lam (\w -> eta (\z -> 
            z +: vr y *: vr w)))
teta2c' = "\\x_0 -> \\x_1 -> \\x_2 -> (GHC.Num.+) x_2 ((GHC.Num.*) x_0 x_1)"
   == runCI teta2'



-- .< fun x u -> 
--              .~(eta (fun z -> .<fun y -> .~z + u*x*y >.)) >.

-- See teta3' below for the example of eliminating repeated weaken
teta3 = lam(\x -> lam(\u -> eta (\z ->
            lam(\y -> weaken z +: (w2 u *: w3 x *: var y))
              )))
 where w2 = weaken . weaken . var
       w3 = weaken . weaken . weaken . var
 

teta3c = 
   "\\x_0 -> \\x_1 -> \\x_2 -> \\x_3 -> " ++
      "(GHC.Num.+) x_2 ((GHC.Num.*) ((GHC.Num.*) x_1 x_0) x_3)"
      == runCI teta3
teta3r = 34 == runRI teta3 2 3 4 5  -- 34

teta3' = lam(\x -> lam(\u -> eta (\z ->
            lam(\y -> weakens z +: (vr u *: vr x *: vr y))
              )))

teta3c' = 
   "\\x_0 -> \\x_1 -> \\x_2 -> \\x_3 -> " ++
      "(GHC.Num.+) x_2 ((GHC.Num.*) ((GHC.Num.*) x_1 x_0) x_3)"
      == runCI teta3'


-- Illustrating Hyland's Disjointness Property or its violation:
-- no binder ends up within a copy of itself if we stay within 
-- residual theory (of the \-calculus), i.e., if we do not contract 
-- newly created redexes.
-- Implement "(\x.x x) (\y.\z.y z) ->> \z1.\z2.z1 z2"
-- The function (\y.\z.y z) with the right staging annotations
-- is eta

-- Inferred type:
-- eta_refl :: (Applicative m, LamPure repr, SSym repr) =>
--      m (repr (a -> b)) -> m (repr (a -> b))
eta_refl = \y -> eta (\u -> weaken y $$ u)

-- etaeta :: (Applicative m, LamPure repr, SSym repr) =>
--      m (repr ((a -> b) -> a -> b))
etaeta = eta eta_refl

etaetac = "\\x_0 -> \\x_1 -> x_0 x_1"
    == runCI etaeta

etaetaetac = "\\x_0 -> (\\x_1 -> \\x_2 -> x_1 x_2) x_0"
    == runCI (eta_refl (eta eta_refl))


-- Second-order eta, the first attempt (see for a simpler expression below)
-- The signature is essentially the same as of eta
-- since a single Applicative j may hide an arbitrary number of extensions
-- Try right-associative :. ??
-- (m :. i) --> J (m (i a))
-- (m :. i :. j) --> m :. (i :. j) --> J m (J i (j a))
-- We need to essentially curry and uncurry
eta2 :: (Applicative m, AppLiftable i, SSym repr, LamPure repr) => 
       (forall j. AppLiftable j => 
        (m :. (i :. j)) (repr a) -> (m :. (i :. j)) (repr b) -> 
        (m :. (i :. j)) (repr c))
       -> (m :. i) (repr (a->b->c))
eta2 f = lam (\x -> lam (\y -> 
       unpack $ f (pack (weaken (var x))) (pack (var y))))
 where
 pack :: (Functor m, Functor i) => 
         (m :. ((i :. j1) :. j2)) a -> (m :. (i :. (j1 :. j2))) a
 pack = mapJ2 jassocp2
 unpack :: (Functor m, Functor i) => 
           (m :. (i :. (j1 :. j2))) a -> (m :. ((i :. j1) :. j2)) a
 unpack = mapJ2 jassocm2
 

teta22 = lam (\x -> lam (\y -> eta2 (\z1 z2 -> 
                  (z1 *: vr x) +:
                  (z2 *: vr y))))


teta22c = "\\x_0 -> \\x_1 -> \\x_2 -> \\x_3 -> "++
            "(GHC.Num.+) ((GHC.Num.*) x_2 x_0) ((GHC.Num.*) x_3 x_1)"
      == runCI teta22

-- Attempting to write eta2 without pack/unpack
eta2' :: (Applicative m, AppLiftable i,
          SSym repr, LamPure repr) => 
       (forall m' j. (m' ~ (m :. j), Extends (m :. i) m') =>
  m' (repr a) -> m' (repr b) -> m' (repr c))
       -> (m :. i) (repr (a->b->c))
eta2' f = lam (\x -> lam (\y -> f (weaken (var x)) (var y)))


teta2'0 :: (SSym repr, LamPure repr, Applicative m, AppLiftable i) =>
           (m :. i) (repr (Int->Int->Int))
teta2'0 = eta2' (\z1 z2 -> (z1 *: int 1) +: (z2 *: int 2))

teta2'0c =
    "\\x_0 -> \\x_1 -> (GHC.Num.+) ((GHC.Num.*) x_0 1) ((GHC.Num.*) x_1 2)"
    == runCI teta2'0

teta2'1 :: (SSym repr, LamPure repr, AppLiftable i,
            Applicative m) =>
           (m :. i) (repr (Int -> Int -> Int -> Int))
teta2'1 = lam (\y1 -> eta2' (\z1 z2 -> 
           (z1 *: vr y1) +: (z2 *: int 2)))

teta2'1c = ("\\x_0 -> \\x_1 -> \\x_2 -> "++
      "(GHC.Num.+) ((GHC.Num.*) x_1 x_0) ((GHC.Num.*) x_2 2)")
    == runCI teta2'1

-- Alas, here it fails: the compiler cannot make a simple 
-- inference of transitivity:
-- if hh extends (x1,(x2,h)) than hh certainly extends (x2,h)
{-

teta2'2 = lam' (\y1 -> lam' (\y2 -> eta2' (\z1 z2 -> 
           (z1 *: weakens y1) +:
                             (z2 *: weakens y2))))

    Could not deduce (Extends (m :. i) m')
      arising from a use of `weakens'
...
    or from (Extends ((m :. i) :. i1) m')
-}


-- We have to help the compiler out, using u and type assignment
-- We stress that we do NOT do any manipulation on values;
-- me merely specialize types to help the compiler draw the transitivity
-- inference
teta2'2 :: (SSym repr, LamPure repr, AppLiftable i, Applicative m) =>
           (m :. i) (repr (Int -> Int -> Int -> Int -> Int))
teta2'2 = lam (\y1 -> lam (\y2' -> 
                           let u = liftJ y1 `asTypeOf` y2' in
         eta2' (\z1 z2 -> 
           (z1 *: vr u) +:
                             (z2 *: vr y2'))))

teta2'2c = ("\\x_0 -> \\x_1 -> \\x_2 -> \\x_3 -> "++
      "(GHC.Num.+) ((GHC.Num.*) x_2 x_0) ((GHC.Num.*) x_3 x_1)")
     == runCI teta2'2

{- Further generalization of eta: statically unknown number of
   new bindings

let rec etan f = function
 | 0 -> .<fun x -> .~(f .<x>.)>.
 | n -> .<fun x -> .~(etan (fun z -> f .<.~z + x>.) (n-1)) x>.
;;
-}

-- Attempting to write in a nice form
{-
etan :: (Applicative m, AppLiftable i,
          SSym repr, LamPure repr) => 
        (forall j. Extends (m :. i) (m :. j) =>
         (m :. j) (repr Int) -> (m :. j) (repr Int))
       -> Int
       -> (m :. i) (repr (Int -> Int))
etan f 0 = lam (\x -> f (var x))
etan f n = lam (\x -> etan (\z -> f (z +: vr x)) (n-1) $$ (var x))
-}
-- Alas, it fails:
--    Could not deduce (Extends (m :. i) (m :. j1))
--    from (Extends (m :. (i :. j)) (m :. j1))
-- Alas, we can't easily control the type of the first
-- argument of Extends (the second argument is easy: the type
-- of the argument of f, which we can easily control).
-- So, we are stuck.

etan :: (Applicative m, AppLiftable i,
          SSym repr, LamPure repr) => 
        (forall j. AppLiftable j =>
         (m :. (i :. j)) (repr Int) -> (m :. (i :. j)) (repr Int))
       -> Int
       -> (m :. i) (repr (Int -> Int))
etan f 0 = lam (\x -> f (var x))
etan f n = lam (\x -> etan (\z -> c1 (f (c2 (z +: vr x)))) (n-1) $$ (var x))
 where
   c2 :: (Functor m, Functor i, AppLiftable jx, AppLiftable je) =>
         (m :. ((i :. jx) :. je)) a -> (m :. (i :. (jx :. je))) a
   c2 = J . fmap (J . fmap J . unJ . unJ) . unJ
   c1 :: (Functor m, Functor i, AppLiftable jx, AppLiftable je) =>
         (m :. (i :. (jx :. je))) a -> (m :. ((i :. jx) :. je)) a
   c1 = J . fmap (J . J . fmap unJ . unJ) . unJ


tetan2c =
  "\\x_0 -> (\\x_1 -> (\\x_2 -> (GHC.Num.+) ((GHC.Num.+) x_2 x_1) x_0) x_1) x_0" ==
  runCI (etan id 2)

tetan2r =
  3 ==
  runRI (etan id 2) 1

-- Tests of the let-form

tl0 = let x = (trace "Let RHS" (int 1 +: int 2)) in x *: x

tl0r = fmap (9 ==) $ runR tl0
{-
Let RHS
Let RHS
True
-}

tl0c = fmap ("(GHC.Num.*) ((GHC.Num.+) 1 2) ((GHC.Num.+) 1 2)" == ) $
       runC tl0
{-
Let RHS
Let RHS
-}

tl1 = let_ (trace "Let RHS" (int 1 +: int 2)) $ \x -> var x *: var x

-- The message is printed only once! And our generation effect is applicative,
-- not a monad!
tl1r = fmap (9 ==) $ runR tl1
{-
Let RHS
True
-}


-- Again, the trace message is printed only once
tl1c = fmap ("let z_0 = (GHC.Num.+) 1 2\n in (GHC.Num.*) z_0 z_0"==) $ runC tl1
{-
Let RHS
let z_0 = 1
 in (GHC.Num.+) z_0 z_0
-}

-- Very simple let-insertion

newtype CPS w a = CPS{unCPS :: (a -> w) -> w}
runCPS :: CPS a a -> a
runCPS m = unCPS m id

instance Functor (CPS w) where
  fmap f (CPS x) = CPS $ \k -> x (k . f)

instance Applicative (CPS w) where
  pure x = CPS $ \k -> k x
  CPS f <*> CPS x = CPS $ \k -> f (\fv -> x (\xv -> k (fv xv)))
  
reset :: CPS a a -> CPS w a
reset m = CPS $ \k -> k (runCPS m)

genlet_simple :: (SSym repr, SymLet repr) =>
  CPS (repr a) (repr a) -> CPS (repr w) (repr a)
genlet_simple e = CPS $ \k -> let_S (runCPS e) (\z -> k z)

tglet = reset (int 1 +: genlet_simple (int 2 +: int 3))
tgletc =
  ("let z_0 = (GHC.Num.+) 2 3\n in (GHC.Num.+) 1 z_0" ==) $
  (runCS . runCPS $ tglet)

genlet_simple' ::
  (CPS (i (repr w)) :. i) (repr a) ->
  (CPS (i (repr w)) :. (i :. j)) (repr a)
genlet_simple' = undefined
toosimple1 e = lam (\x -> var x +: genlet_simple' e)
  
-- How to deal with polymoprhic let?
-- The following code is essentially
--   let tl2a = lam (\x -> var x) in tl2a $$ tl2a
-- that handles polymorphism by inlining.

tl2a :: (SSym repr, LamPure repr, Applicative m, AppLiftable i) =>
     (m :. i) (repr (a -> a))
tl2a = lam (\x -> var x)

tl2 = tl2a $$ tl2a
tl2c = "(\\x_0 -> x_0) (\\x_0 -> x_0)" == runCI tl2

-- To do otherwise, we first need a polymorphic let in the object
-- language. We need new lam, for example, of the type
-- lamP :: (forall a s.
--  HV (H repr s A a, h) repr (A a) 
--       -> J m (HV (H repr s (A a), h) repr) (B a))
--     -> J m (HV h repr) (Arr A B)
-- where A and B are some type constructors (not necessarily functors:
-- perhaps newtype over type function).

main = foldr ((&&)) True [
       ex0c, exA2c,
       ex11r, ex11c,
       ex12,
       ef2r, ef1c, ef2c, 
       teta0c, 
       teta1c, teta1r, 
       teta2c, teta2r,
       teta2c', 
       teta3c, teta3r,
       teta3c',
       etaetac, etaetaetac,
       teta22c, 
       teta2'0c, teta2'1c, teta2'2c,
       tetan2c, tetan2r,
       tl2c, tgletc
       ]
