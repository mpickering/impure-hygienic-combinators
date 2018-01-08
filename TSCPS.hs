{-# LANGUAGE NoMonomorphismRestriction, Rank2Types #-}

-- Tagless Staged with the Cont as the generating applicative
-- Let-insertion

module TSCPS where

import TSCore
import Control.Applicative

-- We use the CPS monad with explicit answer-type parameter
-- (which is essentially the monad for delimited control)

newtype CPS w a = CPS{unCPS :: (a -> w) -> w}

        -- I wish I didn't have to write it!
instance Functor (CPS w) where
    fmap f m = pure f <*> m

instance Applicative (CPS w) where
    pure x  = CPS $ \k -> k x
    f <*> m = CPS $ \k -> unCPS f (\fv -> unCPS m (\mv -> k (fv mv)))

runCPS :: CPS a a -> a
runCPS m = unCPS m id

runRCPS = runCPS . runR
runCCPS = runCPS . runC

-- Useful abstractions
type K a b = a -> b     -- Captured delimited continuation

reset_ :: CPS a a -> CPS w a
reset_ m = pure $ runCPS m

shift_ :: (K a w -> CPS w w) -> CPS w a
shift_ f = CPS $ \k -> runCPS (f k)

throw_ :: K a b -> CPS w a -> CPS w b
throw_ k m = fmap k m



-- more detailed signatures

reset :: J (CPS (repr a)) repr a -> J (CPS w) repr a
reset = J . reset_ . unJ

shift :: (K (HV ha repr a) (HV hw repr w) 
      -> J (CPS (HV hw repr w)) (HV hw repr) w) 
         -> J (CPS (HV hw repr w)) (HV ha repr) a
shift f = J $ shift_ (\k -> unJ (f k))

abort :: J (CPS (HV h repr b)) (HV h repr) b
         -> J (CPS (HV h repr b)) (HV h1 repr) a
abort e = J $ shift_ (\_ -> unJ e)


throw :: K (HV ha repr a) (HV hb repr b)
   -> J (CPS w) (HV ha repr) a -> J (CPS w) (HV hb repr) b
throw k = J . throw_ k . unJ

-- ------------------------------------------------------------------------
-- Basic examples of code generation with delimited control

-- Without control effects, reset does not do anything
exr0 = reset $ lam (\x -> var x +: int 1)
exr0r = 11 == runRCPS exr0 10
exr0c = "\\x_0 -> (GHC.Num.+) x_0 1" == runCCPS exr0


-- exs2 :: (SSym repr) => J (CPS w) (HV h repr Int)
exs2 = reset (int 1 +: abort (int 2))
exs2r = 2 == runRCPS exs2
exs2c = "2" == runCCPS exs2

exs3 = reset (int 1 +: shift (\k -> throw k (int 2 +: int 1)))
exs3r = 4 == runRCPS exs3
exs3c = "(GHC.Num.+) 1 ((GHC.Num.+) 2 1)" == runCCPS exs3


exs4 = reset (int 1 +: shift (\k -> int 2 +: (throw k (int 1))))
exs4r = 4 == runRCPS exs4
exs4c = "(GHC.Num.+) 2 ((GHC.Num.+) 1 1)" == runCCPS exs4


exs5 = reset (int 1 +: shift (\k -> int 2 +: 
           (throw k (int 1) +: throw k (int 3))))
exs5r = 8 == runRCPS exs5
exs5c = "(GHC.Num.+) 2 ((GHC.Num.+) ((GHC.Num.+) 1 1) ((GHC.Num.+) 1 3))"
  == runCCPS exs5


exs6 = reset (lam (\x -> int 1 +: (weaken $ shift (\k -> 
                lam (\x -> int 100)))))
exs6r = 100 == runRCPS exs6 42
exs6c = "\\x_0 -> 100" == runCCPS exs6

exs7 = reset (lam (\x -> int 1 +: (weaken $ abort (int 2))) $$ int 100)
exs7r = 2 == runRCPS exs7
exs7c = "2" == runCCPS exs7

-- Attempting to smuggle out the bound variable: won't type
{-
exs8 = reset (lam (\x -> int 1 +: abort (var x))
      $$ int 100)
    Inferred type is less polymorphic than expected
      Quantified type variable `s' escapes
    In the first argument of `lam', namely
        `(\ x -> int 1 +: abort (var x))'
-}


-- But the following does:
exs9 = reset (lam (\x -> int 1 +: shift (\k -> throw k (var x)))
      $$ int 100)

exs9r = 101 == runRCPS exs9
exs9c = "(\\x_0 -> (GHC.Num.+) 1 x_0) 100" == runCCPS exs9


-- To prevent the smuggling out of the bound variable, we have
-- to insert reset under lambda

exs81 = reset (lam (\x -> reset (int 1 +: (abort (var x))))
        $$ int 100)

exs81r = 100 == runRCPS exs81
exs81c = "(\\x_0 -> x_0) 100" == runCCPS exs81


-- Throwing things across many binders

exs10 = reset (lam (\x -> int 1 +: (lam(\y ->
              shift (\k -> throw k (var y)  *: throw k (var y))) $$ int 5))
               $$ int 100)

exs10r = 36 == runRCPS exs10

exs10c = "(GHC.Num.*) "++
   "((\\x_0 -> (GHC.Num.+) 1 ((\\x_1 -> x_1) 5)) 100) "++
   "((\\x_0 -> (GHC.Num.+) 1 ((\\x_1 -> x_1) 5)) 100)"
   == runCCPS exs10

exs11 = reset (lam (\x -> int 1 +: (lam(\y ->
              shift (\k -> throw k (weaken (var x)) *: 
               throw k (var y))) $$ int 5))
               $$ int 100)

exs11r = 606 == runRCPS exs11
exs11c = "(GHC.Num.*) "++
   "((\\x_0 -> (GHC.Num.+) 1 ((\\x_1 -> x_0) 5)) 100) "++
   "((\\x_0 -> (GHC.Num.+) 1 ((\\x_1 -> x_1) 5)) 100)"
   == runCCPS exs11

-- But we can't leak a variable
{-
exs12 = reset (lam (\x -> int 1 +: (lam(\y ->
              shift (\k -> var y +: throw k (weaken (var x)) *: 
               throw k (var y))) $$ int 5))
               $$ int 100)
    Inferred type is less polymorphic than expected
      Quantified type variable `s' escapes
    In the first argument of `lam', namely
        `(\ y -> shift ...
-}


-- ------------------------------------------------------------------------
-- Let-insertion


-- Baseline: using let in the metalanguage leads to code duplication
-- Code generation breaks the sharing. We need let in the object language
ex41 = let e = int 1 +: int 1 in e +: e
ex41c = "(GHC.Num.+) ((GHC.Num.+) 1 1) ((GHC.Num.+) 1 1)"
  == runCCPS ex41


-- The naive attempt doesn't work: we seemingly leak the variable
{-
genlet e = shift (\k -> let_ e (\x -> throw k (var x)))

    Inferred type is less polymorphic than expected
      Quantified type variable `s' is mentioned in the environment:
        k :: K (HV repr (H repr s a, h) a) (HV repr (H repr s a, h) b)
          (bound at /home/oleg/papers/MetaFX/hybrid/TSCPS.hs:168:19)
        e :: CPS (HV repr (H repr s a, h) b) (HV h repr a)
          (bound at /home/oleg/papers/MetaFX/hybrid/TSCPS.hs:168:7)
    In the second argument of `let_', namely `(\ x -> throw k (var x))'
-}
-- An explicit version of the naive attempt
-- genlet' e = CPS $ \k -> runCPS $ let_ e (\x -> pure (k x))

gennolet :: J (CPS w) (HV h repr) a -> J (CPS w) (HV h repr) a
gennolet e = J . CPS $ \k -> unCPS (unJ e) (\v -> k v)

{-
-- Therefore, we need a controversial
weaken_cont :: K (HV ha repr a) (HV hb repr b) ->
    K (HV (h1,ha) repr a) (HV (h1,hb) repr b)


weaken_cont k = 
   \h1haa (h1,hb) -> k (\ha -> h1haa (h1,ha)) hb

-- We need weakening of a captured
-- continuation, which is, recall, an (env -> repr) transformer.
-- This is sort of pack/unpack...

genlet' :: (SSym repr, SymLet repr) =>
     CPS (HV hw repr w) (HV hw repr a) -> CPS (HV hw repr w) (HV ha repr a)
genlet' e = shift (\k -> letA e (\x -> throw (weaken_cont k) (var x)))
-}



-- A more explicit version:
genlet :: (SSym repr, SymLet repr) =>
     J (CPS (HV hw repr w)) (HV hw repr) a 
     -> J (CPS (HV hw repr w)) (HV ha repr) a
genlet e = J . CPS $ \k -> runCPS . unJ $ let_ e (\x -> 
   J . pure . J $ \ (h1,hw) -> unJ (k (J (\ha -> unJ x (h1,())))) hw)

ex42 = reset $ int 1 +: genlet (int 2 +: int 3)
ex42c = "let z_0 = (GHC.Num.+) 2 3\n in (GHC.Num.+) 1 z_0" == runCCPS ex42
ex42r = 6 == runRCPS ex42

-- Let-insertion across binder
ex43 = reset $ lam (\x -> var x +: genlet (int 2 +: int 3))
ex43c = "let z_0 = (GHC.Num.+) 2 3\n in \\x_1 -> (GHC.Num.+) x_1 z_0"
        == runCCPS ex43
ex43r = 105 == runRCPS ex43 100

-- Can't leak a variable
{-
ex4f1 = lam (\x -> int 1 +: genlet (var x))

    Inferred type is less polymorphic than expected
      Quantified type variable `s' escapes
    In the first argument of `lam', namely
        `(\ x -> int 1 +: genlet (var x))'
-}

-- Let-insertion through several binders
ex44 = reset $ lam (\x -> lam (\y -> var y +: weaken (var x) +:
        genlet (int 2 +: int 3)))
ex44c = "let z_0 = (GHC.Num.+) 2 3\n "++
        "in \\x_1 -> \\x_2 -> (GHC.Num.+) ((GHC.Num.+) x_2 x_1) z_0"
        == runCCPS ex44
ex44r = 405 == runRCPS ex44 300 100


{-
ex450 = reset $ lam (\x -> (lam (\y -> var y +: weaken (var x) +:
        genlet (var x +: int 3))))

    Inferred type is less polymorphic than expected
      Quantified type variable `s' escapes
    In the first argument of `lam', namely
        `(\ x -> (lam ...
-}

ex45 = lam (\x -> reset (lam (\y -> var y +: weaken (var x) +:
        genlet (var x +: int 3))))

ex45c = "\\x_0 -> let z_1 = (GHC.Num.+) x_0 3\n         in "++
        "\\x_2 -> (GHC.Num.+) ((GHC.Num.+) x_2 x_0) z_1"
  == runCCPS ex45
ex45r = 123 == runRCPS ex45 10 100


-- More complex examples: inserting several let

ex46 = int 1 +: genlet (int 2 +: genlet (int 3 +: int 4))
       +: genlet (int 5 +: int 6)
       
ex46c = ("let z_0 = (GHC.Num.+) 3 4\n in "++
   "let z_1 = (GHC.Num.+) 2 z_0\n     in "++
   "let z_2 = (GHC.Num.+) 5 6\n         "++
   "in (GHC.Num.+) ((GHC.Num.+) 1 z_1) z_2")
  == runCCPS (reset ex46)



ex47 = lam (\x -> int 1 +: genlet (int 2 +: genlet (int 3 +: int 4))
       +: genlet (int 5 +: int 6))
       
ex47c = ("let z_0 = (GHC.Num.+) 3 4\n in "++
   "let z_1 = (GHC.Num.+) 2 z_0\n     in "++
   "let z_2 = (GHC.Num.+) 5 6\n         "++
   "in \\x_3 -> (GHC.Num.+) ((GHC.Num.+) 1 z_1) z_2")
  == runCCPS (reset ex47)


{- x escapes

ex48 = lam (\x -> int 1 +: genlet (var x +: genlet (int 3 +: int 4))
       +: genlet (int 5 +: int 6))
-}


ex49 = lam (\x -> reset (lam (\y ->
         int 1 +: genlet (var x +: genlet (int 3 +: int 4))
       +: genlet (int 5 +: int 6))))
       
ex49c = ("\\x_0 -> let z_1 = (GHC.Num.+) 3 4\n"++
   "         in let z_2 = (GHC.Num.+) x_0 z_1\n"++
   "             in let z_3 = (GHC.Num.+) 5 6\n"++
   "                 in \\x_4 -> (GHC.Num.+) ((GHC.Num.+) 1 z_2) z_3") 
  == runCCPS (reset ex49)

-- Although ex49c does insert lets, we would like to let-bind 3+4
-- outside of the outermost lambda, since we the rhs doesn't contain
-- any variable.
-- We need several levels of effects.

main = and [
           exr0r, exr0c,
     exs2r, exs2c,
     exs3r, exs3c,
     exs4r, exs4c,
     exs5r, exs5c,
     exs6r, exs6c,
     exs7r, exs7c,
     exs9r, exs9c,
     exs81r, exs81c,
     exs10r, exs10c,
     exs11r, exs11c,

     ex41c,
           ex42r, ex42c,
           ex43r, ex43c,
           ex44r, ex44c,
           ex45r, ex45c,
           ex46c,
           ex47c,
           ex49c
     ]
