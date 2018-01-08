{-# LANGUAGE RankNTypes, TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
-- {-# OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- Tagless Final with staging
-- The core of the code generation framework

module TSCore (
  SSym(..),
  LamPure(..),
  runCS, unR,

  (+:), (*:), int, ($$),
  var, weaken, lam, Extends(..), vr,
  AppLiftable(..), liftJ, (:.)(..), mapJ2, jassocm2, jassocp2,

  runR, runRI,
  runC, runCI,
  AssertPos, assertPos,

  SymDIV, (/:),
  SymLet(..), let_, let__,

  -- Generating imperative code
  SymBind(..), gretS, gret, (>>:), (=<<:),
  SymLoop, loop,
  SymMin, min_,

  -- Vectors and matrices
  SymMat(..), SymVec(..),
  vec_new_, vec_get_, vec_set_, vec_addto_, vec_clear_,
  mat_new_, mat_get_, mat_set_,
    -- and the corresponding code generators
  vec_new, vec_get, vec_set, vec_addto, vec_clear,
  mat_new, mat_get, mat_set,

  -- Needed only for well-labellness tests, not used in production
  -- LamLPure, State, liftState, Label, lamL, runCL, runCLI

  ErrorA(..),
  ) where

import Control.Applicative
import Control.Exception (assert)
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Ppr
import Data.List (isSuffixOf)

import Control.Monad (ap, liftM, forM_)
import Control.Monad.Identity
import Control.Monad.Trans (MonadIO(..))
import Data.Array.MArray
import Data.Array.IO


-- The object language (EDSL)

-- A Haskell value of the type SSym repr => repr a
-- represents an expression in the object language of the type a

-- There is no lam form; See the class LamPure below
-- dedicated to abstractions.
class SSym repr where
    intS :: Int -> repr Int
    addS :: repr (Int -> Int -> Int)
    mulS :: repr (Int -> Int -> Int)

    appS :: repr (a->b) -> (repr a -> repr b)


{-
The connection to MetaOCaml

Unlike MetaOCaml, based on brackets and escapes for building
code values, we use combinators for code generation (cf. Xi and Thiemann).
Here is how our combinators could be defined in terms of
brackets and escapes:

let intS x  =  <x>
let addS    =  <(+)>
let appS x y =  <~x ~y>

let lamS f   =  <fun x -> ~(f <x>)>

The combinators intS, addS, appS build code _values_, which are inert
at present stage and whose building involves no effect.
-}

exS1 :: SSym repr => repr Int
exS1 = (addS `appS` intS 1) `appS` intS 2
exS1c = runCS exS1
-- "(GHC.Num.+) 1 2"

-- ------------------------------------------------------------------------
-- The interpreters for our DSL

-- The evaluator
newtype R a = R{unR :: a}
-- In other words:
-- newtype R a = R a
-- unR (R x) = x
-- which shows the isomorphism between Haskell types and DSL types

instance SSym R where
    intS = R
    addS = R (+)
    mulS = R (*)
    R x `appS` R y = R $ x y

-- The C interpreter, the compiler
-- We mostly use it to show the code

type VarCounter = Int   -- we will see the need for it shortly, lamS

      -- the pure code value, the analogue
      -- of <1> or <fun x -> x> in MetaOCaml
newtype C a = C{unC :: VarCounter -> Exp}

-- OCaml type 'a c = {unC: varcounter -> exp}

instance SSym C where
    intS = C . const . LitE . IntegerL . fromIntegral
    addS = C $ const $ VarE $ '(Prelude.+)
    mulS = C $ const $ VarE $ '(Prelude.*)
    C x `appS` C y = C $ \vc -> AppE (x vc) (y vc)

runCS :: C a -> String
runCS m = pprint $ unC m 0

-- ------------------------------------------------------------------------
-- Adding `purely generated' lambda-expressions to our EDSL
-- Any effect of generating their body can't propagate past
-- the binder.
-- See below for more general lambda-expressions


class LamPure repr where
    lamS :: (repr a -> repr b) -> repr (a->b)

-- We extend the R and C interpreters
-- The extensions are quite like
-- that in our Tagless-Final paper

instance LamPure R where
    lamS f = R $ unR . f . R

instance LamPure C where
    lamS f = C $ \vc ->
       let name = mkName $ "x_" ++ show vc
           body = unC (f (C . const $ VarE name)) (succ vc)
             in LamE [VarP name] body

-- ------------------------------------------------------------------------
-- Code combinators: generating code in an Applicative m
-- The code is pure but its generation may have an effect.

-- A Haskell value of the type
-- (Applicative m, SSym repr) => m (repr a)
-- represents a generator, in the generating applicative m,
-- of the expression in the object language of the type a

infixl 2 $$
($$) :: (SSym repr, Applicative m) =>
        m (repr (a->b)) -> m (repr a) -> m (repr b)
f $$ x = appS <$> f <*> x

int :: (SSym repr, Applicative m) => Int -> m (repr Int)
int = pure . intS

infixl 7 *:
infixl 6 +:

(+:) :: (SSym repr, Applicative m) =>
        m (repr Int) -> m (repr Int) -> m (repr Int)
x +: y = pure addS $$ x $$ y

(*:) :: (SSym repr, Applicative m) =>
        m (repr Int) -> m (repr Int) -> m (repr Int)
x *: y = pure mulS $$ x $$ y


-- ------------------------------------------------------------------------
-- Applicatives compose
-- A composition of two applicatives is an applicative

-- Composition of two type constructors (kind * -> *)
newtype (i :. j) a = J{unJ:: i (j a)}

instance (Functor i, Functor j) => Functor (i :. j) where
    fmap f (J x) = J $ fmap (fmap f) x

instance (Applicative i, Applicative j) =>
    Applicative (i :. j) where
  pure = J . pure . pure
  J f <*> J x = J $ (<*>) <$> f <*> x

liftJ :: (Applicative m, Applicative i) =>
          m a -> (m :. i) a
liftJ = J . fmap pure

-- A very common operation
mapJ2 :: Functor m => (i a -> j a) -> (m :. i) a -> (m :. j) a
mapJ2 f = J . fmap f . unJ

liftJ2 :: (Applicative m, Applicative i, Applicative j) =>
          (m :. i) a -> (m :. (i :. j)) a
liftJ2 = mapJ2 liftJ

-- Composition of applicatives, just like any composition, is
-- associative
-- Here are the witnesses

jassocp2 :: Functor m => ((m :. i1) :. i2) a -> (m :. (i1 :. i2)) a
jassocp2 (J (J mi1i2)) = J (fmap J mi1i2)
jassocm2 :: Functor m => (m :. (i1 :. i2)) a -> ((m :. i1) :. i2) a
jassocm2 (J mJi1i2) = J . J $ (fmap unJ mJi1i2)


{-
-- `Injecting' a monad into an Applicative stack
-- The following class witnesses that the applicative n is `above'
-- monad m.
-- The operation bindA looks quite like monadic bind, with quite an
-- important difference

class (Monad m, Applicative m, Applicative n) => Above m n where
    bindA :: m a -> (a -> n b) -> n b

instance (Monad m, Applicative m) => Above m m where
    bindA = (>>=)

instance (Applicative i, Monad m, Applicative m, Above m n) =>
    Above m (n :. i) where
    m `bindA` f = J $ m `bindA` (unJ . f)

-- we could replace Above with Extends. However, we would need the
-- inductive instance (the last above) for the inference to go through.
-}


{-
Like MetaOCaml, we also keep track of the (future stage) environment,
distinguishing a closed expression like <1> from the open expression
<x>.  We keep a far detailed track than does MetaOCaml, tracking each
free variable rather than a set of variables of the same classifier.
Thus our type (i (repr a)) is _roughly_ equivalent to (('h,'a) code) of
MetaOCaml.  Roughly because 'h' has a lot more structure than just the
single qualifier.

We are more precise than MetaOCaml in another aspect, keeping track
of effects of code generation as well. In MetaOCaml, as in OCaml in
general, all expressions are effectful. Therefore, our type
(m (i (repr a))) corresponds to a general MetaOCaml expression, with
effects, that will generate the code of type a in the future
stage environment h.
-}

-- We use higher-order abstract syntax for abstractions.
-- The body of lam could receive (m :. (i :. j)) (repr a)
-- However, that creates the fatal problem for let-insertion, where
-- m is CPSA w m' and using the variable in a let-expression, as in
--   lam (\x -> resetJ $ lam (\y -> genlet (x +: int 1)))
-- will hence affect the answer-type w of the outer lam.
-- After all, a variable is a value, that is, it is effect-free
-- and must be answer-type polymorphic. Therefore, we use the type
-- for the future-stage (i :. j) (repr a) variable.
-- The explicit environment (i :. j) makes it easy to to weakens,
-- weakening by arbitrary amounts.

lam :: (Applicative m, AppLiftable i, SSym repr, LamPure repr) =>
       (forall j. AppLiftable j =>
        (i :. j) (repr a) -> (m :. (i :. j)) (repr b))
       -> (m :. i) (repr (a->b))
lam f = fmap lamS (J . fmap unJ . unJ $ f  (J . pure $ v))
 where
 -- instantiate applicative j to be a Reader: repr a -> w
 v = \repra -> repra                    -- bound variable

-- Make a variable an expression
var :: Applicative m => i (repr a) -> (m :. i) (repr a)
var = J . pure

-- Just a specialization of liftJ2
weaken :: (Applicative m, Applicative i, Applicative j) =>
          (m :. i) (repr a) -> (m :. (i :. j)) (repr a)
weaken = liftJ2

-- Exercise: implement the simpler lamS in terms of lam
-- Question by Eric Crockett

data W repr a = W{unW :: repr a}

instance (SSym repr, LamPure repr) => LamPure (W repr) where
    -- lamS :: (repr a -> repr b) -> repr (a->b)
  -- Choosing m and i to be Identity
  lamS (f :: W repr a -> W repr b) =
    W . runIdentity . runIdentity . unJ $ lam g
    where
      g :: forall j. AppLiftable j => (Identity :. j) (repr a)
          -> (Identity :. (Identity :. j)) (repr b)
      g x =
            let jx :: j (repr a)
                jx = runIdentity . unJ $ x
                yv :: j (repr b)
                yv = fmap (unW . f . W) jx
            in J (Identity (J (Identity yv)))

-- Generic var
-- inject (i (repr a)) in the right place in the overall stack
-- m (i1 (i2 ... (in (repr a)))) using the approporiate number of weaken
-- In other words, this is like weakens . var
-- Ideally, this operation could be implemented as follows:
--  if the type of the computation is (m :. i1) and i1 is equal to i,
--  then injection is just 'var' (or, pure).
--  Otherwise, repeat by injecting i (repr a) into m (repr a), and
--  weaken the result.
-- Obviously this algorithm requires type comparison, which is
-- implementable with closed type families.

-- Generic weakening
-- Reflexive transitive closure of weaken
-- The constraint Extends h h'  asserts that the environment h'
-- is either equal to h or is an extension of h with more bindings.
-- The assertion is proved by inserting the needed number of
-- weaken

class (Applicative m, Applicative n) => Extends m n where
    weakens :: m a -> n a

instance Applicative m => Extends m m where
    weakens = id

-- The following is simple but obviously non-generic.
-- See the Regions paper for the generic, inductive weakening
instance (Applicative m, Applicative i) => Extends m (m :. i) where
    weakens = liftJ


instance (Applicative m, Applicative i, Applicative j) =>
   Extends (m :. i) (m :. (i :. j)) where
    weakens = liftJ2

instance (Applicative m,
          Applicative i,
          Applicative j1,
          Applicative j2) =>
   Extends (m :. i) (m :. ((i :. j1) :. j2)) where
    weakens = liftJ2 . liftJ2

instance (Applicative m,
          Applicative i,
          Applicative j1,
          Applicative j2,
          Applicative j3) =>
   Extends (m :. i) (m :. (((i :. j1) :. j2) :. j3)) where
    weakens = liftJ2 . liftJ2 . liftJ2

instance (Applicative m,
          Applicative i,
          Applicative j1,
          Applicative j2,
          Applicative j3,
          Applicative j4) =>
   Extends (m :. i) (m :. ((((i :. j1) :. j2) :. j3) :. j4)) where
    weakens = liftJ2 . liftJ2 . liftJ2 . liftJ2

-- witnessing transitivity
newtype Tr (i :: * -> * ) (j0 :: * -> * ) j a =
  Tr{unTr :: j a}
  deriving (Functor, Applicative)

instance (Extends i j0, Extends j0 j) =>
         Extends i (Tr i j0 j) where
  weakens (m :: i a) = Tr (weakens ((weakens m) :: j0 a))

-- we could compose weakens with var

vr :: forall i j m repr a. (Applicative m) =>
      Extends (m :. i) (m :. j) => i (repr a) -> (m :. j) (repr a)
vr = (weakens :: (m :. i) (repr a) -> (m :. j) (repr a)) . var


{- Generic instance: needs closed type families or overlapping instances
instance (Extends m n, Applicative i, x ~ (n :. i)) => Extends m x where
    weakens = liftJ . weakens
-}

-- Functions to obtain the results

runR :: Applicative m => (m :. Identity) (R a) -> m a
runR = fmap runIdentity . unJ . fmap unR

-- Specialized instances of runR
runRI :: (Identity :. Identity) (R a) -> a
runRI = runIdentity . runR

runC :: Applicative m => (m :. Identity) (C a) -> m String
runC = fmap runIdentity . unJ . fmap runCS

-- Specialized instances of runC
runCI :: (Identity :. Identity) (C a) -> String
runCI = runIdentity . runC


-- ------------------------------------------------------------------------
-- Adding a new DSL feature: assertions
-- (to check the assertion insertion)
--   assertPos test x
-- checks that the value of test is positive. If so, it returns x.
-- Otherwise, a run-time error is generated

class AssertPos repr where
    assertPosS :: repr Int -> repr a -> repr a


instance AssertPos R where
    assertPosS (R test) (R x) = R $ assert (test > 0) x

instance AssertPos C where
    assertPosS (C test) (C x) =
      C $ \vc -> AppE (AppE assertName (testE (test vc))) (x vc)
        where
          testE exp = InfixE (Just exp) ge (Just zero)
          zero = LitE . IntegerL . fromIntegral $ 0
          ge = VarE $ '(Prelude.>)
          assertName = VarE $ 'Control.Exception.assert

assertPos :: (AssertPos repr, Applicative m) =>
             m (repr Int) -> m (repr a) -> m (repr a)
assertPos = liftA2 assertPosS


-- ------------------------------------------------------------------------
-- Adding a new DSL feature: integer division
-- (for the sake of the assertion-insertion example)

class SymDIV repr where
    divS :: repr (Int -> Int -> Int)

instance SymDIV R where
    divS = R div

instance SymDIV C where
    divS = C $ const $ VarE $ 'Prelude.div

infixl 7 /:

(/:) :: (Applicative m, SSym repr, SymDIV repr) =>
  m (repr Int) -> m (repr Int) -> m (repr Int)
x /: y = pure divS $$ x $$ y

-- ------------------------------------------------------------------------
-- Adding a new DSL feature: let-expressions
-- Not surprisingly, it looks like a `composition' of lam and app

class SymLet repr where
    let_S :: repr a -> (repr a -> repr b) -> repr b

-- In a pure language, let_S is a reverse application, as expected
instance SymLet R where
    let_S rhs f = f rhs

instance SymLet C where
    let_S rhs f = C $ \vc ->
       let name = mkName $ "z_" ++ show vc
           body = unC (f (C . const $ VarE name)) (succ vc)
             in LetE [ValD (VarP name) (NormalB $ unC rhs vc) []] body

-- We define let_ as a `combination' of lam and application.
-- Hence the following type, which ensures that the let-bound variable
-- does not escape the scope of the binding.

-- This let__ is useful for let-insertion (although we can
-- do without it, by replacing AppLiftable with AppIdempotent)
let__ :: (SSym repr, SymLet repr, Applicative m, Applicative i) =>
      (m :. i) (repr a)
      -> (forall j. AppLiftable j =>
          j (repr a) -> (m :. (i :. j)) (repr b))
      -> (m :. i) (repr b)
let__ rhs fbody = let_S <$> rhs <*> (J . fmap unJ . unJ)
                                     (fbody (\repra -> repra))

-- The regular let_ is defined in terms of let__
let_ :: (SSym repr, SymLet repr, Applicative m, Applicative i) =>
      (m :. i) (repr a)
      -> (forall j. AppLiftable j =>
          (i :. j) (repr a) -> (m :. (i :. j)) (repr b))
      -> (m :. i) (repr b)
let_ rhs fbody = let__ rhs (\z -> fbody (var z))

{-

-- ------------------------------------------------------------------------
-- Adding a new DSL feature: labels on lam and variables
-- and checking of the labels

type Label = Int

class LamLPure repr where
    lamSL :: Label -> (repr a -> repr b) -> repr (a->b)
    check_label :: Label -> repr a -> repr a

instance LamLPure C where
    lamSL l f = C $ \vc ->
       let name = mkName $ "x_" ++ show vc ++ "_" ++ show l
           body = unC (f (C . const $ VarE name)) (succ vc)
             in LamE [VarP name] body

    check_label l v@(C c) =
         let (VarE name) = c 0 in
         if isSuffixOf ("_"++show l) (show name) then v
            else error $ unwords ["Ill-labeled: got varname",show name,
          " but expected the label", show l]

-- used internally
hrefL :: LamLPure repr => Label -> HV (H repr s a,h) repr a
hrefL l = J $ \ (H x,h) -> check_label l x

-- lamL uniquely labels the introduced free variable promise and the
-- generated binder
lamL :: (Functor m, Monad m, SSym repr, LamLPure repr) =>
       (forall s. HV (H repr s a,h) repr a
  -> J (State Label m) (HV (H repr s a,h) repr) b)
       -> J (State Label m) (HV h repr) (a->b)
lamL f = J (do
      l <- newLabel
      fmap (\body -> J $ \h -> lamSL l (\x -> unJ body (H x,h)))
                  (unJ (f (hrefL l))))

runCL :: (Functor m, Monad m) => J (State Label m) (HV () C) a -> m String
runCL m = fmap (runCS . runH) $ (evalState (unJ m) 0)

-- Specialized instances of runCL
runCLI :: J (State Label Identity) (HV () C) a -> String
runCLI = runIdentity . runCL
-}


-- ------------------------------------------------------------------------
-- We extend our DSL to generate imperative code

-- We add higher-order constants for bind and return
class SymBind repr where
    retS    :: Monad p => repr (a -> p a)
    bindS   :: Monad p => repr (p a -> (a -> p b) -> p b)
    apS     :: Applicative p => repr (p (a->b)) -> repr (p a) -> repr (p b)
    scolonS :: Monad p => repr (p () -> p a -> p a)

instance SymBind R where
    retS    = R return
    bindS   = R (>>=)
    scolonS = R (>>)
    apS (R x) (R y) = R (x <*> y)

instance SymBind C where
    retS    = C (const (VarE 'return))
    bindS   = C (const (VarE '(>>=)))
    scolonS = C (const (VarE '(>>)))
    apS (C x) (C y) = C (\vc ->
                         InfixE (Just (x vc)) (VarE '(<*>)) (Just (y vc)))

-- A bit of syntactic sugar
gretS :: (SSym repr, SymBind repr, Monad p) => repr a -> repr (p a)
gretS a = retS `appS` a

gret :: (SSym repr, SymBind repr, Monad p, Applicative m) =>
         m (repr a) -> m (repr (p a))
gret = fmap gretS

-- sequencing of two computations: `the semi-colon'
infixl 1 >>:
(>>:) :: (SSym repr, SymBind repr, Monad p, Applicative m) =>
   m (repr (p ())) -> m (repr (p a)) -> m (repr (p a))
x >>: y = pure scolonS $$ x $$ y

{-
-- pure-function application
infixl 2 $$$
($$$) :: (SSym repr, SymBind repr, Monad m) =>
   repr (m (a -> b)) -> repr (m a) -> repr (m b)
x $$$ y = app_ $$ x $$ y
-}

-- call-by-value (monadic) application
infixr 1 =<<:
(=<<:) :: (SSym repr, SymBind repr, Monad p, Applicative m) =>
    m (repr (a -> p b)) -> m (repr (p a)) -> m (repr (p b))
x =<<: y = pure TSCore.bindS $$ y $$ x

-- Matrices with 0-based indices
mat_new_ :: MArray IOUArray e IO =>
     Int -> Int -> e -> IO (IOUArray (Int,Int) e)
mat_new_ i j e = newArray ((0,i),(0,j)) e

mat_get_ :: MArray IOUArray e IO =>
     IOUArray (Int,Int) e -> Int -> Int -> IO e
mat_get_ a i j = readArray a (i,j)

mat_set_ :: MArray IOUArray e IO =>
     IOUArray (Int,Int) e -> Int -> Int -> e -> IO ()
mat_set_ a i j e = writeArray a (i,j) e


class SymMat repr where
    mat_newS :: MArray IOUArray e IO =>
          repr (Int -> Int -> e -> IO (IOUArray (Int,Int) e))
    mat_getS :: MArray IOUArray e IO =>
          repr (IOUArray (Int,Int) e -> Int -> Int -> IO e)

    mat_setS :: MArray IOUArray e IO =>
          repr (IOUArray (Int,Int) e -> Int -> Int -> e -> IO ())


instance SymMat R where
    mat_newS = R mat_new_
    mat_getS = R mat_get_
    mat_setS = R mat_set_

instance SymMat C where
    mat_newS = C (const (VarE 'mat_new_))
    mat_getS = C (const (VarE 'mat_get_))
    mat_setS = C (const (VarE 'mat_set_))

mat_new :: (Applicative m, MArray IOUArray e IO, SymMat repr, SSym repr) =>
     m (repr Int) -> m (repr Int) -> m (repr e) ->
           m (repr (IO (IOUArray (Int,Int) e)))
mat_new i j e = pure mat_newS $$ i $$ j $$ e

mat_get :: (Applicative m, MArray IOUArray e IO, SymMat repr, SSym repr) =>
     m (repr (IOUArray (Int,Int) e)) ->
           m (repr Int) -> m (repr Int) -> m (repr (IO e))
mat_get a i j = pure mat_getS $$ a $$ i $$ j

mat_set :: (Applicative m, MArray IOUArray e IO, SymMat repr, SSym repr) =>
     m (repr (IOUArray (Int,Int) e)) ->
           m (repr Int) -> m (repr Int) -> m (repr e) -> m (repr (IO ()))
mat_set a i j e = pure mat_setS $$ a $$ i $$ j $$ e


-- Vectors with 0-based indices
vec_new_ :: MArray IOUArray e IO =>
     Int -> e -> IO (IOUArray Int e)
vec_new_ i e = newArray (0,i) e

vec_get_ :: MArray IOUArray e IO =>
     IOUArray Int e -> Int -> IO e
vec_get_ a i = readArray a i

vec_set_ :: MArray IOUArray e IO =>
     IOUArray Int e -> Int -> e -> IO ()
vec_set_ a i e = writeArray a i e

vec_addto_ :: (Num e, MArray IOUArray e IO) =>
     IOUArray Int e -> Int -> e -> IO ()
vec_addto_ a i e = readArray a i >>= writeArray a i . (e +)

vec_clear_ :: (Num e, MArray IOUArray e IO) =>
        Int -> IOUArray Int e -> IO ()
vec_clear_ n a = forM_ [0..n-1] $ \i -> writeArray a i 0


class SymVec repr where
    vec_newS   :: MArray IOUArray e IO =>
            repr (Int -> e -> IO (IOUArray Int e))
    vec_getS   :: MArray IOUArray e IO =>
            repr (IOUArray Int e -> Int -> IO e)
    vec_setS   :: MArray IOUArray e IO =>
            repr (IOUArray Int e -> Int -> e -> IO ())
    vec_addtoS :: (Num e, MArray IOUArray e IO) =>
            repr (IOUArray Int e -> Int -> e -> IO ())
    vec_clearS :: (Num e, MArray IOUArray e IO) =>
            repr (Int -> IOUArray Int e -> IO ())


instance SymVec R where
    vec_newS   = R vec_new_
    vec_getS   = R vec_get_
    vec_setS   = R vec_set_
    vec_addtoS = R vec_addto_
    vec_clearS = R vec_clear_

instance SymVec C where
    vec_newS   = C (const (VarE 'vec_new_))
    vec_getS   = C (const (VarE 'vec_get_))
    vec_setS   = C (const (VarE 'vec_set_))
    vec_addtoS = C (const (VarE 'vec_addto_))
    vec_clearS = C (const (VarE 'vec_clear_))

vec_new :: (Applicative m, MArray IOUArray e IO, SSym repr, SymVec repr) =>
     m (repr Int) -> m (repr e) -> m (repr (IO (IOUArray Int e)))
vec_new n e = pure vec_newS $$ n $$ e

vec_get :: (Applicative m, MArray IOUArray e IO, SSym repr, SymVec repr) =>
     m (repr (IOUArray Int e)) -> m (repr Int) -> m (repr (IO e))
vec_get a i = pure vec_getS $$ a $$ i


vec_set :: (Applicative m, MArray IOUArray e IO, SSym repr, SymVec repr) =>
     m (repr (IOUArray Int e)) -> m (repr Int) -> m (repr e)
           -> m (repr (IO ()))
vec_set a i e = pure vec_setS $$ a $$ i $$ e

-- The value to add to is typically an IO action. That's why the argument
-- is treated specially.
vec_addto :: (Applicative m, Num e, MArray IOUArray e IO,
             SSym repr, SymVec repr) =>
      m (repr (IOUArray Int e)) -> m (repr Int)
            -> m (repr (e->IO ()))
vec_addto a i = pure vec_addtoS $$ a $$ i

vec_clear :: (Applicative m,MArray IOUArray e IO, Num e,
              SSym repr, SymVec repr) =>
       m (repr Int) -> m (repr (IOUArray Int e)) -> m (repr (IO ()))
vec_clear n a = pure vec_clearS $$ n $$ a



-- The loop combinator, a higher-order constant
--     sloop lb up step (\x -> body)

-- imperative loop with a step
loop_comb :: Int -> Int -> Int -> (Int -> IO ()) -> IO ()
loop_comb lb ub _ _ | lb > ub = return ()
loop_comb lb ub step body = body lb >> loop_comb (lb + step) ub step body


class SymLoop repr where
    loopS :: repr Int -> repr Int -> repr Int ->
             repr (Int -> IO ()) -> repr (IO ())


instance SymLoop R where
    loopS (R lb) (R ub) (R step) (R body) =
        R $ forM_ [lb,lb+step..ub] body

instance SymLoop C where
    loopS (C lb) (C ub) (C step) (C body) =
        C (\vc ->
           (VarE 'forM_) `AppE`
           ((VarE 'Prelude.enumFromThenTo) `AppE` (lb vc)
            `AppE`
            (InfixE (Just (lb vc)) (VarE '(Prelude.+)) (Just (step vc)))
            `AppE` (ub vc))
           `AppE` (body vc))

-- Syntactic sugar
loop :: (Applicative m, SSym repr, SymLoop repr) =>
    m (repr Int) -> m (repr Int) -> m (repr Int) -> m (repr (Int -> IO ())) ->
         m (repr (IO ()))
loop lb ub step body = loopS <$> lb <*> ub <*> step <*> body


-- The min function
class SymMin repr where
    minS :: repr (Int -> Int -> Int)

instance SymMin R where
    minS = R min

instance SymMin C where
    minS  = C (const . VarE $ 'min)

-- Syntactic sugar
min_ :: (Applicative m, SSym repr, SymMin repr) =>
    m (repr Int) -> m (repr Int) -> m (repr Int)
min_ x y = pure minS $$ x $$ y


-- ------------------------------------------------------------------------
-- Commutative Applicative, sort of

{- Nicolas Pouillard has commented:
'app_pull' is already known as 'Distributive.distribute' where
'Distributive' is the categorical dual of 'Traversable'.
 Hence 'distribute' is the inverse of 'sequenceA'.
-}

class Applicative j => AppLiftable j where
    app_pull :: Applicative i => i (j a) -> j (i a)

instance AppLiftable Identity where
    app_pull = Identity . fmap runIdentity

instance AppLiftable ((->) e) where
    app_pull ija = \e -> fmap ($ e) ija

-- Like regular Applicative, it is closed under composition

instance (AppLiftable j, AppLiftable k) =>
    AppLiftable (j :. k) where
    app_pull = J . fmap app_pull . app_pull . fmap unJ

-- ------------------------------------------------------------------------
-- Various pieces missing from the standard libraries
-- We define them here

-- There was no Applicative Identity in standard libraries
-- Now (GHC 7.8)there is
{-
newtype Identity a = Identity{runIdentity :: a}
instance Functor Identity where
    fmap f = Identity . f . runIdentity
instance Applicative Identity where
    pure = Identity
    f <*> x = Identity $ (runIdentity f) (runIdentity x)

instance Monad Identity where
    return  = Identity
    x >>= f = f (runIdentity x)
-}

-- Before 7.04, the standard library misses the following
-- Uncomment the following for older versions of GHC
{-
instance Applicative (Either String) where
    pure = Right
    Left e <*> _  = Left e
    _ <*> Left e  = Left e
    Right f <*> Right m = Right (f m)
-}

-- Error applicative (which is also a monad)
class Applicative m => ErrorA m where
    type ErrT m :: *
    throwA :: ErrT m -> m a
    catchA :: m a -> (ErrT m -> m a) -> m a

instance ErrorA (Either e) where
    type ErrT (Either e) = e
    throwA = Left
    catchA (Left e) f = f e
    catchA m _        = m

instance (ErrorA m, Applicative i) => ErrorA (m :. i) where
    type ErrT (m :. i) = ErrT m
    throwA = J . throwA
    catchA m f = J $ catchA (unJ m) (unJ . f)


-- The state Applicative and monad
newtype State l m a = State{unState :: l -> m (a,l)}

instance Monad m => Functor (State l m) where
    fmap f m = pure f <*> m

instance Monad m => Applicative (State l m) where
    pure    = return
    f <*> m = do
        fv <- f
        mv <- m
        return (fv mv)

instance Monad m => Monad (State l m) where
    return x = State $ \l -> return (x,l)
    m >>= f  = State $ \l -> do (mv,l1) <- unState m l
                                unState (f mv) l1

newLabel :: (Monad m, Num l) => State l m l
newLabel = State $ \l -> return (l, l+1)

evalState :: Monad m => State l m a -> l -> m a
evalState (State m) l = m l >>= return . fst

liftState :: Monad m => m a -> State l m a
liftState a = State $ \l -> a >>= \v -> return (v,l)

{- Old code
-- Hypothetical code values
-- A Haskell value of the type SSym repr => HV h repr a
-- represents an expression in the object language of the type a
-- in the (generator) environment h
-- Recall that (->) h is an applicative.

type HV h = J ((->) h)

-- HV values are thus themselves members of SSym, as we have
-- just seen

hmap :: (h2 -> h1) -> HV h1 repr a -> HV h2 repr a
hmap f e = J $ \h2 -> unJ e (f h2)

runH :: HV () repr a -> repr a
runH m = unJ m ()



-- The data constructor H and the elimination for href are
-- NOT exported!

-- A component of the environment h
newtype H r s a = H (r a)       -- just to attach s

href :: HV (H repr s a,h) repr a    -- hypothesis reference
href = J $ \ (H x,h) -> x



-- We can define the following, but it doesn't help us much...
-- We have do define lam anew
lamH :: (SSym repr, LamPure repr) =>
       (forall s. HV (H repr s a,h) repr a -> HV (H repr s a,h) repr b)
       ->  HV h repr (a->b)
lamH f = J $ \h -> lamS (\x -> (unJ (f href)) (H x,h))

weaken :: Applicative m => J m (HV h repr) a -> J m (HV (h',h) repr) a
weaken (J m) = J (fmap (hmap snd) m)

lam :: (Functor m, SSym repr, LamPure repr) =>
       (forall s. HV (H repr s a,h) repr a -> J m (HV (H repr s a,h) repr) b)
       -> J m (HV h repr) (a->b)
lam f = J (fmap (\body -> J $ \h -> lamS (\x -> unJ body (H x,h)))
                (unJ (f href)))

-}
