{-# LANGUAGE RankNTypes, TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module TCCore where

import Control.Monad.Identity

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Ppr

{-
A new, simpler approach: there are no nominals, no sets or sequences
or tuples of classifiers. It is more abstract: we get just the partial
order on bound variables and no more than that. There is no longer
possible to tell if one variable is `immediately' before or after; or
how many variables are in-between. The notion of reshuffling of the
environment simply does not make sense. So, the approach is as far
away from de Bruijn indices as possible.  Like Fluett and Morrisett's
calculus, ours is just System F with constants. Subject reduction is
easy to see.

Code expressions are parameterized by the type of values
and by a classifier: repr c t
Each free variable corresponds to a unique classifier.
A closed code expression has the type forall c. repr c t.
Bound variables too have the time repr c t, which is no
longer polymorphic in the classifier. 
There is a partial order on free variables; a value
of the type GEC repr c1 c2 is the exidence that c1 >= c2
in that order. We can use this evidence to coerce
(repr c1 t) to (repr c2 t1). The binding forms generate this
eveidence and make it available within their body.

Constants and closed code in general have the type repr c t.
The application has the type 
    ($$) :: repr c (a->b) -> repr c a -> repr c b

There are no automatic coercions of classifiers. All is manual.
See cast.
-}

class Sym repr where
    int_ :: Int -> repr c Int
    add_ :: repr c (Int -> Int -> Int)
    mul_ :: repr c (Int -> Int -> Int)
    -- building applications. Classifiers must match up
    -- no implicit coercions (see cast below)
    app_ :: repr c (a->b) -> repr c a -> repr c b

-- We need effects. So, we lift everything to an Monad
-- (if Haskell had a good notation for composing type constructors,
-- we would've made m . repr the instance of Sym)

int :: (Sym repr, Monad m) => Int -> m (repr c Int)
int = return . int_
add, mul :: (Sym repr, Monad m) => m (repr c (Int -> Int -> Int))
add = return add_
mul = return mul_

($$) :: (Sym repr, Monad m) => 
  m (repr c (a->b)) -> m (repr c a) -> m (repr c b)
f $$ x = liftM2 app_ f x

-- The evidence for the classifier order
type GEC repr c d = forall t. repr c t -> repr d t
-- The GEC relation is order: it is obviously reflexive (id)and
-- and transitive (functional composition)

-- If we defined lam_ in Sym, we couldn't use it to express lam below
-- The variable is represented by effect-free, bare repr d a
class Lam repr where
    lam :: Functor m => (forall d. GEC repr c d -> repr d a -> m (repr d b)) -> 
     m (repr c (a->b))

-- Useful shortcuts

varM :: (Monad m) => repr d t -> m (repr d t)
varM = return 

cast_ :: repr c t -> GEC repr c d -> repr d t
cast_ m tr = tr m

cast :: (Monad m) => 
   m (repr c t) -> GEC repr c d -> m (repr d t)
cast m tr = liftM tr m

-- -- Unify the classifier bounds of two bound variables
-- univar :: Lam repr =>
--           (BV repr c d a, BV repr d e b) ->
--           (BV repr c e a, BV repr c e b)
-- univar (v1,v2) = (v1 `compd` v2, v2 `compu` v1)

-- run (forall c. repr c c t) -> t

t1 = add $$ int 1 $$ int 2
t1r = 3 == runRI t1
t1c = "(GHC.Num.+) 1 2" == runCI t1

t2 = lam (\_ x -> (add $$ int 1) $$ varM x)
t2r = 5 == runRI t2 4

t2c = "\\x -> (GHC.Num.+) 1 x" == runCI t2

t3 = lam (\_ x -> 
    lam (\gexy y -> add  $$ (varM x `cast` gexy) $$ varM y) $$
    varM x)
t3r = 6 == runRI t3 3
t3c = "\\x -> (\\y -> (GHC.Num.+) x y) x" == runCI t3

t4 = lam (\_ x -> lam (\gexy y -> lam (\geyz z ->
      add $$ (varM x `cast` (geyz . gexy)) $$ 
             (mul $$ (varM y `cast` geyz) $$ varM z))))

t4r = 23 == runRI t4 3 4 5
t4c = runCI t4 ==
      "\\x -> \\y -> \\z -> (GHC.Num.+) x ((GHC.Num.*) y z)"


-- check scope extrusion <fun x -> (run <x>)>
-- <fun x -> (run <fun y -> y>)> and then replacing y with x

-- tse1 = lam (\x -> let _ = runCI (var x) in var x)

tse20 = lam (\_ x -> let _ = runCI (lam (\_ y -> varM y)) in varM x)
-- tse21 = lam (\_ x -> let _ = runCI (lam (\_ y -> varM x)) in varM x)
-- tse22 = lam (\_ x -> let _ = runCI (lam (\gey y -> varM x `cast` gey)) in varM x)

-- tse23 = lam (\x -> let _ = (lam (\y -> x)) in x)

-- tse24 = lam (\x -> let _ = runCI (lam (\y -> x `castd` y)) in x)

-- over-approximation: running should be OK...
-- tse25 = lam (\x -> let _ = runCI (lam (\y -> y `castu` x)) in x)

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

ef z = lam (\gex x -> add $$ (z `cast` gex) $$ varM x)
-- ef  :: (Monad m, Functor m, Lam repr, Sym repr) =>
--      m (repr c Int) -> m (repr c (Int -> Int))

ef1 = ef (int 1)
ef1r = 5 == runRI ef1 4
ef1c = runCI ef1 ==
       "\\x -> (GHC.Num.+) 1 x"

ef2 = lam (\_ x -> lam (\gexy y -> ef (mul $$ (varM x `cast` gexy) $$ varM y)))

ef2c = runCI ef2 ==
       "\\x -> \\y -> \\z -> (GHC.Num.+) ((GHC.Num.*) x y) z"


-- All functions from code -> code have to have rank-2 type (because of the
-- parameter c marking the variables)
-- Therefore, we have to write signatures
-- Well, eta is the same as lam...
eta :: (Functor m, Lam repr, Sym repr) =>
  (forall d. GEC repr c d -> repr d a -> m (repr d b)) -> m (repr c (a->b))
eta f = lam (\ge x -> f ge x)

teta0 = eta (\_ z -> add $$ int 1 $$ varM z)
teta0c = runCI teta0 ==
         "\\x -> (GHC.Num.+) 1 x"

teta1 = lam (\_ y -> eta (\gez z -> add $$ (varM y `cast` gez) $$ varM z))

teta1c = runCI teta1 ==
         "\\x -> \\y -> (GHC.Num.+) x y"

-- Second-order eta
-- Unlike before, it looks unremarkable. No packing/unpacking is needed
eta2 :: (Functor m, Lam repr, Sym repr) =>
  (forall d. GEC repr c d -> repr d a -> repr d b -> m (repr d h)) -> 
      m (repr c (a->b->h))
eta2 f = lam (\gex x -> lam (\gexy y -> f (gexy . gex) (x `cast_` gexy) y))

teta22 = lam (\_ x -> lam (\gexy y -> eta2 (\geyz z1 z2 -> 
                  let xyz = (x `cast_` (geyz . gexy)) in
                  let xYz = (y `cast_` geyz) in
                  add $$
                    (mul $$ varM z1 $$ varM xyz) $$
                    (mul $$ varM z2 $$ varM xYz))))


teta22c = 
 "\\x -> \\y -> \\z -> \\u -> (GHC.Num.+) ((GHC.Num.*) z x) ((GHC.Num.*) u y)"

      == runCI teta22

-- Generating an arbitrary number of binders
multi :: (Monad m, Functor m, Lam repr, Sym repr) =>
         Int -> m (repr c Int) -> m (repr c Int)
multi 0 z = z
multi n z = lam(\gex x -> multi (n-1) (add $$ (z `cast` gex) $$ varM x)) $$ 
            (int n)

tmulti1 = runCI (multi 1 (int 1)) ==
          "(\\x -> (GHC.Num.+) 1 x) 1"
tmulti1r = 2 == runRI (multi 1 (int 1))

tmulti2 = runCI (multi 2 (int 1)) ==
          "(\\x -> (\\y -> (GHC.Num.+) ((GHC.Num.+) 1 x) y) 1) 2"
tmulti2r = runRI (multi 2 (int 1)) == 4

tmulti3 = runCI (multi 3 (int 1)) ==
          "(\\x -> (\\y -> (\\z -> (GHC.Num.+) ((GHC.Num.+) ((GHC.Num.+) 1 x) y) z) 1) 2) 3"

tmulti3r = 7 == runRI (multi 3 (int 1))


{-
newtype ContA m repr c w t =
    ContA{unCont :: forall d z. BV repr c d z -> 
    (forall g. BV repr d g t -> m (repr g w)) -> m (repr d w)}
-}


-- Continuation applicative, sort of
-- Parameters n and w are the answer-classifier and answer-type.
-- For `pure' computations, without let-insertion or other effects,
-- both are polymorphic. Parameters c and t are the current classifier
-- and the current type. 
newtype ContA m repr n w c t =
    ContA{unCont :: forall r. GEC repr n r -> 
    (forall g.  GEC repr r g -> repr (g,c) t -> m (repr g w)) -> 
          m (repr r w)}


-- Any two classifiers have the (formal) greatest lower bound (meet)
class Meet repr where
    meet1   :: GEC repr r (r,c)
    meet2   :: GEC repr c (r,c)
    meet_id :: GEC repr (c,c) c
    meet_map1 :: (repr c a -> repr d b) -> repr (c,g) a -> repr (d,g) b
    meet_map2 :: (repr c a -> repr d b) -> repr (g,c) a -> repr (g,d) b

runCA :: (Monad m, Sym repr, Lam repr, Meet repr) =>
   ContA m repr n w n w -> m (repr n w)
runCA m = unCont m id (\geng rgnt -> return . meet_id $ meet_map2 geng rgnt)


ret :: (Monad m, Sym repr, Lam repr, Meet repr) =>
       repr c t -> ContA m repr n w c t
ret x = ContA $ \nr k -> k id (meet2 x)

apc :: (Monad m, Sym repr, Lam repr, Meet repr) =>
       ContA m repr n w c (a->b) ->
       ContA m repr n w c a ->
       ContA m repr n w c b
apc mf mx = ContA $ \ge_nr k ->
  unCont mf ge_nr (\ge_rg1 f -> 
    unCont mx (ge_rg1 . ge_nr) (\ge_g1g2 x ->
       let fx = meet_map1 ge_g1g2 f in          -- fx :: repr (g2,c) (a->b)
        k (ge_g1g2 . ge_rg1) (fx `app_` x)
                            ))


-- reset is essentially ret . runCA
reset :: (Monad m, Sym repr, Lam repr, Meet repr) =>
   ContA m repr n w n w -> ContA m repr n' w' n w
reset m = ContA $ \n'r k -> 
   unCont m id (\geng rgnt -> return . meet_id $ meet_map2 geng rgnt) >>=
          k id . meet2

{-
apc :: (Monad m, Sym repr, Lam repr) =>
       ContA m repr c w (a->b) ->
       ContA m repr c w a ->
       ContA m repr c w b
apc mf mx = ContA $ \vcd k ->
  unCont mf vcd (\f -> 
    unCont mx (vcd `compd` f) (\x ->
      let fx = f `compd` x    -- both var d g1
          xf = x `compu` f
      in 
      k ((unvar (var fx `app_` var xf)) `compu` fx)
             ))
-}

genlet :: (Monad m, Functor m, Sym repr, Lam repr, Meet repr) =>
          m (repr n t) -> ContA m repr n w c t
genlet e = ContA $ \genr k -> 
             lam (\gert t -> k gert (meet1 t)) $$ (e `cast` genr)

-- tl1 = ContA $ \vcd k ->
--      unCont (genlet (int 2)) vcd (\v -> k . unvar =<< ((add $$ int 1) $$ varM v))

tl1 = (ret (add_ `app_` int_ 1)) `apc` genlet (int 2)
tl1r = runRI (runCA tl1) == 3
tl1c = runCI (runCA tl1) ==
       "(\\x -> (GHC.Num.+) 1 x) 2"

-- Let insertion under lam...
tl2 = lam (\_ x -> runCA $ (ret (add_ `app_` x)) `apc` genlet (int 2))
tl2r = runRI tl2 3 == 5
tl2c = runCI tl2 ==
       "\\x -> (\\y -> (GHC.Num.+) x y) 2"

fmp :: Meet repr =>
       (repr c a -> repr d b) -> 
       ContA m repr n w c a ->
       ContA m repr n w d b
fmp f m = ContA $ \genr k ->
   unCont m genr (\gerg vgca -> k gerg (meet_map2 f vgca))

-- Specialization for C and ContA. ContA is not exactly a Functor, so
-- the generic instance doesn't apply. For the paper, it doesn't matter
-- though, since we don't need to be generic there.

lamC :: (forall d. GEC C c d -> C d a -> ContA m C n w d b) -> 
     ContA m C n w c (a->b)
lamC body = fmp cnv (body ge v)
     where
     v     = C $ \ (c,cnt) vc -> VarE (mkname cnt)
     ge  r = C $ \ (c,_) -> unC r c
     cnv body = C $ \c vc -> LamE [VarP (mkname vc)] 
                               (unC body (c,vc) (succ vc))

-- let inside lambda
tl21 = lamC (\_ x -> reset $ (ret (add_ `app_` x)) `apc` genlet (int 2))

tl21c = runCI (runCA tl21) ==
       "\\x -> (\\y -> (GHC.Num.+) x y) 2"

-- let outside lambda
tl3 = lamC (\_ x -> (ret (add_ `app_` x)) `apc` genlet (int 2))

tl3c = runCI (runCA tl3) ==
       "(\\x -> \\y -> (GHC.Num.+) y x) 2"


-- ------------------------------------------------------------------------
-- The interpreters for our DSL

-- Can I have a model of this calculus (real model, that
-- doesn't use strings for everything)

-- The evaluator
newtype R c t = R{unR :: c -> t}

instance Sym R where
    int_ = R . const
    add_ = R $ const (+)
    mul_ = R $ const (*)
    app_ f x = R $ \c -> (unR f c) (unR x c)

instance Lam R where
    lam body = fmap cnv (body ge v)
     where
     v     = R $ \ (c,a) -> a
     ge  r = R $ \ (c,_) -> unR r c
     cnv r = R $ \c -> \a -> unR r (c,a)

runR :: (forall c. R c a) -> a
runR r = unR r ()

runRI :: (forall c. (Identity (R c a))) -> a
runRI r = runR (runIdentity r)

instance Meet R where
    meet1 mr = R $ \ (r,c) -> unR mr r
    meet2 mc = R $ \ (r,c) -> unR mc c
    meet_id mcc = R $ \c -> unR mcc (c,c)
    meet_map1 f cga = R $ \ (d,g) -> unR (f (R $ \c -> unR cga (c,g))) d
    meet_map2 f gca = R $ \ (g,d) -> unR (f (R $ \c -> unR gca (g,c))) d


-- The C interpreter, the compiler
-- We mostly use it to show the code

type VarCounter = Int   -- we will see the need for it shortly, lamS

      -- the pure code value, the analogue
      -- of <1> or <fun x -> x> in MetaOCaml
data C c a = C{unC :: c -> VarCounter -> Exp}

instance Sym C where
    int_ = C . const2 . LitE . IntegerL . fromIntegral
    add_ = C $ const2 $ VarE $ '(Prelude.+)
    mul_ = C $ const2 $ VarE $ '(Prelude.*)
    app_ f x = C $ \e vc -> AppE (unC f e vc) (unC x e vc)

const2 :: a -> b -> c -> a
const2 x _ _ = x


instance Lam C where
    lam body = fmap cnv (body ge v)
     where
     v     = C $ \ (c,cnt) vc -> VarE (mkname cnt)
     ge  r = C $ \ (c,_) -> unC r c
     cnv body = C $ \c vc -> LamE [VarP (mkname vc)] 
                               (unC body (c,vc) (succ vc))

mkname :: VarCounter -> Name
mkname cnt = mkName $ names !! cnt
 where names = ["x","y","z","u","v","w","s","t"] ++
         [ "x_" ++ show i | i <- [0..] ]

runC :: (forall c. C c a) -> String
runC m = pprint $ unC m () 0

runCI :: (forall c. (Identity (C c a))) -> String
runCI r = runC (runIdentity r)

instance Meet C where
    meet1 mr = C $ \ (r,c) -> unC mr r
    meet2 mc = C $ \ (r,c) -> unC mc c
    meet_id mcc = C $ \c -> unC mcc (c,c)
    meet_map1 f cga = C $ \ (d,g) -> unC (f (C $ \c -> unC cga (c,g))) d
    meet_map2 f gca = C $ \ (g,d) -> unC (f (C $ \c -> unC gca (g,c))) d


{-
data CE c where
    CAny :: Exp -> CE c
    CVar :: (VarCounter -> Exp) -> CE Int
    CLft :: CE r -> CE (r,c)
    CRgt :: CE c -> CE (r,c)

runC :: (forall c. C c a) -> String
runC (C (CAny e)) = pprint e
runC (C (CVar f)) = pprint $ f 0
-- Others are not possible

runCI :: (forall c. (Identity (C c a))) -> String
runCI r = runC (runIdentity r)

instance Meet C where
    meet1 = C . CLft . unC
    meet2 = C . CRgt . unC

    meet_id (C (CAny m)) = C (CAny m)
    meet_id (C (CLft m)) = C m
    meet_id (C (CRgt m)) = C m


    meet_map1 f (C (CAny m))   = C . CLft $ unC (f (C (CAny m)))
    meet_map1 f (C (CLft cga)) = C . CLft $ unC (f (C cga))
    meet_map1 f (C (CRgt cga)) = C . CRgt $ cga

    meet_map2 f (C (CAny m))   = C . CRgt $ unC (f (C (CAny m)))
    meet_map2 f (C (CLft cga)) = C . CLft $ cga
    meet_map2 f (C (CRgt cga)) = C . CRgt $ unC (f (C cga))

instance Sym C where
    int_ = C. CAny . LitE . IntegerL . fromIntegral
    add_ = C $ CAny $ VarE $ '(Prelude.+)
    mul_ = C $ CAny $ VarE $ '(Prelude.*)
--    app_ f x = C $ \vc -> AppE (unC f vc) (unC x vc)

instance Lam C where
    lam body = fmap cnv (body ge v)
     where
     v     = C . CRgt . CVar $ \vc -> VarE (mkname (pred vc))
     ge  r = C $ \vc -> unC r (pred vc)
     cnv body = C $ \vc -> LamE [VarP (mkname vc)] (unC body (succ vc))

{-
data C c t where
    CAny :: Exp -> C c t
    CVar :: (VarCounter -> Exp) -> C Int t
    CMet :: (r -> Exp) -> C r t

capply :: C r t -> r -> Exp
capply (CAny e) _ = e
capply (CVar f) x = f x
capply (CMet f) r = f r

instance Meet C where
    meet1 mr = CMet $ \ (r,c) -> capply mr r
    meet2 mc = CMet $ \ (r,c) -> capply mc c 

    meet_id (CAny m) = CAny m
    meet_id (CMet m) = CMet $ \c -> m (c,c)

    meet_map1 f (CAny m) = CMet $ \ (d,g) -> capply (f (CAny m)) d
    meet_map1 f (CMet cga) = 
        CMet $ \ (d,g) -> capply (f (CMet $ \c -> cga (c,g))) d

    meet_map2 f (CAny m) = CMet $ \ (g,d) -> capply (f (CAny m)) d
    meet_map2 f (CMet gca) = 
        CMet $ \ (g,d) -> capply (f (CMet $ \c -> gca (g,c))) d

instance Sym C where
    int_ = CAny . LitE . IntegerL . fromIntegral
    add_ = CAny $ VarE $ '(Prelude.+)
    mul_ = CAny $ VarE $ '(Prelude.*)
--    app_ f x = C $ \vc -> AppE (unC f vc) (unC x vc)


runC :: (forall c. C c a) -> String
runC (CAny e) = pprint e
runC (CVar f) = pprint $ f 0
runC (CMet f) = pprint $ f 0

runCI :: (forall c. (Identity (C c a))) -> String
runCI r = runC (runIdentity r)

instance Lam C where
    lam body = fmap cnv (body ge v)
     where
     v     = CMet $ \vc -> VarE (mkname (pred vc))
     ge  r = CMet $ \vc -> unC r (pred vc)
     cnv body = CVar $ \vc -> LamE [VarP (mkname vc)] (capply body (succ vc))

     v     = R $ \ (c,a) -> a
     ge  r = R $ \ (c,_) -> unR r c
     cnv r = R $ \c -> \a -> unR r (c,a)

-}
-}
