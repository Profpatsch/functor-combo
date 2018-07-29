{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, TypeOperators, FlexibleContexts, TypeFamilies, DefaultSignatures #-}
{-# language UndecidableInstances #-}
-- TODO ^^
module FunctorCombo.Generic (
) where

import Data.Void (Void, vacuous)
import Data.Functor (($>), void)
import Data.Bifunctor (first, second)
import GHC.Generics
import qualified FunctorCombo.Functor as F

class Functor f => Holey f where
  -- | Derivative, i.e., one-hole context
  type Der f :: * -> *
  type Der f = Der (Rep1 f)
  -- | Fill a hole
  -- from1 :: f a -> Rep1 f a
  -- to1 :: Rep1 f a -> f a
  fillC   :: Der f a -> a -> f a
  -- default fillC :: (Generic1 f, Holey (Rep1 f)) => Der f a -> a -> f a
  -- fillC dfa a = to1 $ fillC _ a

  -- | All extractions
  -- type f r = NExprF r
  -- 
  extract :: f a -> f (Loc f a)
  default extract :: ( Generic1 f
                     , Holey (Rep1 f)
                     , Der f ~ Der (Rep1 f))
                  => f a -> f (Der f a, a)
  extract = to1 . extract . from1

type Loc f a = (Der f a, a)

instance Holey U1 where
  type Der U1 = V1
  fillC = undefined
  extract U1 = U1

instance Holey (Rec0 c) where
  type Der (Rec0 c) = V1
  fillC = undefined
  extract (K1 c) = K1 c

instance Holey Par1 where
  type Der Par1 = U1
  fillC U1 = Par1
  extract (Par1 r) = Par1 (U1, r)

instance Functor f => Holey (Rec1 f) where
  -- saves the functor’s structure as const value
  type Der (Rec1 f) = F.Const (f ())
  -- fill the functor structure with elements again
  fillC (F.Const fv) a = Rec1 $ fv $> a
  extract (Rec1 fa) = Rec1 $ fmap (\a -> (F.Const $ fa $> (), a)) fa

instance (Holey f, Holey g) => Holey (f :+: g) where
  type Der (f :+: g) = Der f :+: Der g
  fillC (L1 df) = L1 . fillC df
  fillC (R1 dg) = R1 . fillC dg
  extract (L1 fa) = L1 ((fmap.first) L1 (extract fa))
  extract (R1 ga) = R1 ((fmap.first) R1 (extract ga))


instance (Holey f, Holey g) => Holey (f :*: g) where
  type Der (f :*: g) = Der f :*: g  :+:  f :*: Der g
  fillC (L1 (dfa :*:  ga)) = (:*: ga) . fillC dfa
  fillC (R1 ( fa :*: dga)) = (fa :*:) . fillC dga
  extract (fa :*: ga) = (fmap.first) (L1 . (:*: ga)) (extract fa) :*:
                        (fmap.first) (R1 . (fa :*:)) (extract ga)

tweak2 :: Functor f
       =>   (dg (f a)             , f (df a, a))
       -> f (((dg :.: f) :*: df) a, a)
tweak2 (dgfa, fl) = (fmap.first) (Comp1 dgfa :*:) fl

extractGF :: (Holey f, Holey g) =>
             f (g a) -> f (g (Loc (f :.: g) a))
extractGF = fmap (tweak2 . second extract) . extract

instance (Holey f, Holey g) => Holey (f :.: g) where
  type Der (f :.: g) = Der f :.: g  :*:  Der g
  fillC (Comp1 dffa :*: dga) = Comp1 . fillC dffa . fillC dga
  extract (Comp1 gfa) = Comp1 (extractGF gfa)

instance Holey f => Holey (M1 i c f) where
  type Der (M1 i c f) = Der f
  fillC df = fillC df
  extract (M1 fa) = M1 $ extract fa
