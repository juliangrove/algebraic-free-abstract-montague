{-# LANGUAGE
    AllowAmbiguousTypes,
    DeriveFunctor,
    FlexibleInstances,
    FunctionalDependencies,
    GADTs,
    RankNTypes,
    RebindableSyntax,
    TypeApplications,
    TypeFamilies,
    TypeOperators,
    ScopedTypeVariables,
    UndecidableInstances #-}

module Algebraic where

import Representations
import Model
import Prelude hiding (Monad(..))

-- ============================================
-- == Algebraics effects encoded as functors ==
-- ============================================

-- | Functor composition and identity
newtype (f ∘ g) v = Compose { getCompose :: f (g v) } deriving Functor
data Id v = Id v deriving Functor

-- | The free graded monad over Functor
data FreeGM f v where
  Pure :: v -> FreeGM Id v
  Join :: Functor f => f (FreeGM g v) -> FreeGM (f ∘ g) v

instance Functor (FreeGM Id) where
  fmap f (Pure v) = Pure $ f v

instance Functor (FreeGM g) => Functor (FreeGM (f ∘ g)) where  
  fmap f (Join m) = Join $ fmap (fmap f) m

-- | Functor is monoidal
type family Monoidal op where
  Monoidal ((f ∘ g) ∘ h) = f ∘ Monoidal (g ∘ h) -- associativity
  Monoidal (Id ∘ g) = g                         -- left id
  Monoidal (f ∘ Id) = f                         -- right id
  
-- | Monadic interface
return :: v -> FreeGM Id v
return = Pure

(>>=) :: FreeGM f v -> (v -> FreeGM g w) -> FreeGM (Monoidal (f ∘ g)) w
Pure v >>= k = k v
Join m >>= k = Join $ fmap (>>= k) m

(>>) :: FreeGM f v -> FreeGM g w -> FreeGM (Monoidal (f ∘ g)) w
m >> n = m >>= const n

join :: FreeGM f (FreeGM g v) -> FreeGM (Monoidal (f ∘ g)) v
join m = m >>= id

-- | Every parameter type and arity determines a functor
data (p ~> a) v = Op p (a -> v) deriving Functor

type E repr = repr Entity
type T repr = repr Bool
type Pred p repr = repr p -> T repr
type Quantifier repr = Pred Entity repr -> T repr
type Determiner repr = Pred Entity repr -> Quantifier repr

get :: FreeGM (() ~> s ∘ Id) s
get = Join (Op () (\s -> Pure s))

put :: s -> FreeGM (s ~> () ∘ Id) ()
put s = Join (Op s return)

choose :: Pred p repr -> FreeGM (Pred p repr ~> repr p ∘ Id) (repr p)
choose pred = Join (Op pred return)

scope :: Quantifier repr
      -> FreeGM (Quantifier repr ~> E repr ∘ Id) (E repr)
scope q = Join (Op q return)

det :: Determiner repr
    -> FreeGM (Determiner repr ~> Determiner repr ∘ Id) (Determiner repr)
det d = Join (Op d return)

-- | Class used to handle a computation
class Handleable f p s repr | f -> p where
  handle :: FreeGM f (T repr)
         -> FreeGM (() ~> s ∘ (Pred p repr ~> repr p ∘ (s ~> () ∘ Id))) (T repr)
  
instance (Lambda repr,
          Heyting repr)
      => Handleable Id () s repr where
  handle (Pure v) = do
    s <- get
    choose (const true)
    put s
    return v

instance Handleable f p s repr
      => Handleable (() ~> s ∘ f) p s repr where
  handle (Join (Op () f)) = do
    s <- get
    case handle (f s) of
      Join (Op () g) -> g s

instance Handleable f p s repr
      => Handleable (s ~> () ∘ f) p s repr where
  handle (Join (Op s f)) = do
    _s' <- get
    case handle (f ()) of
      Join (Op () g) -> g s

getPredParam :: FreeGM (() ~> s ∘ (Pred p repr ~> repr p ∘ f)) v
             -> s -> Pred p repr
getPredParam (Join (Op () g)) s = case g s of Join (Op pred h) -> pred

instance (Cartesian repr,
          Heyting repr,
          Handleable f p s repr)
      => Handleable (Pred e repr ~> repr e ∘ f) (e, p) s repr where
  handle (Join (Op pred f)) = do
    s <- get
    ep <- choose (\ep' -> pred (fst_ ep')
                          /\ getPredParam (handle (f (fst_ ep'))) s (snd_ ep'))
    let e = fst_ ep
        p = snd_ ep
    case handle (f e) of
      Join (Op () g) -> case g s of
        Join (Op _p' h) -> h p

-- any_ :: (Foldable t,
--          Functor t,
--          Heyting repr)
--      => (repr a -> T repr) -> t (repr a) -> T repr
-- any_ p t = foldr (/\) true $ fmap p t

-- elem_ :: (Foldable t,
--           Functor t,
--           Heyting repr,
--           Equality a repr)
--       => repr a -> t (repr a) -> T repr
-- x `elem_` l = any_ (equals x) l

class QuantifyTuple t repr where  
  quantify :: (forall a. (HOL a repr, KnownType a)
                      => (repr a -> repr Bool) -> repr Bool)
           -> Pred t repr
           -> repr Bool

instance Cartesian repr => QuantifyTuple () repr where
  quantify _ f = f unit

instance (Cartesian repr,
          HOL a repr,
          KnownType a,
          QuantifyTuple t repr)
      => QuantifyTuple (a, t) repr where
  quantify q f = q $ \x -> quantify q $ \t -> f (pair x t)

class ExistsTuple p repr where
  existsTuple :: Pred p repr -> T repr

instance Cartesian repr => ExistsTuple () repr where
  existsTuple f = f unit

instance (Cartesian repr,
          HOL a repr,
          KnownType a,
          ExistsTuple t repr)
      => ExistsTuple (a, t) repr where
  existsTuple f = exists $ \x -> existsTuple $ \t -> f (pair x t)

-- | Evalutate a computation to (a representation of) a Bool, using your
-- favorite quantifier
eval_with :: forall repr a p s.
             (Cartesian repr,
              Heyting repr,
              QuantifyTuple p repr)
          => (forall a. (HOL a repr, KnownType a)
                     => (repr a -> repr Bool) -> repr Bool)
          -> FreeGM
              (() ~> s ∘ (Pred p repr ~> (repr p) ∘ (s ~> () ∘ Id)))
              (T repr)
          -> s -> T repr
eval_with q (Join (Op () f)) s
  = case f s of
      Join (Op pred g) -> quantify q -- quantify @p q
                           (\p -> case g p of
                                    Join (Op _s' h)
                                      -> case h () of
                                           Pure a -> pred p /\ a)

instance (Cartesian repr,
          Heyting repr,
          Handleable f p s repr,
          QuantifyTuple p repr)
      => Handleable (Quantifier repr ~> (E repr) ∘ f) () s repr where
  handle (Join (Op q f)) = do
    s <- get
    choose (const true)
    put s
    return (q (\x -> eval_with exists (handle @f @p (f x)) s))

instance (Cartesian repr,
          Heyting repr,
          Handleable f p s repr,
          QuantifyTuple p repr)
      => Handleable (Determiner repr ~> Determiner repr ∘ f) () s repr where
  handle (Join (Op d f)) = do
    s <- get
    choose (const true)
    put s
    return (d (\x -> eval_with exists
                      (handle @f @p (f (\p q -> p x))) s) -- convervativity
              (\x -> eval_with exists
                      (handle @f @p (f (\p q -> p x /\ q x))) s))
