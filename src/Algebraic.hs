{-# LANGUAGE
    AllowAmbiguousTypes,
    DeriveFunctor,
    FlexibleInstances,
    GADTs,
    MultiParamTypeClasses,
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

-- | The free graded monad Functor
data FreeGM f v where
  Pure :: v -> FreeGM Id v
  Join :: Functor f => f (FreeGM g v) -> FreeGM (f ∘ g) v

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

-- | Every parameter type and arity determines a functor
data (p ~> a) v = Op p (a -> v) deriving Functor

type Quantifier repr = (repr Entity -> repr Bool) -> repr Bool
type Determiner repr = (repr Entity -> repr Bool) -> Quantifier repr

get :: FreeGM (() ~> s ∘ Id) s
get = Join (Op () (\s -> Pure s))

put :: s -> FreeGM (s ~> () ∘ Id) ()
put s = Join (Op s (\() -> Pure ()))

choose :: [repr p] -> FreeGM ([repr p] ~> repr p ∘ Id) (repr p)
choose l = Join (Op l (\p -> Pure p))

scope :: Quantifier repr
      -> FreeGM (Quantifier repr ~> repr Entity ∘ Id) (repr Entity)
scope q = Join (Op q (\x -> Pure x))

det :: Determiner repr
    -> FreeGM (Determiner repr ~> Determiner repr ∘ Id) (Determiner repr)
det d = Join (Op d (\d' -> Pure d'))

-- | Class used to handle a computation with 'Choose' among the effects.
class Handleable f p s repr where
  handle :: FreeGM f (repr Bool)
         -> FreeGM (() ~> s ∘ ([repr p] ~> repr p ∘ (s ~> () ∘ Id))) (repr Bool)
  
instance Lambda repr => Handleable Id () s repr where
  handle (Pure v) = do
    s <- get
    choose [unit]
    put s
    return v

instance Handleable f p s repr => Handleable (() ~> s ∘ f) p s repr where
  handle (Join (Op () f)) = do
    s <- get
    case handle (f s) of
      Join (Op () g) -> g s

instance Handleable f p s repr => Handleable (s ~> () ∘ f) p s repr where
  handle (Join (Op s f)) = do
    _s' <- get
    case handle (f ()) of
      Join (Op () g) -> g s

getListParam :: FreeGM (() ~> s ∘ ([p] ~> p ∘ f)) v -> s -> [p]
getListParam (Join (Op () g)) s = case g s of Join (Op l h) -> l

instance (Lambda repr, Handleable f p s repr)
      => Handleable ([repr e] ~> (repr e) ∘ f) (e, p) s repr where
  handle (Join (Op l f)) = do
    s <- get
    ep <- choose [ pair e' p'
                 | e' <- l,
                   p' <- getListParam (handle (f e')) s ]
    let e = fst_ ep
        p = snd_ ep
    case handle (f e) of
      Join (Op () g) -> case g s of
        Join (Op _p' h) -> h p

any_ :: (Heyting repr, HOL repr)
     => (repr a -> repr Bool) -> (repr a -> repr Bool) -> repr Bool
any_ restriction p = exists (\x -> restriction x /\ p x)

elementOf :: (Foldable t, Functor t, Heyting repr, Equality a repr)
          => repr a -> t (repr a) -> repr Bool
x `elementOf` l = foldr (/\) true $ fmap (equals x) l

eval :: (Heyting repr, HOL repr, Equality p repr)
     => FreeGM (() ~> s ∘ ([repr p] ~> (repr p) ∘ (s ~> () ∘ Id))) (repr Bool)
     -> s -> repr Bool
eval (Join (Op () f)) s
  = case f s of
     Join (Op l g)
        -> any_ (`elementOf` l) (\p -> case g p of
                        Join (Op _s' h) -> case h () of
                                             Pure a -> a)
           
instance (Lambda repr,
          Heyting repr,
          HOL repr,
          Equality p repr,
          Handleable f p s repr)
      => Handleable (Quantifier repr ~> (repr Entity) ∘ f) () s repr where
  handle (Join (Op q f)) = do
    s <- get
    choose [unit]
    put s
    return (q (\x -> eval (handle @f @p (f x)) s))

instance (Lambda repr,
          Heyting repr,
          HOL repr,
          Equality p repr,
          Handleable f p s repr)
      => Handleable (Determiner repr ~> Determiner repr ∘ f) () s repr where
  handle (Join (Op d f)) = do
    s <- get
    choose [unit]
    put s
    return (d (\x -> eval (handle @f @p (f (\p q -> p x))) s) -- convervativity
              (\x -> eval (handle @f @p (f (\p q -> p x /\ q x))) s))
