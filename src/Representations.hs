{-# LANGUAGE
    FlexibleInstances,
    MultiParamTypeClasses #-}

module Representations where

import Model

-- ==============
-- == Algebras ==
-- ==============

class Lambda repr where
  app :: repr (a -> b) -> repr a -> repr b
  lam :: (repr a -> repr b) -> repr (a -> b)
  unit :: repr ()
  pair :: repr a -> repr b -> repr (a, b)
  fst_ :: repr (a, b) -> repr a
  snd_ :: repr (a, b) -> repr b

class Heyting repr where
  (/\), (\/), (-->) :: repr Bool -> repr Bool -> repr Bool
  true, false :: repr Bool

class HOL repr where
  forall, exists :: (repr a -> repr Bool) -> repr Bool

class Equality a repr where
  equals :: repr a -> repr a -> repr Bool

-- ===============
-- == Instances ==
-- ===============

-- | Evaluation.
newtype Eval a = Eval { unEval :: a }

instance Lambda Eval where
  app m n = Eval $ unEval m (unEval n)
  lam f = Eval $ unEval . f . Eval
  unit = Eval ()
  pair m n = Eval (unEval m, unEval n)
  fst_ = Eval . fst . unEval
  snd_ = Eval . snd . unEval

instance Heyting Eval where  
  phi /\ psi = Eval $ unEval phi && unEval psi
  phi \/ psi = Eval $ unEval phi || unEval psi
  phi --> psi = Eval $ not (unEval phi) || unEval psi
  true = Eval True
  false = Eval False

-- instance HOL Eval where
--   forall f = Eval $ all (unEval . f) (map Eval entities)
--   exists f = Eval $ any (unEval . f) (map Eval entities)

instance Eq a => Equality a Eval where
  equals m n =  Eval $ unEval m == unEval n


-- | Pretty printing.
newtype Print a = Print { getInt :: Int -> String }

instance Lambda Print where
  app m n = Print $ \i -> "(" ++ getInt m i ++ " " ++ getInt n i ++ ")"
  lam f = Print $ \i -> "(λx"
                        ++ show i
                        ++ "."
                        ++ getInt (f (Print $ const $ "x" ++ show i)) (succ i)
                        ++ ")"
  unit = Print $ const "⋆"
  pair m n = Print $ \i -> "⟨" ++ getInt m i ++ ", " ++ getInt n i ++ "⟩"
  fst_ m = Print $ \i -> "π1 " ++ getInt m i
  snd_ m = Print $ \i -> "π2 " ++ getInt m i

instance Heyting Print where
  phi /\ psi = Print $ \i -> "(" ++ getInt phi i ++ " ∧ " ++ getInt psi i ++ ")"
  phi \/ psi = Print $ \i -> "(" ++ getInt phi i ++ " ∨ " ++ getInt psi i ++ ")"
  phi --> psi = Print $ \i -> "(" ++ getInt phi i ++ " → " ++ getInt psi i ++ ")"
  true = Print $ const "⊤"
  false = Print $ const "⊥"

instance HOL Print where
  forall f = Print $ \i -> "(∀x"
                           ++ show i
                           ++ "."
                           ++ getInt (f (Print $ const $ "x" ++ show i)) (succ i)
                           ++ ")"
  exists f = Print $ \i -> "(∃x"
                           ++ show i
                           ++ "."
                           ++ getInt (f (Print $ const $ "x" ++ show i)) (succ i)
                           ++ ")"
instance Equality a Print where  
  equals m n = Print $ \i -> "(" ++ getInt m i ++ " = " ++ getInt n i ++ ")"

instance Show (Print a) where
  show (Print a) = a 0