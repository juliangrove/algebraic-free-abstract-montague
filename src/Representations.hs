{-# LANGUAGE
    AllowAmbiguousTypes,
    DataKinds,
    FlexibleInstances,
    KindSignatures,
    MultiParamTypeClasses,
    TypeFamilies #-}

module Representations where

import GHC.TypeNats
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

class Constant a (i :: Nat) repr where
  c :: repr a

class Heyting repr where
  (/\), (\/), (-->) :: repr Bool -> repr Bool -> repr Bool
  true, false :: repr Bool

class HOL a repr where
  forall, exists :: (repr a -> repr Bool) -> repr Bool

class Equality a repr where
  equals :: repr a -> repr a -> repr Bool

class Context a repr where
  type Gamma a
  empty :: repr (Gamma a)
  upd :: repr a -> repr (Gamma a) -> repr (Gamma a)
  sel :: repr (Gamma a) -> repr a
  

-- ===============
-- == Instances ==
-- ===============

-- | Evaluation

newtype Eval a = Eval { unEval :: a } deriving Show

instance Lambda Eval where
  app m n = Eval $ unEval m (unEval n)
  lam f = Eval $ unEval . f . Eval
  unit = Eval ()
  pair m n = Eval (unEval m, unEval n)
  fst_ = Eval . fst . unEval
  snd_ = Eval . snd . unEval

instance Constant (Entity -> Bool) 0 Eval where
  c = Eval dog'

instance Constant (Entity -> Bool) 1 Eval where
  c = Eval cat'

instance Constant (Entity -> Bool) 2 Eval where
  c = Eval happy'

instance Constant (Entity -> Entity -> Bool) 0 Eval where
  c = Eval chase'

instance Constant (Entity -> Entity -> Bool) 1 Eval where
  c = Eval catch'

instance Heyting Eval where  
  phi /\ psi = Eval $ unEval phi && unEval psi
  phi \/ psi = Eval $ unEval phi || unEval psi
  phi --> psi = Eval $ not (unEval phi) || unEval psi
  true = Eval True
  false = Eval False

-- | Class of types for which some domain of quantification can be determined
class Domain a where
  domain :: [a]

instance Domain () where
  domain = [()]

instance Domain Entity where
  domain = entities

instance (Domain a, Domain b) => Domain (a, b) where
  domain = [ (e, p) | e <- domain, p <- domain ]

-- | Assuming there is such a domain...
instance Domain a => HOL a Eval where
  forall f = Eval $ all (unEval . f) (map Eval domain)
  exists f = Eval $ any (unEval . f) (map Eval domain)

instance Eq a => Equality a Eval where
  equals m n =  Eval $ unEval m == unEval n

instance Context Entity Eval where
  type Gamma Entity = [Entity]
  empty = Eval []
  upd x c = Eval $ unEval x : unEval c
  sel c = Eval $ unEval c !! 0


-- | Pretty printing

data Var = Var Char Int

instance Enum Var where
  succ (Var c i) = case c of
                     'x' -> Var 'y' i
                     'y' -> Var 'z' i
                     'z' -> Var 'u' i
                     'u' -> Var 'v' i
                     'v' -> Var 'w' i
                     'w' -> Var 'x' (succ i)
  toEnum i = case mod i 6 of
               0 -> Var 'x' (div i 6)
               1 -> Var 'y' (div i 6)
               2 -> Var 'z' (div i 6)
               3 -> Var 'u' (div i 6)
               4 -> Var 'v' (div i 6)
               5 -> Var 'w' (div i 6)
  fromEnum (Var c i) = case c of
                         'x' -> i*6
                         'y' -> i*6 + 1
                         'z' -> i*6 + 2
                         'u' -> i*6 + 3
                         'v' -> i*6 + 4
                         'w' -> i*6 + 5

instance Show Var where
  show (Var c i) = if i == 0 then [c] else 'c' : show i

newtype Print a = Print { getVar :: Var -> String }

instance Lambda Print where
  app m n = Print $ \i -> "(" ++ getVar m i ++ " " ++ getVar n i ++ ")"
  lam f = Print $ \i -> "(λ"
                        ++ show i
                        ++ "."
                        ++ getVar (f (Print $ const $ "" ++ show i)) (succ i)
                        ++ ")"
  unit = Print $ const "★"
  pair m n = Print $ \i -> "⟨" ++ getVar m i ++ ", " ++ getVar n i ++ "⟩"
  fst_ m = Print $ \i -> "(π1 " ++ getVar m i ++ ")"
  snd_ m = Print $ \i -> "(π2 " ++ getVar m i ++ ")"

instance Constant (Entity -> Bool) 0 Print where
  c = Print $ const "dog"

instance Constant (Entity -> Bool) 1 Print where
  c = Print $ const "cat"

instance Constant (Entity -> Bool) 2 Print where
  c = Print $ const "happy"

instance Constant (Entity -> Entity -> Bool) 0 Print where
  c = Print $ const "chase"

instance Constant (Entity -> Entity -> Bool) 1 Print where
  c = Print $ const "catch"

instance Heyting Print where
  phi /\ psi = Print $ \i -> "(" ++ getVar phi i ++ " ∧ " ++ getVar psi i ++ ")"
  phi \/ psi = Print $ \i -> "(" ++ getVar phi i ++ " ∨ " ++ getVar psi i ++ ")"
  phi --> psi = Print $ \i -> "(" ++ getVar phi i ++ " → " ++ getVar psi i ++ ")"
  true = Print $ const "⊤"
  false = Print $ const "⊥"

instance HOL a Print where
  forall f = Print $ \i -> "(∀"
                           ++ show i
                           ++ "."
                           ++ getVar (f (Print $ const $ "" ++ show i)) (succ i)
                           ++ ")"
  exists f = Print $ \i -> "(∃"
                           ++ show i
                           ++ "."
                           ++ getVar (f (Print $ const $ "" ++ show i)) (succ i)
                           ++ ")"
instance Equality a Print where  
  equals m n = Print $ \i -> "(" ++ getVar m i ++ " = " ++ getVar n i ++ ")"

instance Show (Print a) where
  show (Print a) = a (Var 'x' 0)

instance Context a Print where
  type Gamma a = [a]
  empty = Print $ const "ε"
  upd x c = Print $ \i -> getVar x i ++ "::" ++ getVar c i
  sel c = Print $ \i -> "(sel (" ++ getVar c i ++ "))"
