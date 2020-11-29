{-# LANGUAGE
    AllowAmbiguousTypes,
    DataKinds,
    FlexibleContexts,
    FlexibleInstances,
    GADTs,
    KindSignatures,
    MultiParamTypeClasses,
    ScopedTypeVariables,
    TypeApplications,
    TypeFamilies,
    UndecidableInstances #-}

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
  domain = [ (a, b) | a <- domain, b <- domain ]

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

instance Context a Print where
  type Gamma a = [a]
  empty = Print $ const "ε"
  upd x c = Print $ \i -> getVar x i ++ "::" ++ getVar c i
  sel c = Print $ \i -> "(sel (" ++ getVar c i ++ "))"

instance Show (Print a) where
  show (Print a) = a (Var 'x' 0)


-- | Coq HOAS

data CoqType a where
  Entity :: CoqType Entity
  Prop :: CoqType Bool
  Arrow :: CoqType a -> CoqType b -> CoqType (a -> b)
  Unit :: CoqType ()
  Prod :: CoqType a -> CoqType b -> CoqType (a, b)

data CoqTerm a where
  Var_ :: String -> CoqTerm a
  Con :: String -> CoqTerm a
  App :: CoqTerm (a -> b) -> CoqTerm a -> CoqTerm b
  Lam :: (CoqTerm a -> CoqTerm b) -> CoqTerm (a -> b)
  TT :: CoqTerm ()
  Pair :: CoqTerm a -> CoqTerm b -> CoqTerm (a, b)
  Fst :: CoqTerm (a, b) -> CoqTerm a
  Snd :: CoqTerm (a, b) -> CoqTerm b
  And, Or, Impl :: CoqTerm Bool -> CoqTerm Bool -> CoqTerm Bool
  True_, False_ :: CoqTerm Bool
  Forall, Exists :: CoqType a
                 -> (CoqTerm a -> CoqTerm Bool)
                 -> CoqTerm Bool
  Equals :: CoqTerm b -> CoqTerm b -> CoqTerm Bool
  Empty :: Context a CoqTerm => CoqTerm (Gamma a)
  Upd :: Context a CoqTerm
      => CoqTerm a -> CoqTerm (Gamma a) -> CoqTerm (Gamma a)
  Sel :: Context a CoqTerm => CoqTerm (Gamma a) -> CoqTerm a
  Type :: CoqType a -> CoqTerm Bool

helpShow :: CoqTerm a -> Var -> String
helpShow (Var_ s) i = s
helpShow (Con s) i = s
helpShow (App m n) i = "(" ++ helpShow m i ++ " " ++ helpShow n i ++ ")"
helpShow (Lam f) i = error "Unknown type!"
helpShow TT i = "tt"
helpShow (Pair m n) i = "(pair " ++ helpShow m i ++ " " ++ helpShow n i ++ ")"
helpShow (Fst m) i = "(fst " ++ helpShow m i ++ ")"
helpShow (Snd m) i = "(snd " ++ helpShow m i ++ ")"
helpShow (And phi psi) i = "(" ++ helpShow phi i
                           ++ " /\\ " ++ helpShow psi i ++ ")"
helpShow (Or phi psi) i = "(" ++ helpShow phi i
                          ++ " \\/ " ++ helpShow psi i ++ ")"
helpShow (Impl phi psi) i = "(" ++ helpShow phi i
                            ++ " -> " ++ helpShow psi i ++ ")"
helpShow True_ i = "true"
helpShow False_ i = "false"
helpShow (Forall t f) i = "(forall (" ++ show i ++ " : " ++ helpShow (Type t) i
                          ++ "), " ++ helpShow (f (Var_ (show i))) (succ i) ++ ")"
helpShow (Exists t f) i = "(exists (" ++ show i ++ " : " ++ helpShow (Type t) i
                          ++ "), " ++ helpShow (f (Var_ (show i))) i ++ ")"
helpShow (Equals m n) i = "(" ++ helpShow m i ++ " = " ++ helpShow n i ++ ")"
helpShow Empty i = "emp"
helpShow (Upd m c) i = "(upd " ++ helpShow m i ++ " " ++ helpShow c i ++ ")"
helpShow (Sel c) i = "(sel " ++ helpShow c i ++ ")"
helpShow (Type Entity) i = "Entity"
helpShow (Type Prop) i = "Prop"
helpShow (Type (Arrow t1 t2)) i = "(" ++ helpShow (Type t1) i ++ " -> "
                                  ++ helpShow (Type t2) i ++ ")"
helpShow (Type Unit) i = "unit"
helpShow (Type (Prod t1 t2)) i = "(prod " ++ helpShow (Type t1) i ++ " "
                                  ++ helpShow (Type t2) i ++ ")"

instance Show (CoqTerm a) where
  show m = helpShow m (Var 'x' 0)

instance Lambda CoqTerm where
  app m n = case m of
              Lam f -> f n
              _ -> App m n
  lam = Lam
  unit = TT
  pair = Pair
  fst_ m = case m of
             Pair n o -> n
             _ -> Fst m
  snd_ m = case m of
             Pair n o -> o
             _ -> Snd m

instance Constant (Entity -> Bool) 0 CoqTerm where
  c = Con "dog"

instance Constant (Entity -> Bool) 1 CoqTerm where
  c = Con "cat"

instance Constant (Entity -> Bool) 2 CoqTerm where
  c = Con "happy"

instance Constant (Entity -> Entity -> Bool) 0 CoqTerm where
  c = Con "chase"

instance Constant (Entity -> Entity -> Bool) 1 CoqTerm where
  c = Con "catch"

instance Heyting (CoqTerm) where
  (/\) = And
  (\/) = Or
  (-->) = Impl
  true = True_
  false = False_

class KnownCoqType a where
  knownCoqType :: CoqType a

instance KnownCoqType Entity where
  knownCoqType = Entity

instance KnownCoqType Bool where
  knownCoqType = Prop

instance (KnownCoqType a, KnownCoqType b) => KnownCoqType (a -> b) where
  knownCoqType = Arrow knownCoqType knownCoqType

instance KnownCoqType () where
  knownCoqType = Unit

instance (KnownCoqType a, KnownCoqType b) => KnownCoqType (a, b) where
  knownCoqType = Prod knownCoqType knownCoqType

instance KnownCoqType a => HOL a CoqTerm where
  forall = Forall knownCoqType
  exists = Exists knownCoqType

instance Equality a (CoqTerm) where
  equals = Equals

instance Context a (CoqTerm) where
  type Gamma a = [a]
  empty = Empty
  upd = Upd
  sel = Sel
