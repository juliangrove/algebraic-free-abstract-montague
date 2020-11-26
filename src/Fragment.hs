{-# LANGUAGE
    DataKinds,
    FlexibleContexts,
    TypeApplications,
    TypeOperators #-}

module Fragment where

import Prelude hiding (Monad(..))
import Algebraic
import Model
import Representations

-- =====================================
-- == Monadic application combinators ==
-- =====================================

-- | Forward application
(|>) :: (Functor (FreeGM g),
         Functor (FreeGM f),
         Lambda repr)
     => FreeGM f (repr (v -> w))
     -> FreeGM g (repr v)
     -> FreeGM (Monoidal (f ∘ g)) (repr w)
m |> n = join $ fmap (\f -> fmap (\x -> app f x) n) m

-- | Backward application
(<|) :: (Functor (FreeGM g),
         Functor (FreeGM f),
         Lambda repr)
     => FreeGM f (repr v)
     -> FreeGM g (repr (v -> w))
     -> FreeGM (Monoidal (f ∘ g)) (repr w)
m <| n = join $ fmap (\x -> fmap (\f -> app f x) n) m


-- =============
-- == Lexicon ==
-- =============

every' :: (Heyting repr,
           HOL Entity repr)
       => Determiner repr
every' pred k = forall (\x -> pred x --> k x)

every :: (Heyting repr,
          HOL Entity repr)
      => Pred Entity repr -> FreeGM (Quantifier repr ~> E repr ∘ Id) (E repr)
every pred = scope (every' pred)

some :: Pred Entity repr -> FreeGM (Pred Entity repr ~> E repr ∘ Id) (E repr)
some = choose

dog :: Constant (Entity -> Bool) 0 repr
    => repr (Entity -> Bool)
dog = c @(Entity -> Bool) @0

cat :: Constant (Entity -> Bool) 1 repr
    => repr (Entity -> Bool)
cat = c @(Entity -> Bool) @1

happy :: Constant (Entity -> Bool) 2 repr
    => repr (Entity -> Bool)
happy = c @(Entity -> Bool) @2


-- =======================
-- == Example sentences ==
-- =======================

-- | 'Every dog is happy.'
sentence1 :: (Lambda repr,
              Heyting repr,
              HOL Entity repr,
              Constant (Entity -> Bool) 0 repr,
              Constant (Entity -> Bool) 2 repr)
          => FreeGM (Quantifier repr ~> E repr ∘ Id) (T repr)
sentence1 = every (app dog) <| return happy

-- | 'Some cat is happy.'
sentence2 :: (Lambda repr,
              Heyting repr,
              HOL Entity repr,
              Constant (Entity -> Bool) 1 repr,
              Constant (Entity -> Bool) 2 repr)
          => FreeGM (Pred Entity repr ~> E repr ∘ Id) (T repr)
sentence2 = some (app cat) <| return happy

-- | Evaluate a sentence into (a representation of) a Bool.
runSentence :: (Heyting repr,
                HOL p repr,
                Equality p repr,
                Handleable f p [Entity] repr)
            => FreeGM f (T repr) -> T repr
runSentence phi = eval (handle phi) ([] @Entity)
