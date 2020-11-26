{-# LANGUAGE
    FlexibleContexts,
    TypeOperators #-}

module Fragment where

import Prelude hiding (Monad(..))
import Algebraic
import Model
import Representations

(|>) :: (Functor (FreeGM g),
         Functor (FreeGM f),
         Lambda repr)
     => FreeGM f (repr (v -> w))
     -> FreeGM g (repr v)
     -> FreeGM (Monoidal (f ∘ g)) (repr w)
m |> n = join $ fmap (\f -> fmap (\x -> app f x) n) m

(<|) :: (Functor (FreeGM g),
         Functor (FreeGM f),
         Lambda repr)
     => FreeGM f (repr v)
     -> FreeGM g (repr (v -> w))
     -> FreeGM (Monoidal (f ∘ g)) (repr w)
m <| n = join $ fmap (\x -> fmap (\f -> app f x) n) m


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

dog :: Constant (Entity -> Bool) repr
    => repr (Entity -> Bool)
dog = c 0

cat :: Constant (Entity -> Bool) repr
    => repr (Entity -> Bool)
cat = c 1

happy :: Constant (Entity -> Bool) repr
    => repr (Entity -> Bool)
happy = c 3

sentence1 :: (Lambda repr,
              Heyting repr,
              HOL Entity repr,
              Constant (Entity -> Bool) repr)
          => FreeGM (Quantifier repr ~> E repr ∘ Id) (T repr)
sentence1 = every (app dog) <| return happy

sentence2 :: (Lambda repr,
              Heyting repr,
              HOL Entity repr,
              Constant (Entity -> Bool) repr)
          => FreeGM (Pred Entity repr ~> E repr ∘ Id) (T repr)
sentence2 = some (app cat) <| return happy

test :: (Lambda repr,
         Heyting repr,
         HOL Entity repr,
         Constant (Entity -> Bool) repr,
         Handleable (Quantifier repr ~> E repr ∘ Id) p s repr)
     => FreeGM ((() ~> s) ∘ ((Pred p repr ~> repr p) ∘ ((s ~> ()) ∘ Id))) (T repr)
test = handle sentence1
