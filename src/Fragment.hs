{-# LANGUAGE
    AllowAmbiguousTypes,
    DataKinds,
    FlexibleContexts,
    ScopedTypeVariables,
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

every :: (Lambda repr,
          Heyting repr,
          HOL Entity repr)
      => FreeGM f (repr (Entity -> Bool))
      -> FreeGM
          (Determiner repr ~> Determiner repr
           ∘ Monoidal (f ∘ (Quantifier repr ~>  E repr ∘ Id)))
          (E repr)                
every pred = det every' >>= \q -> pred >>= \pred' -> scope (q (app pred'))

some :: Lambda repr
     => repr (Entity -> Bool) -> FreeGM (Pred Entity repr ~> E repr ∘ Id) (E repr)
some pred = choose (app pred)

bind :: Context a repr
     => FreeGM f (repr a)
     -> FreeGM
         (Monoidal (f ∘ (() ~> repr (Gamma a) ∘ (repr (Gamma a) ~> () ∘ Id))))
         (repr a)
bind m = m >>= \x -> get >>= \s -> put (upd x s) >> return x

it :: Context a repr => FreeGM (() ~> repr (Gamma a) ∘ Id) (repr a)
it = get >>= \s -> return (sel s)

who :: (Lambda repr,
        Heyting repr)
    => repr ((Entity -> Bool) -> (Entity -> Bool) -> Entity -> Bool)
who = lam (\p -> lam (\q -> lam (\x -> app p x /\ app q x)))

-- | One-place predicates

dog :: Constant (Entity -> Bool) 0 repr
    => repr (Entity -> Bool)
dog = c @(Entity -> Bool) @0

cat :: Constant (Entity -> Bool) 1 repr
    => repr (Entity -> Bool)
cat = c @(Entity -> Bool) @1

happy :: Constant (Entity -> Bool) 2 repr
    => repr (Entity -> Bool)
happy = c @(Entity -> Bool) @2

-- | Two-place predicates

chase :: Constant (Entity -> Entity -> Bool) 0 repr
      => repr (Entity -> Entity -> Bool)
chase = c @(Entity -> Entity -> Bool) @0

catch :: Constant (Entity -> Entity -> Bool) 1 repr
      => repr (Entity -> Entity -> Bool)
catch = c @(Entity -> Entity -> Bool) @1


-- =======================
-- == Example sentences ==
-- =======================

-- | 'Every dog is happy.'
sentence1 :: (Lambda repr,
              Heyting repr,
              HOL Entity repr,
              Constant (Entity -> Bool) 0 repr,
              Constant (Entity -> Bool) 2 repr)
          => FreeGM (Determiner repr ~> Determiner repr
                     ∘ (Quantifier repr ~> E repr ∘ Id))
              (T repr)
sentence1 = every (return dog) <| return happy

-- | 'Some cat is happy.'
sentence2 :: (Lambda repr,
              Heyting repr,
              HOL Entity repr,
              Constant (Entity -> Bool) 1 repr,
              Constant (Entity -> Bool) 2 repr)
          => FreeGM (Pred Entity repr ~> E repr ∘ Id) (T repr)
sentence2 = some cat <| return happy

-- | 'Every dog who chased a cat caught it.'
sentence3 :: (Lambda repr,
              Heyting repr,
              HOL Entity repr,
              Constant (Entity -> Bool) 0 repr,
              Constant (Entity -> Bool) 1 repr,
              Constant (Entity -> Entity -> Bool) 0 repr,
              Constant (Entity -> Entity -> Bool) 1 repr,
              Context Entity repr)
          => FreeGM
              (Determiner repr ~> Determiner repr
               ∘ (Pred Entity repr ~> E repr
                  ∘ (() ~> repr [Entity]
                     ∘ (repr [Entity] ~> ()
                        ∘ (Quantifier repr ~> E repr
                           ∘ (() ~> repr [Entity]
                              ∘ Id))))))
              (T repr)
sentence3 = every (return dog <| (return who |> (return chase |> bind (some cat)))) <| (return catch |> it)

-- | 'Some dog chased some cat.'
sentence4 :: (Lambda repr,
              Constant (Entity -> Bool) 0 repr,
              Constant (Entity -> Bool) 1 repr,
              Constant (Entity -> Entity -> Bool) 0 repr)
          => FreeGM (Pred Entity repr ~> E repr
                     ∘ (Pred Entity repr ~> E repr
                        ∘ Id))
              (T repr)
sentence4 = some dog <| (return chase |> some cat)

-- | 'Some dog chased some cat.'
sentence5 :: (Lambda repr,
              Constant (Entity -> Bool) 0 repr,
              Constant (Entity -> Bool) 1 repr,
              Constant (Entity -> Entity -> Bool) 1 repr)
          => FreeGM (Pred Entity repr ~> E repr
                     ∘ (Pred Entity repr ~> E repr
                        ∘ Id))
              (T repr)
sentence5 = some dog <| (return catch |> some cat)

-- | Evaluate a sentence into (a representation of) a Bool.
runSentence :: forall repr p a f.
               (Heyting repr,
                HOL p repr,
                Equality p repr,
                Context a repr,
                Handleable f p (repr (Gamma a)) repr)
            => FreeGM f (T repr) -> T repr
runSentence phi = eval (handle phi) (empty @a @repr)

-- | Examples from README

test1 = runSentence @Print @() @Entity $ every (return dog <| (return who |> (return chase |> bind (some cat)))) <| (return catch |> it)

test2 = runSentence @Eval @() @Entity $ every (return dog <| (return who |> (return chase |> bind (some cat)))) <| (return catch |> it)

test3 = runSentence @CoqTerm @() @Entity $ every (return dog <| (return who |> (return chase |> bind (some cat)))) <| (return catch |> it)

-- If you evaluate, e.g., test3 in your REPL, you should get:
-- >>> test3
-- (exists (x : unit), ((forall (y : Entity), ((exists (z : (prod Entity unit)), ((((chase (fst z)) y) /\ (dog y)) /\ ((cat (fst z)) /\ (tt = (snd z))))) -> (exists (z : (prod Entity unit)), (((((chase (fst z)) y) /\ (dog y)) /\ (exists (u : unit), (((catch (sel (upd (fst z) emp))) y) /\ (tt = u)))) /\ ((cat (fst z)) /\ (tt = (snd z))))))) /\ (tt = x)))

test4 = runSentence @CoqTerm @(Entity, (Entity, ())) @Entity $ some dog <| (return chase |> some cat)

-- >>> test4
-- (exists (x : (prod Entity (prod Entity unit))), (((chase (fst (snd x))) (fst x)) /\ ((dog (fst x)) /\ ((cat (fst (snd x))) /\ (tt = (snd (snd x)))))))
--

test5 = runSentence @CoqTerm @(Entity, (Entity, ())) @Entity $ some dog <| (return catch |> some cat)

-- >>> test5
-- (exists (x : (prod Entity (prod Entity unit))), (((catch (fst (snd x))) (fst x)) /\ ((dog (fst x)) /\ ((cat (fst (snd x))) /\ (tt = (snd (snd x)))))))
--
