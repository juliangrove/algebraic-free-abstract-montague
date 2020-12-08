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


-- | Discourse update
(>@) :: (Functor (FreeGM f),
         Functor (FreeGM g),
         Lambda repr,
         Heyting repr)
     => FreeGM f (T repr)
     -> FreeGM g (T repr)
     -> FreeGM (Monoidal (f ∘ g)) (T repr)
phi >@ psi = join $ fmap (\p -> fmap (\q -> p /\ q) psi) phi


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
      -> FreeGM (Det repr ∘ Monoidal (f ∘ (Scope repr ∘ Id))) (E repr)               
every pred = det every' >>= \q -> pred >>= \pred' -> scope (q (app pred'))

some :: Lambda repr
     => repr (Entity -> Bool) -> FreeGM (Choose repr Entity ∘ Id) (E repr)
some pred = choose (app pred)

bind :: Context a repr
     => FreeGM f (repr a)
     -> FreeGM
         (Monoidal (f ∘ (Get (repr (Gamma a)) ∘ (Put (repr (Gamma a)) ∘ Id))))
         (repr a)
bind m = m >>= \x -> get >>= \s -> put (upd x s) >> return x

it :: Context a repr => FreeGM (Get (repr (Gamma a)) ∘ Id) (repr a)
it = get >>= \s -> return (sel s)

who :: (Lambda repr,
        Heyting repr)
    => repr ((Entity -> Bool) -> (Entity -> Bool) -> Entity -> Bool)
who = lam (\p -> lam (\q -> lam (\x -> app p x /\ app q x)))

-- | One-place predicates

dog :: Constant (Entity -> Bool) "dog" repr
    => repr (Entity -> Bool)
dog = c @(Entity -> Bool) @"dog"

cat :: Constant (Entity -> Bool) "cat" repr
    => repr (Entity -> Bool)
cat = c @(Entity -> Bool) @"cat"

happy :: Constant (Entity -> Bool) "happy" repr
    => repr (Entity -> Bool)
happy = c @(Entity -> Bool) @"happy"

-- | Two-place predicates

chase :: Constant (Entity -> Entity -> Bool) "chase" repr
      => repr (Entity -> Entity -> Bool)
chase = c @(Entity -> Entity -> Bool) @"chase"

catch :: Constant (Entity -> Entity -> Bool) "catch" repr
      => repr (Entity -> Entity -> Bool)
catch = c @(Entity -> Entity -> Bool) @"catch"


-- =======================
-- == Example sentences ==
-- =======================

-- | 'Every dog is happy.'
sentence1 :: (Lambda repr,
              Heyting repr,
              HOL Entity repr,
              Constant (Entity -> Bool) "dog" repr,
              Constant (Entity -> Bool) "happy" repr)
          => FreeGM (Det repr ∘ (Scope repr ∘ Id)) (T repr)
sentence1 = every (return dog) <| return happy

-- | 'Some cat is happy.'
sentence2 :: (Lambda repr,
              Heyting repr,
              HOL Entity repr,
              Constant (Entity -> Bool) "cat" repr,
              Constant (Entity -> Bool) "happy" repr)
          => FreeGM (Choose repr Entity ∘ Id) (T repr)
sentence2 = some cat <| return happy

-- | 'Every dog who chased a cat caught it.'
sentence3 :: (Lambda repr,
              Heyting repr,
              HOL Entity repr,
              Constant (Entity -> Bool) "dog" repr,
              Constant (Entity -> Bool) "cat" repr,
              Constant (Entity -> Entity -> Bool) "chase" repr,
              Constant (Entity -> Entity -> Bool) "catch" repr,
              Context Entity repr)
          => FreeGM
              (Det repr
               ∘ (Choose repr Entity
                  ∘ (Get (repr [Entity])
                     ∘ (Put (repr [Entity])
                        ∘ (Scope repr
                           ∘ (Get (repr [Entity])
                              ∘ Id))))))
              (T repr)
sentence3 = every (return dog <| (return who |> (return chase |> bind (some cat)))) <| (return catch |> it)

-- | 'Some dog chased some cat.'
sentence4 :: (Lambda repr,
              Constant (Entity -> Bool) "dog" repr,
              Constant (Entity -> Bool) "cat" repr,
              Constant (Entity -> Entity -> Bool) "chase" repr)
          => FreeGM (Choose repr Entity ∘ (Choose repr Entity ∘ Id)) (T repr)
sentence4 = some dog <| (return chase |> some cat)

-- | 'Some dog caught some cat.'
sentence5 :: (Lambda repr,
              Constant (Entity -> Bool) "dog" repr,
              Constant (Entity -> Bool) "cat" repr,
              Constant (Entity -> Entity -> Bool) "catch" repr)
          => FreeGM (Choose repr Entity ∘ (Choose repr Entity ∘ Id)) (T repr)
sentence5 = some dog <| (return catch |> some cat)

-- | Evaluate a sentence into (a representation of) a Bool.
runSentence :: forall repr a b p f.
               (Cartesian repr,
                Heyting repr,
                QuantifyTuple p repr,
                Context b repr,
                Handleable f p (repr (Gamma b)) repr)
            => FreeGM f (T repr) -> T repr
runSentence phi = eval_with @repr @a exists (/\) (handle phi) (empty @b @repr)

-- | Examples from README

test1 = runSentence @Print @Entity @Entity $ every (return dog <| (return who |> (return chase |> bind (some cat)))) <| (return catch |> it)

test2 = runSentence @Eval @Entity @Entity $ every (return dog <| (return who |> (return chase |> bind (some cat)))) <| (return catch |> it)

test3 = runSentence @CoqTerm @Entity @Entity $ every (return dog <| (return who |> (return chase |> bind (some cat)))) <| (return catch |> it)

-- If you evaluate, e.g., test3 in your REPL, you should get:
-- >>> test3
-- (forall (x : Entity), ((exists (y : Entity), ((cat y) /\ (((chase y) x) /\ (dog x)))) -> (forall (y : Entity), ((cat y) -> ((((chase y) x) /\ (dog x)) -> ((catch (sel (upd y emp))) x))))))

test4 = runSentence @CoqTerm @Entity $ some dog <| (return chase |> some cat)

-- >>> test4
-- (exists (x : Entity), (exists (y : Entity), (((dog x) /\ (cat y)) /\ ((chase y) x))))

test5 = runSentence @CoqTerm @Entity $ some dog <| (return catch |> some cat)

-- >>> test5
-- (exists (x : Entity), (exists (y : Entity), (((dog x) /\ (cat y)) /\ ((catch y) x))))

sentence6 :: (Lambda repr,
              Context Entity repr,
              Heyting repr,
              HOL Entity repr,
              Constant (Entity -> Bool) "dog" repr,
              Constant (Entity -> Bool) "cat" repr,
              Constant (Entity -> Entity -> Bool) "chase" repr)
          => FreeGM
              (Det repr
               ∘ (Scope repr
                  ∘ (Get (repr [Entity])
                     ∘ (Put (repr [Entity])
                        ∘ (Choose repr Entity
                           ∘ (Get (repr [Entity])
                              ∘ (Put (repr [Entity])
                                 ∘ Id)))))))
              (T repr)
sentence6 = bind (every (return dog)) <| (return chase |> bind (some cat))

sentence7 :: (Lambda repr,
              Context Entity repr,
              Constant (Entity -> Entity -> Bool) "catch" repr)
          => FreeGM (Get (repr [Entity]) ∘ (Get (repr [Entity]) ∘ Id)) (T repr)
sentence7 = it <| (return catch |> it)

discourse1 ::  (Cartesian repr,
                Lambda repr,
                Heyting repr,
                Context Entity repr,
                HOL Entity repr,
                Constant (Entity -> Bool) "dog" repr,
                Constant (Entity -> Bool) "cat" repr,
                Constant (Entity -> Entity -> Bool) "chase" repr,
                Constant (Entity -> Entity -> Bool) "catch" repr)
           => FreeGM
               (Get (repr (Gamma Entity))
                ∘ (Choose repr ()
                   ∘ (Put (repr (Gamma Entity))
                      ∘ (Get (repr (Gamma Entity))
                         ∘ (Get (repr (Gamma Entity))
                            ∘ Id)))))
               (T repr)
discourse1 = handle sentence6 >@ sentence7

test6 = runSentence @CoqTerm @Entity @Entity @() discourse1

-- >>> test6
-- ((forall (x : Entity), ((dog x) -> ((dog x) -> (exists (y : Entity), ((cat y) /\ ((chase y) x)))))) /\ ((catch (sel emp)) (sel emp)))

discourse2 :: (Cartesian repr,
               Lambda repr,
               Heyting repr,
               Context Entity repr,
               HOL Entity repr,
               Constant (Entity -> Bool) "dog" repr,
               Constant (Entity -> Bool) "cat" repr,
               Constant (Entity -> Entity -> Bool) "chase" repr,
               Constant (Entity -> Entity -> Bool) "catch" repr)
           => FreeGM
               (Det repr
                ∘ (Scope repr
                   ∘ (Get (repr (Gamma Entity))
                      ∘ (Put (repr (Gamma Entity))
                         ∘ (Choose repr Entity
                            ∘ (Get (repr (Gamma Entity))
                               ∘ (Put (repr (Gamma Entity))
                                  ∘ (Get (repr (Gamma Entity))
                                     ∘ (Get (repr (Gamma Entity))
                                        ∘ Id)))))))))
               (T repr)
discourse2 = sentence6 >@ sentence7

test7 = runSentence @CoqTerm @Entity @Entity discourse2

-- >>> test7
-- (forall (x : Entity), ((dog x) -> ((dog x) -> (exists (y : Entity), ((cat y) /\ (((chase y) x) /\ ((catch (sel (upd y (upd x emp)))) (sel (upd y (upd x emp))))))))))
