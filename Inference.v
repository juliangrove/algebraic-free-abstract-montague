(* 
   The sentences

       (1) Every dog who chased a cat caught it.
       (2) Some dog chased some cat.
       (3) Some dog caught some cat.
   
   are assigned Coq formulae by the Haskell code in /src, as illustrated at the
   end of Fragment.hs. This Coq file proves that sentences (1) and (2) entail
   sentence (3), in terms of the formulae they are assigned. Note the required
   axiom 'anaphora_resolution', which says that selecting from a context which
   has been updated with one element returns that element.
 *)

(* The type of entities *)
Parameter Entity : Set.
(* The type of contexts *)
Parameter Gamma : Set.

(* Lexicon *)
Parameter dog : Entity -> Prop.
Parameter cat : Entity -> Prop.
Parameter happy : Entity -> Prop.
Parameter chase : Entity -> Entity -> Prop.
Parameter catch : Entity -> Entity -> Prop.

(* Manipulation of contexts *)
Parameter emp : Gamma.
Parameter upd : Entity -> Gamma -> Gamma.
Parameter sel : Gamma -> Entity.

(* Inference example *)

(* Premise: anaphora resolution *)
Axiom anaphora_resolution : (forall (x : Entity), sel (upd x emp) = x).

(* Premise: 'Every dog who chased a cat caught it.' *)
Axiom every_dog_who_chased_a_cat_caught_it : (exists (x : unit), ((forall (y : Entity), ((exists (z : (prod Entity unit)), ((((chase (fst z)) y) /\ (dog y)) /\ ((cat (fst z)) /\ (tt = (snd z))))) -> (exists (z : (prod Entity unit)), (((((chase (fst z)) y) /\ (dog y)) /\ (exists (u : unit), (((catch (sel (upd (fst z) emp))) y) /\ (tt = u)))) /\ ((cat (fst z)) /\ (tt = (snd z))))))) /\ (tt = x))).

(* Premise: 'Some dog chased some cat.' *)
Axiom some_dog_chased_some_cat : (exists (x : (prod Entity (prod Entity unit))), (((chase (fst (snd x))) (fst x)) /\ ((dog (fst x)) /\ ((cat (fst (snd x))) /\ (tt = (snd (snd x))))))).

(* Conclusion: 'Some dog caught some cat. *)
Definition some_dog_caught_some_cat : (exists (x : (prod Entity (prod Entity unit))), (((catch (fst (snd x))) (fst x)) /\ ((dog (fst x)) /\ ((cat (fst (snd x))) /\ (tt = (snd (snd x))))))).
Proof.
  destruct some_dog_chased_some_cat.
  assert (H1 : exists z : Entity * unit, (chase (fst z) (fst x) /\ dog (fst x)) /\ cat (fst z) /\ tt = snd z).
  exists (fst (snd x), tt).
  simpl.
  destruct H.
  destruct H0.
  destruct H1.
  auto.
  destruct every_dog_who_chased_a_cat_caught_it.
  destruct H0.
  destruct (H0 (fst x) H1).
  destruct H3.
  destruct H3.
  destruct H5.
  destruct H5.
  pose (anaphora_resolution (fst x1)).
  rewrite e in H5.
  destruct H3.
  exists (fst x, (fst x1, tt)).
  destruct H4.
  simpl.
  exact (conj H5 (conj H7 (conj H4 (eq_refl tt)))).
Qed.
