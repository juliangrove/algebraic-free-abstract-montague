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
Axiom every_dog_who_chased_a_cat_caught_it : ((forall (x : Entity), ((exists (y : Entity), ((((chase y) x) /\ (dog x)) /\ ((cat y) /\ (tt = tt)))) -> (exists (y : Entity), (((((chase y) x) /\ (dog x)) /\ (((catch (sel (upd y emp))) x) /\ (tt = tt))) /\ ((cat y) /\ (tt = tt)))))) /\ (tt = tt)).

(* Premise: 'Some dog chased some cat.' *)
Axiom some_dog_chased_some_cat : (exists (x : Entity), (exists (y : Entity), (((chase y) x) /\ ((dog x) /\ ((cat y) /\ (tt = tt)))))).

(* Conclusion: 'Some dog caught some cat. *)
Definition some_dog_caught_some_cat : (exists (x : Entity), (exists (y : Entity), (((catch y) x) /\ ((dog x) /\ ((cat y) /\ (tt = tt)))))).
Proof.
  destruct some_dog_chased_some_cat.
  destruct every_dog_who_chased_a_cat_caught_it.
  pose (H0 x).
  assert ((exists y : Entity, (chase y x /\ dog x) /\ cat y /\ tt = tt)).
  destruct H.
  destruct H.
  destruct H2.
  exists x0.
  auto.
  pose (e H2).
  destruct e0.
  destruct H3.
  destruct H3.
  rewrite anaphora_resolution in H5.
  destruct H3.
  destruct H5.
  exists x.
  exists x0.
  auto.
Qed.
