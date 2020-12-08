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
Axiom every_dog_who_chased_a_cat_caught_it : (forall (x : Entity), ((exists (y : Entity), ((cat y) /\ (((chase y) x) /\ (dog x)))) -> (exists (y : Entity), ((cat y) /\ ((((chase y) x) /\ (dog x)) /\ ((catch (sel (upd y emp))) x)))))).

(* Premise: 'Some dog chased some cat.' *)
Axiom some_dog_chased_some_cat : (exists (x : Entity), (exists (y : Entity), (((dog x) /\ (cat y)) /\ ((chase y) x)))).

(* Conclusion: 'Some dog caught some cat. *)
Definition some_dog_caught_some_cat : (exists (x : Entity), (exists (y : Entity), (((dog x) /\ (cat y)) /\ ((catch y) x)))).
Proof.
  destruct some_dog_chased_some_cat as [x [y [[dog cat] chase]]].
  destruct (every_dog_who_chased_a_cat_caught_it x).
  exists y; exact (conj cat (conj chase dog)).
  destruct H as [cat0 [[chase0 dog0] catch0]].
  rewrite anaphora_resolution in catch0.
  exists x, x0; exact (conj (conj dog cat0) catch0).
Qed.
