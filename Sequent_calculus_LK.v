Require Import Lang.
Require Import List.
Import List.ListNotations.


Coercion list_to_prop (P : prop) : (list prop) := [P].
Reserved Notation "G ⇒ p" (no associativity, at level 61). (* 21d2 *)

Inductive LK : list prop -> list prop -> Prop :=
(* Axiom : A |- A *)
| LKA: forall p : prop, p ⇒ p
(* Structral Rules *)
(* Weakening *)
|LKrW: forall G D (a: prop), G ⇒ D -> G ⇒ a :: D
|LKlW: forall G D (a: prop), G ⇒ D -> G ++ a ⇒ D
(* Exchange *)
|LKrE: forall G D D' (a b : prop), G ⇒ D ++ (a :: b :: D') -> 
        G ⇒ D ++ (b :: a :: D')
|LKlE: forall G G' D (a b : prop), G ++ (a :: b :: G') ⇒ D ->
        G ++ (b :: a :: G') ⇒ D
(* Contraction *)
|LKrC: forall G D (a : prop), G ⇒ a :: a :: D -> G ⇒ a :: D
|LKlC: forall G D (a : prop), G ++ a ++ a ⇒ D -> G ++ a ⇒ D
(* Logical Rules *)
(* Conjunction *)
|LKrA: forall G G' D D' (a b: prop),
G ⇒ a :: D -> G' ⇒ b :: D' -> G ++ G' ⇒ (a ∧ b) :: D ++ D'
|LKl1A: forall G D (a b : prop),
G ++ a ⇒ D -> G ++ (a ∧ b) ⇒ D
|LKl2A: forall G D (a b : prop),
G ++ b ⇒ D -> G ++ (a ∧ b) ⇒ D
(* Disjunction *)
|LKr1O: forall G D (a b : prop),
G ⇒ a :: D -> G ⇒ (a ∨ b) :: D
|LKr2O: forall G D (a b : prop),
G ⇒ b :: D -> G ⇒ (a ∨ b) :: D
|LKlO: forall G G' D D' (a b : prop),
G ++ a ⇒ D -> G' ++ b ⇒ D' -> G ++ G' ++ (a ∨ b) ⇒ D ++ D'
(* Negation *)
|LKrN: forall G D (a : prop), G ++ a ⇒ D -> G ⇒ (¬ a) :: D
|LKlN: forall G D (a : prop), G ⇒ a :: D -> G ++ (¬ a) ⇒ D
(* Implication *)
|LKrI: forall G D (a b : prop), G ++ a ⇒ b :: D ->
        G ⇒ (a ⊃ b) :: D
|LKlI: forall G G' D D' (a b : prop),
        G ⇒ a :: D -> G' ++ b ⇒ D' ->
        G ++ G' ++ (a ⊃ b) ⇒ D ++ D'

where "G ⇒ p" := (LK G p).

Lemma mp : forall p q : prop, (p ⊃ q)::p ⇒ q.
Proof.
  intros p q. 
  apply (LKlE [] [] q p (p ⊃ q)). simpl.
  apply (LKlI p [] [] q p q).
  - apply (LKA p).
  - simpl. apply (LKA q).
Qed.

Lemma cut : forall (G G' D D' : list prop) (a : prop),
G ⇒ a :: D -> G' ++ a ⇒ D' -> G ++ G' ⇒ D ++ D'.
Admitted.

Lemma deduction : forall p q : prop, p ⇒ q <-> [] ⇒ p ⊃ q.
Proof.
    intros. split. 
    - intros. apply LKrI. simpl. apply H.
    - intros. apply (cut [] [p] [] [q] (p ⊃ q)).
        + apply H.
        + apply (LKlE [] [] q (p ⊃ q) p). apply mp.
Qed. 