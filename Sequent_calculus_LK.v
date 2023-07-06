Require Import Lang.
Require Import List.
Import List.ListNotations.


Coercion list_to_prop (P : prop) : (list prop) := [P].
Reserved Notation "G ⇒ p >< n" (no associativity, at level 61). (* 21d2 *)

Inductive LK : nat -> list prop -> list prop -> Prop :=
(* Axiom : A |- A *)
| LKA: forall p : prop, p ⇒ p >< 0
(* Structral Rules *)
(* Weakening *)
|LKrW: forall G D (a: prop) n, G ⇒ D >< n-> G ⇒ a :: D >< (S n)
|LKlW: forall G D (a: prop) n, G ⇒ D >< n -> G ++ a ⇒ D >< (S n)
(* Exchange *)
|LKrE: forall G D D' (a b : prop) n, G ⇒ D ++ (a :: b :: D') >< n -> 
        G ⇒ D ++ (b :: a :: D') >< (S n)
|LKlE: forall G G' D (a b : prop) n, G ++ (a :: b :: G') ⇒ D >< n ->
        G ++ (b :: a :: G') ⇒ D >< (S n)
(* Contraction *)
|LKrC: forall G D (a : prop) n, G ⇒ a :: a :: D >< n -> G ⇒ a :: D >< n
|LKlC: forall G D (a : prop) n, G ++ a ++ a ⇒ D >< n -> G ++ a ⇒ D >< (S n)
(* Logical Rules *)
(* Conjunction *)
|LKrA: forall G G' D D' (a b: prop) m n,
G ⇒ a :: D >< m-> G' ⇒ b :: D' >< n -> G ++ G' ⇒ (a ∧ b) :: D ++ D' >< (S (m + n))
|LKl1A: forall G D (a b : prop) n,
G ++ a ⇒ D >< n -> G ++ (a ∧ b) ⇒ D >< (S n)
|LKl2A: forall G D (a b : prop) n,
G ++ b ⇒ D >< n -> G ++ (a ∧ b) ⇒ D >< (S n)
(* Disjunction *)
|LKr1O: forall G D (a b : prop) n,
G ⇒ a :: D >< n -> G ⇒ (a ∨ b) :: D >< (S n)
|LKr2O: forall G D (a b : prop) n,
G ⇒ b :: D >< n -> G ⇒ (a ∨ b) :: D >< (S n)
|LKlO: forall G G' D D' (a b : prop) m n,
G ++ a ⇒ D >< m -> G' ++ b ⇒ D' >< n -> G ++ G' ++ (a ∨ b) ⇒ D ++ D' >< (S (m + n))
(* Negation *)
|LKrN: forall G D (a : prop) n, G ++ a ⇒ D >< n-> G ⇒ (¬ a) :: D >< (S n)
|LKlN: forall G D (a : prop) n, G ⇒ a :: D >< n -> G ++ (¬ a) ⇒ D >< (S n)
(* Implication *)
|LKrI: forall G D (a b : prop) n, G ++ a ⇒ b :: D >< n ->
        G ⇒ (a ⊃ b) :: D >< (S n)
|LKlI: forall G G' D D' (a b : prop) m n,
        G ⇒ a :: D >< m -> G' ++ b ⇒ D' >< n->
        G ++ G' ++ (a ⊃ b) ⇒ D ++ D' >< (S (m + n))

where "G ⇒ p >< n" := (LK n G p).

Lemma mp : forall p q : prop, exists n, (p ⊃ q)::p ⇒ q >< n.
Proof.
  intros p q.
  exists 2. 
  apply (LKlE [] [] q p (p ⊃ q)). simpl.
  apply (LKlI p [] [] q p q 0 0).
  - apply (LKA p).
  - simpl. apply (LKA q).
Qed.

Lemma cut : forall (G G' D D' : list prop) (a : prop) m n,
G ⇒ a :: D >< m -> G' ++ a ⇒ D' >< n -> exists r, G ++ G' ⇒ D ++ D' >< r.
Admitted.
(* 
Lemma deduction : forall p q : prop, p ⇒ q <-> [] ⇒ p ⊃ q.
Proof.
    intros. split. 
    - intros. apply LKrI. simpl. apply H.
    - intros. apply (cut [] [p] [] [q] (p ⊃ q)).
        + apply H.
        + apply (LKlE [] [] q (p ⊃ q) p). apply mp.
Qed.  *)