Require Import Lang.
Require Import List.
Require Import Sequent_calculus_LK.
Require Import Finset.
Import List.ListNotations.
Include BinNatDef.N.

Axiom prop_to_nat: prop -> nat.
Axiom nat_to_prop: nat -> prop.

Axiom prop_to_prop: forall p, nat_to_prop(prop_to_nat(p)) = p.
Axiom nat_to_nat: forall n, prop_to_nat(nat_to_prop(n)) = n.

Coercion p_nat (p : prop) : nat := prop_to_nat(p).

Reserved Notation "G ⤑ p >< n" (no associativity, at level 68).
Inductive LKS : Node -> finset -> finset -> Prop :=
(* Axiom : A |- A *)
(* 1 *)
|LKSA: forall p: prop, {{p}} ⤑ {{p}} >< leaf
(* Weakening *)
(* 2 *)
|LKSrW: forall G D (a: prop) n, G ⤑ D >< n -> G ⤑ {{a}} ∪ D >< ☉n
(* 3 *)
|LKSlW: forall G D (a: prop) n, G ⤑ D >< n -> {{a}} ∪ G  ⤑ D >< ☉ n
(* Conjunction *)
(* 4 *)
|LKSrA: forall G D (a b: prop) m n,
G ⤑ {{a}} ∪ D >< m-> G ⤑ {{b}} ∪ D >< n -> G ⤑ ({{a ∧ b}} ∪ D)  >< (m ≍ n)
(* 5 *)
|LKSl1A: forall G D (a b : prop) n,
{{a}} ∪ G ⤑ D >< n -> {{(a ∧ b)}} ∪ G ⤑ D >< ☉ n
(* 6 *)
|LKSl2A: forall G D (a b : prop) n,
{{b}} ∪ G ⤑ D >< n -> {{(a ∧ b)}} ∪ G ⤑ D >< ☉ n
(* Disjunction *)
(* 7 *)
|LKSr1O: forall G D (a b : prop) n,
G ⤑ {{a}} ∪ D >< n -> G ⤑ {{a ∨ b}} ∪ D >< ☉ n
(* 8 *)
|LKSr2O: forall G D (a b : prop) n,
G ⤑ {{b}} ∪ D >< n -> G ⤑ {{a ∨ b}} ∪ D >< ☉ n
(* 9 *)
|LKSlO: forall G D (a b : prop) m n,
{{a}} ∪ G ⤑ D >< m -> {{b}} ∪ G ⤑ D >< n -> {{a ∨ b}} ∪ G  ⤑ D >< (m ≍ n)
(* Negation *)
(* 10 *)
|LKSrN: forall G D (a : prop) n, {{a}} ∪ G ⤑ D >< n -> G ⤑ {{¬ a}} ∪ D >< ☉ n
(* 11 *)
|LKSlN: forall G D (a : prop) n, G ⤑ {{a}} ∪ D >< n -> {{¬ a}} ∪ G  ⤑ D >< ☉ n
(* Implication *)
(* 12 *)
|LKSrI: forall G D (a b : prop) n, {{a}} ∪ G  ⤑ {{b}} ∪ D >< n ->
        G ⤑ {{a ⊃ b}} ∪ D >< ☉ n
(* 13 *)
|LKSlI: forall G D (a b : prop) m n,
        G ⤑ {{a}} ∪ D >< m -> {{b}} ∪ G ⤑ D >< n->
        {{a ⊃ b}} ∪ G ⤑ D >< (m ≍ n) 
where "G ⤑ p >< n" := (LKS n G p).

Lemma mp : forall p q : prop, exists n, {{p ⊃ q}} ∪ {{p}} ⤑ {{q}} >< n.
Proof.
  intros p q.
  exists ((☉ leaf) ≍ (☉ leaf)).
  constructor 13.
    - rewrite union_comm. constructor 2. constructor 1.
    - rewrite union_comm. constructor 3. constructor 1.
Qed.
