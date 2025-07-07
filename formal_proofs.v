(* ========================================= *)
(* FormalProofs: Basic Propositional and Predicate Logic in Coq *)
(* ========================================= *)

(* === Propositional Logic === *)

(* 1. Law of Excluded Middle (Classical Logic Required) *)
Require Import Classical.

Theorem excluded_middle : forall P : Prop, P \/ ~P.
Proof.
  apply classic.
Qed.

(* 2. Modus Ponens: From P and P → Q, derive Q (Constructive) *)
Theorem modus_ponens : forall P Q : Prop, P -> (P -> Q) -> Q.
Proof. intros P Q HP HPQ. apply HPQ. exact HP. Qed.

(* 3. Double Negation Introduction: Constructively valid *)
Theorem double_negation_intro : forall P : Prop, P -> ~~P.
Proof. intros P HP HNP. apply HNP. exact HP. Qed.

(* 4. De Morgan's Law 1: ¬(P ∧ Q) → ¬P ∨ ¬Q (Classical) *)
Theorem de_morgan_1_classical : forall P Q : Prop, ~(P /\ Q) -> ~P \/ ~Q.
Proof.
  intros P Q H.
  destruct (classic P) as [HP | HNP].
  - destruct (classic Q) as [HQ | HNQ].
    + exfalso. apply H. split; assumption.
    + right. exact HNQ.
  - left. exact HNP.
Qed.

(* 5. De Morgan's Law 2: ¬(P ∨ Q) ↔ ¬P ∧ ¬Q (Constructive) *)
Theorem de_morgan_2 : forall P Q : Prop, ~(P \/ Q) <-> ~P /\ ~Q.
Proof.
  intros P Q. split.
  - intros H. split; intros HPQ; apply H; [left | right]; exact HPQ.
  - intros [HNP HNQ] [HP | HQ]; [apply HNP | apply HNQ]; assumption.
Qed.

(* === Predicate Logic === *)

Section Predicate_Logic_Proofs.

Variable U : Type.
Variable P : U -> Prop.

(* 6. Universal Implies Existential: ∀x P(x) ⇒ ∃x P(x) (Constructive) *)
Theorem forall_implies_exists : forall (x0 : U), (forall x : U, P x) -> exists x : U, P x.
Proof. intros x0 H. exists x0. apply H. Qed.

(* 7. Existential Implies Not Universal: ∃x P(x) ⇒ ¬∀x ¬P(x) (Constructive) *)
Theorem exists_implies_not_forall : (exists x : U, P x) -> ~(forall x : U, ~P x).
Proof. intros [x HPx] Hforall. apply (Hforall x). exact HPx. Qed.

(* 8. Negation of Existential Implies Universal Negation: ¬∃x P(x) ⇒ ∀x ¬P(x) (Constructive) *)
Theorem not_exists_implies_forall_not : ~(exists x : U, P x) -> forall x : U, ~P x.
Proof.
  intros H x HPx.
  apply H.
  exists x.
  exact HPx.
Qed.

End Predicate_Logic_Proofs.
