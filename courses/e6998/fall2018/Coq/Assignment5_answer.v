(** * Assignment 5: COMS E6998 Formal Verification of System Software *)

(** 

    - Due 12/29/2018 at 6:10 pm
    - Replace all the Admitted with your proofs or definitions.
    - Submit the filled in Assignment5.v via coursework2
    - Academic Honesty
      The computer science department has very strict policies. 
      Please read the department [Academic Honesty page](http://www.cs.columbia.edu/education/honesty/).
      You MUST submit original homework written by you and you alone.
      Do not look at anybody else’s answer. 
      Do not show anybody your answer, or leave your answer where somebody else could see it.
      Cases of non-original submission will receive a 0 and will be referred to the Judicial Committee.

    1) To compile the assigment, first download the following files
    
    _CoqProject 
    Coq_Lecture4_Program.v
    Coq_Lecture5_Hoare.v
    Assignment5.v
    
    in the same directory.
    
    2) Then generate the Makefile in the command line:
    
    [ coq_makefile -f _CoqProject Coq_Lecture4_Program.v Coq_Lecture5_Hoare.v -o Makefile ]
    
    3) Make the files by
    
    [make]
*)

Set Warnings "-notation-overridden,-parsing".
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations.

From LF Require Export Coq_Lecture5_Hoare.

Inductive dcom : Type :=
| DCSkip
| DCSeq (d1 d2:  dcom)
| DCAsgn (X: string) (e: aexp)
| DCIf (b: bexp) (d1: dcom) (d2: dcom)
| DCWhile (b: bexp) (inv: Assertion) (body: dcom).

Inductive decorated : Type :=
  | Decorated : Assertion -> dcom -> Assertion -> decorated.

Notation "'SKIP'" := DCSkip.
Notation "l '::=' a"
  := (DCAsgn l a)
       (at level 60, a at next level).
Notation "'WHILE' b [[ INV ]] 'DO'  d 'END'"
  := (DCWhile b INV d)
       (at level 80, right associativity).
Notation "'IFB' b 'THEN' d 'ELSE' d' 'FI'"
  := (DCIf b d d')
       (at level 80, right associativity).
Notation " d ;; d' "
  := (DCSeq d d')
       (at level 80, right associativity).
Notation "[[ P ]] d [[ Q ]]"
  := (Decorated P d Q) (at level 90, d at next level).

Example dec_while : decorated := 
  [[ fun st => True ]]
  WHILE !(X = 0)
  [[ fun _ => True ]]
  DO
    X ::= X - 1
  END
  [[ fun st => st X = 0 ]].

(** It is easy to go from a [dcom] to a [com] by erasing all
    annotations. *)
Fixpoint extract (d:dcom) : com :=
  match d with
  | DCSkip             => SKIP
  | DCSeq d1 d2        => (extract d1 ;; extract d2)
  | DCAsgn X a         => X ::= a
  | DCIf b d1 d2       => IFB b THEN extract d1 ELSE extract d2 FI
  | DCWhile b _ d      => WHILE b DO extract d END
  end.  
  
Definition extract_dec (dec : decorated) : com :=
  match dec with 
  | Decorated _ d _ => extract d
  end.

Example extract_correct:
  extract_dec dec_while =
  WHILE !(X = 0)
  DO
    X ::= X - 1
  END.
Proof.
  reflexivity.
Qed.

(** It is straightforward to extract the precondition and
    postcondition from a decorated program. *)

Definition pre_dec (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d _ => P
  end.

Definition post_dec (dec : decorated) : Assertion :=
  match dec with
  | Decorated _ d Q => Q
  end.

(** We can express what it means for a decorated program to be
    correct as follows: *)

Definition dec_correct (dec : decorated) :=
  {{pre_dec dec}} (extract_dec dec) {{post_dec dec}}.

Example dec_correct_correct:
  dec_correct dec_while =
  {{ fun st => True }}
  WHILE !(X = 0)
  DO
    X ::= X - 1
  END
  {{ fun st => st X = 0 }}.
Proof.
  reflexivity.
Qed.

(** To check whether this Hoare triple is _valid_, we need a way to
    extract the "proof obligations" from a decorated program.  These
    obligations are often called _verification conditions_, because
    they are the facts that must be verified to see that the
    decorations are logically consistent and thus add up to a complete
    proof of correctness. *)

(* ================================================================= *)
(** ** Extracting Verification Conditions *)

(** The function [verification_conditions] takes a [dcom] [d] together
    with a precondition [P] and returns a _proposition_ that, if it
    can be proved, implies that the triple [{{P}} (extract d) {{post d}}]
    is valid. *)

(** It does this by walking over [d] and generating a big
    conjunction including all the "local checks" that we listed when
    we described the informal rules for decorated programs.  (Strictly
    speaking, we need to massage the informal rules a little bit to
    add some uses of the rule of consequence, but the correspondence
    should be clear.) *)

Definition assert_implies (P Q : Assertion) : Assertion :=
  fun st =>  P st -> Q st.

Notation "P ->> Q" := (assert_implies P Q)
                        (at level 80).

Definition assert_and (P Q : Assertion) : Assertion :=
  fun st =>  P st /\ Q st.

Notation "P //\ Q" := (assert_and P Q)
                        (at level 70).

Definition assert_not (P : Assertion) : Assertion :=
  fun st =>  ~ P st.

Notation "~~ P" := (assert_not P)
                     (at level 60).

Definition ATrue : Assertion :=
  fun st => True.

Fixpoint VC (d:dcom) (Q : Assertion) : Assertion * Assertion :=
  match d with
  | DCSkip => (Q, ATrue)
  | DCSeq d1 d2 =>
    match VC d2 Q with
    | (wp2, sd2) =>
      match VC d1 wp2 with
      | (wp1, sd1) =>
        (wp1, sd1 //\ sd2)
      end
    end
  | DCAsgn X a => (Q [a // X], ATrue)
  | DCIf b d1 d2 =>
    match VC d1 Q, VC d2 Q with
    | (wp1, sd1), (wp2, sd2) =>
      ((bassn b ->> wp1)
         //\ (~~(bassn b) ->> wp2),
       (sd1 //\ sd2))
    end
  | DCWhile b INV d =>
    (INV,
     match VC d INV with
     | (wp, sd) =>
       (INV //\ bassn b ->> wp)
         //\sd
         //\ (INV //\ ~~(bassn b) ->> Q)
     end)
end.

Definition VC_dec (dec : decorated) : Prop :=
  match dec with
  | Decorated P d Q =>
    match VC d Q with
    | (wp, sd) =>
      forall st, (P st -> wp st) /\ sd st
    end
  end.

(** And now the key theorem, stating that [verification_conditions]
    does its job correctly.  Not surprisingly, we need to use each of
    the Hoare Logic rules at some point in the proof. *)

Theorem verification_correct : forall d,
  VC_dec d -> dec_correct d.
Proof.
  destruct d as [P d Q].
  generalize dependent Q.
  generalize dependent P.
  induction d; intros P Q Hdec; simpl in *.
  - (* Skip *)
    eapply hoare_weak_pre.
    + apply hoare_skip.
    + simpl. intros st. eapply Hdec.
  - (* Seq *)
    destruct (VC d2 Q) as (wp2 & sd2) eqn: Hvc2.
    destruct (VC d1 wp2) as (wp1 & sd1) eqn: Hvc1.    
    eapply hoare_seq; simpl.
    + apply IHd2. rewrite Hvc2. intros.
      split; eauto. eapply Hdec.
    + simpl.
      apply IHd1. rewrite Hvc1. intros.
      split; eapply Hdec.
  - (* Asgn *)
    eapply hoare_weak_pre.
    + apply hoare_asgn.
    + simpl. intros st. eapply Hdec.
  - (* If *)
    destruct (VC d2 Q) as (wp2 & sd2) eqn: Hvc2.
    destruct (VC d1 Q) as (wp1 & sd1) eqn: Hvc1.    
    apply hoare_if.
    + simpl. eapply hoare_weak_pre.
      * eapply IHd1. rewrite Hvc1. intros.
        split; eauto. eapply Hdec.
      * simpl. intros st (HP & Hb).
        destruct (Hdec st) as (Ht & _).
        eapply Ht; eauto.
    + simpl. eapply hoare_weak_pre.
      * eapply IHd2. rewrite Hvc2.
        intros st. split; eauto.
        eapply Hdec.
      * simpl. intros st (HP & Hb).
        destruct (Hdec st) as (Ht & _).
        eapply Ht; eauto.
  - (* While *)
    destruct (VC d inv) as (wp & sd) eqn: Hvc.
    eapply hoare_weak_pre.
    + instantiate (1:= inv).
      simpl.
      eapply hoare_weak_post; eauto.
      * apply hoare_while.
        eapply IHd. rewrite Hvc.
        intros. eapply Hdec.
      * intros st. eapply Hdec.
    + simpl. intros st. eapply Hdec.
Qed.

(* ================================================================= *)
(** ** Automation *)

(** Now that all the pieces are in place, we can verify an entire program. *)

Ltac my_simpl :=
  unfold assert_implies, assert_and, assert_not, assn_sub, bassn, beval, aeval, t_update in *;
  simpl in *; intros;
  repeat match goal with
         | [ H0: _ /\ _ |- _ ] => destruct H0
         end;
  simplb; eauto; try omega; try congruence.

Ltac verify :=
  intros;
  match goal with
  | [|- dec_correct _ ] =>
    apply verification_correct;
    simpl; repeat split; my_simpl
  end.

Theorem dec_while_correct :
  dec_correct dec_while.
Proof.
  verify.
Qed.

(** Another example (formalizing a decorated program we've seen
    before): *)
Example subtract_slowly_dec (m:nat) (p:nat) : decorated := 
  [[ fun st => st X = m /\ st Z = p ]]
  WHILE ! (X = 0)
  [[ fun st => st Z - st X = p - m ]]
  DO
     Z ::= Z - 1;;
     X ::= X - 1
  END
  [[ fun st => st Z = p - m ]].

Theorem subtract_slowly_dec_correct : forall m p,
    dec_correct (subtract_slowly_dec m p).
Proof.
  verify.
Qed.

(* ================================================================= *)
(** ** Examples *)

(** In this section, we use the automation developed above to verify
    formal decorated programs corresponding to most of the informal
    ones we have seen. *)

(* ----------------------------------------------------------------- *)
(** *** Swapping Using Addition and Subtraction *)

Definition swap : com :=
  X ::= X + Y;;
  Y ::= X - Y;;
  X ::= X - Y.

Definition swap_dec m n : decorated :=
  [[ fun st => st X = m /\ st Y = n ]]
  X ::= X + Y ;;
  Y ::= X - Y ;;
  X ::= X - Y
  [[ fun st => st X = n /\ st Y = m]].

Theorem swap_correct : forall m n,
    dec_correct (swap_dec m n).
Proof.
  verify.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Simple Conditionals *)
Definition if_minus_plus_com :=
  IFB X <= Y
  THEN Z ::= Y - X
  ELSE Y ::= X + Z
  FI.

Definition if_minus_plus_dec :=
  [[ fun st => True ]]
  IFB X <= Y  THEN
    Z ::= Y - X
  ELSE
    Y ::= X + Z
  FI
  [[ fun st => st Y = st X + st Z ]].

Theorem if_minus_plus_correct :
  dec_correct if_minus_plus_dec.
Proof.
  verify.
Qed.

Definition if_minus_dec :=
  [[ fun st => True ]]
  IFB X <= Y THEN
    Z ::= Y - X
  ELSE
    Z ::= X - Y
  FI
  [[ fun st => st Z + st X = st Y \/ st Z + st Y = st X ]].

Theorem if_minus_correct :
  dec_correct if_minus_dec.
Proof.
  verify.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Division *)

Definition div_mod_dec (a b : nat) : decorated := 
  [[ fun st => True ]]
  X ::= a ;;
  Y ::= 0 ;;
  WHILE b <= X
  [[ fun st => b * st Y + st X = a ]]
  DO
    X ::= X - b ;;
    Y ::= Y + 1
  END
  [[ fun st => b * st Y + st X = a /\ (st X < b) ]].

Theorem div_mod_dec_correct : forall a b,
  dec_correct (div_mod_dec a b).
Proof.
  verify.
  rewrite mult_plus_distr_l. omega.
Qed.


Local Opaque minus mult plus Nat.eqb.

(* ----------------------------------------------------------------- *)
(** *** Square Roots *)
 
Definition sqrt_dec m : decorated := 
  [[ fun st => st X = m ]]
  Z ::= 0 ;;
  WHILE (Z+1)*(Z+1) <= X
  [[ fun st => st X = m /\ st Z*st Z<=m ]]
  DO
    Z ::= Z + 1
  END
  [[ fun st => st Z*st Z<=m /\ m<(st Z+1)*(st Z+1) ]].

Theorem sqrt_correct : forall m,
  dec_correct (sqrt_dec m).
Proof. verify. Qed.

(* ----------------------------------------------------------------- *)
(** *** Two loops *)

Definition two_loops_dec (a b c : nat) : decorated :=
  [[ fun st => True ]]
  X ::= 0 ;;
  Y ::= 0 ;;
  Z ::= c ;;
  WHILE !(X = a)
  [[ fun st => st Z = st X + c /\ st Y = 0 ]]
  DO
    X ::= X + 1 ;;
    Z ::= Z + 1
  END ;;
  WHILE !(Y = b)
  [[ fun st => st Z = a + st Y + c ]]
  DO
    Y ::= Y + 1 ;;
    Z ::= Z + 1 
  END
  [[ fun st => st Z = a + b + c ]].

Theorem two_loops_correct : forall a b c,
  dec_correct (two_loops_dec a b c).
Proof. verify. Qed.