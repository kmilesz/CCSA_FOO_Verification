(************************************************************************)
(* Copyright (c) 2022, Gergei Bana, Qianli Zhang                        *)
(*                                                                      *)
(* This work is licensed under the MIT license. The license is          *)
(* described in the file "LICENSE" available at the root of the source  *)
(* or at https://opensource.org/licenses/MIT                            *)
(*                                                                      *)
(* Special thanks to Dr. Eeralla                                        *)
(************************************************************************)


Require Export H_NonceImplications.




(*  *)
Notation "b0 & b1"    := (If b0 Then b1 Else FAlse)      (at level 21, right associativity).  (* *)
Notation "b0 'or' b1" := (If b0 Then TRue Else b1)       (at level 22, right associativity).  (* *)
Notation "! b "       := (If b Then FAlse Else TRue)     (at level 20, right associativity).  (* *)
Notation "b0 ⨀ b1"   := (If b0 Then b1 Else (!b1))      (at level 22, right associativity).  (* Gives TRue iff both b0 or b1 are TRue or both are FAlse *) 


(*  *)
Proposition AndComm :
  forall A B,
    bppt A ->
    bppt B ->
    A & B = B & A.
Proof.
  intros.
  rewrite (@If_tf B) at 1.
  rewrite (@If_morph (fun x => If A Then x Else FAlse) B).
  rewrite If_same.
  rewrite <- (If_tf).
  reflexivity.
  all: ProveboolandContext.
Qed.



Proposition AndAssoc : 
  forall A B C,
    (A & B) & C = A & B & C.
Proof.
  intros.
  rewrite (@If_morph (fun x => If x Then C Else FAlse) A).
  rewrite If_false.
  reflexivity.
  ProveContext.
Qed.



Proposition OrComm:
  forall A B,
    bppt A ->
    bppt B ->
    A or B = B or A.
Proof.
  intros.
  rewrite (@If_tf B) at 1.
  rewrite (@If_morph (fun x => A or x)).
  rewrite If_same.
  rewrite <- If_tf.
  reflexivity.
  all: ProveboolandContext.
Qed.



Proposition OrAssoc:
  forall A B C,
    (A or B) or C = A or B or C.
Proof.
  intros.
  rewrite (@If_morph (fun x => x or C)).
  rewrite If_true.
  reflexivity.
  ProveContext.
Qed.



Proposition NotElim :
  forall b x y,
    If ! b Then x Else y = If b Then y Else x.
Proof.
  intros.
  rewrite (@If_morph (fun z => If z Then x Else y) _ _ _ ).
  rewrite If_false.
  rewrite If_true.
  reflexivity.
  ProveContext.
Qed.


(**)
Proposition DeMorganNotOr : forall b1 b2,
    ! (b1 or b2) = !b1 & !b2.
Proof.
  intros.
  rewrite (@If_morph (fun x => If x Then FAlse Else TRue)). rewrite If_true.
  rewrite (@If_morph (fun x => x & ! b2)). rewrite If_false, If_true.
  reflexivity.
  all : ProveContext.
Qed.


Proposition XnorComm : forall b0 b1, bppt b0 -> bppt b1 -> b0 ⨀ b1 = b1 ⨀ b0.
Proof.
{ intros. rewrite (@If_morph (fun x => If b0 Then b1 Else x)). rewrite (@If_eval (fun b1 => b0 & b1) (fun b1 => If b0 Then b1 Else TRue)). rewrite <- If_tf.
  reflexivity.
  all : ProveboolandContext. }
Qed.




(**)(* Further useful propositions *)


Proposition OrComp : forall b1 b2 b3 x y,
    If b1 or b2 or b3 Then x Else y
    =
    If b1 Then x Else If b2 Then x Else If b3 Then x Else y.
Proof.
  intros.
  rewrite (@If_morph (fun b => If b Then x Else y)). rewrite If_true.
  rewrite (@If_morph (fun b => If b Then x Else y)). rewrite If_true.
  reflexivity.
  all : ProveContext.
Qed.





(**)
Proposition DeMorganNot2Or : forall b1 b2 b3,
    ! (b1 or b2 or b3) = !b1 & !b2 & !b3.
Proof.
  intros.
  rewrite (@If_morph (fun x => If x Then FAlse Else TRue)). rewrite If_true.
  rewrite (@If_morph (fun x => If x Then FAlse Else TRue)). rewrite If_true.
  rewrite (@If_morph (fun x => x & ! b2 & ! b3)). rewrite If_false, If_true.
  rewrite (@If_morph (fun x => x & ! b3)). rewrite If_false, If_true.
  reflexivity.
  all : ProveContext.
Qed.


Proposition CNF_IfThenElse : forall b1 b2 b3,
    ! (b1 or b2 or b3) =
      If b1 Then FAlse Else If b2 Then FAlse Else If b3 Then FAlse Else TRue.
Proof.
  intros.
  rewrite DeMorganNot2Or.
  rewrite NotElim. rewrite NotElim.
  reflexivity.
Qed.
