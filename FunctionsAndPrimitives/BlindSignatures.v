
(************************************************************************)
(* Copyright (c) 2021, Gergei Bana and Qianli Zhang                     *)
(*                                                                      *)
(* This work is licensed under the MIT license. The license is          *)
(* described in the file "LICENSE" available at the root of the source  *)
(* or at https://opensource.org/licenses/MIT                            *)
(************************************************************************)


Require Import Core.
Require Import Pair.


(*  *)

Definition Blindness_prop (z : list ppt) (m0 m1 t n0 n1 : ppt) (t0 t1 : list ppt -> ppt)
           (blind brand acc ub: list ppt -> ppt ) (bot : ppt) : Prop :=
  Fresh n0 (m0 :: m1 :: t :: z) -> FreshTermc n0 t0 -> FreshTermc n0 t1 ->
  Fresh n1 (m0 :: m1 :: t :: z) -> FreshTermc n1 t0 -> FreshTermc n1 t1 ->
  let bn0 := brand [n0] in
  let bn1 := brand [n1] in
  let ti0 := t0 [blind [m0; t; bn0]; blind [m1; t; bn1]] in
  let ti1 := t1 [blind [m1; t; bn0]; blind [m0; t; bn1]] in
  z ++ [blind [m0; t; bn0]; blind [m1; t; bn1]; If acc [m0; t; bn0; ti0] & acc [m1; t; bn1; ti0]
                                                        Then ＜ ub [m0; t; bn0; ti0], ub [m1; t; bn1; ti0] ＞ Else ( ＜ bot, bot ＞)]
  ~
  z ++ [blind [m1; t; bn0]; blind [m0; t; bn1]; If acc [m1; t; bn0; ti1] & acc [m0; t; bn1; ti1]
                                                        Then ＜ ub [m0; t; bn1; ti1], ub [m1; t; bn0; ti1] ＞ Else (＜ bot, bot ＞)].



(* ------------------------------------------------ *)
(*  *)

Inductive UbNUDContextTerm (bn: ppt) (blind brand: list ppt -> ppt) : ppt -> Prop :=
| UbNUDAttContListTerm :
  forall (tl : list ppt) (f : list ppt -> ppt),
    ContextTerm Adversarial List f ->
    UbNUDContext bn blind brand tl ->
    UbNUDContextTerm bn blind brand (f tl)
| UbNUDBlindSign :
  forall (t1 t: ppt) ,
    FreshTerm bn t1 ->
    FreshTerm bn t ->
    UbNUDContextTerm bn blind brand (blind [t1; t; (brand [bn])])
with UbNUDContext (bn : ppt) (blind brand: list ppt -> ppt): list ppt -> Prop :=
| UbNUDFresh :
  forall tl ,
    Fresh bn tl ->
    UbNUDContext bn blind brand tl
| UbNUDContextConc :
  forall (u : ppt) (ul2 : list ppt),
    UbNUDContextTerm bn blind brand u ->
    UbNUDContext bn blind brand ul2 ->
    UbNUDContext bn blind brand (u :: ul2).

(*  *)

Proposition UbNUDFreshTerm : forall t bn blind brand, 
    FreshTerm bn t -> UbNUDContextTerm bn blind brand t.
Proof.
  intros.
  apply (frConc bn t []) in H.
  apply (UbNUDFresh bn blind brand [t]) in H.
  apply (UbNUDAttContListTerm bn blind brand [t] (fun lx => Nth 0 lx)) in H.
  unfold Nth in H; simpl in H.
  auto.
  ProveContext.
  ProveFresh.
Qed.

(* original constructive rule *)

Proposition UbNUDContextApp : forall bn, forall ul1 ul2 : list ppt, forall blind brand,
     UbNUDContext bn blind brand ul1 -> UbNUDContext bn blind brand ul2 -> UbNUDContext bn blind brand (ul1 ++ ul2).
Proof.
  intros.
  induction ul1.
  - simpl. auto.
  - inversion H.
    + inversion H1.
      apply (UbNUDFresh bn blind brand) in H7.
      apply (UbNUDFreshTerm a bn blind brand) in H6.
      apply IHul1 in H7.
      simpl. apply UbNUDContextConc; auto.
    + apply IHul1 in H4.
      simpl. apply UbNUDContextConc; auto.
Qed.

(*  *)
Definition UbNotUndefined_prop (t1 t n0 t2 : ppt)
           (blind brand acc ub: list ppt -> ppt ) (bot : ppt) : Prop :=
  let bn0 := brand [n0] in
  Fresh n0 [t; t1] ->
  UbNUDContextTerm n0 blind brand t2 ->
  ((acc [t1; t; bn0; t2]) & (ub [t1; t; bn0; t2] ≟ bot)) = FAlse.
