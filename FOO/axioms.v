(************************************************************************)
(* Copyright (c) 2022, Gergei Bana, Qianli Zhang                        *)
(*                                                                      *)
(* This work is licensed under the MIT license. The license is          *)
(* described in the file "LICENSE" available at the root of the source  *)
(* or at https://opensource.org/licenses/MIT                            *)
(*                                                                      *)
(* Special thanks to Dr. Eeralla                                        *)
(************************************************************************)


Require Import Coq.micromega.Lia.
Require Export ltacs.
Import ListNotations.


(* --------------------------------------------- *)
(*  phase identifiers are not the same *)

Axiom ph2Neqph3 : ph3 ≠ ph2.

Axiom  decenc :
      forall {m : ppt} {n n'},
        Dec [❴ m ❵_(Pkey [n]) ＾ (Rand [n']);  (Skey [n])] = m.

(*  *)
Axiom cca_2 : (CCA2 Len Enc Dec Pkey Skey Rand Error).



(* --------------------------------------------- *)
(*  *)
(* aka proposition 20 *)

Axiom CompHid : forall (t0 : list ppt -> list ppt) (t t1 t2 : ppt) (n1 n2 : nat),
    CompHid_prop t0 t t1 t2 n1 n2 Len Commitment Commitkey.

(*  *)
Axiom CompBind: forall (t1 t2 t3 t4: ppt), CompBind_prop t1 t2 t3 t4 Commitment.


(* --------------------------------------------- *)

(*  *)
Axiom Blindness: forall (z : list ppt) (m0 m1 t n0 n1 : ppt) (t0 t1 : list ppt -> ppt),
    Blindness_prop z m0 m1 t n0 n1 t0 t1 Blinding BlindRand Accept Unblinding ⫠.

(*  *)
Axiom UbNotUndefined: forall (t1 t n0 t2 : ppt),
   UbNotUndefined_prop t1 t n0 t2 Blinding BlindRand Accept Unblinding ⫠.




(* --------------------------------------------- *)
(*  *)
Axiom shufl_perm12: forall v1 v2 v3, shufl v1 v2 v3 = shufl v2 v1 v3.
Axiom shufl_perm13: forall v1 v2 v3, shufl v1 v2 v3 = shufl v3 v2 v1.
Axiom shufl_perm23: forall v1 v2 v3, shufl v1 v2 v3 = shufl v1 v3 v2.


(*  *)
Axiom KeyNEq: forall nc x : ppt, FreshTerm nc x -> [Comk (nc) ≟ x] ~ [FAlse].
(* Is this not derivable? *)



(*   *)
Axiom ComplLen: forall t, | compl t | = | t |.


(* Assumptions on length preservation *)

Axiom voteLen : (| vot0 |) = (| vot1 |).

Axiom NonceLen : forall n m , (| nonce n |) = (| nonce m |).

Axiom ComkLen :  forall n m , (| Comk (nonce n) |) = (| Comk (nonce m) |).
Axiom BrandLen :  forall n m , (| Brand (nonce n) |) = (| Brand (nonce m) |).


Axiom ubLen :
  forall x x' y y' t t1 , (| x |) = (| x' |) ->  (| y |) = (| y' |) -> (| ub x t y t1 |) = (| ub x' t y' t1 |).

Axiom comLen :
  forall x x' n m , (| x |) = (| x' |) ->  (| com x (Comk (nonce n)) |) =  (| com x' (Comk (nonce m)) |).


Axiom PairLen :
    forall (x x' y y': ppt) , (| x |) = (| x' |) ->  (| y |) = (| y' |) ->  (| Pair [x ; y ] |) = (| Pair [x' ; y' ] |).


Axiom TripleLen :
    forall (x x' y y' z z': ppt) , (| x |) = (| x' |) ->  (| y |) = (| y' |) ->  (| Triple [x ; y ; z] |) = (| Triple [x' ; y' ; z' ] |).
