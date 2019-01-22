(* SYNTAX TEST "Coq.tmLanguage" *)

Require Import String.
(* ^ keyword *)
(*        ^ keyword *)

Require Import List.
(* ^ keyword *)
(*        ^ keyword *)

Import ListNotations.
(* ^ keyword *)

Open Scope string_scope.
(* ^ keyword *)
(*     ^ keyword *)

(* Now we can use "strings" *)
(*  ^ comment.block *)
(*                    ^ - string *)

(*(**)*) (* weird little nested comment *)
(*  ^ comment.block *)
(*      ^ - comment.block *)
(*          ^ comment.block *)

Ltac inv H := inversion H; clear H; subst.
(* ^ keyword *)
(*    ^ entity.name *)
(*               ^ support.function *)
(*                           ^ support.function *)
(*                                    ^ support.function *)

Ltac breakbool := repeat match goal with
(* ^ keyword *)
(*       ^ entity.name *)
(*                        ^ keyword *)
(*                                    ^ keyword *)
  | [ H : _ /\ _ |- _ ] => destruct H
(*          ^ keyword *)
(*               ^ keyword *)
(*                           ^ support.function *)
  | [ H : _ \/ _ |- _ ] => inv H
end.
(* <- keyword *)

Definition isZero (n : nat) : bool :=
(* ^ keyword *)
(*           ^ entity.name *)
(*                                  ^ keyword *)
  match n with
(*  ^ keyword *)
(*          ^ keyword *)
  | 0 => true
(*  ^ constant.numeric *)
(*        ^ constant *)
  | _ => false
(*  ^ constant *)
(*        ^ constant *)
  end.
(* ^ keyword *)

Theorem foo:
(* ^ keyword *)
(*       ^ entity.name *)
  forall a b,
(*  ^ support.type *)
    a /\ b ->
(*    ^ keyword *)
(*         ^ keyword *)
    a.
Proof.
(* ^^ keyword *)
  intros.
(* ^ support.function *)
  breakbool.
(* ^ - support.function *)
  assumption.
(* ^ support.function *)
Qed.

Inductive MyType :=
  | Case1
(*      ^ - constant *)
  | CaseFalse
(*        ^ - constant *)
  .
