(*** IMP ***)

Require Import Coqlib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import Relation_Definitions Relation_Operators RelationPairs.
Require Import sProp sWorld World SRF.
Require Import ProofMode IProofMode ITactics.

Set Implicit Arguments.

Section IMP.

  Context `{_W: CtxWD.t}.
  
  (*
    *** Exmaple in pseudo-code style ***

        def plus(n: int): int :=
            return n + 1;

        def minus(n: int): int :=
            return n - 1;

        def add(n: int, m: int): int :=
            if (m =? 0)
            then return n;
            else return add(plus(n), minus(m));
   *)

  Definition plusF
    : list val -> itree hAGEs val :=
    fun args =>
      n <- (pargs [Tint] args)?;;
            Ret (Vint (n + 1)).

  Definition minusF
    : list val -> itree hAGEs val :=
    fun args =>
      n <- (pargs [Tint] args)?;;
            Ret (Vint (n - 1)).
  

  Definition addF
    : list val -> itree hAGEs val :=
    fun args =>
      '(n, m) <- (pargs [Tint; Tint] args)?;;
      if (m <=? 0)%Z
      then Ret (Vint n)
      else `r1: val <- ccallU "plus" [Vint n];;
           `r2: val <- ccallU "minus" [Vint m];;
           `rr: val <- ccallU "add" [r1; r2];;
           Ret rr.
  
  Definition AddSem: HModSem.t := {|
    HModSem.fnsems := [("plus", cfunU plusF); ("minus", cfunU minusF); ("add", cfunU addF)];
    HModSem.initial_st := Ret tt↑;
    HModSem.initial_cond := emp                                        
  |}
  .

  Definition Add: HMod.t := {|
    HMod.get_modsem := fun _ => AddSem;
    HMod.sk := [("plus", Gfun↑); ("minus", Gfun↑); ("add", Gfun↑)];
  |}
  .
  
End IMP.
