(*** IMP ***)
Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef STB IPM.

Require Import sProp sWorld World SRF.
From stdpp Require Import coPset gmap namespaces.

Set Implicit Arguments.

Section IMP.

  Context `{_W: CtxWD.t}.

  (*
    *** Example in pseudo-code style ***

        def main(): int :=
            return slow_add(3, 4);
   *)

  Definition mainF
    : list val -> itree hAGEs val :=
    fun args =>
      _ <- (pargs [] args)?;;
      `a: val <- ccallU "add" ([Vint 3; Vint 4]);;
      Ret a.

  Definition HMainSem: HModSem.t :=
    {|
      HModSem.fnsems := [("main", cfunU mainF)];
      HModSem.initial_st := Ret tt↑;
      HModSem.initial_cond := emp;
    |}.

  Definition Main: HMod.t :=
    {|
      HMod.get_modsem := fun _ => HMainSem;
      HMod.sk := [("main", Gfun↑)];
    |}.

End IMP.
