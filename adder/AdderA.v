(*** SPC ***)
Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef STB IPM.
Require Import ProofMode IProofMode.

Require Import sProp sWorld World SRF.
From stdpp Require Import coPset gmap namespaces.

Set Implicit Arguments.

Section MID.

  Context `{_W: CtxWD.t}.

  (*
    *** Example in pseudo-code style ***

        def main(): int :=
            return 7;
   *)
  
  Definition mainA: list val -> itree hEs val :=
    fun args =>
      _ <- (pargs [] args)?;;
      ;;;
      Ret (Vint 7).

  
  Definition main_spec: fspec :=
    mk_fspec_inv 0
      (fun _ _ => mk_simple (X:=unit)
                 (fun _ =>
                    (ord_top,
                      (fun varg => (⌜varg = ([]: list val)↑⌝)%I),
                      (fun vret => (⌜vret = (Vint 7)↑⌝)%I)
      ))).
  
  Definition MainSbtbA: list (string * fspecbody) :=
    [("main", mk_specbody main_spec (cfunU mainA))].

  Definition AMainSem: SModSem.t :=
    {|
      SModSem.fnsems := MainSbtbA;
      SModSem.initial_cond := emp;
      SModSem.initial_st := Ret tt↑;
    |}.

  Definition AMain: SMod.t :=
    {|
      SMod.get_modsem := fun _ => AMainSem;
      SMod.sk := [("main", Gfun↑)];
    |}.

  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Definition Main: HMod.t := (SMod.to_hmod GlobalStb AMain).

End MID.
