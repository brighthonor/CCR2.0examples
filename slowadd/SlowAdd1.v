(*** SPC ***)
Require Import Coqlib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef OpenDef.
Require Import ProofMode.
Require Import IProofMode ITactics.
Require Import STB.
Require Import sProp sWorld World SRF.

Require Import SlowAdd0.

Set Implicit Arguments.

Section SPC.
  Context `{_W: CtxWD.t}.

  Definition plus_spec: fspec :=
    mk_fspec_inv 0
    (fun _ _ => mk_simple (X:=nat)
               (fun n => (
                        (ord_pure 0),
                        (fun varg => (⌜varg = [Vint n]↑⌝)%I),
                        (fun vret => (⌜vret = (Vint (n + 1))↑⌝)%I)
               ))).

  Definition minus_spec: fspec :=
    mk_fspec_inv 0
    (fun _ _ => mk_simple (X:=nat)
               (fun n => (
                        (ord_pure 0),
                        (fun varg => (⌜varg = [Vint n]↑⌝)%I),
                        (fun vret => (⌜vret = (Vint (n - 1))↑⌝)%I)
               ))).

  Definition add_spec: fspec :=
    mk_fspec_inv 0
    (fun _ _ => mk_simple (X:=nat*nat*(Z*Z->Z))
               (fun '(n, m, f_spec) => 
                  ((ord_pure (Ord.omega + m)%ord),
                    (fun varg =>
                       (⌜varg = ([Vint (Z.of_nat n); Vint (Z.of_nat m)]: list val)↑⌝)%I),
                    (fun vret => (⌜vret = (Vint (n + m))↑⌝)%I)
    ))).

  Definition plusF
    : list val -> itree hEs val :=
    fun args =>
      n <- (pargs [Tint] args)?;;
            Ret (Vint (n + 1)).

  Definition minusF
    : list val -> itree hEs val :=
    fun args =>
      n <- (pargs [Tint] args)?;;
            Ret (Vint (n - 1)).
  

  Definition addF
    : list val -> itree hEs val :=
    fun args =>
      '(n, m) <- (pargs [Tint; Tint] args)?;;
                  if (m <=? 0)%Z
                  then Ret (Vint n)
                  else `r1: val <- ccallU "plus" [Vint n];;
                            `r2: val <- ccallU "minus" [Vint m];;
                                 `rr: val <- ccallU "add" [r1; r2];;
                                      Ret rr.

  
  Definition AddSbtb: list (gname * fspecbody) :=
    [("plus", mk_specbody plus_spec (cfunU plusF));
     ("minus", mk_specbody minus_spec (cfunU minusF));
     ("add", mk_specbody add_spec (cfunU addF))].

  Definition SAddSem: SModSem.t :=
    {|
      SModSem.fnsems := AddSbtb;
      SModSem.initial_cond := emp;
      SModSem.initial_st := Ret tt↑;
    |}.

  Definition SAdd: SMod.t :=
    {|
      SMod.get_modsem := fun _ => SAddSem;
      SMod.sk := [("plus", Gfun↑); ("minus", Gfun↑); ("add", Gfun↑)];
    |}
  .

  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Definition Add: HMod.t := (SMod.to_hmod GlobalStb) SAdd.

End SPC.