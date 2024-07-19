Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef STB.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import ProofMode IProofMode.
Require Import Mem1.
Require Import sProp sWorld World SRF.
From stdpp Require Import coPset gmap namespaces.
Set Implicit Arguments.

Section RESOURCE.
  Context `{_W: CtxWD.t}.

  Global Instance singletonRA: URA.t := Auth.t (Excl.t unit)%ra.
  Context `{@GRA.inG singletonRA Γ}.

  Definition Ready: (@URA.car singletonRA) :=
    Auth.black ((Excl.just tt) : @URA.car (Excl.t unit)).

  Definition Ball: (@URA.car singletonRA) :=
    Auth.white ((Excl.just tt) : @URA.car (Excl.t unit)).

  Definition Fired: (@URA.car singletonRA) :=
    Auth.excl (Excl.just tt : @URA.car (Excl.t unit)) (Excl.just tt : @URA.car (Excl.t unit)).

  Lemma ReadyBall: Ready ⋅ Ball = Fired.
  Proof.
    ur. rewrite URA.unit_idl. ss.
  Qed.

  Lemma FiredReady: ~ URA.wf (Fired ⋅ Ready).
  Proof.
    ur. ss.
  Qed.

  Lemma FiredBall: ~ URA.wf (Fired ⋅ Ball).
  Proof.
    ur. ii. des. ur in H0. red in H0. des. ur in H0. des_ifs.
  Qed.

  Lemma BallReady_wf: URA.wf (Ball ⋅ Ready).
  Proof.
    ur. split.
    { eexists. rewrite ! URA.unit_id. ss. }
    { ur. ss. }
  Qed.
End RESOURCE.

Module SingletonRA.
  Class t
    `{_W: CtxWD.t}
    `{@GRA.inG singletonRA Γ}
    := SingletonRA: unit.

End SingletonRA.
