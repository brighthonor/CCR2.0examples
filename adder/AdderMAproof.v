(*** PROOF_MA ***)
Require Import AdderM AdderA HoareDef SimModSem SimModSemFacts.
Require Import Coqlib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem ModSemE Behavior.
Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import HTactics ProofMode IPM.
Require Import OpenDef.
Require Import STS STB Invariant.

Require Import IProofMode IRed ITactics.
Require Import sProp sWorld World SRF.
From stdpp Require Import coPset gmap namespaces.

Set Implicit Arguments.

Local Open Scope nat_scope.

Section PRF.

  Context `{_W: CtxWD.t}.

  Variable GlobalStbM: Sk.t -> gname -> option fspec.
  Variable GlobalStb: Sk.t -> gname -> option fspec.

  (******************************)
  Lemma isim_apc 
    I fls flt r g ps pt {R} RR st_src st_tgt k_src k_tgt stb_src stb_tgt
    (* (STBINCL: stb_pure_incl stb_tgt stb_src) *)
  :
    (I st_src st_tgt ∗ (∀st_src0 st_tgt0 vret, (I st_src0 st_tgt0) -∗ isim I fls flt r g RR true true (st_src0, k_src vret) (st_tgt0, k_tgt vret)))
  -∗
     @isim _ I fls flt r g R RR ps pt (st_src, interp_hEs_hAGEs stb_src ord_top (trigger hAPC) >>= k_src) (st_tgt, interp_hEs_hAGEs stb_tgt ord_top (trigger hAPC) >>= k_tgt).
  Proof. Admitted.
  
  Ltac apc := prep; iApply isim_apc; iSplitL "IST"; [eauto|iIntros "% % %"; iIntros "IST"].

  (******************************)

  Let Ist: Any.t -> Any.t -> iProp :=
        (fun st_src st_tgt =>
           (⌜st_src = tt↑ /\ st_tgt = (3: Z)%Z↑⌝)%I).
  
  Theorem sim: HModPair.sim (AdderA.Main GlobalStb) (AdderM.Main GlobalStbM) Ist.
  Proof.
    sim_init.
    - iIntros. iSplitL; auto. steps. eauto.
    - unfold cfunU, mainA, mainM, interp_sb_hp, HoareFun. s.
      steps. iDestruct "ASM" as "(W & % & %)"; subst.
      force. force. force. iSplitL "W".
      { instantiate (2 := mk_meta y1 y2 x). ss. eauto. }
      steps. apc. steps. force.
      iDestruct "IST" as "[% %]". subst. steps. force.
      iDestruct "GRT" as "(W & % & %)". subst. iSplitL "W".
      { iFrame. eauto. }
      steps. eauto.
   Qed.
  
End PRF.
