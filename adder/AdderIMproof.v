(*** PROOF_IM ***)
Require Import AdderI AdderM SlowAdd1 HoareDef SimModSem SimModSemFacts.
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
Require Import STB.

Require Import IProofMode IRed ITactics.

Require Import sProp sWorld World SRF.
From stdpp Require Import coPset gmap namespaces.

Set Implicit Arguments.

Local Open Scope nat_scope.

Section PRF.

  Context `{_W: CtxWD.t}.

  Variable GlobalStb: Sk.t -> gname -> option fspec.
  
  Hypothesis GlobalStb_add: forall sk,
      GlobalStb sk "add" = Some add_spec.

  (***********************************)
  Lemma APC_start_clo
    I fls flt r g ps pt {R} RR st_src k_src sti_tgt  
    at_most o stb 
  :
    @isim _ I fls flt r g R RR true pt (st_src, _APC stb at_most o >>= (fun x => tau;; Ret x) >>= k_src) sti_tgt
  -∗  
    @isim _ I fls flt r g R RR ps pt (st_src, interp_hEs_hAGEs stb o (trigger hAPC) >>= k_src) sti_tgt.
  Proof.
    unfold interp_hEs_hAGEs. rewrite! interp_trigger. grind.
    destruct sti_tgt. unfold HoareAPC.
    iIntros "K". 
    force. instantiate (1:= at_most).
    iApply "K".
  Qed.

  Lemma APC_stop_clo
    I fls flt r g ps pt {R} RR st_src k_src sti_tgt  
    at_most o stb
  :
    @isim _ I fls flt r g R RR true pt (st_src, k_src tt) sti_tgt
  -∗  
    @isim _ I fls flt r g R RR ps pt (st_src, _APC stb at_most o >>= (fun x => (tau;; Ret x) >>= k_src)) sti_tgt.
  Proof.
    destruct sti_tgt.
    iIntros "K".
    rewrite unfold_APC. 
    force. instantiate (1:= true). steps. eauto.
  Qed.
  
  Lemma APC_step_clo
    I fls flt r g ps pt {R} RR st_src k_src sti_tgt  
    at_most o stb next fn vargs fsp
    (SPEC: stb fn = Some fsp)
    (NEXT: (next < at_most)%ord)
  :
    @isim _ I fls flt r g R RR true pt (st_src, HoareCall true o fsp fn vargs >>= (fun _ => _APC stb next o) >>= (fun x => tau;; Ret x) >>= k_src) sti_tgt
  -∗  
    @isim _ I fls flt r g R RR ps pt (st_src, _APC stb at_most o >>= (fun x => (tau;; Ret x) >>= k_src)) sti_tgt.
  Proof.
    destruct sti_tgt.
    iIntros "K". prep.
    iEval (rewrite unfold_APC).
    force. instantiate (1:= false). steps.
    force. instantiate (1:= next). unfold guarantee.
    force. steps.
    force. instantiate (1:= (fn, vargs)). steps.
    rewrite SPEC. steps. grind.
    Unshelve. eauto.
  Qed.

  (****************************************)
  
  Let Ist: Any.t -> Any.t -> iProp :=
        (fun st_src st_tgt =>
           (⌜st_tgt = tt↑ /\ st_src = (3: Z)%Z↑⌝)%I).

  Theorem sim: HModPair.sim (AdderM.Main GlobalStb) (AdderI.Main) Ist.
  Proof.
    sim_init.
    - iIntros. iSplitL; auto. steps. eauto.
    - unfold main_spec, cfunU, mainM, mainF, interp_sb_hp, HoareFun, ccallU. s.
      steps. iDestruct "ASM" as "(W & % & %)"; subst.
      steps.
      iApply APC_start_clo. steps.
      instantiate (1 := 1).
      iApply APC_step_clo.
      { eapply GlobalStb_add. } { instantiate (1 := 0). apply OrdArith.lt_from_nat. ss. }
      steps. unfold HoareCall.
      force. force. force. iSplitL "W".
      { instantiate (1 := mk_meta y1 y2 (3, 4, _)). ss. iFrame; eauto. }
      call; auto. steps.
      iDestruct "ASM" as "(W & % & %)"; subst. steps.
      iApply APC_stop_clo.
      steps. force. force. 
      iDestruct "IST" as "[% %]"; subst.
      rewrite Any.upcast_downcast in G1. inv G1.
      iSplitL "W".
      { iFrame; eauto. }
      steps. eauto.
      Unshelve. exact (fun _ => 0).
  Qed.
  
End PRF.
