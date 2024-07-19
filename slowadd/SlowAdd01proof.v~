(*** PROOF ***)
Require Import HoareDef OpenDef STB SimModSem.
Require Import ITreelib.
Require Import Coqlib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior ModSemE.
Require Import Relation_Definitions.

Require Import HTactics ProofMode Invariant IPM.
Require Import sProp sWorld World SRF.
Require Import IProofMode ITactics IRed SimModSemFacts.
From stdpp Require Import coPset gmap namespaces.

Require Import SlowAdd0 SlowAdd1.

From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Set Implicit Arguments.

Section PRF.

  Context `{_W: CtxWD.t}.

  Variable GlobalStb: Sk.t -> gname -> option fspec.

  Hypothesis GlobalStb_plus: forall sk,
      GlobalStb sk "plus" = Some plus_spec.
  
  Hypothesis GlobalStb_minus: forall sk,
      GlobalStb sk "minus" = Some minus_spec.

  Hypothesis GlobalStb_add: forall sk,
      GlobalStb sk "add" = Some add_spec.


  Let Ist: Any.t -> Any.t -> iProp :=
        fun _ _ => emp%I.

  Lemma ord_0_lt_omega_Sm: forall n, (0 < Ord.omega + S n)%ord.
  Proof.
    intros.
    apply Ord.lt_trans with Ord.omega.
    apply Ord.omega_upperbound.
    eapply Ord.le_lt_lt.
    { eapply OrdArith.add_base_l. }
    { eapply OrdArith.lt_add_r. rewrite Ord.from_nat_S. eapply Ord.S_lt. }
  Qed.

  (***************************)
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

  Lemma hcall_clo
    I fls flt r g ps pt {R} RR st_src st_tgt k_src k_tgt
    fn varg_src varg_tgt o X (x: shelve__ X) (D: X -> ord) P Q
    (* PURE, ... *)
    (ORD: ord_lt (D x) o)
    (PURE: is_pure (D x))
  :
    (P x varg_src varg_tgt 
      ∗ I st_src st_tgt 
      ∗ (∀st_src0 st_tgt0 vret_src vret_tgt, 
             (Q x vret_src vret_tgt ∗ I st_src0 st_tgt0) 
          -∗ @isim _ I fls flt r g R RR true true (st_src0, k_src vret_src) (st_tgt0, k_tgt vret_tgt)))
  -∗  
    @isim _ I fls flt r g R RR ps pt (st_src, HoareCall true o (mk_fspec D P Q) fn varg_src >>= k_src) (st_tgt, trigger (Call fn varg_tgt) >>= k_tgt).
  Proof.
    iIntros "(P & IST & K)".
    unfold HoareCall. prep.
    force. instantiate (1:= x).
    force. instantiate (1:= varg_tgt).
    force. iSplitL "P"; [eauto|]. 
    call; [eauto|].
    steps. iApply "K". iFrame.
  Qed.



  (***************************)


  Theorem sim: HModPair.sim (SlowAdd1.Add GlobalStb) (SlowAdd0.Add) Ist.
  Proof.
    sim_init.
    - iIntros. iSplit; eauto. steps. eauto.
    - (* plusF *)
      unfold plus_spec, plusF, SlowAdd0.plusF, interp_sb_hp, cfunU, cfunN, HoareFun. s.
      steps. iDestruct "ASM" as "(W & % & %)". subst.
      steps.
      iApply APC_start_clo. steps. iApply APC_stop_clo.
      steps. force. steps. force. force.
      force. iSplitL "W".
      { iFrame. eauto. }
      steps. eauto.
    - (* minusF *)
      unfold minus_spec, minusF, SlowAdd0.minusF, interp_sb_hp, cfunU, cfunN, HoareFun. s.
      steps. iDestruct "ASM" as "(W & % & %)". subst.
      iApply APC_start_clo. steps. iApply APC_stop_clo.
      steps. force. steps. force. force. iSplitL "W".
      { iFrame. eauto. }
      steps. eauto.
    - (* addF *)
      unfold add_spec, addF, SlowAdd0.addF, interp_sb_hp, cfunU, cfunN, HoareFun, ccallU. s.
      steps. iDestruct "ASM" as "(W & % & %)". subst.
      steps.
      destruct x3.
      + (* add x 0 = x *)
        s. iApply APC_start_clo. steps. iApply APC_stop_clo.
        steps. force. steps. force. force.
        iSplitL "W". { iFrame. eauto. }
        steps. rewrite Z.add_0_r. eauto.
      + (* add x (S y) = S (add x y) *)
        s. iApply APC_start_clo.
        instantiate (1 := Ord.omega).
        steps. iApply APC_step_clo.
        { eapply GlobalStb_plus. }
        { instantiate (1:=10). eapply Ord.omega_upperbound. }

        unfold HoareCall. steps. force. force. force.
        instantiate (1 := mk_meta y1 y2 x2). ss.
        iSplitL "W"; [iSplitL "W"; eauto; iSplit; auto; iPureIntro; apply ord_0_lt_omega_Sm |].
        call; auto. steps.
        
        iDestruct "ASM" as "(W & % & %)". subst. steps.
        iApply APC_step_clo.
        { eapply GlobalStb_minus. }
        { instantiate (1:=9). apply OrdArith.lt_from_nat. nia. }

        unfold HoareCall. steps. force. force. force.
        instantiate (1 := mk_meta y1 y2 (S x3)). ss.
        iSplitL "W"; [iSplitL "W"; eauto; iSplit; auto; iPureIntro; apply ord_0_lt_omega_Sm |].
        call; auto. steps.
        
        iDestruct "ASM" as "(W & % & %)". subst. steps.
        iApply APC_step_clo.
        { eapply GlobalStb_add. }
        { instantiate (1 := 8). apply OrdArith.lt_from_nat. nia. }

        unfold HoareCall. steps. force. force. force.
        instantiate (1 := mk_meta y1 y2 (x2 + 1, x3, x1)). ss. iSplitL "W".
        { iSplitL "W"; [iFrame; eauto | iSplit; auto].
          iPureIntro. eapply OrdArith.lt_add_r. apply OrdArith.lt_from_nat. ss. }
        steps.
        (* to match arguments *)
        replace (Z.pos (Pos.of_succ_nat x3) - 1)%Z with (Z.of_nat x3)%Z by nia.
        replace (x2 + 1)%Z with (Z.of_nat (x2 + 1))%Z by nia.
        call; auto. steps.
        
        iApply APC_stop_clo.
        iDestruct "ASM" as "(W & % & %)". subst. steps.
        force. steps. force. force.
        iFrame. iSplitR "IST"; eauto.
        steps. iFrame. iPureIntro.
        replace (x2 + Z.pos (Pos.of_succ_nat x3))%Z with ((Z.of_nat (x2 + 1)%nat) + x3)%Z by nia.
        ss.
        (* fin *)
        Unshelve. all: exact 0.  
  Qed.
End PRF.
