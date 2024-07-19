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

Require Import Singleton0 Singleton1 SingletonRA.

From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Set Implicit Arguments.

Section PRF.

  Context `{_S: SingletonRA.t}.

  Variable GlobalStb: Sk.t -> gname -> option fspec.

  Let Ist: Any.t -> Any.t -> iProp :=
        (fun st_src st_tgt =>
           ((⌜st_tgt = (1: Z)%Z↑⌝ ** OwnM (Ready))
              ∨ (⌜exists m: Z, m <> 1 /\ Any.downcast st_tgt = Some m⌝ ** OwnM (Fired)))%I).
  
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

  Theorem sim: HModPair.sim (Singleton1.Singleton GlobalStb) (Singleton0.Singleton) Ist.
  Proof.
    sim_init.
    - iIntros. iSplitR. auto. steps. iLeft. iFrame. auto.
    - unfold singleton_spec, cfunU, singletonA, singletonF, interp_sb_hp, HoareFun. s.
      steps. iDestruct "ASM" as "(W & [% B] & %)". subst.
      steps. force. force. iSplitL "W".
      { iFrame. eauto. }
      iDestruct "IST" as "[[% R]|[% F]]"; swap 1 2.
      { iExFalso.
        iCombine "F" "B" as "F".
        iOwnWf "F". exfalso. eapply FiredBall. ss. }
      subst. steps. force. steps.
      iCombine "R" "B" as "F".
      rewrite ReadyBall. iSplitL; eauto.
      iRight. iFrame. iPureIntro. exists 0. split; [nia|].
      rewrite Any.upcast_downcast. ss.
      Unshelve. auto.
   Qed.


End PRF.
