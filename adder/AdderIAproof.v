Require Import HoareDef AdderI AdderM AdderA SimModSem AdderIMproof AdderMAproof.
Require Import Coqlib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Require Import ProofMode STB Invariant.
Require Import SimModSemFacts IProofMode IRed ITactics.

Require Import sProp sWorld World SRF.
From stdpp Require Import coPset gmap namespaces.

Set Implicit Arguments.

Section PRF.
  Context `{_W: CtxWD.t}.

  Variable GlobalStb: Sk.t -> gname -> option fspec.

  Let Ist: Any.t -> Any.t -> iProp :=
        (fun st_src st_tgt =>
           (⌜st_src = tt↑ /\ st_tgt = tt↑⌝)%I).

  Theorem sim: HModPair.sim (AdderA.Main GlobalStb) AdderI.Main Ist.
  Proof.
    (* Not implemented yet *)
  Admitted.
End PRF.