(* En este archivo se demuestra que la ejecución de
*  la acción grantP preserva los invariantes del sistema *)
Require Export Exec.
Require Export Implementacion.
Require Export AuxFunsCorrect.
Require Import Classical.
Require Import Estado.
Require Import DefBasicas.
Require Import Semantica.
Require Import Operaciones.
Require Import ErrorManagement.
Require Import Maps.
Require Import Tacticas.
Require Import MyList.
Require Import ListAuxFuns.
Require Import ValidStateLemmas.
Require Import SameEnvLemmas.
Require Import Semantica.

Section GrantPInv.

    
Lemma GrantPIsInvariant : forall (s s':System) (sValid:validstate s) (ic:iCmp) (cp:CProvider) (a:idApp) (u:uri) (pt:PType) , pre_grantP ic cp a u pt s -> post_grantP ic cp a u pt s s' -> validstate s'.
Proof.
    intros.
    unfold validstate.
    unfold pre_grantP in H.
    unfold post_grantP in H0.
    destruct_conj H0.
    
    unfold allCmpDifferent.
    split.
    intros.
    
    
    apply (inAppS'InAppS a1 s) in H11;auto.
    apply (inAppS'InAppS a2 s) in H13;auto.
    apply (inAppSameCmpId s sValid c1 c2 a1 a2);auto.
    
    
    unfold notRepeatedCmps.
    split.
    intros.
    apply (inAppS'InAppS a1 s) in H11;auto.
    apply (inAppS'InAppS a2 s) in H13;auto.
    apply (inAppSameCmp s sValid c a1 a2);auto.
    
    
    unfold notCPrunning.
    split.
    rewrite <-H8.
    destructVS sValid.
    auto.
    
    
    split.
    apply (delTmpRunS' s);auto.
    
    split.
    apply (cmpRunAppInsS' s);auto.
    
    split.
    apply (resContAppInstS' s);auto.
    
    split.
    apply (consistencyUnchanged s);auto.
    
    unfold notDupApp.
    split.
    rewrite <- H4.
    rewrite<-H5.
    destructVS sValid.
    auto.
    
    unfold notDupSysApp.
    split.
    rewrite <-H4.
    destructVS sValid.
    auto.
    
    
    split.
    apply (notDupPermS' s);auto.
    
    unfold allMapsCorrect.
    split.
    rewrite <-H4, <-H6, <-H7, <- H8, <-H9, <-H10.
    repeat (split;auto; try mapcorrect sValid).
    
    split.
    apply (grantedPermsExistS' s);auto.
    split.

    unfold noDupSentIntents.
    rewrite<- H12.
    destructVS sValid.
    auto.

    apply (individualInstanceOfGroupedPermS' s); auto.
Qed.



End GrantPInv.

