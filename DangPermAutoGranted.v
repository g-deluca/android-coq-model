Require Import DefBasicas.
Require Import Estado.
Require Import Operaciones.
Require Import Semantica.
Require Import Exec.
Require Import ErrorManagement.
Require Import Tacticas.
Require Import ValidityInvariance.
Require Import RuntimePermissions.

Theorem DangerousPermissionAutoGrantedProof : forall
  (s s': System)
  (a: idApp)
  (m: Manifest)
  (c: Cert)
  (resources: list res)
  (pDang pNorm : Perm)
  (g: idGrp),
  permExists pDang s'->
  pl pDang = dangerous ->
  pl pNorm = normal ->
  In pNorm (use m) ->
  In pDang (use m) ->
  maybeGrp pNorm = Some g ->
  maybeGrp pDang = Some g ->
  exec s (install a m c resources) s' ok -> 
  pre_grantAuto pDang a s'.
Proof.
    intros s s' a m c resources pDang pNorm g 
      dangExists pDangIsDangerous pNormIsNormal useNorm useDang pNormGrouped pDangGrouped execInstall.
    unfold exec in execInstall. destruct execInstall.
    destruct H0.
 -  destruct_conj H0. clear H1.
    unfold pre_grantAuto.
    repeat split; auto.
 +  exists m. split; auto.
    unfold isManifestOfApp.
    simpl in H3. unfold post_install in H3.
    destruct H3 as [_ [_ [manifests _]]].
    unfold addManifest in manifests.
    destruct_conj manifests.
    left. auto.
 +  intro.
    simpl in H3. unfold post_install in H3.
    destruct_conj H3.
    unfold initializePermLists in H9.
    destruct_conj H9.
    destruct H1 as [lPerm H1].
    destruct H1.
    rewrite H16 in H1.
    inversion H1. rewrite <- H20 in H17.
    inversion H17.
 +  simpl in H3. unfold post_install in H3.  
    destruct H3 as [_ [H3 _]].
    unfold initializeGroups in H3.
    destruct_conj H3.
    destruct H2 as [lGrp [H6 H7]].
    exists g, lGrp.
    repeat split; auto.
    apply (H7 pNorm).
    repeat split;auto.
-   destruct H0 as [ec [H0 _]].
    inversion H0.
Qed.