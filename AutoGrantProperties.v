Require Export Exec.
Require Import Estado.
Require Import DefBasicas.
Require Import Semantica.
Require Import Operaciones.
Require Import ErrorManagement.
Require Import Tacticas.
Require Import Maps.
Require Import Trace.


Section AutoGrantProperties.

(*
 * Este teorema establece que el sistema no puede otorgar automáticamente un permiso (peligroso) 
 * agrupado si el grupo del mismo no ha sido previamente otorgado a través de un grant de usuario.
 *)
Theorem cannotAutoGrantWithoutGroup :
  forall (s s': System) (p: Perm) (g: idGrp) (a: idApp),
    pl p = dangerous ->
    maybeGrp p = Some g ->
    ~ (exists (lGroup: list idGrp),
      map_apply idApp_eq (grantedPermGroups (state s)) a = Value idApp lGroup /\ In g lGroup) ->
    ~ exec s (grantAuto p a) s' ok.
Proof.
  intros s s' p g a dangerousPerm groupedPerm notInGrantedGroups.
  unfold not; intro execGrantAuto.
  unfold exec in execGrantAuto.
  destruct execGrantAuto as [_ [ok | notOk]].
- destruct ok as [_ [preGrantAuto _]].
  unfold pre, pre_grantAuto in preGrantAuto.
  destruct preGrantAuto as [_ [_ [_ [_ existsPermGroup]]]].
  destruct existsPermGroup as [g' [lGroup H]].
  destruct H as [groupedPerm' [groupListOfA gInList]].
  rewrite groupedPerm in groupedPerm'.
  inversion groupedPerm' as [gEquals].
  rewrite <- gEquals in gInList.
  destruct notInGrantedGroups.
  exists lGroup. auto.
- destruct notOk as [ec [absurd _]].
  inversion absurd.
Qed.



End AutoGrantProperties.