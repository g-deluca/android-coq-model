(* En este archivo se demuestra la propiedad que postula que 
*  si en un estado inicial válido se le revoca correctamente un permiso p
*  a una aplicación a, mientras la aplicación no sea desinstalada ni el permiso
*  reotorgado, la aplicación no contará con él *)
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
Require Import RuntimePermissions.
Require Import EqTheorems.
Require Import Trace.
Require Export PropertiesAuxFuns.
Require Export IfPermThenGranted.

Section RvkAndNotGrant.



    Theorem revokeAndNotGrantProof : forall
    (initState sndState lastState:System)
    (initStateValid:validstate initState)
    (a:idApp)
    (p:Perm)
    (pDangerous:pl p=dangerous)
    (pUngrouped : maybeGrp p = None)
    (pNotSelfDefined : ~exists lPerm : list Perm, map_apply idApp_eq (defPerms (environment initState)) a = Value idApp lPerm /\ In p lPerm) 
    (sndStateStep: sndState = system (step initState (revoke p a)))
    (revokeWasOk : response (step initState (revoke p a))=ok)
    (l:list Action)
    (aIsTheSame :~In (uninstall a) l)
    (notRegranted : ~In (grant p a) l)
    (fromSndToLast : last (trace sndState l) sndState = lastState),
    ~appHasPermission a p lastState.
Proof.
    intros.
    unfold not;intros.
    apply notRegranted.
    rewrite sndStateStep in *.
    clear sndStateStep.
    case_eq (revoke_pre p a initState);intros.
    simpl in *.
    unfold revoke_safe in revokeWasOk.
    rewrite H0 in revokeWasOk.
    simpl in revokeWasOk.
    inversion revokeWasOk.
    assert (exists x, map_apply idApp_eq (perms (state initState)) a= Value idApp x) as hasPerms.
    unfold revoke_pre in H0.
    unfold grantedPermsForApp in H0.
    case_eq (map_apply idApp_eq (perms (state initState)) a);intros;rewrite H1 in H0.
    exists l0;auto.
    assert (negb (InBool Perm Perm_eq p nil)=true).
    rewrite negb_true_iff.
    unfold InBool.
    auto.
    rewrite H2 in H0.
    inversion H0.
    destruct hasPerms as [ps].
    apply (ifPermThenGrantedProof (system (step initState (revoke p a))) lastState);auto.
    apply stepIsInvariant;auto.
    simpl in *.
    unfold revoke_safe in *.
    rewrite H0 in *.
    simpl.
    apply (ifPermsThenInApp initState initStateValid a ps);auto.
    unfold appHasPermission.
    unfold not;intros.
    destruct H2.
    destruct H2.
    destruct H2.
    simpl in H2.
    unfold revoke_safe in H2.
    rewrite H0 in H2.
    simpl in H2.
    unfold revokePermission in H2.
    rewrite H1 in H2.
    rewrite <-addAndApply in H2.
    inversion H2.
    rewrite <- H5 in H3.
    rewrite <-removeSthElse in H3.
    destruct H3.
    destruct H3.
    auto.
    destruct H2.
    destruct H3.
    destruct H3.
    destruct H4.
    simpl in H4.
    unfold revoke_safe in H4.
    rewrite H0 in H4.
    simpl in H4.
    contradiction.
    rewrite pDangerous, pUngrouped in H4.
    destruct H4.
    inversion H4.
    destruct H4.
    destruct H4.
    destruct H5.
    destruct H5.
    destruct H5.
    inversion H5.
    destruct H4.
    destruct H4.
    destruct H4;inversion H4.
    destruct H4;inversion H4.
Qed.

End RvkAndNotGrant.

