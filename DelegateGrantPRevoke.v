(* En este archivo se demuestra la propiedad que postula que 
*  en todo estado válido, si se le otorga correctamente un permiso p
*  a una aplicación a que tiene uno de sus componentes ejecutándose 
*  con identificador ic; quien luego delega un permiso de lectura 
*  a una aplicación a' sobre un uri de un contentProvider de lectura 
*  protegida por p, y más tarde se le quita el permiso p a a, 
*  posteriormente si una instancia en ejecución de un componente de
*  a' intenta leer dicho uri de cp, podrá hacerlo correctamente *)
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

Section DelGrantPRevoke.

    Theorem delegateGrantPRevokeProof : forall 
    (s:System)
    (sValid:validstate s)
    (p:Perm)
    (a a':idApp)
    (pGrantable : response (step s (grant p a)) = ok)
    (ic ic': iCmp)
    (c c':Cmp)
    (cIsA : getAppFromCmp c s = a)
    (c'IsA' : getAppFromCmp c' s = a')
    (icIsC : map_apply iCmp_eq (running (state s)) ic = Value iCmp c)
    (ic'IsC' : map_apply iCmp_eq (running (state s)) ic' = Value iCmp c')
    (u:uri)
    (cp:CProvider)
    (uGrantable : canGrant cp u s)
    (uInCp : existsRes cp u s)
    (expCCP : expC cp = Some true)
    (cpReadProtectedByP : readE cp = Some p),
    let opsResult := trace s (grant p a:: grantP ic cp a' u Read:: revoke p a::nil) in
    response (step (last opsResult s) (read ic' cp u))=ok.
Proof.
    intros.
    unfold step.
    unfold opsResult.
    clear opsResult.
    unfold trace.
    unfold last.
    remember (system (step (system (step (system (step s (grant p a))) (grantP ic cp a' u Read))) (revoke p a))) as lastSys.
    assert (validstate lastSys) as lastValid.
    rewrite HeqlastSys.
    repeat apply stepIsInvariant.
    auto.
    assert (environment s = environment lastSys).
    rewrite HeqlastSys.
    apply revokePreservesEnv.
    apply grantPPreservesEnv.
    apply grantPreservesEnv.
    auto.
    assert (inApp c a s) as cInA.
    apply ifRunningThenInApp in icIsC;auto.
    destruct icIsC.
    assert (equis:=H0).
    apply inAppThenGetAppFromCmp in H0;auto.
    rewrite H0 in cIsA.
    rewrite <-cIsA.
    auto.
    assert (inApp c' a' s) as c'InA'.
    apply ifRunningThenInApp in ic'IsC';auto.
    destruct ic'IsC'.
    assert (equis:=H0).
    apply inAppThenGetAppFromCmp in H0;auto.
    rewrite H0 in c'IsA'.
    rewrite <-c'IsA'.
    auto.
    
    assert ( read_pre ic' cp u (system (step (system (step (system (step s (grant p a))) (grantP ic cp a' u Read))) (revoke p a)))=None).
    unfold read_pre.
    assert (negb (existsResBool cp u (system (step (system (step (system (step s (grant p a))) (grantP ic cp a' u Read))) (revoke p a))))=false).
    rewrite negb_false_iff.
    assert (existsRes cp u (system (step (system (step (system (step s (grant p a))) (grantP ic cp a' u Read))) (revoke p a)))).
    unfold existsRes.
    destruct uInCp.
    exists x.
    destruct H0.
    split.
    rewrite <-HeqlastSys.
    apply (inAppS'InAppS x lastSys s);auto.
    destruct H1.
    destruct H1.
    exists x0.
    split.
    auto.
    destruct H2.
    exists x1.
    assert (resCont (state s) = resCont (state (system (step (system (step (system (step s (grant p a))) (grantP ic cp a' u Read))) (revoke p a))))).
    apply revokePreservesResCont.
    apply grantPPreservesResCont.
    apply grantPreservesResCont.
    auto.
    rewrite <-H3.
    auto.
    apply existsRes_iff;auto.
    rewrite HeqlastSys in lastValid;auto.
    rewrite H0.
    assert (running (state s) = running (state (system (step (system (step (system (step s (grant p a))) (grantP ic cp a' u Read))) (revoke p a))))).
    apply revokePreservesRunning.
    apply grantPPreservesRunning.
    apply grantPreservesRunning.
    auto.
    rewrite <-H1.
    rewrite ic'IsC'.
    assert (delPermsBool c' cp u Read (system (step (system (step (system (step s (grant p a))) (grantP ic cp a' u Read))) (revoke p a)))=true).
    assert (delPerms c' cp u Read (system (step (system (step (system (step s (grant p a))) (grantP ic cp a' u Read))) (revoke p a)))).
    unfold delPerms.
    exists a'.
    split.
    rewrite<-HeqlastSys.
    apply (inAppS'InAppS a' lastSys s);auto.
    right.
    assert ( delPPerms (state (system (step (system (step (system (step s (grant p a))) (grantP ic cp a' u Read))) (revoke p a)))) = delPPerms (state (system (step (system (step s (grant p a))) (grantP ic cp a' u Read))))).
    symmetry.
    apply revokePreservesDelPPerms.
    auto.
    rewrite H2.
    unfold step.
    unfold grantP_safe.
    assert (grantP_pre ic cp a' u Read (system (grant_safe p a s))=None).
    unfold grantP_pre.
    assert (negb (canGrantBool cp u (system (grant_safe p a s)))=false).
    rewrite negb_false_iff.
    assert (canGrant cp u (system (grant_safe p a s))).
    unfold canGrant.
    destruct uGrantable.
    destruct H3.
    exists x.
    split;auto.
    apply (inAppS'InAppS x (system (grant_safe p a s)) s);auto.
    symmetry.
    apply grantPreservesEnv.
    auto.
    apply (canGrantCorrect);auto.
    assert (grant_safe p a s=step s (grant p a)).
    auto.
    rewrite H4.
    apply stepIsInvariant;auto.
    rewrite H3.
    assert (negb (existsResBool cp u (system (grant_safe p a s)))=false).
    rewrite negb_false_iff.
    apply existsRes_iff.
    assert (grant_safe p a s=step s (grant p a)).
    auto.
    rewrite H4.
    apply stepIsInvariant;auto.
    assert (grant_safe p a s=step s (grant p a)).
    auto.
    rewrite H4.
    apply (existsResS'ExistsResS s (system (grant_safe p a s))).
    apply grantPreservesResCont;auto.
    apply grantPreservesEnv;auto.
    auto.
    rewrite H4.
    assert (negb (isAppInstalledBool a' (system (grant_safe p a s)))=false).
    rewrite negb_false_iff.
    apply isAppInstalled_iff.
    assert (validstate (system (grant_safe p a s))).
    assert (grant_safe p a s=step s (grant p a)).
    auto.
    rewrite H5.
    apply stepIsInvariant;auto.
    apply (ifInAppThenIsAppInstalled (system (grant_safe p a s)) H5 c').
    apply (inAppS'InAppS a' (system (grant_safe p a s)) s);auto.
    symmetry.
    apply grantPreservesEnv.
    auto.
    rewrite H5.
    assert (running (state s) = running (state (system (grant_safe p a s)))).
    apply grantPreservesRunning.
    auto.
    rewrite<- H6.
    rewrite icIsC.
    assert (canReadBool c cp (system (grant_safe p a s))=true).
    assert (canRead c cp (system (grant_safe p a s))).
    unfold canRead.
    unfold canDoThis.
    exists a.
    destruct uInCp.
    exists x.
    assert (inApp c a s).
    auto.
    split.
    apply (inAppS'InAppS a (system (grant_safe p a s)) s);auto.
    symmetry.
    apply grantPreservesEnv.
    auto.
    
    
    destruct H7.
    destruct H7.
    destruct H7.
    exists x0.
    split.
    apply (isMfstOfAppSS' x x0 s (system (grant_safe p a s))).
    apply grantPreservesEnv.
    auto.
    auto.
    split;auto.
    left.
    split.
    auto.
    rewrite cpReadProtectedByP.
    intros.
    destruct H11.
    inversion H11.
    rewrite <- H13.
    unfold grant_safe.
    case_eq (grant_pre p a s);intros.
    simpl in pGrantable.
    unfold grant_safe in pGrantable.
    rewrite H12 in pGrantable.
    simpl in pGrantable.
    inversion pGrantable.
    simpl.
    unfold appHasPermission.
    left.
    simpl.
    unfold grantPermission.
    unfold grant_pre in H12.
    assert (In p (permsInUse a s)).
    assert (InBool Perm Perm_eq p (permsInUse a s)=true).
    rewrite <-not_false_iff_true.
    unfold not;intros.
    rewrite H14 in H12.
    simpl in H12.
    inversion H12.
    unfold InBool in H14.
    rewrite existsb_exists in H14.
    destruct H14.
    destruct H14.
    destruct Perm_eq in H15.
    rewrite e.
    auto.
    inversion H15.
    unfold permsInUse in H14.


    destruct H8.
    destruct H8.
    assert (In a (apps (state s)) \/ (exists sysapp:SysImgApp, In sysapp (systemImage (environment s)) /\ idSI sysapp = a)).
    destruct H8.
    left.
    apply ifManifestThenInApps with (m:=x1);auto.
    right.
    destruct H8.
    destruct_conj H8.
    exists x2;auto.
    apply ifInAppsOrSysAppThenPerms in H16;auto.
    destruct H16.
    exists (p::x2).
    rewrite H16.
    split.
    rewrite (addAndApply idApp_eq a (p::x2) (perms (state s)));auto.
    apply in_eq.
    
    
    
    destruct H11.
    destruct H11.
    inversion H11.
    destruct H11.
    inversion H11.
    apply canDoThisBoolCorrect;auto.
    assert (validstate (system (grant_safe p a s))).
    assert (grant_safe p a s=step s (grant p a)).
    auto.
    rewrite H8.
    apply stepIsInvariant;auto.
    auto.
    rewrite H7.
    simpl.
    auto.
    rewrite H3.
    simpl.
    unfold addDelPPerm.
    destruct ( map_apply delppermsdomeq (delPPerms (state (system (grant_safe p a s)))) (a', cp, u)).
    unfold ptplus.
    destruct p0.
    right.
    rewrite<-addAndApply;auto.
    left.
    rewrite<-addAndApply;auto.
    left.
    rewrite<-addAndApply;auto.
    right.
    rewrite<-addAndApply;auto.
    
    
    apply delPermsBoolCorrect.
    repeat apply stepIsInvariant.
    auto.
    auto.
    rewrite H2.
    rewrite orb_true_r.
    auto.
    unfold read_safe.
    rewrite  HeqlastSys.
    rewrite H0.
    simpl.
    auto.
Qed.

End DelGrantPRevoke.

