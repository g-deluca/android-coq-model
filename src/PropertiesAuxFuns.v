(* En este archivo se definen lemas auxiliares utilizados en
* la demostración de las propiedades postuladas *)
Require Export Exec.
Require Export Estado.
Require Export Operaciones.
Require Export Semantica.
Require Export ErrorManagement.
Require Export DefBasicas.
Require Export Implementacion.
Require Export ValidityInvariance.
Require Export Soundness.

Lemma stepIsInvariant :forall (s:System) (sValid:validstate s) (act:Action), validstate (system (step s act)).
Proof.
    intros.
    apply (validityIsInvariant s (system (step s act)) act (response (step s act)));auto.
    apply stepIsSound;auto.
Qed.

Lemma grantPreservesEnv : forall (s s':System) (p:Perm) (a:idApp), environment s=environment s'-> environment s = environment (system (step s' (grant p a))).
Proof.
    intros.
    unfold step.
    unfold grant_safe.
    case_eq (grant_pre p a s');intros;simpl;auto.
Qed.

Lemma revokePreservesEnv : forall (s s':System) (p:Perm) (a:idApp), environment s=environment s'-> environment s = environment (system (step s' (revoke p a))).
Proof.
    intros.
    unfold step.
    unfold revoke_safe.
    case_eq (revoke_pre p a s');intros;simpl;auto.
Qed.

Lemma grantPPreservesEnv : forall (s s':System) (ic:iCmp) (cp:CProvider) (a:idApp) (u:uri) (pt:PType), environment s=environment s'-> environment s = environment (system (step s' (grantP ic cp a u pt))).
Proof.
    intros.
    unfold step.
    unfold grantP_safe.
    case_eq (grantP_pre ic cp a u pt s');intros;simpl;auto.
Qed.


Lemma grantPreservesResCont : forall (s s':System) (p:Perm) (a:idApp), resCont (state s)=resCont (state s')-> resCont (state s) = resCont (state (system (step s' (grant p a)))).
Proof.
    intros.
    unfold step.
    unfold grant_safe.
    case_eq (grant_pre p a s');intros;simpl;auto.
Qed.

Lemma revokePreservesResCont : forall (s s':System) (p:Perm) (a:idApp), resCont (state s)=resCont (state s')-> resCont (state s )= resCont (state (system (step s' (revoke p a)))).
Proof.
    intros.
    unfold step.
    unfold revoke_safe.
    case_eq (revoke_pre p a s');intros;simpl;auto.
Qed.

Lemma grantPPreservesResCont : forall (s s':System) (ic:iCmp) (cp:CProvider) (a:idApp) (u:uri) (pt:PType), resCont (state s)=resCont (state s')-> resCont (state s) = resCont (state (system (step s' (grantP ic cp a u pt)))).
Proof.
    intros.
    unfold step.
    unfold grantP_safe.
    case_eq (grantP_pre ic cp a u pt s');intros;simpl;auto.
Qed.


Lemma grantPreservesRunning : forall (s s':System) (p:Perm) (a:idApp), running (state s)=running (state s')-> running (state s) = running (state (system (step s' (grant p a)))).
Proof.
    intros.
    unfold step.
    unfold grant_safe.
    case_eq (grant_pre p a s');intros;simpl;auto.
Qed.

Lemma revokePreservesRunning : forall (s s':System) (p:Perm) (a:idApp), running (state s)=running (state s')-> running (state s )= running (state (system (step s' (revoke p a)))).
Proof.
    intros.
    unfold step.
    unfold revoke_safe.
    case_eq (revoke_pre p a s');intros;simpl;auto.
Qed.

Lemma grantPPreservesRunning : forall (s s':System) (ic:iCmp) (cp:CProvider) (a:idApp) (u:uri) (pt:PType), running (state s)=running (state s')-> running (state s) = running (state (system (step s' (grantP ic cp a u pt)))).
Proof.
    intros.
    unfold step.
    unfold grantP_safe.
    case_eq (grantP_pre ic cp a u pt s');intros;simpl;auto.
Qed.


Lemma grantPreservesDelPPerms : forall (s s':System) (p:Perm) (a:idApp), delPPerms (state s)=delPPerms (state s')-> delPPerms (state s) = delPPerms (state (system (step s' (grant p a)))).
Proof.
    intros.
    unfold step.
    unfold grant_safe.
    case_eq (grant_pre p a s');intros;simpl;auto.
Qed.

Lemma revokePreservesDelPPerms : forall (s s':System) (p:Perm) (a:idApp), delPPerms (state s)=delPPerms (state s')-> delPPerms (state s )= delPPerms (state (system (step s' (revoke p a)))).
Proof.
    intros.
    unfold step.
    unfold revoke_safe.
    case_eq (revoke_pre p a s');intros;simpl;auto.
Qed.
