(* In this file we demonstrate that in a particular scenario, eavesdropping is not possible *)

Require Export Exec.
Require Export Estado.
Require Export Operaciones.
Require Export Semantica.
Require Export ErrorManagement.
Require Export Tacticas.
Require Export Maps.

Lemma vsToNotRepeatedCmps : forall (s:System), validstate s -> notRepeatedCmps s.
Proof.
intros s H_vs.
unfold validstate in H_vs.
apply H_vs.
Qed.

Axiom onlyDangInPerms : forall (a:idApp)(p:Perm)(s:System), (exists l : list Perm,
			map_apply idApp_eq (perms (state s)) a = Value idApp l  /\ In p l) -> (pl p) = dangerous.


    


(* If a component sends a broadcast intent protected with a Signature (or SignatureOrSystem)
permission, then the only applications that will be able to receive it, will be those signed with the
same certificate. *)
Lemma eavesdropping : forall (ic:iCmp)(i:Intent)(cmp:Cmp)(a a':idApp)(c c':Cert)(s:System), 
validstate s ->
map_apply iCmp_eq (running (state s)) ic = Value iCmp cmp ->
~ isCProvider cmp ->
inApp cmp a s ->
In (ic,i) (sentIntents (state s)) ->
(intType i) = intBroadcast ->
(forall sysapp:SysImgApp, In sysapp (systemImage (environment s)) ->
idSI sysapp <> a') ->
(exists p:Perm, ((pl p) = signature \/ (pl p) = signatureOrSys) /\
(brperm i) = Some p /\
RuntimePermissions.appCert a c s /\ RuntimePermissions.certOfDefiner p c s /\
RuntimePermissions.appCert a' c' s /\ ~ RuntimePermissions.certOfDefiner p c' s /\
c' <> RuntimePermissions.manufacturerCert) -> 
~ (pre_receiveIntent i ic a' s).

Proof.
intros ic i cmp a a' c c' s H_vs H_running_ic_cmp H_notCP_cmp H_inApp_cmp_a 
H_sentInt H_intType H_forall H_exists.
destruct H_exists as [p H_conj].
destruct H_conj as [H_pl_p H_conj].
destruct H_conj as [H_brperm_p H_conj].
destruct H_conj as [H_certOf_a H_conj].
destruct H_conj as [H_certDef_p H_conj].
destruct H_conj as [H_certOf_a' H_conj].
destruct H_conj as [H_certNotDef_p H_notMan_c'].

unfold not; intro H_pre_receive.
destruct H_pre_receive as [_[cmp' H_conj]].
destruct H_conj as [H_intentForApp H_conj].
destruct H_conj as [H_notCP_cmp' H_exists].
destruct H_exists as [cmp2 H_conj].
destruct H_conj as [H_running_ic_cmp2 H_conj].
destruct H_conj as [H_notCP_cmp2 H_conj].
destruct H_conj as [H_canStart_cmp2_cmp H_conj];
destruct H_conj as [H_intAct H_intBroad].
clear H_intAct.

assert (exists (p : Perm), brperm i = Some p /\
        RuntimePermissions.appHasPermission a' p s) as H_exists.
apply H_intBroad.
split.
assumption.
rewrite H_brperm_p.
discriminate.

destruct H_exists as [p' H_conj].
destruct H_conj as [H_brperm_p' H_rtperm].
rewrite H_brperm_p in H_brperm_p'.
inversion H_brperm_p' as [H_p_p'].
rewrite <- H_p_p' in *.
elim H_rtperm.

(*case 1: exists l : list Perm,
   map_apply idApp_eq (perms (state s)) a' = Value idApp l /\ In p l*)
intro H_exists.
elim H_pl_p;
intro H_pl;
[absurd (pl p = signature) | absurd (pl p = signatureOrSys)].
rewrite (onlyDangInPerms a' p s H_exists); discriminate.
assumption.
rewrite (onlyDangInPerms a' p s H_exists); discriminate.
assumption.


intro H_conj.
destruct H_conj as [H_permEx H_conj].
destruct H_conj as [H_mfst H_or] .
elim H_or;
clear H_or.

(*case 2: exists lPerm : list Perm,
   map_apply idApp_eq (defPerms (environment s)) a' = Value idApp lPerm /\
   In p lPerm*)
intro H_exists.
destruct H_exists as [lp H_conj].
absurd (RuntimePermissions.certOfDefiner p c' s).
assumption.
unfold RuntimePermissions.certOfDefiner.
elim H_certOf_a'.
intro H_a'_c'.
left.
exists a'.
exists lp.
split.
apply H_conj.
split.
apply H_conj.
assumption.
clear H_conj.
intro H_exists.
elim H_exists.
intros sysapp H_conj.
destruct H_conj as [H_sysapp_env H_conj].
destruct H_conj as [H_sysapp_a' H_cert_sysapp].
assert (idSI sysapp <> a') as H_not_sysapp_a'.
apply (H_forall sysapp H_sysapp_env).
absurd (idSI sysapp = a'); assumption.

intro H_or.
elim H_or;
clear H_or.

(*case 3: pl p = normal*)
intro H_pl.
rewrite H_pl in H_pl_p.
elim H_pl_p;
intro H_norm;
[absurd (normal = signature); [discriminate | ] | absurd (normal = signatureOrSys); [discriminate | ]];
assumption.

intro H_or.
elim H_or;
clear H_or.


(*case 4: (pl p = signature \/ pl p = signatureOrSys) /\ ...*)
intro H_conj.
destruct H_conj as [H_or H_exists].
destruct H_exists as [c'' H_conj].
destruct H_conj as [H_certOf_a'_2 H_certDef_p_2].
replace c'' with c' in *.
absurd (RuntimePermissions.certOfDefiner p c' s); assumption.
elim H_certOf_a'_2; elim H_certOf_a'; intros.

(*case 4.1: map_apply idApp_eq (ce'rt (environment s)) a' = Value idApp c' y 
map_apply idApp_eq (cert (environment s)) a' = Value idApp c''*)
rewrite H in H0.
inversion_clear H0.
reflexivity.

(*case 4.2: exists sysapp : SysImgApp, In sysapp (systemImage (environment s)) /\
	    idSI sysapp = a' /\ certSI sysapp = c' y
	    map_apply idApp_eq (cert (environment s)) a' = Value idApp c''*)
elim H.
intros sysapp H_conj.
destruct H_conj as [H_sysapp_env H_conj].
destruct H_conj as [H_sysapp_a' H_cert_sysapp].
assert (idSI sysapp <> a') as H_not_sysapp_a'.
apply (H_forall sysapp H_sysapp_env).
absurd (idSI sysapp = a'); assumption.

(*case 4.3: map_apply idApp_eq (cert (environment s)) a' = Value idApp c' y
	    exists sysapp : SysImgApp, In sysapp (systemImage (environment s)) /\
	    idSI sysapp = a' /\ certSI sysapp = c''*)
elim H0.
intros sysapp H_conj.
destruct H_conj as [H_sysapp_env H_conj].
destruct H_conj as [H_sysapp_a' H_cert_sysapp].
assert (idSI sysapp <> a') as H_not_sysapp_a'.
apply (H_forall sysapp H_sysapp_env).
absurd (idSI sysapp = a'); assumption.

(*case 4.4: exists sysapp : SysImgApp, In sysapp (systemImage (environment s)) /\
            idSI sysapp = a' /\ certSI sysapp = c' y 
            exists sysapp : SysImgApp, In sysapp (systemImage (environment s)) /\
            idSI sysapp = a' /\ certSI sysapp = c*)
elim H0.
intros sysapp H_conj.
destruct H_conj as [H_sysapp_env H_conj].
destruct H_conj as [H_sysapp_a' H_cert_sysapp].
assert (idSI sysapp <> a') as H_not_sysapp_a'.
apply (H_forall sysapp H_sysapp_env).
absurd (idSI sysapp = a'); assumption.


(*case 5: pl p = signatureOrSys /\ ... *)
intro H_conj.
destruct H_conj as [H_pl_p_2 H_exists].
destruct H_exists as [c'' H_conj].
destruct H_conj as [H_certOf_a'_2 H_manufacturerCert_c''].
replace c'' with c' in *.
absurd (c' = RuntimePermissions.manufacturerCert); assumption.
elim H_certOf_a'_2; elim H_certOf_a'; intros.

(*case 5.1: map_apply idApp_eq (ce'rt (environment s)) a' = Value idApp c' y 
map_apply idApp_eq (cert (environment s)) a' = Value idApp c''*)
rewrite H in H0.
inversion_clear H0.
reflexivity.

(*case 5.2: exists sysapp : SysImgApp, In sysapp (systemImage (environment s)) /\
	    idSI sysapp = a' /\ certSI sysapp = c' y
	    map_apply idApp_eq (cert (environment s)) a' = Value idApp c''*)
elim H.
intros sysapp H_conj.
destruct H_conj as [H_sysapp_env H_conj].
destruct H_conj as [H_sysapp_a' H_cert_sysapp].
assert (idSI sysapp <> a') as H_not_sysapp_a'.
apply (H_forall sysapp H_sysapp_env).
absurd (idSI sysapp = a'); assumption.

(*case 5.3: map_apply idApp_eq (cert (environment s)) a' = Value idApp c' y
	    exists sysapp : SysImgApp, In sysapp (systemImage (environment s)) /\
	    idSI sysapp = a' /\ certSI sysapp = c''*)
elim H0.
intros sysapp H_conj.
destruct H_conj as [H_sysapp_env H_conj].
destruct H_conj as [H_sysapp_a' H_cert_sysapp].
assert (idSI sysapp <> a') as H_not_sysapp_a'.
apply (H_forall sysapp H_sysapp_env).
absurd (idSI sysapp = a'); assumption.

(*case 5.4: exists sysapp : SysImgApp, In sysapp (systemImage (environment s)) /\
            idSI sysapp = a' /\ certSI sysapp = c' y 
            exists sysapp : SysImgApp, In sysapp (systemImage (environment s)) /\
            idSI sysapp = a' /\ certSI sysapp = c*)
elim H0.
intros sysapp H_conj.
destruct H_conj as [H_sysapp_env H_conj].
destruct H_conj as [H_sysapp_a' H_cert_sysapp].
assert (idSI sysapp <> a') as H_not_sysapp_a'.
apply (H_forall sysapp H_sysapp_env).
absurd (idSI sysapp = a'); assumption.
Qed.
