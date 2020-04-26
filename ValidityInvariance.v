(* En este archivo se utilizan los lemas de invarianza por acción
*  para demostrar que la relación exec preserva los invariantes de estado *)
Require Export Exec.
Require Export Estado.
Require Export Operaciones.
Require Export Semantica.
Require Export ErrorManagement.
Require Export Tacticas.
Require Export InstallIsInvariant.
Require Export UninstallIsInvariant.
Require Export GrantIsInvariant.
Require Export RevokeIsInvariant.
Require Export RevokeGroupIsInvariant.
Require Export WriteIsInvariant.
Require Export StartActivityIsInvariant.
Require Export StartServiceIsInvariant.
Require Export SendBroadcastIsInvariant.
Require Export ResolveIntentIsInvariant.
Require Export ReceiveIntentIsInvariant.
Require Export StopIsInvariant.
Require Export GrantPIsInvariant.
Require Export RevokeDelIsInvariant.

Section ValidityInvariance.
(* Este lema certifica la invarianza de la validez de estados en el modelo *)
Lemma validityIsInvariant :forall (s s':System) (act:Action) (r:Response),
        validstate s -> exec s act s' r -> validstate s'.
Proof.
    intros.
    destruct act;
    unfold exec in H0;
    destruct H0;
    try (destruct H1;[ destruct_conj H1;simpl in H1;simpl in H4 | destruct H1;destruct_conj H1; rewrite<- H4;auto; destruct H1]).
    apply (InstallIsInvariant s s' H i m c l);auto.
    apply (UninstallIsInvariant s s' H i);auto.
    apply (GrantIsInvariant s s' H p i);auto.
    apply (RevokeIsInvariant s s' H p i);auto.
    apply (RevokeGroupIsInvariant s s' H i i0);auto.
    unfold post_hasPermission in H4;rewrite<- H4;auto.
    unfold post_read in H4;rewrite<- H4;auto.
    apply (WriteIsInvariant s s' H i c u v);auto.
    apply (StartActivityIsInvariant s s' H i i0);auto.
    apply (StartActivityIsInvariant s s' H i i0);auto.
    apply (StartServiceIsInvariant s s' H i i0);auto.
    apply (SendBroadcastIsInvariant s s' H i i0 o);auto.
    apply (SendBroadcastIsInvariant s s' H i i0 o);auto.
    apply (SendBroadcastIsInvariant s s' H i i0 None);auto.
    apply (ResolveIntentIsInvariant s s' H i i0);auto.
    apply (ReceiveIntentIsInvariant s s' H i i0 i1);auto.
    apply (StopIsInvariant s s' H i);auto.
    apply (GrantPIsInvariant s s' H i c i0 u p);auto.
    apply (RevokeDelIsInvariant s s' H i c u p);auto.
    unfold post_call in H4;rewrite<- H4;auto.
Qed.
End ValidityInvariance.
