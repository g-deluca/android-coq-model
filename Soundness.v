(* En este archivo se utilizan los lemas de corrección por acción
*  para demostrar que la función step respeta el modelo *)
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
Require Import InstallIsSound.
Require Import UninstallIsSound.
Require Import GrantIsSound.
Require Import GrantAutoIsSound.
Require Import RevokeIsSound.
Require Import RevokeGroupIsSound.
Require Import HasPermissionIsSound.
Require Import ReadIsSound.
Require Import WriteIsSound.
Require Import StartActivityIsSound.
Require Import StartActivityForResIsSound.
Require Import StartServiceIsSound.
Require Import SendBroadcastIsSound.
Require Import SendOrderedBroadcastIsSound.
Require Import SendStickyBroadcastIsSound.
Require Import ResolveIntentIsSound.
Require Import ReceiveIntentIsSound.
Require Import StopIsSound.
Require Import GrantPIsSound.
Require Import RevokeDelIsSound.
Require Import CallIsSound.
Require Import VerifyOldAppIsSound.

Section Soundness.
(* La demostración de este teorma certifica la corrección de la función step *)
Theorem stepIsSound : forall (s:System) (act:Action),
    validstate s -> exec s act (system (step s act)) (response (step s act)).
Proof.
    intros.
    destruct act.
    exact (installIsSound s i m c l H).
    exact (uninstallIsSound s i H).
    exact (grantIsSound s i p H).
    exact (grantAutoIsSound s i p H).
    exact (revokeIsSound s i p H).
    exact (revokegroupIsSound s i0 i H).
    exact (hasPermissionIsSound s p c H).
    exact (readIsSound s i c u H).
    exact (writeIsSound s i c u v H).
    exact (startActivityIsSound s i i0 H).
    exact (startActivityForResultIsSound s i i0 H n).
    exact (startServiceIsSound s i i0 H).
    exact (sendBroadcastIsSound s i i0 o H).
    exact (sendOrderedBroadcastIsSound s i i0 o H).
    exact (sendStickyBroadcastIsSound s i i0 H).
    exact (resolveIntentIsSound s i i0 H).
    exact (receiveIntentIsSound s i i0 i1 H).
    exact (stopIsSound s i H).
    exact (grantPIsSound s i c i0 u p H).
    exact (revokeDelIsSound s i c u p H).
    exact (callIsSound s i s0 H).
    exact (verifyOldAppIsSound s i H).
Qed.
End Soundness.

