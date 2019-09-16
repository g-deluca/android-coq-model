(* En este archivo se define la relación de transición entre dos sistemas
* cuando se solicita la ejecución de una acción *)
Require Import Semantica.
Require Import Operaciones.
Require Import ErrorManagement.
Require Import Estado.

Section EjecucionDeOps.

(* Indica si la precondición de una acción se cumple en un sistema *)
Definition pre (act:Action) (s:System) : Prop :=
match act with
   | install a m c l => pre_install a m c l s
   | uninstall a => pre_uninstall a s
   | grant p c => pre_grant p c s
   | revoke p c => pre_revoke p c s
   | grantPermGroup g c => pre_grantGroup g c s
   | revokePermGroup g c => pre_revokeGroup g c s
   | hasPermission p c => pre_hasPermission p c s
   | read ic cp u => pre_read ic cp u s
   | write ic cp u val => pre_write ic cp u val s
   | startActivity i ic => pre_startActivity i ic s
   | startActivityForResult i n ic => pre_startActivityForResult i n ic s
   | startService i ic => pre_startService i ic s
   | sendBroadcast i ic p => pre_sendBroadcast i ic p s
   | sendOrderedBroadcast i ic p => pre_sendOrderedBroadcast i ic p s
   | sendStickyBroadcast i ic => pre_sendStickyBroadcast i ic s
   | resolveIntent i a => pre_resolveIntent i a s
   | receiveIntent i ic a => pre_receiveIntent i ic a s
   | stop ic => pre_stop ic s
   | grantP ic cp a u pt => pre_grantP ic cp a u pt s
   | revokeDel ic cp u pt => pre_revokeDel ic cp u pt s
   | call ic aCall => pre_call ic aCall s
end.

(* Indica si la postcondición de una acción se cumple en un sistema
 * resultante partiendo de uno origen *)
Definition post (act:Action) (s s':System) : Prop :=
match act with
   | install a m c l => post_install a m c l s s'
   | uninstall a => post_uninstall a s s'
   | grant p c => post_grant p c s s'
   | revoke p c => post_revoke p c s s'
   | grantPermGroup g c => post_grantGroup g c s s'
   | revokePermGroup g c => post_revokeGroup g c s s'
   | hasPermission p c => post_hasPermission p c s s'
   | read ic cp u => post_read ic cp u s s'
   | write ic cp u val => post_write ic cp u val s s'
   | startActivity i ic => post_startActivity i ic s s'
   | startActivityForResult i n ic => post_startActivityForResult i n ic s s'
   | startService i ic => post_startService i ic s s'
   | sendBroadcast i ic p => post_sendBroadcast i ic p s s'
   | sendOrderedBroadcast i ic p => post_sendOrderedBroadcast i ic p s s' 
   | sendStickyBroadcast i ic => post_sendStickyBroadcast i ic s s'
   | resolveIntent i a => post_resolveIntent i a s s'
   | receiveIntent i ic a => post_receiveIntent i ic a s s'
   | stop ic => post_stop ic s s'
   | grantP ic cp a u pt => post_grantP ic cp a u pt s s'
   | revokeDel ic cp u pt => post_revokeDel ic cp u pt s s'
   | call ic aCall => post_call ic aCall s s'
end.

(* Esta proposición captura la semántica de la ejecución de una acción *)
Definition exec (s: System) (act:Action) (s':System) (r:Response) : Prop :=
    validstate s /\
   ((r = ok /\ pre act s /\ post act s s') \/
   (exists ec:ErrorCode, r = error ec /\ ErrorMsg s act ec /\ s=s')).

End EjecucionDeOps.
