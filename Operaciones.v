(* En este archivo se formalizan las acciones capaces de modificar el sistema *)
Require Export DefBasicas.

Section Operaciones.

(* El tipo de las acciones *)
Inductive Action : Type :=
    | install : idApp -> Manifest -> Cert -> (list res) -> Action
    | uninstall: idApp -> Action
    | grant: Perm -> idApp -> Action
    (* Incorporamos una nueva operación de grant, que representa el otorgamiento de un permiso sin la notificación
     * al usuario *)
    | grantAuto: Perm -> idApp -> Action
    | revoke: Perm -> idApp -> Action
    | grantPermGroup: idGrp -> idApp -> Action
    | revokePermGroup: idGrp -> idApp -> Action
    | hasPermission: Perm -> Cmp -> Action
    | read : iCmp -> CProvider -> uri -> Action
    | write: iCmp -> CProvider -> uri -> Val -> Action
    | startActivity : Intent -> iCmp -> Action
    | startActivityForResult: Intent -> nat -> iCmp -> Action
    | startService: Intent -> iCmp -> Action
    | sendBroadcast: Intent -> iCmp -> option Perm -> Action
    | sendOrderedBroadcast: Intent -> iCmp -> option Perm -> Action
    | sendStickyBroadcast: Intent -> iCmp -> Action
    | resolveIntent : Intent -> idApp -> Action
    | receiveIntent : Intent -> iCmp -> idApp -> Action
    | stop: iCmp -> Action
    | grantP: iCmp -> CProvider -> idApp -> uri -> PType -> Action
    | revokeDel: iCmp -> CProvider -> uri -> PType -> Action
    | call: iCmp -> SACall -> Action
    (* Esta acción será la encargada de verificar si una aplicación está en condiciones de ser ejecutada*)
    | verifyOldApp: idApp -> Action.



End Operaciones.

