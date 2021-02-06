(* In this file we define the basic actions that are able to make the system transition *)
Require Export DefBasicas.

Section Operaciones.

Inductive Action : Type :=
    | install : idApp -> Manifest -> Cert -> (list res) -> Action
    | uninstall: idApp -> Action
    | grant: Perm -> idApp -> Action
     (* This new action represents granting a dangerous permission to an app without explicit
     authorizatin of the user (whenever this is possible)*)
    | grantAuto: Perm -> idApp -> Action
    (* This action will be used for ungrouped permissions only *)
    | revoke: Perm -> idApp -> Action
    (* Revokes every individual permission grouped under idGrp*)
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
    (* This action represents the prompt where the user validates the legacy permissions of an old app *)
    | verifyOldApp: idApp -> Action.



End Operaciones.

