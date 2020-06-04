(* En este archivo se definen los códigos de errores 
*  y las situaciones en las que cada uno puede lanzarse *)
Require Import Semantica.
Require Import Operaciones.
Require Import Estado.
Require Import Maps.
Require Import RuntimePermissions.


Section ErrorCodes.

(* Códigos de error factibles de ser arrojados *)
Inductive ErrorCode : Set :=
    | app_already_installed
    | duplicated_cmp_id
    | duplicated_perm_id
    | cmp_already_defined
    | perm_already_defined
    | faulty_intent_filter

    | no_such_app
    | app_is_running

    | perm_not_in_use
    | no_such_perm
    | perm_already_granted
    | perm_not_dangerous
    | perm_is_grouped
    | perm_not_grouped
    | perm_should_auto_grant
    | cannot_auto_grant

    | perm_wasnt_granted

    | group_already_granted
    | group_not_in_use

    | group_wasnt_granted

    | no_such_res

    | incorrect_intent_type 
    | faulty_intent
    | intent_already_sent

    | no_such_intt
    | cmp_is_CProvider
    | instance_not_running
    | a_cant_start_b
    | not_enough_permissions
    | no_CProvider_fits
    | should_verify_permissions

    | CProvider_not_grantable

    | no_verification_needed
    | already_verified.

End ErrorCodes.

Section ErrorMessages.

(* Esta relación indica si el intentar ejecutar la acción action
 * en el sistema s permite arrojar el código de error ec *)
Definition ErrorMsg (s:System) (action:Action) (ec:ErrorCode) : Prop :=
match action with
   | install a m c l => match ec with 
        (* Se intenta instalar una aplicación con igual id que una existente *)
        | app_already_installed => isAppInstalled a s 
        (* La aplicación a instalar define componentes con igual identificador *)
        | duplicated_cmp_id => has_duplicates idCmp idCmp_eq (map getCmpId (cmp m)) = true
        (* La aplicación a instalar define permisos con igual identificador *)
        | duplicated_perm_id => has_duplicates idPerm idPerm_eq (map idP (usrP m)) = true
        (* La aplicación a instalar define algún componente cuyo id coincide con el de uno ya instalado *)
        | cmp_already_defined => ~(forall c:Cmp, In c (cmp m) -> cmpNotInState c s)
        (* La aplicación a instalar intenta redefinir un permiso *)
        | perm_already_defined => ~(authPerms m s)
        (* La aplicación declara un intent filter erróneamente *)
        | faulty_intent_filter => ~(forall (c:Cmp), In c (cmp m) -> cmpDeclareIntentFilterCorrectly c)
        | _ => False
        end
   | uninstall a => match ec with
        (* La aplicación que se pretende desinstalar no está instalada *)
        | no_such_app => ~ In a (apps (state s))
        (* Un componente de la aplicación a desinstalar se encuentra en ejecución *)
        | app_is_running => ~(forall (ic : iCmp) (c : Cmp), map_apply iCmp_eq (running (state s)) ic = Value iCmp c -> ~ inApp c a s)
        | _ => False
        end
   | grant p a => match ec with
        (* Se quiere otorgar un permiso no marcado como usado *)
        | perm_not_in_use => ~(exists m:Manifest, map_apply idApp_eq (manifest (environment s)) a = Value idApp m /\ In (idP p) (use m))
        (* Se quiere otorgar un permiso inexistente *)
        | no_such_perm => ~(isSystemPerm p \/ usrDefPerm p s)
        (* Se quiere reotorgar un permiso ya otorgado *)
        | perm_already_granted => (exists lPerm:list Perm, map_apply idApp_eq (perms (state s)) a = Value idApp lPerm /\ In p lPerm)
        (* Se quiere otorgar un permiso que no es peligroso *)
        | perm_not_dangerous => pl p <> dangerous
        (* Se quiere pedir confirmación al usuario por un permiso que debería ser otorgado automáticamente *)
        | perm_should_auto_grant => (exists (g: idGrp) (lGroup: list idGrp), maybeGrp p = Some g /\
               map_apply idApp_eq (grantedPermGroups (state s)) a = Value idApp lGroup /\ In g lGroup)
        | _ => False
        end
   | grantAuto p a => match ec with
        (* Se quiere otorgar un permiso no marcado como usado *)
        | perm_not_in_use => ~(exists m:Manifest, map_apply idApp_eq (manifest (environment s)) a = Value idApp m /\ In (idP p) (use m))
        (* Se quiere otorgar un permiso inexistente *)
        | no_such_perm => ~(isSystemPerm p \/ usrDefPerm p s)
        (* Se quiere reotorgar un permiso ya otorgado *)
        | perm_already_granted => (exists lPerm:list Perm, map_apply idApp_eq (perms (state s)) a = Value idApp lPerm /\ In p lPerm)
        (* Se quiere otorgar un permiso que no es peligroso *)
        | perm_not_dangerous => pl p <> dangerous
        (* Se quiere otorgar automáticamente un permiso que no está agrupado *)
        | perm_not_grouped => maybeGrp p = None
        (* Se quiere otorgar automáticamente un permiso que no pertenece a ningún grupo ya visitado *)
        | cannot_auto_grant => (exists (g: idGrp) (lGroup: list idGrp), maybeGrp p = Some g /\
                map_apply idApp_eq (grantedPermGroups (state s)) a = Value idApp lGroup /\ ~(In g lGroup))
        | _ => False
        end
   | revoke p c => match ec with
        (* Se quiere revocar un permiso que no estaba otorgado *)
        | perm_wasnt_granted => ~pre_revoke p c s
        (* Se quiere revocar un permiso agrupado de manera individual*)
        | perm_is_grouped => exists g: idGrp, maybeGrp p = Some g
        | _ => False
        end
   | revokePermGroup g c => match ec with
        (* Se quiere revocar un grupo de permisos que no estaba otorgado *)
        | group_wasnt_granted => ~pre_revokeGroup g c s
        | _ => False
        end
   | hasPermission p c => False
   | read ic cp u => match ec with
        (* Se intenta leer un recurso inexistente *)
        | no_such_res => ~existsRes cp u s
        (* Quien intenta leer no es una instancia en ejecución válida *)
        | instance_not_running => ~is_Value (map_apply iCmp_eq (running (state s)) ic)
        (* Quien intenta leer no tiene los permisos para hacerlo *)
        | not_enough_permissions => (exists (c:Cmp), map_apply iCmp_eq (running (state s)) ic = Value iCmp c /\ ~(canRead c cp s \/ delPerms c cp u Read s))
        | _ => False
        end
   | write ic cp u val => match ec with
        (* Se intenta escribir un recurso inexistente *)
        | no_such_res => ~existsRes cp u s
        (* Quien intenta escribir no es una instancia en ejecución válida *)
        | instance_not_running => ~is_Value (map_apply iCmp_eq (running (state s)) ic)
        (* Quien intenta escribir no tiene los permisos para hacerlo *)
        | not_enough_permissions => (exists (c:Cmp), map_apply iCmp_eq (running (state s)) ic = Value iCmp c /\ ~(canWrite c cp s \/ delPerms c cp u Write s))
        | _ => False
        end
   | startActivity i ic => match ec with
        (* El intent a enviar no es de actividad *)
        | incorrect_intent_type => intType i <> intActivity
        (* El intent a enviar ya define un permiso *)
        | faulty_intent => brperm i <> None
        (* La instancia que pretende iniciar la actividad no es válida *)
        | instance_not_running => ~cmpRunning ic s
        (* Ya existe un intent enviado con igual identificador *)
        | intent_already_sent => exists (i':Intent) (ic':iCmp), In (ic',i') (sentIntents (state s)) /\ idI i' = idI i
        | _ => False
        end
   | startActivityForResult i n ic => match ec with
        (* El intent a enviar no es de actividad *)
        | incorrect_intent_type => intType i <> intActivity
        (* El intent a enviar ya define un permiso *)
        | faulty_intent => brperm i <> None
        (* La instancia que pretende iniciar la actividad no es válida *)
        | instance_not_running => ~cmpRunning ic s
        (* Ya existe un intent enviado con igual identificador *)
        | intent_already_sent => exists (i':Intent) (ic':iCmp), In (ic',i') (sentIntents (state s)) /\ idI i' = idI i
        | _ => False
        end
   | startService i ic => match ec with
        (* El intent a enviar no es de servicio *)
        | incorrect_intent_type => intType i <> intService
        (* El intent a enviar ya define un permiso *)
        | faulty_intent => brperm i <> None
        (* La instancia que pretende iniciar la actividad no es válida *)
        | instance_not_running => ~cmpRunning ic s
        (* Ya existe un intent enviado con igual identificador *)
        | intent_already_sent => exists (i':Intent) (ic':iCmp), In (ic',i') (sentIntents (state s)) /\ idI i' = idI i
        | _ => False
        end
   | sendBroadcast i ic p => match ec with
        (* El intent a enviar no es de broadcast *)
        | incorrect_intent_type => intType i <> intBroadcast
        (* El intent a enviar ya define un permiso *)
        | faulty_intent => brperm i <> None
        (* La instancia que pretende iniciar la actividad no es válida *)
        | instance_not_running => ~cmpRunning ic s
        (* Ya existe un intent enviado con igual identificador *)
        | intent_already_sent => exists (i':Intent) (ic':iCmp), In (ic',i') (sentIntents (state s)) /\ idI i' = idI i
        | _ => False
        end
   | sendOrderedBroadcast i ic p => match ec with
        (* El intent a enviar no es de broadcast *)
        | incorrect_intent_type => intType i <> intBroadcast
        (* El intent a enviar ya define un permiso *)
        | faulty_intent => brperm i <> None
        (* La instancia que pretende iniciar la actividad no es válida *)
        | instance_not_running => ~cmpRunning ic s
        (* Ya existe un intent enviado con igual identificador *)
        | intent_already_sent => exists (i':Intent) (ic':iCmp), In (ic',i') (sentIntents (state s)) /\ idI i' = idI i
        | _ => False
        end
   | sendStickyBroadcast i ic => match ec with
        (* El intent a enviar no es de broadcast *)
        | incorrect_intent_type => intType i <> intBroadcast
        (* El intent a enviar ya define un permiso *)
        | faulty_intent => brperm i <> None
        (* La instancia que pretende iniciar la actividad no es válida *)
        | instance_not_running => ~cmpRunning ic s
        (* Ya existe un intent enviado con igual identificador *)
        | intent_already_sent => exists (i':Intent) (ic':iCmp), In (ic',i') (sentIntents (state s)) /\ idI i' = idI i
        | _ => False
        end
   | resolveIntent i a => match ec with
        (* Se quiere resolver un intent que no figura como enviado *)
        | no_such_intt => ~ pre_resolveIntent i a s
        | _ => False
        end
   | receiveIntent i ic a => match ec with
        (* Se quiere recibir un intent que no figura como enviado *)
        | no_such_intt => ~(exists (c:Cmp), intentForApp i a c ic s)
        (* Quien pretende recibirlo es un CProvider *)
        | cmp_is_CProvider => exists (c:Cmp), (intentForApp i a c ic s \/ map_apply iCmp_eq (running (state s)) ic=Value iCmp c) /\ isCProvider c
        (* La instancia que intenta recibirlo no tiene un id de ejecución válido *)
        | instance_not_running => ~is_Value (map_apply iCmp_eq (running (state s)) ic)
        (* Quien intenta recibir el intent no puede ser iniciado por el remitente *)
        | a_cant_start_b => exists (c c':Cmp), intentForApp i a c ic s /\ map_apply iCmp_eq (running (state s)) ic=Value iCmp c' /\ ~canStart c' c s
        (* Quien intenta recibir el intent no tiene permisos de hacerlo *)
        | not_enough_permissions => (intType i) = intBroadcast /\ (brperm i) <> None /\ (exists (p:Perm), (brperm i) = Some p /\ ~appHasPermission a p s)
        (* Quien intenta recibir el intent no tiene el permiso de acceso al recurso necesario *)
        | no_CProvider_fits => exists c':Cmp, map_apply iCmp_eq (running (state s)) ic=Value iCmp c' /\ ((intType i) = intActivity /\ forall (u:uri), path (data i)= Some u -> 
                    ~(exists (cp:CProvider), existsRes cp u s /\ canGrant cp u s /\
                        match (intentActionType i) with
                        | Read => canRead c' cp s \/ delPerms c' cp u Read s
                        | Write => canWrite c' cp s \/ delPerms c' cp u Write s
                        | Both => (canRead c' cp s \/ delPerms c' cp u Read s) /\ (canWrite c' cp s \/ delPerms c' cp u Write s)
                        end))
        | should_verify_permissions => ~ (canRun a s)
        | _ => False
        end
   | stop ic => match ec with
        (* La instancia que intenta detenerse no está en ejecución *)
        | instance_not_running => ~is_Value (map_apply iCmp_eq (running (state s)) ic)
        | _ => False
        end
   | grantP ic cp a u pt => match ec with
        (* El CProvider no permite otorgamiento *)
        | CProvider_not_grantable => ~canGrant cp u s
        (* El recurso sobre el que se desea otorgar permisos no existe *)
        | no_such_res => ~existsRes cp u s
        (* La aplicación a la que se desea otorgar permisosno existe *)
        | no_such_app => ~isAppInstalled a s
        (* La instancia que desea otorgar recursos no tiene un id de ejecución válido *)
        | instance_not_running => ~is_Value (map_apply iCmp_eq (running (state s)) ic)
        (* La instancia que desea otorgar el permiso no cuenta con él *)
        | not_enough_permissions => exists (c:Cmp), map_apply iCmp_eq (running (state s)) ic = Value iCmp c /\
                ~(match pt with
                | Read => canRead c cp s \/ delPerms c cp u Read s
                | Write => canWrite c cp s \/ delPerms c cp u Write s
                | Both => (canRead c cp s \/ delPerms c cp u Read s) /\ (canWrite c cp s \/ delPerms c cp u Write s)
                end)
        | _ => False
        end
   | revokeDel ic cp u pt => match ec with
        (* El recurso sobre el que se desea revocar no existe *)
        | no_such_res => ~existsRes cp u s
        (* Quien intenta revocar los permisos otorgados no tiene un identificador de ejecución válido *)
        | instance_not_running => ~is_Value (map_apply iCmp_eq (running (state s)) ic)
        (* La instancia que desea revocar el permiso no cuenta con él *)
        | not_enough_permissions => exists (c:Cmp), map_apply iCmp_eq (running (state s)) ic = Value iCmp c /\
                ~(match pt with
                | Read => canRead c cp s \/ delPerms c cp u Read s
                | Write => canWrite c cp s \/ delPerms c cp u Write s
                | Both => (canRead c cp s \/ delPerms c cp u Read s) /\ (canWrite c cp s \/ delPerms c cp u Write s)
                end)
        | _ => False
        end
   | call ic sac =>  match ec with
        (* La instancia que desea efectuar la llamada al sistema no tiene un identificador de ejecución válido *)
        | instance_not_running => ~is_Value (map_apply iCmp_eq (running (state s)) ic)
        (* La instancia que desea efectuar la llamada al sistema no cuenta con los permisos suficientes para hacerlos *)
        | not_enough_permissions => exists (c:Cmp), map_apply iCmp_eq (running (state s)) ic = Value iCmp c /\
                ~(forall (a:idApp)(p:Perm)(H:isSystemPerm p), 
                inApp c a s -> 
                permSAC p H sac -> 
                appHasPermission a p s)
        | _ => False
        end
    (* TODO: Revisar los errores para esta operación *)
    | verifyOldApp a => match ec with
        (* La aplicación que se quiere verificar no está instalada *)
        | no_such_app => ~isAppInstalled a s
        (* La aplicación ya ha sido ejecutada alguna vez *)
        | already_verified => In a (alreadyRun (state s))
        | no_verification_needed => ~ isOldApp a s
        | _ => False
        end
    end.

End ErrorMessages.

Section Response.

(* El tipo de las respuestas que puede originar la ejecución de una acción *)
Inductive Response : Set :=
| ok
| error : ErrorCode -> Response.

End Response.
