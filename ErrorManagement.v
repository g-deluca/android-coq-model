(* In this file we define the error codes and the situation in which they can be thrown *)
Require Import Semantica.
Require Import Operaciones.
Require Import Estado.
Require Import Maps.
Require Import RuntimePermissions.


Section ErrorCodes.

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

 (* This relation matches the actions a system can perform with the possible error outcomes associated to it *)
Definition ErrorMsg (s:System) (action:Action) (ec:ErrorCode) : Prop :=
match action with
   | install a m c l => match ec with 
        (* Someone tried to install an app with an ID that already exists *)
        | app_already_installed => isAppInstalled a s 
        (* The application defines components that have the same identifier *)
        | duplicated_cmp_id => has_duplicates idCmp idCmp_eq (map getCmpId (cmp m)) = true
        (* The application defines permissions that have the same identifier *)
        | duplicated_perm_id => has_duplicates idPerm idPerm_eq (map idP (usrP m)) = true
        (* A component from the application has an ID that is already taken by another app already installed*)
        | cmp_already_defined => ~(forall c:Cmp, In c (cmp m) -> cmpNotInState c s)
        (* The application being installed tries to redefine a permission *)
        | perm_already_defined => ~(authPerms m s)
        (* The application does not declare the intent filter correctly *)
        | faulty_intent_filter => ~(forall (c:Cmp), In c (cmp m) -> cmpDeclareIntentFilterCorrectly c)
        | _ => False
        end
   | uninstall a => match ec with
        (* The application someone is trying to uninstall is not installed *)
        | no_such_app => ~ In a (apps (state s))
        (* A component from the app that someone wants to uninstall is still running *)
        | app_is_running => ~(forall (ic : iCmp) (c : Cmp), map_apply iCmp_eq (running (state s)) ic = Value iCmp c -> ~ inApp c a s)
        | _ => False
        end
   | grant p a => match ec with
        (* The permission we are trying to grant is not listed as used in the manifest *)
        | perm_not_in_use => ~(exists m:Manifest, map_apply idApp_eq (manifest (environment s)) a = Value idApp m /\ In p (use m))
        (* The permission doesn't exist *)
        | no_such_perm => ~(isSystemPerm p \/ usrDefPerm p s)
        (* The permission is already granted *)
        | perm_already_granted => (exists lPerm:list Perm, map_apply idApp_eq (perms (state s)) a = Value idApp lPerm /\ In p lPerm)
        (* Permission is not dangerous, and therefore, was already granted at installation time *)
        | perm_not_dangerous => pl p <> dangerous
        (* We'll ask confirmation from the user for a permission that should automatically granted *)
        | perm_should_auto_grant => (exists (g: idGrp) (lGroup: list idGrp), maybeGrp p = Some g /\
               map_apply idApp_eq (grantedPermGroups (state s)) a = Value idApp lGroup /\ In g lGroup)
        | _ => False
        end
   | grantAuto p a => match ec with
        (* The permission we are trying to grant is not listed as used in the manifest *)
        | perm_not_in_use => ~(exists m:Manifest, map_apply idApp_eq (manifest (environment s)) a = Value idApp m /\ In p (use m))
        (* The permission doesn't exist *)
        | no_such_perm => ~(isSystemPerm p \/ usrDefPerm p s)
        (* The permission is already granted *)
        | perm_already_granted => (exists lPerm:list Perm, map_apply idApp_eq (perms (state s)) a = Value idApp lPerm /\ In p lPerm)
        (* Permission is not dangerous, and therefore, was already granted at installation time *)
        | perm_not_dangerous => pl p <> dangerous
        (* Permission is not grouped and therefore, cannot be automatically granted *)
        | perm_not_grouped => maybeGrp p = None
        (* No other permission of this group was granted previously and we should ask the user *)
        | cannot_auto_grant => (exists (g: idGrp) (lGroup: list idGrp), maybeGrp p = Some g /\
                map_apply idApp_eq (grantedPermGroups (state s)) a = Value idApp lGroup /\ ~(In g lGroup))
        | _ => False
        end
   | revoke p c => match ec with
        (* The permission we are trying to revoke wasn't granted *)
        | perm_wasnt_granted => ~pre_revoke p c s
        (* We cannot revoke individually a grouped permission *)
        | perm_is_grouped => exists g: idGrp, maybeGrp p = Some g
        | _ => False
        end
   | revokePermGroup g c => match ec with
        (* The permission group we are trying to revoke wasn't granted *)
        | group_wasnt_granted => ~pre_revokeGroup g c s
        | _ => False
        end
   | hasPermission p c => False
   | read ic cp u => match ec with
        (* Resource does not exists *)
        | no_such_res => ~existsRes cp u s
        (* The instance that is trying to read is not valid *)
        | instance_not_running => ~is_Value (map_apply iCmp_eq (running (state s)) ic)
        (* The instance that is trying to read has not enough permissions *)
        | not_enough_permissions => (exists (c:Cmp), map_apply iCmp_eq (running (state s)) ic = Value iCmp c /\ ~(canRead c cp s \/ delPerms c cp u Read s))
        | _ => False
        end
   | write ic cp u val => match ec with
        (* Resource does not exists *)
        | no_such_res => ~existsRes cp u s
        (* The instance that is trying to read is not valid *)
        | instance_not_running => ~is_Value (map_apply iCmp_eq (running (state s)) ic)
        (* The instance that is trying to write has not enough permissions *)
        | not_enough_permissions => (exists (c:Cmp), map_apply iCmp_eq (running (state s)) ic = Value iCmp c /\ ~(canWrite c cp s \/ delPerms c cp u Write s))
        | _ => False
        end
   | startActivity i ic => match ec with
        (* The intent we are trying to send is not an activity type *)
        | incorrect_intent_type => intType i <> intActivity
        (* The intent already defines a permission *)
        | faulty_intent => brperm i <> None
        (* The instance that sent the intent is not valid *)
        | instance_not_running => ~cmpRunning ic s
        (* Another intent with the same identifier was already sent *)
        | intent_already_sent => exists (i':Intent) (ic':iCmp), In (ic',i') (sentIntents (state s)) /\ idI i' = idI i
        | _ => False
        end
   | startActivityForResult i n ic => match ec with
        (* The intent we are trying to send is not an activity type *)
        | incorrect_intent_type => intType i <> intActivity
        (* The intent already defines a permission *)
        | faulty_intent => brperm i <> None
        (* The instance that sent the intent is not valid *)
        | instance_not_running => ~cmpRunning ic s
        (* Another intent with the same identifier was already sent *)
        | intent_already_sent => exists (i':Intent) (ic':iCmp), In (ic',i') (sentIntents (state s)) /\ idI i' = idI i
        | _ => False
        end
   | startService i ic => match ec with
        (* The intent we are trying to send is not a service type *)
        | incorrect_intent_type => intType i <> intService
        (* The intent already defines a permission *)
        | faulty_intent => brperm i <> None
        (* The instance that sent the intent is not valid *)
        | instance_not_running => ~cmpRunning ic s
        (* Another intent with the same identifier was already sent *)
        | intent_already_sent => exists (i':Intent) (ic':iCmp), In (ic',i') (sentIntents (state s)) /\ idI i' = idI i
        | _ => False
        end
   | sendBroadcast i ic p => match ec with
        (* The intent we are trying to send is not a broadcast type *)
        | incorrect_intent_type => intType i <> intBroadcast
        (* The intent already defines a permission *)
        | faulty_intent => brperm i <> None
        (* The instance that sent the intent is not valid *)
        | instance_not_running => ~cmpRunning ic s
        (* Another intent with the same identifier was already sent *)
        | intent_already_sent => exists (i':Intent) (ic':iCmp), In (ic',i') (sentIntents (state s)) /\ idI i' = idI i
        | _ => False
        end
   | sendOrderedBroadcast i ic p => match ec with
        (* The intent we are trying to send is not a broadcast type *)
        | incorrect_intent_type => intType i <> intBroadcast
        (* The intent already defines a permission *)
        | faulty_intent => brperm i <> None
        (* The instance that sent the intent is not valid *)
        | instance_not_running => ~cmpRunning ic s
        (* Another intent with the same identifier was already sent *)
        | intent_already_sent => exists (i':Intent) (ic':iCmp), In (ic',i') (sentIntents (state s)) /\ idI i' = idI i
        | _ => False
        end
   | sendStickyBroadcast i ic => match ec with
        (* The intent we are trying to send is not a broadcast type *)
        | incorrect_intent_type => intType i <> intBroadcast
        (* The intent already defines a permission *)
        | faulty_intent => brperm i <> None
        (* The instance that sent the intent is not valid *)
        | instance_not_running => ~cmpRunning ic s
        (* Another intent with the same identifier was already sent *)
        | intent_already_sent => exists (i':Intent) (ic':iCmp), In (ic',i') (sentIntents (state s)) /\ idI i' = idI i
        | _ => False
        end
   | resolveIntent i a => match ec with
        (* We are trying to resolve an intent that was not sent *)
        | no_such_intt => ~ pre_resolveIntent i a s
        | _ => False
        end
   | receiveIntent i ic a => match ec with
        (* We are trying to resolve an intent that was not sent *)
        | no_such_intt => ~(exists (c:Cmp), intentForApp i a c ic s)
        (* The component that is trying to receive the intent is a content provider*)
        | cmp_is_CProvider => exists (c:Cmp), (intentForApp i a c ic s \/ map_apply iCmp_eq (running (state s)) ic=Value iCmp c) /\ isCProvider c
        (* The instance that is trying to receive the intent is not running *)
        | instance_not_running => ~is_Value (map_apply iCmp_eq (running (state s)) ic)
        (* The intent sender is not able to start a component from the receiver *)
        | a_cant_start_b => exists (c c':Cmp), intentForApp i a c ic s /\ map_apply iCmp_eq (running (state s)) ic=Value iCmp c' /\ ~canStart c' c s
        (* The application that is trying to receive the intent has no permission for it *)
        | not_enough_permissions => (intType i) = intBroadcast /\ (brperm i) <> None /\ (exists (p:Perm), (brperm i) = Some p /\ ~appHasPermission a p s)
        (* The application that is trying to receive the intent cannot access the content provider *)
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
        (* The instance we are trying to stop is not running *)
        | instance_not_running => ~is_Value (map_apply iCmp_eq (running (state s)) ic)
        | _ => False
        end
   | grantP ic cp a u pt => match ec with
        (* The content provider can't grant permissions over the resource u *)
        | CProvider_not_grantable => ~canGrant cp u s
        (* The resource does not exist*)
        | no_such_res => ~existsRes cp u s
        (* The application to which we'll grant the permission does not exist*)
        | no_such_app => ~isAppInstalled a s
        (* The instance that wants to grant the permission is not running *)
        | instance_not_running => ~is_Value (map_apply iCmp_eq (running (state s)) ic)
        (* The instance that wants to grant the permission doesn't have it *)
        | not_enough_permissions => exists (c:Cmp), map_apply iCmp_eq (running (state s)) ic = Value iCmp c /\
                ~(match pt with
                | Read => canRead c cp s \/ delPerms c cp u Read s
                | Write => canWrite c cp s \/ delPerms c cp u Write s
                | Both => (canRead c cp s \/ delPerms c cp u Read s) /\ (canWrite c cp s \/ delPerms c cp u Write s)
                end)
        | _ => False
        end
   | revokeDel ic cp u pt => match ec with
        (* The resource does not exist*)
        | no_such_res => ~existsRes cp u s
        (* The instance that wants to revoke the permission is not running *)
        | instance_not_running => ~is_Value (map_apply iCmp_eq (running (state s)) ic)
        (* The instance that wants to revoke the permission doesn't have it *)
        | not_enough_permissions => exists (c:Cmp), map_apply iCmp_eq (running (state s)) ic = Value iCmp c /\
                ~(match pt with
                | Read => canRead c cp s \/ delPerms c cp u Read s
                | Write => canWrite c cp s \/ delPerms c cp u Write s
                | Both => (canRead c cp s \/ delPerms c cp u Read s) /\ (canWrite c cp s \/ delPerms c cp u Write s)
                end)
        | _ => False
        end
   | call ic sac =>  match ec with
        (* The instance that wants to make the API call is not running *)
        | instance_not_running => ~is_Value (map_apply iCmp_eq (running (state s)) ic)
        (* The instance that wants to make the API call doesn't have the proper permissions to do it *)
        | not_enough_permissions => exists (c:Cmp), map_apply iCmp_eq (running (state s)) ic = Value iCmp c /\
                ~(forall (a:idApp)(p:Perm)(H:isSystemPerm p), 
                inApp c a s -> 
                permSAC p H sac -> 
                appHasPermission a p s)
        | _ => False
        end
    | verifyOldApp a => match ec with
        (* The application we are trying to verify is not installed *)
        | no_such_app => ~isAppInstalled a s
        (* The application was already verified by the user *)
        | already_verified => In a (alreadyVerified (state s))
        (* The application is not considered old enough to be verified *)
        | no_verification_needed => ~ isOldApp a s
        | _ => False
        end
    end.

End ErrorMessages.

Section Response.

Inductive Response : Set :=
| ok
| error : ErrorCode -> Response.

End Response.
