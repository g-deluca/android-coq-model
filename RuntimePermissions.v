(* En este archivo se captura la lógica de Android para decidir
* si una aplicación cuenta con determinado permiso *)
Require Import DefBasicas.
Require Import Estado.
Require Import Maps.

Section PermissionCheck.

(* Este parámetro representa el certificado con el que firma 
 * sus aplicaciones el fabricante del dispositivo *)
Parameter manufacturerCert : Cert.

(* Indica si c es el certificado con el cual a fue firmado *)
Definition appCert (a:idApp) (c:Cert) (s:System) : Prop :=
    (map_apply idApp_eq (cert (environment s)) a = Value idApp c) \/
    (exists sysapp:SysImgApp, In sysapp (systemImage (environment s)) /\ idSI sysapp = a /\ certSI sysapp = c).

(* Indica si c es el certificado con el que fue firmada la
 * aplicación que definió el permiso p *)
Definition certOfDefiner (p:Perm) (c:Cert) (s:System) : Prop :=
    (exists (a:idApp) (lperm:list Perm), map_apply idApp_eq (defPerms (environment s)) a = Value idApp lperm /\
        In p lperm /\
        map_apply idApp_eq (cert (environment s)) a = Value idApp c) \/
    (exists sysapp:SysImgApp, In sysapp (systemImage (environment s)) /\ In p (defPermsSI sysapp) /\ certSI sysapp = c).
    

(* Indica si m es el archivo de manifiesto de a *)
Definition isManifestOfApp (a:idApp) (m:Manifest) (s:System) : Prop :=
(map_apply idApp_eq (manifest (environment s)) a = Value idApp m \/
exists sysapp:SysImgApp,
In sysapp (systemImage (environment s)) /\
idSI sysapp = a /\
manifestSI sysapp = m).

(* Indica si idapp tiene el permiso p en s *)
Definition appHasPermission (idapp:idApp) (p:Perm) (s:System) : Prop :=
    (exists (l:list Perm),
        map_apply idApp_eq (perms (state s)) idapp = Value idApp l /\
        In p l) \/ (* Si tiene el permiso individualmente otorgado o *)
    permExists p s /\
    (exists m:Manifest,
        isManifestOfApp idapp m s /\
        In p (use m)) /\ (* Lo lista como usado y ademas *)
    ((exists lPerm:list Perm, map_apply idApp_eq (defPerms (environment s)) idapp = Value idApp lPerm /\ In p lPerm) \/ (* Lo define el mismo o *)
    pl p=normal \/ (* el permiso es de peligro normal o *)
    ((pl p=signature \/ pl p=signatureOrSys) /\ (* el permiso es de tipo signature o signatureorsys y *)
        (exists c:Cert, appCert idapp c s /\ certOfDefiner p c s)) \/ (* el certificado de la app solicitante coincide con el de quien la define o *)
    (pl p=signatureOrSys /\ (* El permiso es de tipo signatureorsys y *)
        (exists c:Cert, appCert idapp c s /\ c=manufacturerCert) (* la aplicacion solicitante es de sistema *)
    )
    ).


End PermissionCheck.
