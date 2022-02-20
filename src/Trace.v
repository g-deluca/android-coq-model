(* En este archivo se define la función trace, que aplica sucesivamente
* step a partir de una lista de acciones *)
Require Export Implementacion.
Require Export Estado.
Require Export Operaciones.
Require Export RuntimePermissions.
Require Export Semantica.

Section Trace.
Function trace (s:System) (actions:list Action) {struct actions} : list System :=
    match actions with
    | nil => nil
    | action::rest => let sys := (system (step s action)) in (sys :: trace sys rest)
    end.
End Trace.

Extraction Language Haskell.

(* Extraccio'n de tipos sacada de https://coq.inria.fr/library/Coq.extraction.ExtrHaskellBasic.html *)
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive option => "Prelude.Maybe" [ "Prelude.Just" "Prelude.Nothing" ].
Extract Inductive unit => "()" [ "()" ].
Extract Inductive list => "([])" [ "([])" "(:)" ].
Extract Inductive prod => "(,)" [ "(,)" ].

Extract Inductive sumbool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive sumor => "Prelude.Maybe" [ "Prelude.Just" "Prelude.Nothing" ].
Extract Inductive sum => "Prelude.Either" [ "Prelude.Left" "Prelude.Right" ].

Extract Inlined Constant andb => "(Prelude.&&)".
Extract Inlined Constant orb => "(Prelude.||)".
Extract Inlined Constant negb => "Prelude.not".

(* Tipos comparables *)

Extract Constant idPerm => "Prelude.Int".
Extract Constant idPerm_eq => "\x y -> x Prelude.== y".
Extract Constant idGrp => "Prelude.Int".
Extract Constant idGrp_eq => "\x y -> x Prelude.== y".
Extract Constant idCmp => "Prelude.Int".
Extract Constant idCmp_eq => "\x y -> x Prelude.== y". 
Extract Constant uri => "Prelude.String".  
Extract Constant uri_eq => "\x y -> x Prelude.== y". 
Extract Constant res => "Prelude.Int". 
Extract Constant res_eq => "\x y -> x Prelude.== y". 
Extract Constant mimeType => "Prelude.Int". 
Extract Constant mimeType_eq => "\x y -> x Prelude.== y". 
Extract Constant Category => "Prelude.Int". 
Extract Constant Category_eq => "\x y -> x Prelude.== y". 
Extract Constant iCmp => "Prelude.Int". 
Extract Constant iCmp_eq => "\x y -> x Prelude.== y". 
Extract Constant idApp => "Prelude.String".  
Extract Constant idApp_eq => "\x y -> x Prelude.== y". 
Extract Constant Cert => "Prelude.String". 
Extract Constant Cert_eq => "\x y -> x Prelude.== y". 
Extract Constant idInt => "Prelude.Int". 
Extract Constant idInt_eq => "\x y -> x Prelude.== y". 
Extract Constant Extra => "Prelude.Int". 
Extract Constant Extra_eq => "\x y -> x Prelude.== y". 
Extract Constant Flag => "Prelude.Int". 
Extract Constant Flag_eq => "\x y -> x Prelude.== y". 

(* Tipos no necesariamente comparables *)
Extract Constant Val => "Prelude.String".
Extract Constant SACall => "Prelude.String".

(* Constantes *)
Extract Constant manufacturerCert => """ManufacturerCert""". (* Certificado del fabricante *)
Extract Constant initVal => """""". (* Valor inicial de los recursos *)
(* intentActionType?? *)
Extract Constant systemPerms => "[]". (* Permisos del sistema *)
Extract Constant defaultApp => """""". (* Aplicacio'n por defecto. Quizas hasta seri'a mejor dejarlo vaci'o *)
Extract Constant defaultCert => """""". (* Certificado por defecto. Quizas hasta seri'a mejor dejarlo vaci'o *)
Extract Constant defaultiCmp => "0". (* id de instancia corriendo por defecto. Quizas hasta seri'a mejor dejarlo vaci'o *)
Extract Constant defaultCmpId => "0". (* id de componente por defecto. Quizas hasta seri'a mejor dejarlo vaci'o *)
Extract Constant iCmpGenerator => "\used -> Prelude.maximum used Prelude.+ 1 ". (* Generador de ids de componente. Te dara' un nu'mero que no este' en la lista pasada como para'metro *)
Extract Constant getMandatoryPerms => "\_ -> []". (* Ninguna llamada al sistema esta protegida por permisos de sistema. De hecho no existen permisos de sistema. Adaptar a gusto *)



Extraction "CertAndroidSec" trace.
