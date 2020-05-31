module CertAndroidSec where

import qualified Prelude

__ :: any
__ = Prelude.error "Logical or arity value used"

bool_rect :: a1 -> a1 -> Prelude.Bool -> a1
bool_rect f f0 b =
  case b of {
   Prelude.True -> f;
   Prelude.False -> f0}

bool_rec :: a1 -> a1 -> Prelude.Bool -> a1
bool_rec =
  bool_rect

data Nat =
   O
 | S Nat

option_rect :: (a1 -> a2) -> a2 -> (Prelude.Maybe a1) -> a2
option_rect f f0 o =
  case o of {
   Prelude.Just x -> f x;
   Prelude.Nothing -> f0}

option_rec :: (a1 -> a2) -> a2 -> (Prelude.Maybe a1) -> a2
option_rec =
  option_rect

prod_rect :: (a1 -> a2 -> a3) -> ((,) a1 a2) -> a3
prod_rect f p =
  case p of {
   (,) x x0 -> f x x0}

prod_rec :: (a1 -> a2 -> a3) -> ((,) a1 a2) -> a3
prod_rec =
  prod_rect

fst :: ((,) a1 a2) -> a1
fst p =
  case p of {
   (,) x _ -> x}

snd :: ((,) a1 a2) -> a2
snd p =
  case p of {
   (,) _ y -> y}

list_rect :: a2 -> (a1 -> (([]) a1) -> a2 -> a2) -> (([]) a1) -> a2
list_rect f f0 l =
  case l of {
   ([]) -> f;
   (:) y l0 -> f0 y l0 (list_rect f f0 l0)}

list_rec :: a2 -> (a1 -> (([]) a1) -> a2 -> a2) -> (([]) a1) -> a2
list_rec =
  list_rect

app :: (([]) a1) -> (([]) a1) -> ([]) a1
app l m =
  case l of {
   ([]) -> m;
   (:) a l1 -> (:) a (app l1 m)}

sumbool_rect :: (() -> a1) -> (() -> a1) -> Prelude.Bool -> a1
sumbool_rect f f0 s =
  case s of {
   Prelude.True -> f __;
   Prelude.False -> f0 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Prelude.Bool -> a1
sumbool_rec =
  sumbool_rect

leb :: Nat -> Nat -> Prelude.Bool
leb n m =
  case n of {
   O -> Prelude.True;
   S n' ->
    case m of {
     O -> Prelude.False;
     S m' -> leb n' m'}}

ltb :: Nat -> Nat -> Prelude.Bool
ltb n m =
  leb (S n) m

hd :: a1 -> (([]) a1) -> a1
hd default0 l =
  case l of {
   ([]) -> default0;
   (:) x _ -> x}

remove :: (a1 -> a1 -> Prelude.Bool) -> a1 -> (([]) a1) -> ([]) a1
remove eq_dec x l =
  case l of {
   ([]) -> ([]);
   (:) y tl ->
    case eq_dec x y of {
     Prelude.True -> remove eq_dec x tl;
     Prelude.False -> (:) y (remove eq_dec x tl)}}

map :: (a1 -> a2) -> (([]) a1) -> ([]) a2
map f l =
  case l of {
   ([]) -> ([]);
   (:) a t -> (:) (f a) (map f t)}

fold_right :: (a2 -> a1 -> a1) -> a1 -> (([]) a2) -> a1
fold_right f a0 l =
  case l of {
   ([]) -> a0;
   (:) b t -> f b (fold_right f a0 t)}

existsb :: (a1 -> Prelude.Bool) -> (([]) a1) -> Prelude.Bool
existsb f l =
  case l of {
   ([]) -> Prelude.False;
   (:) a l0 -> (Prelude.||) (f a) (existsb f l0)}

filter :: (a1 -> Prelude.Bool) -> (([]) a1) -> ([]) a1
filter f l =
  case l of {
   ([]) -> ([]);
   (:) x l0 ->
    case f x of {
     Prelude.True -> (:) x (filter f l0);
     Prelude.False -> filter f l0}}

data Exc v e =
   Value v
 | Error e

is_ValueBool :: (Exc a1 a2) -> Prelude.Bool
is_ValueBool e =
  case e of {
   Value _ -> Prelude.True;
   Error _ -> Prelude.False}

data Item0 index info =
   Item index info

item_index :: (Item0 a1 a2) -> a1
item_index i =
  case i of {
   Item item_index0 _ -> item_index0}

item_info :: (Item0 a1 a2) -> a2
item_info i =
  case i of {
   Item _ item_info0 -> item_info0}

type Mapping index info = ([]) (Item0 index info)

map_empty :: Mapping a1 a2
map_empty =
  ([])

map_add :: (a1 -> a1 -> Prelude.Bool) -> (Mapping a1 a2) -> a1 -> a2 ->
           Mapping a1 a2
map_add index_eq mp idx inf =
  let {newit = Item idx inf} in
  case mp of {
   ([]) -> (:) newit map_empty;
   (:) it mp1 ->
    case index_eq (item_index it) idx of {
     Prelude.True -> (:) newit mp1;
     Prelude.False -> (:) it (map_add index_eq mp1 idx inf)}}

map_apply :: (a1 -> a1 -> Prelude.Bool) -> (Mapping a1 a2) -> a1 -> Exc a2 a1
map_apply index_eq mp idx =
  case mp of {
   ([]) -> Error idx;
   (:) it mp1 ->
    case index_eq idx (item_index it) of {
     Prelude.True -> Value (item_info it);
     Prelude.False -> map_apply index_eq mp1 idx}}

map_drop :: (a1 -> a1 -> Prelude.Bool) -> (Mapping a1 a2) -> a1 -> Mapping 
            a1 a2
map_drop index_eq mp idx =
  case mp of {
   ([]) -> ([]);
   (:) it mp1 ->
    case index_eq idx (item_index it) of {
     Prelude.True -> map_drop index_eq mp1 idx;
     Prelude.False -> (:) it (map_drop index_eq mp1 idx)}}

map_getKeys :: (Mapping a1 a2) -> ([]) a1
map_getKeys mp =
  map (\item -> item_index item) mp

type IdPerm = Prelude.Int

idPerm_eq :: IdPerm -> IdPerm -> Prelude.Bool
idPerm_eq = \x y -> x Prelude.== y

type IdGrp = Prelude.Int

idGrp_eq :: IdGrp -> IdGrp -> Prelude.Bool
idGrp_eq = \x y -> x Prelude.== y

data PermLevel =
   Dangerous
 | Normal
 | Signature
 | SignatureOrSys

permLevel_rect :: a1 -> a1 -> a1 -> a1 -> PermLevel -> a1
permLevel_rect f f0 f1 f2 p =
  case p of {
   Dangerous -> f;
   Normal -> f0;
   Signature -> f1;
   SignatureOrSys -> f2}

permLevel_rec :: a1 -> a1 -> a1 -> a1 -> PermLevel -> a1
permLevel_rec =
  permLevel_rect

data Perm0 =
   Perm IdPerm (Prelude.Maybe IdGrp) PermLevel

idP :: Perm0 -> IdPerm
idP p =
  case p of {
   Perm idP0 _ _ -> idP0}

maybeGrp :: Perm0 -> Prelude.Maybe IdGrp
maybeGrp p =
  case p of {
   Perm _ maybeGrp0 _ -> maybeGrp0}

pl :: Perm0 -> PermLevel
pl p =
  case p of {
   Perm _ _ pl0 -> pl0}

type IdCmp = Prelude.Int

idCmp_eq :: IdCmp -> IdCmp -> Prelude.Bool
idCmp_eq = \x y -> x Prelude.== y

type Uri = Prelude.String

uri_eq :: Uri -> Uri -> Prelude.Bool
uri_eq = \x y -> x Prelude.== y

type Res = Prelude.Int

res_eq :: Res -> Res -> Prelude.Bool
res_eq = \x y -> x Prelude.== y

type MimeType = Prelude.Int

mimeType_eq :: MimeType -> MimeType -> Prelude.Bool
mimeType_eq = \x y -> x Prelude.== y

data DataType =
   Content
 | File
 | Other

dataType_rect :: a1 -> a1 -> a1 -> DataType -> a1
dataType_rect f f0 f1 d =
  case d of {
   Content -> f;
   File -> f0;
   Other -> f1}

dataType_rec :: a1 -> a1 -> a1 -> DataType -> a1
dataType_rec =
  dataType_rect

data Data =
   Dt (Prelude.Maybe Uri) (Prelude.Maybe MimeType) DataType

path :: Data -> Prelude.Maybe Uri
path d =
  case d of {
   Dt path0 _ _ -> path0}

mime :: Data -> Prelude.Maybe MimeType
mime d =
  case d of {
   Dt _ mime0 _ -> mime0}

type0 :: Data -> DataType
type0 d =
  case d of {
   Dt _ _ type1 -> type1}

type Category = Prelude.Int

category_eq :: Category -> Category -> Prelude.Bool
category_eq = \x y -> x Prelude.== y

data IntentAction =
   ActivityAction
 | ServiceAction
 | BroadcastAction

intentAction_rect :: a1 -> a1 -> a1 -> IntentAction -> a1
intentAction_rect f f0 f1 i =
  case i of {
   ActivityAction -> f;
   ServiceAction -> f0;
   BroadcastAction -> f1}

intentAction_rec :: a1 -> a1 -> a1 -> IntentAction -> a1
intentAction_rec =
  intentAction_rect

data IntentFilter =
   IFilter (([]) IntentAction) (([]) Data) (([]) Category)

actFilter :: IntentFilter -> ([]) IntentAction
actFilter i =
  case i of {
   IFilter actFilter0 _ _ -> actFilter0}

dataFilter :: IntentFilter -> ([]) Data
dataFilter i =
  case i of {
   IFilter _ dataFilter0 _ -> dataFilter0}

catFilter :: IntentFilter -> ([]) Category
catFilter i =
  case i of {
   IFilter _ _ catFilter0 -> catFilter0}

data Activity0 =
   Activity IdCmp (Prelude.Maybe Prelude.Bool) (Prelude.Maybe Perm0) 
 (([]) IntentFilter)

idA :: Activity0 -> IdCmp
idA a =
  case a of {
   Activity idA0 _ _ _ -> idA0}

expA :: Activity0 -> Prelude.Maybe Prelude.Bool
expA a =
  case a of {
   Activity _ expA0 _ _ -> expA0}

cmpEA :: Activity0 -> Prelude.Maybe Perm0
cmpEA a =
  case a of {
   Activity _ _ cmpEA0 _ -> cmpEA0}

intFilterA :: Activity0 -> ([]) IntentFilter
intFilterA a =
  case a of {
   Activity _ _ _ intFilterA0 -> intFilterA0}

data Service0 =
   Service IdCmp (Prelude.Maybe Prelude.Bool) (Prelude.Maybe Perm0) (([])
                                                                    IntentFilter)

idS :: Service0 -> IdCmp
idS s =
  case s of {
   Service idS0 _ _ _ -> idS0}

expS :: Service0 -> Prelude.Maybe Prelude.Bool
expS s =
  case s of {
   Service _ expS0 _ _ -> expS0}

cmpES :: Service0 -> Prelude.Maybe Perm0
cmpES s =
  case s of {
   Service _ _ cmpES0 _ -> cmpES0}

intFilterS :: Service0 -> ([]) IntentFilter
intFilterS s =
  case s of {
   Service _ _ _ intFilterS0 -> intFilterS0}

data BroadReceiver =
   Broadreceiver IdCmp (Prelude.Maybe Prelude.Bool) (Prelude.Maybe Perm0) 
 (([]) IntentFilter)

idB :: BroadReceiver -> IdCmp
idB b =
  case b of {
   Broadreceiver idB0 _ _ _ -> idB0}

expB :: BroadReceiver -> Prelude.Maybe Prelude.Bool
expB b =
  case b of {
   Broadreceiver _ expB0 _ _ -> expB0}

cmpEB :: BroadReceiver -> Prelude.Maybe Perm0
cmpEB b =
  case b of {
   Broadreceiver _ _ cmpEB0 _ -> cmpEB0}

intFilterB :: BroadReceiver -> ([]) IntentFilter
intFilterB b =
  case b of {
   Broadreceiver _ _ _ intFilterB0 -> intFilterB0}

data CProvider =
   Cprovider IdCmp (Mapping Uri Res) (Prelude.Maybe Prelude.Bool) (Prelude.Maybe
                                                                  Perm0) 
 (Prelude.Maybe Perm0) (Prelude.Maybe Perm0) Prelude.Bool (([]) Uri)

idC :: CProvider -> IdCmp
idC c =
  case c of {
   Cprovider idC0 _ _ _ _ _ _ _ -> idC0}

map_res :: CProvider -> Mapping Uri Res
map_res c =
  case c of {
   Cprovider _ map_res0 _ _ _ _ _ _ -> map_res0}

expC :: CProvider -> Prelude.Maybe Prelude.Bool
expC c =
  case c of {
   Cprovider _ _ expC0 _ _ _ _ _ -> expC0}

cmpEC :: CProvider -> Prelude.Maybe Perm0
cmpEC c =
  case c of {
   Cprovider _ _ _ cmpEC0 _ _ _ _ -> cmpEC0}

readE :: CProvider -> Prelude.Maybe Perm0
readE c =
  case c of {
   Cprovider _ _ _ _ readE0 _ _ _ -> readE0}

writeE :: CProvider -> Prelude.Maybe Perm0
writeE c =
  case c of {
   Cprovider _ _ _ _ _ writeE0 _ _ -> writeE0}

grantU :: CProvider -> Prelude.Bool
grantU c =
  case c of {
   Cprovider _ _ _ _ _ _ grantU0 _ -> grantU0}

uriP :: CProvider -> ([]) Uri
uriP c =
  case c of {
   Cprovider _ _ _ _ _ _ _ uriP0 -> uriP0}

data Cmp =
   CmpAct Activity0
 | CmpSrv Service0
 | CmpCP CProvider
 | CmpBR BroadReceiver

cmp_rect :: (Activity0 -> a1) -> (Service0 -> a1) -> (CProvider -> a1) ->
            (BroadReceiver -> a1) -> Cmp -> a1
cmp_rect f f0 f1 f2 c =
  case c of {
   CmpAct x -> f x;
   CmpSrv x -> f0 x;
   CmpCP x -> f1 x;
   CmpBR x -> f2 x}

cmp_rec :: (Activity0 -> a1) -> (Service0 -> a1) -> (CProvider -> a1) ->
           (BroadReceiver -> a1) -> Cmp -> a1
cmp_rec =
  cmp_rect

type ICmp = Prelude.Int

iCmp_eq :: ICmp -> ICmp -> Prelude.Bool
iCmp_eq = \x y -> x Prelude.== y

type IdApp = Prelude.String

idApp_eq :: IdApp -> IdApp -> Prelude.Bool
idApp_eq = \x y -> x Prelude.== y

type Cert = Prelude.String

cert_eq :: Cert -> Cert -> Prelude.Bool
cert_eq = \x y -> x Prelude.== y

data Manifest =
   Mf (([]) Cmp) (Prelude.Maybe Nat) (Prelude.Maybe Nat) (([]) IdPerm) 
 (([]) Perm0) (Prelude.Maybe Perm0)

cmp :: Manifest -> ([]) Cmp
cmp m =
  case m of {
   Mf cmp0 _ _ _ _ _ -> cmp0}

minSdk :: Manifest -> Prelude.Maybe Nat
minSdk m =
  case m of {
   Mf _ minSdk0 _ _ _ _ -> minSdk0}

targetSdk :: Manifest -> Prelude.Maybe Nat
targetSdk m =
  case m of {
   Mf _ _ targetSdk0 _ _ _ -> targetSdk0}

use :: Manifest -> ([]) IdPerm
use m =
  case m of {
   Mf _ _ _ use0 _ _ -> use0}

usrP :: Manifest -> ([]) Perm0
usrP m =
  case m of {
   Mf _ _ _ _ usrP0 _ -> usrP0}

appE :: Manifest -> Prelude.Maybe Perm0
appE m =
  case m of {
   Mf _ _ _ _ _ appE0 -> appE0}

data SysImgApp =
   Siapp IdApp Cert Manifest (([]) Perm0) (([]) Res)

idSI :: SysImgApp -> IdApp
idSI s =
  case s of {
   Siapp idSI0 _ _ _ _ -> idSI0}

certSI :: SysImgApp -> Cert
certSI s =
  case s of {
   Siapp _ certSI0 _ _ _ -> certSI0}

manifestSI :: SysImgApp -> Manifest
manifestSI s =
  case s of {
   Siapp _ _ manifestSI0 _ _ -> manifestSI0}

defPermsSI :: SysImgApp -> ([]) Perm0
defPermsSI s =
  case s of {
   Siapp _ _ _ defPermsSI0 _ -> defPermsSI0}

type IdInt = Prelude.Int

idInt_eq :: IdInt -> IdInt -> Prelude.Bool
idInt_eq = \x y -> x Prelude.== y

type Extra = Prelude.Int

extra_eq :: Extra -> Extra -> Prelude.Bool
extra_eq = \x y -> x Prelude.== y

type Flag = Prelude.Int

flag_eq :: Flag -> Flag -> Prelude.Bool
flag_eq = \x y -> x Prelude.== y

data IntentType =
   IntActivity
 | IntService
 | IntBroadcast

intentType_rect :: a1 -> a1 -> a1 -> IntentType -> a1
intentType_rect f f0 f1 i =
  case i of {
   IntActivity -> f;
   IntService -> f0;
   IntBroadcast -> f1}

intentType_rec :: a1 -> a1 -> a1 -> IntentType -> a1
intentType_rec =
  intentType_rect

data Intent0 =
   Intent IdInt (Prelude.Maybe IdCmp) IntentType (Prelude.Maybe IntentAction) 
 Data (([]) Category) (Prelude.Maybe Extra) (Prelude.Maybe Flag) (Prelude.Maybe
                                                                 Perm0)

idI :: Intent0 -> IdInt
idI i =
  case i of {
   Intent idI0 _ _ _ _ _ _ _ _ -> idI0}

cmpName :: Intent0 -> Prelude.Maybe IdCmp
cmpName i =
  case i of {
   Intent _ cmpName0 _ _ _ _ _ _ _ -> cmpName0}

intType :: Intent0 -> IntentType
intType i =
  case i of {
   Intent _ _ intType0 _ _ _ _ _ _ -> intType0}

action :: Intent0 -> Prelude.Maybe IntentAction
action i =
  case i of {
   Intent _ _ _ action0 _ _ _ _ _ -> action0}

data0 :: Intent0 -> Data
data0 i =
  case i of {
   Intent _ _ _ _ data1 _ _ _ _ -> data1}

category :: Intent0 -> ([]) Category
category i =
  case i of {
   Intent _ _ _ _ _ category0 _ _ _ -> category0}

extra :: Intent0 -> Prelude.Maybe Extra
extra i =
  case i of {
   Intent _ _ _ _ _ _ extra0 _ _ -> extra0}

flags :: Intent0 -> Prelude.Maybe Flag
flags i =
  case i of {
   Intent _ _ _ _ _ _ _ flags0 _ -> flags0}

brperm :: Intent0 -> Prelude.Maybe Perm0
brperm i =
  case i of {
   Intent _ _ _ _ _ _ _ _ brperm0 -> brperm0}

data PType =
   Read
 | Write
 | Both

type Val = Prelude.String

type SACall = Prelude.String

vulnerableSdk :: Nat
vulnerableSdk =
  Prelude.error "AXIOM TO BE REALIZED"

permLevel_eq :: PermLevel -> PermLevel -> Prelude.Bool
permLevel_eq id1 id2 =
  permLevel_rec (\id0 ->
    case id0 of {
     Dangerous -> Prelude.True;
     _ -> Prelude.False}) (\id0 ->
    case id0 of {
     Normal -> Prelude.True;
     _ -> Prelude.False}) (\id0 ->
    case id0 of {
     Signature -> Prelude.True;
     _ -> Prelude.False}) (\id0 ->
    case id0 of {
     SignatureOrSys -> Prelude.True;
     _ -> Prelude.False}) id1 id2

option_eq :: (a1 -> a1 -> Prelude.Bool) -> (Prelude.Maybe a1) ->
             (Prelude.Maybe a1) -> Prelude.Bool
option_eq aeq id1 id2 =
  option_rec (\a id0 ->
    case id0 of {
     Prelude.Just a0 ->
      sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (aeq a a0);
     Prelude.Nothing -> Prelude.False}) (\id0 ->
    case id0 of {
     Prelude.Just _ -> Prelude.False;
     Prelude.Nothing -> Prelude.True}) id1 id2

perm_eq :: Perm0 -> Perm0 -> Prelude.Bool
perm_eq id1 id2 =
  case id1 of {
   Perm idP0 maybeGrp0 pl0 ->
    case id2 of {
     Perm idP1 maybeGrp1 pl1 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ ->
          sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
            (permLevel_eq pl0 pl1)) (\_ -> Prelude.False)
          (option_eq idGrp_eq maybeGrp0 maybeGrp1)) (\_ -> Prelude.False)
        (idPerm_eq idP0 idP1)}}

dataType_eq :: DataType -> DataType -> Prelude.Bool
dataType_eq id1 id2 =
  dataType_rec (\id0 ->
    case id0 of {
     Content -> Prelude.True;
     _ -> Prelude.False}) (\id0 ->
    case id0 of {
     File -> Prelude.True;
     _ -> Prelude.False}) (\id0 ->
    case id0 of {
     Other -> Prelude.True;
     _ -> Prelude.False}) id1 id2

data_eq :: Data -> Data -> Prelude.Bool
data_eq id1 id2 =
  case id1 of {
   Dt path0 mime0 type1 ->
    case id2 of {
     Dt path1 mime1 type2 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ ->
          sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
            (dataType_eq type1 type2)) (\_ -> Prelude.False)
          (option_eq mimeType_eq mime0 mime1)) (\_ -> Prelude.False)
        (option_eq uri_eq path0 path1)}}

list_eq :: (a1 -> a1 -> Prelude.Bool) -> (([]) a1) -> (([]) a1) ->
           Prelude.Bool
list_eq aeq id1 id2 =
  list_rec (\id0 ->
    case id0 of {
     ([]) -> Prelude.True;
     (:) _ _ -> Prelude.False}) (\a _ h id0 ->
    case id0 of {
     ([]) -> Prelude.False;
     (:) a0 l0 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (h l0)) (\_ ->
        Prelude.False) (aeq a a0)}) id1 id2

intentAction_eq :: IntentAction -> IntentAction -> Prelude.Bool
intentAction_eq id1 id2 =
  intentAction_rec (\id0 ->
    case id0 of {
     ActivityAction -> Prelude.True;
     _ -> Prelude.False}) (\id0 ->
    case id0 of {
     ServiceAction -> Prelude.True;
     _ -> Prelude.False}) (\id0 ->
    case id0 of {
     BroadcastAction -> Prelude.True;
     _ -> Prelude.False}) id1 id2

bool_eq :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
bool_eq id1 id2 =
  bool_rec (\id0 ->
    case id0 of {
     Prelude.True -> Prelude.True;
     Prelude.False -> Prelude.False}) (\id0 ->
    case id0 of {
     Prelude.True -> Prelude.False;
     Prelude.False -> Prelude.True}) id1 id2

item_eq :: (a1 -> a1 -> Prelude.Bool) -> (a2 -> a2 -> Prelude.Bool) -> (Item0
           a1 a2) -> (Item0 a1 a2) -> Prelude.Bool
item_eq aeq beq id1 id2 =
  case id1 of {
   Item item_index0 item_info0 ->
    case id2 of {
     Item item_index1 item_info1 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
          (beq item_info0 item_info1)) (\_ -> Prelude.False)
        (aeq item_index0 item_index1)}}

map_eq :: (a1 -> a1 -> Prelude.Bool) -> (a2 -> a2 -> Prelude.Bool) ->
          (Mapping a1 a2) -> (Mapping a1 a2) -> Prelude.Bool
map_eq aeq beq id1 id2 =
  list_rec (\id0 ->
    case id0 of {
     ([]) -> Prelude.True;
     (:) _ _ -> Prelude.False}) (\a _ h id0 ->
    case id0 of {
     ([]) -> Prelude.False;
     (:) i l0 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (h l0)) (\_ ->
        Prelude.False) (item_eq aeq beq a i)}) id1 id2

cProvider_eq :: CProvider -> CProvider -> Prelude.Bool
cProvider_eq id1 id2 =
  case id1 of {
   Cprovider idC0 map_res0 expC0 cmpEC0 readE0 writeE0 grantU0 uriP0 ->
    case id2 of {
     Cprovider idC1 map_res1 expC1 cmpEC1 readE1 writeE1 grantU1 uriP1 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ ->
          sumbool_rec (\_ ->
            sumbool_rec (\_ ->
              sumbool_rec (\_ ->
                sumbool_rec (\_ ->
                  sumbool_rec (\_ ->
                    sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
                      (list_eq uri_eq uriP0 uriP1)) (\_ -> Prelude.False)
                    (bool_eq grantU0 grantU1)) (\_ -> Prelude.False)
                  (option_eq perm_eq writeE0 writeE1)) (\_ -> Prelude.False)
                (option_eq perm_eq readE0 readE1)) (\_ -> Prelude.False)
              (option_eq perm_eq cmpEC0 cmpEC1)) (\_ -> Prelude.False)
            (option_eq bool_eq expC0 expC1)) (\_ -> Prelude.False)
          (map_eq uri_eq res_eq map_res0 map_res1)) (\_ -> Prelude.False)
        (idCmp_eq idC0 idC1)}}

intentType_eq :: IntentType -> IntentType -> Prelude.Bool
intentType_eq id1 id2 =
  intentType_rec (\id0 ->
    case id0 of {
     IntActivity -> Prelude.True;
     _ -> Prelude.False}) (\id0 ->
    case id0 of {
     IntService -> Prelude.True;
     _ -> Prelude.False}) (\id0 ->
    case id0 of {
     IntBroadcast -> Prelude.True;
     _ -> Prelude.False}) id1 id2

intent_eq :: Intent0 -> Intent0 -> Prelude.Bool
intent_eq id1 id2 =
  case id1 of {
   Intent idI0 cmpName0 intType0 action0 data1 category0 extra0 flags0
    brperm0 ->
    case id2 of {
     Intent idI1 cmpName1 intType1 action1 data2 category1 extra1 flags1
      brperm1 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ ->
          sumbool_rec (\_ ->
            sumbool_rec (\_ ->
              sumbool_rec (\_ ->
                sumbool_rec (\_ ->
                  sumbool_rec (\_ ->
                    sumbool_rec (\_ ->
                      sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
                        (option_eq perm_eq brperm0 brperm1)) (\_ ->
                      Prelude.False) (option_eq flag_eq flags0 flags1))
                    (\_ -> Prelude.False) (option_eq extra_eq extra0 extra1))
                  (\_ -> Prelude.False)
                  (list_eq category_eq category0 category1)) (\_ ->
                Prelude.False) (data_eq data1 data2)) (\_ -> Prelude.False)
              (option_eq intentAction_eq action0 action1)) (\_ ->
            Prelude.False) (intentType_eq intType0 intType1)) (\_ ->
          Prelude.False) (option_eq idCmp_eq cmpName0 cmpName1)) (\_ ->
        Prelude.False) (idInt_eq idI0 idI1)}}

intentFilter_eq :: IntentFilter -> IntentFilter -> Prelude.Bool
intentFilter_eq id1 id2 =
  case id1 of {
   IFilter actFilter0 dataFilter0 catFilter0 ->
    case id2 of {
     IFilter actFilter1 dataFilter1 catFilter1 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ ->
          sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
            (list_eq category_eq catFilter0 catFilter1)) (\_ ->
          Prelude.False) (list_eq data_eq dataFilter0 dataFilter1)) (\_ ->
        Prelude.False) (list_eq intentAction_eq actFilter0 actFilter1)}}

activity_eq :: Activity0 -> Activity0 -> Prelude.Bool
activity_eq id1 id2 =
  case id1 of {
   Activity idA0 expA0 cmpEA0 intFilterA0 ->
    case id2 of {
     Activity idA1 expA1 cmpEA1 intFilterA1 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ ->
          sumbool_rec (\_ ->
            sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
              (list_eq intentFilter_eq intFilterA0 intFilterA1)) (\_ ->
            Prelude.False) (option_eq perm_eq cmpEA0 cmpEA1)) (\_ ->
          Prelude.False) (option_eq bool_eq expA0 expA1)) (\_ ->
        Prelude.False) (idCmp_eq idA0 idA1)}}

service_eq :: Service0 -> Service0 -> Prelude.Bool
service_eq id1 id2 =
  case id1 of {
   Service idS0 expS0 cmpES0 intFilterS0 ->
    case id2 of {
     Service idS1 expS1 cmpES1 intFilterS1 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ ->
          sumbool_rec (\_ ->
            sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
              (list_eq intentFilter_eq intFilterS0 intFilterS1)) (\_ ->
            Prelude.False) (option_eq perm_eq cmpES0 cmpES1)) (\_ ->
          Prelude.False) (option_eq bool_eq expS0 expS1)) (\_ ->
        Prelude.False) (idCmp_eq idS0 idS1)}}

broadReceiver_eq :: BroadReceiver -> BroadReceiver -> Prelude.Bool
broadReceiver_eq id1 id2 =
  case id1 of {
   Broadreceiver idB0 expB0 cmpEB0 intFilterB0 ->
    case id2 of {
     Broadreceiver idB1 expB1 cmpEB1 intFilterB1 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ ->
          sumbool_rec (\_ ->
            sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
              (list_eq intentFilter_eq intFilterB0 intFilterB1)) (\_ ->
            Prelude.False) (option_eq perm_eq cmpEB0 cmpEB1)) (\_ ->
          Prelude.False) (option_eq bool_eq expB0 expB1)) (\_ ->
        Prelude.False) (idCmp_eq idB0 idB1)}}

cmp_eq :: Cmp -> Cmp -> Prelude.Bool
cmp_eq id1 id2 =
  cmp_rec (\a id0 ->
    case id0 of {
     CmpAct a0 ->
      sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
        (activity_eq a a0);
     _ -> Prelude.False}) (\s id0 ->
    case id0 of {
     CmpSrv s0 ->
      sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
        (service_eq s s0);
     _ -> Prelude.False}) (\c id0 ->
    case id0 of {
     CmpCP c0 ->
      sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
        (cProvider_eq c c0);
     _ -> Prelude.False}) (\b id0 ->
    case id0 of {
     CmpBR b0 ->
      sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
        (broadReceiver_eq b b0);
     _ -> Prelude.False}) id1 id2

sentIntentsElems_eq :: ((,) ICmp Intent0) -> ((,) ICmp Intent0) ->
                       Prelude.Bool
sentIntentsElems_eq id1 id2 =
  prod_rec (\a b id0 ->
    case id0 of {
     (,) i i0 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
          (intent_eq b i0)) (\_ -> Prelude.False) (iCmp_eq a i)}) id1 id2

sentintentseq :: ((,) ICmp Intent0) -> ((,) ICmp Intent0) -> Prelude.Bool
sentintentseq id1 id2 =
  prod_rec (\a b id0 ->
    case id0 of {
     (,) i i0 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
          (intent_eq b i0)) (\_ -> Prelude.False) (iCmp_eq a i)}) id1 id2

delppermsdomeq :: ((,) ((,) IdApp CProvider) Uri) -> ((,)
                  ((,) IdApp CProvider) Uri) -> Prelude.Bool
delppermsdomeq id1 id2 =
  prod_rec (\a b id0 ->
    case id0 of {
     (,) p u ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (uri_eq b u))
        (\_ -> Prelude.False)
        (prod_rec (\a0 b0 p0 ->
          case p0 of {
           (,) i c ->
            sumbool_rec (\_ ->
              sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
                (cProvider_eq b0 c)) (\_ -> Prelude.False) (idApp_eq a0 i)})
          a p)}) id1 id2

deltpermsdomeq :: ((,) ((,) ICmp CProvider) Uri) -> ((,) ((,) ICmp CProvider)
                  Uri) -> Prelude.Bool
deltpermsdomeq id1 id2 =
  prod_rec (\a b id0 ->
    case id0 of {
     (,) p u ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (uri_eq b u))
        (\_ -> Prelude.False)
        (prod_rec (\a0 b0 p0 ->
          case p0 of {
           (,) i c ->
            sumbool_rec (\_ ->
              sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
                (cProvider_eq b0 c)) (\_ -> Prelude.False) (iCmp_eq a0 i)}) a
          p)}) id1 id2

rescontdomeq :: ((,) IdApp Res) -> ((,) IdApp Res) -> Prelude.Bool
rescontdomeq id1 id2 =
  prod_rec (\a b id0 ->
    case id0 of {
     (,) i r ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (res_eq b r))
        (\_ -> Prelude.False) (idApp_eq a i)}) id1 id2

data Environment =
   Env (Mapping IdApp Manifest) (Mapping IdApp Cert) (Mapping IdApp
                                                     (([]) Perm0)) (([])
                                                                   SysImgApp)

manifest :: Environment -> Mapping IdApp Manifest
manifest e =
  case e of {
   Env manifest0 _ _ _ -> manifest0}

cert :: Environment -> Mapping IdApp Cert
cert e =
  case e of {
   Env _ cert0 _ _ -> cert0}

defPerms :: Environment -> Mapping IdApp (([]) Perm0)
defPerms e =
  case e of {
   Env _ _ defPerms0 _ -> defPerms0}

systemImage :: Environment -> ([]) SysImgApp
systemImage e =
  case e of {
   Env _ _ _ systemImage0 -> systemImage0}

data State =
   St (([]) IdApp) (([]) IdApp) (Mapping IdApp (([]) IdGrp)) (Mapping 
                                                             IdApp
                                                             (([]) Perm0)) 
 (Mapping ICmp Cmp) (Mapping ((,) ((,) IdApp CProvider) Uri) PType) (Mapping
                                                                    ((,)
                                                                    ((,) 
                                                                    ICmp
                                                                    CProvider)
                                                                    Uri)
                                                                    PType) 
 (Mapping ((,) IdApp Res) Val) (([]) ((,) ICmp Intent0))

apps :: State -> ([]) IdApp
apps s =
  case s of {
   St apps0 _ _ _ _ _ _ _ _ -> apps0}

alreadyRun :: State -> ([]) IdApp
alreadyRun s =
  case s of {
   St _ alreadyRun0 _ _ _ _ _ _ _ -> alreadyRun0}

grantedPermGroups :: State -> Mapping IdApp (([]) IdGrp)
grantedPermGroups s =
  case s of {
   St _ _ grantedPermGroups0 _ _ _ _ _ _ -> grantedPermGroups0}

perms :: State -> Mapping IdApp (([]) Perm0)
perms s =
  case s of {
   St _ _ _ perms0 _ _ _ _ _ -> perms0}

running :: State -> Mapping ICmp Cmp
running s =
  case s of {
   St _ _ _ _ running0 _ _ _ _ -> running0}

delPPerms :: State -> Mapping ((,) ((,) IdApp CProvider) Uri) PType
delPPerms s =
  case s of {
   St _ _ _ _ _ delPPerms0 _ _ _ -> delPPerms0}

delTPerms :: State -> Mapping ((,) ((,) ICmp CProvider) Uri) PType
delTPerms s =
  case s of {
   St _ _ _ _ _ _ delTPerms0 _ _ -> delTPerms0}

resCont :: State -> Mapping ((,) IdApp Res) Val
resCont s =
  case s of {
   St _ _ _ _ _ _ _ resCont0 _ -> resCont0}

sentIntents :: State -> ([]) ((,) ICmp Intent0)
sentIntents s =
  case s of {
   St _ _ _ _ _ _ _ _ sentIntents0 -> sentIntents0}

data System =
   Sys State Environment

state :: System -> State
state s =
  case s of {
   Sys state0 _ -> state0}

environment :: System -> Environment
environment s =
  case s of {
   Sys _ environment0 -> environment0}

getCmpId :: Cmp -> IdCmp
getCmpId c =
  case c of {
   CmpAct a -> idA a;
   CmpSrv s -> idS s;
   CmpCP cp -> idC cp;
   CmpBR br -> idB br}

data Action =
   Install IdApp Manifest Cert (([]) Res)
 | Uninstall IdApp
 | Grant Perm0 IdApp
 | GrantAuto Perm0 IdApp
 | Revoke Perm0 IdApp
 | RevokePermGroup IdGrp IdApp
 | HasPermission Perm0 Cmp
 | Read0 ICmp CProvider Uri
 | Write0 ICmp CProvider Uri Val
 | StartActivity Intent0 ICmp
 | StartActivityForResult Intent0 Nat ICmp
 | StartService Intent0 ICmp
 | SendBroadcast Intent0 ICmp (Prelude.Maybe Perm0)
 | SendOrderedBroadcast Intent0 ICmp (Prelude.Maybe Perm0)
 | SendStickyBroadcast Intent0 ICmp
 | ResolveIntent Intent0 IdApp
 | ReceiveIntent Intent0 ICmp IdApp
 | Stop ICmp
 | GrantP ICmp CProvider IdApp Uri PType
 | RevokeDel ICmp CProvider Uri PType
 | Call ICmp SACall
 | VerifyOldApp IdApp

manufacturerCert :: Cert
manufacturerCert = "ManufacturerCert"

inBool :: (a1 -> a1 -> Prelude.Bool) -> a1 -> (([]) a1) -> Prelude.Bool
inBool aeq a list =
  existsb (\a' ->
    case aeq a a' of {
     Prelude.True -> Prelude.True;
     Prelude.False -> Prelude.False}) list

has_duplicates :: (a1 -> a1 -> Prelude.Bool) -> (([]) a1) -> Prelude.Bool
has_duplicates aeq list =
  case list of {
   ([]) -> Prelude.False;
   (:) a rest -> (Prelude.||) (inBool aeq a rest) (has_duplicates aeq rest)}

initVal :: Val
initVal = ""

createIntent :: Intent0 -> (Prelude.Maybe Perm0) -> Intent0
createIntent oldIntent p =
  Intent (idI oldIntent) (cmpName oldIntent) (intType oldIntent)
    (action oldIntent) (data0 oldIntent) (category oldIntent)
    (extra oldIntent) (flags oldIntent) p

intentActionType :: Intent0 -> PType
intentActionType =
  Prelude.error "AXIOM TO BE REALIZED"

ptplus :: PType -> PType -> PType
ptplus pt pt' =
  case pt of {
   Read ->
    case pt' of {
     Read -> Read;
     _ -> Both};
   Write ->
    case pt' of {
     Read -> Both;
     x -> x};
   Both -> Both}

ptminus :: PType -> PType -> Prelude.Maybe PType
ptminus pt pt' =
  case pt' of {
   Read ->
    case pt of {
     Read -> Prelude.Nothing;
     _ -> Prelude.Just Write};
   Write ->
    case pt of {
     Write -> Prelude.Nothing;
     _ -> Prelude.Just Read};
   Both -> Prelude.Nothing}

data ErrorCode =
   App_already_installed
 | Duplicated_cmp_id
 | Duplicated_perm_id
 | Cmp_already_defined
 | Perm_already_defined
 | Faulty_intent_filter
 | No_such_app
 | App_is_running
 | Perm_not_in_use
 | No_such_perm
 | Perm_already_granted
 | Perm_not_dangerous
 | Perm_is_grouped
 | Perm_not_grouped
 | Perm_should_auto_grant
 | Cannot_auto_grant
 | Perm_wasnt_granted
 | Group_already_granted
 | Group_not_in_use
 | Group_wasnt_granted
 | No_such_res
 | Incorrect_intent_type
 | Faulty_intent
 | Intent_already_sent
 | No_such_intt
 | Cmp_is_CProvider
 | Instance_not_running
 | A_cant_start_b
 | Not_enough_permissions
 | No_CProvider_fits
 | Should_verify_permissions
 | CProvider_not_grantable

data Response =
   Ok
 | Error0 ErrorCode

concat :: (([]) (([]) a1)) -> ([]) a1
concat l =
  case l of {
   ([]) -> ([]);
   (:) x l0 -> app x (concat l0)}

removeAll :: (a1 -> a1 -> Prelude.Bool) -> (([]) a1) -> (([]) a1) -> ([]) a1
removeAll eq_dec toBeRemoved fromList =
  case toBeRemoved of {
   ([]) -> fromList;
   (:) x toBeRemoved' ->
    remove eq_dec x (removeAll eq_dec toBeRemoved' fromList)}

data Result0 =
   Result Response System

system :: Result0 -> System
system r =
  case r of {
   Result _ system0 -> system0}

getValues :: (([]) (Exc a2 a1)) -> ([]) a2
getValues l =
  case l of {
   ([]) -> ([]);
   (:) e rest ->
    case e of {
     Value a -> (:) a (getValues rest);
     Error _ -> getValues rest}}

getAllComponents :: System -> ([]) Cmp
getAllComponents s =
  let {
   maybeinstalledManifests = map
                               (map_apply idApp_eq
                                 (manifest (environment s))) (apps (state s))}
  in
  let {installedManifests = getValues maybeinstalledManifests} in
  let {installedCmps = map cmp installedManifests} in
  let {
   sysCmps = map (\sysapp -> cmp (manifestSI sysapp))
               (systemImage (environment s))}
  in
  concat (app installedCmps sysCmps)

cmpIdInStateBool :: Cmp -> System -> Prelude.Bool
cmpIdInStateBool c s =
  let {allComponents = getAllComponents s} in
  let {allComponentIds = map getCmpId allComponents} in
  existsb (\cid ->
    case idCmp_eq cid (getCmpId c) of {
     Prelude.True -> Prelude.True;
     Prelude.False -> Prelude.False}) allComponentIds

cmpInStateBool :: Cmp -> System -> Prelude.Bool
cmpInStateBool c s =
  let {allComponents = getAllComponents s} in
  existsb (\c' ->
    case cmp_eq c' c of {
     Prelude.True -> Prelude.True;
     Prelude.False -> Prelude.False}) allComponents

isAppInstalledBool :: IdApp -> System -> Prelude.Bool
isAppInstalledBool a s =
  let {installedAppsIds = apps (state s)} in
  let {
   installedAppsIds0 = app installedAppsIds
                         (map idSI (systemImage (environment s)))}
  in
  inBool idApp_eq a installedAppsIds0

usrDefPerms :: System -> ([]) Perm0
usrDefPerms s =
  let {
   maybeinstalledDefPerms = map
                              (map_apply idApp_eq (defPerms (environment s)))
                              (apps (state s))}
  in
  let {installeddefPerms = getValues maybeinstalledDefPerms} in
  let {sysDefPerms = map defPermsSI (systemImage (environment s))} in
  concat (app installeddefPerms sysDefPerms)

systemPerms :: ([]) Perm0
systemPerms = []

getAllPerms :: System -> ([]) Perm0
getAllPerms s =
  app systemPerms (usrDefPerms s)

isSystemPermBool :: Perm0 -> Prelude.Bool
isSystemPermBool p =
  inBool idPerm_eq (idP p) (map idP systemPerms)

nonSystemUsrP :: Manifest -> ([]) Perm0
nonSystemUsrP m =
  filter (\perm -> Prelude.not (isSystemPermBool perm)) (usrP m)

authPermsBool :: Manifest -> System -> Prelude.Bool
authPermsBool m s =
  Prelude.not
    (existsb (\p ->
      existsb (\p' ->
        case idPerm_eq (idP p') (idP p) of {
         Prelude.True -> Prelude.True;
         Prelude.False -> Prelude.False}) (usrDefPerms s)) (nonSystemUsrP m))

isNil :: (([]) a1) -> Prelude.Bool
isNil l =
  case l of {
   ([]) -> Prelude.True;
   (:) _ _ -> Prelude.False}

isSomethingBool :: (Prelude.Maybe a1) -> Prelude.Bool
isSomethingBool x =
  case x of {
   Prelude.Just _ -> Prelude.True;
   Prelude.Nothing -> Prelude.False}

definesIntentFilterCorrectlyBool :: Cmp -> Prelude.Bool
definesIntentFilterCorrectlyBool cmp0 =
  let {
   theFilters = case cmp0 of {
                 CmpAct a -> intFilterA a;
                 CmpSrv s -> intFilterS s;
                 CmpCP _ -> ([]);
                 CmpBR br -> intFilterB br}}
  in
  Prelude.not
    (existsb (\iFil ->
      (Prelude.&&)
        (Prelude.not
          ((Prelude.&&) (isNil (dataFilter iFil)) (isNil (catFilter iFil))))
        (isNil (actFilter iFil))) theFilters)

definesIntentFilterIncorrectly :: Cmp -> Prelude.Bool
definesIntentFilterIncorrectly cmp0 =
  Prelude.not (definesIntentFilterCorrectlyBool cmp0)

anyDefinesIntentFilterIncorrectly :: (([]) Cmp) -> Prelude.Bool
anyDefinesIntentFilterIncorrectly cmps =
  existsb definesIntentFilterIncorrectly cmps

addAll :: (a1 -> a1 -> Prelude.Bool) -> (([]) ((,) a1 a2)) -> (Mapping 
          a1 a2) -> Mapping a1 a2
addAll indexeq indexAndValues mp =
  fold_right (\pair oldmap -> map_add indexeq oldmap (fst pair) (snd pair))
    mp indexAndValues

dropAll :: (a1 -> a1 -> Prelude.Bool) -> (([]) a1) -> (Mapping a1 a2) ->
           Mapping a1 a2
dropAll indexeq indexes mp =
  fold_right (\i oldmap -> map_drop indexeq oldmap i) mp indexes

addNewResCont :: IdApp -> (Mapping ((,) IdApp Res) Val) -> (([]) Res) ->
                 Mapping ((,) IdApp Res) Val
addNewResCont app0 oldResCont lRes =
  addAll rescontdomeq (map (\r -> (,) ((,) app0 r) initVal) lRes) oldResCont

getRunningCmps :: System -> ([]) Cmp
getRunningCmps s =
  let {keys = map_getKeys (running (state s))} in
  getValues (map (map_apply iCmp_eq (running (state s))) keys)

isCmpRunning :: Cmp -> System -> Prelude.Bool
isCmpRunning c s =
  inBool idCmp_eq (getCmpId c) (map getCmpId (getRunningCmps s))

isAnyCmpRunning :: IdApp -> System -> Prelude.Bool
isAnyCmpRunning app0 s =
  case map_apply idApp_eq (manifest (environment s)) app0 of {
   Value mfst -> existsb (\c -> isCmpRunning c s) (cmp mfst);
   Error _ -> Prelude.False}

fst3 :: ((,) ((,) a1 a2) a3) -> a1
fst3 tuple3 =
  case tuple3 of {
   (,) a _ -> fst a}

snd3 :: ((,) ((,) a1 a2) a3) -> a2
snd3 tuple3 =
  case tuple3 of {
   (,) a _ -> snd a}

isCProviderBool :: Cmp -> Prelude.Bool
isCProviderBool c =
  case c of {
   CmpCP _ -> Prelude.True;
   _ -> Prelude.False}

isActivityBool :: Cmp -> Prelude.Bool
isActivityBool c =
  case c of {
   CmpAct _ -> Prelude.True;
   _ -> Prelude.False}

isServiceBool :: Cmp -> Prelude.Bool
isServiceBool c =
  case c of {
   CmpSrv _ -> Prelude.True;
   _ -> Prelude.False}

isBroadReceiverBool :: Cmp -> Prelude.Bool
isBroadReceiverBool c =
  case c of {
   CmpBR _ -> Prelude.True;
   _ -> Prelude.False}

defaultManifest :: Manifest
defaultManifest =
  Mf ([]) Prelude.Nothing Prelude.Nothing ([]) ([]) Prelude.Nothing

defaultApp :: IdApp
defaultApp = ""

defaultCert :: Cert
defaultCert = ""

defaultSysApp :: SysImgApp
defaultSysApp =
  Siapp defaultApp defaultCert defaultManifest ([]) ([])

getAllCmps :: IdApp -> System -> ([]) Cmp
getAllCmps app0 s =
  case map_apply idApp_eq (manifest (environment s)) app0 of {
   Value m -> cmp m;
   Error _ ->
    cmp
      (manifestSI
        (hd defaultSysApp
          (filter (\sysapp ->
            case idApp_eq app0 (idSI sysapp) of {
             Prelude.True -> Prelude.True;
             Prelude.False -> Prelude.False}) (systemImage (environment s)))))}

getCProviders :: IdApp -> System -> ([]) Cmp
getCProviders app0 s =
  filter isCProviderBool (getAllCmps app0 s)

dropAppPerms :: System -> IdApp -> Mapping IdApp (([]) Perm0)
dropAppPerms oldstate app0 =
  let {
   defPermsApp = case map_apply idApp_eq (defPerms (environment oldstate))
                        app0 of {
                  Value l -> l;
                  Error _ -> ([])}}
  in
  let {theKeys = map_getKeys (perms (state oldstate))} in
  let {
   theKeyVals = map (\key -> (,) key
                  (case map_apply idApp_eq (perms (state oldstate)) key of {
                    Value l ->
                     filter (\p ->
                       Prelude.not (inBool perm_eq p defPermsApp)) l;
                    Error _ -> ([])})) theKeys}
  in
  map_drop idApp_eq (addAll idApp_eq theKeyVals (perms (state oldstate)))
    app0

dropAllPPerms :: System -> IdApp -> Mapping ((,) ((,) IdApp CProvider) Uri)
                 PType
dropAllPPerms s app0 =
  let {appCProviders = getCProviders app0 s} in
  let {oldpperms = delPPerms (state s)} in
  let {
   filteredkeys = filter (\tuple3 ->
                    case idApp_eq (fst3 tuple3) app0 of {
                     Prelude.True -> Prelude.True;
                     Prelude.False ->
                      inBool cmp_eq (CmpCP (snd3 tuple3)) appCProviders})
                    (map_getKeys oldpperms)}
  in
  dropAll delppermsdomeq filteredkeys oldpperms

dropAllTPerms :: System -> IdApp -> Mapping ((,) ((,) ICmp CProvider) Uri)
                 PType
dropAllTPerms s app0 =
  let {appCProviders = getCProviders app0 s} in
  let {oldtperms = delTPerms (state s)} in
  let {
   filteredkeys = filter (\tuple3 ->
                    inBool cmp_eq (CmpCP (snd3 tuple3)) appCProviders)
                    (map_getKeys oldtperms)}
  in
  dropAll deltpermsdomeq filteredkeys oldtperms

dropAllRes :: (Mapping ((,) IdApp Res) Val) -> IdApp -> Mapping
              ((,) IdApp Res) Val
dropAllRes resCont0 app0 =
  let {
   filteredkeys = filter (\pair ->
                    case idApp_eq app0 (fst pair) of {
                     Prelude.True -> Prelude.True;
                     Prelude.False -> Prelude.False}) (map_getKeys resCont0)}
  in
  dropAll rescontdomeq filteredkeys resCont0

permsInUse :: IdApp -> System -> ([]) IdPerm
permsInUse app0 s =
  case map_apply idApp_eq (manifest (environment s)) app0 of {
   Value m -> use m;
   Error _ ->
    hd ([])
      (map (\sysapp -> use (manifestSI sysapp))
        (filter (\sysapp ->
          case idApp_eq app0 (idSI sysapp) of {
           Prelude.True -> Prelude.True;
           Prelude.False -> Prelude.False}) (systemImage (environment s))))}

grantedPermsForApp :: IdApp -> System -> ([]) Perm0
grantedPermsForApp app0 s =
  case map_apply idApp_eq (perms (state s)) app0 of {
   Value list -> list;
   Error _ -> ([])}

grantPermission :: IdApp -> Perm0 -> (Mapping IdApp (([]) Perm0)) -> Mapping
                   IdApp (([]) Perm0)
grantPermission app0 p oldperms =
  case map_apply idApp_eq oldperms app0 of {
   Value list -> map_add idApp_eq oldperms app0 ((:) p list);
   Error _ -> oldperms}

revokePermission :: IdApp -> Perm0 -> (Mapping IdApp (([]) Perm0)) -> Mapping
                    IdApp (([]) Perm0)
revokePermission app0 p oldperms =
  case map_apply idApp_eq oldperms app0 of {
   Value list -> map_add idApp_eq oldperms app0 (remove perm_eq p list);
   Error _ -> oldperms}

grantPermissionGroup :: IdApp -> IdGrp -> (Mapping IdApp (([]) IdGrp)) ->
                        Mapping IdApp (([]) IdGrp)
grantPermissionGroup app0 g oldpermGroups =
  case map_apply idApp_eq oldpermGroups app0 of {
   Value list -> map_add idApp_eq oldpermGroups app0 ((:) g list);
   Error _ -> oldpermGroups}

revokePermissionGroup :: IdApp -> IdGrp -> (Mapping IdApp (([]) IdGrp)) ->
                         Mapping IdApp (([]) IdGrp)
revokePermissionGroup app0 g oldpermGroups =
  case map_apply idApp_eq oldpermGroups app0 of {
   Value list -> map_add idApp_eq oldpermGroups app0 (remove idGrp_eq g list);
   Error _ -> oldpermGroups}

getPermsOfGroup :: IdGrp -> IdApp -> System -> ([]) Perm0
getPermsOfGroup g app0 s =
  let {allPerms = grantedPermsForApp app0 s} in
  filter (\perm ->
    case maybeGrp perm of {
     Prelude.Just g' ->
      case idGrp_eq g g' of {
       Prelude.True -> Prelude.True;
       Prelude.False -> Prelude.False};
     Prelude.Nothing -> Prelude.False}) allPerms

revokeAllPermsOfGroup :: IdApp -> IdGrp -> System -> Mapping IdApp
                         (([]) Perm0)
revokeAllPermsOfGroup app0 g s =
  let {permsToBeRemoved = getPermsOfGroup g app0 s} in
  let {oldperms = perms (state s)} in
  case map_apply idApp_eq oldperms app0 of {
   Value list ->
    map_add idApp_eq oldperms app0 (removeAll perm_eq permsToBeRemoved list);
   Error _ -> oldperms}

getManifestAndAppFromCmp :: Cmp -> System -> (,) IdApp Manifest
getManifestAndAppFromCmp c s =
  let {
   maybeinstalledPairs = map (\a -> (,) a
                           (map_apply idApp_eq (manifest (environment s)) a))
                           (apps (state s))}
  in
  let {
   maybeinstalledPairs0 = app maybeinstalledPairs
                            (map (\sysapp -> (,) (idSI sysapp) (Value
                              (manifestSI sysapp)))
                              (systemImage (environment s)))}
  in
  let {
   hisManifests = filter (\pair ->
                    case snd pair of {
                     Value mfst ->
                      inBool idCmp_eq (getCmpId c) (map getCmpId (cmp mfst));
                     Error _ -> Prelude.False}) maybeinstalledPairs0}
  in
  let {
   theapp = fst (hd ((,) defaultApp (Value defaultManifest)) hisManifests)}
  in
  let {
   theMaybeMfst = snd
                    (hd ((,) defaultApp (Value defaultManifest))
                      hisManifests)}
  in
  case theMaybeMfst of {
   Value mfst -> (,) theapp mfst;
   Error _ -> (,) theapp defaultManifest}

getManifestFromCmp :: Cmp -> System -> Manifest
getManifestFromCmp c s =
  snd (getManifestAndAppFromCmp c s)

getAppFromCmp :: Cmp -> System -> IdApp
getAppFromCmp c s =
  fst (getManifestAndAppFromCmp c s)

getCmpMinSdkImpl :: Cmp -> System -> Prelude.Maybe Nat
getCmpMinSdkImpl c s =
  minSdk (getManifestFromCmp c s)

getCmpTargetSdkImpl :: Cmp -> System -> Prelude.Maybe Nat
getCmpTargetSdkImpl c s =
  targetSdk (getManifestFromCmp c s)

lebnat :: Nat -> Nat -> Prelude.Bool
lebnat n m =
  case n of {
   O -> Prelude.True;
   S x ->
    case m of {
     O -> Prelude.False;
     S y -> lebnat x y}}

getDefaultExpBool :: CProvider -> System -> Prelude.Bool
getDefaultExpBool cp s =
  case getCmpMinSdkImpl (CmpCP cp) s of {
   Prelude.Just n ->
    case getCmpTargetSdkImpl (CmpCP cp) s of {
     Prelude.Just m ->
      (Prelude.||)
        (lebnat n (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))))
        (lebnat m (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))));
     Prelude.Nothing -> Prelude.False};
   Prelude.Nothing -> Prelude.False}

getDefPermsForApp :: IdApp -> System -> ([]) Perm0
getDefPermsForApp a s =
  case map_apply idApp_eq (defPerms (environment s)) a of {
   Value l -> l;
   Error _ ->
    hd ([])
      (map defPermsSI
        (filter (\sysapp ->
          case idApp_eq a (idSI sysapp) of {
           Prelude.True -> Prelude.True;
           Prelude.False -> Prelude.False}) (systemImage (environment s))))}

getAppCert :: IdApp -> System -> Cert
getAppCert a s =
  case map_apply idApp_eq (cert (environment s)) a of {
   Value c -> c;
   Error _ ->
    hd defaultCert
      (map certSI
        (filter (\sysapp ->
          case idApp_eq a (idSI sysapp) of {
           Prelude.True -> Prelude.True;
           Prelude.False -> Prelude.False}) (systemImage (environment s))))}

getCertOfDefiner :: Perm0 -> System -> Cert
getCertOfDefiner p s =
  let {
   pairs = map (\a -> (,) a (getDefPermsForApp a s))
             (app (apps (state s)) (map idSI (systemImage (environment s))))}
  in
  let {theonelist = filter (\pair -> inBool perm_eq p (snd pair)) pairs} in
  hd defaultCert (map (\pair -> getAppCert (fst pair) s) theonelist)

getManifestForApp :: IdApp -> System -> Manifest
getManifestForApp a s =
  case map_apply idApp_eq (manifest (environment s)) a of {
   Value m -> m;
   Error _ ->
    hd defaultManifest
      (map manifestSI
        (filter (\sysapp ->
          case idApp_eq a (idSI sysapp) of {
           Prelude.True -> Prelude.True;
           Prelude.False -> Prelude.False}) (systemImage (environment s))))}

groupIsGranted :: IdApp -> Perm0 -> System -> Prelude.Bool
groupIsGranted a p s =
  case maybeGrp p of {
   Prelude.Just grp ->
    case map_apply idApp_eq (grantedPermGroups (state s)) a of {
     Value grps -> inBool idGrp_eq grp grps;
     Error _ -> Prelude.False};
   Prelude.Nothing -> Prelude.False}

appHasPermissionBool :: IdApp -> Perm0 -> System -> Prelude.Bool
appHasPermissionBool idapp p s =
  (Prelude.&&)
    ((Prelude.&&) (inBool perm_eq p (getAllPerms s))
      (isAppInstalledBool idapp s))
    ((Prelude.||) (inBool perm_eq p (grantedPermsForApp idapp s))
      (let {mfst = getManifestForApp idapp s} in
       case inBool idPerm_eq (idP p) (use mfst) of {
        Prelude.True ->
         let {defPerms0 = getDefPermsForApp idapp s} in
         case (Prelude.&&) (inBool idApp_eq idapp (apps (state s)))
                (inBool perm_eq p defPerms0) of {
          Prelude.True -> Prelude.True;
          Prelude.False ->
           case pl p of {
            Dangerous -> Prelude.False;
            Normal -> Prelude.True;
            Signature ->
             (Prelude.&&) (inBool perm_eq p (usrDefPerms s))
               (case cert_eq (getAppCert idapp s) (getCertOfDefiner p s) of {
                 Prelude.True -> Prelude.True;
                 Prelude.False -> Prelude.False});
            SignatureOrSys ->
             (Prelude.||)
               ((Prelude.&&) (inBool perm_eq p (usrDefPerms s))
                 (case cert_eq (getAppCert idapp s) (getCertOfDefiner p s) of {
                   Prelude.True -> Prelude.True;
                   Prelude.False -> Prelude.False}))
               (case cert_eq (getAppCert idapp s) manufacturerCert of {
                 Prelude.True -> Prelude.True;
                 Prelude.False -> Prelude.False})}};
        Prelude.False -> Prelude.False}))

canDoThisBool :: Cmp -> CProvider -> System -> (CProvider -> Prelude.Maybe
                 Perm0) -> Prelude.Bool
canDoThisBool c cp s thisE =
  case Prelude.not (cmpInStateBool c s) of {
   Prelude.True -> Prelude.False;
   Prelude.False ->
    case Prelude.not (cmpInStateBool (CmpCP cp) s) of {
     Prelude.True -> Prelude.False;
     Prelude.False ->
      case getManifestAndAppFromCmp c s of {
       (,) a1 _ ->
        case getManifestAndAppFromCmp (CmpCP cp) s of {
         (,) a2 m2 ->
          let {
           requiredPerm = case thisE cp of {
                           Prelude.Just p -> Prelude.Just p;
                           Prelude.Nothing ->
                            case cmpEC cp of {
                             Prelude.Just p -> Prelude.Just p;
                             Prelude.Nothing -> appE m2}}}
          in
          let {
           checkPerm = case requiredPerm of {
                        Prelude.Just p -> appHasPermissionBool a1 p s;
                        Prelude.Nothing -> Prelude.True}}
          in
          case idApp_eq a1 a2 of {
           Prelude.True -> Prelude.True;
           Prelude.False ->
            case expC cp of {
             Prelude.Just b ->
              case b of {
               Prelude.True -> checkPerm;
               Prelude.False -> Prelude.False};
             Prelude.Nothing ->
              case getDefaultExpBool cp s of {
               Prelude.True -> checkPerm;
               Prelude.False -> Prelude.False}}}}}}}

canReadBool :: Cmp -> CProvider -> System -> Prelude.Bool
canReadBool c cp s =
  canDoThisBool c cp s readE

canWriteBool :: Cmp -> CProvider -> System -> Prelude.Bool
canWriteBool c cp s =
  canDoThisBool c cp s writeE

eq_PType :: PType -> PType -> Prelude.Bool
eq_PType pt pt' =
  case pt of {
   Read ->
    case pt' of {
     Read -> Prelude.True;
     _ -> Prelude.False};
   Write ->
    case pt' of {
     Write -> Prelude.True;
     _ -> Prelude.False};
   Both ->
    case pt' of {
     Both -> Prelude.True;
     _ -> Prelude.False}}

delPermsBool :: Cmp -> CProvider -> Uri -> PType -> System -> Prelude.Bool
delPermsBool c cp u pt s =
  case Prelude.not (cmpInStateBool c s) of {
   Prelude.True -> Prelude.False;
   Prelude.False ->
    let {a = getAppFromCmp c s} in
    let {
     runningAppAndiCmps = map (\pair -> (,) (item_index pair)
                            (getAppFromCmp (item_info pair) s))
                            (running (state s))}
    in
    let {
     myRunningiCmps = map (\pair -> fst pair)
                        (filter (\pair ->
                          case idApp_eq a (snd pair) of {
                           Prelude.True -> Prelude.True;
                           Prelude.False -> Prelude.False})
                          runningAppAndiCmps)}
    in
    case existsb (\icmp ->
           case map_apply deltpermsdomeq (delTPerms (state s)) ((,) ((,) icmp
                  cp) u) of {
            Value pt' ->
             case pt' of {
              Both -> Prelude.True;
              _ -> eq_PType pt' pt};
            Error _ -> Prelude.False}) myRunningiCmps of {
     Prelude.True -> Prelude.True;
     Prelude.False ->
      case map_apply delppermsdomeq (delPPerms (state s)) ((,) ((,) a cp) u) of {
       Value pt' ->
        case pt' of {
         Both -> Prelude.True;
         _ -> eq_PType pt' pt};
       Error _ -> Prelude.False}}}

existsResBool :: CProvider -> Uri -> System -> Prelude.Bool
existsResBool cp u s =
  let {allTheComponents = getAllComponents s} in
  case Prelude.not (inBool cmp_eq (CmpCP cp) allTheComponents) of {
   Prelude.True -> Prelude.False;
   Prelude.False ->
    let {theapp = getAppFromCmp (CmpCP cp) s} in
    case map_apply uri_eq (map_res cp) u of {
     Value r ->
      case map_apply rescontdomeq (resCont (state s)) ((,) theapp r) of {
       Value _ -> Prelude.True;
       Error _ -> Prelude.False};
     Error _ -> Prelude.False}}

writeResCont :: ICmp -> CProvider -> Uri -> Val -> System -> Mapping
                ((,) IdApp Res) Val
writeResCont _ cp u val s =
  let {oldResCont = resCont (state s)} in
  let {a = getAppFromCmp (CmpCP cp) s} in
  case map_apply uri_eq (map_res cp) u of {
   Value r -> map_add rescontdomeq oldResCont ((,) a r) val;
   Error _ -> oldResCont}

intTypeEqBool :: IntentType -> IntentType -> Prelude.Bool
intTypeEqBool t t' =
  case t of {
   IntActivity ->
    case t' of {
     IntActivity -> Prelude.True;
     _ -> Prelude.False};
   IntService ->
    case t' of {
     IntService -> Prelude.True;
     _ -> Prelude.False};
   IntBroadcast ->
    case t' of {
     IntBroadcast -> Prelude.True;
     _ -> Prelude.False}}

isiCmpRunningBool :: ICmp -> System -> Prelude.Bool
isiCmpRunningBool ic s =
  inBool iCmp_eq ic (map_getKeys (running (state s)))

getSomes :: (a1 -> Prelude.Maybe a2) -> (([]) a1) -> ([]) a2
getSomes f l =
  case l of {
   ([]) -> ([]);
   (:) x rest ->
    case f x of {
     Prelude.Just y -> (:) y (getSomes f rest);
     Prelude.Nothing -> getSomes f rest}}

actionTestBool :: Intent0 -> IntentFilter -> System -> Prelude.Bool
actionTestBool i iFil _ =
  case action i of {
   Prelude.Just iAct -> inBool intentAction_eq iAct (actFilter iFil);
   Prelude.Nothing -> Prelude.not (isNil (actFilter iFil))}

categoryTestBool :: Intent0 -> IntentFilter -> System -> Prelude.Bool
categoryTestBool i iFil _ =
  case category i of {
   ([]) -> Prelude.True;
   (:) c l ->
    Prelude.not
      (existsb (\c0 -> Prelude.not (inBool category_eq c0 (catFilter iFil)))
        ((:) c l))}

eqDataType :: DataType -> DataType -> Prelude.Bool
eqDataType dt dt' =
  case dt of {
   Content ->
    case dt' of {
     Content -> Prelude.True;
     _ -> Prelude.False};
   File ->
    case dt' of {
     File -> Prelude.True;
     _ -> Prelude.False};
   Other ->
    case dt' of {
     Other -> Prelude.True;
     _ -> Prelude.False}}

isContentOrFileBool :: Intent0 -> Prelude.Bool
isContentOrFileBool i =
  (Prelude.||) (eqDataType (type0 (data0 i)) Content)
    (eqDataType (type0 (data0 i)) File)

notUriAndNotMimeBool :: Intent0 -> IntentFilter -> System -> Prelude.Bool
notUriAndNotMimeBool i iFil _ =
  (Prelude.&&)
    ((Prelude.&&) (Prelude.not (isSomethingBool (path (data0 i))))
      (Prelude.not (isSomethingBool (mime (data0 i)))))
    (isNil (dataFilter iFil))

uriAndNotMimeBool :: Intent0 -> IntentFilter -> System -> Prelude.Bool
uriAndNotMimeBool i iFil _ =
  (Prelude.&&)
    ((Prelude.&&) (isSomethingBool (path (data0 i)))
      (Prelude.not (isSomethingBool (mime (data0 i)))))
    (inBool data_eq (data0 i) (dataFilter iFil))

notUriAndMimeBool :: Intent0 -> IntentFilter -> System -> Prelude.Bool
notUriAndMimeBool i iFil _ =
  (Prelude.&&)
    ((Prelude.&&) (Prelude.not (isSomethingBool (path (data0 i))))
      (isSomethingBool (mime (data0 i))))
    (inBool data_eq (data0 i) (dataFilter iFil))

uriAndMimeBool :: Intent0 -> IntentFilter -> System -> Prelude.Bool
uriAndMimeBool i iFil _ =
  let {allSomeMimes = getSomes mime (dataFilter iFil)} in
  let {allPaths = map path (dataFilter iFil)} in
  let {allSomePaths = getSomes path (dataFilter iFil)} in
  case path (data0 i) of {
   Prelude.Just thePath ->
    case mime (data0 i) of {
     Prelude.Just theMime ->
      (Prelude.&&) (inBool mimeType_eq theMime allSomeMimes)
        ((Prelude.||) (inBool uri_eq thePath allSomePaths)
          ((Prelude.&&) (isContentOrFileBool i)
            (existsb (\maybe -> Prelude.not (isSomethingBool maybe))
              allPaths)));
     Prelude.Nothing -> Prelude.False};
   Prelude.Nothing -> Prelude.False}

dataTestBool :: Intent0 -> IntentFilter -> System -> Prelude.Bool
dataTestBool i iFil s =
  (Prelude.||)
    ((Prelude.||)
      ((Prelude.||) (notUriAndNotMimeBool i iFil s)
        (uriAndNotMimeBool i iFil s)) (notUriAndMimeBool i iFil s))
    (uriAndMimeBool i iFil s)

isSomeTrue :: (Prelude.Maybe Prelude.Bool) -> Prelude.Bool
isSomeTrue maybeB =
  case maybeB of {
   Prelude.Just b -> b;
   Prelude.Nothing -> Prelude.False}

canBeStartedBool :: Cmp -> System -> Prelude.Bool
canBeStartedBool c s =
  case c of {
   CmpAct a ->
    (Prelude.||) (isSomeTrue (expA a))
      ((Prelude.&&) (Prelude.not (isSomethingBool (expA a)))
        (isNil (intFilterA a)));
   CmpSrv sr ->
    (Prelude.||) (isSomeTrue (expS sr))
      ((Prelude.&&) (Prelude.not (isSomethingBool (expS sr)))
        (isNil (intFilterS sr)));
   CmpCP cp ->
    (Prelude.||) (isSomeTrue (expC cp))
      ((Prelude.&&) (Prelude.not (isSomethingBool (expC cp)))
        (getDefaultExpBool cp s));
   CmpBR br ->
    (Prelude.||) (isSomeTrue (expB br))
      ((Prelude.&&) (Prelude.not (isSomethingBool (expB br)))
        (isNil (intFilterB br)))}

canStartBool :: Cmp -> Cmp -> System -> Prelude.Bool
canStartBool c1 c2 s =
  case Prelude.not (cmpInStateBool c1 s) of {
   Prelude.True -> Prelude.False;
   Prelude.False ->
    case Prelude.not (cmpInStateBool c2 s) of {
     Prelude.True -> Prelude.False;
     Prelude.False ->
      case getManifestAndAppFromCmp c1 s of {
       (,) a1 m ->
        let {a2 = getAppFromCmp c2 s} in
        case idApp_eq a1 a2 of {
         Prelude.True -> Prelude.True;
         Prelude.False ->
          (Prelude.&&) (canBeStartedBool c2 s)
            (let {
              maybep = case c2 of {
                        CmpAct a ->
                         case cmpEA a of {
                          Prelude.Just p -> Prelude.Just p;
                          Prelude.Nothing -> appE m};
                        CmpSrv s0 ->
                         case cmpES s0 of {
                          Prelude.Just p -> Prelude.Just p;
                          Prelude.Nothing -> appE m};
                        CmpCP cp ->
                         case cmpEC cp of {
                          Prelude.Just p -> Prelude.Just p;
                          Prelude.Nothing -> appE m};
                        CmpBR br ->
                         case cmpEB br of {
                          Prelude.Just p -> Prelude.Just p;
                          Prelude.Nothing -> appE m}}}
             in
             case maybep of {
              Prelude.Just p -> appHasPermissionBool a1 p s;
              Prelude.Nothing -> Prelude.True})}}}}

canRunBool :: IdApp -> System -> Prelude.Bool
canRunBool app0 s =
  (Prelude.||) (inBool idApp_eq app0 (alreadyRun (state s)))
    (case targetSdk (getManifestForApp app0 s) of {
      Prelude.Just n -> ltb vulnerableSdk n;
      Prelude.Nothing -> Prelude.False})

getFilters :: Cmp -> ([]) IntentFilter
getFilters c =
  case c of {
   CmpAct ac -> intFilterA ac;
   CmpSrv s -> intFilterS s;
   CmpCP _ -> ([]);
   CmpBR br -> intFilterB br}

maybeIntentForAppCmp :: Intent0 -> IdApp -> ICmp -> System -> Prelude.Maybe
                        Cmp
maybeIntentForAppCmp i a ic s =
  case Prelude.not (isAppInstalledBool a s) of {
   Prelude.True -> Prelude.Nothing;
   Prelude.False ->
    case Prelude.not
           (inBool sentintentseq ((,) ic i) (sentIntents (state s))) of {
     Prelude.True -> Prelude.Nothing;
     Prelude.False ->
      let {allCmpsA = getAllCmps a s} in
      case cmpName i of {
       Prelude.Just idc ->
        case filter (\installedcomp ->
               case idCmp_eq idc (getCmpId installedcomp) of {
                Prelude.True -> Prelude.True;
                Prelude.False -> Prelude.False}) allCmpsA of {
         ([]) -> Prelude.Nothing;
         (:) c _ -> Prelude.Just c};
       Prelude.Nothing -> Prelude.Nothing}}}

canGrantBool :: CProvider -> Uri -> System -> Prelude.Bool
canGrantBool cp u s =
  let {allCmps = getAllComponents s} in
  (Prelude.&&) (inBool cmp_eq (CmpCP cp) allCmps)
    ((Prelude.||) (inBool uri_eq u (uriP cp))
      ((Prelude.&&) (isNil (uriP cp)) (grantU cp)))

removeTPerms :: ICmp -> State -> Mapping ((,) ((,) ICmp CProvider) Uri) PType
removeTPerms icmp st =
  let {oldTPerms = delTPerms st} in
  let {allKeys = map_getKeys oldTPerms} in
  let {
   filteredKeys = filter (\tuple ->
                    case iCmp_eq icmp (fst (fst tuple)) of {
                     Prelude.True -> Prelude.True;
                     Prelude.False -> Prelude.False}) allKeys}
  in
  dropAll deltpermsdomeq filteredKeys oldTPerms

receiveIntentCmpRequirements :: Cmp -> Uri -> System -> PType -> Cmp ->
                                Prelude.Bool
receiveIntentCmpRequirements c' u s intactype cmp0 =
  case cmp0 of {
   CmpCP cp ->
    let {
     thiscanread = (Prelude.||) (canReadBool c' cp s)
                     (delPermsBool c' cp u Read s)}
    in
    let {
     thiscanwrite = (Prelude.||) (canWriteBool c' cp s)
                      (delPermsBool c' cp u Write s)}
    in
    (Prelude.&&) ((Prelude.&&) (existsResBool cp u s) (canGrantBool cp u s))
      (case intactype of {
        Read -> thiscanread;
        Write -> thiscanwrite;
        Both -> (Prelude.&&) thiscanread thiscanwrite});
   _ -> Prelude.False}

defaultCmpId :: IdCmp
defaultCmpId = 0

defaultiCmp :: ICmp
defaultiCmp = 0

overrideIntentName :: Intent0 -> IdCmp -> Intent0
overrideIntentName i name =
  Intent (idI i) (Prelude.Just name) (intType i) (action i) (data0 i)
    (category i) (extra i) (flags i) (brperm i)

defaultCProvider :: CProvider
defaultCProvider =
  Cprovider defaultCmpId ([]) Prelude.Nothing Prelude.Nothing Prelude.Nothing
    Prelude.Nothing Prelude.True ([])

chooseCmp :: ((,) ICmp Intent0) -> IdApp -> System -> Cmp
chooseCmp pair a s =
  let {allCmpsA = getAllCmps a s} in
  let {allActsA = filter isActivityBool allCmpsA} in
  let {allServsA = filter isServiceBool allCmpsA} in
  let {allBroadsA = filter isBroadReceiverBool allCmpsA} in
  let {ic = fst pair} in
  let {intt = snd pair} in
  let {defaultCmp = CmpCP defaultCProvider} in
  case map_apply iCmp_eq (running (state s)) ic of {
   Value c1 ->
    let {
     startableCmps = case intType intt of {
                      IntActivity ->
                       filter (\c2 -> canStartBool c1 c2 s) allActsA;
                      IntService ->
                       filter (\c2 -> canStartBool c1 c2 s) allServsA;
                      IntBroadcast ->
                       filter (\c2 -> canStartBool c1 c2 s) allBroadsA}}
    in
    let {
     filteredstartableCmps = filter (\cmp0 ->
                               let {iFils = getFilters cmp0} in
                               existsb (\iFil ->
                                 (Prelude.&&)
                                   ((Prelude.&&) (actionTestBool intt iFil s)
                                     (categoryTestBool intt iFil s))
                                   (dataTestBool intt iFil s)) iFils)
                               startableCmps}
    in
    hd defaultCmp filteredstartableCmps;
   Error _ -> defaultCmp}

chooseCmpId :: ((,) ICmp Intent0) -> IdApp -> System -> IdCmp
chooseCmpId pair a s =
  getCmpId (chooseCmp pair a s)

resolveImplicitToExplicitIntent :: Intent0 -> IdApp -> System -> ([])
                                   ((,) ICmp Intent0)
resolveImplicitToExplicitIntent i a s =
  let {oldSentIntents = sentIntents (state s)} in
  let {
   filterFun = \pair ->
    case idInt_eq (idI i) (idI (snd pair)) of {
     Prelude.True -> Prelude.True;
     Prelude.False -> Prelude.False}}
  in
  let {updateSentIntents = filter filterFun oldSentIntents} in
  let {
   remainingSentIntents = filter (\pair -> Prelude.not (filterFun pair))
                            oldSentIntents}
  in
  let {theIcIntent = hd ((,) defaultiCmp i) updateSentIntents} in
  let {chosenCmpId = chooseCmpId theIcIntent a s} in
  let {
   updatedSentIntents = map (\pair -> (,) (fst pair)
                          (overrideIntentName (snd pair) chosenCmpId))
                          updateSentIntents}
  in
  app remainingSentIntents updatedSentIntents

performRunCmp :: Intent0 -> ICmp -> Cmp -> System -> Mapping ICmp Cmp
performRunCmp _ ic c s =
  let {oldrunning = running (state s)} in map_add iCmp_eq oldrunning ic c

iCmpGenerator :: (([]) ICmp) -> ICmp
iCmpGenerator = \used -> Prelude.maximum used Prelude.+ 1 

getAnyCProviderWithUri :: Uri -> System -> CProvider
getAnyCProviderWithUri u s =
  let {allCmps = getAllComponents s} in
  let {
   allCProviders = getSomes (\cmp0 ->
                     case cmp0 of {
                      CmpAct _ -> Prelude.Nothing;
                      CmpSrv _ -> Prelude.Nothing;
                      CmpCP cp -> Prelude.Just cp;
                      CmpBR _ -> Prelude.Nothing}) allCmps}
  in
  let {filteredCPs = filter (\cp -> existsResBool cp u s) allCProviders} in
  hd defaultCProvider filteredCPs

performGrantTempPerm :: PType -> Uri -> CProvider -> ICmp -> System ->
                        Mapping ((,) ((,) ICmp CProvider) Uri) PType
performGrantTempPerm pt u cp ic s =
  let {oldDelTPerms = delTPerms (state s)} in
  map_add deltpermsdomeq oldDelTPerms ((,) ((,) ic cp) u) pt

addDelPPerm :: (Mapping ((,) ((,) IdApp CProvider) Uri) PType) -> ((,)
               ((,) IdApp CProvider) Uri) -> PType -> Mapping
               ((,) ((,) IdApp CProvider) Uri) PType
addDelPPerm oldPPerms idx pt =
  map_add delppermsdomeq oldPPerms idx
    (case map_apply delppermsdomeq oldPPerms idx of {
      Value pt' -> ptplus pt' pt;
      Error _ -> pt})

removeAllPerms :: (((,) ((,) a1 CProvider) Uri) -> ((,) ((,) a1 CProvider)
                  Uri) -> Prelude.Bool) -> (Mapping
                  ((,) ((,) a1 CProvider) Uri) PType) -> CProvider -> Uri ->
                  PType -> Mapping ((,) ((,) a1 CProvider) Uri) PType
removeAllPerms domeq mp cp u pt =
  let {
   willupdate = filter (\tuple ->
                  case cProvider_eq cp (snd (fst tuple)) of {
                   Prelude.True ->
                    case uri_eq u (snd tuple) of {
                     Prelude.True -> Prelude.True;
                     Prelude.False -> Prelude.False};
                   Prelude.False -> Prelude.False}) (map_getKeys mp)}
  in
  let {
   willdrop = filter (\tuple ->
                case map_apply domeq mp tuple of {
                 Value pt' -> Prelude.not (isSomethingBool (ptminus pt' pt));
                 Error _ -> Prelude.False}) willupdate}
  in
  let {
   overrideKeys = filter (\tuple ->
                    case map_apply domeq mp tuple of {
                     Value pt' -> isSomethingBool (ptminus pt' pt);
                     Error _ -> Prelude.False}) willupdate}
  in
  let {
   overrideKeyVals = map (\tuple -> (,) tuple
                       (case map_apply domeq mp tuple of {
                         Value pt' ->
                          case ptminus pt' pt of {
                           Prelude.Just pt'' -> pt'';
                           Prelude.Nothing -> Both};
                         Error _ -> Both})) overrideKeys}
  in
  dropAll domeq willdrop (addAll domeq overrideKeyVals mp)

getMandatoryPerms :: SACall -> ([]) Perm0
getMandatoryPerms = \_ -> []

install_pre :: IdApp -> Manifest -> Cert -> (([]) Res) -> System ->
               Prelude.Maybe ErrorCode
install_pre app0 m _ _ s =
  case isAppInstalledBool app0 s of {
   Prelude.True -> Prelude.Just App_already_installed;
   Prelude.False ->
    case has_duplicates idCmp_eq (map getCmpId (cmp m)) of {
     Prelude.True -> Prelude.Just Duplicated_cmp_id;
     Prelude.False ->
      case has_duplicates idPerm_eq (map idP (usrP m)) of {
       Prelude.True -> Prelude.Just Duplicated_perm_id;
       Prelude.False ->
        case existsb (\c -> cmpIdInStateBool c s) (cmp m) of {
         Prelude.True -> Prelude.Just Cmp_already_defined;
         Prelude.False ->
          case Prelude.not (authPermsBool m s) of {
           Prelude.True -> Prelude.Just Perm_already_defined;
           Prelude.False ->
            case anyDefinesIntentFilterIncorrectly (cmp m) of {
             Prelude.True -> Prelude.Just Faulty_intent_filter;
             Prelude.False -> Prelude.Nothing}}}}}}

install_post :: IdApp -> Manifest -> Cert -> (([]) Res) -> System -> System
install_post app0 m c lRes s =
  let {oldstate = state s} in
  let {oldenv = environment s} in
  Sys (St ((:) app0 (apps oldstate)) (alreadyRun oldstate)
  (map_add idApp_eq (grantedPermGroups oldstate) app0 ([]))
  (map_add idApp_eq (perms oldstate) app0 ([])) (running oldstate)
  (delPPerms oldstate) (delTPerms oldstate)
  (addNewResCont app0 (resCont oldstate) lRes) (sentIntents oldstate)) (Env
  (map_add idApp_eq (manifest oldenv) app0 m)
  (map_add idApp_eq (cert oldenv) app0 c)
  (map_add idApp_eq (defPerms oldenv) app0 (nonSystemUsrP m))
  (systemImage oldenv))

install_safe :: IdApp -> Manifest -> Cert -> (([]) Res) -> System -> Result0
install_safe app0 m c lRes s =
  case install_pre app0 m c lRes s of {
   Prelude.Just ec -> Result (Error0 ec) s;
   Prelude.Nothing -> Result Ok (install_post app0 m c lRes s)}

uninstall_pre :: IdApp -> System -> Prelude.Maybe ErrorCode
uninstall_pre app0 s =
  case Prelude.not (inBool idApp_eq app0 (apps (state s))) of {
   Prelude.True -> Prelude.Just No_such_app;
   Prelude.False ->
    case isAnyCmpRunning app0 s of {
     Prelude.True -> Prelude.Just App_is_running;
     Prelude.False -> Prelude.Nothing}}

uninstall_post :: IdApp -> System -> System
uninstall_post app0 s =
  let {oldstate = state s} in
  let {oldenv = environment s} in
  Sys (St (remove idApp_eq app0 (apps oldstate)) (alreadyRun oldstate)
  (map_drop idApp_eq (grantedPermGroups oldstate) app0) (dropAppPerms s app0)
  (running oldstate) (dropAllPPerms s app0) (dropAllTPerms s app0)
  (dropAllRes (resCont oldstate) app0) (sentIntents oldstate)) (Env
  (map_drop idApp_eq (manifest oldenv) app0)
  (map_drop idApp_eq (cert oldenv) app0)
  (map_drop idApp_eq (defPerms oldenv) app0) (systemImage oldenv))

uninstall_safe :: IdApp -> System -> Result0
uninstall_safe app0 s =
  case uninstall_pre app0 s of {
   Prelude.Just ec -> Result (Error0 ec) s;
   Prelude.Nothing -> Result Ok (uninstall_post app0 s)}

grant_pre :: Perm0 -> IdApp -> System -> Prelude.Maybe ErrorCode
grant_pre p app0 s =
  case Prelude.not (inBool idPerm_eq (idP p) (permsInUse app0 s)) of {
   Prelude.True -> Prelude.Just Perm_not_in_use;
   Prelude.False ->
    case Prelude.not (inBool perm_eq p (getAllPerms s)) of {
     Prelude.True -> Prelude.Just No_such_perm;
     Prelude.False ->
      case inBool perm_eq p (grantedPermsForApp app0 s) of {
       Prelude.True -> Prelude.Just Perm_already_granted;
       Prelude.False ->
        case permLevel_eq (pl p) Dangerous of {
         Prelude.True ->
          case groupIsGranted app0 p s of {
           Prelude.True -> Prelude.Just Perm_should_auto_grant;
           Prelude.False -> Prelude.Nothing};
         Prelude.False -> Prelude.Just Perm_not_dangerous}}}}

grant_post :: Perm0 -> IdApp -> System -> System
grant_post p app0 s =
  let {oldstate = state s} in
  let {oldenv = environment s} in
  let {
   newGrantedPermGroups = case maybeGrp p of {
                           Prelude.Just g ->
                            grantPermissionGroup app0 g
                              (grantedPermGroups oldstate);
                           Prelude.Nothing -> grantedPermGroups oldstate}}
  in
  Sys (St (apps oldstate) (alreadyRun oldstate) newGrantedPermGroups
  (grantPermission app0 p (perms oldstate)) (running oldstate)
  (delPPerms oldstate) (delTPerms oldstate) (resCont oldstate)
  (sentIntents oldstate)) oldenv

grant_safe :: Perm0 -> IdApp -> System -> Result0
grant_safe p app0 s =
  case grant_pre p app0 s of {
   Prelude.Just ec -> Result (Error0 ec) s;
   Prelude.Nothing -> Result Ok (grant_post p app0 s)}

grantAuto_pre :: Perm0 -> IdApp -> System -> Prelude.Maybe ErrorCode
grantAuto_pre p app0 s =
  case Prelude.not (inBool idPerm_eq (idP p) (permsInUse app0 s)) of {
   Prelude.True -> Prelude.Just Perm_not_in_use;
   Prelude.False ->
    case Prelude.not (inBool perm_eq p (getAllPerms s)) of {
     Prelude.True -> Prelude.Just No_such_perm;
     Prelude.False ->
      case inBool perm_eq p (grantedPermsForApp app0 s) of {
       Prelude.True -> Prelude.Just Perm_already_granted;
       Prelude.False ->
        case permLevel_eq (pl p) Dangerous of {
         Prelude.True ->
          case Prelude.not (isSomethingBool (maybeGrp p)) of {
           Prelude.True -> Prelude.Just Perm_not_grouped;
           Prelude.False ->
            case Prelude.not (groupIsGranted app0 p s) of {
             Prelude.True -> Prelude.Just Cannot_auto_grant;
             Prelude.False -> Prelude.Nothing}};
         Prelude.False -> Prelude.Just Perm_not_dangerous}}}}

grantAuto_post :: Perm0 -> IdApp -> System -> System
grantAuto_post p app0 s =
  let {oldstate = state s} in
  let {oldenv = environment s} in
  Sys (St (apps oldstate) (alreadyRun oldstate) (grantedPermGroups oldstate)
  (grantPermission app0 p (perms oldstate)) (running oldstate)
  (delPPerms oldstate) (delTPerms oldstate) (resCont oldstate)
  (sentIntents oldstate)) oldenv

grantAuto_safe :: Perm0 -> IdApp -> System -> Result0
grantAuto_safe p app0 s =
  case grantAuto_pre p app0 s of {
   Prelude.Just ec -> Result (Error0 ec) s;
   Prelude.Nothing -> Result Ok (grantAuto_post p app0 s)}

revoke_pre :: Perm0 -> IdApp -> System -> Prelude.Maybe ErrorCode
revoke_pre p app0 s =
  case Prelude.not (inBool perm_eq p (grantedPermsForApp app0 s)) of {
   Prelude.True -> Prelude.Just Perm_wasnt_granted;
   Prelude.False ->
    case isSomethingBool (maybeGrp p) of {
     Prelude.True -> Prelude.Just Perm_is_grouped;
     Prelude.False -> Prelude.Nothing}}

revoke_post :: Perm0 -> IdApp -> System -> System
revoke_post p app0 s =
  let {oldstate = state s} in
  let {oldenv = environment s} in
  Sys (St (apps oldstate) (alreadyRun oldstate) (grantedPermGroups oldstate)
  (revokePermission app0 p (perms oldstate)) (running oldstate)
  (delPPerms oldstate) (delTPerms oldstate) (resCont oldstate)
  (sentIntents oldstate)) oldenv

revoke_safe :: Perm0 -> IdApp -> System -> Result0
revoke_safe p app0 s =
  case revoke_pre p app0 s of {
   Prelude.Just ec -> Result (Error0 ec) s;
   Prelude.Nothing -> Result Ok (revoke_post p app0 s)}

revokegroup_pre :: IdGrp -> IdApp -> System -> Prelude.Maybe ErrorCode
revokegroup_pre g app0 s =
  case map_apply idApp_eq (grantedPermGroups (state s)) app0 of {
   Value lGrp ->
    case inBool idGrp_eq g lGrp of {
     Prelude.True -> Prelude.Nothing;
     Prelude.False -> Prelude.Just Group_wasnt_granted};
   Error _ -> Prelude.Just Group_wasnt_granted}

revokegroup_post :: IdGrp -> IdApp -> System -> System
revokegroup_post g app0 s =
  let {oldstate = state s} in
  let {oldenv = environment s} in
  Sys (St (apps oldstate) (alreadyRun oldstate)
  (revokePermissionGroup app0 g (grantedPermGroups oldstate))
  (revokeAllPermsOfGroup app0 g s) (running oldstate) (delPPerms oldstate)
  (delTPerms oldstate) (resCont oldstate) (sentIntents oldstate)) oldenv

revokegroup_safe :: IdGrp -> IdApp -> System -> Result0
revokegroup_safe g app0 s =
  case revokegroup_pre g app0 s of {
   Prelude.Just ec -> Result (Error0 ec) s;
   Prelude.Nothing -> Result Ok (revokegroup_post g app0 s)}

read_pre :: ICmp -> CProvider -> Uri -> System -> Prelude.Maybe ErrorCode
read_pre icmp cp u s =
  case Prelude.not (existsResBool cp u s) of {
   Prelude.True -> Prelude.Just No_such_res;
   Prelude.False ->
    case map_apply iCmp_eq (running (state s)) icmp of {
     Value c ->
      case (Prelude.||) (canReadBool c cp s) (delPermsBool c cp u Read s) of {
       Prelude.True -> Prelude.Nothing;
       Prelude.False -> Prelude.Just Not_enough_permissions};
     Error _ -> Prelude.Just Instance_not_running}}

read_post :: ICmp -> CProvider -> Uri -> System -> System
read_post _ _ _ s =
  s

read_safe :: ICmp -> CProvider -> Uri -> System -> Result0
read_safe icmp cp u s =
  case read_pre icmp cp u s of {
   Prelude.Just ec -> Result (Error0 ec) s;
   Prelude.Nothing -> Result Ok (read_post icmp cp u s)}

write_pre :: ICmp -> CProvider -> Uri -> Val -> System -> Prelude.Maybe
             ErrorCode
write_pre icmp cp u _ s =
  case Prelude.not (existsResBool cp u s) of {
   Prelude.True -> Prelude.Just No_such_res;
   Prelude.False ->
    case map_apply iCmp_eq (running (state s)) icmp of {
     Value c ->
      case (Prelude.||) (canWriteBool c cp s) (delPermsBool c cp u Write s) of {
       Prelude.True -> Prelude.Nothing;
       Prelude.False -> Prelude.Just Not_enough_permissions};
     Error _ -> Prelude.Just Instance_not_running}}

write_post :: ICmp -> CProvider -> Uri -> Val -> System -> System
write_post icmp cp u v s =
  let {oldstate = state s} in
  let {oldenv = environment s} in
  Sys (St (apps oldstate) (alreadyRun oldstate) (grantedPermGroups oldstate)
  (perms oldstate) (running oldstate) (delPPerms oldstate)
  (delTPerms oldstate) (writeResCont icmp cp u v s) (sentIntents oldstate))
  oldenv

write_safe :: ICmp -> CProvider -> Uri -> Val -> System -> Result0
write_safe icmp cp u v s =
  case write_pre icmp cp u v s of {
   Prelude.Just ec -> Result (Error0 ec) s;
   Prelude.Nothing -> Result Ok (write_post icmp cp u v s)}

startActivity_pre :: Intent0 -> ICmp -> System -> Prelude.Maybe ErrorCode
startActivity_pre intt icmp s =
  case Prelude.not (intTypeEqBool (intType intt) IntActivity) of {
   Prelude.True -> Prelude.Just Incorrect_intent_type;
   Prelude.False ->
    case isSomethingBool (brperm intt) of {
     Prelude.True -> Prelude.Just Faulty_intent;
     Prelude.False ->
      case Prelude.not (isiCmpRunningBool icmp s) of {
       Prelude.True -> Prelude.Just Instance_not_running;
       Prelude.False ->
        case existsb (\pair ->
               case idInt_eq (idI intt) (idI (snd pair)) of {
                Prelude.True -> Prelude.True;
                Prelude.False -> Prelude.False}) (sentIntents (state s)) of {
         Prelude.True -> Prelude.Just Intent_already_sent;
         Prelude.False -> Prelude.Nothing}}}}

startActivity_post :: Intent0 -> ICmp -> System -> System
startActivity_post intt icmp s =
  let {oldstate = state s} in
  let {oldenv = environment s} in
  Sys (St (apps oldstate) (alreadyRun oldstate) (grantedPermGroups oldstate)
  (perms oldstate) (running oldstate) (delPPerms oldstate)
  (delTPerms oldstate) (resCont oldstate) ((:) ((,) icmp
  (createIntent intt Prelude.Nothing)) (sentIntents oldstate))) oldenv

startActivity_safe :: Intent0 -> ICmp -> System -> Result0
startActivity_safe intt icmp s =
  case startActivity_pre intt icmp s of {
   Prelude.Just ec -> Result (Error0 ec) s;
   Prelude.Nothing -> Result Ok (startActivity_post intt icmp s)}

startService_pre :: Intent0 -> ICmp -> System -> Prelude.Maybe ErrorCode
startService_pre intt icmp s =
  case Prelude.not (intTypeEqBool (intType intt) IntService) of {
   Prelude.True -> Prelude.Just Incorrect_intent_type;
   Prelude.False ->
    case isSomethingBool (brperm intt) of {
     Prelude.True -> Prelude.Just Faulty_intent;
     Prelude.False ->
      case Prelude.not (isiCmpRunningBool icmp s) of {
       Prelude.True -> Prelude.Just Instance_not_running;
       Prelude.False ->
        case existsb (\pair ->
               case idInt_eq (idI intt) (idI (snd pair)) of {
                Prelude.True -> Prelude.True;
                Prelude.False -> Prelude.False}) (sentIntents (state s)) of {
         Prelude.True -> Prelude.Just Intent_already_sent;
         Prelude.False -> Prelude.Nothing}}}}

startService_post :: Intent0 -> ICmp -> System -> System
startService_post intt icmp s =
  startActivity_post intt icmp s

startService_safe :: Intent0 -> ICmp -> System -> Result0
startService_safe intt icmp s =
  case startService_pre intt icmp s of {
   Prelude.Just ec -> Result (Error0 ec) s;
   Prelude.Nothing -> Result Ok (startService_post intt icmp s)}

sendBroadcast_pre :: Intent0 -> ICmp -> (Prelude.Maybe Perm0) -> System ->
                     Prelude.Maybe ErrorCode
sendBroadcast_pre intt icmp _ s =
  case Prelude.not (intTypeEqBool (intType intt) IntBroadcast) of {
   Prelude.True -> Prelude.Just Incorrect_intent_type;
   Prelude.False ->
    case isSomethingBool (brperm intt) of {
     Prelude.True -> Prelude.Just Faulty_intent;
     Prelude.False ->
      case Prelude.not (isiCmpRunningBool icmp s) of {
       Prelude.True -> Prelude.Just Instance_not_running;
       Prelude.False ->
        case existsb (\pair ->
               case idInt_eq (idI intt) (idI (snd pair)) of {
                Prelude.True -> Prelude.True;
                Prelude.False -> Prelude.False}) (sentIntents (state s)) of {
         Prelude.True -> Prelude.Just Intent_already_sent;
         Prelude.False -> Prelude.Nothing}}}}

sendBroadcast_post :: Intent0 -> ICmp -> (Prelude.Maybe Perm0) -> System ->
                      System
sendBroadcast_post intt icmp p s =
  let {oldstate = state s} in
  let {oldenv = environment s} in
  Sys (St (apps oldstate) (alreadyRun oldstate) (grantedPermGroups oldstate)
  (perms oldstate) (running oldstate) (delPPerms oldstate)
  (delTPerms oldstate) (resCont oldstate) ((:) ((,) icmp
  (createIntent intt p)) (sentIntents oldstate))) oldenv

sendBroadcast_safe :: Intent0 -> ICmp -> (Prelude.Maybe Perm0) -> System ->
                      Result0
sendBroadcast_safe intt icmp p s =
  case sendBroadcast_pre intt icmp p s of {
   Prelude.Just ec -> Result (Error0 ec) s;
   Prelude.Nothing -> Result Ok (sendBroadcast_post intt icmp p s)}

sendStickyBroadcast_pre :: Intent0 -> ICmp -> System -> Prelude.Maybe
                           ErrorCode
sendStickyBroadcast_pre intt icmp s =
  sendBroadcast_pre intt icmp Prelude.Nothing s

sendStickyBroadcast_post :: Intent0 -> ICmp -> System -> System
sendStickyBroadcast_post intt icmp s =
  startActivity_post intt icmp s

sendStickyBroadcast_safe :: Intent0 -> ICmp -> System -> Result0
sendStickyBroadcast_safe intt icmp s =
  case sendStickyBroadcast_pre intt icmp s of {
   Prelude.Just ec -> Result (Error0 ec) s;
   Prelude.Nothing -> Result Ok (sendStickyBroadcast_post intt icmp s)}

resolveIntent_pre :: Intent0 -> IdApp -> System -> Prelude.Maybe ErrorCode
resolveIntent_pre i a s =
  let {allCmpsA = getAllCmps a s} in
  let {allActsA = filter isActivityBool allCmpsA} in
  let {allServsA = filter isServiceBool allCmpsA} in
  let {allBroadsA = filter isBroadReceiverBool allCmpsA} in
  let {theId = idI i} in
  case Prelude.not (isAppInstalledBool a s) of {
   Prelude.True -> Prelude.Just No_such_intt;
   Prelude.False ->
    case existsb (\pair ->
           let {ic = fst pair} in
           let {intt = snd pair} in
           (Prelude.&&)
             ((Prelude.&&) (Prelude.not (isSomethingBool (cmpName intt)))
               (case idInt_eq (idI intt) theId of {
                 Prelude.True -> Prelude.True;
                 Prelude.False -> Prelude.False}))
             (case map_apply iCmp_eq (running (state s)) ic of {
               Value c1 ->
                let {
                 startableCmps = case intType intt of {
                                  IntActivity ->
                                   filter (\c2 -> canStartBool c1 c2 s)
                                     allActsA;
                                  IntService ->
                                   filter (\c2 -> canStartBool c1 c2 s)
                                     allServsA;
                                  IntBroadcast ->
                                   filter (\c2 -> canStartBool c1 c2 s)
                                     allBroadsA}}
                in
                existsb (\iFil ->
                  (Prelude.&&)
                    ((Prelude.&&) (actionTestBool intt iFil s)
                      (categoryTestBool intt iFil s))
                    (dataTestBool intt iFil s))
                  (concat (map getFilters startableCmps));
               Error _ -> Prelude.False})) (sentIntents (state s)) of {
     Prelude.True -> Prelude.Nothing;
     Prelude.False -> Prelude.Just No_such_intt}}

resolveIntent_post :: Intent0 -> IdApp -> System -> System
resolveIntent_post intt a s =
  let {oldstate = state s} in
  let {oldenv = environment s} in
  Sys (St (apps oldstate) (alreadyRun oldstate) (grantedPermGroups oldstate)
  (perms oldstate) (running oldstate) (delPPerms oldstate)
  (delTPerms oldstate) (resCont oldstate)
  (resolveImplicitToExplicitIntent intt a s)) oldenv

resolveIntent_safe :: Intent0 -> IdApp -> System -> Result0
resolveIntent_safe intt a s =
  case resolveIntent_pre intt a s of {
   Prelude.Just ec -> Result (Error0 ec) s;
   Prelude.Nothing -> Result Ok (resolveIntent_post intt a s)}

receiveIntent_pre :: Intent0 -> ICmp -> IdApp -> System -> Prelude.Maybe
                     ErrorCode
receiveIntent_pre i ic a s =
  case maybeIntentForAppCmp i a ic s of {
   Prelude.Just c ->
    case isCProviderBool c of {
     Prelude.True -> Prelude.Just Cmp_is_CProvider;
     Prelude.False ->
      case Prelude.not (canRunBool a s) of {
       Prelude.True -> Prelude.Just Should_verify_permissions;
       Prelude.False ->
        case map_apply iCmp_eq (running (state s)) ic of {
         Value c' ->
          case isCProviderBool c' of {
           Prelude.True -> Prelude.Just Cmp_is_CProvider;
           Prelude.False ->
            case Prelude.not (canStartBool c' c s) of {
             Prelude.True -> Prelude.Just A_cant_start_b;
             Prelude.False ->
              case intType i of {
               IntActivity ->
                case path (data0 i) of {
                 Prelude.Just u ->
                  let {allComponents = getAllComponents s} in
                  case existsb
                         (receiveIntentCmpRequirements c' u s
                           (intentActionType i)) allComponents of {
                   Prelude.True -> Prelude.Nothing;
                   Prelude.False -> Prelude.Just No_CProvider_fits};
                 Prelude.Nothing -> Prelude.Nothing};
               IntService -> Prelude.Nothing;
               IntBroadcast ->
                case brperm i of {
                 Prelude.Just p ->
                  case appHasPermissionBool a p s of {
                   Prelude.True -> Prelude.Nothing;
                   Prelude.False -> Prelude.Just Not_enough_permissions};
                 Prelude.Nothing -> Prelude.Nothing}}}};
         Error _ -> Prelude.Just Instance_not_running}}};
   Prelude.Nothing -> Prelude.Just No_such_intt}

receiveIntent_post :: Intent0 -> ICmp -> IdApp -> System -> System
receiveIntent_post intt ic a s =
  case maybeIntentForAppCmp intt a ic s of {
   Prelude.Just c ->
    let {oldstate = state s} in
    let {oldenv = environment s} in
    let {runningicmps = map_getKeys (running oldstate)} in
    let {newAlreadyRun = (:) a (alreadyRun oldstate)} in
    let {ic' = iCmpGenerator runningicmps} in
    let {
     newTPerms = case intType intt of {
                  IntActivity ->
                   case path (data0 intt) of {
                    Prelude.Just u ->
                     let {cp = getAnyCProviderWithUri u s} in
                     performGrantTempPerm (intentActionType intt) u cp ic' s;
                    Prelude.Nothing -> delTPerms oldstate};
                  _ -> delTPerms oldstate}}
    in
    Sys (St (apps oldstate) newAlreadyRun (grantedPermGroups oldstate)
    (perms oldstate) (performRunCmp intt ic' c s) (delPPerms oldstate)
    newTPerms (resCont oldstate)
    (remove sentIntentsElems_eq ((,) ic intt) (sentIntents oldstate))) oldenv;
   Prelude.Nothing -> s}

receiveIntent_safe :: Intent0 -> ICmp -> IdApp -> System -> Result0
receiveIntent_safe intt ic a s =
  case receiveIntent_pre intt ic a s of {
   Prelude.Just ec -> Result (Error0 ec) s;
   Prelude.Nothing -> Result Ok (receiveIntent_post intt ic a s)}

stop_pre :: ICmp -> System -> Prelude.Maybe ErrorCode
stop_pre icmp s =
  case is_ValueBool (map_apply iCmp_eq (running (state s)) icmp) of {
   Prelude.True -> Prelude.Nothing;
   Prelude.False -> Prelude.Just Instance_not_running}

stop_post :: ICmp -> System -> System
stop_post icmp s =
  let {oldstate = state s} in
  let {oldenv = environment s} in
  Sys (St (apps oldstate) (alreadyRun oldstate) (grantedPermGroups oldstate)
  (perms oldstate) (map_drop iCmp_eq (running oldstate) icmp)
  (delPPerms oldstate) (removeTPerms icmp oldstate) (resCont oldstate)
  (sentIntents oldstate)) oldenv

stop_safe :: ICmp -> System -> Result0
stop_safe icmp s =
  case stop_pre icmp s of {
   Prelude.Just ec -> Result (Error0 ec) s;
   Prelude.Nothing -> Result Ok (stop_post icmp s)}

grantP_pre :: ICmp -> CProvider -> IdApp -> Uri -> PType -> System ->
              Prelude.Maybe ErrorCode
grantP_pre icmp cp a u pt s =
  case Prelude.not (canGrantBool cp u s) of {
   Prelude.True -> Prelude.Just CProvider_not_grantable;
   Prelude.False ->
    case Prelude.not (existsResBool cp u s) of {
     Prelude.True -> Prelude.Just No_such_res;
     Prelude.False ->
      case Prelude.not (isAppInstalledBool a s) of {
       Prelude.True -> Prelude.Just No_such_app;
       Prelude.False ->
        case map_apply iCmp_eq (running (state s)) icmp of {
         Value c ->
          let {
           thiscanread = (Prelude.||) (canReadBool c cp s)
                           (delPermsBool c cp u Read s)}
          in
          let {
           thiscanwrite = (Prelude.||) (canWriteBool c cp s)
                            (delPermsBool c cp u Write s)}
          in
          case pt of {
           Read ->
            case Prelude.not thiscanread of {
             Prelude.True -> Prelude.Just Not_enough_permissions;
             Prelude.False -> Prelude.Nothing};
           Write ->
            case Prelude.not thiscanwrite of {
             Prelude.True -> Prelude.Just Not_enough_permissions;
             Prelude.False -> Prelude.Nothing};
           Both ->
            case (Prelude.||) (Prelude.not thiscanread)
                   (Prelude.not thiscanwrite) of {
             Prelude.True -> Prelude.Just Not_enough_permissions;
             Prelude.False -> Prelude.Nothing}};
         Error _ -> Prelude.Just Instance_not_running}}}}

grantP_post :: ICmp -> CProvider -> IdApp -> Uri -> PType -> System -> System
grantP_post _ cp a u pt s =
  let {oldstate = state s} in
  let {oldenv = environment s} in
  Sys (St (apps oldstate) (alreadyRun oldstate) (grantedPermGroups oldstate)
  (perms oldstate) (running oldstate)
  (addDelPPerm (delPPerms oldstate) ((,) ((,) a cp) u) pt)
  (delTPerms oldstate) (resCont oldstate) (sentIntents oldstate)) oldenv

grantP_safe :: ICmp -> CProvider -> IdApp -> Uri -> PType -> System ->
               Result0
grantP_safe icmp cp a u pt s =
  case grantP_pre icmp cp a u pt s of {
   Prelude.Just ec -> Result (Error0 ec) s;
   Prelude.Nothing -> Result Ok (grantP_post icmp cp a u pt s)}

revokeDel_pre :: ICmp -> CProvider -> Uri -> PType -> System -> Prelude.Maybe
                 ErrorCode
revokeDel_pre icmp cp u pt s =
  case Prelude.not (existsResBool cp u s) of {
   Prelude.True -> Prelude.Just No_such_res;
   Prelude.False ->
    case map_apply iCmp_eq (running (state s)) icmp of {
     Value c ->
      let {
       thiscanread = (Prelude.||) (canReadBool c cp s)
                       (delPermsBool c cp u Read s)}
      in
      let {
       thiscanwrite = (Prelude.||) (canWriteBool c cp s)
                        (delPermsBool c cp u Write s)}
      in
      case pt of {
       Read ->
        case Prelude.not thiscanread of {
         Prelude.True -> Prelude.Just Not_enough_permissions;
         Prelude.False -> Prelude.Nothing};
       Write ->
        case Prelude.not thiscanwrite of {
         Prelude.True -> Prelude.Just Not_enough_permissions;
         Prelude.False -> Prelude.Nothing};
       Both ->
        case (Prelude.||) (Prelude.not thiscanread)
               (Prelude.not thiscanwrite) of {
         Prelude.True -> Prelude.Just Not_enough_permissions;
         Prelude.False -> Prelude.Nothing}};
     Error _ -> Prelude.Just Instance_not_running}}

revokeDel_post :: ICmp -> CProvider -> Uri -> PType -> System -> System
revokeDel_post _ cp u pt s =
  let {oldstate = state s} in
  let {oldenv = environment s} in
  Sys (St (apps oldstate) (alreadyRun oldstate) (grantedPermGroups oldstate)
  (perms oldstate) (running oldstate)
  (removeAllPerms delppermsdomeq (delPPerms oldstate) cp u pt)
  (removeAllPerms deltpermsdomeq (delTPerms oldstate) cp u pt)
  (resCont oldstate) (sentIntents oldstate)) oldenv

revokeDel_safe :: ICmp -> CProvider -> Uri -> PType -> System -> Result0
revokeDel_safe icmp cp u pt s =
  case revokeDel_pre icmp cp u pt s of {
   Prelude.Just ec -> Result (Error0 ec) s;
   Prelude.Nothing -> Result Ok (revokeDel_post icmp cp u pt s)}

call_pre :: ICmp -> SACall -> System -> Prelude.Maybe ErrorCode
call_pre icmp sac s =
  case map_apply iCmp_eq (running (state s)) icmp of {
   Value c ->
    let {a = getAppFromCmp c s} in
    case existsb (\p -> Prelude.not (appHasPermissionBool a p s))
           (getMandatoryPerms sac) of {
     Prelude.True -> Prelude.Just Not_enough_permissions;
     Prelude.False -> Prelude.Nothing};
   Error _ -> Prelude.Just Instance_not_running}

call_post :: ICmp -> SACall -> System -> System
call_post _ _ s =
  s

call_safe :: ICmp -> SACall -> System -> Result0
call_safe icmp sac s =
  case call_pre icmp sac s of {
   Prelude.Just ec -> Result (Error0 ec) s;
   Prelude.Nothing -> Result Ok (call_post icmp sac s)}

verifyOldApp_pre :: IdApp -> System -> Prelude.Maybe ErrorCode
verifyOldApp_pre =
  Prelude.error "AXIOM TO BE REALIZED"

verifyOldApp_post :: IdApp -> System -> System
verifyOldApp_post =
  Prelude.error "AXIOM TO BE REALIZED"

verifyOldApp_safe :: IdApp -> System -> Result0
verifyOldApp_safe a s =
  case verifyOldApp_pre a s of {
   Prelude.Just ec -> Result (Error0 ec) s;
   Prelude.Nothing -> Result Ok (verifyOldApp_post a s)}

step :: System -> Action -> Result0
step s a =
  case a of {
   Install app0 m c lRes -> install_safe app0 m c lRes s;
   Uninstall app0 -> uninstall_safe app0 s;
   Grant p app0 -> grant_safe p app0 s;
   GrantAuto p app0 -> grantAuto_safe p app0 s;
   Revoke p app0 -> revoke_safe p app0 s;
   RevokePermGroup grp app0 -> revokegroup_safe grp app0 s;
   HasPermission _ _ -> Result Ok s;
   Read0 ic cp u -> read_safe ic cp u s;
   Write0 ic cp u v -> write_safe ic cp u v s;
   StartActivity intt ic -> startActivity_safe intt ic s;
   StartActivityForResult intt _ ic -> startActivity_safe intt ic s;
   StartService intt ic -> startService_safe intt ic s;
   SendBroadcast intt ic p -> sendBroadcast_safe intt ic p s;
   SendOrderedBroadcast intt ic p -> sendBroadcast_safe intt ic p s;
   SendStickyBroadcast intt ic -> sendStickyBroadcast_safe intt ic s;
   ResolveIntent intt a0 -> resolveIntent_safe intt a0 s;
   ReceiveIntent intt ic a0 -> receiveIntent_safe intt ic a0 s;
   Stop ic -> stop_safe ic s;
   GrantP ic cp a0 u pt -> grantP_safe ic cp a0 u pt s;
   RevokeDel ic cp u pt -> revokeDel_safe ic cp u pt s;
   Call ic sac -> call_safe ic sac s;
   VerifyOldApp a0 -> verifyOldApp_safe a0 s}

trace :: System -> (([]) Action) -> ([]) System
trace s actions =
  case actions of {
   ([]) -> ([]);
   (:) action0 rest ->
    let {sys = system (step s action0)} in (:) sys (trace sys rest)}

