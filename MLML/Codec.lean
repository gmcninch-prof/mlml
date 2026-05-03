--
-- Time-stamp: <2026-05-03 Sun 13:28 EDT - george@valhalla>
--

import MLML.Expression
open Expression 

--------------------------------------------------------------------------------
namespace Codec

class Decode (α : Type) where
  decode : Expression → Except String α

instance : Alternative (Except String) where
  failure := Except.error "no alternative matched"
  orElse a b := match a with
    | Except.ok x  => Except.ok x
    | Except.error _ => b ()

def decodeField [Decode α] (name : String) (fs : List (Field Expression)) 
    : Except String α :=
  lookupField name fs >>= Decode.decode

instance [Decode α] : Decode (List α) where
  decode
    | .EList es => es.mapM Decode.decode
    | e => .error s!"expected list, got {repr e}"

instance : Decode String where
  decode
    | .StrLit s => .ok s
    | e => .error s!"expected raw string, got {repr e}"
    
instance : Decode Nat where
  decode
    | .NatLit n => .ok n
    | e => .error s!"expected raw Nat, got {repr e}"

instance : Decode Bool where
  decode
    | .BoolLit b => .ok b
    | e => .error s!"expected raw Nat, got {repr e}"


-- Expression-level Option decoder 
instance [Codec.Decode α] : Codec.Decode (Option α) where
  decode
    | .Record "none" [] => .ok none
    | .Record "some" fs => do
        let v ← Codec.decodeField "val" fs
        .ok (some v)
    | e => .error s!"expected none/some constructor, got {repr e}"

-- Field-level: absent → none, present → decoded value
def Codec.decodeFieldOpt [Codec.Decode α] (name : String) (fs : List (Field Expression))
    : Except String (Option α) :=
  match lookupField name fs with
  | .error _ => .ok none          -- missing field ↦ none
  | .ok expr => Codec.Decode.decode expr |>.map some


end Codec
--------------------------------------------------------------------------------


-- at call site for "optional fields"

-- instance : Codec.Decode MyStruct where
--   decode
--     | .Record "MyStruct" fs => do
--         let x ← Codec.decodeField    "requiredField" fs
--         let y ← Codec.decodeFieldOpt "optionalField" fs
--         .ok { x, y }
--     | e => .error s!"expected MyStruct, got {repr e}"
