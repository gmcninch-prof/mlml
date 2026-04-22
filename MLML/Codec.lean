--
-- Time-stamp: <2026-04-22 Wed 12:49 EDT - george@sortilege>
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

def decodeField [Decode α] (name : String) (fs : List Field) : Except String α :=
  lookupField name fs >>= Decode.decode

instance [Decode α] : Decode (List α) where
  decode
    | .EList es => es.mapM Decode.decode
    | e => .error s!"expected list, got {repr e}"

instance : Decode String where
  decode
    | .StrLit s => .ok s
    | .Id s => .ok s
    | e => .error s!"expected raw string or id, got {repr e}"
    
instance : Decode Nat where
  decode
    | .NatLit n => .ok n
    | e => .error s!"expected raw Nat, got {repr e}"

instance : Decode Bool where
  decode
    | .BoolLit b => .ok b
    | e => .error s!"expected raw Nat, got {repr e}"


end Codec
--------------------------------------------------------------------------------
