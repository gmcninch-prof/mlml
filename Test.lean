import Init.System.IO
import MLML
import MLML.Codec

structure MyData where
  name : String
  age  : Nat
  children : List String
deriving Repr
  
def s := "
MyData { 
  name = \"George\"
  age = 58
  children = [ \"Gabe\" \"Nina\" ]
}"
  
open Codec in  
instance : Codec.Decode MyData where
  decode
    | .Constructor "MyData" fs => do
      let name     ← decodeField "name" fs
      let age      ← decodeField "age" fs
      let children ← decodeField "children" fs
      pure <| { name, age, children }
    | e => .error s!"expected MyData, got {repr e}"
    
def main : IO Unit := do
  match (@parseAndDecode MyData _ s) with
  | .ok md => IO.println <| reprStr md
  | .error e => IO.println e

#eval main
