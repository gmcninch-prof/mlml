import Init.System.IO
import MLML
import MLML.Codec

inductive Pet 
  | Cat 
  | Dog
  | Hamster
deriving Repr

structure MyData where
  name : String
  age  : Nat
  pet : Pet
  children : List String
deriving Repr
  
def s := "
MyData { 
  name = alice
  children = children
  pet = Cat
  age = 38  
}

let alice = \"Alice\"
let children = [ \"Bob\" \"Cathy\" ]  
"

open Codec in
instance : Codec.Decode Pet where
  decode
    | .Constructor "Cat" [] => .ok Pet.Cat
    | .Constructor "Dog" [] => .ok Pet.Dog
    | e => .error s!"Expected Pet, received {repr e}"

open Codec in  
instance : Codec.Decode MyData where
  decode
    | .Constructor "MyData" fs => do
      let name     ← decodeField "name" fs
      let age      ← decodeField "age" fs
      let pet      ← decodeField "pet" fs
      let children ← decodeField "children" fs
      pure <| { name, age, children , pet }
    | e => .error s!"expected MyData, got {repr e}"
  

def testdata := [ "data/test1.mlml", "data/test2.mlml" ] 
    
    
def test (fn : String) : IO Unit := do 
  let (s : String)  ← IO.FS.readFile fn
    match expressionFromString s with
    | .ok expr => IO.println expr
    | .error s => IO.println s
    
def main : IO Unit := do
  match (@parseAndDecode MyData _ s) with
  | .ok md => IO.println <| reprStr md
  | .error e => IO.println e

  testdata.forM test


#eval main

-- #guard (tokenize "id = \"foo\"") == [ ... ]
