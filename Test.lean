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
  
def s1 := "
MyData { 
  name = alice
  children = children
  pet = Cat
  age = 38  
}

let alice = \"Alice\"
let children = [ \"Bob\" \"Cathy\" ]  
"


def s2 := "
let c = Test {
    a = 1
    b = 2
    c = \"3\"
  }

Test {
  a = 1
  b = 2
  c = c
}"

def s3 := "
Test {
  a = 1
  b = 2
  c = Test 
    a = 1
    b = 2
    c = \"3\"
  }
}
"

open Codec in
instance : Codec.Decode Pet where
  decode
    | .Record "Cat" [] => .ok Pet.Cat
    | .Record "Dog" [] => .ok Pet.Dog
    | e => .error s!"Expected Pet, received {repr e}"

open Codec in  
instance : Codec.Decode MyData where
  decode
    | .Record "MyData" fs => do
      let name     ← decodeField "name" fs
      let age      ← decodeField "age" fs
      let pet      ← decodeField "pet" fs
      let children ← decodeField "children" fs
      pure <| { name, age, children , pet }
    | e => .error s!"expected MyData, got {repr e}"
    
def test (s : String) : IO Unit := do 
    match expressionFromString s with
    | .ok expr => IO.println expr
    | .error s => IO.println s
    
def main : IO Unit := do
  match (@parseAndDecode MyData _ s1) with
  | .ok md => IO.println <| reprStr md
  | .error e => IO.println e

  [ s2, s3 ].forM test


--#eval main

-- #guard (tokenize "id = \"foo\"") == [ ... ]
