import Init.System.IO
import MLML
import MLML.Codec

inductive Pet 
  | Cat 
  | Dog
  | Hamster
deriving Repr

structure MyData  where
  name : String
  age  : Nat
  pet : Pet
  children : (List String)
deriving Repr

structure MyDataF (f: Type → Type)  where
  name : f String
  age  : f Nat
  pet : f Pet
  children : f (List String)


open Codec in
instance : Decode Pet where
  decode
    | .Record "Cat" [] => .ok Pet.Cat
    | .Record "Dog" [] => .ok Pet.Dog
    | e => .error s!"Expected Pet, received {repr e}"

open Codec in  
instance : DecodeRecord MyDataF where
  decodeFields fs := {
      name     := decodeField "name" fs,
      age      := decodeField "age" fs,
      pet      := decodeField "pet" fs,
      children := decodeField "children" fs
      }
  collect x := do
    let name ← x.name
    let age  ← x.age 
    let pet  ← x.pet
    let children ← x.children
    pure { name, age, pet, children }
  errors x := checkFields x
    [ forget ∘ MyDataF.name
    , forget ∘ MyDataF.age
    , forget ∘ MyDataF.pet
    , forget ∘ MyDataF.children
    ]

-- Decode instance for Person uses PersonF internally but returns plain Person
open Codec in
instance : Decode MyData where
  decode e := do
    let p ← decodeRecord (R := MyDataF) "MyData" e
    return { name := p.name, age := p.age, pet := p.pet, children := p.children }



def s1 := "
MyData { 
  name = alice
  children = children
 ;; pet = Cat
 ;; age = 38  
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
    
def test (s : String) : IO Unit := do 
    match expressionFromString s with
    | .ok expr => IO.println expr
    | .error s => IO.println s
    
def main : IO Unit := do
  match (@parseAndDecode MyData _ s1) with
  | .ok md => IO.println <| reprStr md
  | .error e => IO.println e
  
  IO.println <| String.intercalate "\n" (checkErrors "MyData" MyDataF s1) 
  
  [ s2, s3 ].forM test


#eval main

-- #guard (tokenize "id = \"foo\"") == [ ... ]
