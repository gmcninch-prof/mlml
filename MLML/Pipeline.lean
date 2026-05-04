
import MLML.Codec
import MLML.Expression
import MLML.Parse

def expressionFromString : String → Except String (Expression .Resolved) :=
  fun s => do
    let toks := tokenize s
    let (ltl, _) ← parseTopLevelList toks
    let env ← collectBindings ltl
    extractExpression env ltl

def parseAndDecode {α : Type} [Codec.Decode α]: String → Except String α := 
  fun s => do
    let expr ← expressionFromString s
    Codec.Decode.decode expr
         


def checkErrors (recordId : String) (R : (Type → Type) → Type) 
    [Codec.DecodeRecord R] : String → List String :=
  fun s => 
    match  expressionFromString s with
    | .ok e => Codec.decodeErrorRecord recordId R e
    | .error err => [ err ]
    

