
import MLML.Codec
import MLML.Expression
import MLML.Parse

def expressionFromString : String → Except String Expression :=
  fun s => do
    let toks := tokenize s
    let (expr, rest) ← parseExpression toks
    if rest.isEmpty then 
      pure expr
    else
      .error s!"unexpected tokens after expression: {repr rest}"


def parseAndDecode {α : Type} [Codec.Decode α]: String → Except String α := 
  fun s => do
    let toks := tokenize s
    let (expr, rest) ← parseExpression toks
    if rest.isEmpty then 
      Codec.Decode.decode expr    
    else 
      .error s!"unexpected tokens after expression: {repr rest}"
         
