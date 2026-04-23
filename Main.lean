import Init.System.IO

import MLML.Tokens

import MLML.Parse

import MLML.Codec

def getTokens (file : String) : IO (List Token) := do
  let (s : String)  ← IO.FS.readFile file
  pure <| tokenize s


def getExpression (file : String) : IO (Except String Expression) := do
  let (s : String)  ← IO.FS.readFile file
  let toks : List Token := tokenize s
  pure <| Except.map Prod.fst <| parseExpression toks 

def printExpression (file : String) : IO Unit := do
  let expr ← getExpression file 
  match expr with
  | .ok expr => IO.println <| expr.render 0
  | .error e => IO.println e

-- open Codec in  
-- def getSemester (file : String) : IO (Except String (List Semester.SemSpec)) := do
--   let (s : String)  ← IO.FS.readFile file
--   let toks : List Token := tokenize s
--   match Except.map Prod.fst <| parseExpression toks  with
--   | .ok expr => pure <| Decode.decode expr
--       --IO.println <| reprStr <| Decode.decode expr
--   | .error e => .error e

def testdata: String := "data/test.mlml" 

def main : IO Unit := do
  let expr ← getExpression testdata
  IO.println expr

-- #eval getTokens testdata

-- #eval getExpression testdata

-- #eval printExpression testdata
