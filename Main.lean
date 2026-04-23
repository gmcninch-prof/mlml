import Init.System.IO
import MLML

def testdata := "data/test.mlml"

def main : IO Unit := do
  let (s : String)  ← IO.FS.readFile testdata
  match expressionFromString s with
  | .ok expr => IO.println expr
  | .error s => IO.println s
