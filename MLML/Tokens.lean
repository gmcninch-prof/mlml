-- 
-- Time-stamp: <2026-04-30 Thu 13:25 EDT - george@valhalla>
--

inductive Token
  | ident (s : String)   
  | strLit (s : String)  
  | natLit (n : Nat)
  | boolLit (b : Bool)
  | lbrace | rbrace      
  | lbracket | rbracket  
  | comma | colon | equals
  | eof
  | comment (s : String)
deriving Repr, BEq

def Char.isIdentChar (c : Char) := c.isAlpha || c == '_'
def Char.isIdentContinue (c : Char) :=
  c.isIdentChar || c.isDigit || ":-._+".contains c 

inductive CharAccum
  | none
  | string (cs : List Char)
  | digits (cs : List Char)
  | ident (cs : List Char)
  | comment (cs : List Char)
  
def notComment : Token → Bool
  | .comment _ => False
  | _ => True
  
structure Accum where
  chars : CharAccum
  tokens : List Token

def start : Accum := { chars := CharAccum.none, tokens := [] }

def tokenize (input : String) : List Token :=
  let res := input.foldl go start
  List.filter notComment (flush res).reverse
where
  processChar (c:Char) (tokens : List Token) : Accum := 
    match c with
    | '{' => Accum.mk CharAccum.none (Token.lbrace :: tokens)
    | '}' => Accum.mk CharAccum.none (Token.rbrace :: tokens) 
    | '[' => Accum.mk CharAccum.none (Token.lbracket :: tokens) 
    | ']' => Accum.mk CharAccum.none (Token.rbracket :: tokens) 
    | ',' => Accum.mk CharAccum.none (Token.comma :: tokens)  
    | ':' => Accum.mk CharAccum.none (Token.colon :: tokens) 
    | '=' => Accum.mk CharAccum.none (Token.equals :: tokens)
    | ';' => Accum.mk (CharAccum.comment []) tokens -- start a comment
    | '\x22' =>
      Accum.mk (CharAccum.string []) tokens  -- start a string
    | c => 
      if c.isIdentChar then
        Accum.mk (CharAccum.ident [c]) tokens  -- start an identifier
      else if c.isDigit then
        Accum.mk (CharAccum.digits [c]) tokens  -- start a digit sequence       
      else if c.isWhitespace then
        Accum.mk CharAccum.none tokens       -- skip
      else
        Accum.mk CharAccum.none tokens      -- unknown; skip or error

  flushIdent (cs : List Char) (tokens : List Token) : List Token :=
    match String.ofList cs.reverse with
    | "True" => Token.boolLit true :: tokens
    | "False" => Token.boolLit false :: tokens
    | s => Token.ident s :: tokens          
          
  go (a : Accum) (c:Char) :=
    match a.chars with
    | CharAccum.string cs => 
      match c with
      | '\x22' =>
        let s := String.ofList cs.reverse
        Accum.mk CharAccum.none (Token.strLit s::a.tokens)
      | c =>
        Accum.mk (CharAccum.string (c :: cs)) a.tokens  -- continue getting string literal
    | CharAccum.ident cs =>
      if c.isIdentContinue then
        Accum.mk (CharAccum.ident (c :: cs)) a.tokens -- continue getting identifier
      else
        processChar c <| flushIdent cs a.tokens
    | CharAccum.digits cs =>
      if c.isDigit then
        Accum.mk (CharAccum.digits (c :: cs)) a.tokens -- continue getting digits
      else
        let n := (String.ofList cs.reverse).toNat!
        processChar c <| Token.natLit n :: a.tokens
    | CharAccum.comment cs =>
      match c with
      | '\n' => 
        let s := (String.ofList cs.reverse).trimAscii.toString
        Accum.mk CharAccum.none (Token.comment s :: a.tokens)
      | _ =>
        Accum.mk (CharAccum.comment (c:: cs)) a.tokens  -- continue getting comment
    | CharAccum.none => 
      processChar c a.tokens

  flush (a : Accum) : List Token :=
    match a.chars with 
    | CharAccum.ident cs => flushIdent cs a.tokens 
    | CharAccum.digits cs => (Token.natLit (String.ofList cs.reverse).toNat!) :: a.tokens
    | _ => a.tokens


