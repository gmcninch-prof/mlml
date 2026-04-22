--
-- Time-stamp: <2026-04-22 Wed 12:50 EDT - george@sortilege>
--
import MLML.Tokens
import MLML.Expression

/- BNF
file      ::= binding*
binding   ::= ident '=' expr
expr      ::= record | list | strLit | natLit | ident | constructor
record    ::= '{' field* '}'
field     ::= ident '=' expr
list      ::= '[' (expr (',' expr)*)? ']'
constructor ::= ident record
-/

inductive Symbol where
  | LBracket | RBracket | LBrace | RBrace | Comma |Eq
deriving Repr, BEq

def symbolToken : Symbol -> Token 
  | .LBracket => Token.lbracket
  | .RBracket => Token.rbracket
  | .LBrace => Token.lbrace
  | .RBrace => Token.rbrace
  | .Comma => Token.comma
  | .Eq => Token.equals
  
def Parser (α : Type) := 
  (toks : List Token) → Except String (α × List Token)

def noFuel : String := "parser error: input too deeply nested" 

instance : Monad Parser where
  pure a := fun toks => Except.ok (a, toks)
  bind p f := fun toks => do
    let (a, toks') ← p toks
    f a toks'

instance : MonadExcept String Parser where
  throw e := fun _ => Except.error e
  tryCatch p f := fun toks =>
    match p toks with
    | Except.error e => f e toks
    | ok => ok

instance : Alternative Parser where
  failure := fun _ => Except.error "failure"
  orElse p q := fun toks =>
    match p toks with
    | Except.error _ => q () toks
    | ok => ok  
  
def parseSymbol (sym:Symbol) : Parser Symbol :=
  let stok := symbolToken sym 
  fun toks =>
    match toks with
    | [] => Except.error "nothing to parse"
    | tok :: rest => 
      if tok == stok then
        Except.ok (sym,rest)
      else
        Except.error s!"Expected {reprStr stok} but got {reprStr tok}"

def parseString : Parser String :=
  fun toks =>
  match toks with
  | [] => Except.error "nothing to parse"
  | tok :: rest => match tok with
    | Token.strLit s => Except.ok (s,rest)
    | Token.ident s => Except.ok (s,rest)
    | _ => Except.error s!"wrong type: {reprStr tok} is not an string."

def parseNat : Parser Nat :=
  fun toks =>
  match toks with
  | [] => Except.error "nothing to parse"
  | tok :: rest => match tok with
    | Token.natLit n => Except.ok (n,rest)
    | _ => Except.error s!"wrong type: {reprStr tok} is not a Nat."


def parseBool : Parser Bool :=
  fun toks =>
  match toks with
  | [] => Except.error "nothing to parse"
  | tok :: rest => match tok with
    | Token.boolLit b => Except.ok (b,rest)
    | _ => Except.error s!"wrong type: {reprStr tok} is not a Bool."

--------------------------------------------------------------------------------
mutual
  
def parseField (fuel : Nat): Parser Field := fun toks =>
  match fuel with
  | 0 => .error noFuel
  | n+1 => do
    let (id, toks') ← parseString toks
    let (_, toks'') ← parseSymbol .Eq toks'
    let (expr, toks''') ← parseExpression' n toks''
    pure (Field.mk id expr, toks''')
  
def parseFields (fuel : Nat) (acc : List Field) 
    : Parser (List Field) := fun toks =>
  match fuel with
  | 0 => .error noFuel
  | n+1 =>
    match toks with
    | [] => .ok (acc.reverse, [])
    | Token.rbrace :: rest => Except.ok (acc.reverse, rest)
    | Token.comma :: rest => parseFields n acc rest
    | _ => do
      let (f,toks') ← parseField n toks
      parseFields n (f :: acc) toks' 
    
def parseExpressionList' (fuel : Nat) (acc : List Expression) 
    : Parser (List Expression) := fun toks => 
  match fuel with 
  | 0 => .error noFuel
  | n+1 => 
    match toks with
      | [] => .ok (acc.reverse, [])
      | Token.rbracket :: rest => Except.ok (acc.reverse, rest)
      | Token.comma :: rest => parseExpressionList' n acc rest
      | _ => do
        let (expr, toks') ← parseExpression' n toks
        parseExpressionList' n (expr :: acc) toks'

def parseExpressionList (acc : List Expression) :
    Parser (List Expression) := fun toks =>
  parseExpressionList' toks.length acc toks

def parseExpression' (fuel : Nat) : Parser Expression := fun toks =>
  match fuel with
  | 0 => .error noFuel
  | n+1 => 
    match toks with
    | [] => Except.error "nothing to parse"
    | tok :: rest  => match tok with
      | Token.strLit s => Except.ok (Expression.StrLit s, rest)
      | Token.natLit n => Except.ok (Expression.NatLit n, rest)
      | Token.lbracket => do
        let (exprs,toks') ← parseExpressionList' n [] rest
        pure (Expression.EList exprs,toks')
      | Token.ident id => 
        match rest with
        | [] => Except.ok (Expression.Id id, [])
        | tok' :: rest' => 
          match tok' with
          | Token.lbrace => do
            let (fields,toks'') ← parseFields n [] rest'
            pure (Expression.Constructor id fields,toks'')
          | _ => Except.ok (Expression.Id id, rest)
      | _ => 
        Except.error "mal-formed"

def parseExpression : Parser Expression := fun toks =>
  parseExpression' toks.length toks


end
--------------------------------------------------------------------------------


 
