--
-- Time-stamp: <2026-04-28 Tue 10:01 EDT - george@valhalla>
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

def isLower (s : String) : Bool :=
  match s.toList with
  | c :: _ => c.isLower
  | [] => false

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
  
def parseField (fuel : Nat): Parser (Field RawExpression) := fun toks =>
  match fuel with
  | 0 => .error noFuel
  | n+1 => do
    let (id, toks') ← parseString toks
    let (_, toks'') ← parseSymbol .Eq toks'
    let (expr, toks''') ← parseRawExpression n toks''
    pure (Field.mk id expr, toks''')
  
def parseFields (fuel : Nat) (acc : List (Field RawExpression)) 
    : Parser (List (Field RawExpression)) := fun toks =>
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
    
def parseRawExpressionList (fuel : Nat) (acc : List RawExpression) 
    : Parser (List RawExpression) := fun toks => 
  match fuel with 
  | 0 => .error noFuel
  | n+1 => 
    match toks with
      | [] => .ok (acc.reverse, [])
      | Token.rbracket :: rest => Except.ok (acc.reverse, rest)
      | Token.comma :: rest => parseRawExpressionList n acc rest
      | _ => do
        let (expr, toks') ← parseRawExpression n toks
        parseRawExpressionList n (expr :: acc) toks'

def parseRawExpression  (fuel : Nat) : Parser RawExpression := fun toks =>
  match fuel with
  | 0 => .error noFuel
  | n+1 => 
    match toks with
    | [] => Except.error "nothing to parse"
    | tok :: rest  => match tok with
      | Token.strLit s => Except.ok (RawExpression.StrLit s, rest)
      | Token.natLit n => Except.ok (RawExpression.NatLit n, rest)
      | Token.lbracket => do
        let (exprs,toks') ← parseRawExpressionList n [] rest
        pure (RawExpression.EList exprs,toks')
      | Token.ident ident => 
        
        -- uncapitilized Token.ident → RawExpression.Id
        if isLower ident then                           
          Except.ok (RawExpression.Id ident, rest)
        
        -- capitalized Token.ident → RawExpression.Constructor          
        else                                         
          match rest with
          | [] => Except.ok (RawExpression.Constructor ident [], [])
          | tok' :: rest' => 
            match tok' with
            | Token.lbrace => do
              let (fields,rest'') ← parseFields n [] rest'
              pure (RawExpression.Constructor ident fields,rest'')
            | _ => Except.ok (RawExpression.Constructor ident [], rest)
      | _ => Except.error "mal-formed"

end
--------------------------------------------------------------------------------


def parseTopLevel : Parser TopLevel := fun toks =>
  match toks with 
    | [] => Except.error "nothing to parse"
    | .ident "let" :: rest => do
      let (.mk id rexpr,rest')  ← parseField toks.length rest            
      .ok (TopLevel.Let id rexpr,rest')
    | _ => do
      let (expr,rest') ← parseRawExpression toks.length toks
      .ok (TopLevel.Expr expr,rest')
 
 def parseTopLevelList : Parser (List TopLevel) := fun toks =>
  go toks.length toks
where
  go : Nat → Parser (List TopLevel)
  | 0, _ => .error noFuel
  | _, [] => .ok ([], [])
  | n+1, toks => do
    let (tl, rest) ← parseTopLevel toks
    let (tls, rest') ← go n rest
    .ok (tl :: tls, rest')

