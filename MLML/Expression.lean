--
-- Time-stamp: <2026-04-28 Tue 10:13 EDT - george@valhalla>
--

--------------------------------------------------------------------------------

inductive Field (E : Type) where
  | mk : String → E → Field E
deriving Repr

inductive RawExpression where
  | EList : List RawExpression -> RawExpression
  | StrLit : String -> RawExpression
  | NatLit : Nat -> RawExpression
  | BoolLit : Bool -> RawExpression
  | Id : String -> RawExpression
  | Constructor : String -> List (Field RawExpression) → RawExpression
deriving Repr  

  inductive TopLevel where
  | Let : String → RawExpression → TopLevel
  | Expr : RawExpression → TopLevel
  
inductive Expression where
  | EList : List Expression -> Expression
  | StrLit : String -> Expression
  | NatLit : Nat -> Expression
  | BoolLit : Bool -> Expression
  | Constructor : String -> List (Field Expression) → Expression
deriving Repr

--------------------------------------------------------------------------------

def Field.name : Field E → String
| .mk name _ => name

--------------------------------------------------------------------------------

mutual 
  def Field.render (n : Nat) : Field Expression -> String := fun field =>
    let indent := String.ofList (List.replicate (2 * n) ' ')
    match field with
    | .mk id val => indent ++ id ++ " = " ++ Expression.render n val

  def Expression.render (n : Nat) : Expression -> String := fun expr =>
    let indent := String.ofList (List.replicate (2 * n) ' ')
    match expr with
    | .EList xs =>
        let inner := String.ofList (List.replicate (2 * (n + 1)) ' ')
        let items := xs.attach.map (fun ⟨a, _⟩ => inner ++ Expression.render (n + 1) a)
        "[\n" ++ String.intercalate "\n" items ++ "\n" ++ indent ++ "]"        
    | .StrLit s => "\"" ++ s ++ "\""
    | .NatLit n => toString n
    | .BoolLit b => toString b
    | .Constructor id lst =>
        let fields := lst.attach.map (fun ⟨a, _⟩ => Field.render (n + 1) a)
        id ++ " {\n" ++ String.intercalate "\n" fields ++ "\n" ++ indent ++ "}"

end

instance : ToString Expression where
  toString := Expression.render 0

instance : ToString (Field Expression) where
  toString := Field.render 0


def lookupField (name : String) (fields : List (Field Expression)) : Except String Expression :=
  match fields.find? (fun f => f.name == name) with
  | some (.mk _ expr) => .ok expr
  | none => .error s!"missing field: {name}"


--------------------------------------------------------------------------------

abbrev Environment := List (String × Expression)

def lookupInEnvironment (id : String) (env :Environment) : Except String Expression := 
  match List.lookup id env with
  | .some expr => .ok expr
  | .none => .error s!"Identifier {id} not found"

mutual


def resolve : Environment → RawExpression → Except String Expression :=
  fun env rexp => do
    match rexp with
    | .EList rexps       => do
      let exps ← List.mapM (resolve env) rexps
      pure <| .EList exps
    | .StrLit s          => pure <| .StrLit s
    | .NatLit n          => pure <| .NatLit n
    | .BoolLit b         => pure <| .BoolLit b
    | .Constructor id rfs => do
      let fs ← List.mapM (resolveField env) rfs
      pure <| .Constructor id fs
    | .Id ident => do
      let value ← lookupInEnvironment ident env
      pure value

def resolveField : Environment → Field RawExpression → Except String (Field Expression) :=
  fun env (.mk ident rexp) => do
    let exp ← resolve env rexp
    pure <| .mk ident exp
    
end

def collectBindings (tops : List TopLevel) : Except String Environment :=
  tops.foldlM (fun env top =>
    match top with
    | .Let name rawVal => do
        let val ← resolve env rawVal
        .ok ((name, val) :: env)
    | .Expr _ => .ok env) []


def extractExpression (env : Environment) (ltl : List TopLevel) : Except String Expression := do
  let exprs := ltl.filterMap (fun | .Expr re => some re | _ => none)
  match exprs with
  | [] => .error "No expression found"
  | [re] => resolve env re
  | _ :: _ :: _ => .error "Multiple expressions found"
