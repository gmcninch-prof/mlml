--
-- Time-stamp: <2026-05-04 Mon 10:50 EDT - george@valhalla>
--

--------------------------------------------------------------------------------

inductive Phase where | Raw | Resolved

-- The "extension point" — controls whether Id is possible
def IdPayload : Phase → Type
  | .Raw      => Unit    -- Id constructor exists
  | .Resolved => Empty   -- Id constructor is structurally impossible

instance {p : Phase} : Repr (IdPayload p) where
  reprPrec e _ := match p with
    | .Raw      => "Id"
    | .Resolved => Empty.elim e

--==============================================================================
mutual 
inductive Field (p : Phase) where
  | mk : String → Expression p → Field p
deriving Repr


inductive Expression (p: Phase) where
  | EList   : List (Expression p) → Expression p
  | StrLit  : String → Expression p
  | NatLit  : Nat → Expression p
  | BoolLit : Bool → Expression p
  | Record  : String → List (Field p) → Expression p
  | Id      : IdPayload p → String → Expression p
deriving Repr
end
--==============================================================================

inductive TopLevel where
| Let : String → Expression .Raw → TopLevel
| Expr : Expression .Raw → TopLevel

--------------------------------------------------------------------------------

def Field.name : Field E → String
| .mk name _ => name

--------------------------------------------------------------------------------

--==============================================================================
mutual 
  def Field.render { p : Phase}  (n : Nat) : Field p → String := fun field =>
    let indent := String.ofList (List.replicate (2 * n) ' ')
    match field with
    | .mk id val => indent ++ id ++ " = " ++ Expression.render n val

  def Expression.render { p : Phase} (n : Nat) : 
      Expression p → String := fun expr =>
    let indent := String.ofList (List.replicate (2 * n) ' ')
    match expr with
    | .EList xs =>
        let inner := String.ofList (List.replicate (2 * (n + 1)) ' ')
        let items := xs.attach.map (fun ⟨a, _⟩ => 
          inner ++ Expression.render (n + 1) a)
        "[\n" ++ String.intercalate "\n" items ++ "\n" ++ indent ++ "]"        
    | .StrLit s => "\"" ++ s ++ "\""
    | .NatLit n => toString n
    | .BoolLit b => toString b
    | .Record id lst =>
        let fields := lst.attach.map (fun ⟨a, _⟩ => Field.render (n + 1) a)
        id ++ " {\n" ++ String.intercalate "\n" fields ++ "\n" ++ indent ++ "}"
    | .Id _ ident => s!"*{ident}*"
end
--==============================================================================

instance : ToString (Expression p) where
  toString := Expression.render 0

instance : ToString (Field p) where
  toString := Field.render 0


def lookupField (name : String) (fields : List (Field p)) : Except String (Expression p) :=
  match fields.find? (fun f => f.name == name) with
  | some (.mk _ expr) => .ok expr
  | none => .error s!"missing field: {name}"


--------------------------------------------------------------------------------

abbrev Environment := List (String × (Expression .Resolved))

def lookupInEnvironment (id : String) (env :Environment) : Except String (Expression .Resolved) := 
  match List.lookup id env with
  | .some expr => .ok expr
  | .none => .error s!"Identifier {id} not found"


--==============================================================================
mutual


def resolve : Environment 
            → Expression .Raw 
            → Except String (Expression .Resolved) :=
  fun env rexp => do
    match rexp with
    | .EList rexps       => do
      let exps ← List.mapM (resolve env) rexps
      pure <| .EList exps
    | .StrLit s          => pure <| .StrLit s
    | .NatLit n          => pure <| .NatLit n
    | .BoolLit b         => pure <| .BoolLit b
    | .Record id rfs => do
      let fs ← List.mapM (resolveField env) rfs
      pure <| .Record id fs
    | .Id _ ident => do
      let value ← lookupInEnvironment ident env
      pure value

def resolveField : Environment 
                 → Field .Raw 
                 → Except String (Field .Resolved) :=
  fun env (.mk ident rexp) => do
    let exp ← resolve env rexp
    pure <| .mk ident exp
    
end
--==============================================================================

def collectBindings (tops : List TopLevel) : Except String Environment :=
  tops.foldlM (fun env top =>
    match top with
    | .Let name rawVal => do
        let val ← resolve env rawVal
        .ok ((name, val) :: env)
    | .Expr _ => .ok env) []


def extractExpression (env : Environment) (ltl : List TopLevel) : Except String (Expression .Resolved) := do
  let exprs := ltl.filterMap (fun | .Expr re => some re | _ => none)
  match exprs with
  | [] => .error "No expression found"
  | [re] => resolve env re
  | _ :: _ :: _ => .error "Multiple expressions found"
