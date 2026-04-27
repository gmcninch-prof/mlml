--
-- Time-stamp: <2026-04-27 Mon 17:29 EDT - george@sortilege>
--


--------------------------------------------------------------------------------

inductive Field (E : Type) where
  | mk : String → E → Field E
deriving Repr

  -- inductive Field where 
  --   | mk : String → Expression → Field

inductive RawExpression where
  | EList : List RawExpression -> RawExpression
  | StrLit : String -> RawExpression
  | NatLit : Nat -> RawExpression
  | BoolLit : Bool -> RawExpression
  | Id : String -> RawExpression
  | Constructor : String -> List (Field RawExpression) → RawExpression
  | Let : String → RawExpression → RawExpression
deriving Repr  
  
inductive Expression where
  | EList : List Expression -> Expression
  | StrLit : String -> Expression
  | NatLit : Nat -> Expression
  | BoolLit : Bool -> Expression
  | Id : String -> Expression
  | Constructor : String -> List (Field Expression) → Expression
deriving Repr

--------------------------------------------------------------------------------

def Field.name : Field E → String
| .mk name _ => name

--------------------------------------------------------------------------------

abbrev Environment := List (String × Expression)

def lookupInEnvironment (id : String) (env :Environment) : Except String Expression := 
  match List.lookup id env with
  | .some expr => .ok expr
  | .none => .error s!"Identifier {id} not found"
  
--------------------------------------------------------------------------------

mutual
  def Field.size : Field Expression → Nat
    | .mk _ expr => expr.size + 1
  def Expression.size : Expression → Nat
    | .EList xs => expressionListSize xs + 1
    | .Constructor _ fields => fieldListSize fields + 1
    | _ => 1
  private def expressionListSize : List Expression → Nat
    | [] => 0
    | x :: xs => x.size + expressionListSize xs
  private def fieldListSize : List (Field Expression) → Nat
    | [] => 0
    | x :: xs => x.size + fieldListSize xs
end

theorem Expression.size_lt_list (a : Expression) (xs : List Expression) (h : a ∈ xs) :
    a.size < (Expression.EList xs).size := by 
  induction xs with
  | nil => exact absurd h (by simp)
  | cons hd tl ih => 
    simp [List.mem_cons] at h
    simp [Expression.size]
    cases h with
    | inl h => subst h; simp [expressionListSize]; omega
    | inr h => 
      have := ih h 
      simp [expressionListSize, Expression.size] at *
      omega 

theorem Expression.size_lt_constructor (a : Field Expression) (id : String) (fs : List (Field Expression)) (h : a ∈ fs) :
    a.size < (Expression.Constructor id fs).size := by 
  induction fs with
  | nil => exact absurd h (by simp)
  | cons hd tl ih => 
    simp [List.mem_cons] at h
    simp [Expression.size]
    cases h with
    | inl h => subst h; simp [fieldListSize]; omega
    | inr h => 
      have := ih h
      simp [fieldListSize, Expression.size] at *
      omega

mutual 
  def Field.render (n : Nat) : Field Expression -> String := fun field =>
    let indent := String.ofList (List.replicate (2 * n) ' ')
    match field with
    | .mk id val => indent ++ id ++ " = " ++ Expression.render n val
  termination_by f => f.size
  decreasing_by
    simp [Field.size]

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
    | .Id id => id
    | .Constructor id lst =>
        let fields := lst.attach.map (fun ⟨a, _⟩ => Field.render (n + 1) a)
        id ++ " {\n" ++ String.intercalate "\n" fields ++ "\n" ++ indent ++ "}"
  termination_by e => e.size              
  decreasing_by
    · rename_i h
      apply Expression.size_lt_list _ _ h
    · rename_i h
      apply Expression.size_lt_constructor _ _ _ h
end



instance : ToString Expression where
  toString := Expression.render 0

instance : ToString (Field Expression) where
  toString := Field.render 0


def lookupField (name : String) (fields : List (Field Expression)) : Except String Expression :=
  match fields.find? (fun f => f.name == name) with
  | some (.mk _ expr) => .ok expr
  | none => .error s!"missing field: {name}"


