--
-- Time-stamp: <2026-04-21 Tue 17:13 EDT - george@valhalla>
--


--------------------------------------------------------------------------------
mutual
  inductive Field where 
    | mk : String → Expression → Field
  
  inductive Expression where
    | EList : List Expression -> Expression
    | StrLit : String -> Expression
    | NatLit : Nat -> Expression
    | BoolLit : Bool -> Expression
    | Id : String -> Expression
    | Constructor : String -> List Field → Expression
  deriving Repr

end
--------------------------------------------------------------------------------

def Field.name : Field → String
| .mk name _ => name

--------------------------------------------------------------------------------

mutual
  def Field.size : Field → Nat
    | .mk _ expr => expr.size + 1
  def Expression.size : Expression → Nat
    | .EList xs => expressionListSize xs + 1
    | .Constructor _ fields => fieldListSize fields + 1
    | _ => 1
  private def expressionListSize : List Expression → Nat
    | [] => 0
    | x :: xs => x.size + expressionListSize xs
  private def fieldListSize : List Field → Nat
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

theorem Expression.size_lt_constructor (a : Field) (id : String) (fs : List Field) (h : a ∈ fs) :
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
  def Field.render (n : Nat) : Field -> String := fun field =>
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

instance : ToString Field where
  toString := Field.render 0


def lookupField (name : String) (fields : List Field) : Except String Expression :=
  match fields.find? (fun f => f.name == name) with
  | some (.mk _ expr) => .ok expr
  | none => .error s!"missing field: {name}"


