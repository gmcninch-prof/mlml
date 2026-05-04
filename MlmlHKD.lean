-- MlmlHKD.lean
-- Demonstrates the Higher-Kinded Data (barbies) pattern applied to mlml decoding.
--
-- The core idea: instead of writing a monolithic Decode instance that does
-- field-lookup and binding all at once, we separate concerns:
--   1. `decodeFields`  -- just maps field names to decoded (possibly-failed) values
--   2. `collect`       -- collapses R (Except String) → Except String (R id)
--
-- `collect` is exactly `btraverse` from the barbies literature.

-- ============================================================
-- § 1.  mlml Expression types (minimal stand-in)
-- ============================================================

inductive Expression where
  | StrLit    : String → Expression
  | NatLit    : Nat    → Expression
  | BoolLit   : Bool   → Expression
  | EList     : List Expression → Expression
  | Constructor : String → List (String × Expression) → Expression
  deriving Repr

-- Look up a named field in a constructor's field list.
def lookupField (e : Expression) (field : String) : Except String Expression :=
  match e with
  | .Constructor _ fields =>
      match fields.find? (fun p => p.1 == field) with
      | some (_, v) => .ok v
      | none        => .error s!"missing field '{field}'"
  | _ => .error s!"expected a constructor, got {repr e}"

-- ============================================================
-- § 2.  Decode typeclass (your existing one, essentially)
-- ============================================================

class Decode (α : Type) where
  decode : Expression → Except String α

instance : Decode String where
  decode
    | .StrLit s => .ok s
    | e         => .error s!"expected string, got {repr e}"

instance : Decode Nat where
  decode
    | .NatLit n => .ok n
    | e         => .error s!"expected nat, got {repr e}"

instance : Decode Bool where
  decode
    | .BoolLit b => .ok b
    | e          => .error s!"expected bool, got {repr e}"

instance [Decode α] : Decode (Option α) where
  decode
    | .Constructor "None" [] => .ok none
    | e => (Decode.decode e : Except String α) >>= (pure ∘ some)

-- Convenience: look up a field then decode it.
def decodeField [Decode α] (e : Expression) (field : String) : Except String α :=
  lookupField e field >>= Decode.decode

-- ============================================================
-- § 3.  The HKD / barbies machinery
-- ============================================================

-- A "barbie" record is parameterised by a functor f : Type → Type.
-- We use a typeclass to package the two operations we need:
--
--   decodeFields : Expression → R (Except String)
--     Produce a record whose every field is a (possibly-failed) decode attempt.
--
--   collect : R (Except String) → Except String (R id)
--     This is btraverse: sequence all the Except values, short-circuiting on
--     the first error.  One instance per record type; essentially just `do`-notation.

class DecodeRecord (R : (Type → Type) → Type) where
  decodeFields : Expression → R (Except String)
  collect      : R (Except String) → Except String (R id)

-- The uniform driver: decodeFields then collect.
def decodeRecord [DecodeRecord R] (e : Expression) : Except String (R id) :=
  DecodeRecord.collect (DecodeRecord.decodeFields e)

-- ============================================================
-- § 4.  Concrete record types in HKD style
-- ============================================================

-- A "Person" record in HKD form.
-- f = Except String  →  PersonF (Except String)  : every field may have failed
-- f = id             →  PersonF id               : all fields successfully decoded
structure PersonF (f : Type → Type) where
  name  : f String
  age   : f Nat
  email : f String

instance : DecodeRecord PersonF where
  decodeFields e := {
    name  := decodeField e "name",
    age   := decodeField e "age",
    email := decodeField e "email"
  }
  collect p := do
    return { name := ← p.name, age := ← p.age, email := ← p.email }

-- Convenience alias: a fully-decoded Person is PersonF id.
abbrev Person := PersonF id

-- Wire it into the Decode typeclass so it composes with decodeField.
instance : Decode Person where
  decode := decodeRecord

-- ─────────────────────────────────────────────────────────────
-- A second record: CourseEntry, closer to a real mlml use case.
-- Imagine decoding a gradekeeper-style assignment entry.
structure CourseEntryF (f : Type → Type) where
  title   : f String
  points  : f Nat
  weight  : f Nat      -- integer percentage weight
  counted : f Bool     -- whether it counts toward the grade

instance : DecodeRecord CourseEntryF where
  decodeFields e := {
    title   := decodeField e "title",
    points  := decodeField e "points",
    weight  := decodeField e "weight",
    counted := decodeField e "counted"
  }
  collect p := do
    return {
      title   := ← p.title,
      points  := ← p.points,
      weight  := ← p.weight,
      counted := ← p.counted
    }

abbrev CourseEntry := CourseEntryF id

instance : Decode CourseEntry where
  decode := decodeRecord

-- ============================================================
-- § 5.  The bonus: inspecting errors field-by-field
-- ============================================================

-- Because `decodeFields` gives us an `R (Except String)` *before* we collect,
-- we can inspect which fields failed without short-circuiting.
-- This is the "validation" mode — analogous to using Validated rather than Either
-- in Haskell, but we get it for free just by not calling `collect` yet.

def personFieldErrors (e : Expression) : List String :=
  let p := (DecodeRecord.decodeFields e : PersonF (Except String))
  [ match p.name  with | .error msg => some s!"name: {msg}"  | .ok _ => none,
    match p.age   with | .error msg => some s!"age: {msg}"   | .ok _ => none,
    match p.email with | .error msg => some s!"email: {msg}" | .ok _ => none
  ].filterMap id

-- ============================================================
-- § 6.  Test cases
-- ============================================================

def runTests : IO Unit := do
  IO.println "=== HKD / barbies pattern for mlml ==="
  IO.println ""

  -- ── Test 1: well-formed Person ──────────────────────────────
  let goodPerson : Expression :=
    .Constructor "Person" [
      ("name",  .StrLit "Alice"),
      ("age",   .NatLit 30),
      ("email", .StrLit "alice@example.com")
    ]
  IO.println "Test 1 — well-formed Person:"
  match decodeRecord goodPerson (R := PersonF) with
  | .ok p  => IO.println s!"  ✓ name={p.name} age={p.age} email={p.email}"
  | .error e => IO.println s!"  ✗ {e}"

  IO.println ""

  -- ── Test 2: missing field short-circuits on first error ─────
  let missingAge : Expression :=
    .Constructor "Person" [
      ("name",  .StrLit "Bob"),
      ("email", .StrLit "bob@example.com")
      -- "age" absent
    ]
  IO.println "Test 2 — missing 'age' field (collect short-circuits):"
  match decodeRecord missingAge (R := PersonF) with
  | .ok _  => IO.println "  ✗ should have failed"
  | .error e => IO.println s!"  ✓ got error: {e}"

  IO.println ""

  -- ── Test 3: same expression, but field-by-field error report ─
  -- Uses decodeFields *without* collect, so we see ALL missing fields.
  let missingMuch : Expression :=
    .Constructor "Person" [
      ("name", .StrLit "Charlie")
      -- age and email both absent
    ]
  IO.println "Test 3 — multiple missing fields (validation mode, no short-circuit):"
  let errs := personFieldErrors missingMuch
  if errs.isEmpty
  then IO.println "  ✗ expected errors"
  else errs.forM (fun e => IO.println s!"  ✓ {e}")

  IO.println ""

  -- ── Test 4: wrong type for a field ──────────────────────────
  let wrongType : Expression :=
    .Constructor "Person" [
      ("name",  .NatLit 42),   -- should be StrLit
      ("age",   .NatLit 25),
      ("email", .StrLit "d@example.com")
    ]
  IO.println "Test 4 — wrong type for 'name' field:"
  match decodeRecord wrongType (R := PersonF) with
  | .ok _  => IO.println "  ✗ should have failed"
  | .error e => IO.println s!"  ✓ got error: {e}"

  IO.println ""

  -- ── Test 5: nested decode — Person inside a CourseEntry ─────
  -- Shows that Decode instances compose: once Person has a Decode instance,
  -- it can be a field inside another HKD record.
  let goodEntry : Expression :=
    .Constructor "CourseEntry" [
      ("title",   .StrLit "Homework 3"),
      ("points",  .NatLit 50),
      ("weight",  .NatLit 10),
      ("counted", .BoolLit true)
    ]
  IO.println "Test 5 — well-formed CourseEntry:"
  match decodeRecord goodEntry (R := CourseEntryF) with
  | .ok e  =>
    IO.println s!"  ✓ title={e.title} points={e.points} weight={e.weight} counted={e.counted}"
  | .error e => IO.println s!"  ✗ {e}"

  IO.println ""
  IO.println "Done."

#eval runTests
