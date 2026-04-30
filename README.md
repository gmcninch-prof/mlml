# mlml

A simple configuration language and Lean 4 codec library, designed for
structured data entry in academic and personal workflow tools.

## Overview

`mlml` provides a small expression language for writing structured
configuration files, together with a Lean 4 typeclass-based codec for
parsing those expressions into typed Lean values.

The language is intentionally minimal — it sits between plain text and
full-featured formats like Dhall or TOML, with just enough structure
for nested records, lists, and tagged variants.

## Language

An `mlml` file contains a single `Expression`, which can be:

- **String literals**: `"hello"`
- **Natural number literals**: `42`
- **Boolean literals**: `true`, `false`
- **Identifiers** (for let-bindings):  `classRoom`
- **Constructors** (named records): `Semester { ay = 2025 term = Fall }`
    (possibly with no arguments): `Mon`, `Fall`, `AllDay`
- **Lists**: `[ "item1" "item2" "item3" ]`

### Example

```
let classRoom = "JCC 140"
Course {
  title = "Math 136"
  semester = Semester { ay = 2025 term = Spring }
  components = [
    Lecture {
      description = "course lecture"
      sched = [
        DowTufts {
          dow = Mon
          time = TimeRange { start = "10:30" stop = "11:45" }
          location = classRoom
          }
      ]
      topics = [ "Introduction" "Limits" ]
    }
  ]
}
```

## Lean 4 Codec

The `Codec` library provides a `Decode` typeclass for parsing `Expression`
values into typed Lean values:

```lean
instance : Codec.Decode MyType where
  decode
    | .Constructor "MyType" fs => do
        let field1 ← Codec.decodeField "field1" fs
        let field2 ← Codec.decodeField "field2" fs
        pure { field1, field2 }
    | e => .error s!"Expected MyType; got {repr e}"
```

### Key functions

- `Codec.decodeField : String → List Field → Except String α` — decode a named field from a constructor's field list
- `parseAndDecode : String → Except String α` — parse an mlml string and decode it in one step
- `expressionFromString : String → Except String Expression` — parse only, without decoding

## Pipeline

String → tokenize → List Token → parseExpression → Expression → Codec.Decode → α


## Design notes

`mlml` was developed as a replacement for Dhall for personal academic
workflow tooling. Dhall's constructor syntax was expressive but verbose;
`mlml` retains tagged constructors and nested records while being simpler
to parse and extend. Unknown fields in constructors are silently ignored
by `decodeField`, making the format forward-compatible as types evolve.

## Dependencies

- Lean 4

