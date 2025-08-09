# PLC Interpreter Project

An interpreter for a small, object-oriented language, built as a course project for CIn/UFPE’s PLC (Paradigmas de Linguagens Computacionais, Programming Language Paradigms) course.

## Table of Contents

- [PLC Interpreter Project](#plc-interpreter-project)
  - [Table of Contents](#table-of-contents)
  - [Overview](#overview)
    - [Quick AST reference](#quick-ast-reference)
  - [Getting started](#getting-started)
  - [Tips](#tips)
  - [License](#license)

## Overview

- AST includes: variables, numeric literals, sum/mult, lambda/apply, assignment,
  sequencing, if, while, field access/assign, new, instanceof.
- Runtime model: immutable Environment, mutable State, and Heap of objects
  (Ref -> (ClassName, Fields)).
- Closures capture the Environment and run over (Value, State, Heap).
- Truthiness: Num n with n ≠ 0 is true; Num 0 is false.

See `main.hs` top block comments for details and design notes.

### Quick AST reference

- Variables and literals: `Var id`, `Lit n`
- Arithmetic: `Sum t1 t2`, `Mult t1 t2`
- Functions: `Lam x body`, `Apl f arg` (closures capture the environment)
- Assignment and sequencing: `Atr lhs rhs`, `Seq t1 t2`
- Control flow: `If cond then else`, `While cond body`
- Objects: `AField obj field`, `New classId`, `InstanceOf obj classId`

Runtime values: `Num Double | Ref Int | Fun (Value -> State -> Heap -> (Value, State, Heap)) | Error`.

## Getting started

- Requirements: GHC/GHCi 9.x
- Open GHCi and load the program:

```bash
# from repository root
ghci
:load main.hs
```

Run all built-in tests (simple smoke tests):

```haskell
main
```

You can also call individual tests, e.g. `testWhile`, `testIf`, `testApl`.

Note: requires GHC/GHCi 9.x. All tests are simple prints acting as smoke checks.

## Tips

- State holds `(Id, Value)` where `Value = Num | Ref | Fun | Error`. Do not put AST
  constructors (e.g., `Lit`, `Var`) inside State/Heap.
- Heap entries are `(Ref n, (ClassName, FieldsState))`, e.g. `(Ref 1, ("A", [("x", Num 10)]))`.
- For multi-statement bodies, compose with `Seq`.

## License

This project is licensed under the MIT License. See the LICENSE file for details.
