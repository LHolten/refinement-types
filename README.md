This is where I experiment with SMT solver based type theory.

## Goals
- Allow defining dependent memory layouts like size prefixed arrays
- SMT powered Automatic reasoning about bitvectors
- Support for safe mutable aliasing borrows
- Low overhead in proof annotations (The language should not be much more difficult to use than rust)
- Compile to wasm

## Status
It is possible to parse and typecheck programs and run them in an interpreter.
However, I am not happy with the type system and am researching a new one.
