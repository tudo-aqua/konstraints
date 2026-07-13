<!--
   SPDX-License-Identifier: CC-BY-4.0

   Copyright 2023-2026 The Konstraints Authors

   This work is licensed under the Creative Commons Attribution 4.0
   International License.

   You should have received a copy of the license along with this
   work. If not, see <https://creativecommons.org/licenses/by/4.0/>.
-->

# Changelog

## 0.4.3 - 2026-07-10

This release expands expression traversal and program validation, adds convenient default-solver
support, and extends the integer theory with exponentiation.

### Breaking Changes

- `MutableSMTProgram` now validates assertions against the selected logic as they are added and
  rejects quantifiers, arithmetic outside the selected numerical fragment, and free function symbols
  where the logic does not permit them.
- `Equals` now requires at least two operands.
- `AssertionOutOfLogicBounds` was replaced by the `InvalidSMTProgramException` hierarchy, including
  dedicated exceptions for invalid quantifier, function, datatype, and arithmetic usage.

### Added

- Default solver discovery through `Solver.getDefaultSolver()`, with interactive Z3 and CVC5 support
  and `NoDefaultSolverAvailableException` when neither solver is installed.
- `SMTProgram.solve(...)` and a default-solver overload of `MutableSMTProgram.push(...)` for solving
  without explicitly constructing a solver.
- Expression-tree traversal APIs for preorder and postorder traversal: `any`, `all`, `asSequence`,
  `forEach`, and `onEach`, with recursive and iterative variants.
- A deep-program mode through `SMTScriptParser(..., parseDeepProgram = true)` and the `isDeep`
  program property, allowing iterative validation traversal for deeply nested expressions.
- Integer exponentiation through `IntExp` and parser support for the SMT-LIB `**` operator.
- Validation exceptions rooted at `InvalidSMTProgramException` for reporting logic violations.

### Fixed

- Linear and difference-logic validation now handles `let` expressions, `ite` expressions, and free
  function symbols correctly.
- Difference-logic validation now restricts negation to numeric literals.
- Equality expressions with fewer than two operands are rejected.

### Build And Tooling

- Updated Kotlin to `2.4.0`.
- Updated Gradle to `9.5.1`.
- Updated Spotless to `8.6.0`.
- Updated Develocity to `4.4.2`.
- Updated GitHub Checkout Action to `v7`.

## 0.4.2 - 2026-06-02

`0.4.2` focuses on solver and program integration improvements for GDart. It changes how solver
results and models are requested, adds scoped push/pop solving support, and tightens interactive
solver response parsing.

### Breaking Changes

- `Solver.solve(...)` now takes `produceModel` and `timeout` parameters and returns
  `Pair<SatStatus, Model?>`. Code that previously called `solve(program): SatStatus` and then
  `getModel()` must now request model production in the solve call and use the returned model.
- `Solver.getModel()` was removed.
- `SMTProgramBuilder.checkSat(...)`, `SMTProgramBuilder.getModel(...)`,
  `MutableSMTProgram.checkSat(...)`, and `MutableSMTProgram.getModel(...)` were removed in favor of
  solver-driven `solve(...)` calls.
- `MutableSMTProgram.add(...)` is now internal. Use typed program APIs such as `assert`,
  `declareConst`, `declareFun`, `defineConst`, `defineFun`, `push`, and `pop`.
- `CommandVisitor` no longer exposes separate visits for `CheckSat`, `Exit`, and `GetModel`.
  Visitors that care about these commands should handle them through `NullOp`.
- `Model.getConstantValue(...)` now returns the underlying value instead of a literal wrapper. Use
  `getConstant(...)` to retrieve a literal, or `getConstantFloatValue(...)` /
  `getConstantDoubleValue(...)` for floating-point values.

### Added

- `PushContext` and scoped `MutableSMTProgram.push(solver, produceModel, timeout) { ... }` support
  for temporary assertion-stack changes that are solved and then popped.
- `Model.constants` and `Model.functions` views for separating constant and non-constant
  definitions.
- `Model.getConstant(...)` helpers for retrieving constant literals by symbol, string, function, or
  term.
- `SatStatus.ERROR` and `EchoResponse`.
- Specialized solver response parser entry points for general responses, `check-sat`, `get-model`,
  and `echo` responses.
- `Declaration<T>` and `NullOp` command categories, plus generic `DefineConst<T>` and `DefineFun<T>`
  command types.

### Changed

- `InteractiveCLISolver` now writes commands through `CommandVisitor`, enables `:produce-models`
  based on the solve request, parses command responses according to command type, and returns a
  model together with the satisfiability status when requested.
- `Z3Solver.solve(program, produceModel, timeout)` now performs the satisfiability check as part of
  `solve` and constructs a Konstraints model only when requested and available.
- Program finalization no longer appends `Exit`; `CheckSat`, `GetModel`, and `Exit` are treated as
  null operations by solver visitors.
- `SetOption` now accepts option names with or without the leading `:`.
- Function and constant definitions preserve their sort type more consistently through
  `DefineFun<T>`, `DefineConst<T>`, and `FunctionDef<T>`.

### Fixed

- Interactive solver response parsing now handles `success`, `unsupported`, errors, check-sat
  statuses, model responses, and echo responses through dedicated parser paths.
- General response parsing no longer consumes tokens when a general response is not present,
  improving follow-on parsing of `check-sat` and `get-model` responses.
- Z3 model availability detection no longer relies on nullable behavior from the underlying Z3 API.

### Build And Tooling

- Updated `kotlinx-serialization-json` to `1.11.0`.
- Updated Dokka Gradle plugin to `2.2.0`.
- Updated Develocity to `4.4.1`.
- Updated `commons-io` to `2.22.0`.
- Added integration coverage for interactive solving and scoped push/pop solving.

## 0.4.1 - 2026-04-24

`0.4.1` is closer to a feature release than a pure patch release: it adds meaningful API surface and
also contains a few source-breaking renames.

### Breaking Changes

- `Expression.name` was renamed to `Expression.symbol` across the expression hierarchy. Code that
  reads or overrides `name` must be updated.
- `Char` was renamed to `CharLiteral`.
- `BitVecLiteral.bits` was renamed to `BitVecLiteral.numBits`.
- `Model.definitions` changed from `List<FunctionDef<*>>` to `Map<Symbol, FunctionDef<*>>`. A
  list-based constructor still exists, but code relying on list semantics must adapt.
- `FloatingPointLiteral` now rejects non-constant bitvector components at construction time.

### Added

- New visitor APIs: `VisitByType<T>`, `VisitByStructure<T>`, `RecursionPolicy`, and `FreeVariables`
  for traversal and free-variable collection.
- Rich model accessors: lookup by `Symbol`, `String`, or `SMTFunction`, plus typed `getDefinition*`,
  `getTerm*`, and `getConstantValue(...)` helpers.
- New bitvector DSL helpers: `expr.extract(i, j)`, `(() -> expr).extract(i, j)`, and `.bitvec()`
  extensions for `Byte`, `Short`, `Int`, `Long`, and `BigInteger`.
- `FloatingPointLiteral` now supports conversion back to Kotlin values via `asBitString()`,
  `asFloat()`, and `asDouble()`.

### Changed

- `Equals<T>` now preserves the operand sort parameter, improving type safety and inference.
- Model handling is now centered around keyed lookups instead of manual list inspection.

### Fixed

- Z3 model extraction now resolves constants consistently via `symbol`.
- Floating-point conversion from Z3 was corrected, including exponent extraction and 64-bit double
  handling.
- Model-related integration coverage now checks that solver models expose all free variables used in
  assertions.

### Build And Tooling

- Updated Kotlin to `2.3.21`.
- Updated Gradle to `9.4.1`.
- Updated Spotless to `8.4.0`.
- Updated Develocity to `4.4.0`.
- Updated GitHub Gradle Actions to `v6`.
- Updated `CITATION.cff` with an additional author entry.
