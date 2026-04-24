# Changelog

## 0.4.1 - 2026-04-24

`0.4.1` is closer to a feature release than a pure patch release: it adds meaningful API surface and also contains a few source-breaking renames.

### Breaking Changes

- `Expression.name` was renamed to `Expression.symbol` across the expression hierarchy. Code that reads or overrides `name` must be updated.
- `Char` was renamed to `CharLiteral`.
- `BitVecLiteral.bits` was renamed to `BitVecLiteral.numBits`.
- `Model.definitions` changed from `List<FunctionDef<*>>` to `Map<Symbol, FunctionDef<*>>`. A list-based constructor still exists, but code relying on list semantics must adapt.
- `FloatingPointLiteral` now rejects non-constant bitvector components at construction time.

### Added

- New visitor APIs: `VisitByType<T>`, `VisitByStructure<T>`, `RecursionPolicy`, and `FreeVariables` for traversal and free-variable collection.
- Rich model accessors: lookup by `Symbol`, `String`, or `SMTFunction`, plus typed `getDefinition*`, `getTerm*`, and `getConstantValue(...)` helpers.
- New bitvector DSL helpers: `expr.extract(i, j)`, `(() -> expr).extract(i, j)`, and `.bitvec()` extensions for `Byte`, `Short`, `Int`, `Long`, and `BigInteger`.
- `FloatingPointLiteral` now supports conversion back to Kotlin values via `asBitString()`, `asFloat()`, and `asDouble()`.

### Changed

- `Equals<T>` now preserves the operand sort parameter, improving type safety and inference.
- Model handling is now centered around keyed lookups instead of manual list inspection.

### Fixed

- Z3 model extraction now resolves constants consistently via `symbol`.
- Floating-point conversion from Z3 was corrected, including exponent extraction and 64-bit double handling.
- Model-related integration coverage now checks that solver models expose all free variables used in assertions.

### Build And Tooling

- Updated Kotlin to `2.3.21`.
- Updated Gradle to `9.4.1`.
- Updated Spotless to `8.4.0`.
- Updated Develocity to `4.4.0`.
- Updated GitHub Gradle Actions to `v6`.
- Updated `CITATION.cff` with an additional author entry.
