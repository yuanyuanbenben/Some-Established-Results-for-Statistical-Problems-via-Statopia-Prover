# IMO 2026 Problem 1: guided Deep input

- The mathematical question is checked against the
  [official IMO 2026 problem sheet](../../official-problems.pdf).
- [problem.lean](problem.lean) is the byte-identical published
  [AxiomMath Q1 statement](https://github.com/AxiomMath/IMO2026/blob/c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2/IMO2026/Q1/problem.lean),
  SHA256 `98695afb49630475105d6a6abdfff173b8ef4ac16f66d5800c3c928ea40febc7`.
  It is not an IMO-organizing-committee-endorsed Lean formalization; its
  MIT license is in [LICENSE.AxiomMath](LICENSE.AxiomMath).
- [input.lean](input.lean), SHA256
  `2cc9808f24de022b819c0daee2cde4494cf02ca1d0050f4183a0f45544a8a663`,
  keeps the published definitions unchanged. It removes the unsupported
  `backward.isDefEq.respectTransparency` option for local Lean 4.28 and
  replaces five separate `sorry` proofs with a single conjunction of their
  exact quantified statements. No published claim becomes an assumption.
  `lake env lean` accepts this input with only its expected target `sorry`
  warning; that is not a proof result.
- [proof.md](proof.md) supplies a mathematical guide; [math-route.json](../actual-run-input/math-route.json)
  seeds only the mathematical route. The published `solution.lean` is neither
  imported nor passed to the prover.

The target includes the published explicit terminal-value formula in
addition to the official termination and choice-independence questions.
Normal Lean, axiom, statement-integrity, and finalization gates remain
required for a PASS.

The guided run completed on 2026-09-28. Its proof artifacts, logs, independent
build, and axiom check are in run_20260928T125713Z (historical path: `run_20260928T125713Z/README.md`).
