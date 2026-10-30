# IMO 2026 Problem 2: guided Deep input

- The mathematical problem is cross-checked against [the official IMO 2026 problem sheet](../../official-problems.pdf).
- [problem.lean](problem.lean) is the byte-identical published [AxiomMath Q2 statement](https://github.com/AxiomMath/IMO2026/blob/c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2/IMO2026/Q2/problem.lean), SHA256 `daeca5eca3b46b5a1e9768042925b37ea56e6f8899e055a6bf90064c4ef5c6f2`. This is not an IMO-organizing-committee-endorsed Lean formalization; the MIT license is copied in [LICENSE.AxiomMath](LICENSE.AxiomMath).
- [input.lean](input.lean), SHA256 `be278269774e3ad384662166fb2999bdbc1ec408afc4d003b9b4f6f5c8e09147`, differs only by removing the unsupported `backward.isDefEq.respectTransparency` option for the local Lean 4.28 toolchain. Definitions, hypotheses, theorem statement, and its sole `sorry` are unchanged. Compile from the Statlib root with `lake env lean /home/ai4stat/prover_long_test/docs/imo/2026/problem2/input.lean`; the expected `sorry` warning is not a proof result.
- [proof.md](proof.md) is a newly prepared mathematical guide, and [math-route.json](../actual-run-input/math-route.json) seeds only the mathematical route. No published Lean solution is passed to the prover.

The guide calls out angle-orientation and tangent cases as genuine proof obligations. A completed run must still pass the normal Lean, axiom, statement-integrity, and finalization gates.
