# IMO2026 P5 input provenance

Published source: https://github.com/AxiomMath/IMO2026/blob/c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2/IMO2026/Q5/problem.lean

problem.lean is the byte-identical published statement, git blob
64f96ad2b038e7c321c7ebc6d8ea2eb7378f0d16, SHA256
7ee9e76cdd3bf1c3c10e2fe97624ffe3ff4706b756b59708c2581999a9a102b5.
LICENSE.AxiomMath retains its MIT license.

input.lean is the approved Lean 4.28 test copy. Its sole change is removal of
`set_option backward.isDefEq.respectTransparency false`, an unknown option
in the test toolchain (the published project uses 4.31). All definitions,
theorem signatures, hypotheses and conclusions are unchanged.

proof.md is a separately prepared detailed mathematical proof. Independent
mathematical review passed the orbit, squared comparison, subdivision and
Archimedean arguments, including both directions and source fidelity.
The guided run now passed: archived result (historical path: `run_20260926T072001Z/README.md`).
No published solution.lean was used as proving input. The supplied guide
replaced route generation only; the engine performed Lean search, DAG
planning and proof checking.
