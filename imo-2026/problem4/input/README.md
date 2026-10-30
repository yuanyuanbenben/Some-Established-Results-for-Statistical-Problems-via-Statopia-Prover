# IMO2026 P4 guided attack input

Published statement: https://github.com/AxiomMath/IMO2026/blob/c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2/IMO2026/Q4/problem.lean

`problem.lean` preserves the published bytes (git blob
346dc9e195731925ec3509f7269052fb5d4b687f; SHA256
fdcb9357fa1d806ba0032fad20a08b22e827eb9f1797e1a4800dfdeb67ccf52f).
The publisher is AxiomMath, not the IMO organizing committee. The game text
was cross-checked against `../official-problems.pdf`, Problem 4.

`input.lean` removes only the unsupported compiler option
`set_option backward.isDefEq.respectTransparency false`, following the
previously approved P5 compatibility treatment. Definitions, inductive game
rules, theorem statement, hypotheses and placeholder are unchanged. Input
SHA256: d98b6c0d798282acbb9b1dd3419b918e615face62f4673ce5bc785ff73664735.

`proof.md` is newly prepared detailed mathematical guidance: integral-angle
winning strategies and an integer-multiple avoidance invariant. It includes
both directions and finite-tree justification. No published Lean solution
was read or supplied. `math-route.json` selects this supplied route; it does
not contain a DAG or proof checkpoint. Compilation of the input skeleton
is not a completed proof; final status belongs to the live experiment.

Fresh attack started at 2026-09-26T10:20:03.193Z with job
real_main_theorem_3393c3b8aa74. See the
joint monitor (historical path: `../../../mode_compare/deep_p4_guided_20260926T102000Z/status.md`).
