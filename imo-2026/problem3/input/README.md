# IMO 2026 P3 guided attack input

Published Lean statement:
https://github.com/AxiomMath/IMO2026/blob/c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2/IMO2026/Q3/problem.lean

The publisher is AxiomMath, not the contest organizing committee. The
problem was cross-checked with ../official-problems.pdf. problem.lean
preserves the downloaded bytes, SHA256
e3526163de827c63b91eb7279b3625528075d2aae64ccf9597aa6fda4a99e255.
input.lean removes the previously approved incompatible compiler option
backward.isDefEq.respectTransparency and, after the user requested one
problem decomposed into proof nodes, the five unfinished auxiliary theorem
declarations. All six original definitions and the exact V_eq declaration
remain unchanged. Input SHA256:
380b5532daf0af9586c393a322b7686d11320389046c7fefe5ca40a1620a98b7.
The fully qualified target is LiuBangXiangYu.V_eq; the CLI takes its lexical
name V_eq. Removed auxiliaries are obligations, NOT imported certificates.

proof.md is a detailed mathematical guide prepared for this attack, with
a dyadic multigraph lower bound and a subset-sum matching upper bound.
Public mathematical discussions were consulted (not an unguided attack):
https://github.com/RuoranXu/IMO2026/blob/main/problem3/problem3_solution_en.md
and the search result for
https://github.com/imathwy/IMO_test/blob/master/IMO/solution/P3.md .
No published Lean solution was read or supplied. The matching construction,
edge-count argument and real supremum/infimum obligations are explicitly
expanded in the supplied guide and independently reviewed before launch.

math-route.json is a supplied mathematical route, not a DAG checkpoint.
The experiment must still plan, formalize, prove and verify all dependencies.

Started2026-09-26T11:49:10.804Z on5989e2ad, job real_V_eq_33dfc46dd2d4.
The metadata records10522 bytes of supplied mathematical proof, five keys,
three build workers and three LSP services. See
joint monitor (historical path: `../../../mode_compare/deep_shadow_retirement_20260926T114000Z/status.md`).
