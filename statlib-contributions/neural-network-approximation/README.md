# Neural-network approximation: curated Statlib contribution

Original public endpoint: `Statlib.Nonparametric.Approximation.holder_smooth_shallow_relu_neural_network_approximation`. Its full statement is in [compiled-interface-check.txt](compiled-interface-check.txt). That statement omits the relationship between its resolution parameter and network depth. Use [AtResolution.lean](AtResolution.lean) and [the interface audit](SUMMARY.md) for the explicit depth and error bounds at every sufficiently large resolution, derived from the existing compiled construction. Neither interface is the entire regression-risk theorem of a paper.

| Module | Physical lines |
| --- | ---: |
| `NeuralNetwork.lean` | 447 |
| `NeuralNetworkAlgebra.lean` | 35028 |
| `ReLUNetworkConstruction.lean` | 7713 |
| `ReLUStateMachine.lean` | 8466 |
| `ShallowReLUApproximationGeometry.lean` | 3781 |
| `ShallowReLUApproximation.lean` | 380 |
| `NeuralNetwork.lean` | 107 |

Total: 55,922 lines in these seven named modules. This is a current curated library snapshot, not one timed generation run; no historical total cost or time is assigned.

`verify-public-theorem.lean` was checked against the current compiled library with `lake env lean`. Its axiom report contains only `propext`, `Classical.choice`, `Quot.sound`. This does not constitute a rebuild of all seven sources. Separate source scans found no active `sorry`, `admit` or user-axiom declarations.

`metrics.json` records module hashes and the current Statlib HEAD. HEAD alone does not describe uncommitted working-tree content; the recorded source hashes are the exact snapshot authority. External imports remain dependencies of the surrounding Statlib/Mathlib project.

For this standalone project, use [the contribution summary and reference materials](SUMMARY.md). The private `Statlib/` source snapshots and `public-import-surface.lean` are preserved outside this project directory; [relocation records](../../verification/directory-layout.json) retain local provenance. Compiled dependencies are supplied as ordinary files through `verification/statlib-cache/`.
