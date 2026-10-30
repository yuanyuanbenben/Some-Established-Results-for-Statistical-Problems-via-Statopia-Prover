# Neural-network approximation: curated Statlib contribution

Original public endpoint: `Statlib.Nonparametric.Approximation.holder_smooth_shallow_relu_neural_network_approximation`. Its full statement is in [compiled-interface-check.txt](compiled-interface-check.txt). That statement omits the relationship between its resolution parameter and network depth. Use [AtResolution.lean](AtResolution.lean) and [the interface audit](SUMMARY.md) for the explicit depth and error bounds at every sufficiently large resolution, derived from the existing compiled construction. Neither interface is the entire regression-risk theorem of a paper.

| Source module | Physical lines |
| --- | ---: |
| [Vocabulary/NeuralNetwork.lean](Statlib/Nonparametric/Vocabulary/NeuralNetwork.lean) | 447 |
| [Approximation/NeuralNetworkAlgebra.lean](Statlib/Nonparametric/Approximation/NeuralNetworkAlgebra.lean) | 35,028 |
| [Approximation/ReLUNetworkConstruction.lean](Statlib/Nonparametric/Approximation/ReLUNetworkConstruction.lean) | 7,713 |
| [Approximation/ReLUStateMachine.lean](Statlib/Nonparametric/Approximation/ReLUStateMachine.lean) | 8,466 |
| [Approximation/ShallowReLUApproximationGeometry.lean](Statlib/Nonparametric/Approximation/ShallowReLUApproximationGeometry.lean) | 3,781 |
| [Approximation/ShallowReLUApproximation.lean](Statlib/Nonparametric/Approximation/ShallowReLUApproximation.lean) | 380 |
| [Approximation/NeuralNetwork.lean](Statlib/Nonparametric/Approximation/NeuralNetwork.lean) | 107 |

Total: 55,922 lines in these seven named modules. These seven source files are included in this repository. This is a curated library snapshot, not one timed generation run; no historical total cost or time is assigned.

`verify-public-theorem.lean` was checked against the current compiled library with `lake env lean`. Its axiom report contains only `propext`, `Classical.choice`, `Quot.sound`. This does not constitute a rebuild of all seven sources. Separate source scans found no active `sorry`, `admit` or user-axiom declarations.

`metrics.json` records module hashes and the current Statlib HEAD. HEAD alone does not describe uncommitted working-tree content; the recorded source hashes are the exact snapshot authority. External imports remain dependencies of the surrounding Statlib/Mathlib project.

The seven linked neural-network Lean modules are published under [Statlib/](Statlib/) with their original paths and byte-identical snapshot hashes. Other Statlib dependencies remain supplied as compiled modules through `verification/statlib-cache/`; the broader library source is not included. The old umbrella `public-import-surface.lean` remains outside the project. See [the contribution summary](SUMMARY.md) and [publication/relocation records](../../verification/directory-layout.json).

The recorded `make verify` procedure still compiles the explicit neural wrapper against the pinned binary dependencies; it does not rebuild all seven library source modules. Publishing these sources does not add a new source-rebuild claim.
