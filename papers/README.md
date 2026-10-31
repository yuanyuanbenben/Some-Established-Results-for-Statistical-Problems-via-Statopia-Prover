# Paper results

One directory per paper. Each contains only input materials, Lean sources, required binary caches, build tools/configuration and a result README. HMC groups both selected theorems; Dobriban and Lei are separate papers.

| Paper | Lean files | Lean lines | Cached modules | External references | Passed / tasks (main + supporting) |
| --- | ---: | ---: | ---: | ---: | ---: |
| [CCK — Gaussian comparison and anti-concentration](cck/README.md) | 78 | 12,223 | 122 | 4 | 6/6 (1+5) |
| [Gaussian approximation — Theorem 3.1](gaussian/README.md) | 88 | 15,047 | 90 | 3 | 6/6 (1+5) |
| [HulC — Theorem 1](hulc/README.md) | 15 | 1,397 | 1 | 0 | 2/2 (1+1) |
| [Hamiltonian Monte Carlo](hmc/README.md) | 73 | 7,214 | 2 | 1 | 8/8 (2+6) |
| [Data thinning — Theorem 1](data-thinning/README.md) | 5 | 125 | 0 | 0 | 1/1 (1+0) |
| [EILLS — Theorem 4.2](eills/README.md) | 11 | 2,079 | 0 | 1 | 1/1 (1+0) |
| [Conformalized quantile regression](cqr/README.md) | 6 | 394 | 5 | 0 | 6/6 (1+5) |
| [Dobriban — BH/FDR counterexample](dobriban/README.md) | 6 | 1,789 | 1 | 0 | 1/1 (1+0) |
| [Lei — BH/FDR interfaces](lei/README.md) | 17 | 2,786 | 1 | 0 | 3/3 (1+2) |

Lines count the current Lean source files, including supporting modules. External references count distinct explicit citation axioms throughout the complete source package, including unused declarations; library imports and theorem hypotheses are excluded. Passed/tasks counts selected main and supporting tasks under their permitted external assumptions, excluding internal helper modules and fixed seed modules. Total: **34/34 tasks (10 main + 24 supporting), 9 external references**.
