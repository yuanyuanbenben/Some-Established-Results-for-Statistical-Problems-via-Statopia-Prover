# Some Established Results for Statistical Problems via Statopia Prover

Some selected Lean 4 formalization results verified using [Statopia Prover](https://prover.statopia.ai/).

- [Statopia Prover](https://prover.statopia.ai/)
- [Statlib](https://statlib.statopia.ai/)
- [Statopia Prover source code](https://github.com/statopia/prover)

The collection contains 83 statistics problems, six guided IMO results, ten papers (11 main developments and 40 supporting tasks), and a neural-network approximation component.

- [Paper results](papers/README.md)
- [Statistics benchmark](statistics-benchmark/README.md)
- [IMO results](imo-2026/README.md)
- [Neural-network approximation](statlib-contributions/neural-network-approximation/SUMMARY.md)

Every paper, benchmark task and IMO task has `input/`, `proof/` and a result summary. `proof/` contains Lean sources, the required Statlib cache, exact targets and pinned build configuration. Source line counts include supporting modules. Results are checked under their stated hypotheses and retained external references.

| Paper | Lean files | Lean lines | Cached modules | External references | Passed / tasks (main + supporting) |
| --- | ---: | ---: | ---: | ---: | ---: |
| [CCK — Theorem 2 (covariance-only bound)](papers/cck/README.md) | 78 | 12,223 | 122 | 4 | 6/6 (1+5) |
| [Gaussian approximation — Theorem 3.1](papers/gaussian/README.md) | 88 | 15,047 | 90 | 3 | 6/6 (1+5) |
| [DP clustering — Theorem 1](papers/dp-clustering/README.md) | 226 | 50,508 | 4 | 1 | 17/17 (1+16) |
| [HulC — Theorem 1](papers/hulc/README.md) | 15 | 1,397 | 1 | 0 | 2/2 (1+1) |
| [HMC — Theorems 2.2 (i–ii) and 5.14](papers/hmc/README.md) | 73 | 7,214 | 2 | 1 | 8/8 (2+6) |
| [Data thinning — Theorem 1](papers/data-thinning/README.md) | 5 | 125 | 0 | 0 | 1/1 (1+0) |
| [EILLS — Theorem 4.2](papers/eills/README.md) | 11 | 2,079 | 0 | 1 | 1/1 (1+0) |
| [CQR — Theorem 1 (lower-coverage core)](papers/cqr/README.md) | 6 | 394 | 5 | 0 | 6/6 (1+5) |
| [Dobriban — Theorem 1 (certificate)](papers/dobriban/README.md) | 6 | 1,789 | 1 | 0 | 1/1 (1+0) |
| [Lei — Theorem 3.1 (interfaces)](papers/lei/README.md) | 17 | 2,786 | 1 | 0 | 3/3 (1+2) |

External references count distinct citation axioms in the complete retained source package. Passed/tasks gives the total with its main/supporting split.

To build a single task, enter its `proof/` directory:

```sh
lake update
lake exe cache get
python3 verify.py
```

At the collection root, `make setup` installs public dependencies, `make check` checks file/cache hashes, and `make verify` compiles every configured result and checks target axioms. Lean and Mathlib versions are pinned. The neural wrapper uses the root build entry and cache under `verification/`; its implementation sources and scope are described in its summary.
