# Some Established Results for Statistical Problems via Statopia Prover

This repository showcases a selection of statistical problems and paper theorems formalized and verified using **Statopia Prover**, together with their Lean proofs, input materials, and verification evidence. It also includes six guided IMO problem results and a neural-network approximation contribution to Statlib.

The collection contains 83 selected statistics problems, six IMO results, six paper-theorem developments, two curated paper examples, and a neural-network approximation interface. The results come from selected proof runs and curated examples; supplied mathematical guides, theorem assumptions, and historical provenance are recorded alongside the proofs.

Start with [CATALOG.md](CATALOG.md) for every selected problem and its proof entry, or [SIGNATURES.md](statistics-benchmark/SIGNATURES.md) for the complete Lean theorem signatures of the 83 statistics problems.

## Results and where to find them

| Category | Results | Location |
| --- | --- | --- |
| Statistics problems | 83 selected results: 41 single-file proofs and 42 Deep developments, covering estimation, inference, regression, concentration, survival analysis, and related topics | [statistics-benchmark/](statistics-benchmark/README.md) |
| IMO problems | Six guided results, with exact run inputs, mathematical guides, and Lean proofs; P3 targets `V_eq` | [imo-2026/](imo-2026/README.md) |
| Paper theorems | Gaussian approximation, HulC coverage, two HMC targets, data thinning, EILLS, and the CQR and BH/FDR curated examples listed below | [papers/](papers/README.md) |
| Neural-network approximation | Reference paper, seven Lean source modules, a Statlib contribution summary, and an interface exposing the network depth and approximation-error dependence on resolution | [statlib-contributions/neural-network-approximation/](statlib-contributions/neural-network-approximation/SUMMARY.md) |

The paper developments and examples are organized as follows:

| Result | Materials and Lean proofs |
| --- | --- |
| Gaussian approximation — Theorem 3.1 | [papers/gaussian/](papers/gaussian/README.md) |
| HulC — Theorem 1 and its fixed-batch coverage lemma | [papers/hulc/](papers/hulc/README.md) |
| HMC — Theorem 2.2 (i), (ii) | [papers/hmc/theorem-2.2/](papers/hmc/theorem-2.2/README.md) |
| HMC — Theorem 5.14, v5 corrigendum version | [papers/hmc/theorem-5.14/](papers/hmc/theorem-5.14/README.md) |
| Data thinning — Theorem 1 | [papers/data-thinning/](papers/data-thinning/README.md) |
| EILLS — Theorem 4.2 | [papers/eills/](papers/eills/README.md) |
| CQR — lower-coverage core under explicit score/quantile assumptions | [papers/cqr/](papers/cqr/README.md) |
| BH/FDR — Dobriban certificates and Lei leave-one-out interfaces | [papers/bh-fdr/](papers/bh-fdr/README.md) |

The seven neural-network source modules are available under [Statlib/Nonparametric/](statlib-contributions/neural-network-approximation/Statlib/Nonparametric/), including [ShallowReLUApproximation.lean](statlib-contributions/neural-network-approximation/Statlib/Nonparametric/Approximation/ShallowReLUApproximation.lean). The neural-network result is an approximation component. [AtResolution.lean](statlib-contributions/neural-network-approximation/AtResolution.lean) exposes explicit depth and error bounds for every sufficiently large resolution; it does not claim the full statistical regression-risk theorem.

## File organization

```text
statistics-benchmark/
  SIGNATURES.md                     # Complete signatures for the 83 problems
  <problem>/
    input.tex                      # Original mathematical question
    theorem.yaml                   # Structured theorem input
    input.lean                     # Lean statement supplied to the run
    proof/                         # Original proof: Main.lean or ProverJobs/...
    evidence/                      # Historical run and usage evidence

imo-2026/
  official-problems.pdf
  problem1/ ... problem6/
    input/                         # Available source statements and attribution
    actual-run-input/              # Exact selected Lean input and supplied guide
    proof/                         # Final local Lean module closure
    evidence/                      # Run and usage evidence

papers/
  gaussian/ | hulc/ | hmc/ | data-thinning/ | eills/
    source/                        # Original input TeX
    materials/                     # Paper PDFs and structured theorem inputs
    Main.lean                      # Original main-task reading snapshot
    integrated/                    # Original integrated Lean module tree
    root-closure.json              # Final entry and reachable source inventory
  cqr/ | bh-fdr/
    input/                         # Curated theorem inputs and embedded proofs
    materials/                     # Reference PDFs
    proof/                         # Reconstructed Lean proof modules

statlib-contributions/neural-network-approximation/
  materials/                       # Reference paper and author materials
  SUMMARY.md                       # Contribution and interface summary
  Statlib/Nonparametric/            # Seven published neural-network Lean modules
  AtResolution.lean                # Explicit resolution/depth/error interface

verification/
  minimal-sources/                  # Reproduction proofs with narrowed imports
  statlib-cache/                    # Required Statlib compiled dependencies only
  clean-build.json                  # Case compilation and target-axiom receipts
  kernel-replay.json                # Compiled-declaration replay results
  VALIDATION.md                     # Validation scope and retained assumptions

scripts/                           # Runtime verification tools
  verify_minimal.py                 # Compile all case developments and neural wrapper
  replay_cache.py                   # Kernel-replay selected Statlib declarations
  check_archive.py                  # Check file hashes and validation bindings
evaluation/                        # Historical measurement tables and provenance
CATALOG.md                         # Complete input-to-proof catalogue
```

Layouts vary by case. The catalogue and case READMEs identify the exact entry modules. Original source snapshots remain in the four collections; use the corresponding files in [verification/minimal-sources/](verification/minimal-sources/) to reproduce the proofs with the selected binary dependency subset. Input skeletons and unused historical support declarations may contain placeholders, so the validation record refers to the checked final targets and their actual dependencies.

## Reproduce the verification

Requirements: elan, Python 3.12+, GNU Make, and the pinned public Mathlib dependencies. Lean and Mathlib versions are fixed by `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`. Run from the repository root:

```sh
make check   # Check published file hashes, case inventories, and validation bindings
make setup   # Fetch pinned public Mathlib dependencies and their compiled cache
make verify  # Compile all 97 case developments and the neural wrapper; inspect target axioms
make replay  # Kernel-replay eligible declarations in the supplied Statlib cache
```

`make verify` is the complete proof-compilation entry point. Separate cases retain their own module namespaces, including multiple `Main` modules, so plain `lake build` does not enumerate the collection. Verification commands write new reports; `make check` checks the published snapshot before those reports are regenerated. See [verification/README.md](verification/README.md) for details.

The required **144 compiled Statlib modules** are supplied, together with the **seven neural-network Lean source modules** linked in the [source inventory](statlib-contributions/neural-network-approximation/README.md). Other Statlib implementation sources are not included. Public Lean/Mathlib and these version-matched binary dependencies are sufficient for the recorded reproduction procedure.

## Validation and assumptions

The [validation record](verification/VALIDATION.md) documents successful isolated compilation of **97 case developments / 768 derived Lean modules**, plus the neural wrapper. The 97 cases comprise 83 statistics problems, six IMO results, six paper-theorem developments, and two curated paper examples. Kernel replay accepted **5,915 eligible safe, non-partial declarations** from the selected library subset. Linux with the pinned toolchain is the tested environment.

The Gaussian final target retains **three citation assumptions**, and HMC Theorem 2.2 retains **one**. The other inspected case roots, including HulC, have no nonstandard axioms. HulC retains explicit modeling hypotheses and the pipeline's auto-adoption flag; see its [formalization scope](papers/hulc/FORMALIZATION.md). These assumptions remain explicit: successful compilation does not prove the cited results. Compilation and axiom inspection also do not replace an independent mathematical comparison with the original question or paper.

[Independent review](verification/REVIEW.md), the [binary manifest](verification/binary-manifest.json), and [source provenance](evaluation/source-provenance.json) retain the supporting evidence. Historical manifests may refer to editorial artifacts moved out of the project; [cleanup records](verification/cleanup.json) identify those paths and hashes.

## Historical measurements

[Measurement definitions](evaluation/METHODOLOGY.md), [statistics CSV](evaluation/statistics-offpeak.csv), [IMO CSV](evaluation/imo-offpeak.csv), and [paper CSV](evaluation/papers.csv) retain time, token, and cost evidence for the original runs. These are selected historical experiments with their recorded guidance and accounting limits; the measurements describe the original source snapshots.
