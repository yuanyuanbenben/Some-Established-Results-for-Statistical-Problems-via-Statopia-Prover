# Statistical-paper developments

Each selected development preserves the source paper, organized materials, original manifest, Lean sources and available report, plus usage and timing evidence added for this evaluation.

| Target | Files | Lines |
| --- | ---: | ---: |
| gaussian | 88 | 15,388 |
| eills | 11 | 2,141 |
| data_thinning | 5 | 160 |
| hmc_22 | 22 | 4,103 |
| hmc_v5 | 51 | 3,345 |
| cqr | 6 | 388 |
| bh-fdr | 19 | 2,988 |

Counts use the complete integrated package, including retained support modules. Repeated reading copies and ZIP contents are excluded. Historical timing and fee evidence is retained in per-case files but is not part of the revised paper presentation.

## Earlier curated examples

- [CQR](cqr/README.md): six nodes, score-exchangeability/quantile-count hypotheses, lower-coverage core.
- [BH/FDR](bh-fdr/README.md): four displayed nodes plus fifteen fixed support modules, explicit certificates and input assumptions.

These two examples are reconstructed from embedded proofs in the existing curated YAML fixtures, with no new timing or usage claim.

## Reproduction and current boundaries

Use `make verify` from the project root to build the corresponding sources in `verification/minimal-sources/`. Original `Main.lean`, task reading snapshots and integrated module trees remain unchanged. Each case retains its original input TeX/YAML and paper PDFs; available proof reports remain as PDFs. Duplicate integrated-proof ZIPs, workflow TODO projections and report TeX were moved outside the project.

[Current validation](../verification/VALIDATION.md) reports actual recursive root axioms separately from retained registry entries: Gaussian has three citation assumptions, HMC 2.2 has one, and the remaining five case roots have none. Input skeletons and unused historical support declarations can still contain placeholders.
