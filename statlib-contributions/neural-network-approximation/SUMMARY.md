# Neural-network approximation contribution

Reference: Michael Kohler and Sophie Langer, *On the rate of convergence of fully connected deep neural network regression estimates*, Annals of Statistics 49(4), 2231–2249 (2021), [DOI](https://doi.org/10.1214/20-AOS2034). [Reference PDF](materials/original-paper.pdf) and [retrieved author TeX](materials/arxiv-source.tar.gz) accompany this archive. They are reference materials retrieved during packaging, not proof of the exact version supplied to every historical attack.

The primary reproduction interface is [AtResolution.lean](AtResolution.lean). It explicitly exports fixed positive architecture constants and, for every sufficiently large resolution `M`, a network of depth `M^d * (Dblock + 1)`, bounded width, the stated parameter budget, and error bounded by `cState * M^(-2(r+beta))`. The proof refers to the existing compiled construction certificate; it does not include Statlib implementation source or add an axiom. The binary package is pinned by hashes, and a missing or renamed certificate makes this wrapper fail closed. This remains an approximation component, not the full statistical regression-risk theorem.

The old public endpoint's complete type and recorded axiom check remain in [compiled-interface-check.txt](compiled-interface-check.txt), with [verify-public-theorem.lean](verify-public-theorem.lean) as its small check. Inspection found that its quantified `M` is absent from the remainder of its statement: it does not require `L` to grow with `M`. That older public type alone therefore does not establish arbitrary precision or an asymptotic approximation rate. The new wrapper exposes the stronger depth/resolution relationship already proved by the internal construction, while preserving the original library and public signature.

The local curated snapshot contains seven modules, 55,922 physical source lines:

| Module role | Lines |
| --- | ---: |
| Network vocabulary and parameter counts | 447 |
| Approximation algebra and construction lemmas | 35,028 |
| ReLU network constructions | 7,713 |
| ReLU state machine | 8,466 |
| Smooth-function approximation geometry | 3,781 |
| Public approximation theorem and assembly | 380 |
| Higher-level approximation interfaces | 107 |

[metrics.json](metrics.json) records exact local source hashes. These modules are library development accumulated across runs; this archive assigns no single-run generation cost or runtime. Local source scans and the recorded compiled-interface check are distinct from a source rebuild of the entire contribution.

This project excludes the private `Statlib/` source subtree and `public-import-surface.lean`, which are preserved outside its directory. It supplies this summary, theorem interface, reference materials, and only compiled modules in the required dependency closure. Compiled declarations and proof terms remain inspectable: `.olean` is not an obfuscation or secrecy format.
