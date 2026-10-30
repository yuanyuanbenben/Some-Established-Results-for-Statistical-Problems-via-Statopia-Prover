# HMC — Theorem 5.14（v5 勘误版）

On the Geometric Ergodicity of Hamiltonian Monte Carlo (arXiv 1601.08057 v5 with corrigendum)

- 主定理原始代码：[Main.lean](Main.lean)（199 行，原字节未改）。
- 接合验收代码：[integrated/README.md](integrated/README.md)；51 个 Lean 文件，共 3345 行（不含本目录重复的阅读快照）。
- 输入材料：[main.tex](source/main.tex)、[supp.tex](source/supp.tex)、[theorems.yaml](materials/theorems.yaml)。

## 使用

`Main.lean` 与 `task-main/` 是各任务最终源码的阅读快照；文件名便于归档，原 import 和命名空间保持不变。构建任务组最终接合证明时，以 `integrated/` 下的原始模块树为准；该导出已替换任务组中完成证明的子任务接口，仍显式保留最终验收所需的外部结果假设（若有）。

在匹配的 Lean / Mathlib / Statlib 项目中，将 `integrated/ProverJobs/` 放入模块根目录，按原导出的 README 执行：

```bash
lake build ProverJobs.paper_fresh_20261028t151409527z_hmc_v5.PaperProofInterfaces.Result_r2_388b741cbe374909a3f9937f201e99fc
```

不需要把 `task-main/` 的阅读副本加入构建。包内没有复制整个 Mathlib / Statlib 库。

## 任务源码

| 任务 | 分类 | 组阶段 | 源码 |
|---|---|---|---|
| Theorem 5.14 (corrected statement and replacement proof in the v5 corrigendum, Appendix D; original label thm:light). Use the corrected condition (18) with norm(y) >= 3 norm(x), not the superseded printed version. | root | verified | [Lean](Main.lean) |
| Lemma 5.17 | article | verified | [Lean](task-main/01-paper_53e951f48c854f4db91e6ecda697ee2b.lean) |
| Definition 3.2 | article | verified | [Lean](task-main/02-paper_4f562633bddc4ee9afee32ec40dfa0f0.lean) |
| Proposition 3.5 | article | verified | [Lean](task-main/03-paper_a9a2ab5d4e094509b2cdb371b3b02f1c.lean) |
| Assumption A1 | article | verified | [Lean](task-main/04-paper_7ad7b898530c48b2be48d9fe88a3d538.lean) |
| Lemma 5.16 | article | verified | [Lean](task-main/05-paper_a62240be95074e8caf07c24daf22159a.lean) |
| Lemma 5.15 | article | verified | [Lean](task-main/06-paper_b7909512ace54739b0ef8eae60aa82ed.lean) |

分类与标题沿用实际任务组登记；Definition、Assumption 等条目是工作流材料任务的名称，不代表本次独立证明了这些假设。

## 最终接合保留的假设

最终接合导出没有保留外部结果假设；Lean 标准公理另计。

## retain 登记条目（不等于最终假设）

- paper_6ac1720d15ae46eb9cc770b0a5541a93

外部结果的 `pending` 是 retain 登记状态，不是尚在运行的证明子任务；其具体 Lean 声明见接合源码和integrated/README.md 和 manifest.json。

## 当前验证

精简依赖版本已通过隔离编译和最终声明公理检查；实际使用的非标准引用假设数为 0。历史 retain 登记数与实际公理依赖分别记录，详见[验证记录](../../../verification/VALIDATION.md)。

原始 Main、任务阅读副本和接合 Lean 源码保持原字节。独立项目的复现入口为根目录 `make verify`，使用 `verification/minimal-sources/` 中的对应案例。论文原始输入 TeX/YAML 与 PDF 保留；重复 ZIP、TODO 进度投影及报告 TeX 已移出。

[历史运行报告 PDF](report/report.pdf)。
