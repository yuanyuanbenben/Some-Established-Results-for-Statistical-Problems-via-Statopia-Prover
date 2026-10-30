# EILLS — Theorem 4.2

Environment Invariant Linear Least Squares

- 主定理原始代码：[Main.lean](Main.lean)（736 行，原字节未改）。
- 接合验收代码：[integrated/README.md](integrated/README.md)；11 个 Lean 文件，共 2141 行（不含本目录重复的阅读快照）。
- 输入材料：[main.tex](source/main.tex)、[supp.tex](source/supp.tex)、[theorems.yaml](materials/theorems.yaml)。

## 使用

`Main.lean` 与 `task-main/` 是各任务最终源码的阅读快照；文件名便于归档，原 import 和命名空间保持不变。构建任务组最终接合证明时，以 `integrated/` 下的原始模块树为准；该导出已替换任务组中完成证明的子任务接口，仍显式保留最终验收所需的外部结果假设（若有）。

在匹配的 Lean / Mathlib / Statlib 项目中，将 `integrated/ProverJobs/` 放入模块根目录，按原导出的 README 执行：

```bash
lake build ProverJobs.paper_fresh_20261028t224543381z_eills.PaperProofInterfaces.Result_r2_5caa9f2b59d84ff58e877f7752096e6d
```

不需要把 `task-main/` 的阅读副本加入构建。包内没有复制整个 Mathlib / Statlib 库。

## 任务源码

| 任务 | 分类 | 组阶段 | 源码 |
|---|---|---|---|
| Theorem 4.2 (Strong Convexity with respect to beta-star; thm:global-strong-convexity-main) | root | verified | [Lean](Main.lean) |

分类与标题沿用实际任务组登记；Definition、Assumption 等条目是工作流材料任务的名称，不代表本次独立证明了这些假设。

## 最终接合保留的假设

本轮隔离编译后的递归公理检查表明：最终主定理只依赖 `propext`、`Classical.choice`、`Quot.sound`。下面的 `ext_model_1` 声明保留在原导出包中，但未被该主定理实际使用。当前结果见 `verification/clean-build.json` 的 `papers/eills` 记录；下面列表保留历史导出记录。

- PaperProofTasks.paper_fresh_20261028t224543381z_eills.ext_model_1 (consumer paper_fresh_20261028t224543381z_eills, result paper_2c08ddb98e7c4dc4993a0b23e7a07337)

## retain 登记条目（不等于最终假设）

- Cauchy–Schwarz inequality (standard Euclidean form)

外部结果的 `pending` 是 retain 登记状态，不是尚在运行的证明子任务；其具体 Lean 声明见接合源码和integrated/README.md 和 manifest.json。

## 当前验证

精简依赖版本已通过隔离编译和最终声明公理检查；实际使用的非标准引用假设数为 0。历史 retain 登记数与实际公理依赖分别记录，详见[验证记录](../../verification/VALIDATION.md)。

原始 Main、任务阅读副本和接合 Lean 源码保持原字节。独立项目的复现入口为根目录 `make verify`，使用 `verification/minimal-sources/` 中的对应案例。论文原始输入 TeX/YAML 与 PDF 保留；重复 ZIP、TODO 进度投影及报告 TeX 已移出。

[历史运行报告 PDF](report/report.pdf)。
