# Gaussian — Theorem 3.1

Bootstrapping Max Statistics in High Dimensions: Near-Parametric Rates Under Weak Variance Decay and Application to Functional and Multinomial Data

- 主定理原始代码：[Main.lean](Main.lean)（977 行，原字节未改）。
- 接合验收代码：[integrated/README.md](integrated/README.md)；88 个 Lean 文件，共 15388 行（不含本目录重复的阅读快照）。
- 输入材料：[main.tex](source/main.tex)、[supp.tex](source/supp.tex)、[theorems.yaml](materials/theorems.yaml)。

## 使用

`Main.lean` 与 `task-main/` 是各任务最终源码的阅读快照；文件名便于归档，原 import 和命名空间保持不变。构建任务组最终接合证明时，以 `integrated/` 下的原始模块树为准；该导出已替换任务组中完成证明的子任务接口，仍显式保留最终验收所需的外部结果假设（若有）。

在匹配的 Lean / Mathlib / Statlib 项目中，将 `integrated/ProverJobs/` 放入模块根目录，按原导出的 README 执行：

```bash
lake build ProverJobs.paper_fresh_20261028t224543381z_gaussian.PaperProofInterfaces.Result_r2_2a5e73d910e344948b8ec113203581bb
```

不需要把 `task-main/` 的阅读副本加入构建。包内没有复制整个 Mathlib / Statlib 库。

## 任务源码

| 任务 | 分类 | 组阶段 | 源码 |
|---|---|---|---|
| Theorem 3.1 (Gaussian approximation; THM:G) | root | verified | [Lean](Main.lean) |
| prop:bentkus | article | verified | [Lean](task-main/01-paper_e9c0500526fe4a15b7473a5f9efc21ed.lean) |
| prop:IandIII | article | verified | [Lean](task-main/02-paper_82217ff9ed45452ea25ea7588fe2ef01.lean) |
| Lemma `lem:bounds` | article | verified | [Lean](task-main/03-paper_cb04ce35a04d48a9bf96750470ca0eb0.lean) |
| Lemma `lem:slepian2` | article | verified | [Lean](task-main/04-paper_d731a49b3997405b944f72bca5b16eab.lean) |
| Lemma `lem:Snjnorm` / Lemma D.4 | article | verified | [Lean](task-main/05-paper_df5fdc450bf24d85b08215e07b20fdad.lean) |

分类与标题沿用实际任务组登记；Definition、Assumption 等条目是工作流材料任务的名称，不代表本次独立证明了这些假设。

## 最终接合保留的假设

- PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.ExternalRevision_bb11d988567af52975f2aee092d3dde32f3d1f221c6808fdb6d1bca0ad00547c.citation (consumer paper_e9c0500526fe4a15b7473a5f9efc21ed, result paper_939f6a24b4ee4e378c0de2ad4ed252f8)
- PaperProofTasks.job_paper_df5fdc450bf24d85b08215e07b20fdad.ExternalRevision_b6071945cf90850933f075b907c86da3bc0900ed9d0e2c5e428f11284eee47a4.citation (consumer paper_df5fdc450bf24d85b08215e07b20fdad, result paper_83c5bfd1c48a46908ad83ab8d1287d4f)
- PaperProofTasks.job_paper_df5fdc450bf24d85b08215e07b20fdad.ext_model_2 (consumer paper_df5fdc450bf24d85b08215e07b20fdad, result paper_5e55a39414914735a42d679e7fe1d6d2)

## retain 登记条目（不等于最终假设）

- Theorem 1.1 of Bentkus (2003)
- Lyapunov's inequality
- Li and Shao (2002), Theorem 2.2
- Zinn (1985), Theorem 2.5 (nonnegative case) and Theorem 4.1 with p. 247 remark (mean-zero case)
- Vershynin, High-Dimensional Probability, Proposition 2.7.1 (and Definition 2.7.5)

外部结果的 `pending` 是 retain 登记状态，不是尚在运行的证明子任务；其具体 Lean 声明见接合源码和integrated/README.md 和 manifest.json。

## 当前验证

精简依赖版本已通过隔离编译和最终声明公理检查；实际使用的非标准引用假设数为 3。历史 retain 登记数与实际公理依赖分别记录，详见[验证记录](../../verification/VALIDATION.md)。

原始 Main、任务阅读副本和接合 Lean 源码保持原字节。独立项目的复现入口为根目录 `make verify`，使用 `verification/minimal-sources/` 中的对应案例。论文原始输入 TeX/YAML 与 PDF 保留；重复 ZIP、TODO 进度投影及报告 TeX 已移出。
