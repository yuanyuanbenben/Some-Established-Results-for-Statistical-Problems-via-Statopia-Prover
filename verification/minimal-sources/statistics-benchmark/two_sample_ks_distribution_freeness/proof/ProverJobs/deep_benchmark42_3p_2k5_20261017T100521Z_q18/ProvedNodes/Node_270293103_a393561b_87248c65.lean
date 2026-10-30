import Statlib.HypothesisTesting.Nonparametric.MannWhitney
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q18.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q18.Base

open MeasureTheory ProbabilityTheory Filter

open MeasureTheory ProbabilityTheory Filter

set_option autoImplicit false in
theorem statopia_math_node_270293103_a393561b : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Lam : Measure ℝ) [IsProbabilityMeasure Lam]
    (m n : ℕ)
    (f : Fin m → Ω → ℝ) (f' : Fin m → Ω → ℝ)
    (g : Fin n → Ω → ℝ) (g' : Fin n → Ω → ℝ)
    (hf_meas : ∀ i, Measurable (f i))
    (hf'_meas : ∀ i, Measurable (f' i))
    (hg_meas : ∀ j, Measurable (g j))
    (hg'_meas : ∀ j, Measurable (g' j))
    (hf_indep : iIndepFun f P)
    (hf'_indep : iIndepFun f' P)
    (hg_indep : iIndepFun g P)
    (hg'_indep : iIndepFun g' P)
    (hfg_indep : IndepFun (fun ω ↦ fun i ↦ f i ω) (fun ω ↦ fun j ↦ g j ω) P)
    (hf'g'_indep : IndepFun (fun ω ↦ fun i ↦ f' i ω) (fun ω ↦ fun j ↦ g' j ω) P)
    (hf_law : ∀ i, Measure.map (f i) P = Lam)
    (hf'_law : ∀ i, Measure.map (f' i) P = Lam)
    (hg_law : ∀ j, Measure.map (g j) P = Lam)
    (hg'_law : ∀ j, Measure.map (g' j) P = Lam),
    Measure.map (fun ω ↦ ((fun i ↦ f i ω), (fun j ↦ g j ω))) P
      = Measure.map (fun ω ↦ ((fun i ↦ f' i ω), (fun j ↦ g' j ω))) P := by
  /- @proof-region region.target-node.session.59296819399764d5 begin -/
  intro Ω _ P _ Lam _ m n f f' g g' hf_meas hf'_meas hg_meas hg'_meas
    hf_indep hf'_indep hg_indep hg'_indep hfg_indep hf'g'_indep
    hf_law hf'_law hg_law hg'_law
  have hX : Measure.map (fun ω (i : Fin m) => f i ω) P = Measure.pi (fun _ : Fin m => Lam) := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map fun i => (hf_meas i).aemeasurable).1 hf_indep]
    simpa using congrArg Measure.pi (funext fun i => hf_law i)
  have hY : Measure.map (fun ω (j : Fin n) => g j ω) P = Measure.pi (fun _ : Fin n => Lam) := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map fun j => (hg_meas j).aemeasurable).1 hg_indep]
    simpa using congrArg Measure.pi (funext fun j => hg_law j)
  have hX' : Measure.map (fun ω (i : Fin m) => f' i ω) P = Measure.pi (fun _ : Fin m => Lam) := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map fun i => (hf'_meas i).aemeasurable).1 hf'_indep]
    simpa using congrArg Measure.pi (funext fun i => hf'_law i)
  have hY' : Measure.map (fun ω (j : Fin n) => g' j ω) P = Measure.pi (fun _ : Fin n => Lam) := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map fun j => (hg'_meas j).aemeasurable).1 hg'_indep]
    simpa using congrArg Measure.pi (funext fun j => hg'_law j)
  have hXa : AEMeasurable (fun ω (i : Fin m) => f i ω) P :=
    (measurable_pi_iff.mpr hf_meas).aemeasurable
  have hYa : AEMeasurable (fun ω (j : Fin n) => g j ω) P :=
    (measurable_pi_iff.mpr hg_meas).aemeasurable
  have hX'a : AEMeasurable (fun ω (i : Fin m) => f' i ω) P :=
    (measurable_pi_iff.mpr hf'_meas).aemeasurable
  have hY'a : AEMeasurable (fun ω (j : Fin n) => g' j ω) P :=
    (measurable_pi_iff.mpr hg'_meas).aemeasurable
  have hpair : Measure.map (fun ω => ((fun i => f i ω), (fun j => g j ω))) P
      = Measure.prod (Measure.map (fun ω (i : Fin m) => f i ω) P)
          (Measure.map (fun ω (j : Fin n) => g j ω) P) :=
    Statlib.HypothesisTesting.indepFun_map_pair hXa hYa hfg_indep
  have hpair' : Measure.map (fun ω => ((fun i => f' i ω), (fun j => g' j ω))) P
      = Measure.prod (Measure.map (fun ω (i : Fin m) => f' i ω) P)
          (Measure.map (fun ω (j : Fin n) => g' j ω) P) :=
    Statlib.HypothesisTesting.indepFun_map_pair hX'a hY'a hf'g'_indep
  rw [hpair, hpair', hX, hY, hX', hY']
  /- @proof-region region.target-node.session.59296819399764d5 end -/
