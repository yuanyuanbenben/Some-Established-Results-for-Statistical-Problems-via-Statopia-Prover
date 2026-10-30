import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q02.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q02.Base

open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_3549106997_e1262180 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n)
    (I : Fin n → Ω → Fin n)
    (hI_meas : ∀ j, Measurable (I j))
    (hI_indep : iIndepFun I P)
    (hI_uniform : ∀ i j, P {ω | I j ω = i} = (n : ENNReal)⁻¹)
    (X : Fin n → Ω → ℝ)
    (hIX_indep : IndepFun (fun ω j ↦ I j ω) (fun ω i ↦ X i ω) P)
    (j l : Fin n) (hjl : j ≠ l),
    IndepFun (fun ω ↦ (I j ω, I l ω)) (fun ω i ↦ X i ω) P ∧
      ∀ i k : Fin n,
        (P {ω | I j ω = i ∧ I l ω = k}).toReal = (n : ℝ)⁻¹ * (n : ℝ)⁻¹ := by
  /- @proof-region region.target-node.session.b4c41b7057d0ef8c begin -/
  intro Ω _ P _ n hn I hI_meas hI_indep hI_uniform X hIX_indep j l hjl
  constructor
  · have hΦ : Measurable (fun v : Fin n → Fin n => (v j, v l)) :=
      (measurable_pi_apply j).prodMk (measurable_pi_apply l)
    have hcomp := hIX_indep.comp hΦ measurable_id
    simpa [Function.comp] using hcomp
  · intro i k
    have hind : IndepFun (I j) (I l) P := hI_indep.indepFun hjl
    have hE : (I j) ⁻¹' {i} = {ω | I j ω = i} := by ext ω; simp
    have hF : (I l) ⁻¹' {k} = {ω | I l ω = k} := by ext ω; simp
    have hA : {ω | I j ω = i ∧ I l ω = k} = (I j) ⁻¹' {i} ∩ (I l) ⁻¹' {k} := by
      ext ω; simp
    rw [hA,
      hind.measure_inter_preimage_eq_mul {i} {k} (measurableSet_singleton i) (measurableSet_singleton k),
      hE, hF, hI_uniform i j, hI_uniform k l,
      ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  /- @proof-region region.target-node.session.b4c41b7057d0ef8c end -/
