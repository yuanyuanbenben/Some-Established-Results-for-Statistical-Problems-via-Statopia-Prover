import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q31.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q31.Base

open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_2533135513_78bc87cd : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n)
    (lambda0 beta : ℝ) (hlambda : 0 < lambda0)
    (z : Fin n → ℝ)
    (T : Fin n → Ω → ℝ)
    (hTmeas : ∀ i, Measurable (T i))
    (hindep : iIndepFun T P)
    (hsurvival : ∀ (i : Fin n) (t : ℝ), 0 ≤ t →
      P {ω | t < T i ω} =
        ENNReal.ofReal (Real.exp (-lambda0 * Real.exp (beta * z i) * t))),
    ∀ (t : ℝ), 0 ≤ t → ∀ (S : Finset (Fin n)),
      P {ω | ∀ j ∈ S, t < T j ω} =
        ENNReal.ofReal (Real.exp (-(∑ j ∈ S, lambda0 * Real.exp (beta * z j)) * t)) := by
  /- @proof-region region.target-node.session.eb6a96f17b989405 begin -/
  intro Ω mΩ P hP n hn lambda0 beta hlambda z T hTmeas hindep hsurvival t ht S
  haveI := mΩ
  haveI := hP
  have hset : {ω : Ω | ∀ j ∈ S, t < T j ω} = ⋂ j ∈ S, T j ⁻¹' {x : ℝ | t < x} := by
    ext ω
    simp
  rw [hset]
  have hprod : P (⋂ j ∈ S, T j ⁻¹' {x : ℝ | t < x}) =
      ∏ j ∈ S, P (T j ⁻¹' {x : ℝ | t < x}) :=
    (iIndepFun_iff_measure_inter_preimage_eq_mul.mp hindep) S
      (sets := fun _ => {x : ℝ | t < x}) (fun i _ => measurableSet_Ioi)
  rw [hprod]
  have hfac : ∀ j ∈ S, P (T j ⁻¹' {x : ℝ | t < x}) =
      ENNReal.ofReal (Real.exp (-lambda0 * Real.exp (beta * z j) * t)) := by
    intro j _
    simpa using hsurvival j t ht
  have hprod2 : ∏ j ∈ S, P (T j ⁻¹' {x : ℝ | t < x}) =
      ∏ j ∈ S, ENNReal.ofReal (Real.exp (-lambda0 * Real.exp (beta * z j) * t)) :=
    Finset.prod_congr rfl hfac
  rw [hprod2]
  have hof : ∏ j ∈ S, ENNReal.ofReal (Real.exp (-lambda0 * Real.exp (beta * z j) * t)) =
      ENNReal.ofReal (∏ j ∈ S, Real.exp (-lambda0 * Real.exp (beta * z j) * t)) := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun j _ => (Real.exp_pos _).le)]
  rw [hof]
  congr 1
  rw [← Real.exp_sum]
  congr 1
  rw [← Finset.sum_neg_distrib, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun j _ => by ring)
  /- @proof-region region.target-node.session.eb6a96f17b989405 end -/
