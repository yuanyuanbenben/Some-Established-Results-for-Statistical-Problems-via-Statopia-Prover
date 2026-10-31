import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q26.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q26.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q26.ProvedNodes.Node_803344359_2bd487f3_989f23a6

open MeasureTheory Matrix

open MeasureTheory Matrix

set_option autoImplicit false in
theorem statopia_math_node_4216094757_85bc2c28 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n d : ℕ)
    (X : Matrix (Fin n) (Fin d) ℝ)
    (betaStar : Fin d → ℝ)
    (epsilon : Ω → Fin n → ℝ)
    (lambda : ℝ)
    (heps_int : Integrable epsilon P)
    (hcoord : ∀ i : Fin n, Integrable (fun ω => epsilon ω i) P)
    (hmean : ∫ ω, epsilon ω ∂P = 0),
    let A : Matrix (Fin d) (Fin d) ℝ := X.transpose * X + lambda • 1
    let L : Matrix (Fin d) (Fin n) ℝ := A⁻¹ * X.transpose
    let c : Fin d → ℝ := A⁻¹ *ᵥ betaStar
    ∫ ω, (∑ k : Fin d, c k * (∑ i : Fin n, L k i * epsilon ω i)) ∂P = 0 := by
  /- @proof-region region.target-node.session.2a05ae587ff4f9d4 begin -/
  intro Ω hΩ P hP n d X betaStar epsilon lambda heps_int hcoord hmean
  dsimp only
  set A : Matrix (Fin d) (Fin d) ℝ := X.transpose * X + lambda • 1 with hA
  set L : Matrix (Fin d) (Fin n) ℝ := A⁻¹ * X.transpose with hL
  set c : Fin d → ℝ := A⁻¹ *ᵥ betaStar with hc
  have h0 : ∀ i : Fin n, ∫ ω, epsilon ω i ∂P = 0 := by
    intro i
    have h := ContinuousLinearMap.integral_comp_comm
      (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ) heps_int
    rw [hmean] at h
    simpa using h
  have hint : ∀ k : Fin d, Integrable (fun ω => ∑ i : Fin n, L k i * epsilon ω i) P := by
    intro k
    exact MeasureTheory.integrable_finset_sum Finset.univ
      (fun i _ => Integrable.const_mul (hcoord i) (L k i))
  have hk : ∀ k : Fin d, Integrable (fun ω => c k * (∑ i : Fin n, L k i * epsilon ω i)) P := by
    intro k
    exact Integrable.const_mul (hint k) (c k)
  have hInner : ∀ k : Fin d, ∫ ω, (∑ i : Fin n, L k i * epsilon ω i) ∂P
      = ∑ i : Fin n, L k i * ∫ ω, epsilon ω i ∂P := by
    intro k
    rw [MeasureTheory.integral_finset_sum Finset.univ
      (fun i _ => Integrable.const_mul (hcoord i) (L k i))]
    simp only [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_finset_sum Finset.univ (fun k _ => hk k)]
  simp only [MeasureTheory.integral_const_mul]
  simp only [hInner]
  simp [h0]

  /- @proof-region region.target-node.session.2a05ae587ff4f9d4 end -/
