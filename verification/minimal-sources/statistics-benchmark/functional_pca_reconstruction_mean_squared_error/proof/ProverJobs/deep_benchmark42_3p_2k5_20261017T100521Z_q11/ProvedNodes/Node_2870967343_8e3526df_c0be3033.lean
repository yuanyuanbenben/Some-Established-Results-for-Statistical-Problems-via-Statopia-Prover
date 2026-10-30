import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q11.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q11.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q11.ProvedNodes.Node_714068217_742cf005_d2274bfe

open MeasureTheory

open MeasureTheory

set_option autoImplicit false in
theorem statopia_math_node_2870967343_8e3526df : ∀ {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → H)
    (hXmeas : StronglyMeasurable X)
    (hXsq : Integrable (fun ω => ‖X ω‖ ^ 2) P)
    (C : H →L[ℝ] H)
    (phi : ℕ → H) (lambda : ℕ → ℝ)
    (horth : Orthonormal ℝ phi)
    (heigen : ∀ k, C (phi k) = lambda k • phi k)
    (hC : ∀ h : H,
      C h =
        ∫ ω, (inner ℝ (X ω - ∫ z, X z ∂P) h) •
          (X ω - ∫ z, X z ∂P) ∂P),
    ∀ k : ℕ,
      AEStronglyMeasurable (fun ω => inner ℝ (X ω - ∫ z, X z ∂P) (phi k)) P ∧
      Integrable (fun ω => (inner ℝ (X ω - ∫ z, X z ∂P) (phi k)) ^ 2) P ∧
      lambda k = ∫ ω, (inner ℝ (X ω - ∫ z, X z ∂P) (phi k)) ^ 2 ∂P ∧
      0 ≤ lambda k := by
  /- @proof-region region.target-node.session.74f322eb30b132ef begin -/
  intro Ω H _ _ _ _ P _ X hXmeas hXsq C phi lambda horth heigen hC k
  obtain ⟨-, hYmeas, hYsqint, -, -⟩ :=
    statopia_math_node_714068217_742cf005 P X hXmeas hXsq
  set Y : Ω → H := fun ω => X ω - ∫ z, X z ∂P with hYdef
  set a : Ω → ℝ := fun ω => inner ℝ (Y ω) (phi k) with hadef
  have hinner_self : inner ℝ (phi k) (phi k) = 1 := by
    simpa using (orthonormal_iff_ite.mp horth k k)
  have hphi : ‖phi k‖ = 1 := by
    have h : ‖phi k‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq]
      exact hinner_self
    nlinarith [norm_nonneg (phi k)]
  have ha_meas : AEStronglyMeasurable a P := by
    have h : AEStronglyMeasurable (fun ω => inner ℝ (Y ω) (phi k)) P :=
      hYmeas.inner (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : Ω => phi k) P)
    simpa [hadef, hYdef] using h
  have ha_norm_le : ∀ ω, ‖a ω‖ ≤ ‖Y ω‖ := by
    intro ω
    have h3 : ‖inner ℝ (Y ω) (phi k)‖ ≤ ‖Y ω‖ * ‖phi k‖ :=
      norm_inner_le_norm (Y ω) (phi k)
    rw [hphi, mul_one] at h3
    simpa [hadef] using h3
  have ha_sq_le : ∀ ω, (a ω) ^ 2 ≤ ‖Y ω‖ ^ 2 := by
    intro ω
    have h1 : |a ω| ≤ ‖Y ω‖ := by
      have h3 : ‖a ω‖ ≤ ‖Y ω‖ := ha_norm_le ω
      rwa [Real.norm_eq_abs] at h3
    obtain ⟨h2, h3⟩ := abs_le.mp h1
    exact sq_le_sq' h2 h3
  have ha2_int : Integrable (fun ω => (a ω) ^ 2) P := by
    have hmeas : AEStronglyMeasurable (fun ω => (a ω) ^ 2) P := by
      simpa [pow_two] using ha_meas.mul ha_meas
    refine hYsqint.mono' hmeas ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (a ω))]
    exact ha_sq_le ω
  have hsmul_int : Integrable (fun ω => a ω • Y ω) P := by
    have hmeas : AEStronglyMeasurable (fun ω => a ω • Y ω) P := ha_meas.smul hYmeas
    refine hYsqint.mono' hmeas ?_
    filter_upwards with ω
    rw [norm_smul]
    calc ‖a ω‖ * ‖Y ω‖ ≤ ‖Y ω‖ * ‖Y ω‖ :=
          mul_le_mul_of_nonneg_right (ha_norm_le ω) (norm_nonneg _)
      _ = ‖Y ω‖ ^ 2 := by ring
  have hCk : C (phi k) = ∫ ω, a ω • Y ω ∂P := by
    simpa only [hadef, hYdef] using hC (phi k)
  have hcomm :
      inner ℝ (∫ ω, a ω • Y ω ∂P) (phi k) =
        ∫ ω, inner ℝ (a ω • Y ω) (phi k) ∂P := by
    calc inner ℝ (∫ ω, a ω • Y ω ∂P) (phi k)
        = inner ℝ (phi k) (∫ ω, a ω • Y ω ∂P) := real_inner_comm (phi k) _
      _ = ∫ ω, inner ℝ (phi k) (a ω • Y ω) ∂P :=
          (integral_inner (𝕜 := ℝ) hsmul_int (phi k)).symm
      _ = ∫ ω, inner ℝ (a ω • Y ω) (phi k) ∂P := by
          apply integral_congr_ae
          filter_upwards with ω
          exact (real_inner_comm (phi k) (a ω • Y ω)).symm
  have hlam : lambda k = inner ℝ (C (phi k)) (phi k) := by
    rw [heigen k, real_inner_smul_left, hinner_self, mul_one]
  have hpoint : ∀ ω, inner ℝ (a ω • Y ω) (phi k) = (a ω) ^ 2 := by
    intro ω
    rw [real_inner_smul_left]
    simp [hadef, pow_two]
  have hmain : lambda k = ∫ ω, (a ω) ^ 2 ∂P := by
    rw [hlam, hCk, hcomm]
    simp [hpoint]
  have hnonneg : 0 ≤ lambda k := by
    rw [hmain]
    exact integral_nonneg fun ω => sq_nonneg (a ω)
  exact ⟨by simpa [hadef, hYdef] using ha_meas,
    by simpa [hadef, hYdef] using ha2_int,
    by simpa [hadef, hYdef] using hmain,
    by simpa [hadef, hYdef] using hnonneg⟩
  /- @proof-region region.target-node.session.74f322eb30b132ef end -/
