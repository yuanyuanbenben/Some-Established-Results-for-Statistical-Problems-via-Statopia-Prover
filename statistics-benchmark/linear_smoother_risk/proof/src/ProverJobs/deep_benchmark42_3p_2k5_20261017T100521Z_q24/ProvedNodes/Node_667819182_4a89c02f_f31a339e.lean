import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q24.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q24.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q24.ProvedNodes.Node_164904365_da5689c8_f2899239
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q24.ProvedNodes.Node_256592153_d1df539a_a9eade84
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q24.ProvedNodes.Node_3144086322_3ff63bdf_1eb4bc8d



open MeasureTheory

open MeasureTheory

set_option autoImplicit false in
theorem statopia_math_node_667819182_4a89c02f : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n)
    (f : Fin n → ℝ)
    (xi : Ω → Fin n → ℝ)
    (hxi_meas : Measurable xi)
    (hxi_sq_int : Integrable (fun ω ↦ ∑ i, (xi ω i) ^ 2) P)
    (sigma2 : ℝ) (hsigma2 : 0 ≤ sigma2)
    (hxi_mean : ∀ j : Fin n, ∫ ω, xi ω j ∂P = 0)
    (hxi_cov : ∀ j k : Fin n,
      ∫ ω, xi ω j * xi ω k ∂P = if j = k then sigma2 else 0)
    (S : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n),
    ∫ ω, ((S.mulVec (fun j ↦ f j + xi ω j) - f) i) ^ 2 ∂P
      = ((S.mulVec f - f) i) ^ 2 + sigma2 * ∑ j, (S i j) ^ 2 := by
  /- @proof-region region.target-node.session.52d33db1e98d438d begin -/
  intro Ω hΩ P hPa n hn f xi hxi_meas hxi_sq_int sigma2 hsigma2 hxi_mean hxi_cov S i
  have hcoord_int : ∀ j : Fin n, Integrable (fun ω => xi ω j) P := fun j =>
    (statopia_math_node_3144086322_3ff63bdf P n xi hxi_meas hxi_sq_int j j).2.1
  have hL_int : Integrable (fun ω => ∑ j, S i j * xi ω j) P :=
    (statopia_math_node_256592153_d1df539a P n xi hxi_meas hxi_sq_int S (S.mulVec f - f)).1 i
  have hL2_int : Integrable (fun ω => (∑ j, S i j * xi ω j) ^ 2) P :=
    (statopia_math_node_256592153_d1df539a P n xi hxi_meas hxi_sq_int S (S.mulVec f - f)).2.1 i
  have hpt : ∀ ω : Ω, ((S.mulVec (fun j ↦ f j + xi ω j) - f) i)
      = (S.mulVec f - f) i + ∑ j, S i j * xi ω j := by
    intro ω
    simp only [Matrix.mulVec, Pi.sub_apply]
    rw [show (fun j => S i j) ⬝ᵥ (fun j => f j + xi ω j)
          = ∑ j, S i j * (f j + xi ω j) from rfl,
        show (fun j => S i j) ⬝ᵥ f = ∑ j, S i j * f j from rfl]
    simp only [mul_add, Finset.sum_add_distrib]
    ring
  rw [show (∫ ω, ((S.mulVec (fun j ↦ f j + xi ω j) - f) i) ^ 2 ∂P)
      = ∫ ω, ((S.mulVec f - f) i + ∑ j, S i j * xi ω j) ^ 2 ∂P from by
    apply integral_congr_ae
    filter_upwards with ω
    rw [hpt ω]]
  have hconst : ∫ ω, ((S.mulVec f - f) i) ^ 2 ∂P = ((S.mulVec f - f) i) ^ 2 := by
    rw [integral_const]
    simp
  have hcross : ∫ ω, (2 * (S.mulVec f - f) i) * (∑ j, S i j * xi ω j) ∂P = 0 := by
    have hL_zero : ∫ ω, (∑ j, S i j * xi ω j) ∂P = 0 := by
      rw [integral_finset_sum Finset.univ (fun j _ => (hcoord_int j).const_mul (S i j))]
      simp [integral_const_mul, hxi_mean]
    rw [integral_const_mul, hL_zero, mul_zero]
  have hvar : ∫ ω, (∑ j, S i j * xi ω j) ^ 2 ∂P = sigma2 * ∑ j, (S i j) ^ 2 :=
    statopia_math_node_164904365_da5689c8 P n xi hxi_meas hxi_sq_int sigma2 hxi_cov S i
  have hstep : ∫ ω, ((S.mulVec f - f) i + ∑ j, S i j * xi ω j) ^ 2 ∂P
      = ∫ ω, ((S.mulVec f - f) i) ^ 2 ∂P
        + ∫ ω, (2 * (S.mulVec f - f) i) * (∑ j, S i j * xi ω j) ∂P
        + ∫ ω, (∑ j, S i j * xi ω j) ^ 2 ∂P := by
    have hA : Integrable (fun ω => ((S.mulVec f - f) i) ^ 2) P := integrable_const _
    have hB : Integrable (fun ω => (2 * (S.mulVec f - f) i) * (∑ j, S i j * xi ω j)) P :=
      hL_int.const_mul _
    have hBC : Integrable (fun ω => (2 * (S.mulVec f - f) i) * (∑ j, S i j * xi ω j)
        + (∑ j, S i j * xi ω j) ^ 2) P := hB.add hL2_int
    rw [show (fun ω => ((S.mulVec f - f) i + ∑ j, S i j * xi ω j) ^ 2)
        = (fun ω => ((S.mulVec f - f) i) ^ 2
            + ((2 * (S.mulVec f - f) i) * (∑ j, S i j * xi ω j)
              + (∑ j, S i j * xi ω j) ^ 2)) from by
      funext ω; ring]
    rw [integral_add hA hBC]
    rw [integral_add hB hL2_int]
    ring
  rw [hstep, hconst, hcross, hvar]
  ring
  /- @proof-region region.target-node.session.52d33db1e98d438d end -/
