import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q24.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q24.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q24.ProvedNodes.Node_256592153_d1df539a_a9eade84
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q24.ProvedNodes.Node_3144086322_3ff63bdf_1eb4bc8d


open MeasureTheory

open MeasureTheory

set_option autoImplicit false in
theorem statopia_math_node_164904365_da5689c8 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ)
    (xi : Ω → Fin n → ℝ)
    (hxi_meas : Measurable xi)
    (hxi_sq_int : Integrable (fun ω => ∑ i, (xi ω i) ^ 2) P)
    (sigma2 : ℝ)
    (hxi_cov : ∀ i j : Fin n,
      ∫ ω, xi ω i * xi ω j ∂P = if i = j then sigma2 else 0)
    (S : Matrix (Fin n) (Fin n) ℝ),
    ∀ i : Fin n,
      ∫ ω, (∑ j, S i j * xi ω j) ^ 2 ∂P = sigma2 * ∑ j, (S i j) ^ 2 := by
  /- @proof-region region.target-node.session.95041d9105dc60e5 begin -/
  intro Ω hΩ P hP n xi hxi_meas hxi_sq_int sigma2 hxi_cov S i
  have h_pair : ∀ j k : Fin n, Integrable (fun ω => xi ω j * xi ω k) P :=
    fun j k => (statopia_math_node_3144086322_3ff63bdf P n xi hxi_meas hxi_sq_int j k).2.2
  have h_term : ∀ j k : Fin n,
      Integrable (fun ω => (S i j * S i k) * (xi ω j * xi ω k)) P :=
    fun j k => (h_pair j k).const_mul (S i j * S i k)
  have h_inner : ∀ j : Fin n,
      Integrable (fun ω => ∑ k, (S i j * S i k) * (xi ω j * xi ω k)) P :=
    fun j => integrable_finset_sum Finset.univ (fun k _ => h_term j k)
  have h_point : (fun ω => (∑ j, S i j * xi ω j) ^ 2)
      = fun ω => ∑ j, ∑ k, (S i j * S i k) * (xi ω j * xi ω k) := by
    funext ω
    rw [pow_two, Fintype.sum_mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    refine Finset.sum_congr rfl ?_
    intro k _
    ring
  have hdiag : ∀ j : Fin n,
      ∑ k, (S i j * S i k) * (if j = k then sigma2 else 0) = sigma2 * (S i j) ^ 2 := by
    intro j
    refine (Finset.sum_eq_single j ?_ ?_).trans ?_
    · intro k _ hk
      rw [if_neg (fun hjk => hk hjk.symm), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
    · rw [if_pos rfl]
      ring
  calc
    ∫ ω, (∑ j, S i j * xi ω j) ^ 2 ∂P
        = ∫ ω, ∑ j, ∑ k, (S i j * S i k) * (xi ω j * xi ω k) ∂P := by
          rw [h_point]
    _ = ∑ j, ∫ ω, ∑ k, (S i j * S i k) * (xi ω j * xi ω k) ∂P :=
          integral_finset_sum Finset.univ (fun j _ => h_inner j)
    _ = ∑ j, ∑ k, ∫ ω, (S i j * S i k) * (xi ω j * xi ω k) ∂P := by
          refine Finset.sum_congr rfl ?_
          intro j _
          exact integral_finset_sum Finset.univ (fun k _ => h_term j k)
    _ = ∑ j, ∑ k, (S i j * S i k) * (∫ ω, xi ω j * xi ω k ∂P) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          refine Finset.sum_congr rfl ?_
          intro k _
          exact integral_const_mul (S i j * S i k) (fun ω => xi ω j * xi ω k)
    _ = ∑ j, ∑ k, (S i j * S i k) * (if j = k then sigma2 else 0) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [hxi_cov j k]
    _ = ∑ j, sigma2 * (S i j) ^ 2 :=
          Finset.sum_congr rfl (fun j _ => hdiag j)
    _ = sigma2 * ∑ j, (S i j) ^ 2 := by
          rw [Finset.mul_sum]
  /- @proof-region region.target-node.session.95041d9105dc60e5 end -/
