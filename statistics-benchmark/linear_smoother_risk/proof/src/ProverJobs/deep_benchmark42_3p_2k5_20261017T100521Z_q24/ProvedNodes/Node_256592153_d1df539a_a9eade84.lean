import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q24.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q24.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q24.ProvedNodes.Node_3144086322_3ff63bdf_1eb4bc8d

open MeasureTheory

open MeasureTheory

set_option autoImplicit false in
theorem statopia_math_node_256592153_d1df539a : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ)
    (xi : Ω → Fin n → ℝ)
    (hxi_meas : Measurable xi)
    (hxi_sq_int : Integrable (fun ω => ∑ i, (xi ω i) ^ 2) P)
    (S : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ),
    (∀ i : Fin n, Integrable (fun ω => ∑ j, S i j * xi ω j) P) ∧
    (∀ i : Fin n, Integrable (fun ω => (∑ j, S i j * xi ω j) ^ 2) P) ∧
    (∀ i : Fin n, Integrable (fun ω => (b i + ∑ j, S i j * xi ω j) ^ 2) P) ∧
    (Integrable (fun ω => ∑ i, (b i + ∑ j, S i j * xi ω j) ^ 2) P) := by
  /- @proof-region region.target-node.session.c6260aa34094fb0f begin -/
  intro Ω _ P _ n xi hxi_meas hxi_sq_int S b
  have hcoord := statopia_math_node_3144086322_3ff63bdf P n xi hxi_meas hxi_sq_int
  have hlin : ∀ i : Fin n, Integrable (fun ω => ∑ j, S i j * xi ω j) P := by
    intro i
    have h : Integrable
        (fun ω => ∑ j ∈ (Finset.univ : Finset (Fin n)), S i j * xi ω j) P :=
      integrable_finset_sum _ (fun j _ => ((hcoord j j).2.1).const_mul (S i j))
    simpa using h
  have hsq : ∀ i : Fin n, Integrable (fun ω => (∑ j, S i j * xi ω j) ^ 2) P := by
    intro i
    have h : Integrable
        (fun ω => ∑ j ∈ (Finset.univ : Finset (Fin n)),
          ∑ k ∈ (Finset.univ : Finset (Fin n)),
            (S i j * S i k) * (xi ω j * xi ω k)) P :=
      integrable_finset_sum _ (fun j _ =>
        integrable_finset_sum _ (fun k _ => ((hcoord j k).2.2).const_mul (S i j * S i k)))
    have hfun : (fun ω => (∑ j, S i j * xi ω j) ^ 2)
        = fun ω => ∑ j, ∑ k, (S i j * S i k) * (xi ω j * xi ω k) := by
      funext ω
      rw [pow_two, Fintype.sum_mul_sum]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    rw [hfun]
    simpa using h
  have herr : ∀ i : Fin n, Integrable (fun ω => (b i + ∑ j, S i j * xi ω j) ^ 2) P := by
    intro i
    have h₁ : Integrable (fun _ : Ω => (b i) ^ 2) P := integrable_const _
    have h₂ : Integrable (fun ω => (2 * b i) * (∑ j, S i j * xi ω j)) P :=
      (hlin i).const_mul (2 * b i)
    have h₃ : Integrable (fun ω => (∑ j, S i j * xi ω j) ^ 2) P := hsq i
    have h₄ : Integrable (fun ω => (b i) ^ 2 + (2 * b i) * (∑ j, S i j * xi ω j)
        + (∑ j, S i j * xi ω j) ^ 2) P := (h₁.add h₂).add h₃
    have hfun : (fun ω => (b i) ^ 2 + (2 * b i) * (∑ j, S i j * xi ω j)
        + (∑ j, S i j * xi ω j) ^ 2)
        = fun ω => (b i + ∑ j, S i j * xi ω j) ^ 2 := by
      funext ω
      ring
    rw [hfun] at h₄
    exact h₄
  have hsum : Integrable (fun ω => ∑ i, (b i + ∑ j, S i j * xi ω j) ^ 2) P := by
    have h : Integrable
        (fun ω => ∑ i ∈ (Finset.univ : Finset (Fin n)),
          (b i + ∑ j, S i j * xi ω j) ^ 2) P :=
      integrable_finset_sum _ (fun i _ => herr i)
    simpa using h
  exact ⟨hlin, hsq, herr, hsum⟩
  /- @proof-region region.target-node.session.c6260aa34094fb0f end -/
