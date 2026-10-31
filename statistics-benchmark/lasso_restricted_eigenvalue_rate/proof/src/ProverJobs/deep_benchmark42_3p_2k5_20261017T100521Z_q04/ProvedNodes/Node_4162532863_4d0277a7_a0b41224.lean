import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q04.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q04.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q04.ProvedNodes.Node_136849786_51737db8_33a7f3f1

open MeasureTheory ProbabilityTheory
open Msc62GroundTruth

open MeasureTheory ProbabilityTheory
namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_4162532863_4d0277a7 : ∀ {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (m : ℕ) (epsilon : Fin m → Omega → ℝ) (sigma : ℝ) (hsigma : 0 ≤ sigma)
    (h_epsilon_meas : ∀ i : Fin m, Measurable (epsilon i))
    (h_epsilon_indep : iIndepFun (β := fun _ : Fin m => ℝ) epsilon P)
    (h_exp_integrable : ∀ (i : Fin m) (t : ℝ),
      Integrable (fun omega => Real.exp (t * epsilon i omega)) P)
    (h_mgf_le : ∀ (i : Fin m) (t : ℝ),
      ∫ omega, Real.exp (t * epsilon i omega) ∂P ≤ Real.exp (sigma * t ^ 2 / 2)),
    ∀ (a : Fin m → ℝ) (t : ℝ),
      Integrable
          (fun omega => Real.exp (t * ∑ i : Fin m, a i * epsilon i omega)) P ∧
        ∫ omega, Real.exp (t * ∑ i : Fin m, a i * epsilon i omega) ∂P ≤
          Real.exp ((sigma * ∑ i : Fin m, (a i) ^ 2) * t ^ 2 / 2) := by
  /- @proof-region region.target-node.session.2030a68cc7006f50 begin -/
  intro Omega instOmega P instP m epsilon sigma hsigma h_epsilon_meas h_epsilon_indep
    h_exp_integrable h_mgf_le a t
  have hcoord : ∀ i : Fin m, HasSubgaussianMGF (epsilon i) (⟨sigma, hsigma⟩ : NNReal) P :=
    fun i =>
      (statopia_math_node_136849786_51737db8 P m epsilon sigma hsigma h_exp_integrable h_mgf_le i).1
  have hindep : iIndepFun (fun i : Fin m => fun omega => a i * epsilon i omega) P :=
    h_epsilon_indep.comp (g := fun i (x : ℝ) => a i * x)
      (fun i => (measurable_const : Measurable (fun _ : ℝ => a i)).mul measurable_id)
  have hscaled : ∀ i : Fin m,
      HasSubgaussianMGF (fun omega => a i * epsilon i omega)
        (⟨(a i) ^ 2, sq_nonneg (a i)⟩ * ⟨sigma, hsigma⟩) P :=
    fun i => (hcoord i).const_mul (a i)
  have hsum : HasSubgaussianMGF (fun omega => ∑ i : Fin m, a i * epsilon i omega)
      (∑ i : Fin m, (⟨(a i) ^ 2, sq_nonneg (a i)⟩ * ⟨sigma, hsigma⟩ : NNReal)) P :=
    HasSubgaussianMGF.sum_of_iIndepFun (s := Finset.univ)
      (c := fun i : Fin m => ⟨(a i) ^ 2, sq_nonneg (a i)⟩ * ⟨sigma, hsigma⟩) hindep
      (fun i _ => hscaled i)
  have hcoec : ∑ i : Fin m, (a i) ^ 2 * sigma = sigma * ∑ i : Fin m, (a i) ^ 2 := by
    rw [← Finset.sum_mul]
    ring
  refine ⟨hsum.1 t, ?_⟩
  have h := hsum.2 t
  simp only [mgf] at h
  push_cast at h
  rw [hcoec] at h
  exact h
  /- @proof-region region.target-node.session.2030a68cc7006f50 end -/

end Msc62GroundTruth
