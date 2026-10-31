import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q04.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q04.Base

open MeasureTheory ProbabilityTheory
open Msc62GroundTruth

open MeasureTheory ProbabilityTheory
namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_136849786_51737db8 : ∀ {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (m : ℕ) (epsilon : Fin m → Omega → ℝ) (sigma : ℝ) (hsigma : 0 ≤ sigma)
    (h_exp_integrable : ∀ (i : Fin m) (t : ℝ),
      Integrable (fun omega => Real.exp (t * epsilon i omega)) P)
    (h_mgf_le : ∀ (i : Fin m) (t : ℝ),
      ∫ omega, Real.exp (t * epsilon i omega) ∂P ≤ Real.exp (sigma * t ^ 2 / 2)),
    ∀ i : Fin m,
      HasSubgaussianMGF (epsilon i) (⟨sigma, hsigma⟩ : NNReal) P ∧
        ∀ t : ℝ, Integrable (fun omega => Real.exp (t * epsilon i omega)) P := by
  /- @proof-region region.target-node.session.9933ec60029f095c begin -/
  refine fun {Omega} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (m : ℕ) (epsilon : Fin m → Omega → ℝ) (sigma : ℝ) (hsigma : 0 ≤ sigma)
    (h_exp_integrable : ∀ (i : Fin m) (t : ℝ),
      Integrable (fun omega => Real.exp (t * epsilon i omega)) P)
    (h_mgf_le : ∀ (i : Fin m) (t : ℝ),
      ∫ omega, Real.exp (t * epsilon i omega) ∂P ≤ Real.exp (sigma * t ^ 2 / 2))
    (i : Fin m) => ?_
  refine ⟨⟨h_exp_integrable i, ?_⟩, h_exp_integrable i⟩
  intro t
  simpa [ProbabilityTheory.mgf, NNReal.coe_mk] using h_mgf_le i t
  /- @proof-region region.target-node.session.9933ec60029f095c end -/

end Msc62GroundTruth
