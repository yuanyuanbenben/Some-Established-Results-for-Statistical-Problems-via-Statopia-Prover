import ProverJobs.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Vocabulary
import ProverJobs.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Base

namespace PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed

open _root_.PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open Statlib.StatFoundation.RandomVariable.Gaussian
open Statlib.StatFoundation.RandomVariable.Gaussian.Slepian

namespace Statlib.Imported
open _root_.Statlib
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
universe u₀ u₁

set_option autoImplicit false in
theorem statopia_math_node_2848356570_ec1c5090 : ∀ (p r : ℕ) (hp : 1 ≤ p) (hr : 1 ≤ r)
    (Q : Matrix (Fin p) (Fin r) ℝ) (hQ : Q.transpose * Q = 1)
    (Omega : Type) [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (G : Omega → Fin p → ℝ)
    (hG : Measurable G)
    (hGlaw : Measure.map G P = stdGaussianLaw p),
    Measure.map (fun om => Q.transpose.mulVec (G om)) P = stdGaussianLaw r := by
  /- @proof-region region.target-node.session.ce4ed42c03e62760 begin -/
  intro p r hp hr Q hQ Om mOm Pm hPm G hG hGlaw
  have hstdp : stdGaussianLaw p = standardPi p := rfl
  have hstdr : stdGaussianLaw r = standardPi r := rfl
  haveI hprobp : IsProbabilityMeasure (standardPi p) := standardPi_probability p
  haveI hprobr : IsProbabilityMeasure (standardPi r) := standardPi_probability r
  have hpsp : (1 : Matrix (Fin p) (Fin p) ℝ).PosSemidef := by
    first
      | exact Matrix.PosSemidef.one
      | exact Matrix.posSemidef_one
      | exact (Matrix.PosDef.one (n := Fin p)).posSemidef
  have hpsr : (1 : Matrix (Fin r) (Fin r) ℝ).PosSemidef := by
    first
      | exact Matrix.PosSemidef.one
      | exact Matrix.posSemidef_one
      | exact (Matrix.PosDef.one (n := Fin r)).posSemidef
  have hCGVp : IsCenteredGaussianVector (standardPi p) (id : (Fin p → ℝ) → Fin p → ℝ) (1 : Matrix (Fin p) (Fin p) ℝ) := by
    have h := canonicalGaussianVector_isCenteredGaussianVector (m := p) (by omega) (1 : Matrix (Fin p) (Fin p) ℝ) hpsp
    simpa [identity_canonicalGaussianVector p] using h
  have hCGVr : IsCenteredGaussianVector (standardPi r) (id : (Fin r → ℝ) → Fin r → ℝ) (1 : Matrix (Fin r) (Fin r) ℝ) := by
    have h := canonicalGaussianVector_isCenteredGaussianVector (m := r) (by omega) (1 : Matrix (Fin r) (Fin r) ℝ) hpsr
    simpa [identity_canonicalGaussianVector r] using h
  have hCGVX : IsCenteredGaussianVector (standardPi p) (fun z : Fin p → ℝ => Q.transpose.mulVec z) (1 : Matrix (Fin r) (Fin r) ℝ) := by
    have h := IsCenteredGaussianVector.linearImage (standardPi p) (id : (Fin p → ℝ) → Fin p → ℝ) (1 : Matrix (Fin p) (Fin p) ℝ) hCGVp (Q.transpose : Matrix (Fin r) (Fin p) ℝ)
    simpa [Matrix.transpose_transpose, hQ] using h
  have hXlaw : Measure.map (fun z : Fin p → ℝ => Q.transpose.mulVec z) (standardPi p) = standardPi r := by
    have h := map_eq_map_of_centeredGaussianVector (standardPi p) (standardPi r) (fun z : Fin p → ℝ => Q.transpose.mulVec z) (id : (Fin r → ℝ) → Fin r → ℝ) (1 : Matrix (Fin r) (Fin r) ℝ) hCGVX hCGVr hpsr
    simpa [Measure.map_id] using h
  have hmeas : Measurable (fun z : Fin p → ℝ => Q.transpose.mulVec z) := by
    rw [measurable_pi_iff]
    intro i
    have h1 : (fun z : Fin p → ℝ => (Q.transpose.mulVec z) i) = fun z => ∑ j, Q.transpose i j * z j := rfl
    rw [h1]
    exact Finset.measurable_sum _ (fun j _ => measurable_const.mul (measurable_pi_apply j))
  have hGlaw' : Measure.map G Pm = standardPi p := by rw [hGlaw, hstdp]
  have hcomp : Measure.map (fun z : Fin p → ℝ => Q.transpose.mulVec z) (Measure.map G Pm) = Measure.map ((fun z : Fin p → ℝ => Q.transpose.mulVec z) ∘ G) Pm := Measure.map_map (μ := Pm) hmeas hG
  rw [hGlaw'] at hcomp
  have hstep : Measure.map (fun om => Q.transpose.mulVec (G om)) Pm = Measure.map (fun z : Fin p → ℝ => Q.transpose.mulVec z) (standardPi p) := hcomp.symm
  exact hstep.trans (hXlaw.trans hstdr.symm)
  /- @proof-region region.target-node.session.ce4ed42c03e62760 end -/

end
end Statlib.Imported

