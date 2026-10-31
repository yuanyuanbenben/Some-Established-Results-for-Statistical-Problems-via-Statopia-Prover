import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_68f77b4042a84f6999315e1f7b578de2.Vocabulary
import ProverJobs.job_paper_68f77b4042a84f6999315e1f7b578de2.Base
import ProverJobs.job_paper_68f77b4042a84f6999315e1f7b578de2.ProvedNodes.Node_1852335189_c4ea2480_2e9cbbf1
import ProverJobs.job_paper_68f77b4042a84f6999315e1f7b578de2.ProvedNodes.Node_3150113155_06872c0c_496d4291

namespace PaperProofTasks.job_paper_68f77b4042a84f6999315e1f7b578de2


open _root_.PaperProofTasks.job_paper_68f77b4042a84f6999315e1f7b578de2.Statlib.Imported
open scoped BigOperators

namespace Statlib.Imported

open scoped BigOperators

set_option autoImplicit false in
theorem statopia_math_node_1897111600_7bb83d4b : ∀ (p : ℕ) (hp : 0 < p) (β : ℝ) (hβ : 0 < β)
    (z : Fin p → ℝ) (k : Fin p),
      let S : (Fin p → ℝ) → ℝ := fun v => ∑ m : Fin p, Real.exp (β * v m); let projk : (Fin p → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin p => ℝ) k; let D : (Fin p → ℝ) →L[ℝ] ℝ := ∑ m : Fin p, (β * Real.exp (β * z m)) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin p => ℝ) m); let L : (Fin p → ℝ) →L[ℝ] ℝ := Real.exp (β * z k) • ((-(((S z) ^ 2)⁻¹)) • D) + (S z)⁻¹ • (Real.exp (β * z k) • (β • projk)); HasFDerivAt (fun v : Fin p → ℝ => softmaxWt β v k) L z ∧ (∀ j : Fin p, L (Pi.single j (1 : ℝ)) = β * ((if j = k then (1 : ℝ) else 0) * softmaxWt β z j - softmaxWt β z j * softmaxWt β z k)) ∧ (∀ j : Fin p, L (Pi.single j (1 : ℝ)) = β * wMatEntry β z j k) := by
  /- @proof-region region.target-node.session.3fa7ea28bc480a64 begin -/
  intro p hp β hβ z k
  let S : (Fin p → ℝ) → ℝ := fun v => ∑ m : Fin p, Real.exp (β * v m)
  let projk : (Fin p → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin p => ℝ) k
  let D : (Fin p → ℝ) →L[ℝ] ℝ := ∑ m : Fin p, (β * Real.exp (β * z m)) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin p => ℝ) m)
  let L : (Fin p → ℝ) →L[ℝ] ℝ := Real.exp (β * z k) • ((-(((S z) ^ 2)⁻¹)) • D) + (S z)⁻¹ • (Real.exp (β * z k) • (β • projk))
  change HasFDerivAt (fun v : Fin p → ℝ => softmaxWt β v k) L z ∧
    (∀ j : Fin p, L (Pi.single j (1 : ℝ)) = β * ((if j = k then (1 : ℝ) else 0) * softmaxWt β z j - softmaxWt β z j * softmaxWt β z k)) ∧
    (∀ j : Fin p, L (Pi.single j (1 : ℝ)) = β * wMatEntry β z j k)
  obtain ⟨hSderiv, hDeval⟩ := statopia_math_node_3150113155_06872c0c p hp β hβ z
  obtain ⟨hSpos, -, -⟩ := statopia_math_node_1852335189_c4ea2480 p hp β hβ z
  have hSne : S z ≠ 0 := ne_of_gt hSpos
  have hlin : HasFDerivAt (fun v : Fin p → ℝ => β * v k) (β • projk) z := by
    have h := ContinuousLinearMap.hasFDerivAt (β • projk) (x := z)
    simpa [projk, ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply] using h
  have hnum : HasFDerivAt (fun v : Fin p → ℝ => Real.exp (β * v k)) (Real.exp (β * z k) • (β • projk)) z := by
    have h := (Real.hasDerivAt_exp ((β • projk) z)).comp_hasFDerivAt z hlin
    simpa [projk, ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply] using h
  have hrec : HasFDerivAt (fun v : Fin p → ℝ => (S v)⁻¹) ((-(((S z) ^ 2)⁻¹)) • D) z := by
    have h := (hasFDerivAt_inv hSne).comp z hSderiv
    have hcomp_eq : (ContinuousLinearMap.toSpanSingleton ℝ (-(((S z) ^ 2)⁻¹))).comp D = (-(((S z) ^ 2)⁻¹)) • D := by
      ext v
      simp [ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.smul_apply, mul_comm]
    simpa [S, D, hcomp_eq] using h
  have hprod := hnum.mul hrec
  have hfirst : HasFDerivAt (fun v : Fin p → ℝ => softmaxWt β v k) L z := by
    simpa [L, softmaxWt, div_eq_mul_inv, S] using hprod
  have hL_apply (j : Fin p) :
      L (Pi.single j (1 : ℝ)) =
        Real.exp (β * z k) * (-(((S z) ^ 2)⁻¹)) * (β * Real.exp (β * z j)) +
          (S z)⁻¹ * (Real.exp (β * z k) * (β * ((Pi.single j (1 : ℝ) : Fin p → ℝ) k))) := by
    simp [L, D, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, projk,
      ContinuousLinearMap.proj_apply, hDeval j]
    ring
  have hsingle (j : Fin p) : (Pi.single j (1 : ℝ) : Fin p → ℝ) k = if j = k then (1 : ℝ) else 0 := by
    by_cases h : j = k
    · subst h
      simp
    · have hk : ¬ k = j := fun hk => h hk.symm
      simp [h, hk]
  have hL_apply_soft (j : Fin p) :
      L (Pi.single j (1 : ℝ)) =
        β * ((if j = k then (1 : ℝ) else 0) * softmaxWt β z k - softmaxWt β z j * softmaxWt β z k) := by
    rw [hL_apply j, hsingle j]
    have hpi_j : softmaxWt β z j = Real.exp (β * z j) / S z := by simp [softmaxWt, S]
    have hpi_k : softmaxWt β z k = Real.exp (β * z k) / S z := by simp [softmaxWt, S]
    rw [hpi_j, hpi_k]
    field_simp [hSne]
    ring
  have hsecond : ∀ j : Fin p, L (Pi.single j (1 : ℝ)) = β * ((if j = k then (1 : ℝ) else 0) * softmaxWt β z j - softmaxWt β z j * softmaxWt β z k) := by
    intro j
    rw [hL_apply_soft j]
    by_cases hjk : j = k
    · subst hjk
      ring
    · simp [hjk] <;> ring
  refine ⟨hfirst, hsecond, ?_⟩
  intro j
  rw [hsecond j]
  simp [wMatEntry]
  /- @proof-region region.target-node.session.3fa7ea28bc480a64 end -/

end Statlib.Imported

