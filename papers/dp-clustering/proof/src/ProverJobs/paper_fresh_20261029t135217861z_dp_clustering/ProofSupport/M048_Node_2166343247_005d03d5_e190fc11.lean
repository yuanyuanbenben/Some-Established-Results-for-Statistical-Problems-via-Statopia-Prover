import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M031_Vocabulary
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M032_Base

/- Original module ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_2166343247_005d03d5_e190fc11; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported

open MeasureTheory
open Statlib.Imported

noncomputable section
open MeasureTheory
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_2166343247_005d03d5 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (f g : Ω → ℝ)
    (hf_nonneg : 0 ≤ f) (hg_nonneg : 0 ≤ g)
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_int : Integrable f μ) (hg_int : Integrable g μ)
    (hfg_int : Integrable (fun x => f x * g x) μ)
    (hanti : ∀ᵐ p ∂(μ.prod μ), (f p.1 - f p.2) * (g p.1 - g p.2) ≤ 0),
    (μ Set.univ).toReal * ∫ x, f x * g x ∂μ ≤ (∫ x, f x ∂μ) * (∫ x, g x ∂μ) := by
  /- @proof-region region.target-node.session.e0dac3393ffa093d begin -/
  intro Ω _ μ _ f g hf_nonneg hg_nonneg hf_meas hg_meas hf_int hg_int hfg_int h_mono
  set m : ℝ := (μ Set.univ).toReal with hm
  set A : ℝ := ∫ x, f x ∂μ with hA
  set B : ℝ := ∫ x, g x ∂μ with hB
  set C : ℝ := ∫ x, f x * g x ∂μ with hC
  have hH_le : ∫ p : Ω × Ω, (f p.1 - f p.2) * (g p.1 - g p.2) ∂(μ.prod μ) ≤ 0 :=
    MeasureTheory.integral_nonpos_of_ae h_mono
  have hT1 : Integrable (fun p : Ω × Ω => f p.1 * g p.1) (μ.prod μ) := hfg_int.comp_fst μ
  have hT2 : Integrable (fun p : Ω × Ω => f p.2 * g p.2) (μ.prod μ) := hfg_int.comp_snd μ
  have hT3 : Integrable (fun p : Ω × Ω => f p.1 * g p.2) (μ.prod μ) := hf_int.mul_prod hg_int
  have hT4 : Integrable (fun p : Ω × Ω => g p.1 * f p.2) (μ.prod μ) := hg_int.mul_prod hf_int
  have hV1 : ∫ p : Ω × Ω, f p.1 * g p.1 ∂(μ.prod μ) = m * C := by
    rw [MeasureTheory.integral_prod (fun p : Ω × Ω => f p.1 * g p.1) hT1]
    have hinner : ∀ x : Ω, (∫ y : Ω, (fun p : Ω × Ω => f p.1 * g p.1) (x, y) ∂μ)
        = (μ Set.univ).toReal * (f x * g x) := by
      intro x
      show (∫ y : Ω, f x * g x ∂μ) = (μ Set.univ).toReal * (f x * g x)
      rw [MeasureTheory.integral_const]
      rfl
    simp only [hinner, MeasureTheory.integral_const_mul, ← hC, ← hm]
  have hV2 : ∫ p : Ω × Ω, f p.2 * g p.2 ∂(μ.prod μ) = m * C := by
    have hswap : ∫ p : Ω × Ω, f p.2 * g p.2 ∂(μ.prod μ)
        = ∫ p : Ω × Ω, f p.1 * g p.1 ∂(μ.prod μ) := by
      have key := MeasureTheory.integral_prod_swap (fun p : Ω × Ω => f p.1 * g p.1) (μ := μ) (ν := μ)
      simpa using key
    rw [hswap, hV1]
  have hV3 : ∫ p : Ω × Ω, f p.1 * g p.2 ∂(μ.prod μ) = A * B := by
    rw [MeasureTheory.integral_prod_mul f g, ← hA, ← hB]
  have hV4 : ∫ p : Ω × Ω, g p.1 * f p.2 ∂(μ.prod μ) = A * B := by
    rw [MeasureTheory.integral_prod_mul g f, ← hB, ← hA]
    ring
  have hHval : ∫ p : Ω × Ω, (f p.1 - f p.2) * (g p.1 - g p.2) ∂(μ.prod μ)
      = 2 * (m * C - A * B) := by
    have hP : Integrable (fun p : Ω × Ω => f p.1 * g p.1 - f p.1 * g p.2) (μ.prod μ) :=
      hT1.sub hT3
    have hQ : Integrable (fun p : Ω × Ω => f p.2 * g p.2 - g p.1 * f p.2) (μ.prod μ) :=
      hT2.sub hT4
    have e1 : ∫ p : Ω × Ω, (f p.1 - f p.2) * (g p.1 - g p.2) ∂(μ.prod μ)
        = ∫ p : Ω × Ω, (fun p => f p.1 * g p.1 - f p.1 * g p.2) p
            + (fun p => f p.2 * g p.2 - g p.1 * f p.2) p ∂(μ.prod μ) := by
      have hpt : ∀ p : Ω × Ω, (f p.1 - f p.2) * (g p.1 - g p.2)
          = (fun p => f p.1 * g p.1 - f p.1 * g p.2) p
            + (fun p => f p.2 * g p.2 - g p.1 * f p.2) p := by
        intro p
        show (f p.1 - f p.2) * (g p.1 - g p.2)
            = (f p.1 * g p.1 - f p.1 * g p.2) + (f p.2 * g p.2 - g p.1 * f p.2)
        ring
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
    have e2 : ∫ p : Ω × Ω, (fun p => f p.1 * g p.1 - f p.1 * g p.2) p
            + (fun p => f p.2 * g p.2 - g p.1 * f p.2) p ∂(μ.prod μ)
        = ∫ p : Ω × Ω, (fun p => f p.1 * g p.1 - f p.1 * g p.2) p ∂(μ.prod μ)
          + ∫ p : Ω × Ω, (fun p => f p.2 * g p.2 - g p.1 * f p.2) p ∂(μ.prod μ) :=
      MeasureTheory.integral_add hP hQ
    have e3 : ∫ p : Ω × Ω, (fun p => f p.1 * g p.1 - f p.1 * g p.2) p ∂(μ.prod μ)
        = m * C - A * B := by
      have hsub : ∫ p : Ω × Ω, (f p.1 * g p.1 - f p.1 * g p.2) ∂(μ.prod μ) = m * C - A * B := by
        rw [MeasureTheory.integral_sub hT1 hT3, hV1, hV3]
      exact hsub
    have e4 : ∫ p : Ω × Ω, (fun p => f p.2 * g p.2 - g p.1 * f p.2) p ∂(μ.prod μ)
        = m * C - A * B := by
      have hsub : ∫ p : Ω × Ω, (f p.2 * g p.2 - g p.1 * f p.2) ∂(μ.prod μ) = m * C - A * B := by
        rw [MeasureTheory.integral_sub hT2 hT4, hV2, hV4]
      exact hsub
    rw [e1, e2, e3, e4]
    ring
  have h2 : 2 * (m * C - A * B) ≤ 0 := by rw [← hHval]; exact hH_le
  have key : ∀ x y : ℝ, 2 * (x - y) ≤ 0 → x ≤ y := by
    intro x y hxy
    linarith
  exact key (m * C) (A * B) h2
  /- @proof-region region.target-node.session.e0dac3393ffa093d end -/

end Statlib.Imported
end
end DPCompletedProof
