import ProverJobs.job_paper_df5fdc450bf24d85b08215e07b20fdad.Vocabulary
import ProverJobs.job_paper_df5fdc450bf24d85b08215e07b20fdad.Base
import ProverJobs.job_paper_df5fdc450bf24d85b08215e07b20fdad.ProvedNodes.Node_2137929089_5f7d7f94_6371220c

namespace PaperProofTasks.job_paper_df5fdc450bf24d85b08215e07b20fdad

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators
open _root_.PaperProofTasks.job_paper_df5fdc450bf24d85b08215e07b20fdad.Statlib.Imported

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators
namespace Statlib.Imported


set_option autoImplicit false in
theorem statopia_math_node_2343580459_835d00e9 : ∃ K : ℝ, 0 < K ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ (Ω : Type*) [MeasurableSpace Ω] (p : ℕ → ℕ)
        (X : (n : ℕ) → Fin n → Ω → (Fin (p n) → ℝ)) (ω : Ω) (j : Fin (p n))
        (q : ℝ), 2 ≤ q →
        ∀ (ν : Measure (Fin (p n) → ℝ)),
          IsCenteredGaussianCov ν (SigmaHat p X n ω) →
            LqNorm (fun s : Fin (p n) → ℝ =>
                if sigmaHatOf p X n ω j = 0 then (0 : ℝ)
                else (sigmaHatOf p X n ω j)⁻¹ * s j) q ν
              ≤ ENNReal.ofReal (K * q) := by
  /- @proof-region region.target-node.session.ec1ff69896736908 begin -/
  obtain ⟨K, hKpos, hK⟩ := statopia_math_node_2137929089_5f7d7f94
  refine ⟨K, hKpos, ?_⟩
  intro n hn Ω inst p X ω j q hq ν hcov
  set σ := sigmaHatOf p X n ω j with hσdef
  have hA : 0 ≤ SigmaHat p X n ω j j := by
    simp only [SigmaHat, Matrix.of_apply]
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
      (Finset.sum_nonneg (fun i _ => mul_self_nonneg _))
  by_cases hσ : σ = 0
  · have hzero : (fun s : Fin (p n) → ℝ => if σ = 0 then 0 else σ⁻¹ * s j)
        = fun _ => (0:ℝ) := by
      funext s
      rw [if_pos hσ]
    rw [hzero]
    have hqpos : (0:ℝ) < q := lt_of_lt_of_le two_pos hq
    have hq0 : q ≠ 0 := ne_of_gt hqpos
    have hL : LqNorm (fun _ : Fin (p n) → ℝ => (0:ℝ)) q ν = 0 := by
      simp only [LqNorm, abs_zero, Real.zero_rpow hq0, ENNReal.ofReal_zero, lintegral_zero]
      exact ENNReal.zero_rpow_of_pos (one_div_pos.mpr hqpos)
    rw [hL]
    exact zero_le _
  · have hfun : (fun s : Fin (p n) → ℝ => if σ = 0 then 0 else σ⁻¹ * s j)
        = fun s => σ⁻¹ * s j := by
      funext s
      rw [if_neg hσ]
    rw [hfun]
    have hσsq : σ ^ 2 = SigmaHat p X n ω j j := by
      rw [hσdef, sigmaHatOf]
      exact Real.sq_sqrt hA
    set u : Fin (p n) → ℝ := (fun l => if l = j then (1:ℝ) else 0) with hudef
    have hsum1 : ∀ s : Fin (p n) → ℝ, (∑ l, u l * s l) = s j := by
      intro s
      have hc : (fun l : Fin (p n) => u l * s l) = fun l => if l = j then s l else 0 := by
        funext l
        by_cases hl : l = j
        · simp [hudef, hl]
        · simp [hudef, hl]
      rw [hc]
      simp
    have hquad : (∑ i, ∑ l, u i * SigmaHat p X n ω i l * u l)
        = SigmaHat p X n ω j j := by
      have hinner : ∀ i : Fin (p n), (∑ l, u i * SigmaHat p X n ω i l * u l)
          = u i * SigmaHat p X n ω i j := by
        intro i
        have hc : (fun l : Fin (p n) => u i * SigmaHat p X n ω i l * u l)
            = fun l => if l = j then u i * SigmaHat p X n ω i l else 0 := by
          funext l
          by_cases hl : l = j
          · simp [hudef, hl]
          · simp [hudef, hl]
        rw [hc]
        simp
      simp only [hinner]
      have hc2 : (fun i : Fin (p n) => u i * SigmaHat p X n ω i j)
          = fun i => if i = j then SigmaHat p X n ω i j else 0 := by
        funext i
        by_cases hi : i = j
        · simp [hudef, hi]
        · simp [hudef, hi]
      rw [hc2]
      simp
    have hlin : Measure.map (fun s : Fin (p n) → ℝ => s j) ν
        = gaussianReal 0 (Real.toNNReal (SigmaHat p X n ω j j)) := by
      have h := hcov.2 u
      have hfun2 : (fun s : Fin (p n) → ℝ => ∑ l, u l * s l) = fun s => s j := funext hsum1
      rw [hfun2, hquad] at h
      exact h
    have hscale : Measure.map (fun x : ℝ => σ⁻¹ * x)
        (gaussianReal 0 (Real.toNNReal (SigmaHat p X n ω j j))) = gaussianReal 0 1 := by
      rw [ProbabilityTheory.gaussianReal_map_const_mul]
      rw [mul_zero]
      refine congrArg (fun v : NNReal => gaussianReal (0:ℝ) v) ?_
      refine NNReal.coe_injective ?_
      rw [NNReal.coe_mul, NNReal.coe_one, Real.coe_toNNReal _ hA]
      show (σ⁻¹)^2 * SigmaHat p X n ω j j = 1
      rw [← hσsq]
      rw [← mul_pow, inv_mul_cancel₀ hσ]
      simp
    have hmeasj : Measurable (fun s : Fin (p n) → ℝ => s j) := measurable_pi_apply j
    have hmeasc : Measurable (fun x : ℝ => σ⁻¹ * x) :=
      (continuous_const (y := σ⁻¹)).mul continuous_id |>.measurable
    have hmap : Measure.map (fun s : Fin (p n) → ℝ => σ⁻¹ * s j) ν = gaussianReal 0 1 := by
      have hcomp : (fun s : Fin (p n) → ℝ => σ⁻¹ * s j)
          = (fun x : ℝ => σ⁻¹ * x) ∘ (fun s : Fin (p n) → ℝ => s j) := rfl
      rw [hcomp]
      rw [← MeasureTheory.Measure.map_map hmeasc hmeasj]
      rw [hlin, hscale]
    have hf_meas : Measurable (fun x : ℝ => ENNReal.ofReal (|x| ^ q)) := by
      measurability
    have hgj_meas : Measurable (fun s : Fin (p n) → ℝ => σ⁻¹ * s j) := hmeasc.comp hmeasj
    have hlim : (∫⁻ s : Fin (p n) → ℝ, ENNReal.ofReal (|σ⁻¹ * s j| ^ q) ∂ν)
        = ∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ q) ∂gaussianReal 0 1 := by
      rw [← hmap]
      rw [MeasureTheory.lintegral_map hf_meas hgj_meas]
    have hstep : LqNorm (fun s : Fin (p n) → ℝ => σ⁻¹ * s j) q ν
        = LqNorm (fun x : ℝ => x) q (gaussianReal 0 1) := by
      simp only [LqNorm]
      simp only [hlim]
    calc LqNorm (fun s : Fin (p n) → ℝ => σ⁻¹ * s j) q ν
        = LqNorm (fun x : ℝ => x) q (gaussianReal 0 1) := hstep
      _ ≤ ENNReal.ofReal (K * q) := hK q (le_trans one_le_two hq)
  /- @proof-region region.target-node.session.ec1ff69896736908 end -/

end Statlib.Imported

