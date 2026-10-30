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
theorem statopia_math_node_3022661809_54b8f404 : ∃ K : ℝ, 0 < K ∧
      ∀ (n : ℕ) (hn : 1 ≤ n) (Ω : Type*) [MeasurableSpace Ω] (p : ℕ → ℕ)
        (X : (m : ℕ) → Fin m → Ω → (Fin (p m) → ℝ)) (ω : Ω) (j : Fin (p n))
        (alpha : ℝ) (tau : ℕ → ℝ) (ν : Measure (Fin (p n) → ℝ)),
        IsCenteredGaussianCov ν (SigmaHat p X n ω) →
          LqNorm (fun s : Fin (p n) → ℝ =>
              if sigmaHatOf p X n ω j = 0 then 0
              else (sigmaHatOf p X n ω j)⁻¹ * s j)
            (qN alpha tau n) ν
          ≤ ENNReal.ofReal (K * qN alpha tau n) := by
  /- @proof-region region.target-node.session.fce96561ccf516b5 begin -/
  obtain ⟨K, hKpos, hK⟩ := statopia_math_node_2137929089_5f7d7f94
  refine ⟨K, hKpos, ?_⟩
  intro n hn Ω _ p X ω j alpha tau ν hν
  set q := qN alpha tau n with hqdef
  have hq3 : (3:ℝ) ≤ q := by rw [hqdef]; exact le_max_right _ _
  have hq1 : (1:ℝ) ≤ q := le_trans (by norm_num) hq3
  have hqpos : (0:ℝ) < q := lt_of_lt_of_le (by norm_num) hq3
  have hfun : (fun s : Fin (p n) → ℝ =>
      if sigmaHatOf p X n ω j = 0 then 0 else (sigmaHatOf p X n ω j)⁻¹ * s j)
      = (fun s : Fin (p n) → ℝ => (sigmaHatOf p X n ω j)⁻¹ * s j) := by
    funext s
    by_cases h : sigmaHatOf p X n ω j = 0
    · simp [h]
    · simp [h]
  rw [hfun]
  by_cases hσ : sigmaHatOf p X n ω j = 0
  · have hz : (fun s : Fin (p n) → ℝ => (sigmaHatOf p X n ω j)⁻¹ * s j) = fun _ => 0 := by
      funext s; simp [hσ]
    rw [hz]
    have hlq0 : LqNorm (fun _ : Fin (p n) → ℝ => (0:ℝ)) q ν = 0 := by
      unfold LqNorm
      have h1 : (∫⁻ ω : Fin (p n) → ℝ, ENNReal.ofReal (|(fun _ => (0:ℝ)) ω| ^ q) ∂ν) = 0 := by
        simp [Real.zero_rpow (ne_of_gt hqpos)]
      rw [h1]
      exact ENNReal.zero_rpow_of_pos (one_div_pos.mpr hqpos)
    rw [hlq0]
    exact zero_le (ENNReal.ofReal (K * q))
  · have hσpos : 0 < sigmaHatOf p X n ω j := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hσ)
    have hA : (0:ℝ) ≤ SigmaHat p X n ω j j := by
      simp only [SigmaHat, Matrix.of_apply]
      apply mul_nonneg
      · exact inv_nonneg.mpr (Nat.cast_nonneg n)
      · exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    have hσsq : (sigmaHatOf p X n ω j)^2 = SigmaHat p X n ω j j := by
      rw [sigmaHatOf, Real.sq_sqrt hA]
    have hlin : (fun s : Fin (p n) → ℝ => ∑ j', (if j' = j then (1:ℝ) else 0) * s j')
        = (fun s => s j) := by
      funext s
      have h := Finset.sum_eq_single (s := Finset.univ) j
        (f := fun b => (if b = j then (1:ℝ) else 0) * s b)
        (fun b _ hb => by simp [hb]) (fun hh => absurd (Finset.mem_univ j) hh)
      simpa using h
    have hbilin : (∑ i, ∑ j', (if i = j then (1:ℝ) else 0) * SigmaHat p X n ω i j' * (if j' = j then (1:ℝ) else 0))
        = SigmaHat p X n ω j j := by
      have hinner : ∀ i, (∑ j', (if i = j then (1:ℝ) else 0) * SigmaHat p X n ω i j' * (if j' = j then (1:ℝ) else 0))
          = (if i = j then (1:ℝ) else 0) * SigmaHat p X n ω i j := by
        intro i
        have h := Finset.sum_eq_single (s := Finset.univ) j
          (f := fun b => (if i = j then (1:ℝ) else 0) * SigmaHat p X n ω i b * (if b = j then (1:ℝ) else 0))
          (fun b _ hb => by simp [hb]) (fun hh => absurd (Finset.mem_univ j) hh)
        simpa using h
      calc (∑ i, ∑ j', (if i = j then (1:ℝ) else 0) * SigmaHat p X n ω i j' * (if j' = j then (1:ℝ) else 0))
          = ∑ i, (if i = j then (1:ℝ) else 0) * SigmaHat p X n ω i j := by
            apply Finset.sum_congr rfl; intro i _; exact hinner i
        _ = SigmaHat p X n ω j j := by
            have h := Finset.sum_eq_single (s := Finset.univ) j
              (f := fun b => (if b = j then (1:ℝ) else 0) * SigmaHat p X n ω b j)
              (fun b _ hb => by simp [hb]) (fun hh => absurd (Finset.mem_univ j) hh)
            simpa using h
    have hcov : Measure.map (fun s : Fin (p n) → ℝ => s j) ν
        = gaussianReal 0 (Real.toNNReal (SigmaHat p X n ω j j)) := by
      have h := hν.2 (fun i : Fin (p n) => if i = j then (1:ℝ) else 0)
      simp only [hlin] at h
      simp only [hbilin] at h
      exact h
    have hmap : Measure.map (fun s : Fin (p n) → ℝ => (sigmaHatOf p X n ω j)⁻¹ * s j) ν
        = gaussianReal 0 (1 : NNReal) := by
      have hAne : SigmaHat p X n ω j j ≠ 0 := by
        rw [← hσsq]; exact pow_ne_zero 2 (ne_of_gt hσpos)
      have hcoef : (sigmaHatOf p X n ω j)⁻¹ ^ 2 * SigmaHat p X n ω j j = 1 := by
        rw [inv_pow, hσsq]
        exact inv_mul_cancel₀ hAne
      have hgauss : Measure.map (fun x : ℝ => (sigmaHatOf p X n ω j)⁻¹ * x)
          (gaussianReal 0 (Real.toNNReal (SigmaHat p X n ω j j))) = gaussianReal 0 (1 : NNReal) := by
        rw [ProbabilityTheory.gaussianReal_map_const_mul]
        simp only [mul_zero]
        congr 1
        rw [Real.toNNReal_of_nonneg hA]
        apply NNReal.coe_injective
        simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one]
        exact hcoef
      have hg_meas : Measurable (fun x : ℝ => (sigmaHatOf p X n ω j)⁻¹ * x) := by fun_prop
      have hf_meas : Measurable (fun s : Fin (p n) → ℝ => s j) := by fun_prop
      calc Measure.map (fun s : Fin (p n) → ℝ => (sigmaHatOf p X n ω j)⁻¹ * s j) ν
          = Measure.map ((fun x : ℝ => (sigmaHatOf p X n ω j)⁻¹ * x) ∘ (fun s : Fin (p n) → ℝ => s j)) ν := rfl
        _ = Measure.map (fun x : ℝ => (sigmaHatOf p X n ω j)⁻¹ * x) (Measure.map (fun s : Fin (p n) → ℝ => s j) ν) := by
              exact (MeasureTheory.Measure.map_map (g := fun x : ℝ => (sigmaHatOf p X n ω j)⁻¹ * x) (f := fun s : Fin (p n) → ℝ => s j) (μ := ν) hg_meas hf_meas).symm
        _ = Measure.map (fun x : ℝ => (sigmaHatOf p X n ω j)⁻¹ * x) (gaussianReal 0 (Real.toNNReal (SigmaHat p X n ω j j))) := by rw [hcov]
        _ = gaussianReal 0 (1 : NNReal) := hgauss
    have hlq : LqNorm (fun s : Fin (p n) → ℝ => (sigmaHatOf p X n ω j)⁻¹ * s j) q ν
        = LqNorm (fun x : ℝ => x) q (gaussianReal 0 (1 : NNReal)) := by
      have hcv : LqNorm (fun s : Fin (p n) → ℝ => (sigmaHatOf p X n ω j)⁻¹ * s j) q ν
          = LqNorm (fun x : ℝ => x) q (Measure.map (fun s : Fin (p n) → ℝ => (sigmaHatOf p X n ω j)⁻¹ * s j) ν) := by
        have hF : Measurable (fun a : ℝ => ENNReal.ofReal (|a| ^ q)) := by fun_prop
        have hG : Measurable (fun s : Fin (p n) → ℝ => (sigmaHatOf p X n ω j)⁻¹ * s j) := by fun_prop
        have hint : (∫⁻ a : Fin (p n) → ℝ, ENNReal.ofReal (|(sigmaHatOf p X n ω j)⁻¹ * a j| ^ q) ∂ν)
            = (∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ q) ∂Measure.map (fun s : Fin (p n) → ℝ => (sigmaHatOf p X n ω j)⁻¹ * s j) ν) :=
          (MeasureTheory.lintegral_map (f := fun x : ℝ => ENNReal.ofReal (|x| ^ q))
            (g := fun s : Fin (p n) → ℝ => (sigmaHatOf p X n ω j)⁻¹ * s j) (μ := ν) hF hG).symm
        simp only [LqNorm]
        rw [hint]
      rw [hmap] at hcv
      exact hcv
    rw [hlq]
    exact hK q hq1
  /- @proof-region region.target-node.session.fce96561ccf516b5 end -/

end Statlib.Imported

