import ProverJobs.job_paper_d731a49b3997405b944f72bca5b16eab.Vocabulary
import ProverJobs.job_paper_d731a49b3997405b944f72bca5b16eab.ProvedNodes
import ProverJobs.job_paper_d731a49b3997405b944f72bca5b16eab.Base

namespace PaperProofTasks.job_paper_d731a49b3997405b944f72bca5b16eab

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace Statlib.Imported
open _root_.Statlib

theorem paper_d731a49b3997405b944f72bca5b16eab
    (eps0 : ℝ) (h_eps0_pos : 0 < eps0) (h_eps0_lt_one : eps0 < 1)
    (C : ℝ) (hC : 0 < C) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (m : ℕ), 1 ≤ m →
        ∀ (R : Matrix (Fin m) (Fin m) ℝ), R.IsSymm → (∀ j : Fin m, R j j = 1) →
          R.PosSemidef →
          (R.map (fun x : ℝ => max x 0)).PosSemidef →
          (∀ i j : Fin m, i ≠ j → R i j ≤ 1 - eps0) →
          (∑ p ∈ (Finset.univ.filter (fun p : Fin m × Fin m => p.1 < p.2)),
              max (R p.1 p.2) 0) ≤ C * (m : ℝ) →
          ∀ (ζ : Ω → Fin m → ℝ),
            Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ ζ R →
            (μ {ω | ∀ j : Fin m, ζ ω j ≤ Real.sqrt (Real.log (m : ℝ))}).toReal ≤
              C' * Real.exp ((-(1 / 2) : ℝ) * (m : ℝ) ^ ((1 : ℝ) / 3))
:= by
  /- @proof-region region.root.865085a6f5a4 begin -/
  have hδ_pos : (0:ℝ) < eps0 / 2 := by linarith
  have hδ_lt_one : eps0 / 2 < 1 := by linarith
  obtain ⟨s1, hs1_gt1, hs1⟩ := statopia_math_node_2727738868_45cbd6a3 (eps0 / 2) hδ_pos hδ_lt_one
  obtain ⟨A, hA_pos, hA⟩ := statopia_math_node_1762106652_3bf260e6 eps0 h_eps0_pos h_eps0_lt_one C hC
  have hs1_pos : (0:ℝ) < s1 := by linarith
  have hγpos : (0:ℝ) < 1 / (2 - eps0) - 1 / (2 - eps0 / 2) := by
    have h1 : (0:ℝ) < 2 - eps0 := by linarith
    have h2 : (0:ℝ) < 2 - eps0 / 2 := by linarith
    have hiff : ((2 - eps0) ^ (-1:ℝ) ≤ (2 - eps0 / 2) ^ (-1:ℝ)) ↔ 2 - eps0 / 2 ≤ 2 - eps0 :=
      Real.rpow_le_rpow_iff_of_neg h1 h2 (by norm_num)
    have hgt : (2 - eps0 / 2) ^ (-1:ℝ) < (2 - eps0) ^ (-1:ℝ) := by
      apply lt_of_not_ge
      intro hcon
      have hle := hiff.mp hcon
      linarith
    have e1 : (2 - eps0 / 2) ^ (-1:ℝ) = (2 - eps0 / 2)⁻¹ := by
      rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_one]
    have e2 : (2 - eps0) ^ (-1:ℝ) = (2 - eps0)⁻¹ := by
      rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_one]
    have hlt : 1 / (2 - eps0 / 2) < 1 / (2 - eps0) := by
      rw [one_div, one_div, ← e1, ← e2]
      exact hgt
    linarith
  obtain ⟨N1, hN1⟩ := exists_nat_gt (s1 ^ (1 / (1 / (2 - eps0 / 2))))
  obtain ⟨N2, hN2⟩ := exists_nat_gt ((2 * A) ^ (1 / (1 / (2 - eps0) - 1 / (2 - eps0 / 2))))
  set T : ℝ := max 3 (max (N1:ℝ) (N2:ℝ)) with hT
  have hT3 : (3:ℝ) ≤ T := by rw [hT]; exact le_max_left _ _
  refine ⟨max 1 (Real.exp (T ^ ((1:ℝ)/3) / 2)), ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_left 1 _)
  · intro Ω _ μ _ m hm R hR_symm hR_diag hR_psd hS_psd hR_off hSum ζ hζ
    by_cases hlarge : T ≤ (m:ℝ)
    · have hmT : max 3 (max (N1:ℝ) (N2:ℝ)) ≤ (m:ℝ) := by
        rw [hT] at hlarge
        exact hlarge
      have hm3R : (3:ℝ) ≤ (m:ℝ) := le_trans (le_max_left _ _) hmT
      have hN1R : (N1:ℝ) ≤ (m:ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hmT
      have hN2R : (N2:ℝ) ≤ (m:ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hmT
      have hm3 : 3 ≤ m := by exact_mod_cast hm3R
      have hm1R : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
      have hmpos : (0:ℝ) < (m:ℝ) := by linarith
      have hexpκ : (0:ℝ) ≤ 1 / (2 - eps0 / 2) := by
        have h : (0:ℝ) < 2 - eps0 / 2 := by linarith
        positivity
      have hinv_le_inv : ∀ c d : ℝ, 0 < c → c ≤ d → 1 / d ≤ 1 / c := by
        intro c d hc hcd
        have h1 : d ^ (-1:ℝ) ≤ c ^ (-1:ℝ) := Real.rpow_le_rpow_of_nonpos hc hcd (by norm_num)
        have e1 : d ^ (-1:ℝ) = 1 / d := by rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_one, one_div]
        have e2 : c ^ (-1:ℝ) = 1 / c := by rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_one, one_div]
        rwa [e1, e2] at h1
      have mul_inv_self : ∀ x : ℝ, 0 < x → x * x⁻¹ = 1 := by
        intro x hx
        have h := Real.rpow_add hx (1:ℝ) (-1)
        rw [show (1:ℝ) + (-1) = 0 by norm_num, Real.rpow_zero, Real.rpow_one] at h
        have hneg : x ^ (-1:ℝ) = x⁻¹ := by rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_one]
        rw [hneg] at h
        exact h.symm
      have inv_mul_self : ∀ x : ℝ, 0 < x → x⁻¹ * x = 1 := by
        intro x hx
        rw [mul_comm]
        exact mul_inv_self x hx
      have hκnorm : (1 / (1 / (2 - eps0 / 2))) * (1 / (2 - eps0 / 2)) = 1 := by
        have ha : (0:ℝ) < 2 - eps0 / 2 := by linarith
        simpa only [one_div, inv_inv] using mul_inv_self (2 - eps0 / 2) ha
      have hs1le : s1 ≤ (m:ℝ) ^ (1 / (2 - eps0 / 2)) := by
        have hbase : s1 ^ (1 / (1 / (2 - eps0 / 2))) ≤ (N1:ℝ) := le_of_lt hN1
        have hp : (0:ℝ) ≤ s1 ^ (1 / (1 / (2 - eps0 / 2))) :=
          le_of_lt (Real.rpow_pos_of_pos hs1_pos _)
        have heq : (s1 ^ (1 / (1 / (2 - eps0 / 2)))) ^ (1 / (2 - eps0 / 2)) = s1 := by
          rw [← Real.rpow_mul (le_of_lt hs1_pos), hκnorm, Real.rpow_one]
        refine le_trans (le_of_eq heq.symm) (le_trans (Real.rpow_le_rpow hp hbase hexpκ) ?_)
        exact Real.rpow_le_rpow (by positivity) hN1R hexpκ
      have hγnorm : (1 / (1 / (2 - eps0) - 1 / (2 - eps0 / 2))) * (1 / (2 - eps0) - 1 / (2 - eps0 / 2)) = 1 := by
        simpa only [one_div] using inv_mul_self (1 / (2 - eps0) - 1 / (2 - eps0 / 2)) hγpos
      have h2A : 2 * A ≤ (m:ℝ) ^ (1 / (2 - eps0) - 1 / (2 - eps0 / 2)) := by
        have h2Apos : (0:ℝ) < 2 * A := by linarith
        have hbase : (2 * A) ^ (1 / (1 / (2 - eps0) - 1 / (2 - eps0 / 2))) ≤ (N2:ℝ) := le_of_lt hN2
        have hp : (0:ℝ) ≤ (2 * A) ^ (1 / (1 / (2 - eps0) - 1 / (2 - eps0 / 2))) :=
          le_of_lt (Real.rpow_pos_of_pos h2Apos _)
        have heq : ((2 * A) ^ (1 / (1 / (2 - eps0) - 1 / (2 - eps0 / 2)))) ^ (1 / (2 - eps0) - 1 / (2 - eps0 / 2))
            = 2 * A := by
          rw [← Real.rpow_mul (le_of_lt h2Apos), hγnorm, Real.rpow_one]
        exact le_trans (le_of_eq heq.symm)
          (le_trans (Real.rpow_le_rpow hp hbase (le_of_lt hγpos))
            (Real.rpow_le_rpow (by positivity) hN2R (le_of_lt hγpos)))
      have hΦdef : Statlib.StatFoundation.RandomVariable.Gaussian.standardGaussianCDF
          (Real.sqrt (Real.log (m:ℝ)))
          = ((gaussianReal 0 1) (Set.Iic (Real.sqrt (Real.log (m:ℝ))))).toReal := rfl
      have hPhi_le : Statlib.StatFoundation.RandomVariable.Gaussian.standardGaussianCDF
          (Real.sqrt (Real.log (m:ℝ))) ≤ 1 - 1 / ((m:ℝ) ^ (1 / (2 - eps0 / 2))) := by
        have hlog := Real.log_rpow hmpos (1 / (2 - eps0 / 2))
        have harg : (2 - eps0 / 2) * Real.log ((m:ℝ) ^ (1 / (2 - eps0 / 2))) = Real.log (m:ℝ) := by
          rw [hlog]
          have h2δκ : (2 - eps0 / 2) * (1 / (2 - eps0 / 2)) = 1 := by
            have ha : (0:ℝ) < 2 - eps0 / 2 := by linarith
            simpa only [one_div] using mul_inv_self (2 - eps0 / 2) ha
          rw [← mul_assoc, h2δκ, one_mul]
        have hdep := hs1 ((m:ℝ) ^ (1 / (2 - eps0 / 2))) hs1le
        rw [harg] at hdep
        rw [hΦdef]
        exact hdep
      have hΦnonneg : (0:ℝ) ≤ Statlib.StatFoundation.RandomVariable.Gaussian.standardGaussianCDF
          (Real.sqrt (Real.log (m:ℝ))) := by
        rw [hΦdef]
        positivity
      have hpow_ge_one : (1:ℝ) ≤ (m:ℝ) ^ (1 / (2 - eps0 / 2)) := by
        have h := Real.rpow_le_rpow (le_of_lt (by norm_num : (0:ℝ) < 1)) hm1R hexpκ
        simpa using h
      have hbase_nonneg : (0:ℝ) ≤ 1 - 1 / ((m:ℝ) ^ (1 / (2 - eps0 / 2))) := by
        have hinv : (1:ℝ) / ((m:ℝ) ^ (1 / (2 - eps0 / 2))) ≤ 1 := by
          have h := hinv_le_inv (1:ℝ) ((m:ℝ) ^ (1 / (2 - eps0 / 2))) (by norm_num) hpow_ge_one
          simpa using h
        linarith
      have hmulid : (m:ℝ) * (1 / ((m:ℝ) ^ (1 / (2 - eps0 / 2)))) = (m:ℝ) ^ (1 - 1 / (2 - eps0 / 2)) := by
        rw [Real.rpow_sub hmpos, Real.rpow_one]
        ring
      have hpow_final : (Real.exp (-(1 / ((m:ℝ) ^ (1 / (2 - eps0 / 2)))))) ^ m
          = Real.exp (-((m:ℝ) ^ (1 - 1 / (2 - eps0 / 2)))) := by
        rw [← Real.exp_nat_mul]
        congr 1
        rw [mul_neg, hmulid]
      have hpow_base : (Statlib.StatFoundation.RandomVariable.Gaussian.standardGaussianCDF
          (Real.sqrt (Real.log (m:ℝ)))) ^ m
          ≤ (1 - 1 / ((m:ℝ) ^ (1 / (2 - eps0 / 2)))) ^ m := by
        have h := Real.rpow_le_rpow hΦnonneg hPhi_le (by positivity : (0:ℝ) ≤ (m:ℝ))
        simpa using h
      have hpow_exp : (1 - 1 / ((m:ℝ) ^ (1 / (2 - eps0 / 2)))) ^ m
          ≤ (Real.exp (-(1 / ((m:ℝ) ^ (1 / (2 - eps0 / 2)))))) ^ m := by
        have h := Real.rpow_le_rpow hbase_nonneg (Real.one_sub_le_exp_neg _) (by positivity : (0:ℝ) ≤ (m:ℝ))
        simpa using h
      have hPhi_bound : (Statlib.StatFoundation.RandomVariable.Gaussian.standardGaussianCDF
          (Real.sqrt (Real.log (m:ℝ)))) ^ m ≤ Real.exp (-((m:ℝ) ^ (1 - 1 / (2 - eps0 / 2)))) := by
        refine le_trans hpow_base ?_
        refine le_trans hpow_exp ?_
        exact le_of_eq hpow_final
      have hK_nonneg : (0:ℝ) ≤ Statlib.StatFoundation.RandomVariable.Gaussian.slepianCorrectionFactor m
          (fun i j : Fin m => max (R i j) 0) (Real.sqrt (Real.log (m:ℝ))) := by
        rw [Statlib.StatFoundation.RandomVariable.Gaussian.slepianCorrectionFactor]
        positivity
      have hS_off : ∀ i j : Fin m, i ≠ j →
          0 ≤ (fun i j : Fin m => max (R i j) 0) i j ∧ (fun i j : Fin m => max (R i j) 0) i j ≤ 1 - eps0 := by
        intro i j hij
        have hle := hR_off i j hij
        have h0 : (0:ℝ) < 1 - eps0 := by linarith
        exact ⟨le_max_right _ _, max_le hle (le_of_lt h0)⟩
      have hS_sum : (∑ p ∈ (Finset.univ.filter (fun p : Fin m × Fin m => p.1 < p.2)),
          (fun i j : Fin m => max (R i j) 0) p.1 p.2) ≤ C * (m:ℝ) := hSum
      have hcorr : Statlib.StatFoundation.RandomVariable.Gaussian.slepianCorrectionFactor m
          (fun i j : Fin m => max (R i j) 0) (Real.sqrt (Real.log (m:ℝ)))
          ≤ Real.exp (A * (m:ℝ) ^ (1 - 1 / (2 - eps0))) := by
        have hc := hA m hm (fun i j : Fin m => max (R i j) 0) hS_off hS_sum
        simpa [Statlib.StatFoundation.RandomVariable.Gaussian.slepianCorrectionFactor] using hc
      have hoff1 : ∀ i j : Fin m, i ≠ j → R i j < 1 := by
        intro i j hij
        have hle := hR_off i j hij
        linarith
      have hcmp := statopia_math_node_2042219946_a98a529d m hm3 R hR_symm hR_psd hR_diag hoff1 hS_psd Ω μ ζ hζ
      have hmapapply : (R.map (fun x : ℝ => max x 0)) = fun i j : Fin m => max (R i j) 0 := rfl
      rw [hmapapply] at hcmp
      have hmul : Statlib.StatFoundation.RandomVariable.Gaussian.slepianCorrectionFactor m
          (fun i j : Fin m => max (R i j) 0) (Real.sqrt (Real.log (m:ℝ))) *
          (Statlib.StatFoundation.RandomVariable.Gaussian.standardGaussianCDF (Real.sqrt (Real.log (m:ℝ)))) ^ m
          ≤ Real.exp (A * (m:ℝ) ^ (1 - 1 / (2 - eps0))) *
            Real.exp (-((m:ℝ) ^ (1 - 1 / (2 - eps0 / 2)))) := by
        refine le_trans (mul_le_mul_of_nonneg_left hPhi_bound hK_nonneg) ?_
        exact mul_le_mul_of_nonneg_right hcorr (le_of_lt (Real.exp_pos _))
      have hexp_combine : Real.exp (A * (m:ℝ) ^ (1 - 1 / (2 - eps0))) *
          Real.exp (-((m:ℝ) ^ (1 - 1 / (2 - eps0 / 2))))
          = Real.exp (A * (m:ℝ) ^ (1 - 1 / (2 - eps0)) - (m:ℝ) ^ (1 - 1 / (2 - eps0 / 2))) := by
        rw [← Real.exp_add]
        congr 1
      have hαγ : (1 - 1 / (2 - eps0)) + (1 / (2 - eps0) - 1 / (2 - eps0 / 2)) = 1 - 1 / (2 - eps0 / 2) := by
        ring
      have hsplit : (m:ℝ) ^ (1 - 1 / (2 - eps0)) * (m:ℝ) ^ (1 / (2 - eps0) - 1 / (2 - eps0 / 2))
          = (m:ℝ) ^ (1 - 1 / (2 - eps0 / 2)) := by
        rw [← Real.rpow_add hmpos, hαγ]
      have hstep : A * (m:ℝ) ^ (1 - 1 / (2 - eps0)) ≤ (1 / 2) * (m:ℝ) ^ (1 - 1 / (2 - eps0 / 2)) := by
        have hmα_pos : (0:ℝ) < (m:ℝ) ^ (1 - 1 / (2 - eps0)) := Real.rpow_pos_of_pos hmpos _
        have hhalf : A ≤ (1 / 2) * (m:ℝ) ^ (1 / (2 - eps0) - 1 / (2 - eps0 / 2)) := by linarith
        have h2 : A * (m:ℝ) ^ (1 - 1 / (2 - eps0))
            ≤ ((1 / 2) * (m:ℝ) ^ (1 / (2 - eps0) - 1 / (2 - eps0 / 2))) * (m:ℝ) ^ (1 - 1 / (2 - eps0)) :=
          mul_le_mul_of_nonneg_right hhalf (le_of_lt hmα_pos)
        have heq : ((1 / 2) * (m:ℝ) ^ (1 / (2 - eps0) - 1 / (2 - eps0 / 2))) * (m:ℝ) ^ (1 - 1 / (2 - eps0))
            = (1 / 2) * ((m:ℝ) ^ (1 - 1 / (2 - eps0)) * (m:ℝ) ^ (1 / (2 - eps0) - 1 / (2 - eps0 / 2))) := by
          ring
        rw [heq, hsplit] at h2
        exact h2
      have hkey : (1:ℝ) / (2 - eps0 / 2) ≤ 2 / 3 := by
        have h32 : (3:ℝ) / 2 ≤ 2 - eps0 / 2 := by linarith
        have h := hinv_le_inv ((3:ℝ) / 2) (2 - eps0 / 2) (by norm_num) h32
        have h1 : (1:ℝ) / (3 / 2) = 2 / 3 := by norm_num
        rwa [h1] at h
      have hβge : (1:ℝ) / 3 ≤ 1 - 1 / (2 - eps0 / 2) := by linarith
      have hexp_bound : A * (m:ℝ) ^ (1 - 1 / (2 - eps0)) - (m:ℝ) ^ (1 - 1 / (2 - eps0 / 2))
          ≤ -(1 / 2) * (m:ℝ) ^ ((1:ℝ) / 3) := by
        have h1 : A * (m:ℝ) ^ (1 - 1 / (2 - eps0)) - (m:ℝ) ^ (1 - 1 / (2 - eps0 / 2))
            ≤ -(1 / 2) * (m:ℝ) ^ (1 - 1 / (2 - eps0 / 2)) := by linarith
        have h2 : (m:ℝ) ^ ((1:ℝ) / 3) ≤ (m:ℝ) ^ (1 - 1 / (2 - eps0 / 2)) :=
          Real.rpow_le_rpow_of_exponent_le hm1R hβge
        linarith
      have hfin : (μ {ω | ∀ j : Fin m, ζ ω j ≤ Real.sqrt (Real.log (m:ℝ))}).toReal
          ≤ Real.exp ((-(1 / 2) : ℝ) * (m:ℝ) ^ ((1:ℝ) / 3)) := by
        refine le_trans hcmp ?_
        refine le_trans hmul ?_
        refine le_trans (le_of_eq hexp_combine) ?_
        exact Real.exp_le_exp.mpr hexp_bound
      have hC'ge : (1:ℝ) ≤ max 1 (Real.exp (T ^ ((1:ℝ)/3) / 2)) := le_max_left _ _
      have hz : (0:ℝ) < Real.exp ((-(1 / 2) : ℝ) * (m:ℝ) ^ ((1:ℝ) / 3)) := Real.exp_pos _
      have hone : Real.exp ((-(1 / 2) : ℝ) * (m:ℝ) ^ ((1:ℝ) / 3))
          ≤ max 1 (Real.exp (T ^ ((1:ℝ)/3) / 2)) * Real.exp ((-(1 / 2) : ℝ) * (m:ℝ) ^ ((1:ℝ) / 3)) := by
        have h := mul_le_mul_of_nonneg_right hC'ge (le_of_lt hz)
        simpa using h
      exact le_trans hfin hone
    · have hTle : (m:ℝ) ≤ T := le_of_lt (lt_of_not_ge hlarge)
      have hmn : (0:ℝ) ≤ (m:ℝ) := by positivity
      have hpow : (m:ℝ) ^ ((1:ℝ)/3) ≤ T ^ ((1:ℝ)/3) :=
        Real.rpow_le_rpow hmn hTle (by norm_num)
      have hmeasure : (μ {ω | ∀ j : Fin m, ζ ω j ≤ Real.sqrt (Real.log (m:ℝ))}).toReal ≤ 1 := by
        have hle : μ {ω | ∀ j : Fin m, ζ ω j ≤ Real.sqrt (Real.log (m:ℝ))} ≤ μ Set.univ :=
          measure_mono (Set.subset_univ _)
        have h := ENNReal.toReal_mono (show μ Set.univ ≠ ⊤ from by simp) hle
        simpa using h
      have harg : (0:ℝ) ≤ T ^ ((1:ℝ)/3) / 2 - (1/2) * (m:ℝ) ^ ((1:ℝ)/3) := by linarith
      have hexp1 : (1:ℝ) ≤ Real.exp (T ^ ((1:ℝ)/3) / 2 - (1/2) * (m:ℝ) ^ ((1:ℝ)/3)) := by
        have h := Real.exp_le_exp.mpr harg
        simpa using h
      have hfac : Real.exp (T ^ ((1:ℝ)/3) / 2 - (1/2) * (m:ℝ) ^ ((1:ℝ)/3))
          = Real.exp (T ^ ((1:ℝ)/3) / 2) * Real.exp ((-(1/2) : ℝ) * (m:ℝ) ^ ((1:ℝ)/3)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hC'ge : Real.exp (T ^ ((1:ℝ)/3) / 2) ≤ max 1 (Real.exp (T ^ ((1:ℝ)/3) / 2)) :=
        le_max_right _ _
      have hz : (0:ℝ) < Real.exp ((-(1/2) : ℝ) * (m:ℝ) ^ ((1:ℝ)/3)) := Real.exp_pos _
      have hprod : Real.exp (T ^ ((1:ℝ)/3) / 2) * Real.exp ((-(1/2) : ℝ) * (m:ℝ) ^ ((1:ℝ)/3))
          ≤ max 1 (Real.exp (T ^ ((1:ℝ)/3) / 2)) * Real.exp ((-(1/2) : ℝ) * (m:ℝ) ^ ((1:ℝ)/3)) :=
        mul_le_mul_of_nonneg_right hC'ge (le_of_lt hz)
      calc (μ {ω | ∀ j : Fin m, ζ ω j ≤ Real.sqrt (Real.log (m:ℝ))}).toReal ≤ 1 := hmeasure
        _ ≤ Real.exp (T ^ ((1:ℝ)/3) / 2 - (1/2) * (m:ℝ) ^ ((1:ℝ)/3)) := hexp1
        _ = Real.exp (T ^ ((1:ℝ)/3) / 2) * Real.exp ((-(1/2) : ℝ) * (m:ℝ) ^ ((1:ℝ)/3)) := hfac
        _ ≤ max 1 (Real.exp (T ^ ((1:ℝ)/3) / 2)) * Real.exp ((-(1/2) : ℝ) * (m:ℝ) ^ ((1:ℝ)/3)) := hprod
  /- @proof-region region.root.865085a6f5a4 end -/

end Statlib.Imported

