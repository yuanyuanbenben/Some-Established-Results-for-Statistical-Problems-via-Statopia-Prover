import ProverJobs.manual_dp_prior_finish_20261031.TailBound
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.Vocabulary
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.Base

noncomputable section
open MeasureTheory
namespace Statlib.Imported

theorem paper_3208f098a8f94aafb53ad0b136d14110
    (t : ℝ) (ht : 1 ≤ t)
    (π : ℝ → ℝ) (hπ_meas : Measurable π)
    (hπ_nonneg : ∀ α ∈ Set.Ioi (0 : ℝ), 0 ≤ π α)
    (hπ_prob : ∫⁻ α in Set.Ioi (0 : ℝ), ENNReal.ofReal (π α) = 1)
    (ε₀ δ β : ℝ) (hε₀ : 0 < ε₀) (hδ : 0 < δ) (hβ : 0 < β)
    (hA2 : ∀ α ∈ Set.Ioo (0 : ℝ) ε₀, δ⁻¹ * α ^ β ≤ π α ∧ π α ≤ δ * α ^ β) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧ ε ≤ ε₀ ∧
      δ * ε ^ (β + 1) / (β + 1) ≤ 1 / 2 ∧
      2 * δ ^ 2 * (Real.exp 1)⁻¹ * (t + β) / (t + 1 + β) *
          ε ^ (-(β + 1)) ≥ 2 ∧
      2 * δ ^ 2 * (Real.exp 1)⁻¹ * (t + β) /
          ((t + 1 + β) * (Real.log 2) ^ (t + β)) *
          ε ^ (-(t + 2 * β + 1)) ≥ 2 ∧
      ∃ F : ℝ, 0 < F ∧
        ∀ n s : ℕ, 1 ≤ n → 1 ≤ s → (s : ℝ) + t ≤ (n : ℝ) →
          ENNReal.ofReal
              (F * lowerGamma (t + (s : ℝ) + β) (ε * Real.log (n : ℝ)) /
                (Real.log (n : ℝ) + 1) ^ s) ≤
            Cratio π n t (s : ℝ) ∧
          Cratio π n t (s : ℝ) ≤
            ENNReal.ofReal (Gconst t ε δ β * (s : ℝ) / ε ^ s) *
              priorMoment π (t + (s : ℝ) - 1) *
                ENNReal.ofReal
                  (lowerGamma (t + (s : ℝ) + β) (ε * Real.log (n : ℝ)) /
                    (Real.log ((n : ℝ) / (1 + ε))) ^ s)
:= by
  /- @proof-region region.root.ddabacc30f97 begin -/
  obtain ⟨ε, hεpos, hεhalf, hεle, hB1, hB2, hB3⟩ :=
    statopia_math_node_2258488238_7148e540 t ht ε₀ δ β hε₀ hδ hβ
  have hε1 : ε < 1 := by linarith
  have hA2ε : ∀ α ∈ Set.Ioo (0 : ℝ) ε, δ⁻¹ * α ^ β ≤ π α ∧ π α ≤ δ * α ^ β := by
    intro α hα
    exact hA2 α ⟨hα.1, lt_of_lt_of_le hα.2 hεle⟩
  obtain ⟨hMpos, hMbound⟩ :=
    statopia_math_node_1866815261_49718380 t ht π hπ_meas hπ_nonneg hπ_prob ε δ β hεpos hδ hβ
      hA2ε
  set M : ℝ := risingFac ε ((⌈t + 1⌉).toNat) *
      ε ^ (t - ((⌈t + 1⌉).toNat : ℝ)) / (∫ α in Set.Ioo (0:ℝ) ε, α ^ t * π α) with hMdef
  have hMpos' : 0 < M := by rw [hMdef]; exact hMpos
  have hMtail : ∀ n : ℕ, (⌈t + 1⌉).toNat ≤ n →
      (∫ α in Set.Ioi ε, α ^ t / risingFac α n * π α) ≤
        M * (∫ α in Set.Ioo (0:ℝ) ε, α ^ t / risingFac α n * π α) := by
    intro n hn
    rw [hMdef]
    exact hMbound n hn
  have hGam : 0 < Real.Gamma (t + β) := Real.Gamma_pos_of_pos (by linarith)
  have hlgpos : ∀ x y : ℝ, 0 < x → 0 < y → 0 < lowerGamma x y := by
    intro x y hx hy
    have hint : IntervalIntegrable (fun z : ℝ => z ^ (x - 1) * Real.exp (-z)) volume 0 y := by
      have h1 : IntervalIntegrable (fun z : ℝ => z ^ (x - 1)) volume 0 y :=
        intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < x - 1)
      exact h1.mul_continuousOn (by fun_prop)
    have hpos : ∀ z ∈ Set.Ioo (0:ℝ) y, 0 < z ^ (x - 1) * Real.exp (-z) := by
      intro z hz
      exact mul_pos (Real.rpow_pos_of_pos hz.1 _) (Real.exp_pos _)
    show 0 < ∫ z in (0:ℝ)..y, z ^ (x - 1) * Real.exp (-z)
    exact intervalIntegral.intervalIntegral_pos_of_pos_on hint hpos hy
  have hintIoi : ∀ x : ℝ, 0 < x →
      Integrable (fun z : ℝ => z ^ (x - 1) * Real.exp (-z))
        (volume.restrict (Set.Ioi (0:ℝ))) := by
    intro x hx
    exact MeasureTheory.Integrable.congr (Real.GammaIntegral_convergent hx)
      (Filter.Eventually.of_forall fun z => mul_comm (Real.exp (-z)) (z ^ (x - 1)))
  have hintIoc : ∀ x y : ℝ, 0 < x →
      Integrable (fun z : ℝ => z ^ (x - 1) * Real.exp (-z))
        (volume.restrict (Set.Ioc (0:ℝ) y)) := by
    intro x y hx
    have hss : Set.Ioc (0:ℝ) y ∩ Set.Ioi (0:ℝ) = Set.Ioc (0:ℝ) y := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioi]
      exact ⟨fun h => h.1, fun h => ⟨h, h.1⟩⟩
    have hle : volume.restrict (Set.Ioc (0:ℝ) y) ≤ volume.restrict (Set.Ioi (0:ℝ)) := by
      calc volume.restrict (Set.Ioc (0:ℝ) y)
          = (volume.restrict (Set.Ioi (0:ℝ))).restrict (Set.Ioc (0:ℝ) y) := by
            rw [MeasureTheory.Measure.restrict_restrict (μ := volume) measurableSet_Ioc, hss]
        _ ≤ volume.restrict (Set.Ioi (0:ℝ)) := MeasureTheory.Measure.restrict_le_self
    exact (hintIoi x hx).mono_measure hle
  have hnnIoc : ∀ x y : ℝ,
      0 ≤ᶠ[ae (volume.restrict (Set.Ioc (0:ℝ) y))]
        (fun z : ℝ => z ^ (x - 1) * Real.exp (-z)) := by
    intro x y
    exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall fun z hz =>
        mul_nonneg (Real.rpow_nonneg hz.1.le _) (Real.exp_pos _).le)
  have hγΓ : ∀ x y : ℝ, 0 < x → 0 ≤ y → lowerGamma x y ≤ Real.Gamma x := by
    intro x y hx hy
    have hconv : (∫ z in Set.Ioc (0:ℝ) y, z ^ (x - 1) * Real.exp (-z)) ≤
        ∫ z in Set.Ioi (0:ℝ), z ^ (x - 1) * Real.exp (-z) := by
      refine MeasureTheory.setIntegral_mono_set (hintIoi x hx) ?_ ?_
      · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall ?_)
        intro z hz
        exact mul_nonneg (Real.rpow_nonneg hz.le _) (Real.exp_pos _).le
      · exact Filter.Eventually.of_forall fun z hz => hz.1
    have e1 : lowerGamma x y = ∫ z in Set.Ioc (0:ℝ) y, z ^ (x - 1) * Real.exp (-z) := by
      simp only [lowerGamma]
      exact intervalIntegral.integral_of_le hy
    have e2 : Real.Gamma x = ∫ z in Set.Ioi (0:ℝ), z ^ (x - 1) * Real.exp (-z) := by
      rw [Real.Gamma_eq_integral hx]
      exact MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun z => mul_comm (Real.exp (-z)) (z ^ (x - 1)))
    rw [e1, e2]
    exact hconv
  have hγmono : ∀ x y y' : ℝ, 0 < x → 0 ≤ y → y ≤ y' →
      lowerGamma x y ≤ lowerGamma x y' := by
    intro x y y' hx hy hyy'
    have hconv : (∫ z in Set.Ioc (0:ℝ) y, z ^ (x - 1) * Real.exp (-z)) ≤
        ∫ z in Set.Ioc (0:ℝ) y', z ^ (x - 1) * Real.exp (-z) := by
      refine MeasureTheory.setIntegral_mono_set (hintIoc x y' hx) (hnnIoc x y') ?_
      exact Filter.Eventually.of_forall fun z hz => ⟨hz.1, le_trans hz.2 hyy'⟩
    have e1 : lowerGamma x y = ∫ z in Set.Ioc (0:ℝ) y, z ^ (x - 1) * Real.exp (-z) := by
      simp only [lowerGamma]
      exact intervalIntegral.integral_of_le hy
    have e2 : lowerGamma x y' = ∫ z in Set.Ioc (0:ℝ) y', z ^ (x - 1) * Real.exp (-z) := by
      simp only [lowerGamma]
      exact intervalIntegral.integral_of_le (le_trans hy hyy')
    rw [e1, e2]
    exact hconv
  have hFpos : 0 < 1 / ((M + 1) * δ ^ 2 * Real.Gamma (t + β)) := by
    have h1 : 0 < M + 1 := by linarith
    exact one_div_pos.mpr (mul_pos (mul_pos h1 (pow_pos hδ 2)) hGam)
  refine ⟨ε, hεpos, hεhalf, hεle, hB1, hB2, hB3,
    1 / ((M + 1) * δ ^ 2 * Real.Gamma (t + β)), hFpos, ?_⟩
  intro n s hn hs hns
  have hs1 : (1:ℝ) ≤ (s:ℝ) := by exact_mod_cast hs
  have hn2 : (2:ℝ) ≤ (n:ℝ) := by linarith
  have hn0 : (0:ℝ) < (n:ℝ) := by linarith
  have h1e0 : (0:ℝ) < 1 + ε := by linarith
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogn : (0:ℝ) < Real.log (n:ℝ) := Real.log_pos (by linarith)
  have hLpos : (0:ℝ) < Real.log ((n:ℝ) / (1 + ε)) := by
    rw [Real.log_div (ne_of_gt hn0) (ne_of_gt h1e0)]
    have hlt : Real.log (1 + ε) < Real.log (n:ℝ) := Real.log_lt_log h1e0 (by linarith)
    linarith
  have hrn : (0:ℝ) < Real.log (n:ℝ) + 1 := by linarith
  have hmono : ε * Real.log 2 ≤ ε * Real.log (n:ℝ) :=
    mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num) (by linarith)) hεpos.le
  have hfin :
      0 < (∫ α in Set.Ioo (0 : ℝ) ε, α ^ (t + (s : ℝ)) / risingFac α n * π α) ∧
        IntegrableOn (fun α : ℝ => α ^ (t + (s : ℝ)) / risingFac α n * π α)
          (Set.Ioo (0 : ℝ) ε) ∧
        0 < (∫ α in Set.Ioo (0 : ℝ) ε, α ^ t / risingFac α n * π α) ∧
        IntegrableOn (fun α : ℝ => α ^ t / risingFac α n * π α) (Set.Ioo (0 : ℝ) ε) ∧
        0 ≤ (∫ α in Set.Ioi ε, α ^ (t + (s : ℝ)) / risingFac α n * π α) ∧
        IntegrableOn (fun α : ℝ => α ^ (t + (s : ℝ)) / risingFac α n * π α) (Set.Ioi ε) ∧
        0 ≤ (∫ α in Set.Ioi ε, α ^ t / risingFac α n * π α) ∧
        IntegrableOn (fun α : ℝ => α ^ t / risingFac α n * π α) (Set.Ioi ε) ∧
        0 < ((∫ α in Set.Ioo (0 : ℝ) ε, α ^ (t + (s : ℝ)) / risingFac α n * π α) +
            (∫ α in Set.Ioi ε, α ^ (t + (s : ℝ)) / risingFac α n * π α)) /
          ((∫ α in Set.Ioo (0 : ℝ) ε, α ^ t / risingFac α n * π α) +
            (∫ α in Set.Ioi ε, α ^ t / risingFac α n * π α)) := by
    have hn9 := statopia_math_node_3788355289_2a3e6b7e t ht π hπ_meas hπ_nonneg hπ_prob ε δ β
      hεpos hδ hβ hA2ε n s hs hns
    obtain ⟨hI1, hA, hI2, hB, hI3, hAO, hI4, hBO, hQ⟩ := hn9
    exact ⟨hA, hI1, hB, hI2, hAO, hI3, hBO, hI4, hQ⟩
  have hden : 0 < (∫ α in Set.Ioo (0 : ℝ) ε, α ^ t / risingFac α n * π α) +
      (∫ α in Set.Ioi ε, α ^ t / risingFac α n * π α) := by
    have h1 : 0 < ∫ α in Set.Ioo (0 : ℝ) ε, α ^ t / risingFac α n * π α := hfin.2.2.1
    have h2 : 0 ≤ ∫ α in Set.Ioi ε, α ^ t / risingFac α n * π α := hfin.2.2.2.2.2.2.1
    linarith
  have hlow : ENNReal.ofReal
      ((1 / ((M + 1) * δ ^ 2 * Real.Gamma (t + β))) *
          lowerGamma (t + (s : ℝ) + β) (ε * Real.log (n : ℝ)) /
        (Real.log (n : ℝ) + 1) ^ s) ≤
      Cratio π n t (s : ℝ) := by
    have hcr := statopia_math_node_1497788876_00e778c3 t ht π hπ_meas hπ_nonneg hπ_prob ε δ β
      hεpos hδ hβ hA2ε n s hs (by linarith : (s : ℝ) + t ≤ (n : ℝ))
    set AI : ℝ := ∫ α in Set.Ioo (0 : ℝ) ε, α ^ (t + (s : ℝ)) / risingFac α n * π α
    set BI : ℝ := ∫ α in Set.Ioo (0 : ℝ) ε, α ^ t / risingFac α n * π α
    set AO : ℝ := ∫ α in Set.Ioi ε, α ^ (t + (s : ℝ)) / risingFac α n * π α
    set BO : ℝ := ∫ α in Set.Ioi ε, α ^ t / risingFac α n * π α
    have hfac : ∀ α : ℝ, 0 < α → 0 < risingFac α n := by
      intro α hα
      unfold risingFac
      exact Finset.prod_pos (fun k _ => by
        have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
        linarith)
    have hAInn : 0 ≤ AI := by
      refine MeasureTheory.setIntegral_nonneg_ae measurableSet_Ioo (Filter.Eventually.of_forall ?_)
      intro α hα
      have hα0 : 0 < α := hα.1
      have h1 : 0 < α ^ (t + (s : ℝ)) := Real.rpow_pos_of_pos hα0 _
      exact mul_nonneg (div_pos h1 (hfac α hα0)).le (hπ_nonneg α hα0)
    have hBIpos : 0 < BI := hfin.2.2.1
    have hkey : (1 / ((M + 1) * δ ^ 2 * Real.Gamma (t + β))) *
        lowerGamma (t + (s : ℝ) + β) (ε * Real.log (n : ℝ)) /
        (Real.log (n : ℝ) + 1) ^ s ≤ (1 / (M + 1)) * (AI / BI) := by
      have hL1 : (0 : ℝ) < Real.log (n : ℝ) + 1 := hrn
      have hApos : 0 < lowerGamma (t + (s : ℝ) + β) (ε * (Real.log (n : ℝ) + 1)) :=
        hlgpos _ _ (by linarith) (mul_pos hεpos hL1)
      have hB0pos : 0 < lowerGamma (t + β) (ε * (Real.log (n : ℝ) + 1)) :=
        hlgpos _ _ (by linarith) (mul_pos hεpos hL1)
      have hΦle : lowerGamma (t + (s : ℝ) + β) (ε * Real.log (n : ℝ)) ≤
          lowerGamma (t + (s : ℝ) + β) (ε * (Real.log (n : ℝ) + 1)) :=
        hγmono _ _ _ (by linarith) (mul_pos hεpos hlogn).le
          (mul_le_mul_of_nonneg_left (by linarith : Real.log (n : ℝ) ≤ Real.log (n : ℝ) + 1) hεpos.le)
      have hB0le : lowerGamma (t + β) (ε * (Real.log (n : ℝ) + 1)) ≤ Real.Gamma (t + β) :=
        hγΓ _ _ (by linarith) (mul_pos hεpos hL1).le
      have h1a : lowerGamma (t + (s : ℝ) + β) (ε * Real.log (n : ℝ)) / Real.Gamma (t + β) ≤
          lowerGamma (t + (s : ℝ) + β) (ε * (Real.log (n : ℝ) + 1)) / Real.Gamma (t + β) :=
        (div_le_div_iff_of_pos_right hGam).mpr hΦle
      have h1b : lowerGamma (t + (s : ℝ) + β) (ε * (Real.log (n : ℝ) + 1)) / Real.Gamma (t + β) ≤
          lowerGamma (t + (s : ℝ) + β) (ε * (Real.log (n : ℝ) + 1)) /
            lowerGamma (t + β) (ε * (Real.log (n : ℝ) + 1)) :=
        div_le_div_of_nonneg_left hApos.le hB0pos hB0le
      have hδ2 : (0 : ℝ) < δ ^ 2 := pow_pos hδ 2
      have h2 : lowerGamma (t + (s : ℝ) + β) (ε * Real.log (n : ℝ)) / (δ ^ 2 * Real.Gamma (t + β)) ≤
          lowerGamma (t + (s : ℝ) + β) (ε * (Real.log (n : ℝ) + 1)) /
            (δ ^ 2 * lowerGamma (t + β) (ε * (Real.log (n : ℝ) + 1))) := by
        have e1 : lowerGamma (t + (s : ℝ) + β) (ε * Real.log (n : ℝ)) / (δ ^ 2 * Real.Gamma (t + β)) =
            lowerGamma (t + (s : ℝ) + β) (ε * Real.log (n : ℝ)) / Real.Gamma (t + β) / δ ^ 2 := by
          rw [div_div, mul_comm (Real.Gamma (t + β)) (δ ^ 2)]
        have e2 : lowerGamma (t + (s : ℝ) + β) (ε * (Real.log (n : ℝ) + 1)) /
            (δ ^ 2 * lowerGamma (t + β) (ε * (Real.log (n : ℝ) + 1))) =
            lowerGamma (t + (s : ℝ) + β) (ε * (Real.log (n : ℝ) + 1)) /
              lowerGamma (t + β) (ε * (Real.log (n : ℝ) + 1)) / δ ^ 2 := by
          rw [div_div,
            mul_comm (lowerGamma (t + β) (ε * (Real.log (n : ℝ) + 1))) (δ ^ 2)]
        rw [e1, e2]
        exact (div_le_div_iff_of_pos_right hδ2).mpr (le_trans h1a h1b)
      have hrr := statopia_math_node_3004398593_64d30a63 t ht π hπ_meas hπ_nonneg hπ_prob ε δ β
        hεpos hε1 hδ hβ hA2ε n s hs (by linarith : t + (s : ℝ) ≤ (n : ℝ))
      have hpowcast : ∀ k : ℕ,
          (Real.log (n : ℝ) + 1) ^ ((k : ℝ)) = (Real.log (n : ℝ) + 1) ^ k := by
        intro k
        induction k with
        | zero => simp
        | succ m ih =>
            rw [Nat.cast_succ, Real.rpow_add_one (ne_of_gt hL1), ih, pow_succ]
      have hneg : (Real.log (n : ℝ) + 1) ^ (-(s : ℝ)) = ((Real.log (n : ℝ) + 1) ^ s)⁻¹ := by
        rw [Real.rpow_neg hL1.le, hpowcast s]
      have hnode := hrr.1
      rw [hneg] at hnode
      have hmono : lowerGamma (t + (s : ℝ) + β) (ε * Real.log (n : ℝ)) /
            (δ ^ 2 * Real.Gamma (t + β)) * ((Real.log (n : ℝ) + 1) ^ s)⁻¹ ≤
          lowerGamma (t + (s : ℝ) + β) (ε * (Real.log (n : ℝ) + 1)) /
            (δ ^ 2 * lowerGamma (t + β) (ε * (Real.log (n : ℝ) + 1))) *
            ((Real.log (n : ℝ) + 1) ^ s)⁻¹ :=
        mul_le_mul_of_nonneg_right h2 (le_of_lt (inv_pos.mpr (pow_pos hrn s)))
      have hgoal : lowerGamma (t + (s : ℝ) + β) (ε * Real.log (n : ℝ)) /
            (δ ^ 2 * Real.Gamma (t + β)) * ((Real.log (n : ℝ) + 1) ^ s)⁻¹ ≤ AI / BI :=
        le_trans hmono hnode
      have hM1 : (0 : ℝ) < M + 1 := by linarith
      have hEq : (1 / ((M + 1) * δ ^ 2 * Real.Gamma (t + β))) *
          lowerGamma (t + (s : ℝ) + β) (ε * Real.log (n : ℝ)) /
          (Real.log (n : ℝ) + 1) ^ s =
          (1 / (M + 1)) * (lowerGamma (t + (s : ℝ) + β) (ε * Real.log (n : ℝ)) /
            (δ ^ 2 * Real.Gamma (t + β)) * ((Real.log (n : ℝ) + 1) ^ s)⁻¹) := by
        have hne1 : (M + 1) ≠ 0 := ne_of_gt hM1
        have hne2 : δ ^ 2 ≠ 0 := ne_of_gt hδ2
        have hne3 : Real.Gamma (t + β) ≠ 0 := ne_of_gt hGam
        have hne4 : (Real.log (n : ℝ) + 1) ≠ 0 := ne_of_gt hL1
        have hne5 : (Real.log (n : ℝ) + 1) ^ s ≠ 0 := ne_of_gt (pow_pos hL1 s)
        field_simp
      rw [hEq]
      exact mul_le_mul_of_nonneg_left hgoal (le_of_lt (one_div_pos.mpr hM1))
    have hKn : (⌈t + 1⌉).toNat ≤ n := by
      have h1 : ⌈t + 1⌉ ≤ (n : ℤ) := by
        rw [Int.ceil_le]
        push_cast
        linarith
      exact Int.toNat_le.mpr h1
    have hBOle : BO ≤ M * BI := hMtail n hKn
    have hsum : BI + BO ≤ (M + 1) * BI := by nlinarith [hBOle]
    have hM1 : (0 : ℝ) < M + 1 := by linarith
    have hden : 0 < (M + 1) * BI := mul_pos hM1 hBIpos
    have hBOnn : 0 ≤ BO := by
      refine MeasureTheory.setIntegral_nonneg_ae measurableSet_Ioi (Filter.Eventually.of_forall ?_)
      intro α hα
      have hα0 : 0 < α := lt_trans hεpos hα
      have h1 : 0 < α ^ t := Real.rpow_pos_of_pos hα0 t
      exact mul_nonneg (div_pos h1 (hfac α hα0)).le (hπ_nonneg α hα0)
    have hAOnn : 0 ≤ AO := by
      refine MeasureTheory.setIntegral_nonneg_ae measurableSet_Ioi (Filter.Eventually.of_forall ?_)
      intro α hα
      have hα0 : 0 < α := lt_trans hεpos hα
      have h1 : 0 < α ^ (t + (s : ℝ)) := Real.rpow_pos_of_pos hα0 _
      exact mul_nonneg (div_pos h1 (hfac α hα0)).le (hπ_nonneg α hα0)
    have hden2 : 0 < BI + BO := by linarith
    have hstep : AI / ((M + 1) * BI) ≤ (AI + AO) / (BI + BO) := by
      have hA : AI / ((M + 1) * BI) ≤ AI / (BI + BO) :=
        div_le_div_of_nonneg_left hAInn hden2 hsum
      have hB : AI / (BI + BO) ≤ (AI + AO) / (BI + BO) :=
        (div_le_div_iff_of_pos_right hden2).mpr (by linarith)
      exact le_trans hA hB
    have h3 : (1 / (M + 1)) * (AI / BI) = AI / ((M + 1) * BI) := by
      rw [div_mul_div_comm, one_mul]
    have hq : (1 / ((M + 1) * δ ^ 2 * Real.Gamma (t + β))) *
        lowerGamma (t + (s : ℝ) + β) (ε * Real.log (n : ℝ)) /
        (Real.log (n : ℝ) + 1) ^ s ≤ (AI + AO) / (BI + BO) := by
      calc (1 / ((M + 1) * δ ^ 2 * Real.Gamma (t + β))) *
            lowerGamma (t + (s : ℝ) + β) (ε * Real.log (n : ℝ)) /
            (Real.log (n : ℝ) + 1) ^ s
          ≤ (1 / (M + 1)) * (AI / BI) := hkey
        _ = AI / ((M + 1) * BI) := h3
        _ ≤ (AI + AO) / (BI + BO) := hstep
    calc ENNReal.ofReal ((1 / ((M + 1) * δ ^ 2 * Real.Gamma (t + β))) *
          lowerGamma (t + (s : ℝ) + β) (ε * Real.log (n : ℝ)) /
          (Real.log (n : ℝ) + 1) ^ s)
        ≤ ENNReal.ofReal ((AI + AO) / (BI + BO)) := ENNReal.ofReal_le_ofReal hq
      _ = Cratio π n t (s : ℝ) := hcr.symm
  have hup : Cratio π n t (s : ℝ) ≤
      ENNReal.ofReal (Gconst t ε δ β * (s : ℝ) / ε ^ s) *
        priorMoment π (t + (s : ℝ) - 1) *
          ENNReal.ofReal
            (lowerGamma (t + (s : ℝ) + β) (ε * Real.log (n : ℝ)) /
              (Real.log ((n : ℝ) / (1 + ε))) ^ s) := by
    have hC0 : 0 < lowerGamma (t + β) (ε * Real.log 2) :=
      hlgpos (t + β) (ε * Real.log 2) (by linarith) (mul_pos hεpos hlog2)
    have hcpos : 0 < Gconst t ε δ β * (s : ℝ) / ε ^ s := by
      have hG : 0 < Gconst t ε δ β := by
        show 0 < 4 * δ ^ 2 / (ε ^ (t + β) * lowerGamma (t + β) (ε * Real.log 2))
        exact div_pos (mul_pos (by norm_num) (pow_pos hδ 2))
          (mul_pos (Real.rpow_pos_of_pos hεpos _) hC0)
      have hss : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
      exact div_pos (mul_pos hG hss) (pow_pos hεpos s)
    have hΦpos : 0 < lowerGamma (t + (s : ℝ) + β) (ε * Real.log (n : ℝ)) :=
      hlgpos (t + (s : ℝ) + β) (ε * Real.log (n : ℝ)) (by linarith) (mul_pos hεpos hlogn)
    have hLspos : 0 < (Real.log ((n : ℝ) / (1 + ε))) ^ s := pow_pos hLpos s
    have hfracpos : 0 < lowerGamma (t + (s : ℝ) + β) (ε * Real.log (n : ℝ)) /
        (Real.log ((n : ℝ) / (1 + ε))) ^ s := div_pos hΦpos hLspos
    rcases eq_or_ne (priorMoment π (t + (s : ℝ) - 1)) ⊤ with htop | hmomfin
    · have hA : ENNReal.ofReal (Gconst t ε δ β * (s : ℝ) / ε ^ s) ≠ 0 :=
        ne_of_gt (ENNReal.ofReal_pos.mpr hcpos)
      have hB : ENNReal.ofReal (lowerGamma (t + (s : ℝ) + β) (ε * Real.log (n : ℝ)) /
          (Real.log ((n : ℝ) / (1 + ε))) ^ s) ≠ 0 :=
        ne_of_gt (ENNReal.ofReal_pos.mpr hfracpos)
      rw [htop, ENNReal.mul_top hA, ENNReal.top_mul hB]
      exact le_top
    · have hcr2 := statopia_math_node_1497788876_00e778c3 t ht π hπ_meas hπ_nonneg hπ_prob ε δ β
        hεpos hδ hβ hA2ε n s hs (by linarith : (s : ℝ) + t ≤ (n : ℝ))
      have hEm : priorMoment π (t + (s : ℝ) - 1) =
          ENNReal.ofReal (∫ α in Set.Ioi (0 : ℝ), α ^ (t + (s : ℝ) - 1) * π α) := by
        have hnn : 0 ≤ᶠ[ae (volume.restrict (Set.Ioi (0:ℝ)))]
            (fun α : ℝ => α ^ (t + (s : ℝ) - 1) * π α) :=
          (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
            (Filter.Eventually.of_forall fun α hα =>
              mul_nonneg (Real.rpow_nonneg hα.le _) (hπ_nonneg α hα))
        have hlt : ∫⁻ α in Set.Ioi (0 : ℝ),
            ENNReal.ofReal (α ^ (t + (s : ℝ) - 1) * π α) < ⊤ :=
          lt_of_le_of_ne le_top hmomfin
        have hfi : HasFiniteIntegral (fun α : ℝ => α ^ (t + (s : ℝ) - 1) * π α)
            (volume.restrict (Set.Ioi (0:ℝ))) :=
          (MeasureTheory.hasFiniteIntegral_iff_ofReal hnn).mpr hlt
        have hmeas1 : AEStronglyMeasurable (fun α : ℝ => α ^ (t + (s : ℝ) - 1))
            (volume.restrict (Set.Ioi (0:ℝ))) :=
          ContinuousOn.aestronglyMeasurable
            (ContinuousOn.rpow_const continuousOn_id (fun x hx => Or.inl (ne_of_gt hx)))
            measurableSet_Ioi
        have hmeas2 : AEStronglyMeasurable (fun α : ℝ => π α)
            (volume.restrict (Set.Ioi (0:ℝ))) := hπ_meas.aestronglyMeasurable.restrict
        have hint : Integrable (fun α : ℝ => α ^ (t + (s : ℝ) - 1) * π α)
            (volume.restrict (Set.Ioi (0:ℝ))) := ⟨hmeas1.mul hmeas2, hfi⟩
        exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn).symm
      rw [hEm]
      have hGE : (0 : ℝ) ≤ Gconst t ε δ β * (s : ℝ) / ε ^ s := le_of_lt hcpos
      have hEnn : (0 : ℝ) ≤ ∫ α in Set.Ioi (0 : ℝ), α ^ (t + (s : ℝ) - 1) * π α := by
        refine MeasureTheory.setIntegral_nonneg_ae measurableSet_Ioi (Filter.Eventually.of_forall ?_)
        intro α hα
        exact mul_nonneg (Real.rpow_nonneg hα.le _) (hπ_nonneg α hα)
      have hEhalf : ε ^ (t + (s : ℝ) - 1) / 2 ≤
          ∫ α in Set.Ioi (0 : ℝ), α ^ (t + (s : ℝ) - 1) * π α := by
        have hm := statopia_math_node_1797268609_53e08000 t ht s hs π hπ_meas hπ_nonneg hπ_prob
          ε δ β hεpos hεhalf hδ hβ hA2ε hB1
        obtain ⟨-, -, -, -, -, -, hF⟩ := hm
        exact hF hmomfin

      set_option maxHeartbeats 1600000 in
      have hT : ((∫ α in Set.Ioo (0 : ℝ) ε, α ^ (t + (s : ℝ)) / risingFac α n * π α) +
            (∫ α in Set.Ioi ε, α ^ (t + (s : ℝ)) / risingFac α n * π α)) /
          ((∫ α in Set.Ioo (0 : ℝ) ε, α ^ t / risingFac α n * π α) +
            (∫ α in Set.Ioi ε, α ^ t / risingFac α n * π α)) ≤
          Gconst t ε δ β * (s : ℝ) / ε ^ s *
            (∫ α in Set.Ioi (0 : ℝ), α ^ (t + (s : ℝ) - 1) * π α) *
            (lowerGamma (t + (s : ℝ) + β) (ε * Real.log (n : ℝ)) /
              (Real.log ((n : ℝ) / (1 + ε))) ^ s) := by
        clear hMpos hMpos' hMbound hMtail hMdef hintIoi hintIoc hnnIoc hγΓ hGam hFpos
        have hεβ : ε ^ (β + 1) ≤ 1 / 2 := by
          have h3 : ε ^ (β + 1) ≤ ε ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge' hεpos.le (by linarith) (by norm_num) (by linarith)
          rw [Real.rpow_one] at h3
          exact le_trans h3 hεhalf.le
        set AI : ℝ := ∫ α in Set.Ioo (0 : ℝ) ε, α ^ (t + (s : ℝ)) / risingFac α n * π α with hAI
        set BI : ℝ := ∫ α in Set.Ioo (0 : ℝ) ε, α ^ t / risingFac α n * π α with hBI
        set AO : ℝ := ∫ α in Set.Ioi ε, α ^ (t + (s : ℝ)) / risingFac α n * π α with hAO
        set BO : ℝ := ∫ α in Set.Ioi ε, α ^ t / risingFac α n * π α with hBO
        set Y : ℝ := ∫ α in Set.Ioi (0 : ℝ), α ^ (t + (s : ℝ) - 1) * π α with hY
        set Pg : ℝ := lowerGamma (t + (s : ℝ) + β) (ε * Real.log (n : ℝ)) with hPg
        set Lp : ℝ := (Real.log ((n : ℝ) / (1 + ε))) ^ s with hLp
        set W : ℝ := Gconst t ε δ β * (s : ℝ) / ε ^ s with hW
        have hWnn : 0 ≤ W := hcpos.le
        have hYnn : 0 ≤ Y := hEnn
        have hYhalf : ε ^ (t + (s : ℝ) - 1) / 2 ≤ Y := hEhalf
        have hBIpos : 0 < BI := hfin.2.2.1
        have hBIne : BI ≠ 0 := ne_of_gt hBIpos
        have hBInn : 0 ≤ BI := hBIpos.le
        have hBOnn : 0 ≤ BO := hfin.2.2.2.2.2.2.1
        have hPgnn : 0 ≤ Pg / Lp := hfracpos.le
        have hLppos : 0 < Lp := hLspos
        have hLpne : Lp ≠ 0 := ne_of_gt hLppos
        have hC0ne : lowerGamma (t + β) (ε * Real.log 2) ≠ 0 := ne_of_gt hC0
        have hεbne : ε ^ (t + β) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hεpos _)
        have hεsne : ε ^ s ≠ 0 := ne_of_gt (pow_pos hεpos s)
        have hγnpos : 0 < lowerGamma (t + β) (ε * Real.log (n : ℝ)) :=
          hlgpos _ _ (by linarith) (mul_pos hεpos hlogn)
        have hγnne : lowerGamma (t + β) (ε * Real.log (n : ℝ)) ≠ 0 := ne_of_gt hγnpos
        have hγnge : lowerGamma (t + β) (ε * Real.log 2) ≤
            lowerGamma (t + β) (ε * Real.log (n : ℝ)) :=
          hγmono _ _ _ (by linarith) (mul_pos hεpos hlog2).le hmono
        have hcast : ∀ x : ℝ, x ≠ 0 → ∀ k : ℕ, x ^ ((k : ℝ)) = x ^ k := by
          intro x hx k
          induction k with
          | zero => rw [Nat.cast_zero, Real.rpow_zero, pow_zero]
          | succ m ih => rw [Nat.cast_succ, Real.rpow_add_one hx, ih, pow_succ]
        have hEP : ε ^ (t + (s : ℝ) + β) ≤ (s : ℝ) * Y := by
          have h1 : ε ^ (t + (s : ℝ) + β) = ε ^ (t + (s : ℝ) - 1) * ε ^ (β + 1) := by
            have e : t + (s : ℝ) + β = (t + (s : ℝ) - 1) + (β + 1) := by ring
            rw [e, Real.rpow_add hεpos (t + (s : ℝ) - 1) (β + 1)]
          have h2 : ε ^ (t + (s : ℝ) - 1) * ε ^ (β + 1) ≤
              ε ^ (t + (s : ℝ) - 1) * (1 / 2) :=
            mul_le_mul_of_nonneg_left hεβ (Real.rpow_pos_of_pos hεpos _).le
          have ha : ε ^ (t + (s : ℝ) - 1) * (1 / 2) ≤ Y := by linarith only [hYhalf]
          have hb : (1 : ℝ) * Y ≤ (s : ℝ) * Y := mul_le_mul_of_nonneg_right hs1 hYnn
          rw [h1]
          linarith only [h2, ha, hb]
        have hx3 : ε ^ (t + (s : ℝ) + β) = ε ^ (t + β) * ε ^ s := by
          have e : t + (s : ℝ) + β = (t + β) + (s : ℝ) := by ring
          rw [e, Real.rpow_add hεpos (t + β) (s : ℝ), hcast ε (ne_of_gt hεpos) s]
        have hdene : (0 : ℝ) < ε ^ (t + β) * ε ^ s :=
          mul_pos (Real.rpow_pos_of_pos hεpos _) (pow_pos hεpos s)
        have hone : 1 ≤ (s : ℝ) * Y / (ε ^ (t + β) * ε ^ s) := by
          have hb : ε ^ (t + β) * ε ^ s ≤ (s : ℝ) * Y := by
            rw [← hx3]
            exact hEP
          have h1 : (1 : ℝ) = (ε ^ (t + β) * ε ^ s) / (ε ^ (t + β) * ε ^ s) := by
            rw [div_self (ne_of_gt hdene)]
          rw [h1]
          exact div_le_div_of_nonneg_right hb hdene.le
        have hhead : AI ≤ (W * Y * (Pg / Lp) / 4) * BI := by
          have hnegL : (Real.log ((n : ℝ) / (1 + ε))) ^ (-(s : ℝ)) = Lp⁻¹ := by
            rw [hLp, Real.rpow_neg hLpos.le, hcast _ (ne_of_gt hLpos) s]
          have hUp0 := (statopia_math_node_3004398593_64d30a63 t ht π hπ_meas hπ_nonneg hπ_prob ε δ β
            hεpos hε1 hδ hβ hA2ε n s hs (by linarith : t + (s : ℝ) ≤ (n : ℝ))).2
          rw [hnegL] at hUp0
          have hUp : AI / BI ≤
              δ ^ 2 * Pg / lowerGamma (t + β) (ε * Real.log (n : ℝ)) * Lp⁻¹ := by
            rw [hAI, hBI, hPg]
            exact hUp0
          have he1 : δ ^ 2 * Pg / lowerGamma (t + β) (ε * Real.log (n : ℝ)) * Lp⁻¹ =
              δ ^ 2 * Pg / (lowerGamma (t + β) (ε * Real.log (n : ℝ)) * Lp) := by
            field_simp [hγnne, hLpne]
          have hcore : δ ^ 2 * Pg / (lowerGamma (t + β) (ε * Real.log (n : ℝ)) * Lp) ≤
              W * Y * (Pg / Lp) / 4 := by
            have hbC : (0 : ℝ) ≤ δ ^ 2 * Pg / (lowerGamma (t + β) (ε * Real.log 2) * Lp) :=
              (div_pos (mul_pos (pow_pos hδ 2) hΦpos) (mul_pos hC0 hLppos)).le
            have hCL : (0 : ℝ) < lowerGamma (t + β) (ε * Real.log 2) * Lp := mul_pos hC0 hLppos
            have hle1 : lowerGamma (t + β) (ε * Real.log 2) * Lp ≤
                lowerGamma (t + β) (ε * Real.log (n : ℝ)) * Lp :=
              mul_le_mul_of_nonneg_right hγnge hLppos.le
            have hA : δ ^ 2 * Pg / (lowerGamma (t + β) (ε * Real.log (n : ℝ)) * Lp) ≤
                δ ^ 2 * Pg / (lowerGamma (t + β) (ε * Real.log 2) * Lp) :=
              div_le_div_of_nonneg_left (mul_nonneg (pow_pos hδ 2).le hΦpos.le) hCL hle1
            have hstepB : δ ^ 2 * Pg / (lowerGamma (t + β) (ε * Real.log 2) * Lp) ≤
                δ ^ 2 * Pg / (lowerGamma (t + β) (ε * Real.log 2) * Lp) *
                  ((s : ℝ) * Y / (ε ^ (t + β) * ε ^ s)) := by
              simpa only [mul_one] using mul_le_mul_of_nonneg_left hone hbC
            have heq : δ ^ 2 * Pg / (lowerGamma (t + β) (ε * Real.log 2) * Lp) *
                  ((s : ℝ) * Y / (ε ^ (t + β) * ε ^ s)) = W * Y * (Pg / Lp) / 4 := by
              rw [hW, Gconst]
              field_simp [hC0ne, hLpne, hεbne, hεsne]
            rw [heq] at hstepB
            exact le_trans hA hstepB
          have hratio : AI / BI ≤ W * Y * (Pg / Lp) / 4 := by
            refine le_trans hUp ?_
            rw [he1]
            exact hcore
          have e2 : AI = AI / BI * BI := by field_simp [hBIne]
          rw [e2]
          exact mul_le_mul_of_nonneg_right hratio hBInn
        have hnode := statopia_math_node_3130454126_6f827a50 t ht π hπ_meas hπ_nonneg hπ_prob
          ε₀ δ β hε₀ hδ hβ hA2 ε hεpos hεhalf hεle hB1 n s hs hns
        rw [hEm, ← hPg, ← hLp, ← hW] at hnode
        rw [← hAO] at hnode
        have h34 : (3 : ENNReal) / 4 = ENNReal.ofReal (((3:ℕ):ℝ) / ((4:ℕ):ℝ)) := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < ((4:ℕ):ℝ)),
            ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
          norm_num
        have hXnn : 0 ≤ W * Y * (Pg / Lp) := mul_nonneg (mul_nonneg hWnn hYnn) hPgnn
        have h3nn : (0 : ℝ) ≤ ((3:ℕ):ℝ) / ((4:ℕ):ℝ) := by norm_num
        have hEq : ENNReal.ofReal
              (W * Y * (Pg / Lp) * BO + ((3:ℕ):ℝ) / ((4:ℕ):ℝ) * (W * Y * (Pg / Lp) * BI)) =
            ENNReal.ofReal W * ENNReal.ofReal Y * ENNReal.ofReal (Pg / Lp) * ENNReal.ofReal BO +
              (3 : ENNReal) / 4 *
                (ENNReal.ofReal W * ENNReal.ofReal Y * ENNReal.ofReal (Pg / Lp)) *
                ENNReal.ofReal BI := by
          rw [ENNReal.ofReal_add (mul_nonneg hXnn hBOnn)
                (mul_nonneg h3nn (mul_nonneg hXnn hBInn)),
              ENNReal.ofReal_mul hXnn,
              ENNReal.ofReal_mul (mul_nonneg hWnn hYnn),
              ENNReal.ofReal_mul hWnn,
              ENNReal.ofReal_mul h3nn,
              ENNReal.ofReal_mul hXnn,
              ENNReal.ofReal_mul (mul_nonneg hWnn hYnn),
              ENNReal.ofReal_mul hWnn,
              ← h34]
          simp only [mul_assoc]
        have hqnn : 0 ≤ W * Y * (Pg / Lp) * BO +
            ((3:ℕ):ℝ) / ((4:ℕ):ℝ) * (W * Y * (Pg / Lp) * BI) :=
          add_nonneg (mul_nonneg hXnn hBOnn) (mul_nonneg h3nn (mul_nonneg hXnn hBInn))
        have hTailreal : AO ≤
            W * Y * (Pg / Lp) * BO + ((3:ℕ):ℝ) / ((4:ℕ):ℝ) * (W * Y * (Pg / Lp) * BI) := by
          refine (ENNReal.ofReal_le_ofReal_iff hqnn).mp ?_
          rw [hEq]
          exact hnode
        have hden2 : 0 < BI + BO := by linarith
        have hdenne : BI + BO ≠ 0 := ne_of_gt hden2
        have hcomb : AI + AO ≤ W * Y * (Pg / Lp) * (BI + BO) := by
          calc AI + AO ≤ (W * Y * (Pg / Lp) / 4) * BI +
                (W * Y * (Pg / Lp) * BO + ((3:ℕ):ℝ) / ((4:ℕ):ℝ) * (W * Y * (Pg / Lp) * BI)) :=
                add_le_add hhead hTailreal
            _ = W * Y * (Pg / Lp) * (BI + BO) := by ring
        have hstep : (AI + AO) / (BI + BO) ≤
            W * Y * (Pg / Lp) * (BI + BO) / (BI + BO) :=
          div_le_div_of_nonneg_right hcomb hden2.le
        have e3 : W * Y * (Pg / Lp) * (BI + BO) / (BI + BO) = W * Y * (Pg / Lp) := by
          rw [mul_div_assoc, div_self hdenne, mul_one]
        rw [e3] at hstep
        exact hstep
      calc Cratio π n t (s : ℝ)
          = ENNReal.ofReal (((∫ α in Set.Ioo (0 : ℝ) ε, α ^ (t + (s : ℝ)) / risingFac α n * π α) +
              (∫ α in Set.Ioi ε, α ^ (t + (s : ℝ)) / risingFac α n * π α)) /
            ((∫ α in Set.Ioo (0 : ℝ) ε, α ^ t / risingFac α n * π α) +
              (∫ α in Set.Ioi ε, α ^ t / risingFac α n * π α))) := hcr2
        _ ≤ ENNReal.ofReal (Gconst t ε δ β * (s : ℝ) / ε ^ s *
              (∫ α in Set.Ioi (0 : ℝ), α ^ (t + (s : ℝ) - 1) * π α) *
              (lowerGamma (t + (s : ℝ) + β) (ε * Real.log (n : ℝ)) /
                (Real.log ((n : ℝ) / (1 + ε))) ^ s)) := ENNReal.ofReal_le_ofReal hT
        _ = ENNReal.ofReal (Gconst t ε δ β * (s : ℝ) / ε ^ s) *
              ENNReal.ofReal (∫ α in Set.Ioi (0 : ℝ), α ^ (t + (s : ℝ) - 1) * π α) *
              ENNReal.ofReal (lowerGamma (t + (s : ℝ) + β) (ε * Real.log (n : ℝ)) /
                (Real.log ((n : ℝ) / (1 + ε))) ^ s) := by
            rw [ENNReal.ofReal_mul (mul_nonneg hGE hEnn), ENNReal.ofReal_mul hGE]
  exact ⟨hlow, hup⟩
  /- @proof-region region.root.ddabacc30f97 end -/

/-- The source's own parameter domain: `t` is the number of mixture components,
hence a positive integer. This is the integer-`t` specialization of the sealed
real-`t` statement, with the source's range `0 < s ≤ n - t` written as
`s + t ≤ n`, and it is proved (not assumed). -/
theorem paper_3208f098a8f94aafb53ad0b136d14110_nat
    (k : ℕ) (hk : 1 ≤ k)
    (π : ℝ → ℝ) (hπ_meas : Measurable π)
    (hπ_nonneg : ∀ α ∈ Set.Ioi (0 : ℝ), 0 ≤ π α)
    (hπ_prob : ∫⁻ α in Set.Ioi (0 : ℝ), ENNReal.ofReal (π α) = 1)
    (ε₀ δ β : ℝ) (hε₀ : 0 < ε₀) (hδ : 0 < δ) (hβ : 0 < β)
    (hA2 : ∀ α ∈ Set.Ioo (0 : ℝ) ε₀, δ⁻¹ * α ^ β ≤ π α ∧ π α ≤ δ * α ^ β) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧ ε ≤ ε₀ ∧
      δ * ε ^ (β + 1) / (β + 1) ≤ 1 / 2 ∧
      2 * δ ^ 2 * (Real.exp 1)⁻¹ * ((k : ℝ) + β) / ((k : ℝ) + 1 + β) *
          ε ^ (-(β + 1)) ≥ 2 ∧
      2 * δ ^ 2 * (Real.exp 1)⁻¹ * ((k : ℝ) + β) /
          (((k : ℝ) + 1 + β) * (Real.log 2) ^ ((k : ℝ) + β)) *
          ε ^ (-((k : ℝ) + 2 * β + 1)) ≥ 2 ∧
      ∃ F : ℝ, 0 < F ∧
        ∀ n s : ℕ, 1 ≤ n → 1 ≤ s → s + k ≤ n →
          ENNReal.ofReal
              (F * lowerGamma ((k : ℝ) + (s : ℝ) + β) (ε * Real.log (n : ℝ)) /
                (Real.log (n : ℝ) + 1) ^ s) ≤
            Cratio π n (k : ℝ) (s : ℝ) ∧
          Cratio π n (k : ℝ) (s : ℝ) ≤
            ENNReal.ofReal (Gconst (k : ℝ) ε δ β * (s : ℝ) / ε ^ s) *
              priorMoment π ((k : ℝ) + (s : ℝ) - 1) *
                ENNReal.ofReal
                  (lowerGamma ((k : ℝ) + (s : ℝ) + β) (ε * Real.log (n : ℝ)) /
                    (Real.log ((n : ℝ) / (1 + ε))) ^ s) := by
  obtain ⟨ε, hεpos, hεhalf, hεle, hB1, hB2, hB3, F, hF, hbound⟩ :=
    paper_3208f098a8f94aafb53ad0b136d14110 (k : ℝ) (by exact_mod_cast hk) π hπ_meas
      hπ_nonneg hπ_prob ε₀ δ β hε₀ hδ hβ hA2
  refine ⟨ε, hεpos, hεhalf, hεle, hB1, hB2, hB3, F, hF, ?_⟩
  intro n s hn hs hrange
  have hcast : ((s + k : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast hrange
  have hrange' : (s : ℝ) + (k : ℝ) ≤ (n : ℝ) := by
    simpa [Nat.cast_add] using hcast
  exact hbound n s hn hs hrange'




end Statlib.Imported

-- Paper root revision b5d78ae4-d1fb-461f-8187-61aa084419d2

#print axioms Statlib.Imported.paper_3208f098a8f94aafb53ad0b136d14110
#print axioms Statlib.Imported.paper_3208f098a8f94aafb53ad0b136d14110_nat
