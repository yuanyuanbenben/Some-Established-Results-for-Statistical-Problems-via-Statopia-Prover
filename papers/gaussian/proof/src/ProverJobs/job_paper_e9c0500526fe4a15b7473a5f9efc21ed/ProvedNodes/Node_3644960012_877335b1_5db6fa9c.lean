import ProverJobs.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Vocabulary
import ProverJobs.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Base

namespace PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed

open _root_.PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
universe u₀ u₁

set_option autoImplicit false in
theorem statopia_math_node_3644960012_877335b1 : ∀ (Om : Type) [MeasurableSpace Om] (P : Measure Om) [IsProbabilityMeasure P]
    (xi : Om → ℝ) (hxi : Measurable xi) (c0 : ℝ) (hc0 : 0 < c0)
    (horlicz : Statlib.StatFoundation.Vocabulary.orliczNorm 1 xi P ≤ ENNReal.ofReal c0),
    ∫⁻ om, ENNReal.ofReal (Real.exp (|xi om| / c0)) ∂P ≤ (2 : ENNReal) := by
  /- @proof-region region.target-node.session.20083316cf83af72 begin -/
  intro Om _ P _ xi hxi c0 hc0 horlicz
  have hpsi : ∀ y : ℝ, Statlib.StatFoundation.Vocabulary.psiOrlicz 1 y = Real.exp y - 1 := by
    intro y
    unfold Statlib.StatFoundation.Vocabulary.psiOrlicz
    rw [Real.rpow_one]
  have hExpEq : ∀ y : ℝ, 0 ≤ y →
      ENNReal.ofReal (Real.exp y) = ENNReal.ofReal (Statlib.StatFoundation.Vocabulary.psiOrlicz 1 y) + 1 := by
    intro y hy
    rw [hpsi y]
    have h1 : (0:ℝ) ≤ Real.exp y - 1 := by
      have := Real.one_le_exp hy
      linarith
    have key := ENNReal.ofReal_add h1 (by norm_num : (0:ℝ) ≤ 1)
    rw [ENNReal.ofReal_one] at key
    rw [show Real.exp y - 1 + 1 = Real.exp y from by ring] at key
    exact key
  have hIntegral : ∀ t : ENNReal, 0 < t →
      ∫⁻ om, ENNReal.ofReal (Real.exp (|xi om| / t.toReal)) ∂P
        = ∫⁻ om, ENNReal.ofReal (Statlib.StatFoundation.Vocabulary.psiOrlicz 1 (|xi om| / t.toReal)) ∂P + 1 := by
    intro t ht
    have hmeas_psi : Measurable (fun om => ENNReal.ofReal (Statlib.StatFoundation.Vocabulary.psiOrlicz 1 (|xi om| / t.toReal))) := by
      apply Measurable.ennreal_ofReal
      have hcont : Continuous (fun y : ℝ => Statlib.StatFoundation.Vocabulary.psiOrlicz 1 y) := by
        have hfun : (fun y : ℝ => Statlib.StatFoundation.Vocabulary.psiOrlicz 1 y) = (fun y => Real.exp y - 1) := by
          funext y; exact hpsi y
        rw [hfun]; continuity
      exact hcont.measurable.comp (hxi.abs.div measurable_const)
    have hcongr : (∫⁻ om, ENNReal.ofReal (Real.exp (|xi om| / t.toReal)) ∂P)
        = ∫⁻ om, (ENNReal.ofReal (Statlib.StatFoundation.Vocabulary.psiOrlicz 1 (|xi om| / t.toReal)) + 1) ∂P := by
      apply lintegral_congr
      intro om
      exact hExpEq _ (div_nonneg (abs_nonneg _) ENNReal.toReal_nonneg)
    rw [hcongr, lintegral_add_left hmeas_psi (fun _ => (1 : ENNReal)), lintegral_one, measure_univ]
  set S : Set ENNReal :=
    {t : ENNReal | 0 < t ∧ ∫⁻ om, ENNReal.ofReal (Statlib.StatFoundation.Vocabulary.psiOrlicz 1 (|xi om| / t.toReal)) ∂P ≤ 1} with hSdef
  have horlicz' : sInf S ≤ ENNReal.ofReal c0 := by
    unfold Statlib.StatFoundation.Vocabulary.orliczNorm at horlicz
    exact horlicz
  have htopS : (⊤ : ENNReal) ∈ S := by
    rw [hSdef, Set.mem_setOf_eq]
    refine ⟨ENNReal.zero_lt_top, ?_⟩
    simp [hpsi]
  have hup : ∀ u v : ENNReal, u ∈ S → u ≤ v → v ≠ ⊤ → v ∈ S := by
    intro u v hu huv hvtop
    rw [hSdef, Set.mem_setOf_eq] at hu ⊢
    obtain ⟨hu0, hu1⟩ := hu
    have hutop : u ≠ ⊤ := by
      intro h
      exact hvtop (by rw [h] at huv; exact top_le_iff.mp huv)
    have huv' : u.toReal ≤ v.toReal := ENNReal.toReal_mono hvtop huv
    have hu_pos : 0 < u.toReal := ENNReal.toReal_pos (ne_of_gt hu0) hutop
    refine ⟨lt_of_lt_of_le hu0 huv, ?_⟩
    calc ∫⁻ om, ENNReal.ofReal (Statlib.StatFoundation.Vocabulary.psiOrlicz 1 (|xi om| / v.toReal)) ∂P
        ≤ ∫⁻ om, ENNReal.ofReal (Statlib.StatFoundation.Vocabulary.psiOrlicz 1 (|xi om| / u.toReal)) ∂P := by
          apply lintegral_mono
          intro om
          apply ENNReal.ofReal_le_ofReal
          have hinv : (v.toReal)⁻¹ ≤ (u.toReal)⁻¹ := by
            simpa only [one_div] using one_div_le_one_div_of_le hu_pos huv'
          have hratio : |xi om| / v.toReal ≤ |xi om| / u.toReal := by
            calc |xi om| / v.toReal = |xi om| * (v.toReal)⁻¹ := by rw [div_eq_mul_inv]
              _ ≤ |xi om| * (u.toReal)⁻¹ := mul_le_mul_of_nonneg_left hinv (abs_nonneg _)
              _ = |xi om| / u.toReal := by rw [div_eq_mul_inv]
          calc Statlib.StatFoundation.Vocabulary.psiOrlicz 1 (|xi om| / v.toReal)
              = Real.exp (|xi om| / v.toReal) - 1 := hpsi _
            _ ≤ Real.exp (|xi om| / u.toReal) - 1 := by
                  have := Real.exp_le_exp.mpr hratio; linarith
            _ = Statlib.StatFoundation.Vocabulary.psiOrlicz 1 (|xi om| / u.toReal) := (hpsi _).symm
      _ ≤ 1 := hu1
  have hS_mem : ∀ t : ENNReal, ENNReal.ofReal c0 < t → t ∈ S := by
    intro t ht
    by_contra htS
    have ht_ne_top : t ≠ ⊤ := by
      intro h
      apply htS
      rw [h]
      exact htopS
    have ht_le : t ≤ sInf S := by
      apply le_sInf
      intro u hu
      by_contra hcon
      rw [not_le] at hcon
      exact htS (hup u t hu (le_of_lt hcon) ht_ne_top)
    exact (not_le.mpr ht) (le_trans ht_le horlicz')
  have hexp_bound : ∀ t : ENNReal, 0 < t → t ∈ S →
      ∫⁻ om, ENNReal.ofReal (Real.exp (|xi om| / t.toReal)) ∂P ≤ 2 := by
    intro t ht htS
    rw [hSdef, Set.mem_setOf_eq] at htS
    obtain ⟨_, hpsi_le⟩ := htS
    rw [hIntegral t ht]
    calc ∫⁻ om, ENNReal.ofReal (Statlib.StatFoundation.Vocabulary.psiOrlicz 1 (|xi om| / t.toReal)) ∂P + 1
        ≤ 1 + 1 := add_le_add hpsi_le le_rfl
      _ = 2 := by norm_num
  let d : ℕ → ℝ := fun n => c0 + 1 / ((n:ℝ) + 1)
  have hdn_pos : ∀ n : ℕ, 0 < d n := by
    intro n
    have h : d n = c0 + 1 / ((n:ℝ) + 1) := rfl
    rw [h]; positivity
  have hd_mono : ∀ n m : ℕ, n ≤ m → d m ≤ d n := by
    intro n m hnm
    have hn : d n = c0 + 1 / ((n:ℝ) + 1) := rfl
    have hm : d m = c0 + 1 / ((m:ℝ) + 1) := rfl
    rw [hn, hm]
    have h1 : (1:ℝ) / ((m:ℝ) + 1) ≤ 1 / ((n:ℝ) + 1) := by
      have hnm' : (n:ℝ) + 1 ≤ (m:ℝ) + 1 := by
        have : (n:ℝ) ≤ (m:ℝ) := by exact_mod_cast hnm
        linarith
      exact one_div_le_one_div_of_le (by positivity) hnm'
    linarith
  have hstep : ∀ n : ℕ,
      (fun om => ENNReal.ofReal (Real.exp (|xi om| / d n)))
        ≤ (fun om => ENNReal.ofReal (Real.exp (|xi om| / d (n+1)))) := by
    intro n om
    apply ENNReal.ofReal_le_ofReal
    have hpos : 0 < d (n+1) := hdn_pos (n+1)
    have hle : d (n+1) ≤ d n := hd_mono n (n+1) (Nat.le_succ n)
    have hinv : (d n)⁻¹ ≤ (d (n+1))⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hpos hle
    have hratio : |xi om| / d n ≤ |xi om| / d (n+1) := by
      calc |xi om| / d n = |xi om| * (d n)⁻¹ := by rw [div_eq_mul_inv]
        _ ≤ |xi om| * (d (n+1))⁻¹ := mul_le_mul_of_nonneg_left hinv (abs_nonneg _)
        _ = |xi om| / d (n+1) := by rw [div_eq_mul_inv]
    exact Real.exp_le_exp.mpr hratio
  have hmeas : ∀ n : ℕ, Measurable (fun om => ENNReal.ofReal (Real.exp (|xi om| / d n))) := by
    intro n
    apply Measurable.ennreal_ofReal
    exact Real.continuous_exp.measurable.comp (hxi.abs.div measurable_const)
  have hbound : ∀ n : ℕ,
      ∫⁻ om, ENNReal.ofReal (Real.exp (|xi om| / d n)) ∂P ≤ 2 := by
    intro n
    have hdn : 0 < d n := hdn_pos n
    have htnS : ENNReal.ofReal (d n) ∈ S := by
      apply hS_mem
      rw [ENNReal.ofReal_lt_ofReal_iff hdn]
      have h : c0 < c0 + 1 / ((n:ℝ) + 1) := by
        have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
        linarith
      exact h
    have hpos : 0 < ENNReal.ofReal (d n) := ENNReal.ofReal_pos.mpr hdn
    have key := hexp_bound (ENNReal.ofReal (d n)) hpos htnS
    rwa [ENNReal.toReal_ofReal (le_of_lt hdn)] at key
  have h_tendsto : ∀ om, Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (|xi om| / d n))) Filter.atTop
      (nhds (ENNReal.ofReal (Real.exp (|xi om| / c0)))) := by
    intro om
    have hdT : Filter.Tendsto d Filter.atTop (nhds c0) := by
      have h1 : Filter.Tendsto (fun n : ℕ => (1:ℝ) / ((n:ℝ) + 1)) Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 : Filter.Tendsto (fun n : ℕ => c0 + 1 / ((n:ℝ) + 1)) Filter.atTop (nhds (c0 + 0)) :=
        tendsto_const_nhds.add h1
      simpa [d] using h2
    have hdiv : Filter.Tendsto (fun n : ℕ => |xi om| / d n) Filter.atTop (nhds (|xi om| / c0)) :=
      tendsto_const_nhds.div hdT (ne_of_gt hc0)
    have hexp : Filter.Tendsto (fun n : ℕ => Real.exp (|xi om| / d n)) Filter.atTop (nhds (Real.exp (|xi om| / c0))) :=
      (Real.continuous_exp.tendsto (|xi om| / c0)).comp hdiv
    exact (ENNReal.continuous_ofReal.tendsto (Real.exp (|xi om| / c0))).comp hexp
  have hlim : Filter.Tendsto (fun n : ℕ => ∫⁻ om, ENNReal.ofReal (Real.exp (|xi om| / d n)) ∂P) Filter.atTop
      (nhds (∫⁻ om, ENNReal.ofReal (Real.exp (|xi om| / c0)) ∂P)) :=
    lintegral_tendsto_of_tendsto_of_monotone
      (f := fun n om => ENNReal.ofReal (Real.exp (|xi om| / d n)))
      (F := fun om => ENNReal.ofReal (Real.exp (|xi om| / c0)))
      (fun n => (hmeas n).aemeasurable)
      (Filter.Eventually.of_forall (fun om => monotone_nat_of_le_succ (fun n => hstep n om)))
      (Filter.Eventually.of_forall h_tendsto)
  have hfinal : ∫⁻ om, ENNReal.ofReal (Real.exp (|xi om| / c0)) ∂P ≤ 2 :=
    le_of_tendsto_of_tendsto' hlim tendsto_const_nhds hbound
  exact hfinal

  /- @proof-region region.target-node.session.20083316cf83af72 end -/

end
end Statlib.Imported

