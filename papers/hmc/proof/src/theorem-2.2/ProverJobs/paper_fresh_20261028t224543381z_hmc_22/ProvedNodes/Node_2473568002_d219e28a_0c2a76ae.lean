import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.Vocabulary
import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.Base

namespace PaperProofTasks.paper_fresh_20261028t224543381z_hmc_22

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open _root_.PaperProofTasks.paper_fresh_20261028t224543381z_hmc_22.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace Statlib.Imported


set_option autoImplicit false in
theorem statopia_math_node_2473568002_d219e28a : ∀ (d : ℕ) (hd : 0 < d)
    (P : HMCState d → Measure (HMCState d))
    (hP_prob : ∀ x : HMCState d, IsProbabilityMeasure (P x))
    (hP_meas : ∀ A : Set (HMCState d), MeasurableSet A →
      Measurable fun y : HMCState d => P y A)
    (π : Measure (HMCState d)) [IsProbabilityMeasure π]
    (hπ_atom : ∀ x : HMCState d, π {x} = 0)
    (hS : ∀ η : ℝ, 0 < η → η < 1 → ∀ N : Set (HMCState d), π N = 0 →
      ∃ x : HMCState d, ENNReal.ofReal (1 - η) ≤ P x {x} ∧ x ∉ N),
    ¬ IsGeometricallyErgodic P π := by
  /- @proof-region region.target-node.session.d7a7e38b1aa380ff begin -/
  intro d hd P hP_prob hP_meas π _ hπ_atom hS hge
  obtain ⟨ρ, hρlt1, Mfun, hMfin, hMbd⟩ := hge
  let E : Set (HMCState d) :=
    {x | ¬ (Mfun x < ⊤ ∧ ∀ n : ℕ, tvDist (kernelPow P n x) π ≤ Mfun x * ENNReal.ofReal (ρ ^ n))}
  have hE : π E = 0 := by
    show π {x | ¬ (Mfun x < ⊤ ∧ ∀ n : ℕ, tvDist (kernelPow P n x) π ≤ Mfun x * ENNReal.ofReal (ρ ^ n))} = 0
    exact MeasureTheory.ae_iff.mp (hMfin.and hMbd)
  obtain ⟨η, hηpos, hηlt1, hηρ⟩ : ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ρ < 1 - η := by
    refine ⟨min (1/2) ((1 - ρ)/2), ?_, ?_, ?_⟩
    · exact lt_min (by norm_num) (by linarith)
    · exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    · have h1 : min (1/2:ℝ) ((1-ρ)/2) ≤ (1-ρ)/2 := min_le_right _ _
      linarith
  obtain ⟨xstar, hxself, hxnot⟩ := hS η hηpos hηlt1 E hE
  have hxprops : Mfun xstar < ⊤ ∧ ∀ n : ℕ, tvDist (kernelPow P n xstar) π ≤ Mfun xstar * ENNReal.ofReal (ρ ^ n) := by
    simpa only [E, Set.mem_setOf_eq, not_not] using hxnot
  obtain ⟨hMfin_star, hMbd_star⟩ := hxprops
  have hpos1 : (0:ℝ) < 1 - η := by linarith
  have hπstar : π {xstar} = 0 := hπ_atom xstar
  have hpow : ∀ n : ℕ, ENNReal.ofReal ((1 - η) ^ n) ≤ (kernelPow P n xstar) {xstar} := by
    intro n
    induction n with
    | zero =>
        show ENNReal.ofReal ((1 - η) ^ 0) ≤ (Measure.dirac xstar) {xstar}
        rw [MeasureTheory.Measure.dirac_apply_of_mem (Set.mem_singleton xstar)]
        simp
    | succ n ih =>
        have hbind : (kernelPow P (n + 1) xstar) {xstar}
            = ∫⁻ y, P y {xstar} ∂(kernelPow P n xstar) := by
          have hPm : Measurable P := MeasureTheory.Measure.measurable_of_measurable_coe P hP_meas
          exact MeasureTheory.Measure.bind_apply (MeasurableSet.singleton xstar) hPm.aemeasurable
        have hstep : P xstar {xstar} * (kernelPow P n xstar) {xstar}
            ≤ (kernelPow P (n + 1) xstar) {xstar} := by
          rw [hbind]
          calc P xstar {xstar} * (kernelPow P n xstar) {xstar}
              = ∫⁻ y in {xstar}, P y {xstar} ∂(kernelPow P n xstar) :=
                (MeasureTheory.lintegral_singleton (fun y => P y {xstar}) xstar).symm
            _ ≤ ∫⁻ y, P y {xstar} ∂(kernelPow P n xstar) := by
                have hsub := MeasureTheory.lintegral_mono_set
                  (μ := kernelPow P n xstar) (f := fun y => P y {xstar}) (Set.subset_univ {xstar})
                simpa only [Measure.restrict_univ] using hsub
        calc ENNReal.ofReal ((1 - η) ^ (n + 1))
            = ENNReal.ofReal ((1 - η) ^ n) * ENNReal.ofReal (1 - η) := by
                rw [pow_succ, ENNReal.ofReal_mul (pow_nonneg hpos1.le n)]
          _ ≤ (kernelPow P n xstar) {xstar} * P xstar {xstar} := by gcongr
          _ = P xstar {xstar} * (kernelPow P n xstar) {xstar} := by rw [mul_comm]
          _ ≤ (kernelPow P (n + 1) xstar) {xstar} := hstep
  have hPm : Measurable P := MeasureTheory.Measure.measurable_of_measurable_coe P hP_meas
  have hprob : ∀ n : ℕ, (kernelPow P n xstar) Set.univ = 1 := by
    intro n
    induction n with
    | zero =>
        show (Measure.dirac xstar) Set.univ = 1
        simp [MeasureTheory.Measure.dirac_apply]
    | succ n ih =>
        show ((kernelPow P n xstar).bind P) Set.univ = 1
        rw [MeasureTheory.Measure.bind_apply (MeasurableSet.univ) hPm.aemeasurable]
        have hone : ∀ y : HMCState d, P y Set.univ = 1 := fun y => (hP_prob y).measure_univ
        simp only [hone]
        rw [MeasureTheory.lintegral_one]
        exact ih
  have hne_top : ∀ n : ℕ, (kernelPow P n xstar) {xstar} ≠ ⊤ := by
    intro n
    have h1 : (kernelPow P n xstar) {xstar} ≤ (kernelPow P n xstar) Set.univ :=
      measure_mono (Set.subset_univ {xstar})
    rw [hprob n] at h1
    exact ne_top_of_le_ne_top ENNReal.one_ne_top h1
  have htv : ∀ n : ℕ, ENNReal.ofReal ((1 - η) ^ n) ≤ tvDist (kernelPow P n xstar) π := by
    intro n
    have hmeas : Measurable (Set.indicator {xstar} (fun _ => (1:ℝ))) :=
      measurable_const.indicator (MeasurableSet.singleton xstar)
    have hbound : ∀ x, |Set.indicator {xstar} (fun _ => (1:ℝ)) x| ≤ 1 := by
      intro x
      by_cases hx : x ∈ ({xstar} : Set (HMCState d))
      · rw [Set.indicator_of_mem hx]; simp
      · rw [Set.indicator_of_notMem hx]; simp
    have hgen : ∀ (μ : Measure (HMCState d)),
        ∫ x, Set.indicator {xstar} (fun _ => (1:ℝ)) x ∂μ = (μ {xstar}).toReal := by
      intro μ
      have hpt : ∀ a : HMCState d,
          (Set.indicator {xstar} (fun _ => (1:ℝ≥0∞)) a).toReal = Set.indicator {xstar} (fun _ => (1:ℝ)) a := by
        intro a
        by_cases ha : a ∈ ({xstar} : Set (HMCState d))
        · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha]; simp
        · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha]; simp
      have hfin : ∀ᵐ x ∂μ, Set.indicator {xstar} (fun _ => (1:ℝ≥0∞)) x < ⊤ := by
        apply Filter.Eventually.of_forall
        intro x
        by_cases hx : x ∈ ({xstar} : Set (HMCState d))
        · rw [Set.indicator_of_mem hx]; simp
        · rw [Set.indicator_of_notMem hx]; simp
      have hto := MeasureTheory.integral_toReal
        (μ := μ) (f := Set.indicator {xstar} (fun _ => (1:ℝ≥0∞)))
        (measurable_const.indicator (MeasurableSet.singleton xstar)).aemeasurable hfin
      simp_rw [← hpt]
      rw [hto]
      rw [MeasureTheory.lintegral_indicator_const (MeasurableSet.singleton xstar) (1:ℝ≥0∞)]
      simp
    have hI1 := hgen (kernelPow P n xstar)
    have hI2 := hgen π
    have hle : ENNReal.ofReal |(∫ x, Set.indicator {xstar} (fun _ => (1:ℝ)) x ∂(kernelPow P n xstar)) - ∫ x, Set.indicator {xstar} (fun _ => (1:ℝ)) x ∂π| ≤ tvDist (kernelPow P n xstar) π :=
      le_iSup (fun f : {g : HMCState d → ℝ // Measurable g ∧ ∀ x, |g x| ≤ 1} =>
        ENNReal.ofReal |(∫ x, f.1 x ∂(kernelPow P n xstar)) - ∫ x, f.1 x ∂π|)
        ⟨Set.indicator {xstar} (fun _ => (1:ℝ)), hmeas, hbound⟩
    calc ENNReal.ofReal ((1 - η) ^ n)
        ≤ ENNReal.ofReal ((kernelPow P n xstar) {xstar}).toReal := by
          apply ENNReal.ofReal_le_ofReal
          have h2 := ENNReal.toReal_mono (hne_top n) (hpow n)
          rwa [ENNReal.toReal_ofReal (pow_nonneg hpos1.le n)] at h2
      _ = ENNReal.ofReal |(∫ x, Set.indicator {xstar} (fun _ => (1:ℝ)) x ∂(kernelPow P n xstar)) - ∫ x, Set.indicator {xstar} (fun _ => (1:ℝ)) x ∂π| := by
          rw [hI1, hI2, hπstar, ENNReal.toReal_zero, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg]
      _ ≤ tvDist (kernelPow P n xstar) π := hle
  have hupper : ∀ n : ℕ, ENNReal.ofReal ((1 - η) ^ n) ≤ Mfun xstar * ENNReal.ofReal (ρ ^ n) :=
    fun n => le_trans (htv n) (hMbd_star n)
  by_cases hρ : ρ ≤ 0
  · have h1 := hupper 1
    rw [pow_one, pow_one] at h1
    have hρofreal : ENNReal.ofReal ρ = 0 := by
      rw [ENNReal.ofReal_eq_zero]; exact hρ
    rw [hρofreal, mul_zero] at h1
    have hpos : 0 < ENNReal.ofReal (1 - η) := ENNReal.ofReal_pos.mpr hpos1
    exact absurd h1 (not_le.mpr hpos)
  · have hρpos : 0 < ρ := not_le.mp hρ
    have hm_ne : Mfun xstar ≠ ⊤ := ne_of_lt hMfin_star
    set m : ℝ := (Mfun xstar).toReal with hmdef
    have hMfun_eq : Mfun xstar = ENNReal.ofReal m := (ENNReal.ofReal_toReal hm_ne).symm
    have hmnonneg : 0 ≤ m := ENNReal.toReal_nonneg
    have hc_gt : 1 < (1 - η)/ρ := by
      rw [lt_div_iff₀ hρpos]; linarith
    have hbd : ∀ n : ℕ, ((1 - η)/ρ)^n ≤ m := by
      intro n
      have hh := hupper n
      rw [hMfun_eq, ← ENNReal.ofReal_mul hmnonneg] at hh
      rw [ENNReal.ofReal_le_ofReal_iff (mul_nonneg hmnonneg (pow_nonneg hρpos.le n))] at hh
      rw [div_pow]
      exact (div_le_iff₀ (pow_pos hρpos n)).mpr hh
    have hev : ∀ᶠ n : ℕ in Filter.atTop, m < ((1 - η)/ρ)^n :=
      (tendsto_pow_atTop_atTop_of_one_lt hc_gt).eventually (eventually_gt_atTop m)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
    have hlt : m < ((1 - η)/ρ)^N := hN N le_rfl
    linarith [hbd N]
  /- @proof-region region.target-node.session.d7a7e38b1aa380ff end -/

end Statlib.Imported

end

