import ProverJobs.job_paper_a9a2ab5d4e094509b2cdb371b3b02f1c.Vocabulary
import ProverJobs.job_paper_a9a2ab5d4e094509b2cdb371b3b02f1c.ProvedNodes
import ProverJobs.job_paper_a9a2ab5d4e094509b2cdb371b3b02f1c.Base

namespace PaperProofTasks.job_paper_a9a2ab5d4e094509b2cdb371b3b02f1c

namespace Statlib.Imported
open _root_.Statlib
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
noncomputable section

theorem paper_a9a2ab5d4e094509b2cdb371b3b02f1c
    (d : ℕ) (hd : 0 < d)
    (π : Measure (HMCState d)) (w : HMCState d → ℝ≥0∞) (hw : Measurable w)
    (hπdens : π = volume.withDensity w) (hπfin : IsFiniteMeasure π)
    (P Q : Kernel (HMCState d) (HMCState d)) [IsMarkovKernel P] [IsMarkovKernel Q]
    (α : HMCState d → HMCState d → ℝ) (r : HMCState d → ℝ)
    (hMH : IsMHType P Q α r) (hesssup : essSup r π = 1) :
    ¬ ∃ ρ : ℝ, ρ < 1 ∧ ∃ M : HMCState d → ℝ≥0∞,
      (∀ᵐ x ∂π, M x ≠ ⊤) ∧
      (∀ᵐ x ∂π, ∀ n : ℕ, 1 ≤ n →
        (tvDist ((P ^ n) x) π).toReal ≤ (M x).toReal * ρ ^ n)
:= by
  /- @proof-region region.root.a328fac56974 begin -/
  rintro ⟨ρ, hρ, M, hMfin, hgeo⟩
  haveI : IsFiniteMeasure π := hπfin
  have hρmax : max ρ 0 < 1 := by
    rcases le_total ρ 0 with h | h
    · rw [max_eq_right h]
      norm_num
    · rw [max_eq_left h]
      exact hρ
  have hr_nonneg : ∀ x : HMCState d, 0 ≤ r x := by
    intro x
    haveI : IsProbabilityMeasure (Q x) := IsMarkovKernel.is_probability_measure' x
    have hα_meas : Measurable (fun y => α x y) :=
      hMH.measurable_alpha.comp (measurable_const.prodMk measurable_id)
    have hInt : Integrable (fun y => α x y) (Q x) := by
      refine MeasureTheory.Integrable.of_bound hα_meas.aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hMH.alpha_nonneg x y)]
      exact hMH.alpha_le_one x y
    have hle_one : ∫ y, α x y ∂(Q x) ≤ 1 := by
      have h1 : ∫ y, α x y ∂(Q x) ≤ ∫ _y, (1 : ℝ) ∂(Q x) :=
        integral_mono hInt (integrable_const 1) fun y => hMH.alpha_le_one x y
      simpa using h1
    have h0 : 0 ≤ ∫ y, α x y ∂(Q x) := integral_nonneg fun y => hMH.alpha_nonneg x y
    rw [hMH.r_eq x]
    linarith
  have hpi_atom : ∀ x : HMCState d, π {x} = 0 := by
    intro x
    haveI hne : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    haveI hnz : NeZero d := ⟨by omega⟩
    have hvol : (volume : Measure (HMCState d)) {x} = 0 := by
      first
        | simp
        | exact MeasureTheory.measure_singleton x
        | exact NoAtoms.measure_singleton (inferInstance) x
    have hzero : (volume : Measure (HMCState d)).restrict ({x} : Set (HMCState d)) = 0 := by
      rw [← Measure.measure_univ_eq_zero]
      simp [hvol]
    rw [hπdens, MeasureTheory.withDensity_apply w (measurableSet_singleton x), hzero]
    simp
  have hreturn : ∀ (x : HMCState d) (n : ℕ), 1 ≤ n →
      (P ^ n) x {x} ≥ (ENNReal.ofReal (r x)) ^ n := by
    have hsingle : ∀ x : HMCState d, ENNReal.ofReal (r x) ≤ P x {x} := by
      intro x
      have hpoint : P x {x} = (Q x).withDensity (fun y => ENNReal.ofReal (α x y)) {x}
          + ENNReal.ofReal (r x) := by
        have h := congrArg (fun μ : Measure (HMCState d) => μ ({x} : Set (HMCState d)))
          (hMH.decomp x)
        simpa using h
      rw [hpoint]
      exact le_trans (le_of_eq (zero_add (ENNReal.ofReal (r x))).symm)
        (add_le_add (zero_le _) le_rfl)
    have hsingle_int : ∀ (x : HMCState d) (μ : Measure (HMCState d)),
        ∫⁻ y, ({x} : Set (HMCState d)).indicator (fun y => ENNReal.ofReal (r y)) y ∂μ
          = ENNReal.ofReal (r x) * μ {x} := by
      intro x μ
      rw [lintegral_indicator (measurableSet_singleton x)]
      simp [mul_comm]
    intro x n hn
    induction n with
    | zero => exact absurd hn (by omega)
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        simpa using hsingle x
      · have hrec : (ENNReal.ofReal (r x)) ^ k ≤ (P ^ k) x {x} := ih hk
        rw [ProbabilityTheory.Kernel.pow_succ_apply_eq_lintegral P k x
          (measurableSet_singleton x)]
        calc (ENNReal.ofReal (r x)) ^ (k + 1)
            = ENNReal.ofReal (r x) * (ENNReal.ofReal (r x)) ^ k := by rw [pow_succ']
          _ ≤ ENNReal.ofReal (r x) * ((P ^ k) x {x}) := mul_le_mul_left' hrec _
          _ = ∫⁻ y, ({x} : Set (HMCState d)).indicator
                (fun y => ENNReal.ofReal (r y)) y ∂((P ^ k) x) :=
              (hsingle_int x ((P ^ k) x)).symm
          _ ≤ ∫⁻ y, (P y) {x} ∂((P ^ k) x) := by
              apply lintegral_mono
              intro y
              by_cases hy : y = x
              · rw [Set.indicator_of_mem (Set.mem_singleton_iff.mpr hy), hy]
                exact hsingle x
              · rw [Set.indicator_of_notMem (by simpa using hy)]
                exact zero_le _
  have hae : ∀ᵐ x ∂π, r x ≤ max ρ 0 := by
    filter_upwards [hgeo] with x hx
    refine statopia_math_node_787223495_7db0105c ρ (M x).toReal (r x) hρ ENNReal.toReal_nonneg
      (hr_nonneg x) (fun n hn => ?_)
    exact le_trans (statopia_math_node_1980195792_bc5cfc4b π P r hr_nonneg hpi_atom hreturn x n hn)
      (hx n hn)
  have hle : essSup r π ≤ max ρ 0 := by
    by_cases hπ0 : π = 0
    · have hset : {a : ℝ | r ≤ᶠ[ae π] fun _ => a} = Set.univ := by
        ext a
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        rw [hπ0]
        show ∀ᵐ x ∂(0 : Measure (HMCState d)), r x ≤ a
        rw [ae_iff]
        simp
      show sInf {a : ℝ | r ≤ᶠ[ae π] fun _ => a} ≤ max ρ 0
      rw [hset, Real.sInf_univ]
      exact le_max_right ρ 0
    · have hπuniv : π Set.univ ≠ 0 := fun h => hπ0 (Measure.measure_univ_eq_zero.mp h)
      have hbd : BddBelow {a : ℝ | r ≤ᶠ[ae π] fun _ => a} := by
        refine ⟨0, ?_⟩
        intro a ha
        by_contra hlt
        have ha' : a < 0 := not_le.mp hlt
        have hzero : π {x | ¬ r x ≤ a} = 0 := ae_iff.mp ha
        have huniv : {x : HMCState d | ¬ r x ≤ a} = Set.univ := by
          apply Set.eq_univ_of_forall
          intro x
          simp only [Set.mem_setOf_eq]
          exact not_le.mpr (lt_of_lt_of_le ha' (hr_nonneg x))
        rw [huniv] at hzero
        exact hπuniv hzero
      unfold essSup
      exact csInf_le hbd hae
  rw [hesssup] at hle
  linarith
  /- @proof-region region.root.a328fac56974 end -/

end

