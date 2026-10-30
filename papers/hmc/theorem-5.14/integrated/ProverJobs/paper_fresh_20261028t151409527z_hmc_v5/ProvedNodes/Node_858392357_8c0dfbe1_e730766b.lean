import ProverJobs.paper_fresh_20261028t151409527z_hmc_v5.Vocabulary
import ProverJobs.paper_fresh_20261028t151409527z_hmc_v5.Base
import ProverJobs.paper_fresh_20261028t151409527z_hmc_v5.ProvedNodes.Node_2756182807_18c8f00c_127f3f92
import ProverJobs.paper_fresh_20261028t151409527z_hmc_v5.ProvedNodes.Node_868581166_a5ae0410_0502f1f7

namespace PaperProofTasks.paper_fresh_20261028t151409527z_hmc_v5


open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
open _root_.PaperProofTasks.paper_fresh_20261028t151409527z_hmc_v5.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
namespace Statlib.Imported
open _root_.Statlib

set_option autoImplicit false in
theorem statopia_math_node_858392357_8c0dfbe1 : ∀ (d : ℕ) (U : HMCState d → ℝ) (π : Measure (HMCState d)) (L : ℕ) (ε : ℝ)
    (Rej : HMCState d → ℝ)
    (hpi_atom : ∀ x : HMCState d, π {x} = 0)
    (hiter : ∀ (n : ℕ) (x : HMCState d),
      ENNReal.ofReal ((Rej x) ^ n) • Measure.dirac x ≤
        kernelPow (hmcKernel U L ε) n x)
    (hRej_nonneg : ∀ x : HMCState d, 0 ≤ Rej x)
    (hRej_le_one : ∀ x : HMCState d, Rej x ≤ 1)
    (hP_prob : ∀ x : HMCState d, IsProbabilityMeasure (hmcKernel U L ε x))
    (hpi_finite : IsFiniteMeasure π)
    (hsingle : ∀ x : HMCState d, MeasurableSet ({x} : Set (HMCState d)))
    (n : ℕ) (x : HMCState d),
    (Rej x) ^ n ≤ tvDist (kernelPow (hmcKernel U L ε) n x) π := by
  /- @proof-region region.target-node.session.2a1caa53b5743f37 begin -/
  intro d U π L ε Rej hpi_atom hiter hRej_nonneg hRej_le_one hP_prob hpi_finite hsingle n x
  haveI : IsFiniteMeasure π := hpi_finite
  rw [tvDist]
  set μ : Measure (HMCState d) := kernelPow (hmcKernel U L ε) n x with hμ
  have hpow_le : ∀ k : ℕ, kernelPow (hmcKernel U L ε) k x Set.univ ≤ 1 := by
    intro k
    induction k with
    | zero =>
        show (Measure.dirac x) Set.univ ≤ 1
        rw [Measure.dirac_apply' x MeasurableSet.univ]
        simp
    | succ k ih =>
        show ((kernelPow (hmcKernel U L ε) k x).bind (hmcKernel U L ε)) Set.univ ≤ 1
        calc ((kernelPow (hmcKernel U L ε) k x).bind (hmcKernel U L ε)) Set.univ
            ≤ ∫⁻ a, (hmcKernel U L ε a) Set.univ ∂(kernelPow (hmcKernel U L ε) k x) :=
              Measure.bind_apply_le (hmcKernel U L ε) MeasurableSet.univ
          _ ≤ ∫⁻ a, (1 : ENNReal) ∂(kernelPow (hmcKernel U L ε) k x) :=
              lintegral_mono
                (f := fun a => (hmcKernel U L ε a) Set.univ) (g := fun _ => (1 : ENNReal))
                (fun a => le_of_eq (hP_prob a).measure_univ)
          _ = kernelPow (hmcKernel U L ε) k x Set.univ := by simp
          _ ≤ 1 := ih
  haveI hμfin : IsFiniteMeasure μ := by
    rw [hμ]
    exact ⟨lt_of_le_of_lt (hpow_le n) ENNReal.one_lt_top⟩
  set g : HMCState d → ℝ := ({x} : Set (HMCState d)).indicator (fun _ => (1 : ℝ)) with hg
  have hreal_apply : ∀ (ν : Measure (HMCState d)) (s : Set (HMCState d)),
      ν.real s = (ν s).toReal := fun ν s => rfl
  have hg_meas : Measurable g := by
    rw [hg]
    exact measurable_const.indicator (hsingle x)
  have hg_bound : ∀ y : HMCState d, |g y| ≤ 1 := by
    intro y
    rw [hg]
    by_cases hy : y ∈ ({x} : Set (HMCState d))
    · rw [Set.indicator_of_mem hy]
      norm_num
    · have h0 : ({x} : Set (HMCState d)).indicator (fun _ => (1 : ℝ)) y = 0 := by
        simp [Set.indicator, hy]
      rw [h0]
      norm_num
  have hμ_lt : μ {x} ≠ ⊤ := by
    have hle : μ {x} ≤ μ Set.univ := measure_mono (Set.subset_univ _)
    exact ne_of_lt (lt_of_le_of_lt hle hμfin.measure_univ_lt_top)
  have hsm : (ENNReal.ofReal ((Rej x) ^ n) • Measure.dirac x : Measure (HMCState d)) {x}
      = ENNReal.ofReal ((Rej x) ^ n) := by
    rw [Measure.smul_apply, Measure.dirac_apply' x (hsingle x)]
    simp
  have hμ_atom : ENNReal.ofReal ((Rej x) ^ n) ≤ μ {x} := by
    have h := (Measure.le_iff.mp (hiter n x)) ({x} : Set (HMCState d)) (hsingle x)
    rw [hμ, ← hsm]
    exact h
  have hRej_nonneg' : (0 : ℝ) ≤ (Rej x) ^ n := pow_nonneg (hRej_nonneg x) n
  have hμ_real : (Rej x) ^ n ≤ μ.real {x} := by
    have h2 : (ENNReal.ofReal ((Rej x) ^ n)).toReal ≤ (μ {x}).toReal :=
      ENNReal.toReal_mono hμ_lt hμ_atom
    rw [ENNReal.toReal_ofReal hRej_nonneg'] at h2
    rwa [hreal_apply μ {x}]
  have hμ_real_nn : (0 : ℝ) ≤ μ.real {x} := le_trans hRej_nonneg' hμ_real
  have hg_int_μ : ∫ y, g y ∂μ = μ.real {x} := by
    rw [hg]
    exact MeasureTheory.integral_indicator_one (μ := μ) (hsingle x)
  have hg_int_π : ∫ y, g y ∂π = 0 := by
    have h : ∫ y, g y ∂π = π.real {x} := by
      rw [hg]
      exact MeasureTheory.integral_indicator_one (μ := π) (hsingle x)
    rw [h, hreal_apply π {x}, hpi_atom x]
    simp
  have hval : |∫ y, g y ∂μ - ∫ y, g y ∂π| = μ.real {x} := by
    rw [hg_int_μ, hg_int_π, sub_zero, abs_of_nonneg hμ_real_nn]
  have hmem : |∫ y, g y ∂μ - ∫ y, g y ∂π| ∈
      {r : ℝ | ∃ f : HMCState d → ℝ, Measurable f ∧ (∀ y, |f y| ≤ 1) ∧
        r = |∫ y, f y ∂μ - ∫ y, f y ∂π|} :=
    ⟨g, hg_meas, hg_bound, rfl⟩
  have hbdd : BddAbove
      {r : ℝ | ∃ f : HMCState d → ℝ, Measurable f ∧ (∀ y, |f y| ≤ 1) ∧
        r = |∫ y, f y ∂μ - ∫ y, f y ∂π|} := by
    refine ⟨μ.real Set.univ + π.real Set.univ, ?_⟩
    rintro r ⟨f, hf_meas, hf_bound, rfl⟩
    have h1 : |∫ y, f y ∂μ| ≤ μ.real Set.univ := by
      have h := norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := 1)
        (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hf_bound y)
      simpa [Real.norm_eq_abs] using h
    have h2 : |∫ y, f y ∂π| ≤ π.real Set.univ := by
      have h := norm_integral_le_of_norm_le_const (μ := π) (f := f) (C := 1)
        (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hf_bound y)
      simpa [Real.norm_eq_abs] using h
    have htri : |∫ y, f y ∂μ - ∫ y, f y ∂π| ≤ |∫ y, f y ∂μ| + |∫ y, f y ∂π| := by
      simpa [Real.norm_eq_abs] using norm_sub_le (∫ y, f y ∂μ) (∫ y, f y ∂π)
    calc |∫ y, f y ∂μ - ∫ y, f y ∂π|
        ≤ |∫ y, f y ∂μ| + |∫ y, f y ∂π| := htri
      _ ≤ μ.real Set.univ + π.real Set.univ := add_le_add h1 h2
  have hgoal : (Rej x) ^ n ≤ sSup
      {r : ℝ | ∃ f : HMCState d → ℝ, Measurable f ∧ (∀ y, |f y| ≤ 1) ∧
        r = |∫ y, f y ∂μ - ∫ y, f y ∂π|} := by
    calc (Rej x) ^ n ≤ |∫ y, g y ∂μ - ∫ y, g y ∂π| := by
          rw [hval]
          exact hμ_real
      _ ≤ sSup {r : ℝ | ∃ f : HMCState d → ℝ, Measurable f ∧ (∀ y, |f y| ≤ 1) ∧
          r = |∫ y, f y ∂μ - ∫ y, f y ∂π|} := le_csSup hbdd hmem
  exact hgoal
  /- @proof-region region.target-node.session.2a1caa53b5743f37 end -/

end Statlib.Imported
end

