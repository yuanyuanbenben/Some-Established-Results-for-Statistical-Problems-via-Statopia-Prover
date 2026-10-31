import ProverJobs.job_paper_a9a2ab5d4e094509b2cdb371b3b02f1c.Vocabulary
import ProverJobs.job_paper_a9a2ab5d4e094509b2cdb371b3b02f1c.Base
import ProverJobs.job_paper_a9a2ab5d4e094509b2cdb371b3b02f1c.ProvedNodes.Node_2742352001_844b1090_98f5ce8b

namespace PaperProofTasks.job_paper_a9a2ab5d4e094509b2cdb371b3b02f1c

open _root_.PaperProofTasks.job_paper_a9a2ab5d4e094509b2cdb371b3b02f1c.Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_1980195792_bc5cfc4b : ∀ {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (π : Measure X) [IsFiniteMeasure π]
    (P : Kernel X X) [IsMarkovKernel P]
    (r : X → ℝ)
    (hr_nonneg : ∀ x : X, 0 ≤ r x)
    (hpi_atom : ∀ x : X, π {x} = 0)
    (hreturn : ∀ (x : X) (n : ℕ), 1 ≤ n → (P ^ n) x {x} ≥ (ENNReal.ofReal (r x)) ^ n)
    (x : X) (n : ℕ) (hn : 1 ≤ n),
    (r x) ^ n ≤ (tvDist ((P ^ n) x) π).toReal := by
  /- @proof-region region.target-node.session.eb3d7f519d8a0d15 begin -/
  intro X _ _ π _ P _ r hr_nonneg hpi_atom hreturn x n hn
  have huniv : ∀ k : ℕ, ((P ^ k) x) Set.univ = 1 := by
    intro k
    induction k with
    | zero =>
      change (Measure.dirac x) Set.univ = 1
      exact MeasureTheory.Measure.dirac_apply_of_mem (Set.mem_univ x)
    | succ k ih =>
      rw [ProbabilityTheory.Kernel.pow_succ_apply_eq_lintegral P k x (by simp)]
      rw [show (∫⁻ b, (P b) Set.univ ∂((P ^ k) x)) = ∫⁻ b, (1 : ℝ≥0∞) ∂((P ^ k) x) from
        MeasureTheory.lintegral_congr (fun b => by
          haveI : IsProbabilityMeasure (P b) :=
            ProbabilityTheory.IsMarkovKernel.is_probability_measure' b
          exact measure_univ)]
      rw [MeasureTheory.lintegral_one]
      exact ih
  haveI hfinμ : IsFiniteMeasure ((P ^ n) x) :=
    ⟨by rw [huniv n]; exact ENNReal.one_lt_top⟩
  have hmeas : MeasurableSet ({x} : Set X) := measurableSet_singleton x
  set g : X → ℝ := ({x} : Set X).indicator (fun _ => (1 : ℝ)) with hg
  have hg_meas : Measurable g := by
    rw [hg]
    exact Measurable.indicator measurable_const hmeas
  have hg_bound : ∀ y, |g y| ≤ 1 := by
    intro y
    rw [hg]
    by_cases hy : y ∈ ({x} : Set X) <;> simp [Set.indicator, hy]
  let F : {f : X → ℝ // (∀ y, |f y| ≤ 1) ∧ Measurable f} := ⟨g, hg_bound, hg_meas⟩
  have hle : ENNReal.ofReal |∫ y, g y ∂((P ^ n) x) - ∫ y, g y ∂π| ≤
      tvDist ((P ^ n) x) π := by
    unfold tvDist
    exact le_iSup (fun f : {f : X → ℝ // (∀ y, |f y| ≤ 1) ∧ Measurable f} =>
      ENNReal.ofReal |∫ y, f.1 y ∂((P ^ n) x) - ∫ y, f.1 y ∂π|) F
  have hIμ : ∫ y, g y ∂((P ^ n) x) = (((P ^ n) x) {x}).toReal := by
    rw [hg]
    rw [MeasureTheory.integral_indicator_const (μ := (P ^ n) x) (s := {x}) (1 : ℝ) hmeas]
    simp [Measure.real]
  have hIν : ∫ y, g y ∂π = (π {x}).toReal := by
    rw [hg]
    rw [MeasureTheory.integral_indicator_const (μ := π) (s := {x}) (1 : ℝ) hmeas]
    simp [Measure.real]
  have hmle : ((P ^ n) x) {x} ≤ 1 := by
    calc ((P ^ n) x) {x} ≤ ((P ^ n) x) Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := huniv n
  have hmne : ((P ^ n) x) {x} ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hmle
  have hterm : ENNReal.ofReal |∫ y, g y ∂((P ^ n) x) - ∫ y, g y ∂π| = ((P ^ n) x) {x} := by
    rw [hIμ, hIν, hpi_atom x]
    rw [ENNReal.toReal_zero, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_toReal hmne
  have hstep : ENNReal.ofReal ((r x) ^ n) ≤ tvDist ((P ^ n) x) π := by
    calc ENNReal.ofReal ((r x) ^ n) = (ENNReal.ofReal (r x)) ^ n :=
          ENNReal.ofReal_pow (hr_nonneg x) n
      _ ≤ ((P ^ n) x) {x} := hreturn x n hn
      _ = ENNReal.ofReal |∫ y, g y ∂((P ^ n) x) - ∫ y, g y ∂π| := hterm.symm
      _ ≤ tvDist ((P ^ n) x) π := hle
  have hbound : ∀ f : {f : X → ℝ // (∀ y, |f y| ≤ 1) ∧ Measurable f},
      ENNReal.ofReal |∫ y, f.1 y ∂((P ^ n) x) - ∫ y, f.1 y ∂π|
        ≤ ENNReal.ofReal (((P ^ n) x).real Set.univ + π.real Set.univ) := by
    intro f
    apply ENNReal.ofReal_le_ofReal
    have hf1 : |∫ y, f.1 y ∂((P ^ n) x)| ≤ ((P ^ n) x).real Set.univ := by
      have h := MeasureTheory.norm_integral_le_of_norm_le_const (μ := (P ^ n) x)
        (f := f.1) (C := 1)
        (Filter.Eventually.of_forall (fun y => by rw [Real.norm_eq_abs]; exact f.2.1 y))
      simpa [Real.norm_eq_abs, one_mul] using h
    have hf2 : |∫ y, f.1 y ∂π| ≤ π.real Set.univ := by
      have h := MeasureTheory.norm_integral_le_of_norm_le_const (μ := π) (f := f.1) (C := 1)
        (Filter.Eventually.of_forall (fun y => by rw [Real.norm_eq_abs]; exact f.2.1 y))
      simpa [Real.norm_eq_abs, one_mul] using h
    rw [abs_le]
    constructor <;>
      linarith [neg_abs_le (∫ y, f.1 y ∂((P ^ n) x)),
        le_abs_self (∫ y, f.1 y ∂((P ^ n) x)),
        neg_abs_le (∫ y, f.1 y ∂π), le_abs_self (∫ y, f.1 y ∂π), hf1, hf2]
  have hfin : tvDist ((P ^ n) x) π ≠ ⊤ := by
    have hb : tvDist ((P ^ n) x) π
        ≤ ENNReal.ofReal (((P ^ n) x).real Set.univ + π.real Set.univ) := by
      unfold tvDist
      exact iSup_le hbound
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
  calc (r x) ^ n = (ENNReal.ofReal ((r x) ^ n)).toReal :=
        (ENNReal.toReal_ofReal (pow_nonneg (hr_nonneg x) n)).symm
    _ ≤ (tvDist ((P ^ n) x) π).toReal := ENNReal.toReal_mono hfin hstep

  /- @proof-region region.target-node.session.eb3d7f519d8a0d15 end -/

end
end Statlib.Imported

