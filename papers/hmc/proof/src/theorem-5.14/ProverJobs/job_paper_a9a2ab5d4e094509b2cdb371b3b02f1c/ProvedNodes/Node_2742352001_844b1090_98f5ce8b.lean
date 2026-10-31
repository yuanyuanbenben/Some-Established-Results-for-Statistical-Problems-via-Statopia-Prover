import ProverJobs.job_paper_a9a2ab5d4e094509b2cdb371b3b02f1c.Vocabulary
import ProverJobs.job_paper_a9a2ab5d4e094509b2cdb371b3b02f1c.Base

namespace PaperProofTasks.job_paper_a9a2ab5d4e094509b2cdb371b3b02f1c

open _root_.PaperProofTasks.job_paper_a9a2ab5d4e094509b2cdb371b3b02f1c.Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_2742352001_844b1090 : ∀ {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (P Q : Kernel X X) (α : X → X → ℝ) (r : X → ℝ)
    (hMH : IsMHType P Q α r)
    (x : X) (n : ℕ) (hn : 1 ≤ n),
    (P ^ n) x {x} ≥ (ENNReal.ofReal (r x)) ^ n := by
  /- @proof-region region.target-node.session.d4565caa3d2b8eae begin -/
  intro X _ _ P Q α r hMH x n hn
  have hdirac : (Measure.dirac x) ({x} : Set X) = 1 :=
    Measure.dirac_apply_of_mem (Set.mem_singleton x)
  have hbase : ENNReal.ofReal (r x) ≤ (P x) {x} := by
    have hsm : ENNReal.ofReal (r x) • (1 : ℝ≥0∞) = ENNReal.ofReal (r x) := by simp
    rw [hMH.decomp x, Measure.add_apply, Measure.smul_apply, hdirac, hsm]
    simpa using add_le_add_right
      (zero_le (((Q x).withDensity (fun y => ENNReal.ofReal (α x y))) {x}))
      (ENNReal.ofReal (r x))
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  clear hn
  induction k with
  | zero => simpa using hbase
  | succ k ih =>
    set c : ℝ≥0∞ := ENNReal.ofReal (r x) with hc
    have hrec : (P ^ (Nat.succ k + 1)) x {x} = ∫⁻ y, (P y) {x} ∂((P ^ Nat.succ k) x) :=
      Kernel.pow_succ_apply_eq_lintegral P (Nat.succ k) x (s := {x})
        (measurableSet_singleton x)
    have hpt : ∀ y, ({x} : Set X).indicator (fun _ => c) y ≤ (P y) {x} := by
      intro y
      rcases eq_or_ne y x with rfl | hy
      · simpa [hc] using hbase
      · rw [Set.indicator_of_notMem (by simpa using hy)]
        exact zero_le _
    have hI : ∫⁻ y, ({x} : Set X).indicator (fun _ => c) y ∂((P ^ Nat.succ k) x)
        = c * ((P ^ Nat.succ k) x {x}) := by
      rw [lintegral_indicator (measurableSet_singleton x), lintegral_const]
      simp [Measure.restrict_apply, measurableSet_singleton]
    have hstep : c ^ (Nat.succ k + 1) ≤ ∫⁻ y, (P y) {x} ∂((P ^ Nat.succ k) x) := by
      calc c ^ (Nat.succ k + 1)
          = c * c ^ (Nat.succ k) := pow_succ' c (Nat.succ k)
        _ ≤ c * ((P ^ Nat.succ k) x {x}) := by
            refine mul_le_mul_left' ?_ c
            simpa [hc] using ih
        _ = ∫⁻ y, ({x} : Set X).indicator (fun _ => c) y ∂((P ^ Nat.succ k) x) := hI.symm
        _ ≤ ∫⁻ y, (P y) {x} ∂((P ^ Nat.succ k) x) := lintegral_mono hpt
    rw [hrec]
    exact hstep


  /- @proof-region region.target-node.session.d4565caa3d2b8eae end -/

end
end Statlib.Imported

