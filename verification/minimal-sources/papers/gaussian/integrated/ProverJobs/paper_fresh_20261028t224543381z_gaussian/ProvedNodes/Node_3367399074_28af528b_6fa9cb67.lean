import ProverJobs.paper_fresh_20261028t224543381z_gaussian.Vocabulary
import ProverJobs.paper_fresh_20261028t224543381z_gaussian.Base

namespace PaperProofTasks.paper_fresh_20261028t224543381z_gaussian

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open _root_.PaperProofTasks.paper_fresh_20261028t224543381z_gaussian.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace Statlib.Imported


set_option autoImplicit false in
theorem statopia_math_node_3367399074_28af528b : ∀ (p n : ℕ) (a : ℝ) (hp : 0 < p),
    1 ≤ ellN p n ∧ ellN p n ≤ kN p a n ∧ kN p a n ≤ p := by
  /- @proof-region region.target-node.session.ea62916d4307c3e9 begin -/
  intro p n a hp
  have hp1' : 1 ≤ p := by omega
  have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast hp1'
  have hell : ellN p n
      = (Int.ceil (min (max (1 : ℝ) ((Real.log (n : ℝ)) ^ (3 : ℕ))) ((p : ℕ) : ℝ))).toNat :=
    rfl
  have hk : kN p a n
      = (Int.ceil (min (max ((ellN p n : ℕ) : ℝ)
          ((n : ℝ) ^ ((1 : ℝ) / ((Real.log (n : ℝ)) ^ a)))) ((p : ℕ) : ℝ))).toNat := rfl
  set A1 : ℝ := min (max (1 : ℝ) ((Real.log (n : ℝ)) ^ (3 : ℕ))) ((p : ℕ) : ℝ) with hA1def
  set A2 : ℝ := min (max ((ellN p n : ℕ) : ℝ)
      ((n : ℝ) ^ ((1 : ℝ) / ((Real.log (n : ℝ)) ^ a)))) ((p : ℕ) : ℝ) with hA2def
  have hmin : ∀ (x : ℝ), 1 ≤ x → x ≤ ((p : ℕ) : ℝ) →
      1 ≤ (Int.ceil x).toNat ∧ (Int.ceil x).toNat ≤ p := by
    intro x hx1 hx2
    have hc1 : (1 : ℤ) ≤ Int.ceil x := by exact_mod_cast le_trans hx1 (Int.le_ceil x)
    have hpc : (((p : ℕ) : ℤ) : ℝ) = ((p : ℕ) : ℝ) := by simp
    have hc2 : Int.ceil x ≤ ((p : ℕ) : ℤ) := by
      rw [Int.ceil_le, hpc]
      exact hx2
    exact ⟨by omega, by omega⟩
  have hA1lo : (1 : ℝ) ≤ A1 := by
    rw [hA1def]
    exact le_min (le_max_left _ _) hp1
  have hA1hi : A1 ≤ ((p : ℕ) : ℝ) := by
    rw [hA1def]
    exact min_le_right _ _
  obtain ⟨hell1, hell2⟩ := hmin A1 hA1lo hA1hi
  have hell1' : 1 ≤ ellN p n := by rw [hell]; exact hell1
  have hell2' : ellN p n ≤ p := by rw [hell]; exact hell2
  have hL1 : (1 : ℝ) ≤ ((ellN p n : ℕ) : ℝ) := by exact_mod_cast hell1'
  have hLp : ((ellN p n : ℕ) : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast hell2'
  have hA2lo : (1 : ℝ) ≤ A2 := by
    rw [hA2def]
    exact le_min (le_trans hL1 (le_max_left _ _)) hp1
  have hA2hi : A2 ≤ ((p : ℕ) : ℝ) := by
    rw [hA2def]
    exact min_le_right _ _
  obtain ⟨_, hk2⟩ := hmin A2 hA2lo hA2hi
  have hk2' : kN p a n ≤ p := by rw [hk]; exact hk2
  have hLA2 : ((ellN p n : ℕ) : ℝ) ≤ A2 := by
    rw [hA2def]
    exact le_min (le_max_left _ _) hLp
  have hcoh : ((ellN p n : ℕ) : ℝ) = (((ellN p n : ℕ) : ℤ) : ℝ) := by simp
  have hreal : (((ellN p n : ℕ) : ℤ) : ℝ) ≤ (((Int.ceil A2) : ℤ) : ℝ) := by
    rw [← hcoh]
    exact le_trans hLA2 (Int.le_ceil A2)
  have hZ : ((ellN p n : ℕ) : ℤ) ≤ Int.ceil A2 := Int.cast_le.mp hreal
  have hellk : ellN p n ≤ kN p a n := by
    rw [hk]
    omega
  refine ⟨hell1', hellk, hk2'⟩
  /- @proof-region region.target-node.session.ea62916d4307c3e9 end -/

end Statlib.Imported
end

