import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q21.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q21.Base

open Finset
open Msc62GroundTruth

open Finset
namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_781651629_73b8feb2 : ∀ (N n : ℕ) (hN : 2 ≤ N)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ N),
    ((N - 2).choose (n - 1) : ℝ) / (N.choose n : ℝ)
      = ((n : ℝ) * ((N - n : ℕ) : ℝ)) / ((N : ℝ) * ((N - 1 : ℕ) : ℝ)) := by
  /- @proof-region region.target-node.session.432a052b908060af begin -/
  intro N n hN hn_pos hn_le
  rcases eq_or_lt_of_le hn_le with h | h
  · rw [h]
    have hzero : ((N - 2).choose (N - 1) : ℝ) = 0 := by
      have h0 : (N - 2).choose (N - 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [h0]
    rw [hzero, Nat.choose_self]
    simp
  · have hN1 : n ≤ N := le_of_lt h
    have hn1 : n - 1 ≤ N - 2 := by omega
    have hsub : (N - 2) - (n - 1) = N - n - 1 := by omega
    have hA : ((N - 2).choose (n - 1) : ℝ) =
        ((N - 2).factorial : ℝ) /
          (((n - 1).factorial : ℝ) * (((N - 2) - (n - 1)).factorial : ℝ)) :=
      Nat.cast_choose ℝ hn1
    have hB : (N.choose n : ℝ) =
        (N.factorial : ℝ) / ((n.factorial : ℝ) * ((N - n).factorial : ℝ)) :=
      Nat.cast_choose ℝ hN1
    have hNfac : ((N.factorial : ℕ) : ℝ) = (N : ℝ) * (((N - 1).factorial : ℕ) : ℝ) := by
      have hh := Nat.factorial_succ (N - 1)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ N)] at hh
      exact_mod_cast hh
    have hN1fac : (((N - 1).factorial : ℕ) : ℝ) =
        ((N - 1 : ℕ) : ℝ) * (((N - 2).factorial : ℕ) : ℝ) := by
      have hh := Nat.factorial_succ (N - 2)
      have harg : N - 2 + 1 = N - 1 := by omega
      rw [harg] at hh
      exact_mod_cast hh
    have hnfac : ((n.factorial : ℕ) : ℝ) = (n : ℝ) * (((n - 1).factorial : ℕ) : ℝ) := by
      have hh := Nat.factorial_succ (n - 1)
      rw [Nat.sub_add_cancel hn_pos] at hh
      exact_mod_cast hh
    have hNnfac : (((N - n).factorial : ℕ) : ℝ) =
        ((N - n : ℕ) : ℝ) * (((N - n - 1).factorial : ℕ) : ℝ) := by
      have hh := Nat.factorial_succ (N - n - 1)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ N - n)] at hh
      exact_mod_cast hh
    have hn0 : (n : ℝ) ≠ 0 := by
      have h0 : n ≠ 0 := by omega
      exact_mod_cast h0
    have hN0 : (N : ℝ) ≠ 0 := by
      have h0 : N ≠ 0 := by omega
      exact_mod_cast h0
    have hNm10 : ((N - 1 : ℕ) : ℝ) ≠ 0 := by
      have h0 : N - 1 ≠ 0 := by omega
      exact_mod_cast h0
    have hNn0 : ((N - n : ℕ) : ℝ) ≠ 0 := by
      have h0 : N - n ≠ 0 := by omega
      exact_mod_cast h0
    have hfn0 : (((n - 1).factorial : ℕ) : ℝ) ≠ 0 := by
      have h0 : (n - 1).factorial ≠ 0 := Nat.factorial_ne_zero (n - 1)
      exact_mod_cast h0
    have hfnN0 : (((N - n - 1).factorial : ℕ) : ℝ) ≠ 0 := by
      have h0 : (N - n - 1).factorial ≠ 0 := Nat.factorial_ne_zero (N - n - 1)
      exact_mod_cast h0
    rw [hA, hB, hsub, hNfac, hN1fac, hnfac, hNnfac]
    field_simp
  /- @proof-region region.target-node.session.432a052b908060af end -/

end Msc62GroundTruth
