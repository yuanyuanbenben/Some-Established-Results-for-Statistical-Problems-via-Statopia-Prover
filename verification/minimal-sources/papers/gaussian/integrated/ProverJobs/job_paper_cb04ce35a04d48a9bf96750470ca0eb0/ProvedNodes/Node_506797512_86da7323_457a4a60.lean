import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Vocabulary
import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Base

namespace PaperProofTasks.job_paper_cb04ce35a04d48a9bf96750470ca0eb0

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
open _root_.PaperProofTasks.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Statlib.Imported

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
namespace Statlib.Imported

noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_506797512_86da7323 : ∀ (s : ℝ) (N K : ℕ)
    (hs : 2 ≤ s) (hK : 1 ≤ K),
    (∑ i ∈ Finset.univ.filter (fun i : Fin N => K ≤ (i : ℕ)),
        Real.rpow ((((i : ℕ) + 1 : ℕ)) : ℝ) (-s)) ≤ Real.rpow (K : ℝ) (1 - s) := by
  /- @proof-region region.target-node.session.6508db1dca50130a begin -/
  intro s N K hs hK
  have key : ∀ m : ℕ, 1 ≤ m →
      (((m + 1 : ℕ)) : ℝ) ^ (-s) ≤ (m : ℝ) ^ (1 - s) - (((m + 1 : ℕ)) : ℝ) ^ (1 - s) := by
    intro m hm
    set u : ℝ := (m : ℝ) with hudef
    set v : ℝ := (((m + 1 : ℕ)) : ℝ) with hvdef
    have hvu : v = u + 1 := by
      rw [hvdef, hudef]
      push_cast
      ring
    have hu1 : (1 : ℝ) ≤ u := by
      rw [hudef]
      exact_mod_cast hm
    have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu1
    have hv0 : (0 : ℝ) < v := by
      rw [hvu]
      linarith
    have hvu_ge : (1 : ℝ) ≤ v / u := by
      rw [hvu, le_div_iff₀ hu0]
      linarith
    have hkey1 : v⁻¹ + 1 ≤ v / u := by
      rw [hvu]
      have h1 : ((u + 1 : ℝ))⁻¹ + 1 = (u + 2) / (u + 1) := by
        have hne : (u + 1 : ℝ) ≠ 0 := by linarith
        field_simp
        ring
      rw [h1, le_div_iff₀ hu0, div_mul_eq_mul_div,
        div_le_iff₀ (by linarith : (0 : ℝ) < u + 1)]
      nlinarith
    have hle_pow : v / u ≤ (v / u) ^ (s - 1) := by
      have h : (v / u) ^ (1 : ℝ) ≤ (v / u) ^ (s - 1) :=
        Real.rpow_le_rpow_of_exponent_le hvu_ge (by linarith)
      simpa using h
    have hcomb : v⁻¹ + 1 ≤ (v / u) ^ (s - 1) := le_trans hkey1 hle_pow
    have hdiv_eq : (v / u) ^ (s - 1) = u ^ (1 - s) / v ^ (1 - s) := by
      rw [show s - 1 = -(1 - s) by ring,
        Real.rpow_neg (le_of_lt (div_pos hv0 hu0)),
        Real.div_rpow (le_of_lt hv0) (le_of_lt hu0), inv_div]
    have hpos : (0 : ℝ) < v ^ (1 - s) := Real.rpow_pos_of_pos hv0 _
    have hvv : v ^ (1 - s) * (v⁻¹ + 1) ≤ u ^ (1 - s) := by
      have hmul := mul_le_mul_of_nonneg_left hcomb (le_of_lt hpos)
      rw [hdiv_eq] at hmul
      have hne : v ^ (1 - s) ≠ 0 := ne_of_gt hpos
      have hsimp : v ^ (1 - s) * (u ^ (1 - s) / v ^ (1 - s)) = u ^ (1 - s) := by
        calc v ^ (1 - s) * (u ^ (1 - s) / v ^ (1 - s))
            = (v ^ (1 - s) / v ^ (1 - s)) * u ^ (1 - s) := by ring
          _ = 1 * u ^ (1 - s) := by rw [div_self hne]
          _ = u ^ (1 - s) := one_mul _
      rwa [hsimp] at hmul
    have hvs : v ^ (-s) = v ^ (1 - s) * v⁻¹ := by
      rw [show (-s : ℝ) = (1 - s) + (-1) by ring, Real.rpow_add hv0, Real.rpow_neg_one]
    have hfin : v ^ (-s) + v ^ (1 - s) ≤ u ^ (1 - s) := by
      have hrw : v ^ (1 - s) * v⁻¹ + v ^ (1 - s) = v ^ (1 - s) * (v⁻¹ + 1) := by ring
      calc v ^ (-s) + v ^ (1 - s) = v ^ (1 - s) * v⁻¹ + v ^ (1 - s) := by rw [hvs]
        _ = v ^ (1 - s) * (v⁻¹ + 1) := hrw
        _ ≤ u ^ (1 - s) := hvv
    linarith
  have htel : ∀ n : ℕ,
      (∑ m ∈ Finset.range n,
        (if K ≤ m then ((m : ℝ) ^ (1 - s) - (((m + 1 : ℕ)) : ℝ) ^ (1 - s)) else 0))
        ≤ (K : ℝ) ^ (1 - s) - ((max K n : ℕ) : ℝ) ^ (1 - s) := by
    intro n
    induction n with
    | zero =>
      rw [show max K 0 = K from max_eq_left (Nat.zero_le K)]
      simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      by_cases hkn : K ≤ n
      · have hmax : max K n = n := max_eq_right hkn
        rw [hmax] at ih
        have hif : (if K ≤ n then ((n : ℝ) ^ (1 - s) - (((n + 1 : ℕ)) : ℝ) ^ (1 - s)) else 0)
            = ((n : ℝ) ^ (1 - s) - (((n + 1 : ℕ)) : ℝ) ^ (1 - s)) := if_pos hkn
        rw [hif]
        have hmax2 : max K (n + 1) = n + 1 := max_eq_right (Nat.le_succ_of_le hkn)
        rw [hmax2]
        linarith
      · have hle : max K n = K := max_eq_left (Nat.le_of_lt (Nat.lt_of_not_le hkn))
        rw [hle] at ih
        have hif : (if K ≤ n then ((n : ℝ) ^ (1 - s) - (((n + 1 : ℕ)) : ℝ) ^ (1 - s)) else 0) = 0 :=
          if_neg hkn
        rw [hif, add_zero]
        have hmax2 : max K (n + 1) = K :=
          max_eq_left (Nat.succ_le_of_lt (Nat.lt_of_not_le hkn))
        rw [hmax2]
        exact ih
  have hmain : (∑ m ∈ Finset.range N,
      (if K ≤ m then ((((m + 1 : ℕ)) : ℝ)) ^ (-s) else 0)) ≤ (K : ℝ) ^ (1 - s) := by
    have h1 : (∑ m ∈ Finset.range N, (if K ≤ m then ((((m + 1 : ℕ)) : ℝ)) ^ (-s) else 0))
        ≤ ∑ m ∈ Finset.range N,
          (if K ≤ m then ((m : ℝ) ^ (1 - s) - (((m + 1 : ℕ)) : ℝ) ^ (1 - s)) else 0) := by
      apply Finset.sum_le_sum
      intro m _
      by_cases h : K ≤ m
      · simp only [h, if_true]
        exact key m (le_trans hK h)
      · simp [h]
    have h2 := htel N
    have h3 : (0 : ℝ) ≤ ((max K N : ℕ) : ℝ) ^ (1 - s) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    linarith
  have hconv : (∑ i ∈ Finset.univ.filter (fun i : Fin N => K ≤ (i : ℕ)),
        Real.rpow ((((i : ℕ) + 1 : ℕ)) : ℝ) (-s))
      = ∑ m ∈ Finset.range N,
          (if K ≤ m then Real.rpow ((((m + 1 : ℕ)) : ℝ)) (-s) else 0) := by
    rw [Finset.sum_filter,
      Fin.sum_univ_eq_sum_range
        (fun m : ℕ => (if K ≤ m then Real.rpow ((((m + 1 : ℕ)) : ℝ)) (-s) else 0)) N]
  rw [hconv]
  exact hmain
  /- @proof-region region.target-node.session.6508db1dca50130a end -/

end

end Statlib.Imported

