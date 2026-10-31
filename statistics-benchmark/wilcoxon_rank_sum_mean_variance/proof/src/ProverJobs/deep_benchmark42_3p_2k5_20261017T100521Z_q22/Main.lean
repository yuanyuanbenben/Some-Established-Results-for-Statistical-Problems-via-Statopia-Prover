import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q22.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q22.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q22.Base

open Finset
namespace Msc62GroundTruth

theorem wilcoxon_rank_sum_mean_variance
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    let N : ℕ := m + n
    let samples : Finset (Finset (Fin N)) :=
      (Finset.univ : Finset (Finset (Fin N))).filter (fun A => A.card = m)
    let rank : Fin N → ℝ := fun r => ((r.val + 1 : ℕ) : ℝ)
    let W : Finset (Fin N) → ℝ := fun A => A.sum (fun r => rank r)
    let mean : ℝ := (1 / (samples.card : ℝ)) * samples.sum (fun A => W A)
    let variance : ℝ :=
      (1 / (samples.card : ℝ)) * samples.sum (fun A => (W A - mean) ^ 2)
    mean = (m : ℝ) * ((N : ℝ) + 1) / 2 ∧
      variance = (m : ℝ) * (n : ℝ) * ((N : ℝ) + 1) / 12
:= by
  /- @proof-region region.root.d68da32f4e51 begin -/
  dsimp only
  have hN2 : 2 ≤ m + n := by omega
  have hN1 : 1 ≤ m + n := by omega
  have hmN : m ≤ m + n := by omega
  have hsamples :
      (Finset.univ : Finset (Finset (Fin (m + n)))).filter (fun A => A.card = m)
        = (Finset.univ : Finset (Fin (m + n))).powersetCard m := by
    ext A
    simp [Finset.mem_powersetCard]
  rw [hsamples]
  set P : Finset (Finset (Fin (m + n))) :=
    (Finset.univ : Finset (Fin (m + n))).powersetCard m with hP
  set rank : Fin (m + n) → ℝ := fun r => ((r.val + 1 : ℕ) : ℝ) with hrank
  set W : Finset (Fin (m + n)) → ℝ := fun A => A.sum (fun r => rank r) with hW
  set mean : ℝ := (1 / (P.card : ℝ)) * P.sum (fun A => W A) with hmean_def
  set variance : ℝ :=
    (1 / (P.card : ℝ)) * P.sum (fun A => (W A - mean) ^ 2) with hvar_def
  have hcard : P.card = (m + n).choose m := by
    rw [hP]
    simp [Finset.card_powersetCard]
  have hcard0 : P.card ≠ 0 := by
    rw [hcard]
    exact (Nat.choose_pos hmN).ne'
  have hmean : (1 / (P.card : ℝ)) * P.sum (fun A => W A)
      = (m : ℝ) * ((↑(m + n) : ℝ) + 1) / 2 := by
    have h := statopia_math_node_2649541030_093d648c (m + n) m hN1 hm hmN
    simpa only [hP, hrank, hW] using h
  have hrange1 : ∀ k : ℕ,
      (∑ i ∈ Finset.range k, (((i + 1 : ℕ) : ℝ))) = (k : ℝ) * ((k : ℝ) + 1) / 2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  have hrange2 : ∀ k : ℕ,
      (∑ i ∈ Finset.range k, (((i + 1 : ℕ) : ℝ) ^ 2))
        = (k : ℝ) * ((k : ℝ) + 1) * (2 * (k : ℝ) + 1) / 6 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  have hS1 : (∑ r : Fin (m + n), rank r)
      = (↑(m + n) : ℝ) * ((↑(m + n) : ℝ) + 1) / 2 := by
    simp only [hrank]
    rw [Fin.sum_univ_eq_sum_range (fun i => ((i + 1 : ℕ) : ℝ))]
    exact hrange1 (m + n)
  have hS2 : (∑ r : Fin (m + n), (rank r) ^ 2)
      = (↑(m + n) : ℝ) * ((↑(m + n) : ℝ) + 1) * (2 * (↑(m + n) : ℝ) + 1) / 6 := by
    simp only [hrank]
    rw [Fin.sum_univ_eq_sum_range (fun i => (((i + 1 : ℕ) : ℝ) ^ 2))]
    exact hrange2 (m + n)
  have hvident : variance
      = (1 / (P.card : ℝ)) * P.sum (fun A => (W A) ^ 2) - mean ^ 2 := by
    have h := statopia_math_node_1775715242_093567d1 (Finset (Fin (m + n))) P P.card rfl hcard0 W
    simpa only [hvar_def, hmean_def] using h
  have hsecond : (1 / (P.card : ℝ)) * P.sum (fun A => (W A) ^ 2)
      = ((m : ℝ) / (↑(m + n) : ℝ)) * (∑ r : Fin (m + n), (rank r) ^ 2)
        + (((m : ℝ) * ((m : ℝ) - 1)) / ((↑(m + n) : ℝ) * ((↑(m + n) : ℝ) - 1)))
            * ((∑ r : Fin (m + n), rank r) ^ 2 - (∑ r : Fin (m + n), (rank r) ^ 2)) := by
    have h := statopia_math_node_3549867032_1b9e5d41 (m + n) m hN2 hm hmN
    simpa only [hP, hrank, hW] using h
  have hN0R : (2 : ℝ) ≤ (↑(m + n) : ℝ) := by exact_mod_cast hN2
  have ht0 : (↑(m + n) : ℝ) ≠ 0 := by linarith
  have ht1 : (↑(m + n) : ℝ) - 1 ≠ 0 := by linarith
  have ht01 : (↑(m + n) : ℝ) * ((↑(m + n) : ℝ) - 1) ≠ 0 := mul_ne_zero ht0 ht1
  have hn_eq : (n : ℝ) = (↑(m + n) : ℝ) - (m : ℝ) := by
    have h2 : ((m + n - m : ℕ) : ℝ) = (↑(m + n) : ℝ) - (m : ℝ) := Nat.cast_sub hmN
    have h3 : m + n - m = n := by omega
    rw [h3] at h2
    exact h2
  refine ⟨?_, ?_⟩
  · rw [hmean_def]
    exact hmean
  · rw [hvident, hsecond, hS1, hS2]
    rw [hmean_def, hmean]
    rw [hn_eq]
    field_simp
    ring
  /- @proof-region region.root.d68da32f4e51 end -/

end Msc62GroundTruth
