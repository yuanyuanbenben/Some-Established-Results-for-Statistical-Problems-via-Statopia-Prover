import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q21.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q21.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q21.Base

open Finset
namespace Msc62GroundTruth

theorem finite_population_correction_srs
    (N n : ℕ) (hN : 2 ≤ N) (hn_pos : 1 ≤ n) (hn_le : n ≤ N)
    (y : Fin N → ℝ) :
    let samples : Finset (Finset (Fin N)) :=
      (Finset.univ : Finset (Finset (Fin N))).filter (fun S => S.card = n)
    let mu : ℝ := (1 / (N : ℝ)) * ∑ i : Fin N, y i
    let sampleMean : Finset (Fin N) → ℝ :=
      fun S => (1 / (n : ℝ)) * S.sum (fun i => y i)
    let popVar : ℝ :=
      (1 / ((N - 1 : ℕ) : ℝ)) * ∑ i : Fin N, (y i - mu) ^ 2
    let varSampleMean : ℝ :=
      (1 / (samples.card : ℝ)) *
        samples.sum (fun S => (sampleMean S - mu) ^ 2)
    varSampleMean =
      (1 - (n : ℝ) / (N : ℝ)) * popVar / (n : ℝ)
:= by
  /- @proof-region region.root.a74ce13a4a70 begin -/
  dsimp only
  have hn0 : (n : ℝ) ≠ 0 := by
    have h : (0 : ℕ) < n := by omega
    have h' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h
    linarith
  have hN0 : (N : ℝ) ≠ 0 := by
    have h : (0 : ℕ) < N := by omega
    have h' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast h
    linarith
  have hNm1 : (((N - 1 : ℕ)) : ℝ) ≠ 0 := by
    have h : (0 : ℕ) < N - 1 := by omega
    have h' : (0 : ℝ) < (((N - 1 : ℕ)) : ℝ) := by exact_mod_cast h
    linarith
  let mu : ℝ := (1 / (N : ℝ)) * ∑ i : Fin N, y i
  have hmu : mu = (1 / (N : ℝ)) * ∑ i : Fin N, y i := rfl
  let A : ℝ := ∑ i : Fin N, (y i - mu) ^ 2
  have hAdef : A = ∑ i : Fin N, (y i - mu) ^ 2 := rfl
  let PV : ℝ := (1 / ((N - 1 : ℕ) : ℝ)) * A
  have hPVdef : PV = (1 / ((N - 1 : ℕ) : ℝ)) * A := rfl
  let c : ℝ := (((Finset.univ : Finset (Finset (Fin N))).filter (fun S => S.card = n)).card : ℝ)
  have hcdef : c = (((Finset.univ : Finset (Finset (Fin N))).filter (fun S => S.card = n)).card : ℝ) := rfl
  let V : ℝ := 1 / c * ((Finset.univ : Finset (Finset (Fin N))).filter (fun S => S.card = n)).sum
      (fun S => ((1 / (n : ℝ)) * S.sum (fun i => y i) - mu) ^ 2)
  have hVdef : V = 1 / c * ((Finset.univ : Finset (Finset (Fin N))).filter (fun S => S.card = n)).sum
      (fun S => ((1 / (n : ℝ)) * S.sum (fun i => y i) - mu) ^ 2) := rfl
  show V = (1 - (n : ℝ) / (N : ℝ)) * PV / (n : ℝ)
  have hP : ((Finset.univ : Finset (Finset (Fin N))).filter (fun S => S.card = n))
      = (Finset.univ : Finset (Fin N)).powersetCard n := by
    ext S
    simp [Finset.mem_powersetCard]
  have hcN : c = (N.choose n : ℝ) := by
    rw [hcdef, hP, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hchoose0 : (N.choose n : ℝ) ≠ 0 := by
    have h : 0 < N.choose n := Nat.choose_pos hn_le
    have h' : (0 : ℝ) < (N.choose n : ℝ) := by exact_mod_cast h
    linarith
  have hsum : ∑ i : Fin N, (y i - mu) = 0 := by
    rw [Finset.sum_sub_distrib]
    have h2 : ∑ _i : Fin N, mu = (N : ℝ) * mu := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h3 : (N : ℝ) * mu = ∑ i : Fin N, y i := by
      rw [hmu, ← mul_assoc, one_div, mul_inv_cancel₀ hN0, one_mul]
    rw [h2, h3, sub_self]
  have hper : ∀ S ∈ (Finset.univ : Finset (Finset (Fin N))).filter (fun S => S.card = n),
      (1 / (n : ℝ)) * S.sum (fun i => y i) - mu
        = (1 / (n : ℝ)) * S.sum (fun i => y i - mu) := by
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    have h1 : S.sum (fun i => y i - mu) = S.sum (fun i => y i) - (n : ℝ) * mu := by
      rw [Finset.sum_sub_distrib]
      congr 1
      rw [Finset.sum_const, hS, nsmul_eq_mul]
    have h2 : (1 / (n : ℝ)) * ((n : ℝ) * mu) = mu := by
      rw [← mul_assoc, one_div, inv_mul_cancel₀ hn0, one_mul]
    rw [h1, mul_sub, h2]
  have hsq : ((Finset.univ : Finset (Finset (Fin N))).filter (fun S => S.card = n)).sum
        (fun S => ((1 / (n : ℝ)) * S.sum (fun i => y i) - mu) ^ 2)
      = (1 / (n : ℝ)) ^ 2
        * (((Finset.univ : Finset (Finset (Fin N))).filter (fun S => S.card = n)).sum
          (fun S => (S.sum (fun i => y i - mu)) ^ 2)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro S hS
    rw [hper S hS, mul_pow]
  have hT : ((Finset.univ : Finset (Fin N)).powersetCard n).sum
        (fun S => (S.sum (fun i => y i - mu)) ^ 2)
      = ((((N - 2).choose (n - 1) : ℕ)) : ℝ) * A := by
    have hn := statopia_math_node_2421082732_9eff0878 N n hN hn_pos hn_le
      (fun i : Fin N => y i - mu) hsum
    simpa [hAdef] using hn
  have hAeq : A = (((N - 1 : ℕ)) : ℝ) * PV := by
    rw [hPVdef, ← mul_assoc, one_div, mul_inv_cancel₀ hNm1, one_mul]
  have hratio := statopia_math_node_781651629_73b8feb2 N n hN hn_pos hn_le
  have hX : ((((N - 2).choose (n - 1) : ℕ)) : ℝ)
      = ((n : ℝ) * ((N - n : ℕ) : ℝ) / ((N : ℝ) * (((N - 1 : ℕ)) : ℝ)))
        * (N.choose n : ℝ) := by
    rw [← hratio]
    field_simp
    try ring
  rw [hVdef, hsq, hP, hT, hAeq, hcN, hX]
  have hNn : ((N - n : ℕ) : ℝ) = (N : ℝ) - (n : ℝ) := Nat.cast_sub hn_le
  rw [show (1 - (n : ℝ) / (N : ℝ)) * PV / (n : ℝ)
      = ((N : ℝ) - (n : ℝ)) / ((n : ℝ) * (N : ℝ)) * PV from by
    field_simp
    try ring]
  rw [← hNn]
  field_simp
  try ring
  /- @proof-region region.root.a74ce13a4a70 end -/

end Msc62GroundTruth
