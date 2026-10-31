import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q22.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q22.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q22.ProvedNodes.Node_274088598_752ee41e_3bb2dc4e
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q22.ProvedNodes.Node_945440442_dbf9c5cc_12f0b06c


open Finset
open Msc62GroundTruth

open Finset
namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_3549867032_1b9e5d41 : ∀ (N m : ℕ) (hN : 2 ≤ N) (hm : 1 ≤ m)
    (hmN : m ≤ N),
    let P : Finset (Finset (Fin N)) := (Finset.univ : Finset (Fin N)).powersetCard m
    let rank : Fin N → ℝ := fun r => ((r.val + 1 : ℕ) : ℝ)
    let W : Finset (Fin N) → ℝ := fun A => A.sum (fun r => rank r)
    let S1 : ℝ := (Finset.univ : Finset (Fin N)).sum (fun r => rank r)
    let S2 : ℝ := (Finset.univ : Finset (Fin N)).sum (fun r => (rank r) ^ 2)
    (1 / (P.card : ℝ)) * P.sum (fun A => (W A) ^ 2)
      = ((m : ℝ) / (N : ℝ)) * S2
        + (((m : ℝ) * ((m : ℝ) - 1)) / ((N : ℝ) * ((N : ℝ) - 1))) * (S1 ^ 2 - S2) := by
  /- @proof-region region.target-node.session.f00651ac984b0c18 begin -/
  intro N m hN hm hmN
  simp only []
  set P : Finset (Finset (Fin N)) := (Finset.univ : Finset (Fin N)).powersetCard m with hP
  set C : ℝ := (P.card : ℝ) with hC
  set rank : Fin N → ℝ := fun r => ((r.val + 1 : ℕ) : ℝ) with hrank
  set S1 : ℝ := ∑ r : Fin N, rank r with hS1
  set S2 : ℝ := ∑ r : Fin N, (rank r) ^ 2 with hS2
  set co : ℝ := ((m : ℝ) * ((m : ℝ) - 1)) / ((N : ℝ) * ((N : ℝ) - 1)) with hcodef
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNr0 : (N : ℝ) ≠ 0 := by linarith
  have hNr1 : (N : ℝ) - 1 ≠ 0 := by linarith
  have hPcard : P.card = N.choose m := by
    rw [hP, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hC0 : C ≠ 0 := by
    rw [hC, hPcard]
    have hpos : (0 : ℝ) < ((N.choose m : ℕ) : ℝ) := by exact_mod_cast Nat.choose_pos hmN
    exact ne_of_gt hpos
  have hsq : (∑ r : Fin N, rank r * rank r) = S2 := by
    rw [hS2]
    apply Finset.sum_congr rfl
    intro r _
    rw [pow_two]
  have hW : ∀ A : Finset (Fin N), A.sum rank = ∑ r : Fin N, if r ∈ A then rank r else 0 := by
    intro A
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun x _ => rfl)
    ext x
    simp
  have hW2 : ∀ A : Finset (Fin N), (A.sum rank) ^ 2
      = ∑ r : Fin N, ∑ s : Fin N,
          (if r ∈ A then rank r else 0) * (if s ∈ A then rank s else 0) := by
    intro A
    rw [hW A, pow_two, Finset.sum_mul_sum]
  have hprod : ∀ (A : Finset (Fin N)) (r s : Fin N),
      (if r ∈ A then rank r else 0) * (if s ∈ A then rank s else 0)
        = if r ∈ A ∧ s ∈ A then rank r * rank s else 0 := by
    intro A r s
    by_cases hr : r ∈ A <;> by_cases hs : s ∈ A <;> simp [hr, hs]
  have hconst : ∀ (p : Finset (Fin N) → Prop) [DecidablePred p] (c : ℝ),
      P.sum (fun A => if p A then c else 0) = ((P.filter p).card : ℝ) * c := by
    intro p _ c
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hswap : P.sum (fun A => ∑ r : Fin N, ∑ s : Fin N,
        (if r ∈ A then rank r else 0) * (if s ∈ A then rank s else 0))
      = ∑ r : Fin N, ∑ s : Fin N, P.sum (fun A =>
        (if r ∈ A then rank r else 0) * (if s ∈ A then rank s else 0)) := by
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    conv_lhs => rw [Finset.sum_comm]
  have key : P.sum (fun A => (A.sum rank) ^ 2)
      = ∑ r : Fin N, ∑ s : Fin N,
          ((P.filter (fun A => r ∈ A ∧ s ∈ A)).card : ℝ) * (rank r * rank s) := by
    have h1 : P.sum (fun A => (A.sum rank) ^ 2)
        = P.sum (fun A => ∑ r : Fin N, ∑ s : Fin N,
            (if r ∈ A then rank r else 0) * (if s ∈ A then rank s else 0)) :=
      Finset.sum_congr rfl (fun A _ => hW2 A)
    rw [h1, hswap]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.sum_congr rfl (fun A _ => hprod A r s)]
    exact hconst (fun A => r ∈ A ∧ s ∈ A) (rank r * rank s)
  have hdiagcnt : ∀ r : Fin N,
      ((P.filter (fun A => r ∈ A ∧ r ∈ A)).card : ℝ) = ((N - 1).choose (m - 1) : ℝ) := by
    intro r
    have h1 : (P.filter (fun A => r ∈ A ∧ r ∈ A)) = P.filter (fun A => r ∈ A) := by
      ext A
      simp
    rw [h1]
    have h3 := statopia_math_node_945440442_dbf9c5cc N m hm hmN r
    rw [← hP] at h3
    exact_mod_cast h3
  have hoffcnt : ∀ (r s : Fin N), r ≠ s →
      ((P.filter (fun A => r ∈ A ∧ s ∈ A)).card : ℝ) = C * co := by
    intro r s hrs
    have h := statopia_math_node_274088598_752ee41e N m hN hm hmN r s hrs
    have h2 : ((P.filter (fun A => r ∈ A ∧ s ∈ A)).card : ℝ) * ((N : ℝ) * ((N : ℝ) - 1))
        = C * ((m : ℝ) * ((m : ℝ) - 1)) := by
      rw [hC, hP]
      exact h
    rw [hcodef]
    have hD0 : ((N : ℝ) * ((N : ℝ) - 1)) ≠ 0 := mul_ne_zero hNr0 hNr1
    field_simp
    linarith [h2]
  have hTsplit : (∑ r : Fin N, ∑ s : Fin N,
        ((P.filter (fun A => r ∈ A ∧ s ∈ A)).card : ℝ) * (rank r * rank s))
      = (∑ r : Fin N, ((P.filter (fun A => r ∈ A ∧ r ∈ A)).card : ℝ) * (rank r * rank r))
        + ∑ r : Fin N, ∑ s ∈ (Finset.univ.erase r),
            ((P.filter (fun A => r ∈ A ∧ s ∈ A)).card : ℝ) * (rank r * rank s) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    conv_lhs => rw [← Finset.insert_erase (Finset.mem_univ r)]
    have hnot : r ∉ (Finset.univ.erase r) := by simp
    rw [Finset.sum_insert hnot]
  have hdiag : (∑ r : Fin N,
        ((P.filter (fun A => r ∈ A ∧ r ∈ A)).card : ℝ) * (rank r * rank r))
      = ((N - 1).choose (m - 1) : ℝ) * S2 := by
    calc (∑ r : Fin N, ((P.filter (fun A => r ∈ A ∧ r ∈ A)).card : ℝ) * (rank r * rank r))
        = ∑ r : Fin N, ((N - 1).choose (m - 1) : ℝ) * (rank r * rank r) := by
          apply Finset.sum_congr rfl
          intro r _
          rw [hdiagcnt r]
      _ = ((N - 1).choose (m - 1) : ℝ) * (∑ r : Fin N, rank r * rank r) := by
          rw [Finset.mul_sum]
      _ = ((N - 1).choose (m - 1) : ℝ) * S2 := by rw [hsq]
  have hS1sq : S1 ^ 2 = ∑ r : Fin N, ∑ s : Fin N, rank r * rank s := by
    rw [hS1, pow_two, Finset.sum_mul_sum]
  have hGG : (∑ r : Fin N, ∑ s : Fin N, rank r * rank s)
      = (∑ r : Fin N, rank r * rank r)
        + ∑ r : Fin N, ∑ s ∈ (Finset.univ.erase r), rank r * rank s := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    conv_lhs => rw [← Finset.insert_erase (Finset.mem_univ r)]
    have hnot : r ∉ (Finset.univ.erase r) := by simp
    rw [Finset.sum_insert hnot]
  have hoffdiag : (∑ r : Fin N, ∑ s ∈ (Finset.univ.erase r), rank r * rank s)
      = S1 ^ 2 - S2 := by
    have h := hS1sq
    rw [hGG] at h
    rw [hsq] at h
    linarith
  have hoffsum : (∑ r : Fin N, ∑ s ∈ (Finset.univ.erase r),
        ((P.filter (fun A => r ∈ A ∧ s ∈ A)).card : ℝ) * (rank r * rank s))
      = (C * co) * (S1 ^ 2 - S2) := by
    have h1 : ∀ (r s : Fin N), s ∈ (Finset.univ.erase r) →
        ((P.filter (fun A => r ∈ A ∧ s ∈ A)).card : ℝ) * (rank r * rank s)
          = (C * co) * (rank r * rank s) := by
      intro r s hs
      have hne : r ≠ s := by
        have h2 := (Finset.mem_erase.mp hs).1
        exact fun hh => h2 hh.symm
      rw [hoffcnt r s hne]
    calc (∑ r : Fin N, ∑ s ∈ (Finset.univ.erase r),
            ((P.filter (fun A => r ∈ A ∧ s ∈ A)).card : ℝ) * (rank r * rank s))
        = ∑ r : Fin N, ∑ s ∈ (Finset.univ.erase r), (C * co) * (rank r * rank s) := by
          apply Finset.sum_congr rfl
          intro r _
          apply Finset.sum_congr rfl
          intro s hs
          exact h1 r s hs
      _ = ∑ r : Fin N, (C * co) * (∑ s ∈ (Finset.univ.erase r), rank r * rank s) := by
          apply Finset.sum_congr rfl
          intro r _
          rw [Finset.mul_sum]
      _ = (C * co) * (∑ r : Fin N, ∑ s ∈ (Finset.univ.erase r), rank r * rank s) := by
          rw [Finset.mul_sum]
      _ = (C * co) * (S1 ^ 2 - S2) := by rw [hoffdiag]
  have hmain : P.sum (fun A => (A.sum rank) ^ 2)
      = ((N - 1).choose (m - 1) : ℝ) * S2 + (C * co) * (S1 ^ 2 - S2) := by
    rw [key, hTsplit, hdiag, hoffsum]
  have hchoose : N.choose m * m = N * (N - 1).choose (m - 1) := by
    have h := Nat.choose_mul (n := N) (k := m) (s := 1) hm
    rw [Nat.choose_one_right, Nat.choose_one_right] at h
    exact h
  have hcd : ((N - 1).choose (m - 1) : ℝ) = C * (m : ℝ) / (N : ℝ) := by
    have h2 : C * (m : ℝ) = (N : ℝ) * ((N - 1).choose (m - 1) : ℝ) := by
      rw [hC, hPcard]
      exact_mod_cast hchoose
    rw [eq_div_iff hNr0]
    linarith
  rw [hmain, hcd]
  field_simp
  /- @proof-region region.target-node.session.f00651ac984b0c18 end -/

end Msc62GroundTruth
