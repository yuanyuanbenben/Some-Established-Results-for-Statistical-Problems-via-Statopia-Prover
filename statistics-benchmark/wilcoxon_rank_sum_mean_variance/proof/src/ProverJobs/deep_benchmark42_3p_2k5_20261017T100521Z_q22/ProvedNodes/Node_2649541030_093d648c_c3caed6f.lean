import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q22.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q22.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q22.ProvedNodes.Node_3704713494_2c790cca_6d508c1d
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q22.ProvedNodes.Node_945440442_dbf9c5cc_12f0b06c


open Finset
open Msc62GroundTruth

open Finset
namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_2649541030_093d648c : ∀ (N m : ℕ) (hN : 1 ≤ N) (hm : 1 ≤ m)
    (hmN : m ≤ N),
    let P : Finset (Finset (Fin N)) := (Finset.univ : Finset (Fin N)).powersetCard m
    let rank : Fin N → ℝ := fun r => ((r.val + 1 : ℕ) : ℝ)
    let W : Finset (Fin N) → ℝ := fun A => A.sum (fun r => rank r)
    (1 / (P.card : ℝ)) * P.sum (fun A => W A) = (m : ℝ) * ((N : ℝ) + 1) / 2 := by
  /- @proof-region region.target-node.session.5b010ff24bc22ece begin -/
  intro N m hN hm hmN
  dsimp only
  set P : Finset (Finset (Fin N)) := (Finset.univ : Finset (Fin N)).powersetCard m with hP
  have hS1 : (∑ r : Fin N, ((r.val + 1 : ℕ) : ℝ)) = (N : ℝ) * ((N : ℝ) + 1) / 2 :=
    (statopia_math_node_3704713494_2c790cca N hN).1
  have hcount : ∀ r : Fin N, (P.filter (fun A => r ∈ A)).card = (N - 1).choose (m - 1) := by
    intro r
    rw [hP]
    exact statopia_math_node_945440442_dbf9c5cc N m hm hmN r
  have hcard : P.card = N.choose m := by
    rw [hP, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hinner : ∀ A : Finset (Fin N),
      A.sum (fun r => ((r.val + 1 : ℕ) : ℝ))
        = ∑ r : Fin N, (if r ∈ A then ((r.val + 1 : ℕ) : ℝ) else 0) := by
    intro A
    rw [show A.sum (fun r => ((r.val + 1 : ℕ) : ℝ))
        = ∑ r ∈ A, (if r ∈ A then ((r.val + 1 : ℕ) : ℝ) else 0) from by
      apply Finset.sum_congr rfl
      intro r hr
      rw [if_pos hr]]
    exact Finset.sum_subset (Finset.subset_univ A) (fun r _ hr => if_neg hr)
  have hstep : ∀ r : Fin N, P.sum (fun A => (if r ∈ A then ((r.val + 1 : ℕ) : ℝ) else 0))
      = ((N - 1).choose (m - 1) : ℝ) * ((r.val + 1 : ℕ) : ℝ) := by
    intro r
    rw [← Finset.sum_filter (s := P) (p := fun A => r ∈ A)
      (f := fun _ => ((r.val + 1 : ℕ) : ℝ))]
    rw [Finset.sum_const, hcount r, nsmul_eq_mul]
  have hdc : P.sum (fun A => A.sum (fun r => ((r.val + 1 : ℕ) : ℝ)))
      = ((N - 1).choose (m - 1) : ℝ) * (∑ r : Fin N, ((r.val + 1 : ℕ) : ℝ)) := by
    calc P.sum (fun A => A.sum (fun r => ((r.val + 1 : ℕ) : ℝ)))
        = P.sum (fun A => ∑ r : Fin N, (if r ∈ A then ((r.val + 1 : ℕ) : ℝ) else 0)) :=
            Finset.sum_congr rfl (fun A _ => hinner A)
      _ = ∑ r : Fin N, P.sum (fun A => (if r ∈ A then ((r.val + 1 : ℕ) : ℝ) else 0)) :=
            Finset.sum_comm
      _ = ∑ r : Fin N, ((N - 1).choose (m - 1) : ℝ) * ((r.val + 1 : ℕ) : ℝ) :=
            Finset.sum_congr rfl (fun r _ => hstep r)
      _ = ((N - 1).choose (m - 1) : ℝ) * (∑ r : Fin N, ((r.val + 1 : ℕ) : ℝ)) :=
            (Finset.mul_sum _ _ _).symm
  have hbinom : (P.card : ℝ) * (m : ℝ) = (N : ℝ) * ((N - 1).choose (m - 1) : ℝ) := by
    have h' : N.choose m * m = N * (N - 1).choose (m - 1) := by
      simpa only [Nat.choose_one_right] using Nat.choose_mul (n := N) (k := m) (s := 1) hm
    have h'' : ((N.choose m * m : ℕ) : ℝ) = ((N * (N - 1).choose (m - 1) : ℕ) : ℝ) := by
      rw [h']
    push_cast at h''
    rw [hcard]
    exact h''
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hPpos : (0 : ℝ) < (P.card : ℝ) := by
    have hpos : 0 < N.choose m := Nat.choose_pos hmN
    rw [hcard]
    exact_mod_cast hpos
  have hN0 : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hP0 : (P.card : ℝ) ≠ 0 := ne_of_gt hPpos
  have hc : ((N - 1).choose (m - 1) : ℝ) = (P.card : ℝ) * (m : ℝ) / (N : ℝ) := by
    rw [eq_div_iff hN0]
    linarith [hbinom]
  rw [hdc, hS1, hc]
  field_simp
  /- @proof-region region.target-node.session.5b010ff24bc22ece end -/

end Msc62GroundTruth
