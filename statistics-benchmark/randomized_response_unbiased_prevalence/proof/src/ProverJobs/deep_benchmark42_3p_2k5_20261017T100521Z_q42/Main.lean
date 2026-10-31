import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q42.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q42.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q42.Base

namespace Msc62GroundTruth

theorem randomized_response_unbiased_prevalence
    (n : ℕ) (hn : 1 ≤ n)
    (q : ℝ) (hq_half : (1 : ℝ) / 2 < q) (hq_le_one : q ≤ 1)
    (x : Fin n → Bool) :
    let bit : Bool → ℝ := fun b => if b then 1 else 0
    let prevalence : ℝ := (1 / (n : ℝ)) * ∑ i : Fin n, bit (x i)
    let reportProb : (Fin n → Bool) → ℝ :=
      fun y => ∏ i : Fin n, if y i = x i then q else 1 - q
    let reportedMean : (Fin n → Bool) → ℝ :=
      fun y => (1 / (n : ℝ)) * ∑ i : Fin n, bit (y i)
    let debiased : (Fin n → Bool) → ℝ :=
      fun y => (reportedMean y - (1 - q)) / (2 * q - 1)
    (∑ y : Fin n → Bool, reportProb y * debiased y) = prevalence
:= by
  /- @proof-region region.root.29a24260fa46 begin -/
  show (∑ y : Fin n → Bool,
      (∏ i : Fin n, (if y i = x i then q else 1 - q)) *
        (((1 / (n : ℝ)) * ∑ i : Fin n, (if y i then (1 : ℝ) else 0) - (1 - q)) / (2 * q - 1)))
    = (1 / (n : ℝ)) * ∑ i : Fin n, (if x i then (1 : ℝ) else 0)
  have hd : (2 : ℝ) * q - 1 ≠ 0 := by
    have h : (0 : ℝ) < 2 * q - 1 := by linarith
    exact ne_of_gt h
  have h1 : (∑ y : Fin n → Bool, ∏ i : Fin n, (if y i = x i then q else 1 - q)) = 1 := by
    simpa only using statopia_math_node_3469730755_08c680cd n q x
  have h2 :
      (∑ y : Fin n → Bool,
          (∏ i : Fin n, (if y i = x i then q else 1 - q)) *
            ((1 / (n : ℝ)) * ∑ i : Fin n, (if y i then (1 : ℝ) else 0)))
        = (1 - q) + (2 * q - 1) * ((1 / (n : ℝ)) * ∑ i : Fin n, (if x i then (1 : ℝ) else 0)) := by
    simpa only using statopia_math_node_3416877917_94a68e1c n hn q x
  have key : ∀ y : Fin n → Bool,
      (∏ i : Fin n, (if y i = x i then q else 1 - q)) *
          (((1 / (n : ℝ)) * ∑ i : Fin n, (if y i then (1 : ℝ) else 0) - (1 - q)) / (2 * q - 1))
        = (1 / (2 * q - 1)) *
            ((∏ i : Fin n, (if y i = x i then q else 1 - q)) *
                ((1 / (n : ℝ)) * ∑ i : Fin n, (if y i then (1 : ℝ) else 0))
              - (1 - q) * (∏ i : Fin n, (if y i = x i then q else 1 - q))) := by
    intro y
    rw [div_eq_mul_inv]
    ring
  calc (∑ y : Fin n → Bool,
      (∏ i : Fin n, (if y i = x i then q else 1 - q)) *
        (((1 / (n : ℝ)) * ∑ i : Fin n, (if y i then (1 : ℝ) else 0) - (1 - q)) / (2 * q - 1)))
      = ∑ y : Fin n → Bool, (1 / (2 * q - 1)) *
          ((∏ i : Fin n, (if y i = x i then q else 1 - q)) *
              ((1 / (n : ℝ)) * ∑ i : Fin n, (if y i then (1 : ℝ) else 0))
            - (1 - q) * (∏ i : Fin n, (if y i = x i then q else 1 - q))) := by
        refine Finset.sum_congr rfl ?_
        intro y _
        exact key y
    _ = (1 / (2 * q - 1)) *
          ∑ y : Fin n → Bool,
            ((∏ i : Fin n, (if y i = x i then q else 1 - q)) *
                ((1 / (n : ℝ)) * ∑ i : Fin n, (if y i then (1 : ℝ) else 0))
              - (1 - q) * (∏ i : Fin n, (if y i = x i then q else 1 - q))) := by
        rw [Finset.mul_sum]
    _ = (1 / (2 * q - 1)) *
          ((∑ y : Fin n → Bool,
              (∏ i : Fin n, (if y i = x i then q else 1 - q)) *
                ((1 / (n : ℝ)) * ∑ i : Fin n, (if y i then (1 : ℝ) else 0)))
            - ∑ y : Fin n → Bool,
                (1 - q) * (∏ i : Fin n, (if y i = x i then q else 1 - q))) := by
        rw [Finset.sum_sub_distrib]
    _ = (1 / (2 * q - 1)) *
          ((∑ y : Fin n → Bool,
              (∏ i : Fin n, (if y i = x i then q else 1 - q)) *
                ((1 / (n : ℝ)) * ∑ i : Fin n, (if y i then (1 : ℝ) else 0)))
            - (1 - q) * ∑ y : Fin n → Bool,
                (∏ i : Fin n, (if y i = x i then q else 1 - q))) := by
        rw [← Finset.mul_sum]
    _ = (1 / (2 * q - 1)) *
          ((1 - q) + (2 * q - 1) * ((1 / (n : ℝ)) * ∑ i : Fin n, (if x i then (1 : ℝ) else 0))
            - (1 - q) * 1) := by
        rw [h2, h1]
    _ = (1 / (n : ℝ)) * ∑ i : Fin n, (if x i then (1 : ℝ) else 0) := by
        have hX : (1 - q) + (2 * q - 1) * ((1 / (n : ℝ)) * ∑ i : Fin n, (if x i then (1 : ℝ) else 0))
            - (1 - q) * 1
            = (2 * q - 1) * ((1 / (n : ℝ)) * ∑ i : Fin n, (if x i then (1 : ℝ) else 0)) := by
          ring
        rw [hX, one_div, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]
  /- @proof-region region.root.29a24260fa46 end -/

end Msc62GroundTruth
