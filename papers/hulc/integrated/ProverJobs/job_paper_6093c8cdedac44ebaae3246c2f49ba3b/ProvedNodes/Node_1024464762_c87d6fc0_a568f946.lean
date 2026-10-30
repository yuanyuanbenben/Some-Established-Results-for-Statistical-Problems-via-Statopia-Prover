import ProverJobs.job_paper_6093c8cdedac44ebaae3246c2f49ba3b.Vocabulary
import ProverJobs.job_paper_6093c8cdedac44ebaae3246c2f49ba3b.Base

namespace PaperProofTasks.job_paper_6093c8cdedac44ebaae3246c2f49ba3b

open MeasureTheory ProbabilityTheory
open _root_.PaperProofTasks.job_paper_6093c8cdedac44ebaae3246c2f49ba3b.Statlib.Imported

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
open _root_.Statlib
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_1024464762_c87d6fc0 : ∀ (s t : ℝ) (n : ℕ) (x y : Fin n → ℝ)
    (hs_lower : (1 / 2 : ℝ) ≤ s) (hs_upper : s ≤ 1) (ht : t = 1 - s)
    (hx_nonneg : ∀ j : Fin n, 0 ≤ x j) (hx_le : ∀ j : Fin n, x j ≤ s)
    (hy_nonneg : ∀ j : Fin n, 0 ≤ y j) (hy_le : ∀ j : Fin n, y j ≤ s)
    (hxy : ∀ j : Fin n, x j + y j ≤ 1),
    (∏ j : Fin n, x j) + (∏ j : Fin n, y j) ≤ s ^ n + t ^ n := by
  /- @proof-region region.target-node.session.fe7288aa8b18b45e begin -/
  intro s t n
  induction n with
  | zero =>
      intro x y _ _ _ _ _ _ _ _
      simp
  | succ n ih =>
      intro x y hs_lower hs_upper ht hx_nonneg hx_le hy_nonneg hy_le hxy
      set P : ℝ := ∏ j : Fin n, x (Fin.castSucc j) with hP
      set Q : ℝ := ∏ j : Fin n, y (Fin.castSucc j) with hQ
      have ht0 : (0 : ℝ) ≤ t := by linarith
      have hst0 : (0 : ℝ) ≤ s - t := by linarith
      have hP0 : 0 ≤ P := by
        rw [hP]
        exact Finset.prod_nonneg (fun j _ => hx_nonneg (Fin.castSucc j))
      have hQ0 : 0 ≤ Q := by
        rw [hQ]
        exact Finset.prod_nonneg (fun j _ => hy_nonneg (Fin.castSucc j))
      have hPs : P ≤ s ^ n := by
        rw [hP]
        calc (∏ j : Fin n, x (Fin.castSucc j)) ≤ ∏ _j : Fin n, s :=
              Finset.prod_le_prod (fun j _ => hx_nonneg (Fin.castSucc j))
                (fun j _ => hx_le (Fin.castSucc j))
          _ = s ^ n := Fin.prod_const n s
      have hQs : Q ≤ s ^ n := by
        rw [hQ]
        calc (∏ j : Fin n, y (Fin.castSucc j)) ≤ ∏ _j : Fin n, s :=
              Finset.prod_le_prod (fun j _ => hy_nonneg (Fin.castSucc j))
                (fun j _ => hy_le (Fin.castSucc j))
          _ = s ^ n := Fin.prod_const n s
      have hsum : P + Q ≤ s ^ n + t ^ n := by
        rw [hP, hQ]
        exact ih (fun j => x (Fin.castSucc j)) (fun j => y (Fin.castSucc j))
          hs_lower hs_upper ht (fun j => hx_nonneg (Fin.castSucc j))
          (fun j => hx_le (Fin.castSucc j))
          (fun j => hy_nonneg (Fin.castSucc j)) (fun j => hy_le (Fin.castSucc j))
          (fun j => hxy (Fin.castSucc j))

      have hxprod : (∏ j : Fin (n + 1), x j) = x (Fin.last n) * P := by
        rw [Fin.prod_univ_castSucc, ← hP, mul_comm]
      have hyprod : (∏ j : Fin (n + 1), y j) = y (Fin.last n) * Q := by
        rw [Fin.prod_univ_castSucc, ← hQ, mul_comm]
      have hmain : x (Fin.last n) * P + y (Fin.last n) * Q ≤ s ^ (n + 1) + t ^ (n + 1) := by
        have hxlast : x (Fin.last n) ≤ s := hx_le (Fin.last n)
        have hylast : y (Fin.last n) ≤ s := hy_le (Fin.last n)
        have hxylast : x (Fin.last n) + y (Fin.last n) ≤ 1 := hxy (Fin.last n)
        have hs1 : s * s ^ n = s ^ (n + 1) := by rw [pow_succ, mul_comm]
        have ht1 : t * t ^ n = t ^ (n + 1) := by rw [pow_succ, mul_comm]
        rcases le_total Q P with hPQ | hQP
        · have h1 : x (Fin.last n) * P + y (Fin.last n) * Q
              = x (Fin.last n) * (P - Q) + (x (Fin.last n) + y (Fin.last n)) * Q := by ring
          have h2 : x (Fin.last n) * (P - Q) ≤ s * (P - Q) :=
            mul_le_mul_of_nonneg_right hxlast (by linarith)
          have h3 : (x (Fin.last n) + y (Fin.last n)) * Q ≤ 1 * Q :=
            mul_le_mul_of_nonneg_right hxylast hQ0
          have h4 : x (Fin.last n) * P + y (Fin.last n) * Q ≤ s * P + t * Q := by
            calc x (Fin.last n) * P + y (Fin.last n) * Q
                = x (Fin.last n) * (P - Q) + (x (Fin.last n) + y (Fin.last n)) * Q := h1
              _ ≤ s * (P - Q) + 1 * Q := add_le_add h2 h3
              _ = s * P + t * Q := by rw [one_mul, ht]; ring
          have h5 : s * P + t * Q = (s - t) * P + t * (P + Q) := by ring
          have h6 : (s - t) * P ≤ (s - t) * s ^ n := mul_le_mul_of_nonneg_left hPs hst0
          have h7 : t * (P + Q) ≤ t * (s ^ n + t ^ n) := mul_le_mul_of_nonneg_left hsum ht0
          have h8 : s * P + t * Q ≤ s * s ^ n + t * t ^ n := by
            calc s * P + t * Q = (s - t) * P + t * (P + Q) := h5
              _ ≤ (s - t) * s ^ n + t * (s ^ n + t ^ n) := add_le_add h6 h7
              _ = s * s ^ n + t * t ^ n := by ring
          linarith
        · have h1 : x (Fin.last n) * P + y (Fin.last n) * Q
              = y (Fin.last n) * (Q - P) + (x (Fin.last n) + y (Fin.last n)) * P := by ring
          have h2 : y (Fin.last n) * (Q - P) ≤ s * (Q - P) :=
            mul_le_mul_of_nonneg_right hylast (by linarith)
          have h3 : (x (Fin.last n) + y (Fin.last n)) * P ≤ 1 * P :=
            mul_le_mul_of_nonneg_right hxylast hP0
          have h4 : x (Fin.last n) * P + y (Fin.last n) * Q ≤ s * Q + t * P := by
            calc x (Fin.last n) * P + y (Fin.last n) * Q
                = y (Fin.last n) * (Q - P) + (x (Fin.last n) + y (Fin.last n)) * P := h1
              _ ≤ s * (Q - P) + 1 * P := add_le_add h2 h3
              _ = s * Q + t * P := by rw [one_mul, ht]; ring
          have h5 : s * Q + t * P = (s - t) * Q + t * (P + Q) := by ring
          have h6 : (s - t) * Q ≤ (s - t) * s ^ n := mul_le_mul_of_nonneg_left hQs hst0
          have h7 : t * (P + Q) ≤ t * (s ^ n + t ^ n) := mul_le_mul_of_nonneg_left hsum ht0
          have h8 : s * Q + t * P ≤ s * s ^ n + t * t ^ n := by
            calc s * Q + t * P = (s - t) * Q + t * (P + Q) := h5
              _ ≤ (s - t) * s ^ n + t * (s ^ n + t ^ n) := add_le_add h6 h7
              _ = s * s ^ n + t * t ^ n := by ring
          linarith
      rw [hxprod, hyprod]
      exact hmain
  /- @proof-region region.target-node.session.fe7288aa8b18b45e end -/

end

end Statlib.Imported

