import Statlib.HighDim.Vocabulary.Norms
import ProverJobs.real_main_theorem_e7f39350f194.Vocabulary
import ProverJobs.real_main_theorem_e7f39350f194.Base
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_3431605529_2a745110_37ebd9aa
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_358362470_f6dd73c9_3c66278a
open EuclideanGeometry

open EuclideanGeometry

set_option autoImplicit false in
theorem statopia_math_node_1079600542_410cd104 : ∀ (A B C L N Y U : Plane) (t v s r2 : ℝ)
    (hN : N = midpoint ℝ A C)
    (hY : Y = A + s • (C - A))
    (hL : L = C + v • ((A + t • (B - A)) - C))
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    (ht : 0 < t) (ht1 : t < 1)
    (hv : 0 < v) (hv1 : v < 1)
    (hs : 0 < s) (hs1 : s < 1)
    (hInside : InsideTriangle B N C L)
    (hBU : ‖B - U‖ ^ 2 - r2 = 0)
    (hLU : ‖L - U‖ ^ 2 - r2 = 0)
    (hNU : ‖N - U‖ ^ 2 - r2 = 0)
    (hangle : ∠ L B Y = ∠ L N C)
    (hbranch : (1 - v) - (1 - v * t) * s > 0),
    2 * inner ℝ (C - A) (N - U) + (s - 1 / 2) * ‖C - A‖ ^ 2 = 0 := by
  /- @proof-region region.target-node.session.fe991945c1989544 begin -/
  intro A B C L N Y U t v s r2 hN hY hL hABC ht ht1 hv hv1 hs hs1 hInside hBU hLU hNU hangle hbranch
  set p : Plane := B - A with hp
  set q : Plane := C - A with hq
  set W : Plane := U - A with hW
  set g : ℝ := inner ℝ p p with hg
  set hh : ℝ := inner ℝ p q with hhh
  set b2 : ℝ := inner ℝ q q with hb2
  set a : ℝ := v * t with ha
  set c : ℝ := 1 - v with hc
  set ga : ℝ := a + 2 * c - 1 with hga
  set Wq : ℝ := inner ℝ q W with hWq
  have hB_eq : B = A + p := by rw [hp]; abel
  have hU_eq : U = A + W := by rw [hW]; abel
  have hC_eq : C = A + q := by rw [hq]; abel
  have hN_eq : N = A + (1 / 2 : ℝ) • q := by
    rw [hN, hC_eq, midpoint_eq_smul_add]
    rw [show (⅟(2 : ℝ) : ℝ) = 1 / 2 by norm_num]
    module
  have hL_eq : L = A + a • p + c • q := by
    rw [hL, hC_eq]
    module
  have hcomm : ∀ x y : Plane, inner ℝ x y = inner ℝ y x := by
    intro x y
    rw [Statlib.HighDim.Vocabulary.inner_eq_sum, Statlib.HighDim.Vocabulary.inner_eq_sum]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hnorm : ∀ x : Plane, ‖x‖ ^ 2 = inner ℝ x x := fun x => by
    rw [real_inner_self_eq_norm_sq]
  have hsm : ∀ (r : ℝ) (x y : Plane), inner ℝ (r • x) y = r * inner ℝ x y := by
    intro r x y
    rw [hcomm (r • x) y, inner_smul_right, hcomm x y]
  have hexp : ∀ x y : Plane,
      inner ℝ (x - y) (x - y) = inner ℝ x x - 2 * inner ℝ x y + inner ℝ y y := by
    intro x y
    rw [inner_sub_left, inner_sub_right, inner_sub_right, hcomm y x]
    ring
  have hsum : ∀ x y : Plane, inner ℝ (x + y) (x + y)
      = inner ℝ x x + 2 * inner ℝ x y + inner ℝ y y := by
    intro x y
    rw [inner_add_left, inner_add_right, inner_add_right, hcomm y x]
    ring
  have huu : ∀ α β : ℝ, inner ℝ (α • p + β • q) (α • p + β • q)
      = α ^ 2 * g + 2 * α * β * hh + β ^ 2 * b2 := by
    intro α β
    rw [hsum]
    simp only [hsm, inner_smul_right, ← hg, ← hhh, ← hb2]
    ring
  have huW : ∀ α β : ℝ, inner ℝ (α • p + β • q) W
      = α * inner ℝ p W + β * inner ℝ q W := by
    intro α β
    simp only [inner_add_left, hsm]
  have eqB : ‖B - U‖ ^ 2 - r2 = g - 2 * inner ℝ p W + (‖W‖ ^ 2 - r2) := by
    have hsub : B - U = p - W := by rw [hB_eq, hU_eq]; module
    rw [hsub, hnorm, hexp, ← hg, ← hnorm W]
    ring
  have eqN : ‖N - U‖ ^ 2 - r2 = b2 / 4 - inner ℝ q W + (‖W‖ ^ 2 - r2) := by
    have hsub : N - U = (1 / 2 : ℝ) • q - W := by rw [hN_eq, hU_eq]; module
    rw [hsub, hnorm, hexp]
    simp only [hsm, inner_smul_right, ← hb2]
    rw [← hnorm W]
    ring
  have eqL : ‖L - U‖ ^ 2 - r2
      = a ^ 2 * g + 2 * a * c * hh + c ^ 2 * b2 - 2 * a * inner ℝ p W
        - 2 * c * inner ℝ q W + (‖W‖ ^ 2 - r2) := by
    have hsub : L - U = a • p + c • q - W := by rw [hL_eq, hU_eq]; module
    rw [hsub, hnorm, hexp, huu a c, huW a c, ← hnorm W]
    ring
  have zB : g - 2 * inner ℝ p W + (‖W‖ ^ 2 - r2) = 0 := by linarith [hBU, eqB]
  have zN : b2 / 4 - inner ℝ q W + (‖W‖ ^ 2 - r2) = 0 := by linarith [hNU, eqN]
  have zL : a ^ 2 * g + 2 * a * c * hh + c ^ 2 * b2 - 2 * a * inner ℝ p W
      - 2 * c * inner ℝ q W + (‖W‖ ^ 2 - r2) = 0 := by linarith [hLU, eqL]
  have hcirc : Wq * ga = g * (a ^ 2 - a) + 2 * a * c * hh + b2 * (c ^ 2 - 1 / 4 + a / 4) := by
    rw [hga, hWq]
    linear_combination a * zB - (a - 1) * zN - zL
  have hL_eq' : L = A + a • (B - A) + c • (C - A) := by rw [hL_eq, hp, hq]
  have hN_eq' : N = A + (1 / 2 : ℝ) • (C - A) := by rw [hN_eq, hq]
  have hY' : Y = A + s • (C - A) := by rw [hY, hq]
  have ha' : 0 < a := by rw [ha]; exact mul_pos hv ht
  have ha1' : a < 1 := by
    rw [ha, mul_comm]
    linarith [mul_lt_mul_of_pos_right ht1 hv, hv1]
  have hc' : 0 < c := by rw [hc]; linarith
  have hc1' : c < 1 := by rw [hc]; linarith
  have hstep := statopia_math_node_358362470_f6dd73c9 A B C L N Y a c s hABC hL_eq' hN_eq' hY'
    hInside ha' ha1' hc' hc1' hs hs1 hbranch hangle
  have hgane : ga ≠ 0 := by
    rw [hga]
    exact ne_of_gt hstep.1
  have hang : s * b2 * ga = 2 * g * (a ^ 2 - a) + 4 * a * c * hh + b2 * c * (2 * c - 1) := by
    have h2 := hstep.2
    have hA : ‖C - A‖ ^ 2 = b2 := by rw [← hq, ← real_inner_self_eq_norm_sq]
    have hB : inner ℝ (B - A) (B - A) = g := by rw [← hp]
    have hC : inner ℝ (B - A) (C - A) = hh := by rw [← hp, ← hq]
    rw [hA, hB, hC, ← hga] at h2
    exact h2
  have hH : 2 * Wq = (s + 1 / 2) * b2 := by
    have h1 : (2 * Wq) * ga = ((s + 1 / 2) * b2) * ga := by
      have e2 : ((s + 1 / 2) * b2) * ga = s * b2 * ga + (1 / 2) * b2 * ga := by ring
      rw [e2, hang, hga]
      rw [show (2 * Wq) * ga = 2 * (Wq * ga) by ring, hcirc]
      ring
    exact mul_right_cancel₀ hgane h1
  have h2mid : (2 : ℝ) • midpoint ℝ A C = A + C := by
    rw [midpoint_eq_smul_add, smul_smul,
      show (2 : ℝ) * ⅟(2 : ℝ) = 1 by norm_num, one_smul]
  have hvec : (2 : ℝ) • (N - U) = q - (2 : ℝ) • W := by
    rw [hN, hq, hW, smul_sub, h2mid]
    module
  have hb2q : ‖q‖ ^ 2 = b2 := by
    rw [← real_inner_self_eq_norm_sq]
  have hW2 : inner ℝ q ((2 : ℝ) • W) = 2 * Wq := by
    rw [show (2 : ℝ) • W = W + W by rw [two_smul], inner_add_right, ← hWq]
    ring
  have hinner2 : 2 * inner ℝ q (N - U) = b2 - 2 * Wq := by
    have h1 : 2 * inner ℝ q (N - U) = inner ℝ q (q - (2 : ℝ) • W) := by
      rw [← inner_smul_right, hvec]
    rw [h1, inner_sub_right, hW2, ← hb2]
  have hkey : 2 * inner ℝ q (N - U) + (s - 1 / 2) * ‖q‖ ^ 2 = 0 := by
    rw [hinner2, hb2q]
    linarith [hH]
  exact hkey
  /- @proof-region region.target-node.session.fe991945c1989544 end -/
