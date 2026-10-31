import ProverJobs.real_main_theorem_e7f39350f194.Vocabulary
import ProverJobs.real_main_theorem_e7f39350f194.Base
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_1807274513_fb8b9cdc_098b0ba3
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_2237241960_78eabb87_2e43ad8f
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_2737272013_69da5b5b_2ef91ffb
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_3431605529_2a745110_37ebd9aa
open EuclideanGeometry

open EuclideanGeometry

set_option autoImplicit false in
theorem statopia_math_node_302587009_faa16c35 : ∀ (A B C K L : Plane)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    (M N : Plane) (hM : M = midpoint ℝ A B) (hN : N = midpoint ℝ A C)
    (hK : InsideTriangle B M C K) (hL : InsideTriangle B N C L)
    (hKangle : InsideAngle L B A K) (hLangle : InsideAngle A C K L)
    (h2 : ∠ L B K = ∠ L N C) (h3 : ∠ L C K = ∠ B M K)
    (s t u v : ℝ)
    (hs : 0 < s) (hs1 : s < 1) (ht : 0 < t) (ht1 : t < 1)
    (hu : 0 < u) (hu1 : u < 1) (hv : 0 < v) (hv1 : v < 1)
    (X Y : Plane)
    (hY : Y = A + s • (C - A)) (hX : X = A + t • (B - A))
    (hKu : K = B + u • (Y - B)) (hLv : L = C + v • (X - C))
    (hE : dist A B ^ 2 * t = dist A C ^ 2 * s)
    (W : Plane)
    (hWa : inner ℝ (B - A) W = ‖B - A‖ ^ 2 * (1 + t) / 4)
    (hWb : inner ℝ (C - A) W = ‖C - A‖ ^ 2 * (1 + s) / 4),
    ‖K - (A + W)‖ ^ 2 - ‖W‖ ^ 2 = 0 ∧ ‖L - (A + W)‖ ^ 2 - ‖W‖ ^ 2 = 0 := by
  /- @proof-region region.target-node.session.0a4d06085d7982fc begin -/
  intro A B C K L hABC M N hM hN hK hL hKangle hLangle h2 h3 s t u v
    hs hs1 ht ht1 hu hu1 hv hv1 X Y hY hX hKu hLv hE W hWa hWb
  have hbranch : t < 1 / 2 ∨ 0 < (1 - u) - t * (1 - u * s) := by
    obtain ⟨a, b, ha, _hb, hLac⟩ := hLangle
    have hli : LinearIndependent ℝ ![B - A, (C - A : Plane)] :=
      statopia_math_node_2737272013_69da5b5b A B C hABC
    have hsgn : ∀ x y : ℝ,
        x • (B - A) + y • (A - C) = 0 → x • (B - A) + (-y) • (C - A) = 0 := by
      intro x y hxy
      have h1 : (-y) • (C - A) = y • (A - C) := by
        rw [neg_smul, ← neg_sub C A, smul_neg]
      rw [h1]
      exact hxy
    have hcoef : ∀ x y : ℝ, x • (B - A) + y • (A - C) = 0 → x = 0 ∧ y = 0 := by
      intro x y hxy
      have h0 : (∑ i : Fin 2,
          (![x, -y] : Fin 2 → ℝ) i • (![B - A, (C - A : Plane)] : Fin 2 → Plane) i) = 0 := by
        simpa using hsgn x y hxy
      have hx : (![x, -y] : Fin 2 → ℝ) 0 = 0 :=
        (Fintype.linearIndependent_iff.mp hli) ![x, -y] h0 0
      have hy : (![x, -y] : Fin 2 → ℝ) 1 = 0 :=
        (Fintype.linearIndependent_iff.mp hli) ![x, -y] h0 1
      have hy0 : (-y : ℝ) = 0 := by simpa using hy
      exact ⟨by simpa using hx, by linarith⟩
    have hcomp : ∀ x y x' y' : ℝ,
        x • (B - A) + y • (A - C) = x' • (B - A) + y' • (A - C) → x = x' ∧ y = y' := by
      intro x y x' y' hxy
      have h0 : (x - x') • (B - A) + (y - y') • (A - C) = 0 := by
        rw [sub_smul, sub_smul]
        rw [show x • (B - A) - x' • (B - A) + (y • (A - C) - y' • (A - C))
              = (x • (B - A) + y • (A - C)) - (x' • (B - A) + y' • (A - C)) from by abel,
          hxy, sub_self]
      obtain ⟨h1, h2⟩ := hcoef (x - x') (y - y') h0
      exact ⟨by linarith, by linarith⟩
    have hKC : K - C = (1 - u) • (B - A) + (1 - u * s) • (A - C) := by
      rw [hKu, hY]
      simp only [smul_sub, smul_add, sub_smul, add_smul, smul_smul, one_smul]
      abel
    have hLC : L - C = (v * t) • (B - A) + v • (A - C) := by
      rw [hLv, hX]
      simp only [smul_sub, smul_add, sub_smul, add_smul, smul_smul, one_smul]
      abel
    have h1 : (v * t) • (B - A) + v • (A - C)
        = (b - b * u) • (B - A) + (a + b - b * (u * s)) • (A - C) := by
      rw [← hLC, hLac, hKC]
      simp only [smul_sub, smul_add, sub_smul, add_smul, smul_smul, one_smul]
      abel
    obtain ⟨hc1, hc2⟩ := hcomp (v * t) v (b - b * u) (a + b - b * (u * s)) h1
    have hu1' : 0 < 1 - u := by linarith
    have hrel : a * (1 - u) = v * ((1 - u) - t * (1 - u * s)) := by
      have hb' : b * (1 - u) = v * t := by linarith
      have ha' : a = v - b * (1 - u * s) := by linarith
      have key : b * (1 - u * s) * (1 - u) = v * t * (1 - u * s) := by
        have h : b * (1 - u * s) * (1 - u) = b * (1 - u) * (1 - u * s) := by ring
        rw [h, hb']
      calc a * (1 - u) = (v - b * (1 - u * s)) * (1 - u) := by rw [ha']
        _ = v * (1 - u) - b * (1 - u * s) * (1 - u) := by ring
        _ = v * (1 - u) - v * t * (1 - u * s) := by rw [key]
        _ = v * ((1 - u) - t * (1 - u * s)) := by ring
    have hmain : (1 - u) - t * (1 - u * s) = a * (1 - u) / v :=
      (eq_div_iff (ne_of_gt hv)).mpr (by rw [mul_comm]; exact hrel.symm)
    exact Or.inr (by rw [hmain]; exact div_pos (mul_pos ha hu1') hv)
  obtain ⟨U3, r3, hQ3C, hQ3K, hQ3line⟩ :=
    statopia_math_node_2237241960_78eabb87 A B C K L M N X Y s t u v hABC hM hN hK hL
      hs hs1 ht ht1 hu hu1 hv hv1 hY hX hKu hLv h3 hbranch
  obtain ⟨Q2, hQ2pow, hQ2B, hQ2L, hQ2line, hQ2A, hQ2C⟩ :=
    statopia_math_node_1807274513_fb8b9cdc A B C K L hABC M N hM hN hK hL hKangle
      s t u v hs hs1 ht ht1 hu hu1 hv hv1 Y X hY hX hLv hKu h2
  obtain ⟨U2, r2, hQ2pow'⟩ := hQ2pow
  have hcalc := statopia_math_node_3431605529_2a745110
  have hQ3A : ‖A - U3‖ ^ 2 - r3 = dist A B ^ 2 * t / 2 := by
    have h := hQ3line 0
    rw [zero_smul, add_zero] at h
    rw [h]; ring
  have hQ3B : ‖B - U3‖ ^ 2 - r3 = dist A B ^ 2 * (1 - t) / 2 := by
    have h := hQ3line 1
    have hB : A + (1 : ℝ) • (B - A) = B := by rw [one_smul]; abel
    rw [hB] at h
    rw [h]; ring
  have hdAB : dist A B ^ 2 = ‖B - A‖ ^ 2 := by rw [dist_comm A B, dist_eq_norm]
  have hdAC : dist A C ^ 2 = ‖C - A‖ ^ 2 := by rw [dist_comm A C, dist_eq_norm]
  have hQA0 : ‖A - (A + W)‖ ^ 2 - ‖W‖ ^ 2 = 0 := by
    have h : A - (A + W) = -W := by abel
    rw [h, norm_neg]; ring
  have hQC : ‖C - (A + W)‖ ^ 2 - ‖W‖ ^ 2 = dist A C ^ 2 * (1 - s) / 2 := by
    have h : C - (A + W) = (C - A) - W := by abel
    rw [h, norm_sub_sq_real, hWb, hdAC]; ring
  have hQB : ‖B - (A + W)‖ ^ 2 - ‖W‖ ^ 2 = dist A B ^ 2 * (1 - t) / 2 := by
    have h : B - (A + W) = (B - A) - W := by abel
    rw [h, norm_sub_sq_real, hWa, hdAB]; ring
  have hRA : (‖A - U3‖ ^ 2 - r3) - (‖A - (A + W)‖ ^ 2 - ‖W‖ ^ 2) = dist A B ^ 2 * t / 2 := by
    rw [hQ3A, hQA0]; ring
  have hRC : (‖C - U3‖ ^ 2 - r3) - (‖C - (A + W)‖ ^ 2 - ‖W‖ ^ 2) = -(dist A C ^ 2 * (1 - s) / 2) := by
    rw [hQ3C, hQC]; ring
  have hRB : (‖B - U3‖ ^ 2 - r3) - (‖B - (A + W)‖ ^ 2 - ‖W‖ ^ 2) = 0 := by
    rw [hQ3B, hQB]; ring
  have hYeq : Y = (1 - s) • A + s • C := by
    rw [hY]; rw [smul_sub, sub_smul, one_smul]; abel
  have hRY : (‖Y - U3‖ ^ 2 - r3) - (‖Y - (A + W)‖ ^ 2 - ‖W‖ ^ 2) = 0 := by
    rw [hYeq, hcalc.2.1 U3 r3 (A + W) (‖W‖ ^ 2) A C s, hRA, hRC, hE]; ring
  have hKeq : K = (1 - u) • B + u • Y := by
    rw [hKu]; rw [smul_sub, sub_smul, one_smul]; abel
  have hKU : ‖K - U3‖ ^ 2 - r3 = 0 := hQ3K
  have hK0 : ‖K - (A + W)‖ ^ 2 - ‖W‖ ^ 2 = 0 := by
    have hRK : (‖K - U3‖ ^ 2 - r3) - (‖K - (A + W)‖ ^ 2 - ‖W‖ ^ 2) = 0 := by
      rw [hKeq, hcalc.2.1 U3 r3 (A + W) (‖W‖ ^ 2) B Y u, hRB, hRY]; ring
    rw [hKU, zero_sub] at hRK
    exact neg_eq_zero.mp hRK
  have hR2A : (‖A - U2‖ ^ 2 - r2) - (‖A - (A + W)‖ ^ 2 - ‖W‖ ^ 2) = dist A C ^ 2 * s / 2 := by
    have ha1 : ‖A - U2‖ ^ 2 - r2 = dist A C ^ 2 * s / 2 := by rw [← hQ2pow' A]; exact hQ2A
    rw [ha1, hQA0]; ring
  have hR2C : (‖C - U2‖ ^ 2 - r2) - (‖C - (A + W)‖ ^ 2 - ‖W‖ ^ 2) = 0 := by
    have hc1 : ‖C - U2‖ ^ 2 - r2 = dist A C ^ 2 * (1 - s) / 2 := by rw [← hQ2pow' C]; exact hQ2C
    rw [hc1, hQC]; ring
  have hR2B : (‖B - U2‖ ^ 2 - r2) - (‖B - (A + W)‖ ^ 2 - ‖W‖ ^ 2) = -(dist A B ^ 2 * (1 - t) / 2) := by
    have hb1 : ‖B - U2‖ ^ 2 - r2 = 0 := by rw [← hQ2pow' B]; exact hQ2B
    rw [hb1, hQB]; ring
  have hXeq : X = (1 - t) • A + t • B := by
    rw [hX]; rw [smul_sub, sub_smul, one_smul]; abel
  have hR2X : (‖X - U2‖ ^ 2 - r2) - (‖X - (A + W)‖ ^ 2 - ‖W‖ ^ 2) = 0 := by
    rw [hXeq, hcalc.2.1 U2 r2 (A + W) (‖W‖ ^ 2) A B t, hR2A, hR2B, ← hE]; ring
  have hLeq : L = (1 - v) • C + v • X := by
    rw [hLv]; rw [smul_sub, sub_smul, one_smul]; abel
  have hLU : ‖L - U2‖ ^ 2 - r2 = 0 := by rw [← hQ2pow' L]; exact hQ2L
  have hL0 : ‖L - (A + W)‖ ^ 2 - ‖W‖ ^ 2 = 0 := by
    have hRL : (‖L - U2‖ ^ 2 - r2) - (‖L - (A + W)‖ ^ 2 - ‖W‖ ^ 2) = 0 := by
      rw [hLeq, hcalc.2.1 U2 r2 (A + W) (‖W‖ ^ 2) C X v, hR2C, hR2X]; ring
    rw [hLU, zero_sub] at hRL
    exact neg_eq_zero.mp hRL
  exact ⟨hK0, hL0⟩
  /- @proof-region region.target-node.session.0a4d06085d7982fc end -/
