import ProverJobs.real_main_theorem_e7f39350f194.Vocabulary
import ProverJobs.real_main_theorem_e7f39350f194.Base
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_2626076788_21f7138a_5b53c3f7
open EuclideanGeometry

open EuclideanGeometry

set_option autoImplicit false in
theorem statopia_math_node_2618456207_6af1ee36 : ∀ (A B C K L : Plane)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    (M N : Plane) (hM : M = midpoint ℝ A B) (hN : N = midpoint ℝ A C)
    (hK : InsideTriangle B M C K) (hL : InsideTriangle B N C L)
    (s t u v : ℝ)
    (hs : 0 < s) (hs1 : s < 1) (ht : 0 < t) (ht1 : t < 1)
    (hu : 0 < u) (hu1 : u < 1) (hv : 0 < v) (hv1 : v < 1)
    (X Y : Plane)
    (hY : Y = A + s • (C - A)) (hX : X = A + t • (B - A))
    (hKtrace : K = B + u • (Y - B)) (hLtrace : L = C + v • (X - C))
    (h3 : ∠ L C K = ∠ B M K)
    (hbranch : t < 1 / 2 ∨ 0 < (1 - u) - t * (1 - u * s))
    (htne : t ≠ 1 / 2),
    (¬ Collinear ℝ ({X, K, C} : Set Plane)) ∧
      ((0 < ((K - X) 0 * (C - X) 1 - (K - X) 1 * (C - X) 0) *
              ((K - X) 0 * (M - X) 1 - (K - X) 1 * (M - X) 0) ∧
          ∠ X C K = ∠ X M K) ∨
        (((K - X) 0 * (C - X) 1 - (K - X) 1 * (C - X) 0) *
            ((K - X) 0 * (M - X) 1 - (K - X) 1 * (M - X) 0) < 0 ∧
          ∠ X C K + ∠ X M K = (Real.pi : Real.Angle))) := by
  /- @proof-region region.target-node.session.e60e81390544cb30 begin -/
  intro A B C K L hABC M N hM hN hK hL s t u v hs hs1 ht ht1 hu hu1 hv hv1 X Y hY hX hKtrace hLtrace h3 hbranch htne
  unfold Collinear at hABC
  set b : Plane := B - A with hb
  set c : Plane := C - A with hc
  have hB : B = A + b := by rw [hb]; abel
  have hC : C = A + c := by rw [hc]; abel
  have hX' : X = A + t • b := by rw [hX]
  have hY' : Y = A + s • c := by rw [hY]
  have hMA : M - A = (1 / 2 : ℝ) • (B - A) := by
    rw [hM]
    change midpoint ℝ A B -ᵥ A = (1 / 2 : ℝ) • (B -ᵥ A)
    rw [midpoint_vsub_left]
    norm_num
  have hM' : M = A + (1 / 2 : ℝ) • b := by rw [hb, ← hMA]; abel
  have hMX : M - X = (1 / 2 - t) • b := by rw [hM', hX']; module
  have hK' : K = A + (1 - u) • b + (u * s) • c := by
    rw [hKtrace, hY', hB]; module
  have hLC : L - C = v • (X - C) := by rw [hLtrace]; abel
  have hKX : K - X = (1 - u - t) • b + (u * s) • c := by rw [hK', hX']; module
  have hCX : C - X = c - t • b := by rw [hC, hX']; module
  have hdetC : (K - X) 0 * (C - X) 1 - (K - X) 1 * (C - X) 0
      = ((B - A) 0 * (C - A) 1 - (B - A) 1 * (C - A) 0) *
          ((1 - u) - t * (1 - u * s)) := by
    rw [hKX, hCX, hb, hc]
    simp only [WithLp.ofLp_add, WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.add_apply,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hdetM : (K - X) 0 * (M - X) 1 - (K - X) 1 * (M - X) 0
      = ((B - A) 0 * (C - A) 1 - (B - A) 1 * (C - A) 0) * ((u * s) * (t - 1 / 2)) := by
    rw [hKX, hMX, hb, hc]
    simp only [WithLp.ofLp_add, WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.add_apply,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, hKbary⟩ := hK
  have hΔnb : (B - A) 0 * (C - A) 1 - (B - A) 1 * (C - A) 0 ≠ 0 :=
    (statopia_math_node_2626076788_21f7138a A B C).1 hABC
  have key : ∀ x y : ℝ, x • b + y • c = 0 → x = 0 ∧ y = 0 := by
    intro x y hxy
    have h0 : x * (b 0) + y * (c 0) = 0 := by
      have h := congrArg (fun v : Plane => v 0) hxy
      simpa using h
    have h1 : x * (b 1) + y * (c 1) = 0 := by
      have h := congrArg (fun v : Plane => v 1) hxy
      simpa using h
    have hx : x * ((b 0) * (c 1) - (b 1) * (c 0)) = 0 := by
      linear_combination (c 1) * h0 - (c 0) * h1
    have hy : y * ((b 0) * (c 1) - (b 1) * (c 0)) = 0 := by
      linear_combination (b 0) * h1 - (b 1) * h0
    have hD : (b 0) * (c 1) - (b 1) * (c 0) ≠ 0 := by
      simpa only [hb, hc] using hΔnb
    exact ⟨(mul_eq_zero.mp hx).resolve_right hD, (mul_eq_zero.mp hy).resolve_right hD⟩
  have hKM : K = A + (α + β / 2) • b + γ • c := by
    have key2 : α • (A + b) + β • (A + (1 / 2 : ℝ) • b) + γ • (A + c)
        = A + (α + β / 2) • b + γ • c := by
      calc α • (A + b) + β • (A + (1 / 2 : ℝ) • b) + γ • (A + c)
          = (α + β + γ) • A + (α + β / 2) • b + γ • c := by module
        _ = A + (α + β / 2) • b + γ • c := by rw [hsum, one_smul]
    rw [hKbary, hB, hM', hC, key2]
  have hAB : (1 - u) • b + (u * s) • c = (α + β / 2) • b + γ • c := by
    have h : A + (1 - u) • b + (u * s) • c = A + (α + β / 2) • b + γ • c :=
      hK'.symm.trans hKM
    rw [add_assoc, add_assoc] at h
    exact add_left_cancel h
  have hvec : (1 - u - (α + β / 2)) • b + (u * s - γ) • c = 0 := by
    have hsq : (1 - u - (α + β / 2)) • b + (u * s - γ) • c
        = ((1 - u) • b + (u * s) • c) - ((α + β / 2) • b + γ • c) := by module
    rw [hsq, hAB, sub_self]
  have hcoef1 : 1 - u = α + β / 2 := by
    have h := (key (1 - u - (α + β / 2)) (u * s - γ) hvec).1
    linarith
  have hcoef2 : u * s = γ := by
    have h := (key (1 - u - (α + β / 2)) (u * s - γ) hvec).2
    linarith
  have hγ' : γ = 1 - α - β := by linarith
  have hΔc : (1 - u) - t * (1 - u * s) = α * (1 - t) + β * (1 / 2 - t) := by
    rw [hcoef1, hcoef2, hγ']
    ring
  have hΔcpos : 0 < (1 - u) - t * (1 - u * s) := by
    rcases lt_or_gt_of_ne htne with hlt | hgt
    · rw [hΔc]
      exact add_pos (mul_pos hα (by linarith)) (mul_pos hβ (by linarith))
    · rcases hbranch with hb1 | hb2
      · linarith
      · exact hb2
  have hΔCne : (K - X) 0 * (C - X) 1 - (K - X) 1 * (C - X) 0 ≠ 0 := by
    rw [hdetC]
    exact mul_ne_zero hΔnb (ne_of_gt hΔcpos)
  have hnc : ¬ Collinear ℝ ({X, K, C} : Set Plane) :=
    (statopia_math_node_2626076788_21f7138a X K C).2 hΔCne
  have hposm : 0 < (u * s) * (t - 1 / 2) ↔ 1 / 2 < t := by
    rw [hcoef2]
    constructor
    · intro h
      have h' : 0 < γ⁻¹ * (γ * (t - 1 / 2)) := mul_pos (inv_pos.mpr hγ) h
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hγ), one_mul] at h'
      exact sub_pos.mp h'
    · intro h; exact mul_pos hγ (sub_pos.mpr h)
  have hprod : ((K - X) 0 * (C - X) 1 - (K - X) 1 * (C - X) 0)
      * ((K - X) 0 * (M - X) 1 - (K - X) 1 * (M - X) 0)
      = ((B - A) 0 * (C - A) 1 - (B - A) 1 * (C - A) 0) ^ 2
        * (((1 - u) - t * (1 - u * s)) * ((u * s) * (t - 1 / 2))) := by
    rw [hdetC, hdetM]
    ring
  have hdivcancel : ∀ (a b d c : ℝ), c ≠ 0 → (c * a) / (c * (b * d)) = a / (b * d) := by
    intro a b d c hc
    by_cases hbd : b * d = 0
    · simp [hbd]
    · field_simp
  have hang_pos : ∀ (c : ℝ) (x y : Plane), 0 < c →
      InnerProductGeometry.angle (c • x) y = InnerProductGeometry.angle x y := by
    intro c x y hc
    unfold InnerProductGeometry.angle
    rw [real_inner_smul_left, norm_smul, Real.norm_of_nonneg hc.le]
    congr 1
    rw [mul_assoc]
    exact hdivcancel (inner ℝ x y) ‖x‖ ‖y‖ c (ne_of_gt hc)
  have hang_neg : ∀ (c : ℝ) (x y : Plane), c < 0 →
      InnerProductGeometry.angle (c • x) y = Real.pi - InnerProductGeometry.angle x y := by
    intro c x y hc
    unfold InnerProductGeometry.angle
    rw [real_inner_smul_left, norm_smul, ← norm_neg c,
      Real.norm_of_nonneg (neg_nonneg.mpr hc.le)]
    have harg : (c * inner ℝ x y) / ((-c) * ‖x‖ * ‖y‖)
        = -(inner ℝ x y / (‖x‖ * ‖y‖)) := by
      rw [show (-c) * ‖x‖ * ‖y‖ = -(c * (‖x‖ * ‖y‖)) by ring, div_neg,
        hdivcancel (inner ℝ x y) ‖x‖ ‖y‖ c (ne_of_lt hc)]
    rw [harg, Real.arccos_neg]
  have hangXC : ∠ X C K = ∠ L C K := by
    unfold EuclideanGeometry.angle
    change InnerProductGeometry.angle (X - C) (K - C)
      = InnerProductGeometry.angle (L - C) (K - C)
    rw [hLC, hang_pos v (X - C) (K - C) hv]
  have hhalf : ∀ u : Plane, u - (1 / 2 : ℝ) • u = (1 / 2 : ℝ) • u := by
    intro u
    have hsum2 : u = (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • u := by
      have hc : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
      calc u = (1 : ℝ) • u := (one_smul ℝ u).symm
        _ = ((1 / 2 : ℝ) + 1 / 2) • u := congrArg (fun r : ℝ => r • u) hc.symm
        _ = (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • u := add_smul _ _ _
    nth_rewrite 1 [hsum2]
    abel
  have hBM : B - M = (1 / 2 : ℝ) • b := by
    have h1 : B - M = b - (1 / 2 : ℝ) • b := by rw [hB, hM']; abel
    rw [h1]
    exact hhalf b
  have hXM : X - M = (t - 1 / 2) • b := by
    have h1 : X - M = t • b - (1 / 2 : ℝ) • b := by rw [hX', hM']; abel
    have h3 : t • b = (t - 1 / 2) • b + (1 / 2 : ℝ) • b := by
      have hc : t - 1 / 2 + 1 / 2 = t := by ring
      calc t • b = (t - 1 / 2 + 1 / 2) • b := (congrArg (fun r : ℝ => r • b) hc).symm
        _ = (t - 1 / 2) • b + (1 / 2 : ℝ) • b := add_smul _ _ _
    rw [h1]
    nth_rewrite 1 [h3]
    abel
  have hangM_pos : 1 / 2 < t → ∠ B M K = ∠ X M K := by
    intro hgt
    have h1 : ∠ B M K = InnerProductGeometry.angle b (K - M) := by
      unfold EuclideanGeometry.angle
      change InnerProductGeometry.angle (B - M) (K - M)
        = InnerProductGeometry.angle b (K - M)
      rw [hBM]
      exact hang_pos (1 / 2) b (K - M) (by norm_num)
    have h2 : ∠ X M K = InnerProductGeometry.angle b (K - M) := by
      unfold EuclideanGeometry.angle
      change InnerProductGeometry.angle (X - M) (K - M)
        = InnerProductGeometry.angle b (K - M)
      rw [hXM]
      exact hang_pos (t - 1 / 2) b (K - M) (sub_pos.mpr hgt)
    rw [h1, h2]
  have hangM_neg : t < 1 / 2 → ∠ X M K = Real.pi - ∠ B M K := by
    intro hlt
    have h1 : ∠ X M K = Real.pi - InnerProductGeometry.angle b (K - M) := by
      unfold EuclideanGeometry.angle
      change InnerProductGeometry.angle (X - M) (K - M)
        = Real.pi - InnerProductGeometry.angle b (K - M)
      rw [hXM]
      exact hang_neg (t - 1 / 2) b (K - M) (sub_neg.mpr hlt)
    have h2 : ∠ B M K = InnerProductGeometry.angle b (K - M) := by
      unfold EuclideanGeometry.angle
      change InnerProductGeometry.angle (B - M) (K - M)
        = InnerProductGeometry.angle b (K - M)
      rw [hBM]
      exact hang_pos (1 / 2) b (K - M) (by norm_num)
    rw [h1, h2]
  refine ⟨hnc, ?_⟩
  rcases lt_or_gt_of_ne htne with hlt | hgt
  · right
    have hm : (u * s) * (t - 1 / 2) < 0 := by
      rw [hcoef2]
      exact mul_neg_of_pos_of_neg hγ (by linarith)
    refine ⟨?_, ?_⟩
    · rw [hprod]
      exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hΔnb)
        (mul_neg_of_pos_of_neg hΔcpos hm)
    · have h1 : ∠ X C K = ∠ B M K := hangXC.trans h3
      have h2 : ∠ X M K = Real.pi - ∠ B M K := hangM_neg hlt
      have hangsum : ∠ X C K + ∠ X M K = Real.pi := by rw [h1, h2]; ring
      rw [← Real.Angle.coe_add, hangsum]
  · left
    have hm : 0 < (u * s) * (t - 1 / 2) := hposm.2 hgt
    refine ⟨?_, ?_⟩
    · rw [hprod]
      exact mul_pos (sq_pos_of_ne_zero hΔnb) (mul_pos hΔcpos hm)
    · exact (hangXC.trans h3).trans (hangM_pos hgt)
  /- @proof-region region.target-node.session.e60e81390544cb30 end -/
