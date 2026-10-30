import ProverJobs.real_main_theorem_e7f39350f194.Vocabulary
import ProverJobs.real_main_theorem_e7f39350f194.Base
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_3431605529_2a745110_37ebd9aa
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_3895931102_11f4646c_4d9a9d7e
open EuclideanGeometry

open EuclideanGeometry

set_option autoImplicit false in
theorem statopia_math_node_507356754_65c92604 : ∀ (A B C K M U : Plane) (r2 : ℝ)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    (hM : M = midpoint ℝ A B)
    (hK : InsideTriangle B M C K)
    (hangle : ∠ M C K = ∠ B M K)
    (hCU : ‖C - U‖ ^ 2 - r2 = 0)
    (hKU : ‖K - U‖ ^ 2 - r2 = 0)
    (hMU : ‖M - U‖ ^ 2 - r2 = 0),
    inner ℝ (B - A) (M - U) = 0 := by
  /- @proof-region region.target-node.session.80c6eb5a3ec378ea begin -/
  intro A B C K M U r2 hABC hM hK hangle hCU hKU hMU
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, hKdef⟩ := hK
  have hMA : M - A = (2:ℝ)⁻¹ • (B - A) := by
    rw [hM]
    simpa using (midpoint_vsub A B A)
  have hBA : B - A = (2:ℝ) • (B - M) := by
    have h1 : B - M = (B - A) - (M - A) := by abel
    rw [h1, hMA, smul_sub, smul_smul, show (2:ℝ) * 2⁻¹ = 1 by norm_num, one_smul]
    module
  set b : Plane := B - M with hbdef
  set c : Plane := C - M with hcdef
  set k : Plane := K - M with hkdef
  set u : Plane := U - M with hudef
  have hkabc : k = α • b + γ • c := by
    rw [hkdef, hbdef, hcdef, hKdef]
    have hs : (α + β + γ) • M = M := by rw [hsum, one_smul]
    calc α • B + β • M + γ • C - M
        = α • B + β • M + γ • C - (α + β + γ) • M := by rw [hs]
      _ = α • (B - M) + γ • (C - M) := by module
  have hQe : ∀ (U : Plane) (r2 : ℝ) (P0 v : Plane) (z : ℝ),
      ‖(P0 + z • v) - U‖ ^ 2 - r2
        = ‖v‖ ^ 2 * z ^ 2 + 2 * z * inner ℝ v (P0 - U) + (‖P0 - U‖ ^ 2 - r2) :=
    statopia_math_node_3431605529_2a745110.2.2.2.2.1
  have hcu : inner ℝ c u = ‖c‖ ^ 2 / 2 := by
    have h := hQe U r2 M c 1
    have hMC : M + (1:ℝ) • c = C := by rw [hcdef]; module
    rw [hMC, hCU, hMU] at h
    have hu : inner ℝ c (M - U) = -inner ℝ c u := by
      have e : M - U = -u := by rw [hudef]; abel
      rw [e, inner_neg_right]
    rw [hu] at h
    norm_num at h
    linarith [h]
  have hku : inner ℝ k u = ‖k‖ ^ 2 / 2 := by
    have h := hQe U r2 M k 1
    have hMK : M + (1:ℝ) • k = K := by rw [hkdef]; module
    rw [hMK, hKU, hMU] at h
    have hu : inner ℝ k (M - U) = -inner ℝ k u := by
      have e : M - U = -u := by rw [hudef]; abel
      rw [e, inner_neg_right]
    rw [hu] at h
    norm_num at h
    linarith [h]
  have hbu : inner ℝ b u = (‖k‖ ^ 2 - γ * ‖c‖ ^ 2) / (2 * α) := by
    have h : inner ℝ k u = α * inner ℝ b u + γ * inner ℝ c u := by
      rw [hkabc, inner_add_left, inner_smul_left, inner_smul_left]
      simp
    rw [hku, hcu] at h
    rw [eq_div_iff (mul_ne_zero two_ne_zero (ne_of_gt hα))]
    nlinarith [h]
  have hMC : M - C = -c := by rw [hcdef]; abel
  have hKC : K - C = k - c := by rw [hkdef, hcdef]; abel
  have hBM : B - M = b := by rw [hbdef]
  have hKM : K - M = k := by rw [hkdef]
  have hang : InnerProductGeometry.angle (-c) (k - c) = InnerProductGeometry.angle b k := by
    have h1 : (∠ M C K) = InnerProductGeometry.angle (M - C) (K - C) := rfl
    rw [hMC, hKC] at h1
    have h2 : (∠ B M K) = InnerProductGeometry.angle (B - M) (K - M) := rfl
    rw [hBM, hKM] at h2
    rw [h1, h2] at hangle
    exact hangle
  have htan : inner ℝ b u = 0 :=
    statopia_math_node_3895931102_11f4646c b c k u α γ hα hγ hkabc hcu hku hang
  have hBA' : B - A = (2 : ℝ) • b := by rw [hBA, hbdef]
  have hMU' : M - U = -u := by rw [hudef]; abel
  rw [hBA', hMU']
  have hs : inner ℝ ((2 : ℝ) • b) (-u) = 2 * inner ℝ b (-u) := by
    rw [inner_smul_left]
    simp
  rw [hs, inner_neg_right, htan]
  ring
  /- @proof-region region.target-node.session.80c6eb5a3ec378ea end -/
