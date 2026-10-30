import ProverJobs.real_main_theorem_e7f39350f194.Vocabulary
import ProverJobs.real_main_theorem_e7f39350f194.Base
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_2572412618_fc84ca75_76d868b1
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_3431605529_2a745110_37ebd9aa
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_393965618_6807243a_6d058c5d
open EuclideanGeometry

open EuclideanGeometry

set_option autoImplicit false in
theorem statopia_math_node_1807274513_fb8b9cdc : ∀ (A B C K L : Plane)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    (M N : Plane) (hM : M = midpoint ℝ A B) (hN : N = midpoint ℝ A C)
    (hK : InsideTriangle B M C K)
    (hL : InsideTriangle B N C L)
    (hKangle : InsideAngle L B A K)
    (s t u v : ℝ)
    (hs : 0 < s) (hs1 : s < 1) (ht : 0 < t) (ht1 : t < 1)
    (hu : 0 < u) (hu1 : u < 1) (hv : 0 < v) (hv1 : v < 1)
    (Y X : Plane) (hY : Y = A + s • (C - A)) (hX : X = A + t • (B - A))
    (hLtrace : L = C + v • (X - C))
    (hKtrace : K = B + u • (Y - B))
    (h2 : ∠ L B K = ∠ L N C),
    ∃ Q2 : Plane → ℝ,
      (∃ U : Plane, ∃ r2 : ℝ, ∀ P : Plane, Q2 P = ‖P - U‖ ^ 2 - r2) ∧
        Q2 B = 0 ∧ Q2 L = 0 ∧
        (∀ z : ℝ,
          Q2 (A + z • (C - A)) = dist A C ^ 2 * (z - (1 / 2 : ℝ)) * (z - s)) ∧
        Q2 A = dist A C ^ 2 * s / 2 ∧
        Q2 C = dist A C ^ 2 * (1 - s) / 2 := by
  /- @proof-region region.target-node.session.f05c245b675c1d7f begin -/
  intro A B C K L hABC M N hM hN hK hL hKangle s t u v hs hs1 ht ht1 hu hu1 hv hv1 Y X hY hX hLtrace hKtrace h2
  obtain ⟨U, r2, hBU, hLU, hNU, htan, hYU⟩ :=
    statopia_math_node_393965618_6807243a A B C K L hABC M N hM hN hK hL hKangle
      s t u v hs hs1 ht ht1 hu hu1 hv hv1 Y X hY hX hLtrace hKtrace h2
  have hline : ∀ z : ℝ,
      ‖(A + z • (C - A)) - U‖ ^ 2 - r2 = dist A C ^ 2 * (z - 1 / 2) * (z - s) := by
    obtain ⟨_, _, _, _, _, _, hc3, hc4⟩ := statopia_math_node_3431605529_2a745110
    have hne : C - A ≠ 0 := by
      intro h
      apply hABC
      have hCA : C = A := sub_eq_zero.mp h
      rw [hCA]
      have hset : ({A, B, A} : Set Plane) = {A, B} := by
        ext x
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rw [hset]
      exact collinear_pair ℝ A B
    have hN' : N = A + (1 / 2 : ℝ) • (C - A) := by
      rw [hN]
      first
        | (unfold midpoint; rw [AffineMap.lineMap_apply]; simp; module)
        | (unfold midpoint; rw [AffineMap.lineMap_apply]; dsimp; module)
        | (unfold midpoint; rw [AffineMap.lineMap_apply]; module)
        | (unfold midpoint; rw [AffineMap.lineMap_apply]; module)
    have hd : dist A C ^ 2 = ‖C - A‖ ^ 2 := by
      rw [dist_comm, dist_eq_norm]
    have hQ : ‖(A + (1 / 2 : ℝ) • (C - A)) - U‖ ^ 2 - r2 = 0 := by
      rw [← hN']
      exact hNU
    intro z
    by_cases hh : s = 1 / 2
    · have hin : inner ℝ (C - A) (A + (1 / 2 : ℝ) • (C - A) - U) = 0 := by
        rw [← hN']
        exact htan hh
      have hc := hc4 U r2 A (C - A) (1 / 2) hne hQ hin z
      rw [hc, hd, hh]
      ring
    · have hY' : ‖(A + s • (C - A)) - U‖ ^ 2 - r2 = 0 := by
        rw [← hY]
        exact hYU hh
      have hc := hc3 U r2 A (C - A) (1 / 2) s hne (fun hcon => hh hcon.symm) hQ hY' z
      rw [hc, hd]
  refine ⟨fun P => ‖P - U‖ ^ 2 - r2, ⟨U, r2, fun P => rfl⟩, hBU, hLU, hline, ?_, ?_⟩
  · have h := hline 0
    rw [zero_smul, add_zero] at h
    change ‖A - U‖ ^ 2 - r2 = dist A C ^ 2 * s / 2
    rw [h]
    ring
  · have h := hline 1
    rw [one_smul] at h
    have hC : A + (C - A) = C := by abel
    rw [hC] at h
    change ‖C - U‖ ^ 2 - r2 = dist A C ^ 2 * (1 - s) / 2
    rw [h]
    ring
  /- @proof-region region.target-node.session.f05c245b675c1d7f end -/
