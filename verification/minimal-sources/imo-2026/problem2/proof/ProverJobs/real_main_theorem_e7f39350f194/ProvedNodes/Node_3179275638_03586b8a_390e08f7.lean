import ProverJobs.real_main_theorem_e7f39350f194.Vocabulary
import ProverJobs.real_main_theorem_e7f39350f194.Base
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_1807274513_fb8b9cdc_098b0ba3
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_2237241960_78eabb87_2e43ad8f
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_2572412618_fc84ca75_76d868b1
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_3431605529_2a745110_37ebd9aa
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_3691240324_1176a2cb_8a7631d0
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_981975689_c1054012_46ac252e
open EuclideanGeometry

open EuclideanGeometry

set_option autoImplicit false in
theorem statopia_math_node_3179275638_03586b8a : ∀ (A B C K L : Plane)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    (M N : Plane) (hM : M = midpoint ℝ A B) (hN : N = midpoint ℝ A C)
    (hK : InsideTriangle B M C K)
    (hL : InsideTriangle B N C L)
    (s t u v : ℝ)
    (hs : 0 < s) (hs1 : s < 1) (ht : 0 < t) (ht1 : t < 1)
    (hu : 0 < u) (hu1 : u < 1) (hv : 0 < v) (hv1 : v < 1)
    (Y X : Plane)
    (hY : Y = A + s • (C - A)) (hX : X = A + t • (B - A))
    (hKtrace : K = B + u • (Y - B))
    (hLtrace : L = C + v • (X - C))
    (hE : dist A B ^ 2 * t = dist A C ^ 2 * s)
    (Q3 Q2 : Plane → ℝ)
    (hQ3pow : ∃ U : Plane, ∃ r2 : ℝ, ∀ P : Plane, Q3 P = ‖P - U‖ ^ 2 - r2)
    (hQ3C : Q3 C = 0) (hQ3K : Q3 K = 0)
    (hQ3A : Q3 A = dist A B ^ 2 * t / 2)
    (hQ3B : Q3 B = dist A B ^ 2 * (1 - t) / 2)
    (hQ2pow : ∃ U : Plane, ∃ r2 : ℝ, ∀ P : Plane, Q2 P = ‖P - U‖ ^ 2 - r2)
    (hQ2B : Q2 B = 0) (hQ2L : Q2 L = 0)
    (hQ2A : Q2 A = dist A C ^ 2 * s / 2)
    (hQ2C : Q2 C = dist A C ^ 2 * (1 - s) / 2),
    ∃ Q : Plane → ℝ,
      (∃ U : Plane, ∃ r2 : ℝ, ∀ P : Plane, Q P = ‖P - U‖ ^ 2 - r2) ∧
        Q A = 0 ∧ Q K = 0 ∧ Q L = 0 ∧
        Q B = dist A B ^ 2 * (1 - t) / 2 ∧
        Q C = dist A C ^ 2 * (1 - s) / 2 := by
  /- @proof-region region.target-node.session.e5ddeb961bd18cf2 begin -/
  intro A B C K L hABC M N hM hN hK hL s t u v hs hs1 ht ht1 hu hu1 hv hv1 Y X hY hX hKtrace
    hLtrace hE Q3 Q2 hQ3pow hQ3C hQ3K hQ3A hQ3B hQ2pow hQ2B hQ2L hQ2A hQ2C
  obtain ⟨U3, r3, h3all⟩ := hQ3pow
  obtain ⟨U2, r2q, h2all⟩ := hQ2pow
  have hpc_int := statopia_math_node_3431605529_2a745110.2.1
  have hpc_line := statopia_math_node_3431605529_2a745110.2.2.1
  obtain ⟨U, r, hUA, hUB, hUC⟩ := statopia_math_node_981975689_c1054012 A B C hABC
    (dist A B ^ 2 * (1 - t) / 2) (dist A C ^ 2 * (1 - s) / 2)
  refine ⟨fun P => ‖P - U‖ ^ 2 - r, ⟨U, r, fun P => rfl⟩, hUA, ?_, ?_, hUB, hUC⟩
  · show ‖K - U‖ ^ 2 - r = 0
    have hk3 : ‖K - U3‖ ^ 2 - r3 = 0 := by rw [← h3all K, hQ3K]
    have hBval : (‖B - U3‖ ^ 2 - r3) - (‖B - U‖ ^ 2 - r) = 0 := by
      rw [← h3all B, hQ3B, hUB]; ring
    by_cases hBY : B = Y
    · have hKB : K = B := by rw [hKtrace, ← hBY]; module
      rw [hKB] at hk3 ⊢
      linarith [hBval, hk3]
    · have hYeq : Y = (1 - s) • A + s • C := by rw [hY]; module
      have hYval : (‖Y - U3‖ ^ 2 - r3) - (‖Y - U‖ ^ 2 - r) = 0 := by
        rw [hYeq, hpc_int U3 r3 U r A C s]
        have hA : (‖A - U3‖ ^ 2 - r3) - (‖A - U‖ ^ 2 - r) = dist A B ^ 2 * t / 2 := by
          rw [← h3all A, hQ3A, hUA]; ring
        have hC : (‖C - U3‖ ^ 2 - r3) - (‖C - U‖ ^ 2 - r) = -(dist A C ^ 2 * (1 - s) / 2) := by
          rw [← h3all C, hQ3C, hUC]; ring
        rw [hA, hC, hE]; ring
      have hKval : (‖K - U3‖ ^ 2 - r3) - (‖K - U‖ ^ 2 - r) = 0 := by
        have h := hpc_line U3 r3 U r B Y hBY hBval hYval u
        have hKeq : (1 - u) • B + u • Y = K := by rw [hKtrace]; module
        rw [hKeq] at h
        exact h
      linarith [hKval, hk3]
  · show ‖L - U‖ ^ 2 - r = 0
    have hl2 : ‖L - U2‖ ^ 2 - r2q = 0 := by rw [← h2all L, hQ2L]
    have hCval : (‖C - U2‖ ^ 2 - r2q) - (‖C - U‖ ^ 2 - r) = 0 := by
      rw [← h2all C, hQ2C, hUC]; ring
    by_cases hCX : C = X
    · have hLC : L = C := by rw [hLtrace, ← hCX]; module
      rw [hLC] at hl2 ⊢
      linarith [hCval, hl2]
    · have hXeq : X = (1 - t) • A + t • B := by rw [hX]; module
      have hXval : (‖X - U2‖ ^ 2 - r2q) - (‖X - U‖ ^ 2 - r) = 0 := by
        rw [hXeq, hpc_int U2 r2q U r A B t]
        have hA : (‖A - U2‖ ^ 2 - r2q) - (‖A - U‖ ^ 2 - r) = dist A C ^ 2 * s / 2 := by
          rw [← h2all A, hQ2A, hUA]; ring
        have hB' : (‖B - U2‖ ^ 2 - r2q) - (‖B - U‖ ^ 2 - r) = -(dist A B ^ 2 * (1 - t) / 2) := by
          rw [← h2all B, hQ2B, hUB]; ring
        rw [hA, hB', ← hE]; ring
      have hLval : (‖L - U2‖ ^ 2 - r2q) - (‖L - U‖ ^ 2 - r) = 0 := by
        have h := hpc_line U2 r2q U r C X hCX hCval hXval v
        have hLeq : (1 - v) • C + v • X = L := by rw [hLtrace]; module
        rw [hLeq] at h
        exact h
      linarith [hLval, hl2]
  /- @proof-region region.target-node.session.e5ddeb961bd18cf2 end -/
