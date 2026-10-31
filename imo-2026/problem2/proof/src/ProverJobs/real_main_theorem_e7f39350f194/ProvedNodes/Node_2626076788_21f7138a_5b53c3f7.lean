import ProverJobs.real_main_theorem_e7f39350f194.Vocabulary
import ProverJobs.real_main_theorem_e7f39350f194.Base
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_624265820_ebe43d05_fd04936e
open EuclideanGeometry

open EuclideanGeometry

set_option autoImplicit false in
theorem statopia_math_node_2626076788_21f7138a : ∀ (P Q R : Plane),
    ¬ Collinear ℝ ({P, Q, R} : Set Plane) ↔
      (Q - P).ofLp 0 * (R - P).ofLp 1 - (Q - P).ofLp 1 * (R - P).ofLp 0 ≠ 0 := by
  /- @proof-region region.target-node.session.6ad2a143162771e7 begin -/
  intro P Q R
  have hA := statopia_math_node_624265820_ebe43d05 P Q R
  have hB : LinearIndependent ℝ ![Q - P, R - P] ↔
      (Q - P).ofLp 0 * (R - P).ofLp 1 - (Q - P).ofLp 1 * (R - P).ofLp 0 ≠ 0 := by
    have key : ∀ u v : Plane,
        (LinearIndependent ℝ ![u, v] ↔
          ∀ g₀ g₁ : ℝ, g₀ • u + g₁ • v = 0 → g₀ = 0 ∧ g₁ = 0) := by
      intro u v
      rw [Fintype.linearIndependent_iff]
      constructor
      · intro h g₀ g₁ hg
        have hg' : (∑ i : Fin 2, (![g₀, g₁] : Fin 2 → ℝ) i • ![u, v] i) = 0 := by
          rw [Fin.sum_univ_two]
          simpa using hg
        have hz := h ![g₀, g₁] hg'
        exact ⟨by simpa using hz 0, by simpa using hz 1⟩
      · intro h g hg
        have hg' : g 0 • u + g 1 • v = 0 := by
          rw [Fin.sum_univ_two] at hg
          simpa using hg
        have hz := h (g 0) (g 1) hg'
        intro i
        fin_cases i
        · simpa using hz.1
        · simpa using hz.2
    rw [key (Q - P) (R - P)]
    constructor
    · intro h hD
      have hD' : (Q.ofLp 0 - P.ofLp 0) * (R.ofLp 1 - P.ofLp 1)
            - (Q.ofLp 1 - P.ofLp 1) * (R.ofLp 0 - P.ofLp 0) = 0 := by
        simpa using hD
      have coeq : ∀ w : Plane, w = 0 ↔ w.ofLp 0 = 0 ∧ w.ofLp 1 = 0 := by
        intro w
        constructor
        · intro hw
          rw [hw]
          exact ⟨by simp, by simp⟩
        · intro hw
          apply WithLp.ofLp_injective
          funext i
          fin_cases i
          · simpa using hw.1
          · simpa using hw.2
      have hw1 : (R - P).ofLp 1 • (Q - P) + (-((Q - P).ofLp 1)) • (R - P) = 0 := by
        rw [coeq]
        constructor
        · simp
          nlinarith [hD']
        · simp
          ring
      have h1 := h ((R - P).ofLp 1) (-((Q - P).ofLp 1)) hw1
      have hw2 : (-((R - P).ofLp 0)) • (Q - P) + ((Q - P).ofLp 0) • (R - P) = 0 := by
        rw [coeq]
        constructor
        · simp
          ring
        · simp
          nlinarith [hD']
      have h2 := h (-((R - P).ofLp 0)) ((Q - P).ofLp 0) hw2
      have hu : (Q - P) = 0 := by
        rw [coeq]
        exact ⟨h2.2, neg_eq_zero.mp h1.2⟩
      have h3 := h 1 0 (by rw [one_smul, zero_smul, add_zero]; exact hu)
      exact one_ne_zero h3.1
    · intro hD g₀ g₁ hg
      have h0 : g₀ * (Q - P).ofLp 0 + g₁ * (R - P).ofLp 0 = 0 := by
        have hh := congrArg (fun w : Plane => w.ofLp 0) hg
        simpa using hh
      have h1 : g₀ * (Q - P).ofLp 1 + g₁ * (R - P).ofLp 1 = 0 := by
        have hh := congrArg (fun w : Plane => w.ofLp 1) hg
        simpa using hh
      have hg0 : g₀ * ((Q - P).ofLp 0 * (R - P).ofLp 1 - (Q - P).ofLp 1 * (R - P).ofLp 0) = 0 := by
        have hid : (R - P).ofLp 1 * (g₀ * (Q - P).ofLp 0 + g₁ * (R - P).ofLp 0)
            - (R - P).ofLp 0 * (g₀ * (Q - P).ofLp 1 + g₁ * (R - P).ofLp 1)
            = g₀ * ((Q - P).ofLp 0 * (R - P).ofLp 1 - (Q - P).ofLp 1 * (R - P).ofLp 0) := by
          ring
        rw [← hid, h0, h1]
        ring
      have hg1 : g₁ * ((Q - P).ofLp 0 * (R - P).ofLp 1 - (Q - P).ofLp 1 * (R - P).ofLp 0) = 0 := by
        have hid : (Q - P).ofLp 0 * (g₀ * (Q - P).ofLp 1 + g₁ * (R - P).ofLp 1)
            - (Q - P).ofLp 1 * (g₀ * (Q - P).ofLp 0 + g₁ * (R - P).ofLp 0)
            = g₁ * ((Q - P).ofLp 0 * (R - P).ofLp 1 - (Q - P).ofLp 1 * (R - P).ofLp 0) := by
          ring
        rw [← hid, h0, h1]
        ring
      constructor
      · by_contra hg0'
        exact hD ((mul_eq_zero.mp hg0).resolve_left hg0')
      · by_contra hg1'
        exact hD ((mul_eq_zero.mp hg1).resolve_left hg1')
  rw [hA]
  exact hB
  /- @proof-region region.target-node.session.6ad2a143162771e7 end -/
