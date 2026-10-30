import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q40.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q40.Base

open Matrix

open Matrix

set_option autoImplicit false in
theorem statopia_math_node_3652586393_a25bccab : ∀ (d n : ℕ) (hn : 1 ≤ n)
    (x : Fin n → Fin d → ℝ)
    (hx : ∀ i, dotProduct (x i) (x i) = 1),
    ∀ p : Fin d → ℝ,
      (n : ℝ)⁻¹ * ∑ i : Fin n, dotProduct (x i - p) (x i - p) =
        1 + dotProduct p p -
          2 * dotProduct ((n : ℝ)⁻¹ • ∑ i : Fin n, x i) p := by
  /- @proof-region region.target-node.session.18b1642d4b24e921 begin -/
  intro d n hn x hx p
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hdot_eq : ∀ u v : Fin d → ℝ, dotProduct u v = ∑ j : Fin d, u j * v j := by
    intro u v
    simpa only [dotProduct] using
      (Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => mul_comm (v j) (u j)) :
        ∑ j : Fin d, v j * u j = ∑ j : Fin d, u j * v j)
  have hxx : ∀ i : Fin n, ∑ j : Fin d, x i j * x i j = 1 := by
    intro i
    rw [← hdot_eq (x i) (x i)]
    exact hx i
  have hterm : ∀ i : Fin n, ∑ j : Fin d, (x i j - p j) * (x i j - p j)
      = 1 - 2 * (∑ j : Fin d, x i j * p j) + ∑ j : Fin d, p j * p j := by
    intro i
    have h1 : ∑ j : Fin d, (x i j - p j) * (x i j - p j)
        = ∑ j : Fin d, (x i j * x i j - 2 * (x i j * p j) + p j * p j) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, hxx i, ← Finset.mul_sum]
  have hSS : ∑ i : Fin n, ∑ j : Fin d, x i j * p j
      = ∑ j : Fin d, (∑ i : Fin n, x i j) * p j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_mul]
  have hone : ∑ i : Fin n, (1 : ℝ) = (n : ℝ) := by
    simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
  have hQsum : ∑ i : Fin n, (∑ j : Fin d, p j * p j) = (n : ℝ) * ∑ j : Fin d, p j * p j := by
    simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
  have h2T : ∑ i : Fin n, 2 * (∑ j : Fin d, x i j * p j)
      = 2 * ∑ i : Fin n, ∑ j : Fin d, x i j * p j :=
    (Finset.mul_sum Finset.univ (fun i : Fin n => ∑ j : Fin d, x i j * p j) 2).symm
  have hsum : ∑ i : Fin n, ∑ j : Fin d, (x i j - p j) * (x i j - p j)
      = (n : ℝ) * (1 + ∑ j : Fin d, p j * p j)
        - 2 * ∑ j : Fin d, (∑ i : Fin n, x i j) * p j := by
    calc ∑ i : Fin n, ∑ j : Fin d, (x i j - p j) * (x i j - p j)
        = ∑ i : Fin n, (1 - 2 * (∑ j : Fin d, x i j * p j) + ∑ j : Fin d, p j * p j) :=
          Finset.sum_congr rfl (fun i _ => hterm i)
      _ = ((n : ℝ) - 2 * ∑ i : Fin n, ∑ j : Fin d, x i j * p j)
            + (n : ℝ) * ∑ j : Fin d, p j * p j := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hone, h2T, hQsum]
      _ = (n : ℝ) * (1 + ∑ j : Fin d, p j * p j)
            - 2 * ∑ j : Fin d, (∑ i : Fin n, x i j) * p j := by
          rw [hSS]
          ring
  have hmean : dotProduct ((n : ℝ)⁻¹ • ∑ i : Fin n, x i) p
      = (n : ℝ)⁻¹ * ∑ j : Fin d, (∑ i : Fin n, x i j) * p j := by
    have hstep : ∀ j : Fin d,
        ((n : ℝ)⁻¹ • ∑ i : Fin n, x i) j = (n : ℝ)⁻¹ * ∑ i : Fin n, x i j := by
      intro j
      simp [Finset.sum_apply, smul_eq_mul]
    calc dotProduct ((n : ℝ)⁻¹ • ∑ i : Fin n, x i) p
        = ∑ j : Fin d, ((n : ℝ)⁻¹ • ∑ i : Fin n, x i) j * p j := hdot_eq _ _
      _ = ∑ j : Fin d, ((n : ℝ)⁻¹ * ∑ i : Fin n, x i j) * p j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [hstep j]
      _ = ∑ j : Fin d, (n : ℝ)⁻¹ * ((∑ i : Fin n, x i j) * p j) := by
          apply Finset.sum_congr rfl
          intro j _
          ring
      _ = (n : ℝ)⁻¹ * ∑ j : Fin d, (∑ i : Fin n, x i j) * p j :=
          (Finset.mul_sum Finset.univ (fun j : Fin d => (∑ i : Fin n, x i j) * p j) ((n : ℝ)⁻¹)).symm
  have hbridge : ∑ i : Fin n, dotProduct (x i - p) (x i - p)
      = ∑ i : Fin n, ∑ j : Fin d, (x i j - p j) * (x i j - p j) := by
    apply Finset.sum_congr rfl
    intro i _
    exact hdot_eq (x i - p) (x i - p)
  rw [hbridge, hsum, hdot_eq p p, hmean]
  have h1 : (n : ℝ)⁻¹ * (n : ℝ) = 1 := inv_mul_cancel₀ hn0
  have hstep2 : (n : ℝ)⁻¹ * ((n : ℝ) * (1 + ∑ j : Fin d, p j * p j)
        - 2 * ∑ j : Fin d, (∑ i : Fin n, x i j) * p j)
      = ((n : ℝ)⁻¹ * (n : ℝ)) * (1 + ∑ j : Fin d, p j * p j)
        - 2 * ((n : ℝ)⁻¹ * ∑ j : Fin d, (∑ i : Fin n, x i j) * p j) := by ring
  rw [hstep2, h1]
  ring
  /- @proof-region region.target-node.session.18b1642d4b24e921 end -/
