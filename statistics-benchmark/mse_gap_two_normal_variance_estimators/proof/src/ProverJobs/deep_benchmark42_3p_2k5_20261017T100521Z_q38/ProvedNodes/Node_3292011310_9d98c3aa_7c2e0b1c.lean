import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q38.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q38.Base

open MeasureTheory ProbabilityTheory
open scoped BigOperators

open MeasureTheory ProbabilityTheory
open scoped BigOperators

set_option autoImplicit false in
theorem statopia_math_node_3292011310_9d98c3aa : ∀ (n : ℕ) (v : ℝ) (A : Fin n → Fin n → ℝ)
    (hA : ∀ i j : Fin n, A i j = A j i),
    (∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n, ∑ s : Fin n,
      A p q * A r s * (v ^ 2 * ((if p = q then (1 : ℝ) else 0) * (if r = s then (1 : ℝ) else 0)
        + (if p = r then (1 : ℝ) else 0) * (if q = s then (1 : ℝ) else 0)
        + (if p = s then (1 : ℝ) else 0) * (if q = r then (1 : ℝ) else 0))))
    = v ^ 2 * ((∑ i : Fin n, A i i) ^ 2 + 2 * ∑ i : Fin n, ∑ j : Fin n, A i j ^ 2) := by
  /- @proof-region region.target-node.session.b6fa757e38e6105a begin -/
  intro n v A hA
  have delta_sum : ∀ (a : Fin n) (f : Fin n → ℝ),
      (∑ x : Fin n, f x * (if a = x then (1 : ℝ) else 0)) = f a := by
    intro a f
    have key : (∑ x : Fin n, f x * (if a = x then (1 : ℝ) else 0))
        = f a * (if a = a then (1 : ℝ) else 0) := by
      exact Finset.sum_eq_single a
        (fun b _ hb => by rw [if_neg (fun hab : a = b => hb hab.symm), mul_zero])
        (fun h => absurd (Finset.mem_univ a) h)
    rw [key]
    simp
  have hfact : ∀ (f g : Fin n → Fin n → ℝ),
      (∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n, ∑ s : Fin n, f p q * g r s)
        = (∑ p : Fin n, ∑ q : Fin n, f p q) * (∑ r : Fin n, ∑ s : Fin n, g r s) := by
    intro f g
    simp only [← Finset.mul_sum]
    simp only [← Finset.sum_mul]
  have hdiag : ∀ (B : Fin n → Fin n → ℝ),
      (∑ p : Fin n, ∑ q : Fin n, B p q * (if p = q then (1 : ℝ) else 0))
        = (∑ i : Fin n, B i i) := by
    intro B
    rw [show (∑ p : Fin n, ∑ q : Fin n, B p q * (if p = q then (1 : ℝ) else 0))
        = (∑ p : Fin n, B p p) from by
      apply Finset.sum_congr rfl
      intro p _
      exact delta_sum p (fun q => B p q)]
  have hrw1 : ∀ p q r s : Fin n,
      A p q * A r s * ((if p = q then (1 : ℝ) else 0) * (if r = s then (1 : ℝ) else 0))
        = (A p q * (if p = q then (1 : ℝ) else 0)) * (A r s * (if r = s then (1 : ℝ) else 0)) := by
    intro p q r s
    ring
  have S1 : (∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n, ∑ s : Fin n,
        A p q * A r s * ((if p = q then (1 : ℝ) else 0) * (if r = s then (1 : ℝ) else 0)))
      = (∑ i : Fin n, A i i) ^ 2 := by
    simp only [hrw1]
    rw [hfact (fun (p : Fin n) (q : Fin n) => A p q * (if p = q then (1 : ℝ) else 0))
      (fun (r : Fin n) (s : Fin n) => A r s * (if r = s then (1 : ℝ) else 0))]
    simp only [hdiag]
    ring
  have hrw2 : ∀ p q r s : Fin n,
      A p q * A r s * ((if p = r then (1 : ℝ) else 0) * (if q = s then (1 : ℝ) else 0))
        = (A p q * A r s * (if p = r then (1 : ℝ) else 0)) * (if q = s then (1 : ℝ) else 0) := by
    intro p q r s
    ring
  have S2 : (∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n, ∑ s : Fin n,
        A p q * A r s * ((if p = r then (1 : ℝ) else 0) * (if q = s then (1 : ℝ) else 0)))
      = (∑ i : Fin n, ∑ j : Fin n, A i j ^ 2) := by
    have e1 : (∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n, ∑ s : Fin n,
          A p q * A r s * ((if p = r then (1 : ℝ) else 0) * (if q = s then (1 : ℝ) else 0)))
        = (∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n,
          A p q * A r q * (if p = r then (1 : ℝ) else 0)) := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro r _
      simp only [hrw2]
      exact delta_sum q (fun s => A p q * A r s * (if p = r then (1 : ℝ) else 0))
    have e2 : (∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n,
          A p q * A r q * (if p = r then (1 : ℝ) else 0))
        = (∑ p : Fin n, ∑ q : Fin n, A p q * A p q) := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      exact delta_sum p (fun r => A p q * A r q)
    have e3 : (∑ p : Fin n, ∑ q : Fin n, A p q * A p q)
        = (∑ i : Fin n, ∑ j : Fin n, A i j ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [e1, e2, e3]
  have hrw3 : ∀ p q r s : Fin n,
      A p q * A r s * ((if p = s then (1 : ℝ) else 0) * (if q = r then (1 : ℝ) else 0))
        = (A p q * A r s * (if q = r then (1 : ℝ) else 0)) * (if p = s then (1 : ℝ) else 0) := by
    intro p q r s
    ring
  have S3 : (∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n, ∑ s : Fin n,
        A p q * A r s * ((if p = s then (1 : ℝ) else 0) * (if q = r then (1 : ℝ) else 0)))
      = (∑ i : Fin n, ∑ j : Fin n, A i j ^ 2) := by
    have f1 : (∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n, ∑ s : Fin n,
          A p q * A r s * ((if p = s then (1 : ℝ) else 0) * (if q = r then (1 : ℝ) else 0)))
        = (∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n,
          A p q * A r p * (if q = r then (1 : ℝ) else 0)) := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro r _
      simp only [hrw3]
      exact delta_sum p (fun s => A p q * A r s * (if q = r then (1 : ℝ) else 0))
    have f2 : (∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n,
          A p q * A r p * (if q = r then (1 : ℝ) else 0))
        = (∑ p : Fin n, ∑ q : Fin n, A p q * A q p) := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      exact delta_sum q (fun r => A p q * A r p)
    have f3 : (∑ p : Fin n, ∑ q : Fin n, A p q * A q p)
        = (∑ i : Fin n, ∑ j : Fin n, A i j ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hA j i]
      ring
    rw [f1, f2, f3]
  rw [show (∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n, ∑ s : Fin n,
        A p q * A r s * (v ^ 2 * ((if p = q then (1 : ℝ) else 0) * (if r = s then (1 : ℝ) else 0)
          + (if p = r then (1 : ℝ) else 0) * (if q = s then (1 : ℝ) else 0)
          + (if p = s then (1 : ℝ) else 0) * (if q = r then (1 : ℝ) else 0))))
      = v ^ 2 * ((∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n, ∑ s : Fin n,
            A p q * A r s * ((if p = q then (1 : ℝ) else 0) * (if r = s then (1 : ℝ) else 0)))
        + (∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n, ∑ s : Fin n,
            A p q * A r s * ((if p = r then (1 : ℝ) else 0) * (if q = s then (1 : ℝ) else 0)))
        + (∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n, ∑ s : Fin n,
            A p q * A r s * ((if p = s then (1 : ℝ) else 0) * (if q = r then (1 : ℝ) else 0)))) from by
    calc (∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n, ∑ s : Fin n,
        A p q * A r s * (v ^ 2 * ((if p = q then (1 : ℝ) else 0) * (if r = s then (1 : ℝ) else 0)
          + (if p = r then (1 : ℝ) else 0) * (if q = s then (1 : ℝ) else 0)
          + (if p = s then (1 : ℝ) else 0) * (if q = r then (1 : ℝ) else 0))))
        = (∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n, ∑ s : Fin n,
            v ^ 2 * (A p q * A r s * ((if p = q then (1 : ℝ) else 0) * (if r = s then (1 : ℝ) else 0))
              + A p q * A r s * ((if p = r then (1 : ℝ) else 0) * (if q = s then (1 : ℝ) else 0))
              + A p q * A r s * ((if p = s then (1 : ℝ) else 0) * (if q = r then (1 : ℝ) else 0)))) := by
          apply Finset.sum_congr rfl
          intro p _
          apply Finset.sum_congr rfl
          intro q _
          apply Finset.sum_congr rfl
          intro r _
          apply Finset.sum_congr rfl
          intro s _
          ring
      _ = v ^ 2 * (∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n, ∑ s : Fin n,
            (A p q * A r s * ((if p = q then (1 : ℝ) else 0) * (if r = s then (1 : ℝ) else 0))
              + A p q * A r s * ((if p = r then (1 : ℝ) else 0) * (if q = s then (1 : ℝ) else 0))
              + A p q * A r s * ((if p = s then (1 : ℝ) else 0) * (if q = r then (1 : ℝ) else 0)))) := by
          simp only [← Finset.mul_sum]
      _ = v ^ 2 * ((∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n, ∑ s : Fin n,
              A p q * A r s * ((if p = q then (1 : ℝ) else 0) * (if r = s then (1 : ℝ) else 0)))
            + (∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n, ∑ s : Fin n,
              A p q * A r s * ((if p = r then (1 : ℝ) else 0) * (if q = s then (1 : ℝ) else 0)))
            + (∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n, ∑ s : Fin n,
              A p q * A r s * ((if p = s then (1 : ℝ) else 0) * (if q = r then (1 : ℝ) else 0)))) := by
          simp only [Finset.sum_add_distrib]]
  rw [S1, S2, S3]
  ring
  /- @proof-region region.target-node.session.b6fa757e38e6105a end -/
