import ProverJobs.job_paper_a62240be95074e8caf07c24daf22159a.Vocabulary
import ProverJobs.job_paper_a62240be95074e8caf07c24daf22159a.Base

namespace PaperProofTasks.job_paper_a62240be95074e8caf07c24daf22159a

open _root_.PaperProofTasks.job_paper_a62240be95074e8caf07c24daf22159a.Statlib.Imported

namespace Statlib.Imported
open _root_.Statlib

set_option autoImplicit false in
theorem statopia_math_node_1508296774_c3a2de09 : ∀ (d : ℕ)
    (U : EuclideanSpace ℝ (Fin d) → ℝ)
    (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ : δ < 1) (L : ℕ) (hL : 1 ≤ L)
    (R : ℝ) (hR : 1 ≤ R)
    (hRgrad : ∀ x : EuclideanSpace ℝ (Fin d), R < ‖x‖ →
      (16 / 3 : ℝ) ≤ ε ^ 2 * (‖gradient U x‖ / ‖x‖))
    (η15 : ℝ)
    (hη15 : ∀ x0 : EuclideanSpace ℝ (Fin d), η15 < ‖x0‖ →
      ∀ p0 : EuclideanSpace ℝ (Fin d), ‖p0‖ ≤ ‖x0‖ ^ δ →
        (3 : ℝ) * ‖x0‖ < ‖leapfrogPos U ε x0 p0 1‖),
    ∀ x0 : EuclideanSpace ℝ (Fin d), max R η15 < ‖x0‖ →
      ∀ p0 : EuclideanSpace ℝ (Fin d), ‖p0‖ ≤ ‖x0‖ ^ δ →
        (∀ i ∈ Finset.Icc 1 L,
          (3 : ℝ) * ‖leapfrogPos U ε x0 p0 (i - 1)‖ ≤ ‖leapfrogPos U ε x0 p0 i‖) ∧
        (3 : ℝ) ^ L * ‖x0‖ ≤ ‖leapfrogPos U ε x0 p0 L‖ := by
  /- @proof-region region.target-node.session.a68b031cfe4a9cd8 begin -/
  intro d U ε hε δ hδ L hL R hR hRgrad η15 hη15 x0 hx0 p0 hp0
  have hηx0 : η15 < ‖x0‖ := lt_of_le_of_lt (le_max_right R η15) hx0
  have hRx0 : R < ‖x0‖ := lt_of_le_of_lt (le_max_left R η15) hx0
  have hx0pos : 0 < ‖x0‖ := lt_trans (lt_of_lt_of_le zero_lt_one hR) hRx0
  let f : ℕ → EuclideanSpace ℝ (Fin d) := fun i => leapfrogPos U ε x0 p0 i
  have hbase : 3 * ‖x0‖ < ‖f 1‖ := hη15 x0 hηx0 p0 hp0
  have hbase0 : 3 * ‖f 0‖ < ‖f 1‖ := by
    have h : f 0 = x0 := rfl
    rw [h]
    exact hbase
  have hstep : ∀ n : ℕ, (3 : ℝ) ^ (n + 1) * ‖x0‖ ≤ ‖f (n + 1)‖ →
      3 * ‖f n‖ ≤ ‖f (n + 1)‖ →
      (3 : ℝ) ^ (n + 1 + 1) * ‖x0‖ ≤ ‖f (n + 1 + 1)‖ ∧
        3 * ‖f (n + 1)‖ ≤ ‖f (n + 1 + 1)‖ := by
    intro n hA hB
    have hp1 : (1 : ℝ) ≤ (3 : ℝ) ^ (n + 1) := one_le_pow₀ (by norm_num)
    have hxle : ‖x0‖ ≤ (3 : ℝ) ^ (n + 1) * ‖x0‖ :=
      le_mul_of_one_le_left (le_of_lt hx0pos) hp1
    have hnpos : (0 : ℝ) < ‖f (n + 1)‖ := by linarith
    have hRfn : R < ‖f (n + 1)‖ := by linarith
    have hgrad := hRgrad (f (n + 1)) hRfn
    have hgrad2 : (16 / 3 : ℝ) * ‖f (n + 1)‖ ≤ ε ^ 2 * ‖gradient U (f (n + 1))‖ := by
      rw [← mul_div_assoc] at hgrad
      rwa [le_div_iff₀ hnpos] at hgrad
    have hrec : f (n + 1 + 1) = 2 • f (n + 1) - f n - ε ^ 2 • gradient U (f (n + 1)) := rfl
    have hnorm : ε ^ 2 * ‖gradient U (f (n + 1))‖ - 2 * ‖f (n + 1)‖ - ‖f n‖ ≤ ‖f (n + 1 + 1)‖ := by
      have hrt := norm_sub_norm_le (ε ^ 2 • gradient U (f (n + 1))) (2 • f (n + 1) - f n)
      have hD : ‖ε ^ 2 • gradient U (f (n + 1))‖ = ε ^ 2 * ‖gradient U (f (n + 1))‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ε)]
      have hG : ‖2 • f (n + 1) - f n‖ ≤ 2 * ‖f (n + 1)‖ + ‖f n‖ := by
        have h2 : ‖2 • f (n + 1)‖ = 2 * ‖f (n + 1)‖ := by
          rw [← Nat.cast_smul_eq_nsmul ℝ 2 (f (n + 1)), norm_smul, Real.norm_eq_abs]
          norm_num
        calc ‖2 • f (n + 1) - f n‖ ≤ ‖2 • f (n + 1)‖ + ‖f n‖ := norm_sub_le _ _
          _ = 2 * ‖f (n + 1)‖ + ‖f n‖ := by rw [h2]
      have hE : ‖f (n + 1 + 1)‖ = ‖ε ^ 2 • gradient U (f (n + 1)) - (2 • f (n + 1) - f n)‖ := by
        rw [hrec]
        exact norm_sub_rev _ _
      rw [hE]
      rw [hD] at hrt
      linarith
    have hnew : 3 * ‖f (n + 1)‖ ≤ ‖f (n + 1 + 1)‖ := by linarith
    refine ⟨?_, hnew⟩
    have hpow : (3 : ℝ) ^ (n + 1 + 1) * ‖x0‖ = 3 * ((3 : ℝ) ^ (n + 1) * ‖x0‖) := by
      rw [pow_succ]
      ring
    rw [hpow]
    have hmul : 3 * ((3 : ℝ) ^ (n + 1) * ‖x0‖) ≤ 3 * ‖f (n + 1)‖ :=
      mul_le_mul_of_nonneg_left hA (by norm_num)
    linarith
  have hT : ∀ n : ℕ, (3 : ℝ) ^ (n + 1) * ‖x0‖ ≤ ‖f (n + 1)‖ ∧ 3 * ‖f n‖ ≤ ‖f (n + 1)‖ := by
    intro n
    induction n with
    | zero => exact ⟨by simpa using le_of_lt hbase, by simpa using le_of_lt hbase0⟩
    | succ n ih => exact hstep n ih.1 ih.2
  refine ⟨?_, ?_⟩
  · intro i hi
    obtain ⟨hi1, _⟩ := Finset.mem_Icc.mp hi
    have h := (hT (i - 1)).2
    rw [Nat.sub_add_cancel hi1] at h
    exact h
  · have h := (hT (L - 1)).1
    rw [Nat.sub_add_cancel hL] at h
    exact h
  /- @proof-region region.target-node.session.a68b031cfe4a9cd8 end -/

end Statlib.Imported

