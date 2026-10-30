import ProverJobs.real_main_theorem_d734bdb6a642.Vocabulary
import ProverJobs.real_main_theorem_d734bdb6a642.Base
import ProverJobs.real_main_theorem_d734bdb6a642.ProvedNodes.Node_2498287263_10c06cca_bf6ab8d1

set_option autoImplicit false in
theorem statopia_math_node_4115935916_c5a90aa0 : ∀ (f : PositiveReal → PositiveReal)
    (hf : IsAdmissible f) (u v : PositiveReal),
    (f u : ℝ) - (u : ℝ) = (f v : ℝ) - (v : ℝ) := by
  /- @proof-region region.target-node.session.a0c9d36b5db819a7 begin -/
  intro f hf u v
  have core : ∀ p q : PositiveReal, (p : ℝ) < (q : ℝ) →
      (f q : ℝ) - (q : ℝ) = (f p : ℝ) - (p : ℝ) := by
    intro p q hpq
    have hp : 0 < (p : ℝ) := p.2
    have hqp : 0 < (q : ℝ) - (p : ℝ) := sub_pos.mpr hpq
    have bound : ∀ n : ℕ, 0 < n →
        |((f q : ℝ) - (q : ℝ)) - ((f p : ℝ) - (p : ℝ))| ≤
          ((q : ℝ) - (p : ℝ)) ^ 2 / (4 * (p : ℝ) * (n : ℝ)) := by
      intro n hn
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
      let h : ℝ := ((q : ℝ) - (p : ℝ)) / (n : ℝ)
      have hh : h = ((q : ℝ) - (p : ℝ)) / (n : ℝ) := rfl
      have hhpos : 0 < h := by rw [hh]; exact div_pos hqp hnR
      let t : ℕ → PositiveReal := fun i =>
        ⟨(p : ℝ) + (i : ℝ) * h,
          add_pos_of_pos_of_nonneg hp (mul_nonneg (Nat.cast_nonneg i) (le_of_lt hhpos))⟩
      let z : ℕ → ℝ := fun i =>
        ((f (t (i + 1)) : ℝ) - (t (i + 1) : ℝ)) - ((f (t i) : ℝ) - (t i : ℝ))
      have hzk : ∀ k : ℕ, z k = ((f (t (k + 1)) : ℝ) - (t (k + 1) : ℝ)) -
          ((f (t k) : ℝ) - (t k : ℝ)) := fun k => rfl
      have ht0 : t 0 = p := by
        apply Subtype.ext
        show (p : ℝ) + ((0 : ℕ) : ℝ) * h = (p : ℝ)
        simp
      have htn : t n = q := by
        apply Subtype.ext
        show (p : ℝ) + (n : ℝ) * h = (q : ℝ)
        rw [hh]
        field_simp
        ring
      have hth : ∀ i : ℕ, (t (i + 1) : ℝ) - (t i : ℝ) = h := by
        intro i
        show (p : ℝ) + ((i + 1 : ℕ) : ℝ) * h - ((p : ℝ) + (i : ℝ) * h) = h
        push_cast
        ring
      have htmem : ∀ i : ℕ, i ≤ n → (p : ℝ) ≤ (t i : ℝ) ∧ (t i : ℝ) ≤ (q : ℝ) := by
        intro i hi
        have hiR : (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast hi
        constructor
        · show (p : ℝ) ≤ (p : ℝ) + (i : ℝ) * h
          have h0 : 0 ≤ (i : ℝ) * h := mul_nonneg (Nat.cast_nonneg i) (le_of_lt hhpos)
          linarith
        · show (p : ℝ) + (i : ℝ) * h ≤ (q : ℝ)
          have hnnh : (n : ℝ) * h = (q : ℝ) - (p : ℝ) := by
            rw [hh]; field_simp
          have hle : (i : ℝ) * h ≤ (n : ℝ) * h :=
            mul_le_mul_of_nonneg_right hiR (le_of_lt hhpos)
          linarith
      have hstep : ∀ i : ℕ, i < n → |z i| ≤ h ^ 2 / (4 * (p : ℝ)) := by
        intro i hi
        obtain ⟨hl1, hu1⟩ := htmem i (le_of_lt hi)
        obtain ⟨hl2, hu2⟩ := htmem (i + 1) (by omega)
        have hdep := statopia_math_node_2498287263_10c06cca f hf (p : ℝ) (q : ℝ) hp hpq
          (t i) (t (i + 1)) hl1 hu1 hl2 hu2
        have hdep' := hdep
        rw [hth i] at hdep'
        exact hdep'
      have htel : ∀ m : ℕ, (∑ i ∈ Finset.range m, z i) =
          ((f (t m) : ℝ) - (t m : ℝ)) - ((f (t 0) : ℝ) - (t 0 : ℝ)) := by
        intro m
        induction m with
        | zero => simp
        | succ k ih =>
          rw [Finset.sum_range_succ, ih, hzk k]
          ring
      have htri : |∑ i ∈ Finset.range n, z i| ≤ ∑ i ∈ Finset.range n, |z i| := by
        have hall : ∀ m : ℕ, |∑ i ∈ Finset.range m, z i| ≤ ∑ i ∈ Finset.range m, |z i| := by
          intro m
          induction m with
          | zero => simp
          | succ k ih =>
            calc |(∑ i ∈ Finset.range (k + 1), z i)|
                = |(∑ i ∈ Finset.range k, z i) + z k| := by rw [Finset.sum_range_succ]
              _ ≤ |∑ i ∈ Finset.range k, z i| + |z k| := abs_add_le _ _
              _ ≤ (∑ i ∈ Finset.range k, |z i|) + |z k| := by linarith [ih]
              _ = ∑ i ∈ Finset.range (k + 1), |z i| := by rw [Finset.sum_range_succ]
        exact hall n
      have hconst : (∑ i ∈ Finset.range n, h ^ 2 / (4 * (p : ℝ))) =
          (n : ℝ) * (h ^ 2 / (4 * (p : ℝ))) := by
        have hall : ∀ m : ℕ, (∑ i ∈ Finset.range m, h ^ 2 / (4 * (p : ℝ))) =
            (m : ℝ) * (h ^ 2 / (4 * (p : ℝ))) := by
          intro m
          induction m with
          | zero => simp
          | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
        exact hall n
      calc |((f q : ℝ) - (q : ℝ)) - ((f p : ℝ) - (p : ℝ))|
          = |((f (t n) : ℝ) - (t n : ℝ)) - ((f (t 0) : ℝ) - (t 0 : ℝ))| := by rw [htn, ht0]
        _ = |∑ i ∈ Finset.range n, z i| := by rw [htel n]
        _ ≤ ∑ i ∈ Finset.range n, |z i| := htri
        _ ≤ ∑ i ∈ Finset.range n, h ^ 2 / (4 * (p : ℝ)) := by
            apply Finset.sum_le_sum
            intro i hi
            exact hstep i (Finset.mem_range.mp hi)
        _ = (n : ℝ) * (h ^ 2 / (4 * (p : ℝ))) := hconst
        _ = ((q : ℝ) - (p : ℝ)) ^ 2 / (4 * (p : ℝ) * (n : ℝ)) := by
            first | (rw [hh]; field_simp; ring) | (rw [hh]; field_simp)
    have hzero : |((f q : ℝ) - (q : ℝ)) - ((f p : ℝ) - (p : ℝ))| = 0 := by
      by_contra hne
      have hDpos : 0 < |((f q : ℝ) - (q : ℝ)) - ((f p : ℝ) - (p : ℝ))| :=
        lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
      have hnum : 0 < ((q : ℝ) - (p : ℝ)) ^ 2 := pow_pos hqp 2
      have hXpos : 0 < ((q : ℝ) - (p : ℝ)) ^ 2 /
          (4 * (p : ℝ) * |((f q : ℝ) - (q : ℝ)) - ((f p : ℝ) - (p : ℝ))|) :=
        div_pos hnum (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hp) hDpos)
      obtain ⟨n, hn⟩ := exists_nat_gt (((q : ℝ) - (p : ℝ)) ^ 2 /
        (4 * (p : ℝ) * |((f q : ℝ) - (q : ℝ)) - ((f p : ℝ) - (p : ℝ))|))
      have hnpos : 0 < n := by
        have : (0 : ℝ) < (n : ℝ) := lt_trans hXpos hn
        exact_mod_cast this
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
      have hden1 : 0 < 4 * (p : ℝ) * |((f q : ℝ) - (q : ℝ)) - ((f p : ℝ) - (p : ℝ))| :=
        mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hp) hDpos
      have hden2 : 0 < 4 * (p : ℝ) * (n : ℝ) :=
        mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hp) hnR
      have hA1 : ((q : ℝ) - (p : ℝ)) ^ 2 /
            (4 * (p : ℝ) * |((f q : ℝ) - (q : ℝ)) - ((f p : ℝ) - (p : ℝ))|) *
            (4 * (p : ℝ) * |((f q : ℝ) - (q : ℝ)) - ((f p : ℝ) - (p : ℝ))|)
          < (n : ℝ) * (4 * (p : ℝ) * |((f q : ℝ) - (q : ℝ)) - ((f p : ℝ) - (p : ℝ))|) :=
        mul_lt_mul_of_pos_right hn hden1
      have hC1 : ((q : ℝ) - (p : ℝ)) ^ 2 /
            (4 * (p : ℝ) * |((f q : ℝ) - (q : ℝ)) - ((f p : ℝ) - (p : ℝ))|) *
            (4 * (p : ℝ) * |((f q : ℝ) - (q : ℝ)) - ((f p : ℝ) - (p : ℝ))|)
          = ((q : ℝ) - (p : ℝ)) ^ 2 := by
        first | (field_simp; ring) | field_simp
      have hA2 : (n : ℝ) * (4 * (p : ℝ) * |((f q : ℝ) - (q : ℝ)) - ((f p : ℝ) - (p : ℝ))|)
          = |((f q : ℝ) - (q : ℝ)) - ((f p : ℝ) - (p : ℝ))| * (4 * (p : ℝ) * (n : ℝ)) := by
        ring
      have hB1 : |((f q : ℝ) - (q : ℝ)) - ((f p : ℝ) - (p : ℝ))| * (4 * (p : ℝ) * (n : ℝ)) ≤
          ((q : ℝ) - (p : ℝ)) ^ 2 / (4 * (p : ℝ) * (n : ℝ)) * (4 * (p : ℝ) * (n : ℝ)) :=
        mul_le_mul_of_nonneg_right (bound n hnpos) (le_of_lt hden2)
      have hC2 : ((q : ℝ) - (p : ℝ)) ^ 2 / (4 * (p : ℝ) * (n : ℝ)) * (4 * (p : ℝ) * (n : ℝ))
          = ((q : ℝ) - (p : ℝ)) ^ 2 := by
        first | (field_simp; ring) | field_simp
      have hlt2 : ((q : ℝ) - (p : ℝ)) ^ 2 <
          |((f q : ℝ) - (q : ℝ)) - ((f p : ℝ) - (p : ℝ))| * (4 * (p : ℝ) * (n : ℝ)) := by
        have ht := hA1
        rw [hC1, hA2] at ht
        exact ht
      have hle2 : |((f q : ℝ) - (q : ℝ)) - ((f p : ℝ) - (p : ℝ))| * (4 * (p : ℝ) * (n : ℝ)) ≤
          ((q : ℝ) - (p : ℝ)) ^ 2 := by
        have ht := hB1
        rw [hC2] at ht
        exact ht
      linarith
    have hdiff0 : ((f q : ℝ) - (q : ℝ)) - ((f p : ℝ) - (p : ℝ)) = 0 := abs_eq_zero.mp hzero
    linarith
  rcases lt_trichotomy (u : ℝ) (v : ℝ) with h | h | h
  · exact (core u v h).symm
  · have huv : u = v := Subtype.ext h
    rw [huv]
  · exact core v u h
  /- @proof-region region.target-node.session.a0c9d36b5db819a7 end -/
