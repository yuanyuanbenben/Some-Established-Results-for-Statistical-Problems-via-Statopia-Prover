import ProverJobs.real_main_theorem_edd06e2c7e6c.Vocabulary
import ProverJobs.real_main_theorem_edd06e2c7e6c.Base


set_option autoImplicit false in
theorem statopia_math_node_3776635361_5eaf0306 : ∀ (a : ℕ → ℕ) (ha : IsValidSeq a),
    (∀ n : ℕ, 1 < a n) ∧
    (∀ n : ℕ, a n < a (n + 1)) ∧
    (∀ i j : ℕ, i ≤ j → a i ≤ a j) ∧
    Function.Injective a ∧
    (∀ x : ℕ, ∃ n : ℕ, x ≤ a n) ∧
    (∀ n : ℕ, 0 < a n ∧ ∀ i : ℕ, 1 < Nat.gcd (a n) (a i)) ∧
    (∀ x y : ℕ, (0 < x ∧ ∀ i : ℕ, 1 < Nat.gcd x (a i)) → x ∣ y → 0 < y →
      (0 < y ∧ ∀ i : ℕ, 1 < Nat.gcd y (a i))) ∧
    ¬ ((0 : ℕ) < 1 ∧ ∀ i : ℕ, 1 < Nat.gcd 1 (a i)) := by
  /- @proof-region region.target-node.session.029f5fc103a7c6fd begin -/
  intro a ha
  obtain ⟨h1, h2⟩ := ha
  have hstep : ∀ n : ℕ, a n < a (n + 1) := fun n => (h2 n).1
  have hmono_aux : ∀ k i : ℕ, a i ≤ a (i + k) := by
    intro k
    induction k with
    | zero =>
      intro i
      simp
    | succ k ih =>
      intro i
      have h1' : a i ≤ a (i + k) := ih i
      have h2' : a (i + k) ≤ a (i + (k + 1)) := by
        rw [← Nat.add_assoc]
        exact le_of_lt (hstep (i + k))
      exact le_trans h1' h2'
  have hmono : ∀ i j : ℕ, i ≤ j → a i ≤ a j := by
    intro i j hij
    have h := hmono_aux (j - i) i
    have heq : i + (j - i) = j := by omega
    rw [heq] at h
    exact h
  have hinj : Function.Injective a := by
    intro i j hij
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have h1' : a i < a (i + 1) := hstep i
      have h2' : a (i + 1) ≤ a j := hmono (i + 1) j (by omega)
      omega
    · have h1' : a j < a (j + 1) := hstep j
      have h2' : a (j + 1) ≤ a i := hmono (j + 1) i (by omega)
      omega
  have hbound : ∀ x : ℕ, x ≤ a x := by
    intro x
    induction x with
    | zero => exact Nat.zero_le (a 0)
    | succ x ih =>
      have h := hstep x
      omega
  have hgood : ∀ n : ℕ, 0 < a n ∧ ∀ i : ℕ, 1 < Nat.gcd (a n) (a i) := by
    intro n
    refine ⟨Nat.lt_trans Nat.zero_lt_one (h1 n), ?_⟩
    intro i
    rcases lt_trichotomy i n with hlt | heq | hgt
    · have h := (h2 (n - 1)).2.1 i (by omega)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at h
      exact h
    · rw [heq, Nat.gcd_self]
      exact h1 n
    · have h := (h2 (i - 1)).2.1 n (by omega)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ i), Nat.gcd_comm] at h
      exact h
  have hclosed : ∀ x y : ℕ, (0 < x ∧ ∀ i : ℕ, 1 < Nat.gcd x (a i)) → x ∣ y → 0 < y →
      (0 < y ∧ ∀ i : ℕ, 1 < Nat.gcd y (a i)) := by
    intro x y hx hxy hy
    refine ⟨hy, ?_⟩
    intro i
    have hd1 : 1 < Nat.gcd x (a i) := hx.2 i
    have hdvd : Nat.gcd x (a i) ∣ Nat.gcd y (a i) :=
      Nat.dvd_gcd (dvd_trans (Nat.gcd_dvd_left x (a i)) hxy) (Nat.gcd_dvd_right x (a i))
    obtain ⟨c, hc⟩ := hdvd
    have hcpos : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h0 | hpos
      · exfalso
        rw [h0, mul_zero] at hc
        obtain ⟨e, he⟩ := Nat.gcd_dvd_left y (a i)
        rw [hc, zero_mul] at he
        omega
      · exact hpos
    rw [hc]
    have hle : Nat.gcd x (a i) * 1 ≤ Nat.gcd x (a i) * c := Nat.mul_le_mul_left _ hcpos
    rw [mul_one] at hle
    exact lt_of_lt_of_le hd1 hle
  refine ⟨h1, hstep, hmono, hinj, fun x => ⟨x, hbound x⟩, hgood, hclosed, ?_⟩
  rintro ⟨-, h⟩
  have h0 := h 0
  simp at h0

  /- @proof-region region.target-node.session.029f5fc103a7c6fd end -/
