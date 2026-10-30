import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q18.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q18.Base

open MeasureTheory ProbabilityTheory Filter

open MeasureTheory ProbabilityTheory Filter

set_option autoImplicit false in
theorem statopia_math_node_3990029311_22268063 : ∀ (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n),
    Measurable (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
      max 0 (max
        ((Finset.univ : Finset (Fin m)).sup'
          ⟨⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hm⟩, Finset.mem_univ _⟩
          (fun i : Fin m =>
            |(m : ℝ)⁻¹ * ∑ k : Fin m, (if p.1 k ≤ p.1 i then (1 : ℝ) else 0) -
             (n : ℝ)⁻¹ * ∑ k : Fin n, (if p.2 k ≤ p.1 i then (1 : ℝ) else 0)|))
        ((Finset.univ : Finset (Fin n)).sup'
          ⟨⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩, Finset.mem_univ _⟩
          (fun j : Fin n =>
            |(m : ℝ)⁻¹ * ∑ k : Fin m, (if p.1 k ≤ p.2 j then (1 : ℝ) else 0) -
             (n : ℝ)⁻¹ * ∑ k : Fin n, (if p.2 k ≤ p.2 j then (1 : ℝ) else 0)|)))) := by
  /- @proof-region region.target-node.session.0fa49145820ca021 begin -/
  intro m n hm hn
  have hsumM : ∀ (s : Finset (Fin m)) (g : Fin m → (Fin m → ℝ) × (Fin n → ℝ) → ℝ),
      (∀ k, Measurable (g k)) → Measurable (fun p => ∑ k ∈ s, g k p) := by
    intro s g hg
    induction s using Finset.induction with
    | empty =>
      have h0 := (hg ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hm⟩).sub
        (hg ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hm⟩)
      simpa using h0
    | insert a s ha ih =>
      simpa only [Finset.sum_insert ha] using (hg a).add ih
  have hsumN : ∀ (s : Finset (Fin n)) (g : Fin n → (Fin m → ℝ) × (Fin n → ℝ) → ℝ),
      (∀ k, Measurable (g k)) → Measurable (fun p => ∑ k ∈ s, g k p) := by
    intro s g hg
    induction s using Finset.induction with
    | empty =>
      have h0 := (hg ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩).sub
        (hg ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩)
      simpa using h0
    | insert a s ha ih =>
      simpa only [Finset.sum_insert ha] using (hg a).add ih
  have hindM : ∀ (i k : Fin m), Measurable (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
      (if p.1 k ≤ p.1 i then (1 : ℝ) else 0)) := by
    intro i k
    have hd : Measurable fun p : (Fin m → ℝ) × (Fin n → ℝ) => p.1 k - p.1 i :=
      ((measurable_pi_apply k).comp measurable_fst).sub
        ((measurable_pi_apply i).comp measurable_fst)
    have hs0 : MeasurableSet {p : (Fin m → ℝ) × (Fin n → ℝ) | p.1 k - p.1 i ≤ 0} :=
      hd measurableSet_Iic
    have hs : MeasurableSet {p : (Fin m → ℝ) × (Fin n → ℝ) | p.1 k ≤ p.1 i} := by
      simpa [sub_nonpos] using hs0
    have h := (measurable_const : Measurable fun _ : (Fin m → ℝ) × (Fin n → ℝ) => (1 : ℝ)).indicator hs
    simpa [Set.indicator_apply] using h
  have hindN : ∀ (i k : Fin n), Measurable (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
      (if p.2 k ≤ p.2 i then (1 : ℝ) else 0)) := by
    intro i k
    have hd : Measurable fun p : (Fin m → ℝ) × (Fin n → ℝ) => p.2 k - p.2 i :=
      ((measurable_pi_apply k).comp measurable_snd).sub
        ((measurable_pi_apply i).comp measurable_snd)
    have hs0 : MeasurableSet {p : (Fin m → ℝ) × (Fin n → ℝ) | p.2 k - p.2 i ≤ 0} :=
      hd measurableSet_Iic
    have hs : MeasurableSet {p : (Fin m → ℝ) × (Fin n → ℝ) | p.2 k ≤ p.2 i} := by
      simpa [sub_nonpos] using hs0
    have h := (measurable_const : Measurable fun _ : (Fin m → ℝ) × (Fin n → ℝ) => (1 : ℝ)).indicator hs
    simpa [Set.indicator_apply] using h
  have hcrossM : ∀ (i : Fin m) (k : Fin n), Measurable (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
      (if p.2 k ≤ p.1 i then (1 : ℝ) else 0)) := by
    intro i k
    have hd : Measurable fun p : (Fin m → ℝ) × (Fin n → ℝ) => p.2 k - p.1 i :=
      ((measurable_pi_apply k).comp measurable_snd).sub
        ((measurable_pi_apply i).comp measurable_fst)
    have hs0 : MeasurableSet {p : (Fin m → ℝ) × (Fin n → ℝ) | p.2 k - p.1 i ≤ 0} :=
      hd measurableSet_Iic
    have hs : MeasurableSet {p : (Fin m → ℝ) × (Fin n → ℝ) | p.2 k ≤ p.1 i} := by
      simpa [sub_nonpos] using hs0
    have h := (measurable_const : Measurable fun _ : (Fin m → ℝ) × (Fin n → ℝ) => (1 : ℝ)).indicator hs
    simpa [Set.indicator_apply] using h
  have hcrossN : ∀ (i : Fin n) (k : Fin m), Measurable (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
      (if p.1 k ≤ p.2 i then (1 : ℝ) else 0)) := by
    intro i k
    have hd : Measurable fun p : (Fin m → ℝ) × (Fin n → ℝ) => p.1 k - p.2 i :=
      ((measurable_pi_apply k).comp measurable_fst).sub
        ((measurable_pi_apply i).comp measurable_snd)
    have hs0 : MeasurableSet {p : (Fin m → ℝ) × (Fin n → ℝ) | p.1 k - p.2 i ≤ 0} :=
      hd measurableSet_Iic
    have hs : MeasurableSet {p : (Fin m → ℝ) × (Fin n → ℝ) | p.1 k ≤ p.2 i} := by
      simpa [sub_nonpos] using hs0
    have h := (measurable_const : Measurable fun _ : (Fin m → ℝ) × (Fin n → ℝ) => (1 : ℝ)).indicator hs
    simpa [Set.indicator_apply] using h
  have hA : ∀ i : Fin m, Measurable (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
      |(m : ℝ)⁻¹ * ∑ k : Fin m, (if p.1 k ≤ p.1 i then (1 : ℝ) else 0) -
       (n : ℝ)⁻¹ * ∑ k : Fin n, (if p.2 k ≤ p.1 i then (1 : ℝ) else 0)|) := by
    intro i
    have h1 : Measurable (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
        ∑ k : Fin m, (if p.1 k ≤ p.1 i then (1 : ℝ) else 0)) :=
      hsumM Finset.univ (fun k p => (if p.1 k ≤ p.1 i then (1 : ℝ) else 0)) (fun k => hindM i k)
    have h2 : Measurable (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
        ∑ k : Fin n, (if p.2 k ≤ p.1 i then (1 : ℝ) else 0)) :=
      hsumN Finset.univ (fun k p => (if p.2 k ≤ p.1 i then (1 : ℝ) else 0)) (fun k => hcrossM i k)
    have hc1 : Measurable (fun _ : (Fin m → ℝ) × (Fin n → ℝ) => (m : ℝ)⁻¹) := measurable_const
    have hc2 : Measurable (fun _ : (Fin m → ℝ) × (Fin n → ℝ) => (n : ℝ)⁻¹) := measurable_const
    have h3 := (hc1.mul h1).sub (hc2.mul h2)
    exact continuous_abs.measurable.comp h3
  have hB : ∀ j : Fin n, Measurable (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
      |(m : ℝ)⁻¹ * ∑ k : Fin m, (if p.1 k ≤ p.2 j then (1 : ℝ) else 0) -
       (n : ℝ)⁻¹ * ∑ k : Fin n, (if p.2 k ≤ p.2 j then (1 : ℝ) else 0)|) := by
    intro j
    have h1 : Measurable (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
        ∑ k : Fin m, (if p.1 k ≤ p.2 j then (1 : ℝ) else 0)) :=
      hsumM Finset.univ (fun k p => (if p.1 k ≤ p.2 j then (1 : ℝ) else 0)) (fun k => hcrossN j k)
    have h2 : Measurable (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
        ∑ k : Fin n, (if p.2 k ≤ p.2 j then (1 : ℝ) else 0)) :=
      hsumN Finset.univ (fun k p => (if p.2 k ≤ p.2 j then (1 : ℝ) else 0)) (fun k => hindN j k)
    have hc1 : Measurable (fun _ : (Fin m → ℝ) × (Fin n → ℝ) => (m : ℝ)⁻¹) := measurable_const
    have hc2 : Measurable (fun _ : (Fin m → ℝ) × (Fin n → ℝ) => (n : ℝ)⁻¹) := measurable_const
    have h3 := (hc1.mul h1).sub (hc2.mul h2)
    exact continuous_abs.measurable.comp h3
  have hsupM : ∀ (F : Fin m → (Fin m → ℝ) × (Fin n → ℝ) → ℝ), (∀ i, Measurable (F i)) →
      Measurable (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
        (Finset.univ : Finset (Fin m)).sup'
          ⟨⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hm⟩, Finset.mem_univ _⟩
          (fun i => F i p)) := by
    intro F hF
    measurability
  have hsupN : ∀ (G : Fin n → (Fin m → ℝ) × (Fin n → ℝ) → ℝ), (∀ j, Measurable (G j)) →
      Measurable (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
        (Finset.univ : Finset (Fin n)).sup'
          ⟨⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩, Finset.mem_univ _⟩
          (fun j => G j p)) := by
    intro G hG
    measurability
  have hsupA : Measurable (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
      (Finset.univ : Finset (Fin m)).sup'
        ⟨⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hm⟩, Finset.mem_univ _⟩
        (fun i : Fin m =>
          |(m : ℝ)⁻¹ * ∑ k : Fin m, (if p.1 k ≤ p.1 i then (1 : ℝ) else 0) -
           (n : ℝ)⁻¹ * ∑ k : Fin n, (if p.2 k ≤ p.1 i then (1 : ℝ) else 0)|)) :=
    hsupM (fun i p =>
      |(m : ℝ)⁻¹ * ∑ k : Fin m, (if p.1 k ≤ p.1 i then (1 : ℝ) else 0) -
       (n : ℝ)⁻¹ * ∑ k : Fin n, (if p.2 k ≤ p.1 i then (1 : ℝ) else 0)|) hA
  have hsupB : Measurable (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
      (Finset.univ : Finset (Fin n)).sup'
        ⟨⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩, Finset.mem_univ _⟩
        (fun j : Fin n =>
          |(m : ℝ)⁻¹ * ∑ k : Fin m, (if p.1 k ≤ p.2 j then (1 : ℝ) else 0) -
           (n : ℝ)⁻¹ * ∑ k : Fin n, (if p.2 k ≤ p.2 j then (1 : ℝ) else 0)|)) :=
    hsupN (fun j p =>
      |(m : ℝ)⁻¹ * ∑ k : Fin m, (if p.1 k ≤ p.2 j then (1 : ℝ) else 0) -
       (n : ℝ)⁻¹ * ∑ k : Fin n, (if p.2 k ≤ p.2 j then (1 : ℝ) else 0)|) hB
  have hmaxid : ∀ a b : ℝ, max a b = (a + b + |a - b|) / 2 := by
    intro a b
    rcases le_total a b with h | h
    · rw [max_eq_right h, abs_of_nonpos (by linarith : a - b ≤ 0)]
      linarith
    · rw [max_eq_left h, abs_of_nonneg (by linarith : 0 ≤ a - b)]
      linarith
  have hmax2 : ∀ (F G : (Fin m → ℝ) × (Fin n → ℝ) → ℝ), Measurable F → Measurable G →
      Measurable (fun p => max (F p) (G p)) := by
    intro F G hF hG
    have hd : Measurable fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p - G p := hF.sub hG
    have h1 : Measurable fun p : (Fin m → ℝ) × (Fin n → ℝ) => |F p - G p| :=
      continuous_abs.measurable.comp hd
    have h2 : Measurable fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p + G p + |F p - G p| :=
      (hF.add hG).add h1
    have hc : Measurable fun _ : (Fin m → ℝ) × (Fin n → ℝ) => (2 : ℝ)⁻¹ := measurable_const
    have h4 : Measurable fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
        (F p + G p + |F p - G p|) / 2 := by
      simpa only [div_eq_mul_inv] using h2.mul hc
    simpa only [hmaxid] using h4
  have hmax0 : ∀ (F : (Fin m → ℝ) × (Fin n → ℝ) → ℝ), Measurable F →
      Measurable (fun p => max (0 : ℝ) (F p)) := by
    intro F hF
    exact hmax2 (fun _ => 0) F
      (measurable_const : Measurable fun _ : (Fin m → ℝ) × (Fin n → ℝ) => (0 : ℝ)) hF
  exact hmax0 _ (hmax2 _ _ hsupA hsupB)
  /- @proof-region region.target-node.session.0fa49145820ca021 end -/
