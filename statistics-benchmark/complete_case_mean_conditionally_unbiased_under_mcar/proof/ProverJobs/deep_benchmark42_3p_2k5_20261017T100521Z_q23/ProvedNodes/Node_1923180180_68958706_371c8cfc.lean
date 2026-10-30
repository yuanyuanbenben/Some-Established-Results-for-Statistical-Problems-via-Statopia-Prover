import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q23.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q23.Base

open MeasureTheory ProbabilityTheory
open scoped BigOperators

open MeasureTheory ProbabilityTheory
open scoped BigOperators

set_option autoImplicit false in
theorem statopia_math_node_1923180180_68958706 : ∀ {Ω : Type*}
    [MeasurableSpace Ω]
    (n : ℕ)
    (R : Fin n → Ω → Bool)
    (hRmeas : ∀ i, Measurable (R i)),
    let Xvec : Ω → (Fin n → Bool) := fun ω j => R j ω
    let Kb : (Fin n → Bool) → ℕ := fun b => ∑ j : Fin n, if b j then 1 else 0
    let K : Ω → ℕ := fun ω => ∑ j : Fin n, if R j ω then 1 else 0
      let psi : Fin n → (Fin n → Bool) → ℝ := fun i b =>
        if 0 < Kb b then ((if b i then 1 else 0 : ℝ) / (Kb b : ℝ)) else 0
      let w : Fin n → Ω → ℝ := fun i ω => psi i (Xvec ω)
      (∀ (i : Fin n) (ω : Ω),
        w i ω = if 0 < K ω then ((if R i ω then 1 else 0 : ℝ) / (K ω : ℝ)) else 0) ∧
      Measurable Xvec ∧
      (∀ i : Fin n, Measurable (psi i)) ∧
      (∀ i : Fin n, Measurable (w i)) ∧
      (∀ (i : Fin n) (b : Fin n → Bool), 0 ≤ psi i b ∧ psi i b ≤ 1) ∧
      (∀ (i : Fin n) (ω : Ω), 0 ≤ w i ω ∧ w i ω ≤ 1) ∧
      (∀ (i : Fin n) (ω : Ω), |w i ω| ≤ 1) ∧
      MeasurableSet {ω : Ω | 0 < K ω} ∧
      {ω : Ω | 0 < K ω} = Xvec ⁻¹' {b : Fin n → Bool | 0 < Kb b} := by
  /- @proof-region region.target-node.session.4266132547b50081 begin -/
  intro Ω hΩ n R hRmeas
  letI : MeasurableSpace Ω := hΩ
  let Xvec : Ω → (Fin n → Bool) := fun ω j => R j ω
  let Kb : (Fin n → Bool) → ℕ := fun b => ∑ j : Fin n, if b j then 1 else 0
  let K : Ω → ℕ := fun ω => ∑ j : Fin n, if R j ω then 1 else 0
  let psi : Fin n → (Fin n → Bool) → ℝ := fun i b =>
    if 0 < Kb b then ((if b i then 1 else 0 : ℝ) / (Kb b : ℝ)) else 0
  let w : Fin n → Ω → ℝ := fun i ω => psi i (Xvec ω)
  have hKb_eval : ∀ b : Fin n → Bool, Kb b = ∑ j : Fin n, (if b j then 1 else 0 : ℕ) :=
    fun b => rfl
  have hK_eval : ∀ ω : Ω, K ω = ∑ j : Fin n, (if R j ω then 1 else 0 : ℕ) := fun ω => rfl
  have hXvec_eval : ∀ (ω : Ω) (j : Fin n), Xvec ω j = R j ω := fun ω j => rfl
  have hpsi_eval : ∀ (i : Fin n) (b : Fin n → Bool),
      psi i b = if 0 < Kb b then ((if b i then 1 else 0 : ℝ) / (Kb b : ℝ)) else 0 :=
    fun i b => rfl
  have hw_eval : ∀ (i : Fin n) (ω : Ω), w i ω = psi i (Xvec ω) := fun i ω => rfl
  have hcoord : ∀ j : Fin n, Measurable (fun b : Fin n → Bool => b j) :=
    fun j => measurable_pi_apply j
  have hsetj : ∀ j : Fin n, MeasurableSet {b : Fin n → Bool | b j = true} :=
    fun j => hcoord j measurableSet_eq
  have hXvec_meas : Measurable Xvec := by
    show Measurable (fun ω j => R j ω)
    exact measurable_pi_iff.mpr (fun j => hRmeas j)
  have hnum : ∀ j : Fin n, Measurable (fun b : Fin n → Bool => (if b j then 1 else 0 : ℝ)) := by
    intro j
    exact Measurable.ite (hsetj j) measurable_const measurable_const
  have hsum_meas : ∀ (f : Fin n → (Fin n → Bool) → ℝ), (∀ j : Fin n, Measurable (f j)) →
      Measurable (fun b : Fin n → Bool => ∑ j : Fin n, f j b) := by
    intro f hf
    have key : ∀ s : Finset (Fin n),
        Measurable (fun b : Fin n → Bool => ∑ j ∈ s, f j b) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using (measurable_const : Measurable fun _ : Fin n → Bool => (0 : ℝ))
      | insert a s ha ih =>
        have hsplit : (fun b : Fin n → Bool => ∑ j ∈ insert a s, f j b)
            = fun b => f a b + ∑ j ∈ s, f j b := by
          funext b
          rw [Finset.sum_insert ha]
        rw [hsplit]
        exact (hf a).add ih
    exact key Finset.univ
  have hden : Measurable (fun b : Fin n → Bool => (Kb b : ℝ)) := by
    have hcast : (fun b : Fin n → Bool => (Kb b : ℝ))
        = fun b => ∑ j : Fin n, (if b j then 1 else 0 : ℝ) := by
      funext b
      rw [hKb_eval b, Nat.cast_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      by_cases hbj : b j = true <;> simp [hbj]
    rw [hcast]
    exact hsum_meas (fun j b => (if b j then 1 else 0 : ℝ)) hnum
  have hKb_set : MeasurableSet {b : Fin n → Bool | 0 < Kb b} := by
    have heq : {b : Fin n → Bool | 0 < Kb b}
        = ⋃ j : Fin n, {b : Fin n → Bool | b j = true} := by
      ext b
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      rw [hKb_eval b]
      constructor
      · intro h
        by_contra hc
        simp only [not_exists] at hc
        have hzero : ∑ j : Fin n, (if b j then 1 else 0 : ℕ) = 0 := by
          apply Finset.sum_eq_zero
          intro j _
          have hbj : b j = false := by
            cases hh : b j with
            | false => rfl
            | true => exact absurd hh (hc j)
          simp [hbj]
        rw [hzero] at h
        exact lt_irrefl 0 h
      · rintro ⟨j, hj⟩
        have hle : (if b j then 1 else 0 : ℕ) ≤ ∑ x : Fin n, (if b x then 1 else 0) :=
          Finset.single_le_sum (f := fun x : Fin n => (if b x then 1 else 0 : ℕ))
            (fun x _ => Nat.zero_le _) (Finset.mem_univ j)
        have hone : (if b j then 1 else 0 : ℕ) = 1 := by simp [hj]
        rw [hone] at hle
        omega
    rw [heq]
    exact MeasurableSet.iUnion (fun j => hsetj j)
  have hpsi_meas : ∀ i : Fin n, Measurable (psi i) := by
    intro i
    show Measurable (fun b : Fin n → Bool =>
      if 0 < Kb b then ((if b i then 1 else 0 : ℝ) / (Kb b : ℝ)) else 0)
    exact Measurable.ite hKb_set ((hnum i).div hden) measurable_const
  have hw_meas : ∀ i : Fin n, Measurable (w i) := by
    intro i
    show Measurable (fun ω => psi i (Xvec ω))
    exact (hpsi_meas i).comp hXvec_meas
  have hK_set : MeasurableSet {ω : Ω | 0 < K ω} := by
    have heq : {ω : Ω | 0 < K ω} = ⋃ i : Fin n, {ω : Ω | R i ω = true} := by
      ext ω
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      rw [hK_eval ω]
      constructor
      · intro h
        by_contra hc
        simp only [not_exists] at hc
        have hzero : ∑ j : Fin n, (if R j ω then 1 else 0 : ℕ) = 0 := by
          apply Finset.sum_eq_zero
          intro j _
          have hbj : R j ω = false := by
            cases hh : R j ω with
            | false => rfl
            | true => exact absurd hh (hc j)
          simp [hbj]
        rw [hzero] at h
        exact lt_irrefl 0 h
      · rintro ⟨j, hj⟩
        have hle : (if R j ω then 1 else 0 : ℕ) ≤ ∑ x : Fin n, (if R x ω then 1 else 0) :=
          Finset.single_le_sum (f := fun x : Fin n => (if R x ω then 1 else 0 : ℕ))
            (fun x _ => Nat.zero_le _) (Finset.mem_univ j)
        have hone : (if R j ω then 1 else 0 : ℕ) = 1 := by simp [hj]
        rw [hone] at hle
        omega
    rw [heq]
    exact MeasurableSet.iUnion (fun i => hRmeas i measurableSet_eq)
  have hEq : {ω : Ω | 0 < K ω} = Xvec ⁻¹' {b : Fin n → Bool | 0 < Kb b} := by
    ext ω
    show 0 < K ω ↔ 0 < Kb (Xvec ω)
    simp only [hK_eval, hKb_eval, hXvec_eval]
  have hpt : ∀ (i : Fin n) (ω : Ω),
      w i ω = if 0 < K ω then ((if R i ω then 1 else 0 : ℝ) / (K ω : ℝ)) else 0 := by
    intro i ω
    have hKbX : Kb (Xvec ω) = K ω := by
      simp only [hKb_eval, hK_eval, hXvec_eval]
    have hXi : Xvec ω i = R i ω := hXvec_eval ω i
    simp only [hw_eval, hpsi_eval, hKbX, hXi]
  have hpsi_bounds : ∀ (i : Fin n) (b : Fin n → Bool), 0 ≤ psi i b ∧ psi i b ≤ 1 := by
    intro i b
    show 0 ≤ (if 0 < Kb b then ((if b i then 1 else 0 : ℝ) / (Kb b : ℝ)) else 0) ∧
      (if 0 < Kb b then ((if b i then 1 else 0 : ℝ) / (Kb b : ℝ)) else 0) ≤ 1
    by_cases h : 0 < Kb b
    · rw [if_pos h]
      have hpos : (0 : ℝ) < (Kb b : ℝ) := by exact_mod_cast h
      have hge1 : (1 : ℝ) ≤ (Kb b : ℝ) := by
        have h1 : (1 : ℕ) ≤ Kb b := by omega
        exact_mod_cast h1
      have hnum0 : (0 : ℝ) ≤ (if b i then 1 else 0 : ℝ) := by
        by_cases hbi : b i = true <;> simp [hbi]
      have hnum1 : (if b i then 1 else 0 : ℝ) ≤ 1 := by
        by_cases hbi : b i = true <;> simp [hbi]
      refine ⟨div_nonneg hnum0 hpos.le, ?_⟩
      have hstep : (if b i then 1 else 0 : ℝ) / (Kb b : ℝ) ≤ (if b i then 1 else 0 : ℝ) :=
        div_le_self hnum0 hge1
      linarith
    · rw [if_neg h]
      exact ⟨le_refl 0, by norm_num⟩
  refine ⟨hpt, hXvec_meas, hpsi_meas, hw_meas, hpsi_bounds, ?_, ?_, hK_set, hEq⟩
  · intro i ω
    show 0 ≤ psi i (Xvec ω) ∧ psi i (Xvec ω) ≤ 1
    exact hpsi_bounds i (Xvec ω)
  · intro i ω
    have h0 : (0 : ℝ) ≤ psi i (Xvec ω) := (hpsi_bounds i (Xvec ω)).1
    have h1 : psi i (Xvec ω) ≤ 1 := (hpsi_bounds i (Xvec ω)).2
    show |psi i (Xvec ω)| ≤ 1
    exact abs_le.mpr ⟨by linarith, h1⟩
  /- @proof-region region.target-node.session.4266132547b50081 end -/
