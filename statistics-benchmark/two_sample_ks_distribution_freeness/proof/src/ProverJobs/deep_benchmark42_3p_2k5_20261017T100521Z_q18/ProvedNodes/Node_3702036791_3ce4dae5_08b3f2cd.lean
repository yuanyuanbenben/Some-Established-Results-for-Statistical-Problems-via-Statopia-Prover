import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q18.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q18.Base

open MeasureTheory ProbabilityTheory Filter

open MeasureTheory ProbabilityTheory Filter

set_option autoImplicit false in
theorem statopia_math_node_3702036791_3ce4dae5 : ∀ (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (a : Fin m → ℝ) (b : Fin n → ℝ),
    let Delta : ℝ → ℝ := fun t =>
      |(m : ℝ)⁻¹ * ∑ i : Fin m, (if a i ≤ t then (1 : ℝ) else 0)
        - (n : ℝ)⁻¹ * ∑ j : Fin n, (if b j ≤ t then (1 : ℝ) else 0)|
    let M : ℝ := sSup (Set.insert (0 : ℝ)
      (Set.range (fun i : Fin m => Delta (a i)) ∪
       Set.range (fun j : Fin n => Delta (b j))))
    (⨆ t : ℝ, Delta t) = M ∧
      ((∀ i : Fin m, a i ∈ Set.Ioo (0 : ℝ) 1) →
       (∀ j : Fin n, b j ∈ Set.Ioo (0 : ℝ) 1) →
        (⨆ u : Set.Icc (0 : ℝ) 1, Delta u.1) = M) := by
  /- @proof-region region.target-node.session.2d11a77b1cc2c53f begin -/
  intro m n hm hn a b
  classical
  let Delta : ℝ → ℝ := fun t =>
      |(m : ℝ)⁻¹ * ∑ i : Fin m, (if a i ≤ t then (1 : ℝ) else 0)
        - (n : ℝ)⁻¹ * ∑ j : Fin n, (if b j ≤ t then (1 : ℝ) else 0)|
  let S : Set ℝ := Set.insert (0 : ℝ)
      (Set.range (fun i : Fin m => Delta (a i)) ∪
       Set.range (fun j : Fin n => Delta (b j)))
  let M : ℝ := sSup S
  change (⨆ t : ℝ, Delta t) = M ∧
    ((∀ i : Fin m, a i ∈ Set.Ioo (0 : ℝ) 1) →
     (∀ j : Fin n, b j ∈ Set.Ioo (0 : ℝ) 1) →
      (⨆ u : Set.Icc (0 : ℝ) 1, Delta u.1) = M)
  haveI hneR : Nonempty ℝ := ⟨0⟩
  have hDelta_apply : ∀ t : ℝ, Delta t =
      |(m : ℝ)⁻¹ * ∑ i : Fin m, (if a i ≤ t then (1 : ℝ) else 0)
        - (n : ℝ)⁻¹ * ∑ j : Fin n, (if b j ≤ t then (1 : ℝ) else 0)| := fun t => rfl
  have hSdef : S = Set.insert (0 : ℝ)
      (Set.range (fun i : Fin m => Delta (a i)) ∪
       Set.range (fun j : Fin n => Delta (b j))) := rfl
  have hSfin : S.Finite := by
    rw [hSdef]
    exact (Set.finite_range (fun i : Fin m => Delta (a i))).union
      (Set.finite_range (fun j : Fin n => Delta (b j))) |>.insert 0
  have hBddS : BddAbove S := hSfin.bddAbove
  have hSne : S.Nonempty :=
    ⟨0, by rw [hSdef]; exact Set.mem_insert_iff.mpr (Or.inl rfl)⟩
  have hstep : ∀ t : ℝ, Delta t ∈ S := by
    intro t
    let pool : Finset ℝ := Finset.univ.image a ∪ Finset.univ.image b
    have hmemA : ∀ i : Fin m, a i ∈ pool := by
      intro i
      show a i ∈ Finset.univ.image a ∪ Finset.univ.image b
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
    have hmemB : ∀ j : Fin n, b j ∈ pool := by
      intro j
      show b j ∈ Finset.univ.image a ∪ Finset.univ.image b
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩))
    have hkey : ∀ s s' : ℝ, (∀ x ∈ pool, (x ≤ s ↔ x ≤ s')) → Delta s = Delta s' := by
      intro s s' hss
      have hSa : (∑ i : Fin m, (if a i ≤ s then (1 : ℝ) else 0))
          = (∑ i : Fin m, (if a i ≤ s' then (1 : ℝ) else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        have hi : a i ≤ s ↔ a i ≤ s' := hss (a i) (hmemA i)
        by_cases h : a i ≤ s
        · rw [if_pos h, if_pos (hi.mp h)]
        · rw [if_neg h, if_neg (fun hc => h (hi.mpr hc))]
      have hSb : (∑ j : Fin n, (if b j ≤ s then (1 : ℝ) else 0))
          = (∑ j : Fin n, (if b j ≤ s' then (1 : ℝ) else 0)) := by
        apply Finset.sum_congr rfl
        intro j _
        have hj : b j ≤ s ↔ b j ≤ s' := hss (b j) (hmemB j)
        by_cases h : b j ≤ s
        · rw [if_pos h, if_pos (hj.mp h)]
        · rw [if_neg h, if_neg (fun hc => h (hj.mpr hc))]
      rw [hDelta_apply s, hDelta_apply s', hSa, hSb]
    by_cases hne : (pool.filter (fun x => x ≤ t)).Nonempty
    · have hmemmax : (pool.filter (fun x => x ≤ t)).max' hne ∈ pool.filter (fun x => x ≤ t) :=
        Finset.max'_mem _ hne
      have hlemax : (pool.filter (fun x => x ≤ t)).max' hne ≤ t := (Finset.mem_filter.mp hmemmax).2
      have hkey2 : ∀ x ∈ pool, (x ≤ t ↔ x ≤ (pool.filter (fun x => x ≤ t)).max' hne) := by
        intro x hx
        exact ⟨fun hxt => Finset.le_max' _ x (Finset.mem_filter.mpr ⟨hx, hxt⟩),
          fun hx' => le_trans hx' hlemax⟩
      have hEq : Delta t = Delta ((pool.filter (fun x => x ≤ t)).max' hne) := hkey t _ hkey2
      have hpool : (pool.filter (fun x => x ≤ t)).max' hne ∈ pool := (Finset.mem_filter.mp hmemmax).1
      rcases Finset.mem_union.mp hpool with h | h
      · rcases Finset.mem_image.mp h with ⟨i, _, hi⟩
        rw [hEq, ← hi, hSdef]
        exact Set.mem_insert_iff.mpr (Or.inr (Or.inl ⟨i, rfl⟩))
      · rcases Finset.mem_image.mp h with ⟨j, _, hj⟩
        rw [hEq, ← hj, hSdef]
        exact Set.mem_insert_iff.mpr (Or.inr (Or.inr ⟨j, rfl⟩))
    · have hall : ∀ x ∈ pool, ¬ x ≤ t := by
        intro x hx hxt
        exact hne ⟨x, Finset.mem_filter.mpr ⟨hx, hxt⟩⟩
      have hSa : (∑ i : Fin m, (if a i ≤ t then (1 : ℝ) else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        have hi : ¬ a i ≤ t := hall (a i) (hmemA i)
        simp only [if_neg hi]
      have hSb : (∑ j : Fin n, (if b j ≤ t then (1 : ℝ) else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        have hj : ¬ b j ≤ t := hall (b j) (hmemB j)
        simp only [if_neg hj]
      have h0 : Delta t = 0 := by
        rw [hDelta_apply t, hSa, hSb]
        simp
      rw [h0, hSdef]
      exact Set.mem_insert_iff.mpr (Or.inl rfl)
  have hsubR : Set.range Delta ⊆ S := by
    rintro x ⟨t, rfl⟩
    exact hstep t
  have hBddR : BddAbove (Set.range Delta) := hBddS.mono hsubR
  constructor
  · apply le_antisymm
    · apply ciSup_le
      intro t
      exact le_csSup hBddS (hstep t)
    · apply csSup_le hSne
      intro x hx
      rw [hSdef] at hx
      rcases Set.mem_insert_iff.mp hx with hx0 | hx
      · rw [hx0]
        have h0 : (0 : ℝ) ≤ Delta 0 := by
          rw [hDelta_apply 0]
          exact abs_nonneg _
        exact le_trans h0 (le_ciSup hBddR 0)
      · rcases hx with ⟨i, rfl⟩ | ⟨j, rfl⟩
        · exact le_ciSup hBddR (a i)
        · exact le_ciSup hBddR (b j)
  · intro ha hb
    haveI hneI : Nonempty (Set.Icc (0 : ℝ) 1) := ⟨⟨0, le_refl 0, zero_le_one⟩⟩
    have hsubI : Set.range (fun u : Set.Icc (0 : ℝ) 1 => Delta u.1) ⊆ S := by
      rintro x ⟨u, rfl⟩
      exact hstep u.1
    have hBddI : BddAbove (Set.range (fun u : Set.Icc (0 : ℝ) 1 => Delta u.1)) :=
      hBddS.mono hsubI
    apply le_antisymm
    · apply ciSup_le
      intro u
      exact le_csSup hBddS (hstep u.1)
    · apply csSup_le hSne
      intro x hx
      rw [hSdef] at hx
      rcases Set.mem_insert_iff.mp hx with hx0 | hx
      · rw [hx0]
        have h0 : Delta 0 = 0 := by
          rw [hDelta_apply 0]
          have hSa : (∑ i : Fin m, (if a i ≤ (0 : ℝ) then (1 : ℝ) else 0)) = 0 := by
            apply Finset.sum_eq_zero
            intro i _
            have hi : ¬ a i ≤ (0 : ℝ) := not_le.mpr (ha i).1
            simp only [if_neg hi]
          have hSb : (∑ j : Fin n, (if b j ≤ (0 : ℝ) then (1 : ℝ) else 0)) = 0 := by
            apply Finset.sum_eq_zero
            intro j _
            have hj : ¬ b j ≤ (0 : ℝ) := not_le.mpr (hb j).1
            simp only [if_neg hj]
          rw [hSa, hSb]
          simp
        exact (le_of_eq h0.symm).trans (le_ciSup hBddI ⟨0, le_refl (0 : ℝ), zero_le_one⟩)
      · rcases hx with ⟨i, rfl⟩ | ⟨j, rfl⟩
        · exact le_ciSup hBddI ⟨a i, le_of_lt (ha i).1, le_of_lt (ha i).2⟩
        · exact le_ciSup hBddI ⟨b j, le_of_lt (hb j).1, le_of_lt (hb j).2⟩
  /- @proof-region region.target-node.session.2d11a77b1cc2c53f end -/
