import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base

open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_4092604145_3ac20b10 : ∀ (β : Type) [Fintype β] [DecidableEq β]
    (W : β → ℝ) (lab : β → ℕ) (S : Finset β) (ε : β → ℝ)
    (hS : ∃ u ∈ S, W u ≠ 0)
    (hW : ∀ u : β, W u ≠ 0 → W u = (2 : ℝ) ^ (lab u))
    (hInj : ∀ u v : β, W u ≠ 0 → W v ≠ 0 → lab u = lab v → u = v)
    (hEps : ∀ u ∈ S, ε u = 1 ∨ ε u = -1),
    1 ≤ |∑ u ∈ S, ε u * W u| := by
  /- @proof-region region.target-node.session.341cbdd2b4a8a4d8 begin -/
  intro β _ _ W lab S ε hS hW hInj hEps
  classical
  set T : Finset β := S.filter (fun u => W u ≠ 0) with hT
  have hTmem : ∀ u, u ∈ T ↔ u ∈ S ∧ W u ≠ 0 := by
    intro u
    rw [hT]
    exact Finset.mem_filter
  have hTnonempty : T.Nonempty := by
    obtain ⟨u, huS, huW⟩ := hS
    exact ⟨u, (hTmem u).mpr ⟨huS, huW⟩⟩
  have hTsubl : T ⊆ S := fun u hu => ((hTmem u).mp hu).1
  have hWne : ∀ u ∈ T, W u ≠ 0 := fun u hu => ((hTmem u).mp hu).2
  have hsum_eq : (∑ u ∈ S, ε u * W u) = ∑ u ∈ T, ε u * W u := by
    symm
    apply Finset.sum_subset hTsubl
    intro x hxS hxT
    have hxW : W x = 0 := by
      by_contra h
      exact hxT ((hTmem x).mpr ⟨hxS, h⟩)
    rw [hxW, mul_zero]
  obtain ⟨r, hrT, hrmax⟩ := Finset.exists_max_image T lab hTnonempty
  have hN : ∀ u ∈ T.erase r, lab u < lab r := by
    intro u hu
    have huT : u ∈ T := (Finset.mem_erase.mp hu).2
    have hune : u ≠ r := (Finset.mem_erase.mp hu).1
    rcases lt_or_eq_of_le (hrmax u huT) with h | h
    · exact h
    · exact absurd (hInj u r (hWne u huT) (hWne r hrT) h) hune
  have hinj2 : ∀ u ∈ T.erase r, ∀ v ∈ T.erase r, lab u = lab v → u = v := by
    intro u hu v hv h
    exact hInj u v (hWne u (Finset.mem_erase.mp hu).2) (hWne v (Finset.mem_erase.mp hv).2) h
  have hgeom : ∀ n : ℕ, (∑ i ∈ Finset.range n, (2:ℝ)^i) = (2:ℝ)^n - 1 := by
    intro n
    induction n with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  have injection_bound : ∀ (A : Finset β) (N : ℕ),
      (∀ u ∈ A, lab u < N) → (∀ u ∈ A, ∀ v ∈ A, lab u = lab v → u = v) →
      ∑ u ∈ A, (2:ℝ)^(lab u) ≤ ∑ i ∈ Finset.range N, (2:ℝ)^i := by
    intro A N hNA hinjA
    have hstep1 : (∑ u ∈ A, (2:ℝ)^(lab u))
        = ∑ u ∈ A, ∑ i ∈ Finset.range N, (if lab u = i then (2:ℝ)^i else 0) := by
      apply Finset.sum_congr rfl
      intro u hu
      have hsub : (∑ i ∈ Finset.range N, (if lab u = i then (2:ℝ)^i else 0))
                = ∑ i ∈ ({lab u} : Finset ℕ), (if lab u = i then (2:ℝ)^i else 0) := by
        symm
        apply Finset.sum_subset
        · intro x hx
          rw [Finset.mem_singleton] at hx
          rw [hx]
          exact Finset.mem_range.mpr (hNA u hu)
        · intro x hxr hxnot
          have hxne : x ≠ lab u := by rintro rfl; exact hxnot (Finset.mem_singleton_self _)
          have hne2 : ¬ (lab u = x) := fun h => hxne h.symm
          simp [hne2]
      rw [hsub, Finset.sum_singleton]
      simp
    have hswap : (∑ u ∈ A, (2:ℝ)^(lab u))
        = ∑ i ∈ Finset.range N, ∑ u ∈ A, (if lab u = i then (2:ℝ)^i else 0) :=
      hstep1.trans Finset.sum_comm
    rw [hswap]
    apply Finset.sum_le_sum
    intro i hi
    by_cases hex : ∃ u ∈ A, lab u = i
    · obtain ⟨u0, hu0A, hu0⟩ := hex
      have hsingle : (∑ u ∈ A, (if lab u = i then (2:ℝ)^i else 0)) = (2:ℝ)^i := by
        have hsub : (∑ u ∈ A, (if lab u = i then (2:ℝ)^i else 0))
                  = ∑ u ∈ ({u0} : Finset β), (if lab u = i then (2:ℝ)^i else 0) := by
          symm
          apply Finset.sum_subset
          · intro x hx
            rw [Finset.mem_singleton] at hx
            rw [hx]
            exact hu0A
          · intro x hxA hxnot
            have hxne : x ≠ u0 := by rintro rfl; exact hxnot (Finset.mem_singleton_self _)
            have hli : lab x ≠ i := by
              intro h
              exact hxne (hinjA x hxA u0 hu0A (by rw [h, hu0]))
            simp [hli]
        rw [hsub, Finset.sum_singleton]
        simp [hu0]
      exact le_of_eq hsingle
    · have hz : (∑ u ∈ A, (if lab u = i then (2:ℝ)^i else 0)) = 0 :=
        Finset.sum_eq_zero (fun u hu => by
          have : lab u ≠ i := fun h => hex ⟨u, hu, h⟩
          simp [this])
      rw [hz]
      positivity
  have hGB2 : ∑ u ∈ T.erase r, (2:ℝ)^(lab u) ≤ ∑ i ∈ Finset.range (lab r), (2:ℝ)^i :=
    injection_bound (T.erase r) (lab r) hN hinj2
  have hGB : ∑ u ∈ T.erase r, W u ≤ (2:ℝ)^(lab r) - 1 := by
    have hWpow : (∑ u ∈ T.erase r, W u) = ∑ u ∈ T.erase r, (2:ℝ)^(lab u) := by
      apply Finset.sum_congr rfl
      intro u hu
      exact hW u (hWne u (Finset.mem_erase.mp hu).2)
    rw [hWpow, ← hgeom (lab r)]
    exact hGB2
  have hB : |ε r * W r| = (2:ℝ)^(lab r) := by
    have hWr : W r = (2:ℝ)^(lab r) := hW r (hWne r hrT)
    have heps : |ε r| = 1 := by
      rcases hEps r (hTsubl hrT) with h | h <;> rw [h] <;> simp
    rw [abs_mul, heps, one_mul, hWr, abs_of_nonneg (by positivity)]
  have hC : |∑ u ∈ T.erase r, ε u * W u| ≤ ∑ u ∈ T.erase r, W u := by
    calc |∑ u ∈ T.erase r, ε u * W u|
        ≤ ∑ u ∈ T.erase r, |ε u * W u| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ u ∈ T.erase r, W u := by
          apply Finset.sum_congr rfl
          intro u hu
          have huT : u ∈ T := (Finset.mem_erase.mp hu).2
          have hWu : W u = (2:ℝ)^(lab u) := hW u (hWne u huT)
          have hpos : 0 ≤ W u := by rw [hWu]; positivity
          rcases hEps u (hTsubl huT) with h | h
          · rw [h, one_mul, abs_of_nonneg hpos]
          · rw [h, abs_mul, abs_neg, abs_one, one_mul, abs_of_nonneg hpos]
  have hsplit : (∑ u ∈ T, ε u * W u) = ε r * W r + ∑ u ∈ T.erase r, ε u * W u := by
    conv_lhs => rw [← Finset.insert_erase hrT]
    rw [Finset.sum_insert (by intro h; exact (Finset.mem_erase.mp h).1 rfl)]
  have hrev : |ε r * W r| - |∑ u ∈ T.erase r, ε u * W u|
      ≤ |ε r * W r + ∑ u ∈ T.erase r, ε u * W u| := by
    have hBC : (ε r * W r + ∑ u ∈ T.erase r, ε u * W u)
        + (-(∑ u ∈ T.erase r, ε u * W u)) = ε r * W r := by ring
    have h2 : |ε r * W r|
        ≤ |ε r * W r + ∑ u ∈ T.erase r, ε u * W u| + |∑ u ∈ T.erase r, ε u * W u| := by
      calc |ε r * W r|
          = |(ε r * W r + ∑ u ∈ T.erase r, ε u * W u)
              + (-(∑ u ∈ T.erase r, ε u * W u))| := by rw [hBC]
        _ ≤ |ε r * W r + ∑ u ∈ T.erase r, ε u * W u|
              + |-(∑ u ∈ T.erase r, ε u * W u)| := abs_add_le _ _
        _ = |ε r * W r + ∑ u ∈ T.erase r, ε u * W u|
              + |∑ u ∈ T.erase r, ε u * W u| := by rw [abs_neg]
    linarith
  have hmain : (2:ℝ)^(lab r) - (∑ u ∈ T.erase r, W u) ≤ |∑ u ∈ T, ε u * W u| := by
    rw [hsplit]
    calc (2:ℝ)^(lab r) - ∑ u ∈ T.erase r, W u
        ≤ |ε r * W r| - |∑ u ∈ T.erase r, ε u * W u| := by rw [hB]; linarith [hC]
      _ ≤ |ε r * W r + ∑ u ∈ T.erase r, ε u * W u| := hrev
  rw [hsum_eq]
  have hfin : (1:ℝ) ≤ (2:ℝ)^(lab r) - ∑ u ∈ T.erase r, W u := by linarith [hGB]
  linarith [hmain, hfin]
  /- @proof-region region.target-node.session.341cbdd2b4a8a4d8 end -/

end LiuBangXiangYu
