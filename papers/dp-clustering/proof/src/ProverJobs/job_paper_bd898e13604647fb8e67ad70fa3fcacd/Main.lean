import ProverJobs.job_paper_bd898e13604647fb8e67ad70fa3fcacd.Vocabulary
import ProverJobs.job_paper_bd898e13604647fb8e67ad70fa3fcacd.ProvedNodes
import ProverJobs.job_paper_bd898e13604647fb8e67ad70fa3fcacd.Base

namespace Statlib.Imported

theorem paper_bd898e13604647fb8e67ad70fa3fcacd
    (t : ℕ) (ht : 0 < t) (p : Fin t → ℝ) (n : Fin t → ℕ) (s : ℕ)
    (hp_pos : ∀ j, 0 < p j) (hp_lt : ∀ j, p j < 1) (hp_sum : ∑ j, p j = 1) :
    ((Fintype.piFinset (fun _ : Fin t => Finset.range (s + 1))).filter
        (fun sv : Fin t → ℕ => (∀ j, sv j ≤ n j) ∧ ∑ j, sv j = s)).sum
        (fun sv : Fin t → ℕ => (s.factorial : ℝ) / ∏ j, ((sv j).factorial : ℝ))
      ≤ ((Finset.univ.inf' ⟨⟨0, ht⟩, Finset.mem_univ (⟨0, ht⟩ : Fin t)⟩ p)⁻¹) ^ s
:= by
  /- @proof-region region.root.85454ee8f8d9 begin -/
  set pstar : ℝ := (Finset.univ : Finset (Fin t)).inf' ⟨⟨0, ht⟩, Finset.mem_univ (⟨0, ht⟩ : Fin t)⟩ p with hpstar
  let K : Finset (Fin t → ℕ) := Fintype.piFinset (fun _ : Fin t => Finset.range (s + 1))
  let T : Finset (Fin t → ℕ) := K.filter (fun sv => ∑ j, sv j = s)
  set S : Finset (Fin t → ℕ) :=
    (Fintype.piFinset (fun _ : Fin t => Finset.range (s + 1))).filter
      (fun sv : Fin t → ℕ => (∀ j, sv j ≤ n j) ∧ ∑ j, sv j = s) with hS
  let X : (Fin t → ℕ) → ℝ := fun sv => (s.factorial : ℝ) / ∏ j, ((sv j).factorial : ℝ)
  let P : (Fin t → ℕ) → ℝ := fun sv => ∏ j, (p j) ^ (sv j)
  have hpstar_pos : 0 < pstar := by
    rw [hpstar, Finset.lt_inf'_iff]
    intro i _
    exact hp_pos i
  have hpstar_le : ∀ j : Fin t, pstar ≤ p j := by
    intro j
    rw [hpstar]
    exact Finset.inf'_le p (Finset.mem_univ j)
  have hX_nonneg : ∀ sv : Fin t → ℕ, 0 ≤ X sv := by
    intro sv
    exact div_nonneg (by positivity) (Finset.prod_nonneg (fun j _ => by positivity))
  have hP_nonneg : ∀ sv : Fin t → ℕ, 0 ≤ P sv := by
    intro sv
    exact Finset.prod_nonneg (fun j _ => pow_nonneg (le_of_lt (hp_pos j)) _)
  have hbound : ∀ sv ∈ T, pstar ^ s ≤ P sv := by
    intro sv hsv
    have hsum : ∑ j, sv j = s := (Finset.mem_filter.mp hsv).2
    have hfactor : ∀ j : Fin t, pstar ^ (sv j) ≤ (p j) ^ (sv j) := by
      intro j
      have hpj : pstar ≤ p j := hpstar_le j
      have h0 : (0 : ℝ) ≤ pstar := le_of_lt hpstar_pos
      have h : ∀ k : ℕ, pstar ^ k ≤ (p j) ^ k := by
        intro k
        induction k with
        | zero => simp
        | succ m ih =>
            rw [pow_succ, pow_succ]
            exact mul_le_mul ih hpj h0 (pow_nonneg (le_of_lt (hp_pos j)) m)
      exact h (sv j)
    have hprod : ∏ j : Fin t, pstar ^ (sv j) ≤ P sv :=
      Finset.prod_le_prod (fun j _ => pow_nonneg (le_of_lt hpstar_pos) _) (fun j _ => hfactor j)
    calc pstar ^ s = ∏ j : Fin t, pstar ^ (sv j) := by
          rw [Finset.prod_pow_eq_pow_sum, hsum]
      _ ≤ P sv := hprod
  have hkey : ∀ sv ∈ T, 1 ≤ (pstar⁻¹) ^ s * P sv := by
    intro sv hsv
    have hP := hbound sv hsv
    have h1 : (pstar⁻¹) ^ s * pstar ^ s = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt hpstar_pos), one_pow]
    have h2 : (pstar⁻¹) ^ s * pstar ^ s ≤ (pstar⁻¹) ^ s * P sv :=
      mul_le_mul_of_nonneg_left hP (pow_nonneg (inv_nonneg.mpr (le_of_lt hpstar_pos)) s)
    rwa [h1] at h2
  have hterm : ∀ sv ∈ T, X sv ≤ (pstar⁻¹) ^ s * (X sv * P sv) := by
    intro sv hsv
    have h1 := hkey sv hsv
    have h2 : X sv * 1 ≤ X sv * ((pstar⁻¹) ^ s * P sv) :=
      mul_le_mul_of_nonneg_left h1 (hX_nonneg sv)
    calc X sv = X sv * 1 := (mul_one (X sv)).symm
      _ ≤ X sv * ((pstar⁻¹) ^ s * P sv) := h2
      _ = (pstar⁻¹) ^ s * (X sv * P sv) := by ring
  have hST : S ⊆ T := by
    intro sv hsv
    have h := Finset.mem_filter.mp hsv
    exact Finset.mem_filter.mpr ⟨h.1, h.2.2⟩
  have hstep1 : S.sum X ≤ S.sum (fun sv => (pstar⁻¹) ^ s * (X sv * P sv)) :=
    Finset.sum_le_sum (fun sv hsv => hterm sv (hST hsv))
  have hstep2 : S.sum (fun sv => (pstar⁻¹) ^ s * (X sv * P sv))
      = (pstar⁻¹) ^ s * S.sum (fun sv => X sv * P sv) := by
    rw [Finset.mul_sum]
  have hstep3 : S.sum (fun sv => X sv * P sv) ≤ T.sum (fun sv => X sv * P sv) :=
    Finset.sum_le_sum_of_subset_of_nonneg hST
      (fun sv _ _ => mul_nonneg (hX_nonneg sv) (hP_nonneg sv))
  have hmass : T.sum (fun sv => X sv * P sv) = (∑ j, p j) ^ s :=
    statopia_math_node_360176551_1d2728fd t s p
  have hmass1 : T.sum (fun sv => X sv * P sv) = 1 := by
    rw [hmass, hp_sum, one_pow]
  have hfinal : S.sum X ≤ (pstar⁻¹) ^ s := by
    calc S.sum X
        ≤ S.sum (fun sv => (pstar⁻¹) ^ s * (X sv * P sv)) := hstep1
      _ = (pstar⁻¹) ^ s * S.sum (fun sv => X sv * P sv) := hstep2
      _ ≤ (pstar⁻¹) ^ s * T.sum (fun sv => X sv * P sv) :=
          mul_le_mul_of_nonneg_left hstep3 (pow_nonneg (inv_nonneg.mpr (le_of_lt hpstar_pos)) s)
      _ = (pstar⁻¹) ^ s * 1 := by rw [hmass1]
      _ = (pstar⁻¹) ^ s := mul_one _
  exact hfinal
  /- @proof-region region.root.85454ee8f8d9 end -/

end Statlib.Imported
