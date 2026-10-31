import ProverJobs.job_paper_a2bb64c47d4d486d8be39815258273b1.Vocabulary
import ProverJobs.job_paper_a2bb64c47d4d486d8be39815258273b1.ProvedNodes
import ProverJobs.job_paper_a2bb64c47d4d486d8be39815258273b1.Base

open MeasureTheory
open Classical
namespace Statlib.Imported

theorem paper_a2bb64c47d4d486d8be39815258273b1
    (t : ℕ) (ht : 1 ≤ t) (c : ℝ) (hc : 0 < c)
    (g : ℝ → ℝ) (theta_star : Fin t → ℝ) (R : ℝ)
    
    (hT1 : ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ y ∈ Set.Icc (-c) c, m ≤ g y ∧ g y ≤ M)
    
    (hT2_diff : DifferentiableOn ℝ g (Set.Ioo (-c) c))
    
    (hT2_bound : ∀ y ∈ Set.Ioo (-c) c, |deriv g y / g y| ≤ R)
    
    (h_end : ContinuousWithinAt g (Set.Iic c) c ∧ ContinuousWithinAt g (Set.Ici (-c)) (-c))
    
    (hg_nonneg : ∀ y : ℝ, 0 ≤ g y)
    (j : Fin t) (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ)
    
    (S : Finset (Fin n)) (hne : S.Nonempty)
    (hS : S = Finset.univ.filter
      (fun i => x i ∈ Set.Icc (theta_star j - c) (theta_star j + c))) :
    ∀ theta : ℝ,
      Real.exp (-R)
          * Set.indicator (Set.Icc (0 : ℝ) (1 / (S.card : ℝ))) (fun _ => (1 : ℝ))
              |theta - theta_star j|
          * Set.indicator
              (Set.Icc ((S.image x).max' (hne.image x) - c)
                ((S.image x).min' (hne.image x) + c))
              (fun _ => (1 : ℝ)) theta
        ≤ Finset.prod S (fun i => g (x i - theta) / g (x i - theta_star j))
:= by
  /- @proof-region region.root.fca8c8000894 begin -/
  intro theta
  obtain ⟨m, M, hm, hM, hb⟩ := hT1
  have hm_pos : ∀ y ∈ Set.Icc (-c) c, 0 < g y := fun y hy => lt_of_lt_of_le hm (hb y hy).1
  have hR : 0 ≤ R := (abs_nonneg (deriv g 0 / g 0)).trans (hT2_bound 0 ⟨by linarith, hc⟩)
  have hcard : 0 < S.card := Finset.card_pos.mpr hne
  have hcardR : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hcard
  have hmemS : ∀ i ∈ S, x i ∈ Set.Icc (theta_star j - c) (theta_star j + c) := by
    intro i hi
    have h : i ∈ Finset.univ.filter
        (fun i => x i ∈ Set.Icc (theta_star j - c) (theta_star j + c)) := hS ▸ hi
    exact (Finset.mem_filter.mp h).2
  have hy : ∀ i ∈ S, x i - theta_star j ∈ Set.Icc (-c) c := by
    intro i hi
    obtain ⟨h1, h2⟩ := hmemS i hi
    exact ⟨by linarith, by linarith⟩
  have hnonneg : ∀ i ∈ S, 0 ≤ g (x i - theta) / g (x i - theta_star j) := by
    intro i hi
    exact div_nonneg (hg_nonneg _) (le_of_lt (hm_pos _ (hy i hi)))
  have hprod_nonneg : 0 ≤ Finset.prod S (fun i => g (x i - theta) / g (x i - theta_star j)) :=
    Finset.prod_nonneg hnonneg
  by_cases hwin : theta ∈
      Set.Icc ((S.image x).max' (hne.image x) - c) ((S.image x).min' (hne.image x) + c)
  · have hmax : ∀ i ∈ S, x i ≤ (S.image x).max' (hne.image x) := by
      intro i hi
      exact Finset.le_max' (S.image x) (x i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    have hmin : ∀ i ∈ S, (S.image x).min' (hne.image x) ≤ x i := by
      intro i hi
      exact Finset.min'_le (S.image x) (x i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    have hz : ∀ i ∈ S, x i - theta ∈ Set.Icc (-c) c := by
      intro i hi
      have hle := hmax i hi
      have hge := hmin i hi
      exact ⟨by linarith [hwin.2, hge], by linarith [hwin.1, hle]⟩
    have hfactor : ∀ i ∈ S,
        Real.exp (-(R * |theta - theta_star j|)) ≤ g (x i - theta) / g (x i - theta_star j) := by
      intro i hi
      have hu := hz i hi
      have hv := hy i hi
      have hlip := statopia_math_node_3719821444_17db7983 c hc g R hm_pos hT2_diff
        hT2_bound h_end.1 h_end.2 (x i - theta) hu (x i - theta_star j) hv
      have hshift : (x i - theta) - (x i - theta_star j) = -(theta - theta_star j) := by ring
      have hkey : -(R * |theta - theta_star j|)
          ≤ Real.log (g (x i - theta)) - Real.log (g (x i - theta_star j)) := by
        have h1 := (abs_le.mp hlip).1
        simpa only [hshift, abs_neg] using h1
      have hexple : Real.exp (-(R * |theta - theta_star j|))
          ≤ Real.exp (Real.log (g (x i - theta)) - Real.log (g (x i - theta_star j))) :=
        Real.exp_le_exp.mpr hkey
      rwa [Real.exp_sub, Real.exp_log (hm_pos (x i - theta) hu),
        Real.exp_log (hm_pos (x i - theta_star j) hv)] at hexple
    have hprod_le : Finset.prod S (fun i => Real.exp (-(R * |theta - theta_star j|)))
        ≤ Finset.prod S (fun i => g (x i - theta) / g (x i - theta_star j)) :=
      Finset.prod_le_prod (fun i hi => (Real.exp_pos _).le) hfactor
    have hpow : Finset.prod S (fun i => Real.exp (-(R * |theta - theta_star j|)))
        = Real.exp (-(R * (S.card : ℝ) * |theta - theta_star j|)) := by
      rw [Finset.prod_const]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hprod : Real.exp (-(R * (S.card : ℝ) * |theta - theta_star j|))
        ≤ Finset.prod S (fun i => g (x i - theta) / g (x i - theta_star j)) := by
      rw [← hpow]
      exact hprod_le
    simp only [Set.indicator_of_mem (f := fun _ => (1 : ℝ)) hwin, mul_one]
    by_cases hind : |theta - theta_star j| ∈ Set.Icc (0 : ℝ) (1 / (S.card : ℝ))
    · simp only [Set.indicator_of_mem (f := fun _ => (1 : ℝ)) hind, mul_one]
      have hle1 : (S.card : ℝ) * |theta - theta_star j| ≤ 1 := by
        have hne0 : (S.card : ℝ) ≠ 0 := ne_of_gt hcardR
        have hmul : (S.card : ℝ) * (1 / (S.card : ℝ)) = 1 := by field_simp
        calc (S.card : ℝ) * |theta - theta_star j|
            ≤ (S.card : ℝ) * (1 / (S.card : ℝ)) :=
              mul_le_mul_of_nonneg_left hind.2 hcardR.le
          _ = 1 := hmul
      have hRle : R * (S.card : ℝ) * |theta - theta_star j| ≤ R := by
        calc R * (S.card : ℝ) * |theta - theta_star j|
            = R * ((S.card : ℝ) * |theta - theta_star j|) := by ring
          _ ≤ R * 1 := mul_le_mul_of_nonneg_left hle1 hR
          _ = R := mul_one R
      have hexpR : Real.exp (-R) ≤ Real.exp (-(R * (S.card : ℝ) * |theta - theta_star j|)) := by
        apply Real.exp_le_exp.mpr
        linarith [hRle]
      exact hexpR.trans hprod
    · simp only [Set.indicator_of_notMem (f := fun _ => (1 : ℝ)) hind, mul_zero]
      exact hprod_nonneg
  · simp only [Set.indicator_of_notMem (f := fun _ => (1 : ℝ)) hwin, mul_zero]
    exact hprod_nonneg
  /- @proof-region region.root.fca8c8000894 end -/

end Statlib.Imported
