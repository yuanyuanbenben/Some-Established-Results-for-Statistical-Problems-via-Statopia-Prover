import ProverJobs.job_paper_0baaef19576449e5945304ab4df728fe.Vocabulary
import ProverJobs.job_paper_0baaef19576449e5945304ab4df728fe.ProvedNodes
import ProverJobs.job_paper_0baaef19576449e5945304ab4df728fe.Base

open Set
open scoped BigOperators
namespace Statlib.Imported

theorem paper_0baaef19576449e5945304ab4df728fe
    (c : ℝ) (hc : 0 < c)
    (g : ℝ → ℝ) (hg_nonneg : ∀ y : ℝ, 0 ≤ g y)
    (m M : ℝ) (hm : 0 < m) (hmM : m ≤ M)
    (hg_lower : ∀ y : ℝ, y ∈ Set.Icc (-c) c → m ≤ g y)
    (hg_upper : ∀ y : ℝ, y ∈ Set.Icc (-c) c → g y ≤ M)
    (hg_diff : DifferentiableOn ℝ g (Set.Ioo (-c) c))
    (R : ℝ) (hR : ∀ y : ℝ, y ∈ Set.Ioo (-c) c → |deriv g y / g y| ≤ R)
    (pt : ℝ → ℝ) (hpt_cont : ContinuousOn pt (Set.Icc (-c) c))
    (hpt_eq : ∀ y : ℝ, y ∈ Set.Ioo (-c) c → pt y = Real.log (g y))
    (n : ℕ) (x : Fin n → ℝ) :
    (let Cj : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => x i ∈ Set.Icc (-c) c)
     let nj : ℕ := Cj.card
     ∀ (hne : Cj.Nonempty) (θ : ℝ),
       (∏ i ∈ Cj, Real.exp (pt (x i - θ)) / Real.exp (pt (x i)))
         ≥ Real.exp (-R)
             * (if |θ| ≤ ((nj : ℝ))⁻¹ then (1 : ℝ) else 0)
             * (if θ ∈ Set.Icc (Cj.sup' hne (fun i : Fin n => x i) - c)
                            (Cj.inf' hne (fun i : Fin n => x i) + c)
                then (1 : ℝ) else 0))
:= by
  /- @proof-region region.root.7fed8bd78ee9 begin -/
  dsimp only
  intro hne θ
  set Cj : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => x i ∈ Set.Icc (-c) c) with hCj
  have hR0 : 0 ≤ R := by
    have hy : (0 : ℝ) ∈ Set.Ioo (-c) c := ⟨by linarith, hc⟩
    exact le_trans (abs_nonneg _) (hR 0 hy)
  have hprod_nonneg : (0 : ℝ) ≤ ∏ i ∈ Cj, Real.exp (pt (x i - θ)) / Real.exp (pt (x i)) := by
    apply Finset.prod_nonneg
    intro i hi
    exact div_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _))
  by_cases h1 : (|θ| ≤ ((Cj.card : ℝ))⁻¹)
  · by_cases h2 : θ ∈ Set.Icc (Cj.sup' hne (fun i : Fin n => x i) - c)
      (Cj.inf' hne (fun i : Fin n => x i) + c)
    · rw [if_pos h1, if_pos h2, mul_one, mul_one]
      have h2a : Cj.sup' hne (fun i : Fin n => x i) - c ≤ θ := (Set.mem_Icc.mp h2).1
      have h2b : θ ≤ Cj.inf' hne (fun i : Fin n => x i) + c := (Set.mem_Icc.mp h2).2
      have hxCj : ∀ i ∈ Cj, x i ∈ Set.Icc (-c) c := by
        intro i hi
        simp only [hCj, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact hi
      have hxi : ∀ i ∈ Cj, x i - θ ∈ Set.Icc (-c) c := by
        intro i hi
        have hsup : x i ≤ Cj.sup' hne (fun i : Fin n => x i) :=
          Finset.le_sup' (fun i : Fin n => x i) hi
        have hinf : Cj.inf' hne (fun i : Fin n => x i) ≤ x i :=
          Finset.inf'_le (fun i : Fin n => x i) hi
        refine Set.mem_Icc.mpr ⟨?_, ?_⟩
        · linarith
        · linarith
      have hbound : ∀ i ∈ Cj, -(R * |θ|) ≤ pt (x i - θ) - pt (x i) := by
        intro i hi
        have hlip := statopia_math_node_3833670677_6831556d c hc g m hm hg_lower hg_diff R hR
          pt hpt_cont hpt_eq (x i) (hxCj i hi) (x i - θ) (hxi i hi)
        have hb : |pt (x i - θ) - pt (x i)| ≤ R * |θ| := by
          have hsub : (x i - θ) - x i = -θ := by ring
          simpa only [hsub, abs_neg] using hlip
        exact (abs_le.mp hb).1
      have hsum_le : (∑ i ∈ Cj, (-(R * |θ|))) ≤ ∑ i ∈ Cj, (pt (x i - θ) - pt (x i)) :=
        Finset.sum_le_sum hbound
      have hsumconst : (∑ i ∈ Cj, (-(R * |θ|))) = -((Cj.card : ℝ) * (R * |θ|)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
      have hcardpos : (0 : ℝ) < (Cj.card : ℝ) := by
        exact_mod_cast (Finset.card_pos.mpr hne)
      have hnj_ne : (Cj.card : ℝ) ≠ 0 := ne_of_gt hcardpos
      have hmul_le : (Cj.card : ℝ) * |θ| ≤ 1 := by
        calc (Cj.card : ℝ) * |θ| ≤ (Cj.card : ℝ) * ((Cj.card : ℝ))⁻¹ :=
              mul_le_mul_of_nonneg_left h1 (le_of_lt hcardpos)
          _ = 1 := mul_inv_cancel₀ hnj_ne
      have hRle : (Cj.card : ℝ) * (R * |θ|) ≤ R := by
        have hstep : R * ((Cj.card : ℝ) * |θ|) ≤ R * 1 :=
          mul_le_mul_of_nonneg_left hmul_le hR0
        calc (Cj.card : ℝ) * (R * |θ|) = R * ((Cj.card : ℝ) * |θ|) := by ring
          _ ≤ R * 1 := hstep
          _ = R := mul_one R
      have hsumR : -R ≤ ∑ i ∈ Cj, (pt (x i - θ) - pt (x i)) := by
        have hle1 : -((Cj.card : ℝ) * (R * |θ|)) ≤
            ∑ i ∈ Cj, (pt (x i - θ) - pt (x i)) := by
          rw [← hsumconst]
          exact hsum_le
        linarith
      calc ∏ i ∈ Cj, Real.exp (pt (x i - θ)) / Real.exp (pt (x i))
          = ∏ i ∈ Cj, Real.exp (pt (x i - θ) - pt (x i)) := by
            refine Finset.prod_congr rfl (fun i hi => ?_)
            exact (Real.exp_sub (pt (x i - θ)) (pt (x i))).symm
        _ = Real.exp (∑ i ∈ Cj, (pt (x i - θ) - pt (x i))) := by
            rw [Real.exp_sum]
        _ ≥ Real.exp (-R) := Real.exp_le_exp.mpr hsumR
    · rw [if_neg h2, mul_zero]
      exact hprod_nonneg
  · rw [if_neg h1, mul_zero, zero_mul]
    exact hprod_nonneg
  /- @proof-region region.root.7fed8bd78ee9 end -/

end Statlib.Imported
