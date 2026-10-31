import ProverJobs.job_paper_c93669ef201447419b92d6591d8bc1aa.Vocabulary
import ProverJobs.job_paper_c93669ef201447419b92d6591d8bc1aa.Base
import ProverJobs.job_paper_c93669ef201447419b92d6591d8bc1aa.ProvedNodes.Node_4114883645_8b1ad159_302c54f6
import ProverJobs.job_paper_c93669ef201447419b92d6591d8bc1aa.ProvedNodes.Node_834363190_4b893991_cf348327


open Statlib.Imported
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators

namespace Statlib.Imported
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators

set_option autoImplicit false in
theorem statopia_math_node_537990944_6d0e223c : ∀ (t : ℕ) (ht : 1 ≤ t)
    (c : ℝ) (hc : 0 < c)
    (θstar : Fin t → ℝ)
    (g : ℝ → ℝ)
    (Rg : ℝ) (hRg : 0 ≤ Rg)
    {Ω : Type} (X : ℕ → Ω → ℝ) (n : ℕ) (j : Fin t) (ω : Ω)
    (hnj : 1 ≤ windowCount X θstar c n j ω)
    (hUj : upperOrderStat X θstar c n j ω ≤ θstar j + c)
    (hint : ∀ i ∈ windowIdx X θstar c n j ω, X i ω - θstar j ∈ Set.Ioo (-c) c)
    (m M : ℝ) (hm : 0 < m) (hM : 0 < M)
    (hT1 : ∀ y ∈ Set.Icc (-c) c, m ≤ g y ∧ g y ≤ M)
    (hT2diff : DifferentiableOn ℝ g (Set.Ioo (-c) c))
    (hT2 : ∀ y ∈ Set.Ioo (-c) c, |deriv g y / g y| ≤ Rg),
    (∀ θ : ℝ,
        θstar j - min (c + θstar j - upperOrderStat X θstar c n j ω)
            (1 / ((windowCount X θstar c n j ω : ℕ) : ℝ)) < θ →
        θ ≤ θstar j →
        (∏ i ∈ windowIdx X θstar c n j ω, g (X i ω - θ) / g (X i ω - θstar j))
          ≥ Real.exp (-Rg)) ∧
    (∀ θ : ℝ,
        θ ∈ Set.Ioo (θstar j - min (c + θstar j - upperOrderStat X θstar c n j ω)
            (1 / ((windowCount X θstar c n j ω : ℕ) : ℝ))) (θstar j) ∪ {θstar j} →
        (∏ i ∈ windowIdx X θstar c n j ω, g (X i ω - θ) / g (X i ω - θstar j))
          ≥ Real.exp (-Rg)) := by
  /- @proof-region region.target-node.session.02ac7f151d04805d begin -/
  intro t ht c hc θstar g Rg hRg Ω X n j ω hnj hUj hint m M hm hM hT1 hT2diff hT2
  obtain ⟨_, hwin, _, _, hsm⟩ :=
    statopia_math_node_834363190_4b893991 t ht c hc θstar X n j ω hnj
  obtain ⟨_, _, hsA, _, hnsle⟩ := hsm
  have hgpos : ∀ y ∈ Set.Ioo (-c) c, 0 < g y := by
    intro y hy
    have h1 := (hT1 y (Set.Ioo_subset_Icc_self hy)).1
    linarith
  have hderivLog : ∀ y ∈ Set.Ioo (-c) c,
      HasDerivAt (fun z => Real.log (g z)) (deriv g y / g y) y := by
    intro y hy
    have hd : DifferentiableAt ℝ g y :=
      hT2diff.differentiableAt (isOpen_Ioo.mem_nhds hy)
    have hne : g y ≠ 0 := ne_of_gt (hgpos y hy)
    exact hd.hasDerivAt.log hne
  have hderivLog_eq : ∀ y ∈ Set.Ioo (-c) c,
      deriv (fun z => Real.log (g z)) y = deriv g y / g y := by
    intro y hy
    exact (hderivLog y hy).deriv
  have hLipschitz : ∀ y ∈ Set.Ioo (-c) c, ∀ y' ∈ Set.Ioo (-c) c,
      |Real.log (g y) - Real.log (g y')| ≤ Rg * |y - y'| := by
    intro y hy y' hy'
    have hbound : ∀ z ∈ Set.Ioo (-c) c, ‖deriv (fun w => Real.log (g w)) z‖ ≤ Rg := by
      intro z hz
      rw [hderivLog_eq z hz, Real.norm_eq_abs]
      exact hT2 z hz
    have hdiff : ∀ z ∈ Set.Ioo (-c) c, DifferentiableAt ℝ (fun w => Real.log (g w)) z :=
      fun z hz => (hderivLog z hz).differentiableAt
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (s := Set.Ioo (-c) c) (f := fun w => Real.log (g w)) (C := Rg)
      hdiff hbound (convex_Ioo (-c) c) hy' hy
    simpa only [Real.norm_eq_abs] using h
  have hbdd : BddAbove ((fun i => X i ω) '' ((windowIdx X θstar c n j ω : Finset ℕ) : Set ℕ)) := by
    refine ⟨θstar j + c, ?_⟩
    rintro z ⟨i, hi, rfl⟩
    exact (hwin i (Finset.mem_coe.mp hi)).2.1
  have hleUj : ∀ i ∈ windowIdx X θstar c n j ω,
      X i ω ≤ upperOrderStat X θstar c n j ω := by
    intro i hi
    exact le_csSup hbdd ⟨i, Finset.mem_coe.mpr hi, rfl⟩
  have key : ∀ θ : ℝ,
      θstar j - min (c + θstar j - upperOrderStat X θstar c n j ω)
          (1 / ((windowCount X θstar c n j ω : ℕ) : ℝ)) < θ →
      θ ≤ θstar j →
      (∏ i ∈ windowIdx X θstar c n j ω, g (X i ω - θ) / g (X i ω - θstar j))
        ≥ Real.exp (-Rg) := by
    intro θ hθ1 hθ2
    have hd0 : 0 ≤ θstar j - θ := by linarith
    have hds : θstar j - θ ≤ min (c + θstar j - upperOrderStat X θstar c n j ω)
        (1 / ((windowCount X θstar c n j ω : ℕ) : ℝ)) := by linarith
    have hy_int : ∀ i ∈ windowIdx X θstar c n j ω, X i ω - θ ∈ Set.Ioo (-c) c := by
      intro i hi
      have hi' := hint i hi
      have hle : X i ω ≤ upperOrderStat X θstar c n j ω := hleUj i hi
      have hhigh : X i ω - θ < c := by
        have h2 : upperOrderStat X θstar c n j ω - c < θ := by linarith
        linarith
      exact ⟨by linarith [hi'.1], hhigh⟩
    have hfactor : ∀ i ∈ windowIdx X θstar c n j ω,
        Real.exp (-(Rg * (θstar j - θ))) ≤ g (X i ω - θ) / g (X i ω - θstar j) := by
      intro i hi
      have hy : X i ω - θ ∈ Set.Ioo (-c) c := hy_int i hi
      have hy' : X i ω - θstar j ∈ Set.Ioo (-c) c := hint i hi
      have hpos : 0 < g (X i ω - θ) := hgpos _ hy
      have hpos' : 0 < g (X i ω - θstar j) := hgpos _ hy'
      have hdabs : |(X i ω - θ) - (X i ω - θstar j)| = θstar j - θ := by
        rw [show (X i ω - θ) - (X i ω - θstar j) = θstar j - θ by ring, abs_of_nonneg hd0]
      have hl := hLipschitz (X i ω - θ) hy (X i ω - θstar j) hy'
      rw [hdabs] at hl
      have hlog : -(Rg * (θstar j - θ)) ≤
          Real.log (g (X i ω - θ)) - Real.log (g (X i ω - θstar j)) := (abs_le.mp hl).1
      calc Real.exp (-(Rg * (θstar j - θ)))
          ≤ Real.exp (Real.log (g (X i ω - θ)) - Real.log (g (X i ω - θstar j))) :=
            Real.exp_le_exp.mpr hlog
        _ = g (X i ω - θ) / g (X i ω - θstar j) := by
            rw [Real.exp_sub, Real.exp_log hpos, Real.exp_log hpos']
    have hprod : (∏ i ∈ windowIdx X θstar c n j ω, Real.exp (-(Rg * (θstar j - θ))))
        ≤ ∏ i ∈ windowIdx X θstar c n j ω, g (X i ω - θ) / g (X i ω - θstar j) :=
      Finset.prod_le_prod (fun i _ => (Real.exp_pos _).le) hfactor
    have hconst : (∏ i ∈ windowIdx X θstar c n j ω, Real.exp (-(Rg * (θstar j - θ))))
        = Real.exp ((windowCount X θstar c n j ω : ℝ) * (-(Rg * (θstar j - θ)))) := by
      rw [Finset.prod_const, windowCount, ← Real.exp_nat_mul]
    have hnj0 : (0 : ℝ) ≤ (windowCount X θstar c n j ω : ℝ) := Nat.cast_nonneg _
    have hnd : (windowCount X θstar c n j ω : ℝ) * (θstar j - θ) ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hds hnj0
      linarith
    have hexp : Real.exp (-Rg)
        ≤ Real.exp ((windowCount X θstar c n j ω : ℝ) * (-(Rg * (θstar j - θ)))) := by
      have h1 : (windowCount X θstar c n j ω : ℝ) * (-(Rg * (θstar j - θ)))
          = -((windowCount X θstar c n j ω : ℝ) * (Rg * (θstar j - θ))) := by ring
      have h2 : (windowCount X θstar c n j ω : ℝ) * (Rg * (θstar j - θ))
          = Rg * ((windowCount X θstar c n j ω : ℝ) * (θstar j - θ)) := by ring
      have h3 : (windowCount X θstar c n j ω : ℝ) * (Rg * (θstar j - θ)) ≤ Rg := by
        rw [h2]
        calc Rg * ((windowCount X θstar c n j ω : ℝ) * (θstar j - θ)) ≤ Rg * 1 :=
              mul_le_mul_of_nonneg_left hnd hRg
          _ = Rg := by ring
      rw [h1]
      exact Real.exp_le_exp.mpr (by linarith)
    rw [hconst] at hprod
    exact le_trans hexp hprod
  constructor
  · exact key
  · intro θ hθ
    rw [Set.mem_union] at hθ
    rcases hθ with h | h
    · exact key θ h.1 (le_of_lt h.2)
    · rw [Set.mem_singleton_iff] at h
      rw [h]
      have hone : (∏ i ∈ windowIdx X θstar c n j ω,
          g (X i ω - θstar j) / g (X i ω - θstar j)) = 1 := by
        refine Finset.prod_eq_one (fun i hi => ?_)
        exact div_self (ne_of_gt (hgpos _ (hint i hi)))
      rw [hone]
      simpa using Real.exp_le_exp.mpr (show -Rg ≤ 0 by linarith)
  /- @proof-region region.target-node.session.02ac7f151d04805d end -/

end Statlib.Imported
