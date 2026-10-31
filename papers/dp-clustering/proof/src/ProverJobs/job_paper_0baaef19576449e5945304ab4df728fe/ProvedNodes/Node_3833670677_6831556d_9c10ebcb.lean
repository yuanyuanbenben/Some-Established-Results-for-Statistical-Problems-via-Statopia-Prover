import ProverJobs.job_paper_0baaef19576449e5945304ab4df728fe.Vocabulary
import ProverJobs.job_paper_0baaef19576449e5945304ab4df728fe.Base

open Set
open scoped BigOperators
open Statlib.Imported

open Set
open scoped BigOperators
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_3833670677_6831556d : ∀ (c : ℝ) (hc : 0 < c)
    (g : ℝ → ℝ)
    (m : ℝ) (hm : 0 < m)
    (hg_lower : ∀ y : ℝ, y ∈ Set.Icc (-c) c → m ≤ g y)
    (hg_diff : DifferentiableOn ℝ g (Set.Ioo (-c) c))
    (R : ℝ) (hR : ∀ y : ℝ, y ∈ Set.Ioo (-c) c → |deriv g y / g y| ≤ R)
    (pt : ℝ → ℝ) (hpt_cont : ContinuousOn pt (Set.Icc (-c) c))
    (hpt_eq : ∀ y : ℝ, y ∈ Set.Ioo (-c) c → pt y = Real.log (g y))
    (a : ℝ) (ha : a ∈ Set.Icc (-c) c)
    (b : ℝ) (hb : b ∈ Set.Icc (-c) c),
    |pt b - pt a| ≤ R * |b - a| := by
  /- @proof-region region.target-node.session.b72c2c359077b359 begin -/
  intro c hc g m hm hg_lower hg_diff R hR pt hpt_cont hpt_eq a ha b hb
  have hne : -c ≠ c := by intro h; linarith
  have hsub : Set.Ioo (-c) c ⊆ Set.Icc (-c) c := fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hpos : ∀ y : ℝ, y ∈ Set.Ioo (-c) c → 0 < g y := by
    intro y hy
    exact lt_of_lt_of_le hm (hg_lower y (hsub hy))
  have hderiv : ∀ y : ℝ, y ∈ Set.Ioo (-c) c →
      HasDerivWithinAt pt (deriv g y / g y) (Set.Ioo (-c) c) y := by
    intro y hy
    have hy_nhds : Set.Ioo (-c) c ∈ nhds y := Ioo_mem_nhds hy.1 hy.2
    have hg_at : HasDerivAt g (deriv g y) y := hg_diff.hasDerivAt hy_nhds
    have hgy : g y ≠ 0 := ne_of_gt (hpos y hy)
    have hlog : HasDerivAt (fun z => Real.log (g z)) ((g y)⁻¹ * deriv g y) y :=
      (Real.hasDerivAt_log hgy).comp y hg_at
    have hlog' : HasDerivAt (fun z => Real.log (g z)) (deriv g y / g y) y := by
      rw [div_eq_inv_mul]
      exact hlog
    have heq : pt =ᶠ[nhds y] (fun z => Real.log (g z)) := by
      filter_upwards [hy_nhds] with z hz using hpt_eq z hz
    exact (hlog'.congr_of_eventuallyEq heq).hasDerivWithinAt
  have hstep3 : ∀ x : ℝ, x ∈ Set.Ioo (-c) c → ∀ y : ℝ, y ∈ Set.Ioo (-c) c →
      |pt y - pt x| ≤ R * |y - x| := by
    intro x hx y hy
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := pt)
      (f' := fun z => deriv g z / g z) (s := Set.Ioo (-c) c) (x := x) (y := y) (C := R)
      hderiv (fun z hz => by
        rw [Real.norm_eq_abs]
        exact hR z hz) (convex_Ioo (-c) c) hx hy
    simpa [Real.norm_eq_abs] using h
  have hcontφ : ∀ u : ℝ,
      ContinuousOn (fun x : ℝ => R * |x - u| - |pt x - pt u|) (Set.Icc (-c) c) := by
    intro u
    exact (continuous_const.continuousOn.mul
      ((continuous_id.continuousOn.sub continuous_const.continuousOn).abs)).sub
      ((hpt_cont.sub continuous_const.continuousOn).abs)
  have round1 : ∀ a' : ℝ, a' ∈ Set.Ioo (-c) c → ∀ b' : ℝ, b' ∈ Set.Icc (-c) c →
      0 ≤ R * |b' - a'| - |pt b' - pt a'| := by
    intro a' ha' b' hb'
    have hb_clos : b' ∈ closure (Set.Ioo (-c) c) := by
      rw [closure_Ioo hne]
      exact hb'
    haveI : Filter.NeBot (nhdsWithin b' (Set.Ioo (-c) c)) :=
      mem_closure_iff_nhdsWithin_neBot.mp hb_clos
    have hlim : Filter.Tendsto (fun x : ℝ => R * |x - a'| - |pt x - pt a'|)
        (nhdsWithin b' (Set.Ioo (-c) c)) (nhds (R * |b' - a'| - |pt b' - pt a'|)) :=
      (hcontφ a' b' hb').mono hsub
    have hle : Filter.EventuallyLE (nhdsWithin b' (Set.Ioo (-c) c)) (fun _ : ℝ => (0:ℝ))
        (fun x : ℝ => R * |x - a'| - |pt x - pt a'|) := by
      filter_upwards [self_mem_nhdsWithin] with x hx using sub_nonneg.mpr (hstep3 a' ha' x hx)
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim hle
  have round2 : ∀ a' : ℝ, a' ∈ Set.Icc (-c) c → ∀ b' : ℝ, b' ∈ Set.Icc (-c) c →
      0 ≤ R * |b' - a'| - |pt b' - pt a'| := by
    intro a' ha' b' hb'
    have ha_clos : a' ∈ closure (Set.Ioo (-c) c) := by
      rw [closure_Ioo hne]
      exact ha'
    haveI : Filter.NeBot (nhdsWithin a' (Set.Ioo (-c) c)) :=
      mem_closure_iff_nhdsWithin_neBot.mp ha_clos
    have hlim : Filter.Tendsto (fun x : ℝ => R * |x - b'| - |pt x - pt b'|)
        (nhdsWithin a' (Set.Ioo (-c) c)) (nhds (R * |a' - b'| - |pt a' - pt b'|)) :=
      (hcontφ b' a' ha').mono hsub
    have hle : Filter.EventuallyLE (nhdsWithin a' (Set.Ioo (-c) c)) (fun _ : ℝ => (0:ℝ))
        (fun x : ℝ => R * |x - b'| - |pt x - pt b'|) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have h := round1 x hx b' hb'
      rwa [abs_sub_comm b' x, abs_sub_comm (pt b') (pt x)] at h
    have h0 : 0 ≤ R * |a' - b'| - |pt a' - pt b'| :=
      le_of_tendsto_of_tendsto tendsto_const_nhds hlim hle
    rwa [abs_sub_comm a' b', abs_sub_comm (pt a') (pt b')] at h0
  linarith [round2 a ha b hb]
  /- @proof-region region.target-node.session.b72c2c359077b359 end -/

end Statlib.Imported
