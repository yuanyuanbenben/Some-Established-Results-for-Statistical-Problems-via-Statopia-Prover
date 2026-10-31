import ProverJobs.job_paper_a2bb64c47d4d486d8be39815258273b1.Vocabulary
import ProverJobs.job_paper_a2bb64c47d4d486d8be39815258273b1.Base

open MeasureTheory
open Classical
open Statlib.Imported

open MeasureTheory
open Classical
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_3719821444_17db7983 : ∀ (c : ℝ) (hc : 0 < c) (g : ℝ → ℝ) (R : ℝ)
    (hpos : ∀ y ∈ Set.Icc (-c) c, 0 < g y)
    (hdiff : DifferentiableOn ℝ g (Set.Ioo (-c) c))
    (hbound : ∀ y ∈ Set.Ioo (-c) c, |deriv g y / g y| ≤ R)
    (hleft : ContinuousWithinAt g (Set.Iic c) c)
    (hright : ContinuousWithinAt g (Set.Ici (-c)) (-c))
    (u : ℝ) (hu : u ∈ Set.Icc (-c) c)
    (v : ℝ) (hv : v ∈ Set.Icc (-c) c),
    |Real.log (g u) - Real.log (g v)| ≤ R * |u - v| := by
  /- @proof-region region.target-node.session.9ba3d17a05a9a3a6 begin -/
  intro c hc g R hpos hdiff hbound hleft hright u hu v hv
  let L : ℝ → ℝ := fun y => Real.log (g y)
  change |L u - L v| ≤ R * |u - v|
  have hdiffL : DifferentiableOn ℝ L (Set.Ioo (-c) c) := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    exact ((hdiff.differentiableAt (isOpen_Ioo.mem_nhds ⟨hx1, hx2⟩)).log
      (ne_of_gt (hpos x ⟨le_of_lt hx1, le_of_lt hx2⟩))).differentiableWithinAt
  have hderiv : ∀ y ∈ Set.Ioo (-c) c, |deriv L y| ≤ R := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    have hgd : DifferentiableAt ℝ g y :=
      hdiff.differentiableAt (isOpen_Ioo.mem_nhds ⟨hy1, hy2⟩)
    have hne : g y ≠ 0 := ne_of_gt (hpos y ⟨le_of_lt hy1, le_of_lt hy2⟩)
    have hhas : HasDerivAt L (deriv g y / g y) y := hgd.hasDerivAt.log hne
    rw [hhas.deriv]
    exact hbound y ⟨hy1, hy2⟩
  have hccont : ContinuousWithinAt L (Set.Icc (-c) c) c := by
    have hgc : g c ≠ 0 := ne_of_gt (hpos c ⟨by linarith, le_refl c⟩)
    exact (hleft.log hgc).mono Set.Icc_subset_Iic_self
  have hmccont : ContinuousWithinAt L (Set.Icc (-c) c) (-c) := by
    have hgmc : g (-c) ≠ 0 := ne_of_gt (hpos (-c) ⟨le_refl (-c), by linarith⟩)
    exact (hright.log hgmc).mono Set.Icc_subset_Ici_self
  have hcont : ContinuousOn L (Set.Icc (-c) c) := by
    intro x hx
    obtain ⟨h1, h2⟩ := hx
    rcases lt_or_eq_of_le h1 with hlt | heq
    · rcases lt_or_eq_of_le h2 with hlt2 | heq2
      · have hgd : DifferentiableAt ℝ g x :=
          hdiff.differentiableAt (isOpen_Ioo.mem_nhds ⟨hlt, hlt2⟩)
        have hne : g x ≠ 0 := ne_of_gt (hpos x ⟨le_of_lt hlt, le_of_lt hlt2⟩)
        exact (hgd.hasDerivAt.log hne).continuousAt.continuousWithinAt
      · exact heq2.symm ▸ hccont
    · exact heq ▸ hmccont
  have key : ∀ a b : ℝ, a ∈ Set.Icc (-c) c → b ∈ Set.Icc (-c) c → a < b →
      |L a - L b| ≤ R * |a - b| := by
    intro a b ha hb hab
    have hcontab : ContinuousOn L (Set.Icc a b) :=
      hcont.mono (fun y hy => ⟨le_trans ha.1 hy.1, le_trans hy.2 hb.2⟩)
    have hdiffab : DifferentiableOn ℝ L (Set.Ioo a b) :=
      hdiffL.mono (fun y hy => ⟨lt_of_le_of_lt ha.1 hy.1, lt_of_lt_of_le hy.2 hb.2⟩)
    obtain ⟨x, hx, hxd⟩ := exists_deriv_eq_slope L hab hcontab hdiffab
    have hsub : x ∈ Set.Ioo (-c) c :=
      ⟨lt_of_le_of_lt ha.1 hx.1, lt_of_lt_of_le hx.2 hb.2⟩
    have hbnd : |deriv L x| ≤ R := hderiv x hsub
    have habpos : (0 : ℝ) < b - a := by linarith
    have hkey : |L b - L a| = |deriv L x| * (b - a) := by
      have h1 : L b - L a = deriv L x * (b - a) := by
        rw [hxd]
        field_simp
      rw [h1, abs_mul, abs_of_pos habpos]
    calc |L a - L b| = |L b - L a| := abs_sub_comm (L a) (L b)
      _ = |deriv L x| * (b - a) := hkey
      _ ≤ R * (b - a) := mul_le_mul_of_nonneg_right hbnd (le_of_lt habpos)
      _ = R * |a - b| := by
          rw [abs_of_neg (by linarith : a - b < 0), neg_sub]
  rcases lt_trichotomy u v with huv | huv | huv
  · exact key u v hu hv huv
  · simp [huv]
  · have h := key v u hv hu huv
    calc |L u - L v| = |L v - L u| := abs_sub_comm (L u) (L v)
      _ ≤ R * |v - u| := h
      _ = R * |u - v| := by rw [abs_sub_comm]
  /- @proof-region region.target-node.session.9ba3d17a05a9a3a6 end -/

end Statlib.Imported
