import ProverJobs.manual_dp_cons_finish_20261031.Conditional
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.Base
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace ManualDPCons
open Statlib.Imported

lemma density_integrable_and_integral (f : ℝ → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hnorm : ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1) :
    Integrable f volume ∧ ∫ x, f x ∂volume = 1 := by
  have hi : Integrable f volume :=
    (lintegral_ofReal_ne_top_iff_integrable hf.aestronglyMeasurable (Eventually.of_forall hf0)).mp
      (by rw [hnorm]; exact ENNReal.one_ne_top)
  refine ⟨hi, ?_⟩
  have hh := ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hf0)
  rw [hnorm] at hh
  exact ENNReal.ofReal_eq_one.mp hh

/-- Finitely many source T4 neighborhoods give one strictly positive common radius. -/
lemma uniform_T4_radius {t : ℕ} (q0 : ℝ → ℝ) (theta : Fin t → ℝ) (L : ℝ)
    (hT4 : ∀ j, ∀ᶠ z in 𝓝 (theta j), L ≤ q0 z) :
    ∃ r : ℝ, 0 < r ∧ ∀ j z, |z-theta j| < r → L ≤ q0 z := by
  have hshift : ∀ j : Fin t, ∀ᶠ u in 𝓝 (0:ℝ), L ≤ q0 (theta j+u) := by
    intro j
    have hmap : Tendsto (fun u : ℝ => theta j+u) (𝓝 0) (𝓝 (theta j)) := by
      simpa using (continuous_const.add continuous_id).tendsto (0:ℝ)
    exact hmap.eventually (hT4 j)
  have hall : ∀ᶠ u in 𝓝 (0:ℝ), ∀ j : Fin t, L ≤ q0 (theta j+u) := eventually_all.mpr hshift
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨r,hr,?_⟩
  intro j z hz
  have h := hball (show dist (z-theta j) 0 < r by simpa only [Real.dist_eq, sub_zero] using hz) j
  convert h using 1 <;> congr 1 <;> ring

/-- Source B3 selects the translated q0 bound before any concentration prior is chosen. -/
def sourceTranslatedU (B : ℝ) : ℝ := 2 * max 1 B

lemma sourceTranslatedU_pos (B : ℝ) : 0 < sourceTranslatedU B := by dsimp [sourceTranslatedU]; positivity
lemma sourceTranslatedU_bound (q0 : ℝ → ℝ) (B : ℝ) (hB : ∀ x, q0 x ≤ B) {t : ℕ}
    (theta : Fin t → ℝ) :
    ∀ j y, q0 (theta j+y)+q0 (theta j-y) ≤ sourceTranslatedU B := by
  intro j y
  have h1 := hB (theta j+y)
  have h2 := hB (theta j-y)
  have hmax : B ≤ max 1 B := le_max_right _ _
  dsimp [sourceTranslatedU]
  linarith

/-- Package only the source assumptions; the previously omitted B3 bound is explicit.
The chosen U, common T4 radius, and all configuration fields precede the prior. -/
theorem exists_config_from_source
    (g q0 : ℝ → ℝ) (c : ℝ) (hc : 0<c)
    (hg : Measurable g) (hg0 : ∀ x, 0≤g x)
    (hgnorm : ∫⁻ x, ENNReal.ofReal (g x) ∂volume = 1)
    (hgzero : ∀ x, x ∉ Set.Icc (-c) c → g x=0)
    (hq : Measurable q0) (hq0 : ∀ x, 0≤q0 x)
    (hqnorm : ∫⁻ x, ENNReal.ofReal (q0 x) ∂volume = 1)
    (hT1 : ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧ ∀ x ∈ Set.Icc (-c) c, m ≤ g x ∧ g x ≤ M)
    (hT2 : DifferentiableOn ℝ g (Set.Ioo (-c) c) ∧
      ∃ R : ℝ, 0 < R ∧ ∀ x ∈ Set.Ioo (-c) c, |deriv g x / g x| ≤ R)
    (B : ℝ) (hB3 : ∀ x, q0 x≤B)
    (t : ℕ) (P : Measure ℝ) (p : Fin t → ℝ) (Rm : Fin t → Measure ℝ) (theta : Fin t → ℝ)
    (hData : IsDataConfig g q0 c t P p Rm theta) :
    ∃ C : LocationConfig, C.t=t ∧ C.c=c ∧ C.g=g ∧ C.q0=q0 ∧ HEq C.theta theta ∧
      C.U=sourceTranslatedU B ∧ (∀ j, C.N j=1) := by
  classical
  obtain ⟨m,M,hm,hmM,hbounds⟩ := hT1
  obtain ⟨hgdiff,R,hR,hgderiv⟩ := hT2
  rcases hData with ⟨ht,hp,hpsum,hRprob,hRmeq,hinj,hsep,hsupp,⟨L,hL,hT4⟩,hP⟩
  obtain ⟨r,hr,hT4r⟩ := uniform_T4_radius q0 theta L hT4
  have hM : 0≤M := hm.le.trans hmM
  have hgupper : ∀ x, g x ≤ M := by
    intro x
    by_cases hx : x∈Set.Icc (-c) c
    · exact (hbounds x hx).2
    · rw [hgzero x hx]; exact hM
  have hgreal := density_integrable_and_integral g hg hg0 hgnorm
  have hqreal := density_integrable_and_integral q0 hq hq0 hqnorm
  have hQ : IsProbabilityMeasure (dpQ0 q0) := ⟨by
    rw [dpQ0, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hqnorm]⟩
  have hkernel : ∀ j, IsProbabilityMeasure (dpRmeasure g theta j) := by
    intro j
    have h := hRprob j
    rw [hRmeq j] at h
    exact h
  let C : LocationConfig := {
    t:=t, ht:=by omega, c:=c, hc:=hc, g:=g, q0:=q0, theta:=theta,
    m:=m, U:=sourceTranslatedU B, M:=M, R:=R, L:=L, r:=r,
    hm:=hm, hU:=sourceTranslatedU_pos B, hM:=hM, hR:=hR.le, hL:=hL, hr:=hr,
    N:=fun _=>1, hN:=fun _=>le_rfl, hg:=hg, hg0:=hg0,
    hgpos:=fun x hx => hm.trans_le (hbounds x hx).1,
    hgzero:=hgzero, hglo:=fun x hx => (hbounds x hx).1, hgM:=hgupper,
    hgnorm:=hgreal.2, hgdiff:=hgdiff, hgderiv:=hgderiv,
    hq:=hq, hq0:=hq0, hqnorm:=hqreal.2, hqint:=hqreal.1, hQ:=hQ,
    hRprob:=hkernel, hT3:=fun j y hy => sourceTranslatedU_bound q0 B hB3 theta j y,
    hT4:=hT4r, hsep:=hsep }
  exact ⟨C,rfl,rfl,rfl,rfl,HEq.rfl,rfl,fun _=>rfl⟩

#print axioms density_integrable_and_integral
#print axioms uniform_T4_radius
#print axioms exists_config_from_source
end ManualDPCons
