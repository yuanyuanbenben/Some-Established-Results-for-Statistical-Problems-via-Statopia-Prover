import ProverJobs.job_paper_7aa885023a494b54a3d0f82a9b80e7b2.Vocabulary
import ProverJobs.job_paper_7aa885023a494b54a3d0f82a9b80e7b2.Base

open MeasureTheory
open scoped ENNReal BigOperators
open scoped Interval
open Statlib.Imported

open MeasureTheory
open scoped ENNReal BigOperators
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_1939138294_723e8d32 : ∀ (g q0 : ℝ → ℝ) (c m U θstar : ℝ) (a : ℕ)
    (hc : 0 < c) (hm : 0 < m) (hU : 0 < U) (ha : 1 ≤ a)
    (hg_meas : Measurable g) (hq0_meas : Measurable q0)
    (hq0_int : Integrable q0 volume)
    (hg_nonneg : ∀ x : ℝ, 0 ≤ g x)
    (hg_zero : ∀ x : ℝ, x ∉ Set.Icc (-c) c → g x = 0)
    (hg_mass : ∫ x : ℝ, g x ∂volume = 1)
    (hg_ge : ∀ x ∈ Set.Icc (-c) c, m ≤ g x)
    (hq0_nonneg : ∀ θ : ℝ, 0 ≤ q0 θ)
    (hT3 : ∀ y ∈ Set.Icc (0 : ℝ) (2 * c), symmPriorAt q0 θstar y ≤ U)
    (h_lhs_int : Integrable
      (fun θ : ℝ => (∫ x in (θstar - c)..(θstar + c), g (x - θ)) ^ a * q0 θ) volume),
    ∫ θ : ℝ, (∫ x in (θstar - c)..(θstar + c), g (x - θ)) ^ a * q0 θ ∂volume
      ≤ U / (m * ((a : ℝ) + 1)) := by
  /- @proof-region region.target-node.session.8288e595f7a96981 begin -/
  intro g q0 c m U θstar a hc hm hU ha hg_meas hq0_meas hq0_int hg_nonneg hg_zero hg_mass hg_ge
    hq0_nonneg hT3 h_lhs_int
  have hg_int : Integrable g volume := by
    by_contra hcon
    rw [MeasureTheory.integral_undef hcon] at hg_mass
    exact one_ne_zero hg_mass.symm
  have h_ind : (Set.Icc (-c) c).indicator g = g := by
    funext x
    by_cases hx : x ∈ Set.Icc (-c) c
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      exact (hg_zero x hx).symm
  have h_mass_I : ∫ x in (-c)..c, g x = 1 := by
    have h1 : ∫ x : ℝ, g x = ∫ x in Set.Icc (-c) c, g x := by
      conv_lhs => rw [← h_ind]
      exact MeasureTheory.integral_indicator measurableSet_Icc
    have h2 : ∫ x in Set.Icc (-c) c, g x = ∫ x in (-c)..c, g x := by
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (show -c ≤ c by linarith)]
    rw [← h2, ← h1]
    exact hg_mass
  have hIg : IntervalIntegrable g volume (-c) c := hg_int.intervalIntegrable

  have h2cm : 2 * c * m ≤ 1 := by
    have hIb : IntervalIntegrable (fun _ : ℝ => m) volume (-c) c := intervalIntegrable_const
    have hle : ∫ x in (-c)..c, (m : ℝ) ≤ ∫ x in (-c)..c, g x :=
      intervalIntegral.integral_mono_on (show -c ≤ c by linarith) hIb hIg (fun x hx => hg_ge x hx)
    have hconst : ∫ x in (-c)..c, (m : ℝ) = m * (2 * c) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [h_mass_I, hconst] at hle
    nlinarith
  have hzero_left : ∀ a b : ℝ, a ≤ b → b ≤ -c → ∫ z in a..b, g z = 0 := by
    intro a b hab hb
    rw [intervalIntegral.integral_of_le hab, ← MeasureTheory.integral_indicator measurableSet_Ioc]
    have hsub : {z : ℝ | ¬ ((Set.Ioc a b).indicator g z = 0)} ⊆ {-c} := by
      intro z hz
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at hz ⊢
      by_contra hne
      refine hz ?_
      by_cases hmem : z ∈ Set.Ioc a b
      · rw [Set.indicator_of_mem hmem]
        refine hg_zero z ?_
        intro hin
        have h1 : z ≤ -c := le_trans hmem.2 hb
        exact absurd hin.1 (not_le.mpr (lt_of_le_of_ne h1 hne))
      · rw [Set.indicator_of_notMem hmem]
    have hnull : ∀ᵐ z ∂volume, (Set.Ioc a b).indicator g z = 0 := by
      rw [MeasureTheory.ae_iff]
      exact MeasureTheory.measure_mono_null hsub (by simp)
    rw [MeasureTheory.integral_congr_ae hnull]
    simp
  have hzero_right : ∀ a b : ℝ, a ≤ b → c ≤ a → ∫ z in a..b, g z = 0 := by
    intro a b hab ha
    rw [intervalIntegral.integral_of_le hab, ← MeasureTheory.integral_indicator measurableSet_Ioc]
    have hsub : {z : ℝ | ¬ ((Set.Ioc a b).indicator g z = 0)} ⊆ {c} := by
      intro z hz
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at hz ⊢
      by_contra hne
      refine hz ?_
      by_cases hmem : z ∈ Set.Ioc a b
      · rw [Set.indicator_of_mem hmem]
        refine hg_zero z ?_
        intro hin
        have h1 : c ≤ z := le_trans ha (le_of_lt hmem.1)
        exact absurd hin.2 (not_le.mpr (lt_of_le_of_ne h1 (Ne.symm hne)))
      · rw [Set.indicator_of_notMem hmem]
    have hnull : ∀ᵐ z ∂volume, (Set.Ioc a b).indicator g z = 0 := by
      rw [MeasureTheory.ae_iff]
      exact MeasureTheory.measure_mono_null hsub (by simp)
    rw [MeasureTheory.integral_congr_ae hnull]
    simp
  have hmass_z : ∫ z in (-c)..c, g z = 1 := h_mass_I
  have hJ_pos : ∀ u : ℝ, 0 ≤ u → u ≤ 2 * c →
      (∫ x in (θstar - c)..(θstar + c), g (x - (θstar + u))) ≤ 1 - m * u := by
    intro u hu hu2
    have hsub : (∫ x in (θstar - c)..(θstar + c), g (x - (θstar + u)))
        = ∫ z in (-c - u)..(c - u), g z := by
      have h := intervalIntegral.integral_comp_sub_right (f := g) (a := θstar - c) (b := θstar + c) (θstar + u)
      rw [show θstar - c - (θstar + u) = -c - u from by ring,
        show θstar + c - (θstar + u) = c - u from by ring] at h
      exact h
    rw [hsub]
    have hstep1 : ∫ z in (-c - u)..(c - u), g z = ∫ z in (-c)..(c - u), g z := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (f := g) (a := -c - u) (b := -c) (c := c - u)
          hg_int.intervalIntegrable hg_int.intervalIntegrable,
        hzero_left (-c - u) (-c) (by linarith) (le_refl (-c)), zero_add]
    rw [hstep1]
    have hmass2 : (∫ z in (-c)..(c - u), g z) + (∫ z in (c - u)..c, g z) = 1 := by
      have h := intervalIntegral.integral_add_adjacent_intervals (f := g) (a := -c) (b := c - u) (c := c)
        hg_int.intervalIntegrable hg_int.intervalIntegrable
      exact h.trans hmass_z
    have hlow : m * u ≤ ∫ z in (c - u)..c, g z := by
      have hb : ∫ z in (c - u)..c, (m : ℝ) ≤ ∫ z in (c - u)..c, g z :=
        intervalIntegral.integral_mono_on (show c - u ≤ c by linarith) intervalIntegrable_const
          hg_int.intervalIntegrable (fun x hx => hg_ge x ⟨by linarith [hx.1, hu2], hx.2⟩)
      have hc : ∫ z in (c - u)..c, (m : ℝ) = m * u := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        ring
      calc m * u = ∫ z in (c - u)..c, (m : ℝ) := hc.symm
        _ ≤ ∫ z in (c - u)..c, g z := hb
    have hBval : ∫ z in (-c)..(c - u), g z = 1 - ∫ z in (c - u)..c, g z := by
      rw [eq_sub_iff_add_eq]
      exact hmass2
    calc ∫ z in (-c)..(c - u), g z
        = 1 - ∫ z in (c - u)..c, g z := hBval
      _ ≤ 1 - m * u := sub_le_sub_left hlow 1
  have hJ_neg : ∀ v : ℝ, 0 ≤ v → v ≤ 2 * c →
      (∫ x in (θstar - c)..(θstar + c), g (x - (θstar - v))) ≤ 1 - m * v := by
    intro v hv hv2
    have hsub : (∫ x in (θstar - c)..(θstar + c), g (x - (θstar - v)))
        = ∫ z in (v - c)..(c + v), g z := by
      have h := intervalIntegral.integral_comp_sub_right (f := g) (a := θstar - c) (b := θstar + c) (θstar - v)
      rw [show θstar - c - (θstar - v) = v - c from by ring,
        show θstar + c - (θstar - v) = c + v from by ring] at h
      exact h
    rw [hsub]
    have hstep1 : ∫ z in (v - c)..(c + v), g z = ∫ z in (v - c)..c, g z := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (f := g) (a := v - c) (b := c) (c := c + v)
          hg_int.intervalIntegrable hg_int.intervalIntegrable,
        hzero_right c (c + v) (by linarith) (le_refl c), add_zero]
    rw [hstep1]
    have hmass2 : (∫ z in (-c)..(v - c), g z) + (∫ z in (v - c)..c, g z) = 1 := by
      have h := intervalIntegral.integral_add_adjacent_intervals (f := g) (a := -c) (b := v - c) (c := c)
        hg_int.intervalIntegrable hg_int.intervalIntegrable
      exact h.trans hmass_z
    have hlow : m * v ≤ ∫ z in (-c)..(v - c), g z := by
      have hb : ∫ z in (-c)..(v - c), (m : ℝ) ≤ ∫ z in (-c)..(v - c), g z :=
        intervalIntegral.integral_mono_on (show -c ≤ v - c by linarith) intervalIntegrable_const
          hg_int.intervalIntegrable (fun x hx => hg_ge x ⟨hx.1, by linarith [hx.2, hv2]⟩)
      have hc : ∫ z in (-c)..(v - c), (m : ℝ) = m * v := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        ring
      calc m * v = ∫ z in (-c)..(v - c), (m : ℝ) := hc.symm
        _ ≤ ∫ z in (-c)..(v - c), g z := hb
    have hBval : ∫ z in (v - c)..c, g z = 1 - ∫ z in (-c)..(v - c), g z := by
      rw [eq_sub_iff_add_eq, add_comm]
      exact hmass2
    calc ∫ z in (v - c)..c, g z
        = 1 - ∫ z in (-c)..(v - c), g z := hBval
      _ ≤ 1 - m * v := sub_le_sub_left hlow 1
  have hJ_zero_pos : ∀ u : ℝ, 2 * c < u →
      (∫ x in (θstar - c)..(θstar + c), g (x - (θstar + u))) = 0 := by
    intro u hu
    have hsub : (∫ x in (θstar - c)..(θstar + c), g (x - (θstar + u)))
        = ∫ z in (-c - u)..(c - u), g z := by
      have h := intervalIntegral.integral_comp_sub_right (f := g) (a := θstar - c) (b := θstar + c) (θstar + u)
      rw [show θstar - c - (θstar + u) = -c - u from by ring,
        show θstar + c - (θstar + u) = c - u from by ring] at h
      exact h
    rw [hsub]
    exact hzero_left (-c - u) (c - u) (by linarith) (by linarith)
  have hJ_zero_neg : ∀ v : ℝ, 2 * c < v →
      (∫ x in (θstar - c)..(θstar + c), g (x - (θstar - v))) = 0 := by
    intro v hv
    have hsub : (∫ x in (θstar - c)..(θstar + c), g (x - (θstar - v)))
        = ∫ z in (v - c)..(c + v), g z := by
      have h := intervalIntegral.integral_comp_sub_right (f := g) (a := θstar - c) (b := θstar + c) (θstar - v)
      rw [show θstar - c - (θstar - v) = v - c from by ring,
        show θstar + c - (θstar - v) = c + v from by ring] at h
      exact h
    rw [hsub]
    exact hzero_right (v - c) (c + v) (by linarith) (by linarith)
  have hII : ∀ θ : ℝ, IntervalIntegrable (fun x => g (x - θ)) volume (θstar - c) (θstar + c) := by
    intro θ
    have h := (hg_int.intervalIntegrable (a := θstar - c - θ) (b := θstar + c - θ)).comp_sub_right θ
    rw [show θstar - c - θ + θ = θstar - c from by ring,
      show θstar + c - θ + θ = θstar + c from by ring] at h
    exact h
  have hJ_nonneg : ∀ θ : ℝ, 0 ≤ ∫ x in (θstar - c)..(θstar + c), g (x - θ) := by
    intro θ
    have hmono := intervalIntegral.integral_mono_on (show θstar - c ≤ θstar + c by linarith)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume (θstar - c) (θstar + c))
      (hII θ) (fun x _ => hg_nonneg (x - θ))
    simpa using hmono
  have hpt : ∀ θ : ℝ, (∫ x in (θstar - c)..(θstar + c), g (x - θ)) ^ a * q0 θ ≤
      (Set.Icc (θstar - 2 * c) (θstar + 2 * c)).indicator
        (fun y => (1 - m * |y - θstar|) ^ a * q0 y) θ := by
    intro θ
    by_cases hmem : θ ∈ Set.Icc (θstar - 2 * c) (θstar + 2 * c)
    · rw [Set.indicator_of_mem hmem]
      have hu : |θ - θstar| ≤ 2 * c := by
        rw [abs_le]
        exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
      have hJle : (∫ x in (θstar - c)..(θstar + c), g (x - θ)) ≤ 1 - m * |θ - θstar| := by
        by_cases hpos : 0 ≤ θ - θstar
        · have h := hJ_pos (θ - θstar) hpos (abs_le.mp hu).2
          rw [show θstar + (θ - θstar) = θ from by ring] at h
          rwa [abs_of_nonneg hpos]
        · have hneg : θ - θstar < 0 := not_le.mp hpos
          have hnn : 0 ≤ -(θ - θstar) := by linarith
          have hu' : -(θ - θstar) ≤ 2 * c := by
            rwa [abs_of_neg hneg] at hu
          have h := hJ_neg (-(θ - θstar)) hnn hu'
          rw [show θstar - -(θ - θstar) = θ from by ring] at h
          rwa [abs_of_neg hneg]
      have hpow : (∫ x in (θstar - c)..(θstar + c), g (x - θ)) ^ a ≤ (1 - m * |θ - θstar|) ^ a :=
        pow_le_pow_left₀ (hJ_nonneg θ) hJle a
      exact mul_le_mul_of_nonneg_right hpow (hq0_nonneg θ)
    · rw [Set.indicator_of_notMem hmem]
      have habs : 2 * c < |θ - θstar| := by
        have hx : ¬ (|θ - θstar| ≤ 2 * c) := by
          rw [abs_le]
          exact fun hc' => hmem ⟨by linarith [hc'.1], by linarith [hc'.2]⟩
        linarith
      have hJ0 : (∫ x in (θstar - c)..(θstar + c), g (x - θ)) = 0 := by
        by_cases hpos : 0 ≤ θ - θstar
        · have hp2 : 2 * c < θ - θstar := by
            rw [abs_of_nonneg hpos] at habs
            linarith
          have h := hJ_zero_pos (θ - θstar) hp2
          rwa [show θstar + (θ - θstar) = θ from by ring] at h
        · have hneg : θ - θstar < 0 := not_le.mp hpos
          have hp2 : 2 * c < -(θ - θstar) := by
            rw [abs_of_neg hneg] at habs
            linarith
          have h := hJ_zero_neg (-(θ - θstar)) hp2
          rwa [show θstar - -(θ - θstar) = θ from by ring] at h
      rw [hJ0]
      obtain ⟨k, rfl⟩ : ∃ k : ℕ, a = k + 1 := ⟨a - 1, by omega⟩
      simp [pow_succ]

  by_cases hF : Integrable
      (fun θ : ℝ => (∫ x in (θstar - c)..(θstar + c), g (x - θ)) ^ a * q0 θ) volume
  · have hFnonneg : ∀ θ : ℝ, 0 ≤ (∫ x in (θstar - c)..(θstar + c), g (x - θ)) ^ a * q0 θ :=
      fun θ => mul_nonneg (pow_nonneg (hJ_nonneg θ) a) (hq0_nonneg θ)
    have hFind : (Set.Icc (θstar - 2 * c) (θstar + 2 * c)).indicator
        (fun θ => (∫ x in (θstar - c)..(θstar + c), g (x - θ)) ^ a * q0 θ)
        = fun θ => (∫ x in (θstar - c)..(θstar + c), g (x - θ)) ^ a * q0 θ := by
      funext θ
      by_cases hmem : θ ∈ Set.Icc (θstar - 2 * c) (θstar + 2 * c)
      · rw [Set.indicator_of_mem hmem]
      · rw [Set.indicator_of_notMem hmem]
        have hle := hpt θ
        rw [Set.indicator_of_notMem hmem] at hle
        exact le_antisymm (hFnonneg θ) hle
    have h1 : (∫ θ : ℝ, (∫ x in (θstar - c)..(θstar + c), g (x - θ)) ^ a * q0 θ)
        = ∫ θ in (θstar - 2 * c)..(θstar + 2 * c),
            (∫ x in (θstar - c)..(θstar + c), g (x - θ)) ^ a * q0 θ := by
      conv_lhs => rw [← hFind]
      rw [MeasureTheory.integral_indicator measurableSet_Icc,
        MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (show θstar - 2 * c ≤ θstar + 2 * c by linarith)]
    have hGmeas : Measurable fun y : ℝ => (1 - m * |y - θstar|) ^ a * q0 y := by
      fun_prop
    have hGbound : ∀ᵐ θ ∂volume, ‖(Set.Icc (θstar - 2 * c) (θstar + 2 * c)).indicator
        (fun y => (1 - m * |y - θstar|) ^ a * q0 y) θ‖ ≤ ‖q0 θ‖ := by
      refine Filter.Eventually.of_forall (fun θ => ?_)
      by_cases hmem : θ ∈ Set.Icc (θstar - 2 * c) (θstar + 2 * c)
      · rw [Set.indicator_of_mem hmem]
        have hu : |θ - θstar| ≤ 2 * c := by
          rw [abs_le]
          exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
        have hnn : 0 ≤ 1 - m * |θ - θstar| := by
          have h1 : m * |θ - θstar| ≤ 1 := by
            calc m * |θ - θstar| ≤ m * (2 * c) := mul_le_mul_of_nonneg_left hu (le_of_lt hm)
              _ = 2 * c * m := by ring
              _ ≤ 1 := h2cm
          linarith
        have hle1 : (1 - m * |θ - θstar|) ^ a ≤ 1 := by
          have hle' : 1 - m * |θ - θstar| ≤ 1 := by nlinarith [hm, abs_nonneg (θ - θstar)]
          have := pow_le_one₀ hnn hle' (n := a)
          simpa using this
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hnn a) (hq0_nonneg θ)),
          Real.norm_eq_abs, abs_of_nonneg (hq0_nonneg θ)]
        exact mul_le_of_le_one_left (hq0_nonneg θ) hle1
      · rw [Set.indicator_of_notMem hmem, norm_zero]
        exact norm_nonneg (q0 θ)
    have hGint : Integrable ((Set.Icc (θstar - 2 * c) (θstar + 2 * c)).indicator
        (fun y => (1 - m * |y - θstar|) ^ a * q0 y)) volume := by
      refine hq0_int.mono ?_ ?_ <;>
        first
          | exact (hGmeas.indicator measurableSet_Icc).aestronglyMeasurable
          | exact hGbound
    have hmono : (∫ θ : ℝ, (∫ x in (θstar - c)..(θstar + c), g (x - θ)) ^ a * q0 θ)
        ≤ ∫ θ : ℝ, (Set.Icc (θstar - 2 * c) (θstar + 2 * c)).indicator
            (fun y => (1 - m * |y - θstar|) ^ a * q0 y) θ := by
      refine MeasureTheory.integral_mono_ae ?_ ?_ ?_ <;>
        first
          | exact hF
          | exact hF.aestronglyMeasurable
          | exact hGint
          | exact Filter.Eventually.of_forall (fun θ => hpt θ)
    have h2 : (∫ θ : ℝ, (Set.Icc (θstar - 2 * c) (θstar + 2 * c)).indicator
            (fun y => (1 - m * |y - θstar|) ^ a * q0 y) θ)
        = ∫ θ in (θstar - 2 * c)..(θstar + 2 * c), (1 - m * |θ - θstar|) ^ a * q0 θ := by
      rw [MeasureTheory.integral_indicator measurableSet_Icc,
        MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (show θstar - 2 * c ≤ θstar + 2 * c by linarith)]
    have h3 : (∫ θ in (θstar - 2 * c)..(θstar + 2 * c), (1 - m * |θ - θstar|) ^ a * q0 θ)
        = ∫ u in (-2 * c)..(2 * c), (1 - m * |u|) ^ a * q0 (θstar + u) := by
      have hcongr : (∫ θ in (θstar - 2 * c)..(θstar + 2 * c), (1 - m * |θ - θstar|) ^ a * q0 θ)
          = ∫ x in (θstar - 2 * c)..(θstar + 2 * c),
              (fun u => (1 - m * |u|) ^ a * q0 (θstar + u)) (x - θstar) := by
        apply intervalIntegral.integral_congr
        intro x _
        show (1 - m * |x - θstar|) ^ a * q0 x
            = (1 - m * |x - θstar|) ^ a * q0 (θstar + (x - θstar))
        rw [show θstar + (x - θstar) = x from by ring]
      have h := intervalIntegral.integral_comp_sub_right
        (f := fun u => (1 - m * |u|) ^ a * q0 (θstar + u))
        (a := θstar - 2 * c) (b := θstar + 2 * c) θstar
      rw [show θstar - 2 * c - θstar = -2 * c from by ring,
        show θstar + 2 * c - θstar = 2 * c from by ring] at h
      rw [hcongr]
      exact h
    have hpow : ∫ y in (0 : ℝ)..(2 * c), (1 - m * y) ^ a ≤ 1 / (m * ((a : ℝ) + 1)) := by
      have e1 : ∫ y in (0 : ℝ)..(2 * c), (1 - m * y) ^ a
          = ∫ x in (-2 * c)..(0 : ℝ), (1 + m * x) ^ a := by
        have h := intervalIntegral.integral_comp_neg (f := fun t : ℝ => (1 + m * t) ^ a)
          (a := (0 : ℝ)) (b := 2 * c)
        rw [show -(2 * c) = -2 * c from by ring, neg_zero] at h
        rw [← h]
        apply intervalIntegral.integral_congr
        intro x _
        show (1 - m * x) ^ a = (1 + m * (-x)) ^ a
        rw [show (1 + m * (-x)) = 1 - m * x from by ring]
      rw [e1]
      have e2 : ∫ x in (-2 * c)..(0 : ℝ), (1 + m * x) ^ a
          = m⁻¹ * ∫ x in (1 - 2 * c * m)..(1 : ℝ), x ^ a := by
        have hcongr : ∫ x in (-2 * c)..(0 : ℝ), (1 + m * x) ^ a
            = ∫ x in (-2 * c)..(0 : ℝ), (fun t : ℝ => t ^ a) (m * x + 1) := by
          apply intervalIntegral.integral_congr
          intro x _
          show (1 + m * x) ^ a = (m * x + 1) ^ a
          rw [show 1 + m * x = m * x + 1 from by ring]
        rw [hcongr]
        have hh : m * (∫ x in (-2 * c)..(0 : ℝ), (m * x + 1) ^ a)
            = ∫ x in (1 - 2 * c * m)..(1 : ℝ), x ^ a := by
          have h := intervalIntegral.mul_integral_comp_mul_add (a := -2 * c) (b := (0 : ℝ))
            (f := fun t : ℝ => t ^ a) m (1 : ℝ)
          rw [show m * (-2 * c) + 1 = 1 - 2 * c * m from by ring,
            show m * (0 : ℝ) + 1 = 1 from by ring] at h
          exact h
        rw [← hh, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hm), one_mul]
      rw [e2]
      have hval : ∫ x in (1 - 2 * c * m)..(1 : ℝ), x ^ a
          = (1 - (1 - 2 * c * m) ^ (a + 1)) / ((a : ℝ) + 1) := by
        rw [integral_pow]
        simp
      rw [hval]
      have hfin : (1 - (1 - 2 * c * m) ^ (a + 1)) / ((a : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) := by
        have hp : (0 : ℝ) ≤ (1 - 2 * c * m) ^ (a + 1) := pow_nonneg (by linarith) _
        have hq : (0 : ℝ) < (a : ℝ) + 1 := by positivity
        rw [sub_div]
        linarith [div_nonneg hp (le_of_lt hq)]
      calc m⁻¹ * ((1 - (1 - 2 * c * m) ^ (a + 1)) / ((a : ℝ) + 1))
          ≤ m⁻¹ * (1 / ((a : ℝ) + 1)) := by
            exact mul_le_mul_of_nonneg_left hfin (le_of_lt (inv_pos.mpr hm))
        _ = 1 / (m * ((a : ℝ) + 1)) := by
            have hm0 : m ≠ 0 := ne_of_gt hm
            have ha0 : ((a : ℝ) + 1) ≠ 0 := by positivity
            field_simp
    have key : ∫ u in (-2 * c)..(2 * c), (1 - m * |u|) ^ a * q0 (θstar + u)
        ≤ U * ∫ y in (0 : ℝ)..(2 * c), (1 - m * y) ^ a := by
      have h2cpos : (0:ℝ) ≤ 2 * c := by linarith
      have hWsym : ∀ u : ℝ, symmPriorAt q0 θstar u = symmPriorAt q0 θstar |u| := by
        intro u
        by_cases h : 0 ≤ u
        · rw [abs_of_nonneg h]
        · have h' : u < 0 := not_le.mp h
          rw [abs_of_neg h']
          show q0 (θstar + u) + q0 (θstar - u) = q0 (θstar + -u) + q0 (θstar - -u)
          rw [show θstar + -u = θstar - u from by ring,
            show θstar - -u = θstar + u from by ring, add_comm]
      have hq0U : ∀ u ∈ Set.Icc (-2*c) (2*c), q0 (θstar + u) ≤ U := by
        intro u hu
        have habs : |u| ≤ 2 * c := by
          rw [abs_le]
          exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
        have hT := hT3 |u| ⟨abs_nonneg u, habs⟩
        rw [← hWsym u] at hT
        have hle : q0 (θstar + u) ≤ symmPriorAt q0 θstar u := by
          show q0 (θstar + u) ≤ q0 (θstar + u) + q0 (θstar - u)
          linarith [hq0_nonneg (θstar - u)]
        linarith
      have hq0U' : ∀ y ∈ Set.Icc (0:ℝ) (2*c), q0 (θstar - y) ≤ U := by
        intro y hy
        have hT := hT3 y ⟨hy.1, hy.2⟩
        have hle : q0 (θstar - y) ≤ symmPriorAt q0 θstar y := by
          show q0 (θstar - y) ≤ q0 (θstar + y) + q0 (θstar - y)
          linarith [hq0_nonneg (θstar + y)]
        linarith
      have hWmem : ∀ u ∈ Set.Icc (-2*c) (2*c),
          (0:ℝ) ≤ (1 - m * |u|) ^ a ∧ (1 - m * |u|) ^ a ≤ 1 := by
        intro u hu
        have habs : |u| ≤ 2 * c := by
          rw [abs_le]
          exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
        have h1 : m * |u| ≤ 1 := by
          calc m * |u| ≤ m * (2*c) := mul_le_mul_of_nonneg_left habs (le_of_lt hm)
            _ = 2*c*m := by ring
            _ ≤ 1 := h2cm
        have h2 : (0:ℝ) ≤ 1 - m * |u| := by linarith
        have h3 : 1 - m * |u| ≤ 1 := by nlinarith [hm, abs_nonneg u]
        exact ⟨pow_nonneg h2 a, pow_le_one₀ h2 h3 (n := a)⟩
      have hII_of_bound : ∀ (f : ℝ → ℝ) (A B : ℝ), Measurable f → -2*c ≤ A → A ≤ B → B ≤ 2*c →
          (∀ u ∈ Set.Icc A B, |f u| ≤ U) → IntervalIntegrable f volume A B := by
        intro f A B hf hAB' hAB hB hb
        have hbdd : ∀ᵐ u ∂(volume.restrict (Set.Icc A B)), ‖f u‖ ≤ ‖U‖ := by
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with u hu
          have h1 : ‖U‖ = U := by rw [Real.norm_eq_abs, abs_of_pos hU]
          rw [h1]
          simpa using hb u hu
        have hconstInt : Integrable (fun _ : ℝ => U) (volume.restrict (Set.Icc A B)) :=
          (intervalIntegrable_iff_integrableOn_Icc_of_le hAB).mp intervalIntegrable_const
        have hInt : Integrable f (volume.restrict (Set.Icc A B)) := by
          refine hconstInt.mono ?_ ?_ <;>
            first
              | exact hf.aestronglyMeasurable
              | exact hbdd
        exact (intervalIntegrable_iff_integrableOn_Icc_of_le hAB).mpr hInt
      have hGbound' : ∀ u ∈ Set.Icc (-2*c) (2*c), |(1 - m * |u|) ^ a * q0 (θstar + u)| ≤ U := by
        intro u hu
        have h1 := hWmem u hu
        have h2 := hq0U u hu
        have h3 : (0:ℝ) ≤ q0 (θstar + u) := hq0_nonneg _
        rw [abs_of_nonneg (mul_nonneg h1.1 h3)]
        calc (1 - m * |u|) ^ a * q0 (θstar + u) ≤ 1 * U := mul_le_mul h1.2 h2 h3 (by norm_num)
          _ = U := by ring
      have hpos_le : ∀ y ∈ Set.Icc (0:ℝ) (2*c), |(1 - m * y) ^ a * q0 (θstar + y)| ≤ U := by
        intro y hy
        have hG := hGbound' y ⟨by linarith [hy.1], by linarith [hy.2]⟩
        rw [abs_of_nonneg hy.1] at hG
        exact hG
      have hneg_le : ∀ y ∈ Set.Icc (0:ℝ) (2*c), |(1 - m * y) ^ a * q0 (θstar - y)| ≤ U := by
        intro y hy
        have hu : y ∈ Set.Icc (-2*c) (2*c) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
        have h1 := hWmem y hu
        have h2 := hq0U' y hy
        have h3 : (0:ℝ) ≤ q0 (θstar - y) := hq0_nonneg _
        rw [abs_of_nonneg hy.1] at h1
        rw [abs_of_nonneg (mul_nonneg h1.1 h3)]
        calc (1 - m * y) ^ a * q0 (θstar - y) ≤ 1 * U := mul_le_mul h1.2 h2 h3 (by norm_num)
          _ = U := by ring
      have hII_l : IntervalIntegrable (fun u : ℝ => (1 - m * |u|) ^ a * q0 (θstar + u)) volume (-2*c) (0:ℝ) :=
        hII_of_bound _ _ 0 (by fun_prop) (by linarith) (by linarith) (by linarith) (by
          intro u hu
          exact hGbound' u ⟨by linarith [hu.1], by linarith [hu.2]⟩)
      have hII_r : IntervalIntegrable (fun u : ℝ => (1 - m * |u|) ^ a * q0 (θstar + u)) volume (0:ℝ) (2*c) :=
        hII_of_bound _ 0 (2*c) (by fun_prop) (by linarith) (by linarith) (by linarith) (by
          intro u hu
          exact hGbound' u ⟨by linarith [hu.1], by linarith [hu.2]⟩)
      have hII_a : IntervalIntegrable (fun y : ℝ => (1 - m * y) ^ a * q0 (θstar + y)) volume (0:ℝ) (2*c) :=
        hII_of_bound _ 0 (2*c) (by fun_prop) (by linarith) (by linarith) (by linarith) hpos_le
      have hII_b : IntervalIntegrable (fun y : ℝ => (1 - m * y) ^ a * q0 (θstar - y)) volume (0:ℝ) (2*c) :=
        hII_of_bound _ 0 (2*c) (by fun_prop) (by linarith) (by linarith) (by linarith) hneg_le
      have hII_c : IntervalIntegrable (fun y : ℝ => (1 - m * y) ^ a * U) volume (0:ℝ) (2*c) := by
        refine hII_of_bound _ 0 (2*c) (by fun_prop) (by linarith) (by linarith) (by linarith) ?_
        intro y hy
        have hu : y ∈ Set.Icc (-2*c) (2*c) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
        have h1 := hWmem y hu
        rw [abs_of_nonneg hy.1] at h1
        rw [abs_of_nonneg (mul_nonneg h1.1 (le_of_lt hU))]
        calc (1 - m * y) ^ a * U ≤ 1 * U := mul_le_mul h1.2 (le_refl U) (le_of_lt hU) (by norm_num)
          _ = U := by ring
      have hII_d : IntervalIntegrable
          (fun y : ℝ => (1 - m * y) ^ a * (q0 (θstar + y) + q0 (θstar - y))) volume (0:ℝ) (2*c) := by
        refine hII_of_bound _ 0 (2*c) (by fun_prop) (by linarith) (by linarith) (by linarith) ?_
        intro y hy
        have hu : y ∈ Set.Icc (-2*c) (2*c) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
        have h1 := hWmem y hu
        have h2 : q0 (θstar + y) + q0 (θstar - y) ≤ U := hT3 y ⟨hy.1, hy.2⟩
        have h3 : (0:ℝ) ≤ q0 (θstar + y) + q0 (θstar - y) := by
          linarith [hq0_nonneg (θstar + y), hq0_nonneg (θstar - y)]
        rw [abs_of_nonneg hy.1] at h1
        rw [abs_of_nonneg (mul_nonneg h1.1 h3)]
        calc (1 - m * y) ^ a * (q0 (θstar + y) + q0 (θstar - y)) ≤ 1 * U :=
              mul_le_mul h1.2 h2 h3 (by norm_num)
          _ = U := by ring
      have hsplit : ∫ u in (-2*c)..(2*c), (1 - m * |u|) ^ a * q0 (θstar + u)
          = (∫ u in (-2*c)..(0:ℝ), (1 - m * |u|) ^ a * q0 (θstar + u))
            + ∫ u in (0:ℝ)..(2*c), (1 - m * |u|) ^ a * q0 (θstar + u) := by
        rw [← intervalIntegral.integral_add_adjacent_intervals
          (f := fun u : ℝ => (1 - m * |u|) ^ a * q0 (θstar + u))
          (a := -2*c) (b := (0:ℝ)) (c := 2*c) hII_l hII_r]
      have hreflect : (∫ u in (-2*c)..(0:ℝ), (1 - m * |u|) ^ a * q0 (θstar + u))
          = ∫ y in (0:ℝ)..(2*c), (1 - m * y) ^ a * q0 (θstar - y) := by
        have h := intervalIntegral.integral_comp_neg
          (f := fun u : ℝ => (1 - m * |u|) ^ a * q0 (θstar + u)) (a := (0:ℝ)) (b := 2*c)
        rw [show -(2*c) = -2*c from by ring, neg_zero] at h
        rw [← h]
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le h2cpos] at hx
        show (1 - m * |(-x)|) ^ a * q0 (θstar + -x) = (1 - m * x) ^ a * q0 (θstar - x)
        rw [abs_neg, show θstar + -x = θstar - x from by ring, abs_of_nonneg hx.1]
      have hpos_half : (∫ u in (0:ℝ)..(2*c), (1 - m * |u|) ^ a * q0 (θstar + u))
          = ∫ y in (0:ℝ)..(2*c), (1 - m * y) ^ a * q0 (θstar + y) := by
        apply intervalIntegral.integral_congr
        intro y hy
        rw [Set.uIcc_of_le h2cpos] at hy
        show (1 - m * |y|) ^ a * q0 (θstar + y) = (1 - m * y) ^ a * q0 (θstar + y)
        rw [abs_of_nonneg hy.1]
      have hadd : (∫ y in (0:ℝ)..(2*c), (1 - m * y) ^ a * q0 (θstar + y))
          + ∫ y in (0:ℝ)..(2*c), (1 - m * y) ^ a * q0 (θstar - y)
          = ∫ y in (0:ℝ)..(2*c), (1 - m * y) ^ a * (q0 (θstar + y) + q0 (θstar - y)) := by
        rw [← intervalIntegral.integral_add hII_a hII_b]
        apply intervalIntegral.integral_congr
        intro y _
        ring
      have hmono2 : (∫ y in (0:ℝ)..(2*c), (1 - m * y) ^ a * (q0 (θstar + y) + q0 (θstar - y)))
          ≤ ∫ y in (0:ℝ)..(2*c), (1 - m * y) ^ a * U := by
        refine intervalIntegral.integral_mono_on h2cpos hII_d hII_c ?_
        intro y hy
        have h1 := hWmem y ⟨by linarith [hy.1], by linarith [hy.2]⟩
        have h2 : q0 (θstar + y) + q0 (θstar - y) ≤ U := hT3 y ⟨hy.1, hy.2⟩
        have h3 : (0:ℝ) ≤ q0 (θstar + y) + q0 (θstar - y) := by
          linarith [hq0_nonneg (θstar + y), hq0_nonneg (θstar - y)]
        rw [abs_of_nonneg hy.1] at h1
        exact mul_le_mul_of_nonneg_left h2 h1.1
      have hconstmul : (∫ y in (0:ℝ)..(2*c), (1 - m * y) ^ a * U)
          = U * ∫ y in (0:ℝ)..(2*c), (1 - m * y) ^ a := by
        have hcongr : (∫ y in (0:ℝ)..(2*c), (1 - m * y) ^ a * U)
            = ∫ y in (0:ℝ)..(2*c), U * (1 - m * y) ^ a := by
          apply intervalIntegral.integral_congr
          intro y _
          ring
        rw [hcongr, intervalIntegral.integral_const_mul] <;> rfl
      calc ∫ u in (-2*c)..(2*c), (1 - m * |u|) ^ a * q0 (θstar + u)
          = (∫ u in (-2*c)..(0:ℝ), (1 - m * |u|) ^ a * q0 (θstar + u))
            + ∫ u in (0:ℝ)..(2*c), (1 - m * |u|) ^ a * q0 (θstar + u) := hsplit
        _ = (∫ y in (0:ℝ)..(2*c), (1 - m * y) ^ a * q0 (θstar - y))
            + ∫ y in (0:ℝ)..(2*c), (1 - m * y) ^ a * q0 (θstar + y) := by
              rw [hreflect, hpos_half]
        _ = (∫ y in (0:ℝ)..(2*c), (1 - m * y) ^ a * q0 (θstar + y))
            + ∫ y in (0:ℝ)..(2*c), (1 - m * y) ^ a * q0 (θstar - y) := by rw [add_comm]
        _ = ∫ y in (0:ℝ)..(2*c), (1 - m * y) ^ a * (q0 (θstar + y) + q0 (θstar - y)) := hadd
        _ ≤ ∫ y in (0:ℝ)..(2*c), (1 - m * y) ^ a * U := hmono2
        _ = U * ∫ y in (0:ℝ)..(2*c), (1 - m * y) ^ a := hconstmul
    calc (∫ θ : ℝ, (∫ x in (θstar - c)..(θstar + c), g (x - θ)) ^ a * q0 θ)
        ≤ ∫ θ : ℝ, (Set.Icc (θstar - 2 * c) (θstar + 2 * c)).indicator
            (fun y => (1 - m * |y - θstar|) ^ a * q0 y) θ := hmono
      _ = ∫ θ in (θstar - 2 * c)..(θstar + 2 * c), (1 - m * |θ - θstar|) ^ a * q0 θ := h2
      _ = ∫ u in (-2 * c)..(2 * c), (1 - m * |u|) ^ a * q0 (θstar + u) := h3
      _ ≤ U * ∫ y in (0 : ℝ)..(2 * c), (1 - m * y) ^ a := key
      _ ≤ U * (1 / (m * ((a : ℝ) + 1))) := by
            exact mul_le_mul_of_nonneg_left hpow (le_of_lt hU)
      _ = U / (m * ((a : ℝ) + 1)) := by rw [mul_one_div]
  · rw [MeasureTheory.integral_undef hF]
    have haR : (0 : ℝ) ≤ (a : ℝ) := by positivity
    have hmpos : 0 < m * ((a : ℝ) + 1) := mul_pos hm (by linarith)
    exact div_nonneg (le_of_lt hU) (le_of_lt hmpos)
  /- @proof-region region.target-node.session.8288e595f7a96981 end -/

end Statlib.Imported
