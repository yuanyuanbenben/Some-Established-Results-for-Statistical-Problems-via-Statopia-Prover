import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q18.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q18.Base

open MeasureTheory ProbabilityTheory Filter

open MeasureTheory ProbabilityTheory Filter

set_option autoImplicit false in
theorem statopia_math_node_2816082626_d13a3ccf : ∀ (f : ℝ → ℝ)
    (hf_cont : Continuous f)
    (hf_strict : StrictMono f)
    (hf_bot : Tendsto f Filter.atBot (nhds (0 : ℝ)))
    (hf_top : Tendsto f Filter.atTop (nhds (1 : ℝ))),
    (∀ x : ℝ, 0 < f x ∧ f x < 1) ∧
    (∀ x y : ℝ, f x ≤ f y ↔ x ≤ y) ∧
    (∀ u : ℝ, 0 < u → u < 1 → ∃ x : ℝ, f x = u) ∧
    (∃ e : ℝ ≃o Set.Ioo (0 : ℝ) 1, ∀ x : ℝ, (e x).1 = f x) := by
  /- @proof-region region.target-node.session.3e31d9c3ccae1d87 begin -/
  intro f hf_cont hf_strict hf_bot hf_top
  have hb : ∀ x y : ℝ, f x ≤ f y ↔ x ≤ y := by
    intro x y
    constructor
    · intro h
      by_contra hxy
      push_neg at hxy
      exact absurd h (not_le.mpr (hf_strict hxy))
    · intro h
      exact hf_strict.monotone h
  have ha_pos : ∀ x : ℝ, 0 < f x := by
    intro x
    obtain ⟨y, hyx⟩ := exists_lt x
    have hfyx : f y < f x := hf_strict hyx
    have hfy : 0 ≤ f y := by
      by_contra hneg
      push_neg at hneg
      have h1 : ∀ᶠ z in Filter.atBot, f y < f z := (tendsto_order.1 hf_bot).1 (f y) hneg
      have h2 : ∀ᶠ z in Filter.atBot, z ≤ y := Filter.eventually_atBot.2 ⟨y, fun z hz => hz⟩
      obtain ⟨z, hz1, hz2⟩ := (h1.and h2).exists
      have hz3 : f z ≤ f y := hf_strict.monotone hz2
      linarith
    linarith
  have ha_lt : ∀ x : ℝ, f x < 1 := by
    intro x
    obtain ⟨w, hxw⟩ := exists_gt x
    have hxw' : f x < f w := hf_strict hxw
    have hfw : f w ≤ 1 := by
      by_contra h1
      push_neg at h1
      have h2 : ∀ᶠ z in Filter.atTop, f z < f w := (tendsto_order.1 hf_top).2 (f w) h1
      have h3 : ∀ᶠ z in Filter.atTop, w ≤ z := Filter.eventually_atTop.2 ⟨w, fun z hz => hz⟩
      obtain ⟨z, hz1, hz2⟩ := (h2.and h3).exists
      have hz3 : f w ≤ f z := hf_strict.monotone hz2
      linarith
    linarith
  have hc : ∀ u : ℝ, 0 < u → u < 1 → ∃ x : ℝ, f x = u := by
    intro u hu0 hu1
    have hlow : ∀ᶠ z in Filter.atBot, f z < u := (tendsto_order.1 hf_bot).2 u hu0
    have hhigh : ∀ᶠ z in Filter.atTop, u < f z := (tendsto_order.1 hf_top).1 u hu1
    obtain ⟨a, ha⟩ := hlow.exists
    obtain ⟨b, hb'⟩ := hhigh.exists
    have hlt : a < b := by
      by_contra h
      push_neg at h
      have hmono : f b ≤ f a := hf_strict.monotone h
      linarith
    have hcont : ContinuousOn f (Set.Icc a b) := hf_cont.continuousOn
    have hmem : u ∈ Set.Ioo (f a) (f b) := ⟨ha, hb'⟩
    have himg : u ∈ f '' Set.Ioo a b := intermediate_value_Ioo (le_of_lt hlt) hcont hmem
    rw [Set.mem_image] at himg
    obtain ⟨c, -, hc'⟩ := himg
    exact ⟨c, hc'⟩
  refine ⟨fun x => ⟨ha_pos x, ha_lt x⟩, hb, hc, ?_⟩
  refine ⟨{ toFun := fun x => ⟨f x, ha_pos x, ha_lt x⟩,
            invFun := fun u => Classical.choose (hc u.1 u.2.1 u.2.2),
            left_inv := ?_,
            right_inv := ?_,
            map_rel_iff' := ?_ }, ?_⟩
  · intro x
    exact hf_strict.injective (Classical.choose_spec (hc (f x) (ha_pos x) (ha_lt x)))
  · intro u
    exact Subtype.ext (Classical.choose_spec (hc u.1 u.2.1 u.2.2))
  · intro a b
    simpa using hb a b
  · intro x
    rfl
  /- @proof-region region.target-node.session.3e31d9c3ccae1d87 end -/
