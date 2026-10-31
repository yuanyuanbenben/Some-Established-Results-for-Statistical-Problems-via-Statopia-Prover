import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.Vocabulary
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.Base

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal
open scoped Classical
open Statlib.Imported

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_1429964664_ddbd65e4 : ∀ (g q0 : ℝ → ℝ) (c : ℝ) (t : ℕ)
    (P : Measure ℝ) (p : Fin t → ℝ) (Rm : Fin t → Measure ℝ) (θstar : Fin t → ℝ)
    (hc : 0 < c) (ht : 1 ≤ t)
    (hg_meas : Measurable g) (hg_nonneg : ∀ x : ℝ, 0 ≤ g x)
    (hg_support : ∀ x : ℝ, x ∉ Set.Icc (-c) c → g x = 0)
    (hg_density : ∫⁻ x, ENNReal.ofReal (g x) ∂volume = 1)
    (hq0_meas : Measurable q0) (hq0_nonneg : ∀ x : ℝ, 0 ≤ q0 x)
    (hp_pos : ∀ j : Fin t, 0 < p j)
    (hp_sum : ∑ j : Fin t, p j = 1)
    (hRm_prob : ∀ j : Fin t, IsProbabilityMeasure (Rm j))
    (hRm_eq : ∀ j : Fin t,
      Rm j = volume.withDensity (fun x : ℝ => ENNReal.ofReal (g (x - θstar j))))
    (hsep : ∀ j k : Fin t, j ≠ k → 2 * c < |θstar j - θstar k|)
    (hP : P = ∑ j : Fin t, ENNReal.ofReal (p j) • Rm j),
    Tendsto
      (fun n : ℕ => (iidLaw P) {ω : ℕ → ℝ |
        (∀ j : Fin t, 1 ≤ (Finset.univ.filter
            (fun i : Fin n => ω (i : ℕ) ∈ Set.Icc (θstar j - c) (θstar j + c))).card)
        ∧ (∑ j : Fin t, (Finset.univ.filter
            (fun i : Fin n => ω (i : ℕ) ∈ Set.Icc (θstar j - c) (θstar j + c))).card = n)
        ∧ (∀ i : Fin n, ∀ j : Fin t,
            ω (i : ℕ) ≠ θstar j - c ∧ ω (i : ℕ) ≠ θstar j + c)})
      atTop (𝓝 (1 : ENNReal)) := by
  /- @proof-region region.target-node.session.9b5dce10b487e28c begin -/
  intro g q0 c t P p Rm θstar hc ht hg_meas hg_nonneg hg_support hg_density
    hq0_meas hq0_nonneg hp_pos hp_sum hRm_prob hRm_eq hsep hP
  classical
  let I : Fin t → Set ℝ := fun j => Set.Icc (θstar j - c) (θstar j + c)
  let Sub : ℕ → Set (ℕ → ℝ) := fun n =>
    ⋂ j : Fin t, {ω : ℕ → ℝ | 1 ≤ (Finset.univ.filter (fun i : Fin n => ω (i:ℕ) ∈ I j)).card}
  let A : ℕ → Set (ℕ → ℝ) := fun n =>
    {ω : ℕ → ℝ | ∑ j : Fin t, (Finset.univ.filter (fun i : Fin n => ω (i:ℕ) ∈ I j)).card = n}
  let B : ℕ → Set (ℕ → ℝ) := fun n =>
    {ω : ℕ → ℝ | ∀ i : Fin n, ∀ j : Fin t, ω (i:ℕ) ≠ θstar j - c ∧ ω (i:ℕ) ≠ θstar j + c}
  let G : ℕ → Set (ℕ → ℝ) := fun n => {ω : ℕ → ℝ |
    (∀ j : Fin t, 1 ≤ (Finset.univ.filter (fun i : Fin n => ω (i:ℕ) ∈ I j)).card)
    ∧ (∑ j : Fin t, (Finset.univ.filter (fun i : Fin n => ω (i:ℕ) ∈ I j)).card = n)
    ∧ (∀ i : Fin n, ∀ j : Fin t, ω (i:ℕ) ≠ θstar j - c ∧ ω (i:ℕ) ≠ θstar j + c)}
  change Tendsto (fun n : ℕ => (iidLaw P) (G n)) atTop (𝓝 1)
  have hImeas : ∀ j : Fin t, MeasurableSet (I j) := fun j => by
    show MeasurableSet (Set.Icc (θstar j - c) (θstar j + c))
    exact measurableSet_Icc
  have hIsep : ∀ j k : Fin t, j ≠ k → Disjoint (I j) (I k) := by
    intro j k hjk
    refine Set.disjoint_left.2 (fun x hx hx' => ?_)
    have hx2 : x ∈ Set.Icc (θstar j - c) (θstar j + c) := hx
    have hx2' : x ∈ Set.Icc (θstar k - c) (θstar k + c) := hx'
    have h1 : |x - θstar j| ≤ c := by
      rw [abs_le]
      simp only [Set.mem_Icc] at hx2
      constructor <;> linarith [hx2.1, hx2.2]
    have h2 : |x - θstar k| ≤ c := by
      rw [abs_le]
      simp only [Set.mem_Icc] at hx2'
      constructor <;> linarith [hx2'.1, hx2'.2]
    have h3 : |θstar j - θstar k| ≤ 2 * c := by
      have e : θstar j - θstar k = (θstar j - x) + (x - θstar k) := by ring
      rw [e]
      calc |(θstar j - x) + (x - θstar k)| ≤ |θstar j - x| + |x - θstar k| := abs_add_le _ _
        _ = |x - θstar j| + |x - θstar k| := by rw [abs_sub_comm (θstar j) x]
        _ ≤ 2 * c := by linarith
    linarith [hsep j k hjk]
  have hRm_apply : ∀ (k : Fin t) (s : Set ℝ), MeasurableSet s →
      Rm k s = ∫⁻ x in s, ENNReal.ofReal (g (x - θstar k)) ∂volume := by
    intro k s hs
    rw [hRm_eq k]
    exact MeasureTheory.withDensity_apply (fun x : ℝ => ENNReal.ofReal (g (x - θstar k))) hs
  have hRm_zero_off : ∀ k : Fin t, Rm k (I k)ᶜ = 0 := by
    intro k
    rw [hRm_apply k _ (hImeas k).compl]
    have hpt : ∀ᵐ x ∂(volume.restrict (I k)ᶜ), ENNReal.ofReal (g (x - θstar k)) = 0 := by
      filter_upwards [MeasureTheory.ae_restrict_mem (hImeas k).compl] with x hx
      have hmem : x - θstar k ∉ Set.Icc (-c) c := by
        intro hcon
        have hx' : x ∈ Set.Icc (θstar k - c) (θstar k + c) := by
          simp only [Set.mem_Icc] at hcon ⊢
          constructor <;> linarith [hcon.1, hcon.2]
        exact hx hx'
      rw [hg_support _ hmem]
      simp
    calc (∫⁻ x in (I k)ᶜ, ENNReal.ofReal (g (x - θstar k)) ∂volume)
        = ∫⁻ x in (I k)ᶜ, (0 : ENNReal) ∂volume := MeasureTheory.lintegral_congr_ae hpt
      _ = 0 := by simp
  have hRm_other : ∀ j k : Fin t, j ≠ k → Rm k (I j) = 0 := by
    intro j k hjk
    rw [hRm_apply k _ (hImeas j)]
    have hpt : ∀ᵐ x ∂(volume.restrict (I j)), ENNReal.ofReal (g (x - θstar k)) = 0 := by
      filter_upwards [MeasureTheory.ae_restrict_mem (hImeas j)] with x hx
      have hx2 : x ∈ Set.Icc (θstar j - c) (θstar j + c) := hx
      have hmem : x - θstar k ∉ Set.Icc (-c) c := by
        intro hcon
        have h1 : |x - θstar j| ≤ c := by
          rw [abs_le]
          constructor <;> linarith [hx2.1, hx2.2]
        have h2 : |x - θstar k| ≤ c := by
          rw [abs_le]
          constructor <;> linarith [hcon.1, hcon.2]
        have h3 : |θstar j - θstar k| ≤ 2 * c := by
          have e : θstar j - θstar k = (θstar j - x) + (x - θstar k) := by ring
          rw [e]
          calc |(θstar j - x) + (x - θstar k)| ≤ |θstar j - x| + |x - θstar k| := abs_add_le _ _
            _ = |x - θstar j| + |x - θstar k| := by rw [abs_sub_comm (θstar j) x]
            _ ≤ 2 * c := by linarith
        linarith [hsep j k hjk]
      rw [hg_support _ hmem]
      simp
    calc (∫⁻ x in I j, ENNReal.ofReal (g (x - θstar k)) ∂volume)
        = ∫⁻ x in I j, (0 : ENNReal) ∂volume := MeasureTheory.lintegral_congr_ae hpt
      _ = 0 := by simp
  have hRm_self : ∀ k : Fin t, Rm k (I k) = 1 := by
    intro k
    have h1 : Rm k (I k) + Rm k (I k)ᶜ = Rm k Set.univ :=
      MeasureTheory.measure_add_measure_compl (hImeas k)
    rw [hRm_zero_off k, (hRm_prob k).measure_univ, add_zero] at h1
    exact h1
  have hP_apply : ∀ s : Set ℝ, P s = ∑ j : Fin t, ENNReal.ofReal (p j) * Rm j s := by
    intro s
    rw [hP, MeasureTheory.Measure.finset_sum_apply]
    simp
  have hsum_ofReal : ∑ j : Fin t, ENNReal.ofReal (p j) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j (_ : j ∈ Finset.univ) => (hp_pos j).le), hp_sum,
      ENNReal.ofReal_one]
  have hP_univ : P Set.univ = 1 := by
    rw [hP_apply]
    have huniv : ∀ j : Fin t, Rm j Set.univ = 1 := fun j => (hRm_prob j).measure_univ
    simp only [huniv, mul_one]
    exact hsum_ofReal
  haveI : IsProbabilityMeasure P := ⟨hP_univ⟩
  have hIprob : ∀ j : Fin t, P (I j) = ENNReal.ofReal (p j) := by
    intro j
    rw [hP_apply]
    have hsub : ∀ k : Fin t, Rm k (I j) = if k = j then 1 else 0 := by
      intro k
      by_cases h : k = j
      · rw [h, if_pos rfl, hRm_self j]
      · rw [hRm_other j k (fun he => h he.symm), if_neg h]
    calc ∑ k : Fin t, ENNReal.ofReal (p k) * Rm k (I j)
        = ∑ k : Fin t, ENNReal.ofReal (p k) * (if k = j then 1 else 0) :=
          Finset.sum_congr rfl (fun k _ => by rw [hsub k])
      _ = ENNReal.ofReal (p j) := by
          have hs := Finset.sum_eq_single (s := (Finset.univ : Finset (Fin t)))
            (f := fun k => ENNReal.ofReal (p k) * (if k = j then 1 else 0)) j ?_ ?_
          · rw [hs]; simp
          · intro k _ hk; simp [hk]
          · intro hmem; exact absurd (Finset.mem_univ j) hmem
  have hS_meas : MeasurableSet (⋃ j : Fin t, I j) := MeasurableSet.iUnion hImeas
  have hSunion : P (⋃ j : Fin t, I j) = 1 := by
    have h := MeasureTheory.measure_iUnion (μ := P) (f := I) (fun j k hjk => hIsep j k hjk) hImeas
    rw [h, tsum_fintype]
    simp only [hIprob, hsum_ofReal]
  have hScompl : P (⋃ j : Fin t, I j)ᶜ = 0 := by
    have hne : P (⋃ j : Fin t, I j) ≠ ⊤ := by
      have hle : P (⋃ j : Fin t, I j) ≤ P Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
      rw [hP_univ] at hle
      exact ne_top_of_le_ne_top (by simp) hle
    rw [MeasureTheory.measure_compl hS_meas hne, hSunion, hP_univ]
    simp
  have hmap_eval : ∀ i : ℕ, Measure.map (fun ω : ℕ → ℝ => ω i) (iidLaw P) = P := by
    intro i
    exact MeasureTheory.Measure.infinitePi_map_eval (fun _ : ℕ => P) i
  have hae_eval : ∀ (i : ℕ) (s : Set ℝ), MeasurableSet s →
      (iidLaw P) {ω : ℕ → ℝ | ω i ∈ s} = P s := by
    intro i s hs
    have h1 : {ω : ℕ → ℝ | ω i ∈ s} = (fun ω : ℕ → ℝ => ω i) ⁻¹' s := rfl
    rw [h1, ← MeasureTheory.Measure.map_apply (measurable_pi_apply i) hs, hmap_eval i]
  have hiid_univ : (iidLaw P) Set.univ = 1 := by
    have h := hae_eval 0 Set.univ MeasurableSet.univ
    simpa using h
  have hRm_singleton : ∀ (k : Fin t) (x : ℝ), Rm k {x} = 0 := by
    intro k x
    rw [hRm_apply k {x} (measurableSet_singleton x)]
    have hz : volume.restrict ({x} : Set ℝ) = 0 := by
      rw [← MeasureTheory.Measure.measure_univ_eq_zero]
      rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]
      simp
    rw [show (∫⁻ y in ({x} : Set ℝ), ENNReal.ofReal (g (y - θstar k)) ∂volume)
        = ∫⁻ y, ENNReal.ofReal (g (y - θstar k)) ∂(volume.restrict {x}) from rfl, hz]
    simp
  have hP_singleton : ∀ x : ℝ, P {x} = 0 := by
    intro x
    rw [hP_apply]
    have h1 : ∀ j : Fin t, Rm j {x} = 0 := fun j => hRm_singleton j x
    simp [h1]
  have hp_le_one : ∀ j : Fin t, p j ≤ 1 := by
    intro j
    have h : p j ≤ ∑ i : Fin t, p i :=
      Finset.single_le_sum (f := p) (fun i _ => (hp_pos i).le) (Finset.mem_univ j)
    simpa [hp_sum] using h
  have hsing : ∀ (i : ℕ) (x : ℝ), (iidLaw P) {ω : ℕ → ℝ | ω i = x} = 0 := by
    intro i x
    have h := hae_eval i {x} (measurableSet_singleton x)
    have heq : {ω : ℕ → ℝ | ω i = x} = {ω : ℕ → ℝ | ω i ∈ ({x} : Set ℝ)} := by
      ext ω
      simp
    rw [heq, h, hP_singleton x]
  have hbox : ∀ (n : ℕ) (T : Set ℝ), MeasurableSet T →
      (iidLaw P) {ω : ℕ → ℝ | ∀ i ∈ Finset.range n, ω i ∈ T} = (P T) ^ n := by
    intro n T hT
    have h1 : {ω : ℕ → ℝ | ∀ i ∈ Finset.range n, ω i ∈ T} =
        Set.pi (↑(Finset.range n) : Set ℕ) (fun _ => T) := by
      ext ω
      simp
    have hiid : iidLaw P = Measure.infinitePi (fun _ : ℕ => P) := rfl
    rw [h1, hiid, MeasureTheory.Measure.infinitePi_pi (fun _ : ℕ => P) (fun i _ => hT),
      Finset.prod_const, Finset.card_range]
  have hcover : ∀ n : ℕ, ∀ᵐ ω ∂(iidLaw P), ∀ i : Fin n, ω (i:ℕ) ∈ ⋃ j : Fin t, I j := by
    intro n
    rw [MeasureTheory.ae_all_iff]
    intro i
    rw [MeasureTheory.ae_iff]
    have h3 : (iidLaw P) {ω : ℕ → ℝ | ω (i:ℕ) ∈ (⋃ j : Fin t, I j)ᶜ} =
        P (⋃ j : Fin t, I j)ᶜ := hae_eval (i:ℕ) _ hS_meas.compl
    have heq : {ω : ℕ → ℝ | ¬ (ω (i:ℕ) ∈ ⋃ j : Fin t, I j)} =
        {ω : ℕ → ℝ | ω (i:ℕ) ∈ (⋃ j : Fin t, I j)ᶜ} := by
      ext ω
      simp
    rw [heq, h3, hScompl]
  have hcount : ∀ (n : ℕ) (ω : ℕ → ℝ), (∀ i : Fin n, ω (i:ℕ) ∈ ⋃ j : Fin t, I j) →
      ∑ j : Fin t, (Finset.univ.filter (fun i : Fin n => ω (i:ℕ) ∈ I j)).card = n := by
    intro n ω hcov
    have hstep : ∀ j : Fin t, (Finset.univ.filter (fun i : Fin n => ω (i:ℕ) ∈ I j)).card
        = ∑ i : Fin n, (if ω (i:ℕ) ∈ I j then 1 else 0) := by
      intro j
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    calc ∑ j : Fin t, (Finset.univ.filter (fun i : Fin n => ω (i:ℕ) ∈ I j)).card
        = ∑ j : Fin t, ∑ i : Fin n, (if ω (i:ℕ) ∈ I j then 1 else 0) :=
          Finset.sum_congr rfl (fun j _ => hstep j)
      _ = ∑ i : Fin n, ∑ j : Fin t, (if ω (i:ℕ) ∈ I j then 1 else 0) := Finset.sum_comm
      _ = ∑ i : Fin n, 1 := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          obtain ⟨j₀, hj₀⟩ := Set.mem_iUnion.1 (hcov i)
          rw [Finset.sum_eq_single j₀]
          · simp [hj₀]
          · intro k _ hk
            have hnot : ¬ (ω (i:ℕ) ∈ I k) :=
              fun hmem => (Set.disjoint_left.1 (hIsep k j₀ hk) hmem) hj₀
            simp [hnot]
          · intro hmem
            exact absurd (Finset.mem_univ j₀) hmem
      _ = n := by simp
  have hsum_ae : ∀ n : ℕ, ∀ᵐ ω ∂(iidLaw P),
      ∑ j : Fin t, (Finset.univ.filter (fun i : Fin n => ω (i:ℕ) ∈ I j)).card = n := by
    intro n
    filter_upwards [hcover n] with ω hω
    exact hcount n ω hω
  have hBad : ∀ (n : ℕ) (j : Fin t),
      (iidLaw P) {ω : ℕ → ℝ | (Finset.univ.filter (fun i : Fin n => ω (i:ℕ) ∈ I j)).card = 0}
        = ENNReal.ofReal ((1 - p j) ^ n) := by
    intro n j
    have hset1 : {ω : ℕ → ℝ | (Finset.univ.filter (fun i : Fin n => ω (i:ℕ) ∈ I j)).card = 0}
        = {ω : ℕ → ℝ | ∀ i : Fin n, ω (i:ℕ) ∉ I j} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h i hi
        rw [Finset.card_eq_zero] at h
        have hmem : i ∈ Finset.univ.filter (fun i : Fin n => ω (i:ℕ) ∈ I j) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
        rw [h] at hmem
        exact absurd hmem (by simp)
      · intro h
        rw [Finset.card_eq_zero]
        ext i
        simp [h i]
    have hset2 : {ω : ℕ → ℝ | ∀ i : Fin n, ω (i:ℕ) ∉ I j}
        = {ω : ℕ → ℝ | ∀ i ∈ Finset.range n, ω i ∈ (I j)ᶜ} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Finset.mem_range]
      exact ⟨fun h i hi => h ⟨i, hi⟩, fun h i => h i i.isLt⟩
    rw [hset1, hset2, hbox n (I j)ᶜ (hImeas j).compl]
    have hofs : (1 : ENNReal) - ENNReal.ofReal (p j) = ENNReal.ofReal (1 - p j) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (hp_pos j).le]
    have hPc : P (I j)ᶜ = ENNReal.ofReal (1 - p j) := by
      have hne : P (I j) ≠ ⊤ := by
        have hle : P (I j) ≤ P Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
        rw [hP_univ] at hle
        exact ne_top_of_le_ne_top (by simp) hle
      rw [MeasureTheory.measure_compl (hImeas j) hne, hP_univ, hIprob j, hofs]
    rw [hPc, ← ENNReal.ofReal_pow (show (0:ℝ) ≤ 1 - p j by linarith [hp_pos j, hp_le_one j])]
  have hS1 : ∀ n : ℕ,
      (iidLaw P) {ω : ℕ → ℝ | ¬ (∀ j : Fin t,
        1 ≤ (Finset.univ.filter (fun i : Fin n => ω (i:ℕ) ∈ I j)).card)}
        ≤ ∑ j : Fin t, ENNReal.ofReal ((1 - p j) ^ n) := by
    intro n
    have hsub : {ω : ℕ → ℝ | ¬ (∀ j : Fin t,
        1 ≤ (Finset.univ.filter (fun i : Fin n => ω (i:ℕ) ∈ I j)).card)}
        ⊆ ⋃ j : Fin t, {ω : ℕ → ℝ |
          (Finset.univ.filter (fun i : Fin n => ω (i:ℕ) ∈ I j)).card = 0} := by
      intro ω hω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion] at hω ⊢
      push_neg at hω
      obtain ⟨j, hj⟩ := hω
      exact ⟨j, by omega⟩
    calc (iidLaw P) {ω : ℕ → ℝ | ¬ (∀ j : Fin t,
          1 ≤ (Finset.univ.filter (fun i : Fin n => ω (i:ℕ) ∈ I j)).card)}
        ≤ (iidLaw P) (⋃ j : Fin t, {ω : ℕ → ℝ |
            (Finset.univ.filter (fun i : Fin n => ω (i:ℕ) ∈ I j)).card = 0}) :=
          MeasureTheory.measure_mono hsub
      _ ≤ ∑' j : Fin t, (iidLaw P) {ω : ℕ → ℝ |
            (Finset.univ.filter (fun i : Fin n => ω (i:ℕ) ∈ I j)).card = 0} :=
          MeasureTheory.measure_iUnion_le _
      _ = ∑ j : Fin t, (iidLaw P) {ω : ℕ → ℝ |
            (Finset.univ.filter (fun i : Fin n => ω (i:ℕ) ∈ I j)).card = 0} :=
          tsum_fintype _
      _ = ∑ j : Fin t, ENNReal.ofReal ((1 - p j) ^ n) :=
          Finset.sum_congr rfl (fun j _ => hBad n j)
  have hS2 : ∀ n : ℕ, (iidLaw P) {ω : ℕ → ℝ | ¬ (∑ j : Fin t,
      (Finset.univ.filter (fun i : Fin n => ω (i:ℕ) ∈ I j)).card = n)} = 0 := by
    intro n
    have hsub : {ω : ℕ → ℝ | ¬ (∑ j : Fin t,
        (Finset.univ.filter (fun i : Fin n => ω (i:ℕ) ∈ I j)).card = n)}
        ⊆ {ω : ℕ → ℝ | ¬ (∀ i : Fin n, ω (i:ℕ) ∈ ⋃ j : Fin t, I j)} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      intro hcov
      exact hω (hcount n ω hcov)
    exact bot_unique (le_trans (MeasureTheory.measure_mono hsub)
      (le_of_eq (MeasureTheory.ae_iff.1 (hcover n))))
  have hS3 : ∀ n : ℕ, (iidLaw P) {ω : ℕ → ℝ | ¬ (∀ i : Fin n, ∀ j : Fin t,
      ω (i:ℕ) ≠ θstar j - c ∧ ω (i:ℕ) ≠ θstar j + c)} = 0 := by
    intro n
    have hsub : {ω : ℕ → ℝ | ¬ (∀ i : Fin n, ∀ j : Fin t,
        ω (i:ℕ) ≠ θstar j - c ∧ ω (i:ℕ) ≠ θstar j + c)}
        ⊆ ⋃ i : Fin n, ⋃ j : Fin t, ({ω : ℕ → ℝ | ω (i:ℕ) = θstar j - c} ∪
          {ω : ℕ → ℝ | ω (i:ℕ) = θstar j + c}) := by
      intro ω hω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_union] at hω ⊢
      push_neg at hω
      obtain ⟨i, j, hij⟩ := hω
      refine ⟨i, j, ?_⟩
      by_cases hc' : ω (i:ℕ) = θstar j - c
      · exact Or.inl hc'
      · exact Or.inr (hij hc')
    have hstep : (iidLaw P) (⋃ i : Fin n, ⋃ j : Fin t, ({ω : ℕ → ℝ | ω (i:ℕ) = θstar j - c} ∪
        {ω : ℕ → ℝ | ω (i:ℕ) = θstar j + c}))
        ≤ ∑ i : Fin n, ∑ j : Fin t, ((iidLaw P) {ω : ℕ → ℝ | ω (i:ℕ) = θstar j - c} +
          (iidLaw P) {ω : ℕ → ℝ | ω (i:ℕ) = θstar j + c}) := by
      calc (iidLaw P) (⋃ i : Fin n, ⋃ j : Fin t, ({ω : ℕ → ℝ | ω (i:ℕ) = θstar j - c} ∪
            {ω : ℕ → ℝ | ω (i:ℕ) = θstar j + c}))
          ≤ ∑' i : Fin n, (iidLaw P) (⋃ j : Fin t, ({ω : ℕ → ℝ | ω (i:ℕ) = θstar j - c} ∪
              {ω : ℕ → ℝ | ω (i:ℕ) = θstar j + c})) := MeasureTheory.measure_iUnion_le _
        _ = ∑ i : Fin n, (iidLaw P) (⋃ j : Fin t, ({ω : ℕ → ℝ | ω (i:ℕ) = θstar j - c} ∪
              {ω : ℕ → ℝ | ω (i:ℕ) = θstar j + c})) := tsum_fintype _
        _ ≤ ∑ i : Fin n, ∑ j : Fin t, ((iidLaw P) {ω : ℕ → ℝ | ω (i:ℕ) = θstar j - c} +
              (iidLaw P) {ω : ℕ → ℝ | ω (i:ℕ) = θstar j + c}) := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            calc (iidLaw P) (⋃ j : Fin t, ({ω : ℕ → ℝ | ω (i:ℕ) = θstar j - c} ∪
                  {ω : ℕ → ℝ | ω (i:ℕ) = θstar j + c}))
                ≤ ∑' j : Fin t, (iidLaw P) ({ω : ℕ → ℝ | ω (i:ℕ) = θstar j - c} ∪
                    {ω : ℕ → ℝ | ω (i:ℕ) = θstar j + c}) := MeasureTheory.measure_iUnion_le _
              _ = ∑ j : Fin t, (iidLaw P) ({ω : ℕ → ℝ | ω (i:ℕ) = θstar j - c} ∪
                    {ω : ℕ → ℝ | ω (i:ℕ) = θstar j + c}) := tsum_fintype _
              _ ≤ ∑ j : Fin t, ((iidLaw P) {ω : ℕ → ℝ | ω (i:ℕ) = θstar j - c} +
                    (iidLaw P) {ω : ℕ → ℝ | ω (i:ℕ) = θstar j + c}) :=
                  Finset.sum_le_sum (fun j _ => MeasureTheory.measure_union_le _ _)
    have hzero : ∑ i : Fin n, ∑ j : Fin t, ((iidLaw P) {ω : ℕ → ℝ | ω (i:ℕ) = θstar j - c} +
        (iidLaw P) {ω : ℕ → ℝ | ω (i:ℕ) = θstar j + c}) = 0 := by
      simp only [hsing, zero_add]
      simp
    exact bot_unique (le_trans (MeasureTheory.measure_mono hsub) (le_trans hstep (le_of_eq hzero)))
  have hbound : ∀ n : ℕ, (iidLaw P) (G n)ᶜ ≤ ∑ j : Fin t, ENNReal.ofReal ((1 - p j) ^ n) := by
    intro n
    have hSsub : ({ω : ℕ → ℝ | (∀ j : Fin t,
          1 ≤ (Finset.univ.filter (fun i : Fin n => ω (i:ℕ) ∈ I j)).card)} ∩
        ({ω : ℕ → ℝ | (∑ j : Fin t,
          (Finset.univ.filter (fun i : Fin n => ω (i:ℕ) ∈ I j)).card = n)} ∩
        {ω : ℕ → ℝ | ∀ i : Fin n, ∀ j : Fin t,
          ω (i:ℕ) ≠ θstar j - c ∧ ω (i:ℕ) ≠ θstar j + c})) ⊆ G n := by
      intro ω hω
      exact ⟨hω.1, hω.2.1, hω.2.2⟩
    have hsub : (G n)ᶜ ⊆ ({ω : ℕ → ℝ | ¬ (∀ j : Fin t,
          1 ≤ (Finset.univ.filter (fun i : Fin n => ω (i:ℕ) ∈ I j)).card)} ∪
        ({ω : ℕ → ℝ | ¬ (∑ j : Fin t,
          (Finset.univ.filter (fun i : Fin n => ω (i:ℕ) ∈ I j)).card = n)} ∪
        {ω : ℕ → ℝ | ¬ (∀ i : Fin n, ∀ j : Fin t,
          ω (i:ℕ) ≠ θstar j - c ∧ ω (i:ℕ) ≠ θstar j + c)})) := by
      intro ω hω
      have h2 := Set.compl_subset_compl.2 hSsub hω
      simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_union,
        not_and_or] at h2 ⊢
      tauto
    calc (iidLaw P) (G n)ᶜ
        ≤ (iidLaw P) ({ω : ℕ → ℝ | ¬ (∀ j : Fin t,
            1 ≤ (Finset.univ.filter (fun i : Fin n => ω (i:ℕ) ∈ I j)).card)} ∪
          ({ω : ℕ → ℝ | ¬ (∑ j : Fin t,
            (Finset.univ.filter (fun i : Fin n => ω (i:ℕ) ∈ I j)).card = n)} ∪
          {ω : ℕ → ℝ | ¬ (∀ i : Fin n, ∀ j : Fin t,
            ω (i:ℕ) ≠ θstar j - c ∧ ω (i:ℕ) ≠ θstar j + c)})) :=
          MeasureTheory.measure_mono hsub
      _ ≤ (iidLaw P) {ω : ℕ → ℝ | ¬ (∀ j : Fin t,
            1 ≤ (Finset.univ.filter (fun i : Fin n => ω (i:ℕ) ∈ I j)).card)} +
          (iidLaw P) ({ω : ℕ → ℝ | ¬ (∑ j : Fin t,
            (Finset.univ.filter (fun i : Fin n => ω (i:ℕ) ∈ I j)).card = n)} ∪
          {ω : ℕ → ℝ | ¬ (∀ i : Fin n, ∀ j : Fin t,
            ω (i:ℕ) ≠ θstar j - c ∧ ω (i:ℕ) ≠ θstar j + c)}) :=
          MeasureTheory.measure_union_le _ _
      _ ≤ (iidLaw P) {ω : ℕ → ℝ | ¬ (∀ j : Fin t,
            1 ≤ (Finset.univ.filter (fun i : Fin n => ω (i:ℕ) ∈ I j)).card)} +
          ((iidLaw P) {ω : ℕ → ℝ | ¬ (∑ j : Fin t,
            (Finset.univ.filter (fun i : Fin n => ω (i:ℕ) ∈ I j)).card = n)} +
          (iidLaw P) {ω : ℕ → ℝ | ¬ (∀ i : Fin n, ∀ j : Fin t,
            ω (i:ℕ) ≠ θstar j - c ∧ ω (i:ℕ) ≠ θstar j + c)}) := by
          exact add_le_add (le_refl _) (MeasureTheory.measure_union_le _ _)
      _ ≤ ∑ j : Fin t, ENNReal.ofReal ((1 - p j) ^ n) := by
          rw [hS2 n, hS3 n]
          simp only [add_zero]
          exact hS1 n
  have hrealT : Tendsto (fun n : ℕ => ∑ j : Fin t, (1 - p j) ^ n) atTop (𝓝 0) := by
    have hterm : ∀ j : Fin t, Tendsto (fun n : ℕ => (1 - p j) ^ n) atTop (𝓝 0) := by
      intro j
      apply tendsto_pow_atTop_nhds_zero_of_abs_lt_one
      rw [abs_of_nonneg (by linarith [hp_pos j, hp_le_one j])]
      linarith [hp_pos j]
    have h := tendsto_finset_sum (s := (Finset.univ : Finset (Fin t))) (fun j _ => hterm j)
    simpa using h
  have hdtoReal : ∀ n : ℕ,
      (∑ j : Fin t, ENNReal.ofReal ((1 - p j) ^ n)).toReal = ∑ j : Fin t, (1 - p j) ^ n := by
    intro n
    rw [ENNReal.toReal_sum (fun j _ => ENNReal.ofReal_ne_top)]
    exact Finset.sum_congr rfl (fun j _ =>
      ENNReal.toReal_ofReal (pow_nonneg (by linarith [hp_pos j, hp_le_one j]) n))
  have hdtend : Tendsto (fun n : ℕ => (∑ j : Fin t, ENNReal.ofReal ((1 - p j) ^ n)).toReal)
      atTop (𝓝 0) := by
    simpa only [hdtoReal] using hrealT
  have hsumtop : ∀ n : ℕ, (∑ j : Fin t, ENNReal.ofReal ((1 - p j) ^ n)) ≠ ⊤ := by
    intro n
    have h : (∑ j : Fin t, ENNReal.ofReal ((1 - p j) ^ n)) < ⊤ := by
      rw [WithTop.sum_lt_top]
      exact fun j _ => ENNReal.ofReal_lt_top
    exact ne_of_lt h
  have hle1 : ∀ n : ℕ, (iidLaw P) (G n) ≤ 1 := by
    intro n
    have hle : (iidLaw P) (G n) ≤ (iidLaw P) Set.univ :=
      MeasureTheory.measure_mono (Set.subset_univ _)
    rwa [hiid_univ] at hle
  have hle1' : ∀ n : ℕ, (iidLaw P) (G n)ᶜ ≤ 1 := by
    intro n
    have hle : (iidLaw P) (G n)ᶜ ≤ (iidLaw P) Set.univ :=
      MeasureTheory.measure_mono (Set.subset_univ _)
    rwa [hiid_univ] at hle
  have hb : Tendsto (fun n : ℕ => ((iidLaw P) (G n)ᶜ).toReal) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => ?_) (fun n => ?_) hdtend
    · exact ENNReal.toReal_nonneg
    · exact ENNReal.toReal_mono (hsumtop n) (hbound n)
  have hge : ∀ n : ℕ, (1 : ENNReal) ≤ (iidLaw P) (G n) + (iidLaw P) (G n)ᶜ := by
    intro n
    have hun : G n ∪ (G n)ᶜ = Set.univ := by
      ext ω
      simp
    have h : (iidLaw P) (G n ∪ (G n)ᶜ) ≤ (iidLaw P) (G n) + (iidLaw P) (G n)ᶜ :=
      MeasureTheory.measure_union_le (G n) ((G n)ᶜ)
    rw [hun, hiid_univ] at h
    exact h
  have htop : ∀ n : ℕ, (iidLaw P) (G n) + (iidLaw P) (G n)ᶜ ≠ ⊤ := by
    intro n
    have h3 : (iidLaw P) (G n) + (iidLaw P) (G n)ᶜ ≤ 1 + 1 := add_le_add (hle1 n) (hle1' n)
    exact ne_top_of_le_ne_top (by simp) h3
  have hneG : ∀ n : ℕ, (iidLaw P) (G n) ≠ ⊤ :=
    fun n => ne_top_of_le_ne_top (by simp) (hle1 n)
  have hneGc : ∀ n : ℕ, (iidLaw P) (G n)ᶜ ≠ ⊤ :=
    fun n => ne_top_of_le_ne_top (by simp) (hle1' n)
  have hboundR : ∀ n : ℕ, 1 - ((iidLaw P) (G n)ᶜ).toReal ≤ ((iidLaw P) (G n)).toReal := by
    intro n
    have h2 : (1 : ℝ) ≤ ((iidLaw P) (G n)).toReal + ((iidLaw P) (G n)ᶜ).toReal := by
      have h := ENNReal.toReal_mono (htop n) (hge n)
      rwa [ENNReal.toReal_add (hneG n) (hneGc n), ENNReal.toReal_one] at h
    linarith
  have ha : Tendsto (fun n : ℕ => ((iidLaw P) (G n)).toReal) atTop (𝓝 1) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun n => 1 - ((iidLaw P) (G n)ᶜ).toReal) (h := fun _ => (1 : ℝ)) ?_ ?_ ?_ ?_
    · have h : Tendsto (fun n : ℕ => (1 : ℝ) - ((iidLaw P) (G n)ᶜ).toReal) atTop (𝓝 (1 - 0)) :=
        Tendsto.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)) hb
      simpa using h
    · exact tendsto_const_nhds
    · intro n
      exact hboundR n
    · intro n
      have h := ENNReal.toReal_mono (by simp : (1 : ENNReal) ≠ ⊤) (hle1 n)
      simpa using h
  have hcont : Tendsto (fun n : ℕ => ENNReal.ofReal (((iidLaw P) (G n)).toReal)) atTop
      (𝓝 (ENNReal.ofReal 1)) :=
    (ENNReal.continuous_ofReal.tendsto (1 : ℝ)).comp ha
  have heqG : (fun n : ℕ => ENNReal.ofReal (((iidLaw P) (G n)).toReal))
      = fun n : ℕ => (iidLaw P) (G n) := by
    funext n
    exact ENNReal.ofReal_toReal (hneG n)
  rw [heqG] at hcont
  simpa using hcont
  /- @proof-region region.target-node.session.9b5dce10b487e28c end -/

end Statlib.Imported
