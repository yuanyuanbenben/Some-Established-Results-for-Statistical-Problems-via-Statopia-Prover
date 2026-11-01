import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M021_Vocabulary
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions

/- Original module ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProvedNodes.Node_4113706424_f2009e3d_da786935; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal
open Statlib.Imported
open scoped Classical

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_4113706424_f2009e3d : ∀ (g : ℝ → ℝ) (c : ℝ) (t : ℕ) (hc : 0 < c)
    (hg_meas : Measurable g) (hg_nonneg : ∀ x : ℝ, 0 ≤ g x)
    (hg_support : ∀ x : ℝ, x ∉ Set.Icc (-c) c → g x = 0)
    (hg_density : ∫⁻ x, ENNReal.ofReal (g x) ∂volume = 1)
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (p : Fin t → ℝ) (hp_pos : ∀ j : Fin t, 0 < p j) (hp_sum : ∑ j : Fin t, p j = 1)
    (thetaStar : Fin t → ℝ)
    (hsep : ∀ j k : Fin t, j ≠ k → 2 * c < |thetaStar j - thetaStar k|)
    (Rm : Fin t → Measure ℝ)
    (hRm_prob : ∀ j : Fin t, IsProbabilityMeasure (Rm j))
    (hRm_eq : ∀ j : Fin t,
      Rm j = volume.withDensity (fun x : ℝ => ENNReal.ofReal (g (x - thetaStar j))))
    (hP_eq : P = ∑ j : Fin t, ENNReal.ofReal (p j) • Rm j)
    (N : Fin t → ℕ),
    ∀ j : Fin t,
      Tendsto
        (fun n : ℕ => ((iidLaw P) {ω : ℕ → ℝ |
          (Finset.univ.filter
            (fun i : Fin n => ω (i : ℕ) ∈ Set.Icc (thetaStar j - c) (thetaStar j + c))).card
            < N j}).toReal)
        atTop (nhds 0) := by
  /- @proof-region region.target-node.session.40358823863ec059 begin -/
  intro g c t hc hg_meas hg_nonneg hg_support hg_density P hPprob p hp_pos hp_sum thetaStar hsep Rm
    hRm_prob hRm_eq hP_eq N j
  haveI : IsProbabilityMeasure P := hPprob
  set I : Set ℝ := Set.Icc (thetaStar j - c) (thetaStar j + c) with hI
  have hI_meas : MeasurableSet I := measurableSet_Icc
  have hcard : ∀ (n : ℕ) (ω : ℕ → ℝ),
      (Finset.univ.filter (fun i : Fin n => ω (i : ℕ) ∈ I)).card
        = ((Finset.range n).filter (fun i : ℕ => ω i ∈ I)).card := by
    intro n ω
    rw [Finset.card_filter, Finset.card_filter,
      Fin.sum_univ_eq_sum_range (f := fun i : ℕ => if ω i ∈ I then 1 else 0) n]
  have hgm : Measurable fun x : ℝ => g (x - thetaStar j) :=
    hg_meas.comp (measurable_id.sub measurable_const)
  have hkey : ∫⁻ x in I, ENNReal.ofReal (g (x - thetaStar j)) ∂volume = 1 := by
    have hs : MeasurableSet (Set.Icc (-c) c) := measurableSet_Icc
    have hstep1 : ∀ x : ℝ, x ∈ I ↔ (x - thetaStar j) ∈ Set.Icc (-c) c := by
      intro x
      rw [hI]
      simp only [Set.mem_Icc]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    have hind : ∀ x : ℝ,
        I.indicator (fun y : ℝ => ENNReal.ofReal (g (y - thetaStar j))) x
          = (Set.Icc (-c) c).indicator (fun y : ℝ => ENNReal.ofReal (g y)) (x - thetaStar j) := by
      intro x
      by_cases hx : x ∈ I
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hstep1 x).1 hx)]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem]
        exact fun h => hx ((hstep1 x).2 h)
    calc ∫⁻ x in I, ENNReal.ofReal (g (x - thetaStar j)) ∂volume
        = ∫⁻ x, I.indicator (fun y : ℝ => ENNReal.ofReal (g (y - thetaStar j))) x ∂volume := by
          rw [← MeasureTheory.lintegral_indicator (s := I) hI_meas
            (f := fun y : ℝ => ENNReal.ofReal (g (y - thetaStar j)))]
      _ = ∫⁻ x, (Set.Icc (-c) c).indicator (fun y : ℝ => ENNReal.ofReal (g y)) (x - thetaStar j) ∂volume :=
          MeasureTheory.lintegral_congr hind
      _ = ∫⁻ x, (Set.Icc (-c) c).indicator (fun y : ℝ => ENNReal.ofReal (g y)) x ∂volume :=
          MeasureTheory.lintegral_sub_right_eq_self _ (thetaStar j)
      _ = ∫⁻ x in Set.Icc (-c) c, ENNReal.ofReal (g x) ∂volume := by
          rw [MeasureTheory.lintegral_indicator (s := Set.Icc (-c) c) hs
            (f := fun y : ℝ => ENNReal.ofReal (g y))]
      _ = 1 := by
          rw [← MeasureTheory.lintegral_indicator (s := Set.Icc (-c) c) hs
            (f := fun y : ℝ => ENNReal.ofReal (g y)), ← hg_density]
          apply MeasureTheory.lintegral_congr
          intro x
          by_cases hx : x ∈ Set.Icc (-c) c
          · rw [Set.indicator_of_mem hx]
          · rw [Set.indicator_of_notMem hx, hg_support x hx, ENNReal.ofReal_zero]
  have hRmJ : Rm j I = 1 := by
    have hfmeas : Measurable fun x : ℝ => ENNReal.ofReal (g (x - thetaStar j)) :=
      ENNReal.measurable_ofReal.comp hgm
    calc Rm j I
        = (volume.withDensity (fun x : ℝ => ENNReal.ofReal (g (x - thetaStar j)))) I := by
          rw [hRm_eq j]
      _ = ∫⁻ x in I, (fun _ : ℝ => (1 : ℝ≥0∞)) x
            ∂(volume.withDensity (fun x : ℝ => ENNReal.ofReal (g (x - thetaStar j)))) := by
          rw [MeasureTheory.setLIntegral_const]
          simp
      _ = ∫⁻ x in I, ((fun x : ℝ => ENNReal.ofReal (g (x - thetaStar j))) * 1) x ∂volume :=
          MeasureTheory.setLIntegral_withDensity_eq_setLIntegral_mul (μ := volume)
            (f := fun x : ℝ => ENNReal.ofReal (g (x - thetaStar j)))
            (g := fun _ : ℝ => (1 : ℝ≥0∞)) hfmeas measurable_const hI_meas
      _ = ∫⁻ x in I, ENNReal.ofReal (g (x - thetaStar j)) ∂volume := by simp
      _ = 1 := hkey
  have hPpos : 0 < P I := by
    have hval : (ENNReal.ofReal (p j) • Rm j) I = ENNReal.ofReal (p j) := by
      rw [MeasureTheory.Measure.smul_apply, hRmJ]
      simp
    have hle : (ENNReal.ofReal (p j) • Rm j) I
        ≤ (∑ k : Fin t, ENNReal.ofReal (p k) • Rm k) I := by
      rw [MeasureTheory.Measure.finset_sum_apply]
      exact Finset.single_le_sum (f := fun k : Fin t => (ENNReal.ofReal (p k) • Rm k) I)
        (fun k _ => zero_le _) (Finset.mem_univ j)
    rw [hP_eq]
    exact lt_of_lt_of_le (by rw [hval]; exact ENNReal.ofReal_pos.2 (hp_pos j)) hle
  set q : ℝ≥0∞ := P Iᶜ with hq
  have hPIc_le : P Iᶜ ≤ 1 := by
    rw [← measure_univ (μ := P)]
    exact MeasureTheory.measure_mono (Set.subset_univ _)
  have hq_lt : q < 1 := by
    have htop : P Iᶜ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hPIc_le
    have hsum : P I + P Iᶜ = 1 := by
      rw [MeasureTheory.measure_add_measure_compl hI_meas, measure_univ]
    rw [hq, ← hsum]
    have h := (ENNReal.add_lt_add_iff_right (a := P Iᶜ) htop).2 hPpos
    simpa using h
  have hbound : ∀ n : ℕ,
      (iidLaw P) {ω : ℕ → ℝ | (Finset.univ.filter (fun i : Fin n => ω (i : ℕ) ∈ I)).card < N j}
        ≤ (N j : ℝ≥0∞) * q ^ (n / N j) := by
    intro n
    have hstep : {ω : ℕ → ℝ | (Finset.univ.filter (fun i : Fin n => ω (i : ℕ) ∈ I)).card < N j}
        = {ω : ℕ → ℝ | ((Finset.range n).filter (fun i : ℕ => ω i ∈ I)).card < N j} := by
      ext ω
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hcard n ω]
    rw [hstep]
    by_cases hk : N j = 0
    · have hempty :
          {ω : ℕ → ℝ | ((Finset.range n).filter (fun i : ℕ => ω i ∈ I)).card < N j} = ∅ := by
        ext ω
        simp [hk]
      rw [hempty, hk]
      simp
    · have hkpos : 0 < N j := Nat.pos_of_ne_zero hk
      set m : ℕ := n / N j with hm
      have hb_le : ∀ r : Fin (N j), r.val * m + m ≤ n := by
        intro r
        have h1 : r.val + 1 ≤ N j := r.isLt
        have h2 : (r.val + 1) * m ≤ N j * m := Nat.mul_le_mul_right m h1
        have h3 : N j * m ≤ n := by rw [hm]; exact Nat.mul_div_le n (N j)
        have he : (r.val + 1) * m = r.val * m + m := by ring
        omega
      set B : Fin (N j) → Finset ℕ := fun r =>
        (Finset.range m).map ⟨fun b : ℕ => r.val * m + b, add_right_injective (r.val * m)⟩ with hB
      have hBcard : ∀ r : Fin (N j), (B r).card = m := by
        intro r
        rw [hB]
        simp
      have hBmem : ∀ (r : Fin (N j)) (i : ℕ), i ∈ B r →
          r.val * m ≤ i ∧ i < r.val * m + m := by
        intro r i hi
        rw [hB] at hi
        simp only [Finset.mem_map, Finset.mem_range] at hi
        obtain ⟨b, hb, hbi⟩ := hi
        have hbval : r.val * m + b = i := hbi
        rw [← hbval]
        omega
      have hdisj : ∀ (r r' : Fin (N j)) (i : ℕ), i ∈ B r → i ∈ B r' → r = r' := by
        intro r r' i hi hi'
        obtain ⟨h1, h2⟩ := hBmem r i hi
        obtain ⟨h3, h4⟩ := hBmem r' i hi'
        apply Fin.ext
        by_contra hv
        rcases Nat.lt_or_gt_of_ne hv with hlt | hlt
        · have hm1 : (r.val + 1) * m ≤ r'.val * m := Nat.mul_le_mul_right m (by omega)
          have he : (r.val + 1) * m = r.val * m + m := by ring
          omega
        · have hm1 : (r'.val + 1) * m ≤ r.val * m := Nat.mul_le_mul_right m (by omega)
          have he : (r'.val + 1) * m = r'.val * m + m := by ring
          omega
      have hpigeon : ∀ ω : ℕ → ℝ,
          ((Finset.range n).filter (fun i : ℕ => ω i ∈ I)).card < N j →
          ∃ r : Fin (N j), ∀ i ∈ B r, ω i ∉ I := by
        intro ω hω
        by_contra hcon
        push_neg at hcon
        choose f hfB hfI using hcon
        have hfinj : Function.Injective f := by
          intro r r' he
          refine hdisj r r' (f r) (hfB r) ?_
          rw [he]
          exact hfB r'
        have hsub2 : (Finset.univ : Finset (Fin (N j))).map ⟨f, hfinj⟩ ⊆
            (Finset.range n).filter (fun i : ℕ => ω i ∈ I) := by
          intro i hi
          rw [Finset.mem_map] at hi
          obtain ⟨r, -, hbi⟩ := hi
          have hfr : f r = i := hbi
          rw [← hfr]
          refine Finset.mem_filter.2 ⟨Finset.mem_range.2 ?_, hfI r⟩
          have h1 := (hBmem r (f r) (hfB r)).2
          have h2 := hb_le r
          omega
        have hc := Finset.card_le_card hsub2
        rw [Finset.card_map, Finset.card_univ, Fintype.card_fin] at hc
        omega
      have hcyl : ∀ r : Fin (N j),
          (iidLaw P) {ω : ℕ → ℝ | ∀ i ∈ B r, ω i ∉ I} = q ^ m := by
        intro r
        have hset : {ω : ℕ → ℝ | ∀ i ∈ B r, ω i ∉ I}
            = (↑(B r) : Set ℕ).pi (fun _ : ℕ => (Iᶜ : Set ℝ)) := by
          ext ω
          simp [Set.mem_pi]
        rw [hset]
        have hunf : iidLaw P = Measure.infinitePi (fun _ : ℕ => P) := rfl
        rw [hunf]
        rw [MeasureTheory.Measure.infinitePi_pi (fun _ : ℕ => P) (hμ := fun _ => hPprob)
          (s := B r) (t := fun _ : ℕ => (Iᶜ : Set ℝ)) (fun i _ => hI_meas.compl)]
        rw [Finset.prod_const, hBcard r, ← hq]
      have hsub : {ω : ℕ → ℝ | ((Finset.range n).filter (fun i : ℕ => ω i ∈ I)).card < N j}
          ⊆ ⋃ r : Fin (N j), {ω : ℕ → ℝ | ∀ i ∈ B r, ω i ∉ I} := by
        intro ω hω
        obtain ⟨r, hr⟩ := hpigeon ω hω
        exact Set.mem_iUnion.2 ⟨r, hr⟩
      calc (iidLaw P) {ω : ℕ → ℝ | ((Finset.range n).filter (fun i : ℕ => ω i ∈ I)).card < N j}
          ≤ (iidLaw P) (⋃ r : Fin (N j), {ω : ℕ → ℝ | ∀ i ∈ B r, ω i ∉ I}) :=
            MeasureTheory.measure_mono hsub
        _ ≤ ∑ r : Fin (N j), (iidLaw P) {ω : ℕ → ℝ | ∀ i ∈ B r, ω i ∉ I} := by
            have hEq : (⋃ r : Fin (N j), {ω : ℕ → ℝ | ∀ i ∈ B r, ω i ∉ I})
                = ⋃ r ∈ (Finset.univ : Finset (Fin (N j))),
                    {ω : ℕ → ℝ | ∀ i ∈ B r, ω i ∉ I} := by simp
            rw [hEq]
            exact MeasureTheory.measure_biUnion_finset_le _ _
        _ = ∑ r : Fin (N j), q ^ m := by simp [hcyl]
        _ = (N j : ℝ≥0∞) * q ^ m := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hqtop : q ≠ ⊤ := ne_of_lt (lt_of_lt_of_le hq_lt le_top)
  have hqr_lt : q.toReal < 1 := by
    have hle : q.toReal ≤ 1 := by
      have h := ENNReal.toReal_mono ENNReal.one_ne_top (le_of_lt hq_lt)
      rwa [ENNReal.toReal_one] at h
    refine lt_of_le_of_ne hle ?_
    intro hcon
    have hone : q = 1 := by
      rw [← ENNReal.ofReal_toReal hqtop, hcon, ENNReal.ofReal_one]
    exact absurd hone (ne_of_lt hq_lt)
  have hboundR : ∀ n : ℕ,
      ((iidLaw P) {ω : ℕ → ℝ |
        (Finset.univ.filter (fun i : Fin n => ω (i : ℕ) ∈ I)).card < N j}).toReal
        ≤ (N j : ℝ) * (q.toReal) ^ (n / N j) := by
    intro n
    have hb_eq : (N j : ℝ≥0∞) * q ^ (n / N j)
        = ENNReal.ofReal ((N j : ℝ) * (q.toReal) ^ (n / N j)) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg (N j)),
        ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hqtop]
      simp
    have h1 : ((iidLaw P) {ω : ℕ → ℝ |
          (Finset.univ.filter (fun i : Fin n => ω (i : ℕ) ∈ I)).card < N j}).toReal
        ≤ ((N j : ℝ≥0∞) * q ^ (n / N j)).toReal :=
      ENNReal.toReal_mono (by rw [hb_eq]; exact ENNReal.ofReal_ne_top) (hbound n)
    rw [hb_eq, ENNReal.toReal_ofReal (by positivity)] at h1
    exact h1
  have hbR : Tendsto (fun n : ℕ => (N j : ℝ) * (q.toReal) ^ (n / N j)) atTop (nhds 0) := by
    by_cases hk : N j = 0
    · simp [hk]
    · have hkpos : 0 < N j := Nat.pos_of_ne_zero hk
      have hdiv : Tendsto (fun n : ℕ => n / N j) atTop atTop := by
        rw [tendsto_atTop]
        intro a
        filter_upwards [eventually_ge_atTop (a * N j)] with n hn
        exact (Nat.le_div_iff_mul_le hkpos).2 hn
      have hpow : Tendsto (fun n : ℕ => (q.toReal) ^ (n / N j)) atTop (nhds 0) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one ENNReal.toReal_nonneg hqr_lt).comp hdiv
      have h2 := hpow.const_mul (N j : ℝ)
      simpa using h2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbR
    (fun n => ENNReal.toReal_nonneg) hboundR
  /- @proof-region region.target-node.session.40358823863ec059 end -/

end Statlib.Imported
end DPCompletedProof
