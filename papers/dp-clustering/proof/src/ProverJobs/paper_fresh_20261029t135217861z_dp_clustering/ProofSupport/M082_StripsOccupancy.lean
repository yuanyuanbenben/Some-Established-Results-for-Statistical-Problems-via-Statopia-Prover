import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions

/- Original module ProverJobs.manual_dp_root_finish_20261031.StripsOccupancy; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators
noncomputable section
namespace OfflineDPRoot

/-- Finite positive-probability sets are all visited with probability tending to one. -/
theorem finite_occupancy {X : Type*} [MeasurableSpace X]
    {J : Type*} [Fintype J] (P : Measure X) [IsProbabilityMeasure P]
    (A : J → Set X) (hA : ∀ j, MeasurableSet (A j)) (hpos : ∀ j, 0 < P (A j)) :
    Tendsto (fun n : ℕ => (Measure.infinitePi (fun _ : ℕ => P))
      {ω : ℕ → X | ¬ ∀ j, ∃ i : Fin n, ω (i : ℕ) ∈ A j}) atTop (𝓝 0) := by
  classical
  let ν := Measure.infinitePi (fun _ : ℕ => P)
  have hmiss : ∀ j (n : ℕ),
      ν {ω : ℕ → X | ¬ ∃ i : Fin n, ω (i : ℕ) ∈ A j} = (P (A j)ᶜ)^n := by
    intro j n
    have hset : {ω : ℕ → X | ¬ ∃ i : Fin n, ω (i : ℕ) ∈ A j} =
        Set.pi (↑(Finset.range n) : Set ℕ) (fun _ => (A j)ᶜ) := by
      ext ω
      simp only [Set.mem_setOf_eq, not_exists, Set.mem_pi, Finset.mem_coe, Finset.mem_range,
        Set.mem_compl_iff]
      constructor
      · intro h i hi
        exact h ⟨i,hi⟩
      · intro h i
        exact h i.val i.isLt
    rw [hset]
    change (Measure.infinitePi (fun _ : ℕ => P)) _ = _
    rw [Measure.infinitePi_pi (fun _ => P) (fun _ _ => (hA j).compl)]
    simp
  have hbad : ∀ n : ℕ, ν {ω : ℕ → X | ¬ ∀ j, ∃ i : Fin n, ω (i : ℕ) ∈ A j} ≤
      ∑ j : J, (P (A j)ᶜ)^n := by
    intro n
    have hset : {ω : ℕ → X | ¬ ∀ j, ∃ i : Fin n, ω (i : ℕ) ∈ A j} =
        ⋃ j : J, {ω : ℕ → X | ¬ ∃ i : Fin n, ω (i : ℕ) ∈ A j} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, not_forall]
    rw [hset]
    simpa only [hmiss] using (measure_iUnion_fintype_le
      (μ := ν) (fun j : J => {ω : ℕ → X | ¬ ∃ i : Fin n, ω (i : ℕ) ∈ A j}))
  have hlim : Tendsto (fun n : ℕ => ∑ j : J, (P (A j)ᶜ)^n) atTop (𝓝 0) := by
    have hcomp : ∀ j, P (A j)ᶜ < 1 := by
      intro j
      rw [measure_compl (hA j) (measure_ne_top _ _), measure_univ]
      exact ENNReal.sub_lt_self ENNReal.one_ne_top (by simp) (hpos j).ne'
    simpa using tendsto_finset_sum Finset.univ
      (fun j _ => ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (hcomp j))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => zero_le _) hbad

/-- A single small central interval at each true component preserves separation. -/
theorem separated_radius (t : ℕ) (ht : 1 ≤ t) (c : ℝ) (hc : 0 < c)
    (θ : Fin t → ℝ) (hsep : ∀ i j, i ≠ j → 2*c < |θ i - θ j|) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ c ∧ ∀ i j, i ≠ j →
      ∀ x ∈ Set.Ioo (θ i - δ) (θ i + δ),
      ∀ y ∈ Set.Ioo (θ j - δ) (θ j + δ), 2*c < |x-y| := by
  classical
  let r : Fin t × Fin t → ℝ := fun ij =>
    if ij.1 = ij.2 then c else min c ((|θ ij.1 - θ ij.2| - 2*c)/4)
  haveI : Nonempty (Fin t) := ⟨⟨0, by omega⟩⟩
  have hne : (Finset.univ : Finset (Fin t × Fin t)).Nonempty := Finset.univ_nonempty
  let d := Finset.univ.inf' hne r
  have hd : 0 < d := by
    apply (Finset.lt_inf'_iff hne).mpr
    intro ij _
    dsimp [r]
    split_ifs with h
    · exact hc
    · exact lt_min hc (by linarith [hsep ij.1 ij.2 h])
  refine ⟨d/2, by positivity, ?_, ?_⟩
  · have hdc : d ≤ c := by
      let k : Fin t := ⟨0, by omega⟩
      have h : d ≤ r (k,k) := Finset.inf'_le r (Finset.mem_univ _)
      simpa [r] using h
    linarith
  · intro i j hij x hx y hy
    have hsmall : d ≤ (|θ i - θ j| - 2*c)/4 := by
      exact (Finset.inf'_le r (Finset.mem_univ (i,j))).trans
        (by simp only [r, if_neg hij]; exact min_le_right _ _)
    have htriangle : |θ i - θ j| ≤ |θ i - x| + |x-y| + |y-θ j| := by
      calc |θ i - θ j| = |(θ i - x) + (x-y) + (y-θ j)| := by congr 1; ring
           _ ≤ |θ i - x| + |x-y| + |y-θ j| := abs_add_three _ _ _
    have hxi : |θ i - x| < d/2 := abs_lt.mpr ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have hyj : |y-θ j| < d/2 := abs_lt.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
    linarith [hsep i j hij]


/-- Each small central strip of a true mixture component has positive truth mass. -/
theorem central_strip_positive (g : ℝ → ℝ) (c m δ : ℝ)
    (hm : 0 < m) (hδ : 0 < δ) (hδc : δ ≤ c)
    (hT1 : ∀ x ∈ Set.Icc (-c) c, m ≤ g x)
    (t : ℕ) (P : Measure ℝ) (p : Fin t → ℝ)
    (Rm : Fin t → Measure ℝ) (θ : Fin t → ℝ)
    (hp : ∀ j, 0 < p j)
    (hRm : ∀ j, Rm j = volume.withDensity (fun x => ENNReal.ofReal (g (x-θ j))))
    (hP : P = ∑ j, ENNReal.ofReal (p j) • Rm j) :
    ∀ j, 0 < P (Set.Ioo (θ j-δ) (θ j+δ)) := by
  intro j
  let A : Set ℝ := Set.Ioo (θ j-δ) (θ j+δ)
  have hconst : 0 < ∫⁻ _ in A, ENNReal.ofReal m ∂volume := by
    simp only [lintegral_const, Measure.restrict_apply_univ, A, Real.volume_Ioo]
    apply bot_lt_iff_ne_bot.mpr
    exact mul_ne_zero (ENNReal.ofReal_pos.mpr hm).ne'
      (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  have hRpos : 0 < Rm j A := by
    rw [hRm j, withDensity_apply _ measurableSet_Ioo]
    apply lt_of_lt_of_le hconst
    apply setLIntegral_mono' measurableSet_Ioo
    intro x hx
    exact ENNReal.ofReal_le_ofReal (hT1 (x-θ j) ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  have hsub : ENNReal.ofReal (p j) • Rm j ≤ P := by
    rw [hP]
    intro S
    rw [Measure.finset_sum_apply]
    exact Finset.single_le_sum
      (f := fun k : Fin t => ((ENNReal.ofReal (p k) • Rm k) S : ℝ≥0∞))
      (fun _ _ => zero_le _) (Finset.mem_univ j)
  have hmass : 0 < (ENNReal.ofReal (p j) • Rm j) A := by
    simpa only [Measure.smul_apply, smul_eq_mul] using
      bot_lt_iff_ne_bot.mpr (mul_ne_zero (ENNReal.ofReal_pos.mpr (hp j)).ne' hRpos.ne')
  exact lt_of_lt_of_le hmass (hsub A)

/-- Actual separated truth samples contain t incompatible representatives with
probability tending to one, without invoking an abstract DP posterior. -/
theorem separated_representatives (g : ℝ → ℝ) (c m : ℝ)
    (hc : 0 < c) (hm : 0 < m)
    (hT1 : ∀ x ∈ Set.Icc (-c) c, m ≤ g x)
    (t : ℕ) (ht : 1 ≤ t) (P : Measure ℝ) [IsProbabilityMeasure P]
    (p : Fin t → ℝ) (Rm : Fin t → Measure ℝ) (θ : Fin t → ℝ)
    (hp : ∀ j, 0 < p j)
    (hRm : ∀ j, Rm j = volume.withDensity (fun x => ENNReal.ofReal (g (x-θ j))))
    (hP : P = ∑ j, ENNReal.ofReal (p j) • Rm j)
    (hsep : ∀ i j, i ≠ j → 2*c < |θ i - θ j|) :
    Tendsto (fun n : ℕ => (Measure.infinitePi (fun _ : ℕ => P))
      {ω : ℕ → ℝ | ¬ ∃ idx : Fin t → Fin n,
        ∀ i j, i ≠ j → 2*c < |ω (idx i) - ω (idx j)|}) atTop (𝓝 0) := by
  classical
  obtain ⟨δ,hδ,hδc,hδsep⟩ := separated_radius t ht c hc θ hsep
  let A : Fin t → Set ℝ := fun j => Set.Ioo (θ j-δ) (θ j+δ)
  have hpos := central_strip_positive g c m δ hm hδ hδc hT1 t P p Rm θ hp hRm hP
  have hlim := finite_occupancy P A (fun _ => measurableSet_Ioo) hpos
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le _) (fun n => measure_mono ?_)
  intro ω hbad hgood
  apply hbad
  choose idx hidx using hgood
  exact ⟨idx,fun i j hij => hδsep i j hij (ω (idx i)) (hidx i) (ω (idx j)) (hidx j)⟩


end OfflineDPRoot
end
end DPCompletedProof
