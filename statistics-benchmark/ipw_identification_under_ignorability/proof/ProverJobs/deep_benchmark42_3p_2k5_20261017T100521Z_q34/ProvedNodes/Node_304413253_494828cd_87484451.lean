import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q34.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q34.Base

open MeasureTheory

open MeasureTheory

set_option autoImplicit false in
theorem statopia_math_node_304413253_494828cd : ∀ {Ω 𝒵 : Type*}
    [MeasurableSpace Ω]
    [Fintype 𝒵]
    [MeasurableSpace 𝒵]
    [MeasurableSingletonClass 𝒵]
    (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Z : Ω → 𝒵)
    (hZmeas : Measurable Z)
    (f : Ω → ℝ)
    (hf : Integrable f P),
    ∫ ω, f ω ∂P = ∑ z : 𝒵, ∫ ω in {ω | Z ω = z}, f ω ∂P := by
  /- @proof-region region.target-node.session.74c5eabf8f0c415b begin -/
  intro Ω 𝒵 _ _ _ _ P _ Z hZmeas f hf
  have hatom : ∀ z : 𝒵, MeasurableSet {ω : Ω | Z ω = z} :=
    fun z => hZmeas (measurableSet_singleton z)
  have hdecomp : ∀ s : Set Ω, MeasurableSet s →
      (∑ z : 𝒵, P (s ∩ {ω : Ω | Z ω = z})) = P s := by
    intro s hs
    have hdisj : Set.PairwiseDisjoint ((Finset.univ : Finset 𝒵) : Set 𝒵)
        (fun z : 𝒵 => s ∩ {ω : Ω | Z ω = z}) := by
      intro a _ b _ hab
      refine Set.disjoint_left.mpr (fun x hxa hxb => ?_)
      exact hab (hxa.2.symm.trans hxb.2)
    have hmeas : ∀ b ∈ (Finset.univ : Finset 𝒵), MeasurableSet (s ∩ {ω : Ω | Z ω = b}) :=
      fun b _ => hs.inter (hatom b)
    have hbi := MeasureTheory.measure_biUnion_finset (μ := P) (s := (Finset.univ : Finset 𝒵))
      (f := fun z : 𝒵 => s ∩ {ω : Ω | Z ω = z}) hdisj hmeas
    have hconv : (⋃ b ∈ (Finset.univ : Finset 𝒵), (s ∩ {ω : Ω | Z ω = b}))
        = ⋃ b : 𝒵, (s ∩ {ω : Ω | Z ω = b}) := by
      ext x
      simp [Set.mem_iUnion]
    have hone : (⋃ b : 𝒵, (s ∩ {ω : Ω | Z ω = b})) = s := by
      ext x
      constructor
      · intro hx
        obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hx
        exact hb.1
      · intro hx
        exact Set.mem_iUnion.mpr ⟨Z x, hx, rfl⟩
    rw [hconv, hone] at hbi
    exact hbi.symm
  have hsum_eq : (∑ z : 𝒵, P.restrict {ω : Ω | Z ω = z}) = P := by
    apply MeasureTheory.Measure.ext
    intro s hs
    rw [MeasureTheory.Measure.finset_sum_apply]
    exact (Finset.sum_congr rfl
      (fun z _ => MeasureTheory.Measure.restrict_apply hs)).trans (hdecomp s hs)
  have hmain := MeasureTheory.integral_finset_sum_measure (s := (Finset.univ : Finset 𝒵))
    (μ := fun z : 𝒵 => P.restrict {ω : Ω | Z ω = z}) (f := f) (fun z _ => hf.restrict)
  rw [hsum_eq] at hmain
  exact hmain
  /- @proof-region region.target-node.session.74c5eabf8f0c415b end -/
