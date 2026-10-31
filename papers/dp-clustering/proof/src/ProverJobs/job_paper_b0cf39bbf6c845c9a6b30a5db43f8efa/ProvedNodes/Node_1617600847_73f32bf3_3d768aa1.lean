import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.Vocabulary
import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.Base

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal MeasureTheory Topology BigOperators
open Statlib.Imported
open Statlib.Imported.DPMModel

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal MeasureTheory Topology BigOperators
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_1617600847_73f32bf3 : ∀ (Θ : Type*) [MeasurableSpace Θ],
    Measurable (fun P : ProbabilityMeasure Θ =>
      Measure.infinitePi (fun _ : ℕ => (P : Measure Θ))) := by
  /- @proof-region region.target-node.session.d00ea53b9df8d7b7 begin -/
  intro Θ _
  classical
  let B : Set (Set (ℕ → Θ)) :=
    {S | ∃ (s : Finset ℕ) (t : ℕ → Set Θ), (∀ i, MeasurableSet (t i)) ∧ S = (s : Set ℕ).pi t}
  have h_eq : (inferInstance : MeasurableSpace (ℕ → Θ)) = MeasurableSpace.generateFrom B := by
    refine le_antisymm ?_ ?_
    · rw [show (inferInstance : MeasurableSpace (ℕ → Θ)) = MeasurableSpace.pi from rfl,
        MeasurableSpace.pi_eq_generateFrom_projections]
      refine MeasurableSpace.generateFrom_mono ?_
      rintro T ⟨i, A, hA, rfl⟩
      refine ⟨{i}, fun _ => A, fun _ => hA, ?_⟩
      ext f
      simp [Set.mem_pi]
    · refine MeasurableSpace.generateFrom_le ?_
      rintro T ⟨s, t, ht, rfl⟩
      have hbox : (s : Set ℕ).pi t
          = ⋂ i : ℕ, Function.eval i ⁻¹' (if i ∈ (s : Set ℕ) then t i else Set.univ) := by
        ext f
        simp only [Set.mem_pi, Set.mem_iInter, Set.mem_preimage, Set.mem_univ]
        constructor
        · intro h i
          by_cases hi : i ∈ (s : Set ℕ)
          · simpa [hi] using h i hi
          · simp [hi]
        · intro h i hi
          simpa [hi] using h i
      rw [hbox]
      refine MeasurableSet.iInter (fun i => ?_)
      have hif : MeasurableSet (if i ∈ (s : Set ℕ) then t i else Set.univ) := by
        by_cases hi : i ∈ (s : Set ℕ)
        · simpa [hi] using ht i
        · simp [hi]
      exact hif.preimage (measurable_pi_apply i)
  have h_piS : IsPiSystem B := by
    rintro T1 ⟨s1, t1, h1, rfl⟩ T2 ⟨s2, t2, h2, rfl⟩ _
    refine ⟨s1 ∪ s2, fun i => (if i ∈ (s1 : Set ℕ) then t1 i else Set.univ) ∩
      (if i ∈ (s2 : Set ℕ) then t2 i else Set.univ), ?_, ?_⟩
    · intro i
      by_cases ha : i ∈ (s1 : Set ℕ) <;> by_cases hb : i ∈ (s2 : Set ℕ)
      · simpa [ha, hb] using (h1 i).inter (h2 i)
      · simpa [ha, hb] using (h1 i).inter MeasurableSet.univ
      · simpa [ha, hb] using MeasurableSet.univ.inter (h2 i)
      · simpa [ha, hb] using MeasurableSet.univ.inter MeasurableSet.univ
    · ext f
      simp only [Set.mem_inter_iff, Set.mem_pi]
      constructor
      · rintro ⟨h1', h2'⟩ i _
        by_cases ha : i ∈ (s1 : Set ℕ) <;> by_cases hb : i ∈ (s2 : Set ℕ)
        · exact ⟨by simpa [ha] using h1' i ha, by simpa [hb] using h2' i hb⟩
        · exact ⟨by simpa [ha] using h1' i ha, by simp [hb]⟩
        · exact ⟨by simp [ha], by simpa [hb] using h2' i hb⟩
        · exact ⟨by simp [ha], by simp [hb]⟩
      · rintro h
        constructor
        · intro i hi1
          have hmem : f i ∈ (if i ∈ (s1 : Set ℕ) then t1 i else Set.univ) ∩
              (if i ∈ (s2 : Set ℕ) then t2 i else Set.univ) :=
            h i (Finset.mem_union.mpr (Or.inl hi1))
          simpa [hi1] using hmem.1
        · intro i hi2
          have hmem : f i ∈ (if i ∈ (s1 : Set ℕ) then t1 i else Set.univ) ∩
              (if i ∈ (s2 : Set ℕ) then t2 i else Set.univ) :=
            h i (Finset.mem_union.mpr (Or.inr hi2))
          simpa [hi2] using hmem.2
  refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    (μ := fun P : ProbabilityMeasure Θ => Measure.infinitePi (fun _ : ℕ => (P : Measure Θ)))
    h_eq h_piS ?_
  rintro T ⟨s, t, ht, rfl⟩
  have hval : (fun P : ProbabilityMeasure Θ =>
      (Measure.infinitePi (fun _ : ℕ => (P : Measure Θ))) ((s : Set ℕ).pi t))
      = fun P : ProbabilityMeasure Θ => ∏ i ∈ s, (P : Measure Θ) (t i) := by
    funext P
    exact Measure.infinitePi_pi (fun _ : ℕ => (P : Measure Θ)) (fun i _ => ht i)
  rw [hval]
  refine Finset.measurable_prod
    (f := fun i (P : ProbabilityMeasure Θ) => (P : Measure Θ) (t i)) s (fun i _ => ?_)
  have hco : Measurable fun P : ProbabilityMeasure Θ => (P : Measure Θ) := by
    first
      | exact measurable_subtype_coe
      | exact Measurable.subtype_coe measurable_id
  exact (Measure.measurable_coe (ht i)).comp hco


  /- @proof-region region.target-node.session.d00ea53b9df8d7b7 end -/

end Statlib.Imported
