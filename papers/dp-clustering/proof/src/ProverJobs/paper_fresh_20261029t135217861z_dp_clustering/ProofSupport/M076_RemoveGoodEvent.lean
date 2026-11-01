import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M074_MarkovTail

/- Original module ProverJobs.manual_dp_root_finish_20261031.RemoveGoodEvent; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported
open MeasureTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace OfflineDPConsGeneral
attribute [local instance] Classical.propDecidable

lemma complement_probability {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (G : ℕ → Set X) (hGm : ∀ n, MeasurableSet (G n))
    (hG : Tendsto (fun n => μ (G n)) atTop (𝓝 1)) :
    Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0) := by
  have h := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1:ℝ≥0∞))) hG (Or.inl ENNReal.one_ne_top)
  simp only [tsub_self] at h
  have heq n : μ (G n)ᶜ = 1 - μ (G n) := by rw [measure_compl (hGm n) (measure_ne_top _ _), measure_univ]
  simpa only [heq] using h

lemma remove_good_event {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (G : ℕ → Set X) (hGm : ∀ n, MeasurableSet (G n))
    (hG : Tendsto (fun n => μ (G n)) atTop (𝓝 1))
    (f : ℕ → X → ℝ)
    (hlocal : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => μ {x | ε < if x ∈ G n then f n x else 0}) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => μ {x | ε < f n x}) atTop (𝓝 0) := by
  intro ε hε
  have h := (complement_probability μ G hGm hG).add (hlocal ε hε)
  simp only [zero_add] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le _)
  intro n
  apply (measure_mono (show {x | ε < f n x} ⊆ (G n)ᶜ ∪ {x | ε < if x ∈ G n then f n x else 0} from ?_)).trans (measure_union_le _ _)
  intro x hx
  by_cases hxG : x ∈ G n
  · exact Or.inr (by simpa only [Set.mem_setOf_eq, if_pos hxG] using hx)
  · exact Or.inl hxG
end OfflineDPConsGeneral
end
end DPCompletedProof
