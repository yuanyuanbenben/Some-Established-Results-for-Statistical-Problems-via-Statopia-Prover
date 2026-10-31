import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q30.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q30.Base

open MeasureTheory ProbabilityTheory
open Msc62GroundTruth

open MeasureTheory ProbabilityTheory
namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_2879488259_e798087e : ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → Ω → ℕ) (hX_meas : ∀ i : Fin n, Measurable (X i)) (k : ℕ),
    (∀ m ∈ (Finset.univ : Finset (Fin n)).piAntidiag k,
        ∀ m' ∈ (Finset.univ : Finset (Fin n)).piAntidiag k, m ≠ m' →
          Disjoint {ω : Ω | ∀ i : Fin n, X i ω = m i}
            {ω : Ω | ∀ i : Fin n, X i ω = m' i}) ∧
      {ω : Ω | (∑ i : Fin n, X i ω) = k} =
        ⋃ m ∈ (Finset.univ : Finset (Fin n)).piAntidiag k,
          {ω : Ω | ∀ i : Fin n, X i ω = m i} ∧
      (P {ω : Ω | (∑ i : Fin n, X i ω) = k}).toReal =
        ∑ m ∈ (Finset.univ : Finset (Fin n)).piAntidiag k,
          (P {ω : Ω | ∀ i : Fin n, X i ω = m i}).toReal := by
  /- @proof-region region.target-node.session.b1d373bc7060a1e8 begin -/
  intro Ω _ P _ n X hX_meas k
  have hdisj : ∀ m ∈ (Finset.univ : Finset (Fin n)).piAntidiag k,
      ∀ m' ∈ (Finset.univ : Finset (Fin n)).piAntidiag k, m ≠ m' →
        Disjoint {ω : Ω | ∀ i : Fin n, X i ω = m i}
          {ω : Ω | ∀ i : Fin n, X i ω = m' i} := by
    intro m _ m' _ hne
    rw [Set.disjoint_left]
    intro ω h1 h2
    exact hne (funext fun i => by rw [← h1 i, h2 i])
  have hpart : {ω : Ω | (∑ i : Fin n, X i ω) = k}
      = ⋃ m ∈ (Finset.univ : Finset (Fin n)).piAntidiag k,
          {ω : Ω | ∀ i : Fin n, X i ω = m i} := by
    ext ω
    constructor
    · intro h
      have hm : (fun i : Fin n => X i ω) ∈ (Finset.univ : Finset (Fin n)).piAntidiag k := by
        rw [Finset.mem_piAntidiag]
        exact ⟨by simpa using h, fun i _ => Finset.mem_univ i⟩
      exact Set.mem_iUnion.mpr ⟨fun i : Fin n => X i ω,
        Set.mem_iUnion.mpr ⟨hm, fun i => rfl⟩⟩
    · intro h
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp h
      obtain ⟨hmT, hω⟩ := Set.mem_iUnion.mp hm
      rw [Finset.mem_piAntidiag] at hmT
      calc (∑ i : Fin n, X i ω) = ∑ i : Fin n, m i := Finset.sum_congr rfl fun i _ => hω i
        _ = k := by simpa using hmT.1
  have hmeas : ∀ m ∈ (Finset.univ : Finset (Fin n)).piAntidiag k,
      MeasurableSet {ω : Ω | ∀ i : Fin n, X i ω = m i} := by
    intro m _
    have hset : {ω : Ω | ∀ i : Fin n, X i ω = m i}
        = ⋂ i ∈ (Finset.univ : Finset (Fin n)), X i ⁻¹' ({m i} : Set ℕ) := by
      ext ω
      simp
    rw [hset]
    exact Finset.measurableSet_biInter _
      (fun i _ => hX_meas i (measurableSet_singleton (m i)))
  have hadd : P {ω : Ω | (∑ i : Fin n, X i ω) = k}
      = ∑ m ∈ (Finset.univ : Finset (Fin n)).piAntidiag k,
          P {ω : Ω | ∀ i : Fin n, X i ω = m i} := by
    rw [hpart]
    exact measure_biUnion_finset hdisj hmeas
  refine ⟨hdisj, hpart, ?_⟩
  rw [hadd]
  exact ENNReal.toReal_sum (fun m _ => measure_ne_top P _)
  /- @proof-region region.target-node.session.b1d373bc7060a1e8 end -/

end Msc62GroundTruth
