import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q30.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q30.Base

open MeasureTheory ProbabilityTheory
open Msc62GroundTruth

open MeasureTheory ProbabilityTheory
namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_3983978749_db5aa105 : ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → Ω → ℕ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (m : Fin n → ℕ),
    (P (⋂ i : Fin n, {ω : Ω | X i ω = m i})
        = ∏ i : Fin n, P {ω : Ω | X i ω = m i}) ∧
      ((P (⋂ i : Fin n, {ω : Ω | X i ω = m i})).toReal
        = ∏ i : Fin n, (P {ω : Ω | X i ω = m i}).toReal) := by
  /- @proof-region region.target-node.session.f3d943dfce0dcc0b begin -/
  intro Ω mΩ P hP n X hX_meas hX_indep m
  haveI : MeasurableSpace Ω := mΩ
  haveI : IsProbabilityMeasure P := hP
  have hpre : P (⋂ i ∈ (Finset.univ : Finset (Fin n)), X i ⁻¹' ({m i} : Set ℕ))
      = ∏ i ∈ (Finset.univ : Finset (Fin n)), P (X i ⁻¹' ({m i} : Set ℕ)) :=
    (iIndepFun_iff_measure_inter_preimage_eq_mul (μ := P)).1 hX_indep Finset.univ
      (sets := fun i => ({m i} : Set ℕ)) (fun i _ => measurableSet_singleton (m i))
  have hB : ∀ i : Fin n, P (X i ⁻¹' ({m i} : Set ℕ)) = P {ω : Ω | X i ω = m i} := by
    intro i
    congr 1
  have h1 : (⋂ i ∈ (Finset.univ : Finset (Fin n)), X i ⁻¹' ({m i} : Set ℕ))
      = ⋂ i : Fin n, {ω : Ω | X i ω = m i} := by
    ext ω
    simp
  have h2 : (∏ i ∈ (Finset.univ : Finset (Fin n)), P (X i ⁻¹' ({m i} : Set ℕ)))
      = ∏ i : Fin n, P {ω : Ω | X i ω = m i} := by
    simp only [hB]
  have hmain : P (⋂ i : Fin n, {ω : Ω | X i ω = m i}) = ∏ i : Fin n, P {ω : Ω | X i ω = m i} := by
    rw [← h1, ← h2]
    exact hpre
  refine ⟨hmain, ?_⟩
  have hne : ∀ i : Fin n, P {ω : Ω | X i ω = m i} ≠ ⊤ := by
    intro i
    exact ne_of_lt (measure_lt_top P _)
  have htoReal : ∀ (s : Finset (Fin n)) (f : Fin n → ENNReal), (∀ i ∈ s, f i ≠ ⊤) →
      (∏ i ∈ s, f i).toReal = ∏ i ∈ s, (f i).toReal := by
    intro s
    induction s using Finset.induction with
    | empty =>
      intro f _
      simp
    | insert a s ha ih =>
      intro f hf
      rw [Finset.prod_insert ha, Finset.prod_insert ha, ENNReal.toReal_mul,
        ih f (fun i hi => hf i (Finset.mem_insert_of_mem hi))]
  rw [hmain]
  exact htoReal Finset.univ _ fun i _ => hne i
  /- @proof-region region.target-node.session.f3d943dfce0dcc0b end -/

end Msc62GroundTruth
