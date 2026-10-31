import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q39.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q39.Base

open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_3148995752_04a8170e : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (hP : P Set.univ = 1)
    (s : Set Ω) (hs : ∀ᵐ ω ∂P, ω ∈ s),
    P s = 1 := by
  /- @proof-region region.target-node.session.4f14f15905f74e2d begin -/
  intro Ω _ P hP s hs
  have hcompl : P sᶜ = 0 := by
    have h : P {ω | ¬ ω ∈ s} = 0 := (MeasureTheory.ae_iff).1 hs
    have hset : sᶜ = {ω | ¬ ω ∈ s} := by
      ext ω
      simp
    rwa [hset]
  have hunion : s ∪ sᶜ = Set.univ := by
    ext ω
    simp
  have hlow : P Set.univ ≤ P s := by
    calc P Set.univ = P (s ∪ sᶜ) := by rw [hunion]
      _ ≤ P s + P sᶜ := measure_union_le s sᶜ
      _ = P s + 0 := by rw [hcompl]
      _ = P s := add_zero _
  have hhigh : P s ≤ P Set.univ := measure_mono (Set.subset_univ s)
  rw [hP] at hlow hhigh
  exact le_antisymm hhigh hlow
  /- @proof-region region.target-node.session.4f14f15905f74e2d end -/
