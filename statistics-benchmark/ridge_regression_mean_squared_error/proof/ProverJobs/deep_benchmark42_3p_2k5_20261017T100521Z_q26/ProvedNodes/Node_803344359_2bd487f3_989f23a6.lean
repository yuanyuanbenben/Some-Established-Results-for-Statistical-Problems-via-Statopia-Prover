import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q26.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q26.Base

open MeasureTheory Matrix

open MeasureTheory Matrix

set_option autoImplicit false in
theorem statopia_math_node_803344359_2bd487f3 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (epsilon : Ω → Fin n → ℝ)
    (heps : MemLp epsilon 2 P),
    Integrable epsilon P ∧
      (∀ i : Fin n, Integrable (fun ω => epsilon ω i) P) ∧
      (∀ i j : Fin n, Integrable (fun ω => epsilon ω i * epsilon ω j) P) := by
  /- @proof-region region.target-node.session.c8513e529d5fa12e begin -/
  intro Ω _ P _ n epsilon heps
  have hco2 : ∀ i : Fin n, MemLp (fun ω => epsilon ω i) 2 P :=
    fun i => (MeasureTheory.memLp_pi_iff (ι := Fin n) (E := fun _ => ℝ) (p := 2)).mp heps i
  have hone : MemLp (fun _ : Ω => (1 : ℝ)) 2 P := MeasureTheory.memLp_const 1
  have hco1 : ∀ i : Fin n, Integrable (fun ω => epsilon ω i) P := by
    intro i
    have hmul : Integrable (fun ω => epsilon ω i * 1) P :=
      MeasureTheory.MemLp.integrable_mul (hco2 i) hone
    simpa using hmul
  refine ⟨?_, hco1, ?_⟩
  · exact (MeasureTheory.integrable_pi_iff (ι := Fin n) (E := fun _ => ℝ) (f := epsilon)).mpr hco1
  · intro i j
    exact MeasureTheory.MemLp.integrable_mul (hco2 i) (hco2 j)
  /- @proof-region region.target-node.session.c8513e529d5fa12e end -/
