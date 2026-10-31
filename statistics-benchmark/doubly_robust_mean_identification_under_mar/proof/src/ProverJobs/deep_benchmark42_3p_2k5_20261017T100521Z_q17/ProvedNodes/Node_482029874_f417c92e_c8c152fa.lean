import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q17.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q17.Base

open MeasureTheory

open MeasureTheory

set_option autoImplicit false in
theorem statopia_math_node_482029874_f417c92e : ∀ {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (P : Measure Ω)
    (T : ι → Set Ω) (hT : ∀ i, MeasurableSet (T i))
    (g : ι → Ω → ℝ) (hg : ∀ i, Integrable (g i) P),
    Integrable (fun ω => ∑ i, (T i).indicator (g i) ω) P ∧
      ∫ ω, (∑ i, (T i).indicator (g i) ω) ∂P = ∑ i, ∫ ω in (T i), g i ω ∂P := by
  /- @proof-region region.target-node.session.f734f74dd5435c59 begin -/
  intro Ω ι _ _ _ P T hT g hg
  have hInt : ∀ i, Integrable (fun ω => (T i).indicator (g i) ω) P :=
    fun i => (hg i).indicator (hT i)
  refine ⟨?_, ?_⟩
  · simpa using
      (integrable_finset_sum (s := Finset.univ)
        (f := fun i => fun ω => (T i).indicator (g i) ω) (fun i _ => hInt i))
  · calc ∫ ω, (∑ i, (T i).indicator (g i) ω) ∂P
        = ∑ i, ∫ ω, (T i).indicator (g i) ω ∂P :=
          integral_finset_sum Finset.univ (fun i _ => hInt i)
      _ = ∑ i, ∫ ω in (T i), g i ω ∂P := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          exact integral_indicator (hT i)
  /- @proof-region region.target-node.session.f734f74dd5435c59 end -/
