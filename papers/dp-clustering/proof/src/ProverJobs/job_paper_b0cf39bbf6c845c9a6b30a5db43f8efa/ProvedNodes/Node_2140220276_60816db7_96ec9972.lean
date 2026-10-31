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
theorem statopia_math_node_2140220276_60816db7 : ∀ {Θ X : Type*} [MeasurableSpace Θ] [TopologicalSpace Θ] [MeasurableSpace X]
    (k : Θ → X → ℝ) (hk_meas : Measurable (Function.uncurry k))
    (n : ℕ) (x : Fin n → X) (P : ProbabilityMeasure Θ),
    (∫⁻ θ : ℕ → Θ, ∏ i : Fin n, ENNReal.ofReal (k (θ (i : ℕ)) (x i))
        ∂ Measure.infinitePi (fun _ : ℕ => P.toMeasure))
      = ∏ i : Fin n, ∫⁻ θ : Θ, ENNReal.ofReal (k θ (x i)) ∂ P.toMeasure := by
  /- @proof-region region.target-node.session.cc772a6194bb39ef begin -/
  intro Θ X _ _ _ k hk_meas n x P
  haveI hP : IsProbabilityMeasure P.toMeasure := inferInstance
  haveI hμ : ∀ i : ℕ, IsProbabilityMeasure ((fun _ : ℕ => P.toMeasure) i) := fun _ => hP
  set f : ℕ → Θ → ENNReal :=
    fun i v => if h : i < n then ENNReal.ofReal (k v (x ⟨i, h⟩)) else 1 with hf
  have hbase_meas : ∀ (y : X), Measurable (fun v : Θ => ENNReal.ofReal (k v y)) := by
    intro y
    exact ENNReal.measurable_ofReal.comp (hk_meas.comp measurable_prodMk_right)
  have hf_meas : ∀ i, Measurable (f i) := by
    intro i
    by_cases hi : i < n
    · have hfi : f i = fun v => ENNReal.ofReal (k v (x ⟨i, hi⟩)) := by
        ext v; rw [hf]; simp only [dif_pos hi]
      rw [hfi]; exact hbase_meas (x ⟨i, hi⟩)
    · have hfi : f i = fun _ => (1 : ENNReal) := by
        ext v; rw [hf]; simp only [dif_neg hi]
      rw [hfi]; exact measurable_const
  have hIndep : iIndepFun (fun (i : ℕ) (ω : ℕ → Θ) => f i (ω i))
      (Measure.infinitePi (fun _ : ℕ => P.toMeasure)) :=
    iIndepFun_infinitePi (P := fun _ : ℕ => P.toMeasure) (X := f) hf_meas
  have hfac := lintegral_prod_eq_prod_lintegral_of_indepFun (s := Finset.range n)
    (X := fun (i : ℕ) (ω : ℕ → Θ) => f i (ω i)) hIndep
    (fun i => (hf_meas i).comp (measurable_pi_apply i))
  trans ∫⁻ ω : ℕ → Θ, ∏ i ∈ Finset.range n, f i (ω i)
      ∂ Measure.infinitePi (fun _ : ℕ => P.toMeasure)
  · apply lintegral_congr
    intro ω
    rw [← Fin.prod_univ_eq_prod_range (fun i => f i (ω i)) n]
    apply Finset.prod_congr rfl
    intro i _
    simp only [hf, dif_pos i.isLt, Fin.eta]
  · rw [hfac]
    rw [← Fin.prod_univ_eq_prod_range
      (fun i => ∫⁻ ω : ℕ → Θ, f i (ω i) ∂ Measure.infinitePi (fun _ : ℕ => P.toMeasure)) n]
    apply Finset.prod_congr rfl
    intro i _
    rw [show (∫⁻ ω : ℕ → Θ, f ↑i (ω ↑i)
          ∂ Measure.infinitePi (fun _ : ℕ => P.toMeasure))
        = ∫⁻ ω : ℕ → Θ, ENNReal.ofReal (k (ω ↑i) (x i))
          ∂ Measure.infinitePi (fun _ : ℕ => P.toMeasure) from by
      apply lintegral_congr
      intro ω
      simp only [hf, dif_pos i.isLt, Fin.eta]]
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => P.toMeasure) (↑i)).lintegral_comp
      (hbase_meas (x i))
  /- @proof-region region.target-node.session.cc772a6194bb39ef end -/

end Statlib.Imported
