import ProverJobs.job_paper_6093c8cdedac44ebaae3246c2f49ba3b.Vocabulary
import ProverJobs.job_paper_6093c8cdedac44ebaae3246c2f49ba3b.Base

namespace PaperProofTasks.job_paper_6093c8cdedac44ebaae3246c2f49ba3b

open MeasureTheory ProbabilityTheory
open _root_.PaperProofTasks.job_paper_6093c8cdedac44ebaae3246c2f49ba3b.Statlib.Imported

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported

noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_3135439720_9bebc028 : ∀ (B : ℕ) (hB : 0 < B) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (theta0 : ℝ) (theta : Fin B → Ω → ℝ) (htheta : ∀ j, Measurable (theta j))
    (hindep : iIndepFun theta μ),
    μ.real {ω | theta0 ∉ Set.Icc
        (Finset.univ.inf' ⟨⟨0, hB⟩, Finset.mem_univ _⟩ (fun j => theta j ω))
        (Finset.univ.sup' ⟨⟨0, hB⟩, Finset.mem_univ _⟩ (fun j => theta j ω))}
      = (∏ j : Fin B, μ.real {ω | theta j ω < theta0})
        + (∏ j : Fin B, μ.real {ω | theta0 < theta j ω}) := by
  /- @proof-region region.target-node.session.46e00bad1f71c871 begin -/
  intro B hB Ω instΩ μ instμ theta0 theta htheta hindep
  classical
  have hind := ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul.mp hindep
  have hmeasIH : MeasurableSet (⋂ j : Fin B, {ω : Ω | theta0 < theta j ω}) :=
    MeasurableSet.iInter (fun j => (htheta j) measurableSet_Ioi)
  have hmeasIL : MeasurableSet (⋂ j : Fin B, {ω : Ω | theta j ω < theta0}) :=
    MeasurableSet.iInter (fun j => (htheta j) measurableSet_Iio)
  have hprodH : μ (⋂ j : Fin B, {ω : Ω | theta0 < theta j ω})
      = ∏ j : Fin B, μ {ω : Ω | theta0 < theta j ω} := by
    have h := hind (Finset.univ : Finset (Fin B)) (sets := fun _ => Set.Ioi theta0) (fun i _ => measurableSet_Ioi)
    rw [show (⋂ i ∈ (Finset.univ : Finset (Fin B)), (theta i) ⁻¹' Set.Ioi theta0)
            = (⋂ j : Fin B, {ω : Ω | theta0 < theta j ω}) from by ext ω; simp,
        show (∏ i ∈ (Finset.univ : Finset (Fin B)), μ ((theta i) ⁻¹' Set.Ioi theta0))
            = (∏ j : Fin B, μ {ω : Ω | theta0 < theta j ω}) from by
          have hfun : (fun i : Fin B => μ ((theta i) ⁻¹' Set.Ioi theta0))
              = (fun j : Fin B => μ {ω : Ω | theta0 < theta j ω}) := by
            funext i
            rw [show (theta i) ⁻¹' Set.Ioi theta0 = {ω : Ω | theta0 < theta i ω} from by
              ext ω; simp]
          rw [hfun]] at h
    exact h
  have hprodL : μ (⋂ j : Fin B, {ω : Ω | theta j ω < theta0})
      = ∏ j : Fin B, μ {ω : Ω | theta j ω < theta0} := by
    have h := hind (Finset.univ : Finset (Fin B)) (sets := fun _ => Set.Iio theta0) (fun i _ => measurableSet_Iio)
    rw [show (⋂ i ∈ (Finset.univ : Finset (Fin B)), (theta i) ⁻¹' Set.Iio theta0)
            = (⋂ j : Fin B, {ω : Ω | theta j ω < theta0}) from by ext ω; simp,
        show (∏ i ∈ (Finset.univ : Finset (Fin B)), μ ((theta i) ⁻¹' Set.Iio theta0))
            = (∏ j : Fin B, μ {ω : Ω | theta j ω < theta0}) from by
          have hfun : (fun i : Fin B => μ ((theta i) ⁻¹' Set.Iio theta0))
              = (fun j : Fin B => μ {ω : Ω | theta j ω < theta0}) := by
            funext i
            rw [show (theta i) ⁻¹' Set.Iio theta0 = {ω : Ω | theta i ω < theta0} from by
              ext ω; simp]
          rw [hfun]] at h
    exact h
  have hHreal : μ.real (⋂ j : Fin B, {ω : Ω | theta0 < theta j ω})
      = ∏ j : Fin B, μ.real {ω : Ω | theta0 < theta j ω} := by
    rw [MeasureTheory.measureReal_def, hprodH, ENNReal.toReal_prod]
    simp [MeasureTheory.measureReal_def]
  have hLreal : μ.real (⋂ j : Fin B, {ω : Ω | theta j ω < theta0})
      = ∏ j : Fin B, μ.real {ω : Ω | theta j ω < theta0} := by
    rw [MeasureTheory.measureReal_def, hprodL, ENNReal.toReal_prod]
    simp [MeasureTheory.measureReal_def]
  have hA : {ω : Ω | theta0 < Finset.univ.inf' ⟨⟨0, hB⟩, Finset.mem_univ _⟩ (fun j => theta j ω)}
      = ⋂ j : Fin B, {ω : Ω | theta0 < theta j ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [Finset.lt_inf'_iff ⟨⟨0, hB⟩, Finset.mem_univ _⟩]
    simp
  have hB1 : {ω : Ω | Finset.univ.sup' ⟨⟨0, hB⟩, Finset.mem_univ _⟩ (fun j => theta j ω) < theta0}
      = ⋂ j : Fin B, {ω : Ω | theta j ω < theta0} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [Finset.sup'_lt_iff ⟨⟨0, hB⟩, Finset.mem_univ _⟩]
    simp
  have hmeasB1 : MeasurableSet {ω : Ω | Finset.univ.sup' ⟨⟨0, hB⟩, Finset.mem_univ _⟩ (fun j => theta j ω) < theta0} := by
    rw [hB1]; exact hmeasIL
  have hdisj : Disjoint {ω : Ω | theta0 < Finset.univ.inf' ⟨⟨0, hB⟩, Finset.mem_univ _⟩ (fun j => theta j ω)}
      {ω : Ω | Finset.univ.sup' ⟨⟨0, hB⟩, Finset.mem_univ _⟩ (fun j => theta j ω) < theta0} := by
    rw [Set.disjoint_left]
    intro ω h1 h2
    simp only [Set.mem_setOf_eq] at h1 h2
    have hle : Finset.univ.inf' ⟨⟨0, hB⟩, Finset.mem_univ _⟩ (fun j => theta j ω)
        ≤ Finset.univ.sup' ⟨⟨0, hB⟩, Finset.mem_univ _⟩ (fun j => theta j ω) := by
      calc Finset.univ.inf' ⟨⟨0, hB⟩, Finset.mem_univ _⟩ (fun j => theta j ω)
          ≤ theta ⟨0, hB⟩ ω := Finset.inf'_le (fun j => theta j ω) (b := ⟨0, hB⟩) (Finset.mem_univ _)
        _ ≤ Finset.univ.sup' ⟨⟨0, hB⟩, Finset.mem_univ _⟩ (fun j => theta j ω) :=
            Finset.le_sup' (fun j => theta j ω) (b := ⟨0, hB⟩) (Finset.mem_univ _)
    linarith
  have hM : {ω : Ω | theta0 ∉ Set.Icc (Finset.univ.inf' ⟨⟨0, hB⟩, Finset.mem_univ _⟩ (fun j => theta j ω)) (Finset.univ.sup' ⟨⟨0, hB⟩, Finset.mem_univ _⟩ (fun j => theta j ω))}
      = {ω : Ω | theta0 < Finset.univ.inf' ⟨⟨0, hB⟩, Finset.mem_univ _⟩ (fun j => theta j ω)}
        ∪ {ω : Ω | Finset.univ.sup' ⟨⟨0, hB⟩, Finset.mem_univ _⟩ (fun j => theta j ω) < theta0} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Icc, not_and_or, not_le]
  rw [hM, MeasureTheory.measureReal_union hdisj hmeasB1, hA, hB1, hHreal, hLreal]
  ring


  /- @proof-region region.target-node.session.46e00bad1f71c871 end -/

end

end Statlib.Imported

