import ProverJobs.job_paper_4f562633bddc4ee9afee32ec40dfa0f0.Vocabulary
import ProverJobs.job_paper_4f562633bddc4ee9afee32ec40dfa0f0.ProvedNodes
import ProverJobs.job_paper_4f562633bddc4ee9afee32ec40dfa0f0.Base

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Statlib.Imported

theorem paper_4f562633bddc4ee9afee32ec40dfa0f0
    (d : ℕ)
    (P Q : Kernel (MHState d) (MHState d)) [IsMarkovKernel P] [IsMarkovKernel Q]
    (pi : Measure (MHState d)) [IsFiniteMeasure pi]
    (piDens : MHState d → ℝ≥0∞) (q : MHState d → MHState d → ℝ≥0∞)
    (hpi : pi = volume.withDensity piDens)
    (hq : ∀ x, Q x = volume.withDensity (q x)) :
    IsMHType P Q piDens q ↔
      ∀ (x : MHState d) (A : Set (MHState d)), MeasurableSet A →
        (P x) A = ∫⁻ y in A, mhAccept piDens q x y ∂(Q x)
          + mhRejection Q piDens q x * (Measure.dirac x) A
:= by
  /- @proof-region region.root.116ee1f97112 begin -/
  constructor
  · rintro h x A hA
    rw [h x]
    rw [Measure.add_apply, MeasureTheory.withDensity_apply _ hA, Measure.smul_apply,
      smul_eq_mul]
  · intro h x
    ext A hA
    rw [h x A hA, Measure.add_apply, MeasureTheory.withDensity_apply _ hA,
      Measure.smul_apply, smul_eq_mul]
  /- @proof-region region.root.116ee1f97112 end -/

end Statlib.Imported
