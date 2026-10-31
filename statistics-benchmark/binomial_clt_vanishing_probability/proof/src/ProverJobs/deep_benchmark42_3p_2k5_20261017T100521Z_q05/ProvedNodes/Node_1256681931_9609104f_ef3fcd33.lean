import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q05.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q05.Base

open MeasureTheory ProbabilityTheory Filter
open Msc62GroundTruth

open MeasureTheory ProbabilityTheory Filter
namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_1256681931_9609104f : ∀ (ν : Measure ℝ) [IsFiniteMeasure ν] (a b t : ℝ),
    charFun (Measure.map (fun y : ℝ => a * y + b) ν) t =
      Complex.exp (Complex.I * ((b * t : ℝ) : ℂ)) * charFun ν (a * t) := by
  /- @proof-region region.target-node.session.f86efaf4590b69a8 begin -/
  intro ν hν a b t
  rw [MeasureTheory.charFun_apply_real, MeasureTheory.charFun_apply_real]
  have hmap :
      ∫ (z : ℝ), Complex.exp ((t : ℂ) * (z : ℂ) * Complex.I)
          ∂Measure.map (fun y : ℝ => a * y + b) ν
        = ∫ (y : ℝ), Complex.exp ((t : ℂ) * ((a * y + b : ℝ) : ℂ) * Complex.I) ∂ν :=
    integral_map (by fun_prop) (by fun_prop)
  rw [hmap]
  rw [← MeasureTheory.integral_const_mul]
  have hpt : ∀ y : ℝ,
      Complex.exp ((t : ℂ) * ((a * y + b : ℝ) : ℂ) * Complex.I) =
        Complex.exp (Complex.I * ((b * t : ℝ) : ℂ)) *
          Complex.exp (((a * t : ℝ) : ℂ) * (y : ℂ) * Complex.I) := by
    intro y
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [hpt]
  /- @proof-region region.target-node.session.f86efaf4590b69a8 end -/

end Msc62GroundTruth
