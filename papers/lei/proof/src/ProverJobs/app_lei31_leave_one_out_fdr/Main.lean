import Mathlib
import Mathlib
import ProverJobs.bh_showcase_workspace_seed_01.Main
import ProverJobs.bh_showcase_workspace_seed_06.Main

open MeasureTheory

namespace Statlib.MultipleTesting.Lei

theorem app_lei31_leave_one_out_fdr
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (hmuFin : IsFiniteMeasure mu) {m : Nat} (hm : 0 < m)
    (isNull : Fin m -> Prop) [DecidablePred isNull]
    (q : Real) (p : Omega -> Fin m -> Real)
    [forall omega,
      DecidablePred
        (fun i : Fin m => Statlib.MultipleTesting.bhReject (p omega) q i)]
    (excess : Real)
    (hinputs : leiBhLeaveOneOutFdrInputs mu isNull q p excess) :
    Statlib.MultipleTesting.fdr mu isNull
      (fun omega i => Statlib.MultipleTesting.bhReject (p omega) q i) <=
      q * (1 + excess) := by
  letI : IsFiniteMeasure mu := hmuFin
  exact lei_bh_fdr_le_q_mul_one_add_of_leave_one_out_inputs
    mu isNull q p excess hinputs

end Statlib.MultipleTesting.Lei
