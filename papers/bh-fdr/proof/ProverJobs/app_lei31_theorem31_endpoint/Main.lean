import Mathlib
import Statlib
import ProverJobs.bh_showcase_workspace_seed_01.Main
import ProverJobs.bh_showcase_workspace_seed_15.Main
import ProverJobs.app_lei31_leave_one_out_fdr.Main
import ProverJobs.app_lei31_tail_ratio_excess.Main

open MeasureTheory

namespace Statlib.MultipleTesting.Lei

theorem app_lei31_theorem31_endpoint
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (hmuFin : IsFiniteMeasure mu) {m : Nat} (hm : 0 < m)
    (isNull : Fin m -> Prop) [DecidablePred isNull]
    (q : Real) (p : Omega -> Fin m -> Real)
    (hp_meas : forall i, Measurable fun omega => p omega i)
    [forall omega : Omega,
      DecidablePred
        (fun i : Fin m => Statlib.MultipleTesting.bhReject (p omega) q i)]
    (tail : Real -> Real) (m0 : Nat)
    (pi0 u_q excess tailLoss scaleLoss : Real)
    (hqdomain : leiTheorem31QDomain tail q u_q)
    (hfrac : leiTheorem31NullFraction m m0 pi0)
    (hlo : leiBhLeaveOneOutFdrInputs mu isNull q p excess)
    (htailratio :
      leiTailRatioExcessComponents q pi0 u_q excess tailLoss scaleLoss) :
    Statlib.MultipleTesting.fdr mu isNull
      (fun omega i => Statlib.MultipleTesting.bhReject (p omega) q i) <=
      leiCommonFactorFdrRhs q pi0 u_q := by
  letI : IsFiniteMeasure mu := hmuFin
  have hfdr :
      Statlib.MultipleTesting.fdr mu isNull
        (fun omega i => Statlib.MultipleTesting.bhReject (p omega) q i) <=
        q * (1 + excess) := by
    exact app_lei31_leave_one_out_fdr mu hmuFin hm isNull q p excess hlo
  have hexcess : excess <= leiCommonFactorExcessBudget q pi0 u_q := by
    exact app_lei31_tail_ratio_excess
      q pi0 u_q excess tailLoss scaleLoss htailratio
  exact lei_theorem31_explicit_bh_fdr_app_display
    mu isNull q p tail m0 pi0 u_q excess hqdomain hfrac hfdr hexcess

end Statlib.MultipleTesting.Lei
