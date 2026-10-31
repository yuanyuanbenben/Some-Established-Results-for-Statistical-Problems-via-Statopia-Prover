import Mathlib
import Mathlib
import ProverJobs.bh_showcase_workspace_seed_01.Main
import ProverJobs.bh_showcase_workspace_seed_07.Main

namespace Statlib.MultipleTesting.Lei

theorem app_lei31_tail_ratio_excess
    (q pi0 u_q excess tailLoss scaleLoss : Real)
    (hcomponents :
      leiTailRatioExcessComponents q pi0 u_q excess tailLoss scaleLoss) :
    excess <= leiCommonFactorExcessBudget q pi0 u_q := by
  exact lei_common_factor_excess_bound_of_tail_ratio_components
    q pi0 u_q excess tailLoss scaleLoss hcomponents

end Statlib.MultipleTesting.Lei
