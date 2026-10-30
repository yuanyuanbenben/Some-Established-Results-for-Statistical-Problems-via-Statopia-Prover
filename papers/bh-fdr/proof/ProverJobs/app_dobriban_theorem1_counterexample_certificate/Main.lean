import Mathlib
import Statlib
import ProverJobs.bh_showcase_workspace_seed_01.Main
import ProverJobs.bh_showcase_workspace_seed_02.Main
import ProverJobs.bh_showcase_workspace_seed_05.Main

open Filter

namespace Statlib.MultipleTesting.Dobriban

theorem app_dobriban_theorem1_counterexample_certificate
    {H_N : Nat -> Real -> Real}
    {H : Real -> Real}
    {cutoff fdrN : Nat -> Real}
    {cMinus cPlus eps : Real}
    (h_eps : 0 < eps)
    (h_left : H cMinus <= -eps)
    (h_right : eps <= H cPlus)
    (h_uniform :
      Filter.Eventually
        (fun N : Nat =>
          |H_N N cMinus - H cMinus| < eps /\
            |H_N N cPlus - H cPlus| < eps)
        Filter.atTop)
    (h_bracket_of_signs :
      Filter.Eventually
        (fun N : Nat =>
          (H_N N cMinus < 0 /\ 0 < H_N N cPlus) ->
            (cMinus <= cutoff N /\ cutoff N <= cPlus))
        Filter.atTop)
    (h_fdp_of_bracket :
      Filter.Eventually
        (fun N : Nat =>
          (cMinus <= cutoff N /\ cutoff N <= cPlus) ->
            (104168290704737131174725663852504915 : Real) /
              (10 : Real) ^ 37 <= fdrN N)
        Filter.atTop) :
    (exists margin : Real,
      0 < margin /\
        Filter.Eventually
          (fun N : Nat => (1 : Real) / 100 + margin < fdrN N)
          Filter.atTop) /\
    ((104 : Real) / 10000 < AppendixB.dobribanAppendixBFullCertificateRealFloor /\
      (1 : Real) / 100 < AppendixB.dobribanAppendixBFullCertificateRealFloor) := by
  exact And.intro
      (dobriban_bh_fdr_counterexample_from_appendix_b_certificate
        h_eps h_left h_right h_uniform h_bracket_of_signs h_fdp_of_bracket)
      AppendixB.dobriban_appendix_b_full_certificate_floor_closed
  
  If the prover has split the root goal into local subgoals, use the same
  two workspace calls on the corresponding subgoal:
  
    exact dobriban_bh_fdr_counterexample_from_appendix_b_certificate
      h_eps h_left h_right h_uniform h_bracket_of_signs h_fdp_of_bracket
  
    exact AppendixB.dobriban_appendix_b_full_certificate_floor_closed

end Statlib.MultipleTesting.Dobriban
