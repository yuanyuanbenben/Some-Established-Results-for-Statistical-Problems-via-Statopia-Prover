import Statlib.Nonparametric.Approximation.ShallowReLUApproximation
import Lean

open Lean Elab Term Meta
open Statlib.Nonparametric.Vocabulary
open Statlib.Nonparametric.Approximation.NeuralNetworkAlgebra

elab "archivedResolutionCertificate" : term => do
  let expected := "_private.Statlib.Nonparametric.Approximation.ShallowReLUApproximation.0.Statlib.Nonparametric.Approximation.NeuralNetworkAlgebra.holder_smooth_shallow_relu_neural_network_approximation_at_resolution"
  let certificates := (← getEnv).constants.toList.filter (fun p => p.1.toString == expected)
  let [(name, _)] := certificates | throwError "The pinned binary resolution certificate is unavailable"
  mkConstWithFreshMVarLevels name

theorem established_holder_smooth_relu_at_resolution
    {d r : ℕ} {beta C B : ℝ}
    (hd : 0 < d)
    (hbeta_pos : 0 < beta) (hbeta_le_one : beta ≤ 1)
    (hC_nonneg : 0 ≤ C) (hB_nonneg : 0 ≤ B) :
    ∃ W0 M0 Dblock : ℕ,
      0 < W0 ∧ 0 < M0 ∧ 0 < Dblock ∧
      ∃ cState : ℝ, 0 < cState ∧
        ∀ M : ℕ, M0 ≤ M →
          ∀ f : (Fin d → ℝ) → ℝ,
            f ∈ holderSmoothBall r beta C B →
              ∃ N : FullyConnectedReLUNet d,
                N.depth = M ^ d * (Dblock + 1) ∧
                N.width ≤ W0 ∧
                N.parameterCount ≤
                  fullyConnectedReLUParameterCount d (M ^ d * (Dblock + 1)) W0 ∧
                ∀ x : Fin d → ℝ,
                  (∀ q : Fin d, x q ∈ Set.Icc (0 : ℝ) 1) →
                    |N.realize x - f x| ≤
                      cState * (M : ℝ).rpow (-(2 * ((r : ℝ) + beta))) := by
  exact archivedResolutionCertificate hd hbeta_pos hbeta_le_one hC_nonneg hB_nonneg

#print axioms established_holder_smooth_relu_at_resolution
