import Mathlib

open MeasureTheory ProbabilityTheory

namespace Msc62GroundTruth

/-- The finite-design Lasso oracle bounds under a cone restricted eigenvalue. -/
theorem lasso_restricted_eigenvalue_rate
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (S : Finset (Fin n))
    (x : Fin m → Fin n → ℝ)
    (X : Fin m → Fin n → ℝ)
    (hX : ∀ i j, X i j = x i j)
    (sigmaHat : Matrix (Fin n) (Fin n) ℝ)
    (hSigmaHat : ∀ j k,
      sigmaHat j k = (1 / (m : ℝ)) * ∑ i : Fin m, X i j * X i k)
    (kappa Lambda B sigma lambda : ℝ)
    (hkappa : 0 < kappa) (hLambda : 0 < Lambda) (hB : 0 < B)
    (hsigma : 0 < sigma) (hlambda : 0 < lambda)
    (hRE : ∀ v : Fin n → ℝ,
      (∑ j ∈ Finset.univ.filter (fun j => j ∉ S), |v j|) ≤
        3 * (∑ j ∈ S, |v j|) →
      kappa ^ 2 * (∑ j : Fin n, (v j) ^ 2) ≤
        ∑ j : Fin n, ∑ k : Fin n, v j * sigmaHat j k * v k)
    (hUpper : ∀ v : Fin n → ℝ,
      (∑ j : Fin n, ∑ k : Fin n, v j * sigmaHat j k * v k) ≤
        Lambda * ∑ j : Fin n, (v j) ^ 2)
    (hscale : (m : ℝ) * Lambda ≤ B ^ 2)
    (epsilon : Fin m → Omega → ℝ)
    (h_epsilon_meas : ∀ i, Measurable (epsilon i))
    (h_epsilon_integrable : ∀ i, Integrable (epsilon i) P)
    (h_epsilon_indep : iIndepFun (β := fun _ : Fin m => ℝ) epsilon P)
    (h_epsilon_centered : ∀ i, ∫ omega, epsilon i omega ∂P = 0)
    (h_epsilon_exp_integrable : ∀ (i : Fin m) (t : ℝ),
      Integrable (fun omega => Real.exp (t * epsilon i omega)) P)
    (h_epsilon_subGaussian : ∀ (i : Fin m) (t : ℝ),
      ∫ omega, Real.exp (t * epsilon i omega) ∂P ≤
        Real.exp (sigma * t ^ 2 / 2))
    (betaStar : Fin n → ℝ)
    (h_support : ∀ j, j ∉ S → betaStar j = 0) :
    let score (omega : Omega) : Prop :=
      ∀ j : Fin n, |(1 / (m : ℝ)) * ∑ i : Fin m, X i j * epsilon i omega| ≤ lambda / 2
    let response (omega : Omega) (i : Fin m) : ℝ :=
      (∑ j : Fin n, X i j * betaStar j) + epsilon i omega
    let objective (omega : Omega) (beta : Fin n → ℝ) : ℝ :=
      (1 / (2 * (m : ℝ))) *
          ∑ i : Fin m, (response omega i - ∑ j : Fin n, X i j * beta j) ^ 2 +
        lambda * ∑ j : Fin n, |beta j|
    let lassoSolution (omega : Omega) (beta : Fin n → ℝ) : Prop :=
      ∀ gamma : Fin n → ℝ, objective omega beta ≤ objective omega gamma
    let oracleBounds (betaHat : Fin n → ℝ) : Prop :=
        (1 / (m : ℝ)) * ∑ i : Fin m,
            (∑ j : Fin n, X i j * (betaHat j - betaStar j)) ^ 2 ≤
              16 * lambda ^ 2 * (S.card : ℝ) / kappa ^ 2 ∧
        (∑ j : Fin n, |betaHat j - betaStar j|) ≤
              8 * lambda * (S.card : ℝ) / kappa ^ 2 ∧
        ∑ j : Fin n, (betaHat j - betaStar j) ^ 2 ≤
              16 * lambda ^ 2 * (S.card : ℝ) / kappa ^ 4
    (P {omega | score omega}).toReal ≥
        1 - 2 * (n : ℝ) * Real.exp (-((m : ℝ) ^ 2 * (lambda / 2) ^ 2) /
          (2 * sigma * B ^ 2)) ∧
      ∀ omega, score omega → ∀ betaHat : Fin n → ℝ,
        lassoSolution omega betaHat → oracleBounds betaHat := by
  sorry

end Msc62GroundTruth
