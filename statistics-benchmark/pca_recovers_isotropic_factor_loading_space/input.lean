import Mathlib

open MeasureTheory Matrix

theorem pca_recovers_isotropic_factor_loading_space
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (d q : ℕ) (hd : 2 ≤ d) (hq₀ : 1 ≤ q) (hqd : q < d)
    (F : Ω → Fin q → ℝ)
    (epsilon : Ω → Fin d → ℝ)
    (hF_L2 : MemLp F 2 P)
    (hε_L2 : MemLp epsilon 2 P)
    (sigma : ℝ) (hsigma : 0 ≤ sigma)
    (hFmean : ∫ ω, F ω ∂P = 0)
    (hFcov : ∀ i j, ∫ ω, F ω i * F ω j ∂P =
      if i = j then 1 else 0)
    (hεmean : ∫ ω, epsilon ω ∂P = 0)
    (hεcov : ∀ i j, ∫ ω, epsilon ω i * epsilon ω j ∂P =
      if i = j then sigma ^ 2 else 0)
    (hcross : ∀ i j, ∫ ω, F ω i * epsilon ω j ∂P = 0)
    (Lambda : Matrix (Fin d) (Fin q) ℝ)
    (hLambda : Function.Injective Lambda.mulVec)
    (mu : Fin d → ℝ)
    (u : Fin d → Fin d → ℝ)
    (rho : Fin d → ℝ)
    (horth : ∀ j k, dotProduct (u j) (u k) = if j = k then 1 else 0)
    (hspan : Submodule.span ℝ (Set.range u) = ⊤) :
    let X : Ω → Fin d → ℝ := fun ω ↦
      mu + Lambda *ᵥ F ω + epsilon ω
    let Sigma : Matrix (Fin d) (Fin d) ℝ :=
      fun i j ↦ ∫ ω, (X ω - mu) i * (X ω - mu) j ∂P
    (∀ j, Sigma *ᵥ u j = rho j • u j) →
    Antitone rho →
      Submodule.span ℝ
          {w | ∃ j : Fin d, j.val < q ∧ w = u j} =
        Submodule.span ℝ
          (Set.range fun j : Fin q ↦ fun i : Fin d ↦ Lambda i j) := by
  sorry
