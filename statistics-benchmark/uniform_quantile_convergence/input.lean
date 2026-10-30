import Mathlib

open Filter MeasureTheory
open scoped Topology

theorem uniform_quantile_convergence
    {U : Type*} [Nonempty U]
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (F : U → StieltjesFunction ℝ)
    (Fr : ℕ → U → StieltjesFunction ℝ)
    (hF_bot : ∀ u, Tendsto (F u) atBot (nhds 0))
    (hF_top : ∀ u, Tendsto (F u) atTop (nhds 1))
    (hFr_bot : ∀ r u, Tendsto (Fr r u) atBot (nhds 0))
    (hFr_top : ∀ r u, Tendsto (Fr r u) atTop (nhds 1))
    (hunif : Tendsto
      (fun r ↦ ⨆ u : U, ⨆ x : ℝ, |Fr r u x - F u x|)
      atTop (nhds 0)) :
    let q : U → ℝ := fun u ↦ sInf {x : ℝ | p ≤ F u x}
    let qr : ℕ → U → ℝ := fun r u ↦ sInf {x : ℝ | p ≤ Fr r u x}
    (∀ δ : ℝ, 0 < δ → ∃ eta : ℝ, 0 < eta ∧
      ∀ u, F u (q u - δ) ≤ p - eta ∧ p + eta ≤ F u (q u + δ)) →
      Tendsto (fun r ↦ ⨆ u : U, |qr r u - q u|) atTop (nhds 0) := by
  sorry
