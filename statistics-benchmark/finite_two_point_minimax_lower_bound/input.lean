import Mathlib

open scoped BigOperators

theorem finite_two_point_minimax_lower_bound
    {Θ : Type*}
    [MetricSpace Θ]
    (N : ℕ)
    (hN : 1 ≤ N)
    (p0 p1 : Fin N → ℝ)
    (hp0_nonneg : ∀ x, 0 ≤ p0 x)
    (hp0_le_one : ∀ x, p0 x ≤ 1)
    (hp1_nonneg : ∀ x, 0 ≤ p1 x)
    (hp1_le_one : ∀ x, p1 x ≤ 1)
    (hp0_sum : ∑ x, p0 x = 1)
    (hp1_sum : ∑ x, p1 x = 1)
    (θ0 θ1 : Θ)
    (hθ : 0 < dist θ0 θ1)
    (T : Fin N → Θ) :
    let V : ℝ := (2 : ℝ)⁻¹ * ∑ x, |p0 x - p1 x|
    let R0 : ℝ := ∑ x, p0 x * dist (T x) θ0 ^ 2
    let R1 : ℝ := ∑ x, p1 x * dist (T x) θ1 ^ 2
    max R0 R1 ≥ dist θ0 θ1 ^ 2 / 8 * (1 - V) := by
  sorry
