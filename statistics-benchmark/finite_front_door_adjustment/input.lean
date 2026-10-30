import Mathlib

open scoped BigOperators

theorem finite_front_door_adjustment
    (U X Z Y : Type*)
    [Fintype U] [Nonempty U]
    [Fintype X] [Nonempty X]
    [Fintype Z] [Nonempty Z]
    [Fintype Y] [Nonempty Y]
    (pU : U → ℝ)
    (pXgivenU : X → U → ℝ)
    (pZgivenX : Z → X → ℝ)
    (pYgivenZU : Y → Z → U → ℝ)
    (hpUpos : ∀ u, 0 < pU u)
    (hpXUpos : ∀ x u, 0 < pXgivenU x u)
    (hpZXpos : ∀ z x, 0 < pZgivenX z x)
    (hpYZUpos : ∀ y z u, 0 < pYgivenZU y z u)
    (hpUsum : ∑ u, pU u = 1)
    (hpXUsum : ∀ u, ∑ x, pXgivenU x u = 1)
    (hpZXsum : ∀ x, ∑ z, pZgivenX z x = 1)
    (hpYZUsum : ∀ z u, ∑ y, pYgivenZU y z u = 1) :
    let pX : X → ℝ := fun x ↦ ∑ u, pU u * pXgivenU x u
    let pYgivenXZ : Y → X → Z → ℝ := fun y x z ↦
      (∑ u, pU u * pXgivenU x u * pYgivenZU y z u) / pX x
    let pDo : X → Y → ℝ := fun x y ↦
      ∑ z, ∑ u, pU u * pZgivenX z x * pYgivenZU y z u
    ∀ x y,
      pDo x y =
        ∑ z, pZgivenX z x * ∑ x', pYgivenXZ y x' z * pX x' := by
  sorry
