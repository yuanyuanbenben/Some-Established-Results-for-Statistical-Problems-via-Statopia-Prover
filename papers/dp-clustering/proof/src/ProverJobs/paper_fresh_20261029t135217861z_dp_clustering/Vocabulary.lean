import Mathlib

-- Shared append-only definitions for the root theorem and every Math node.
-- Node Formalize may add def/abbrev/structure/class/inductive declarations here.

/-- The translated kernel block `x ↦ g (x − θ)` viewed as a (finite) measure on `ℝ`, namely the
density `g (· − θ)` against Lebesgue measure. -/
noncomputable def dpMixBlock (g : ℝ → ℝ) (θ : ℝ) : MeasureTheory.Measure ℝ :=
  MeasureTheory.volume.withDensity (fun x : ℝ => ENNReal.ofReal (g (x - θ)))

/-- A finite translated kernel mixture `∑_l w_l • g(· − θ_l)` with weights `w` and locations
`θ`: a generic element of the `s`-atom family `{∑_{l : Fin s} w_l • g(· − φ_l)}`. -/
noncomputable def dpMixBlockSum (g : ℝ → ℝ) {s : ℕ} (w : Fin s → ℝ) (θ : Fin s → ℝ) :
    MeasureTheory.Measure ℝ :=
  ∑ l : Fin s, ENNReal.ofReal (w l) • dpMixBlock g (θ l)

/-- The stick-breaking mixture measure with `s` atoms, weights `w`, atom locations `θ` and
residual base-measure mass `B`:
`h = ∑_{l : Fin s} w_l • (volume.withDensity (ofReal ∘ g (· − θ_l))) + B • Q₀`,
where `Q₀ = volume.withDensity (ofReal ∘ q₀)` is the base measure. -/
noncomputable def dpStickMixture (g q0 : ℝ → ℝ) {s : ℕ} (w : Fin s → ℝ) (θ : Fin s → ℝ)
    (B : ℝ) : MeasureTheory.Measure ℝ :=
  dpMixBlockSum g w θ +
    ENNReal.ofReal B • MeasureTheory.volume.withDensity (fun x : ℝ => ENNReal.ofReal (q0 x))

/-- The family of translated kernel mixtures with fewer than `t` atoms and weights summing to at
most one — the family that the weak neighbourhood `U` of `P` is required to avoid. -/
def dpSmallMixFamily (g : ℝ → ℝ) (t : ℕ) : Set (MeasureTheory.Measure ℝ) :=
  {h | ∃ (s : ℕ) (w θ : Fin s → ℝ), s < t ∧ (∀ l, 0 ≤ w l) ∧ (∑ l, w l ≤ 1) ∧
      h = dpMixBlockSum g w θ}

/-- The event `{K_n < t}`: the mixture measure `h` has fewer than `t` atoms, i.e. it admits a
stick-breaking representation with `s < t` atoms, nonnegative weights `w`, atom locations `θ`
and nonnegative residual base-measure mass `B`. -/
def dpFewAtoms (g q0 : ℝ → ℝ) (t : ℕ) : Set (MeasureTheory.Measure ℝ) :=
  {h | ∃ (s : ℕ) (w θ : Fin s → ℝ) (B : ℝ), s < t ∧ (∀ l, 0 ≤ w l) ∧ 0 ≤ B ∧
      h = dpStickMixture g q0 w θ B}

/-- The stratum family `Strata s` (written `dpStrata g s`): the probability measures that are
genuine `s`-fold translated kernel mixtures `h = ∑_{l : Fin s} w l • g(· − φ l)` with strictly
positive weights `w` summing to one and pairwise distinct atom locations `φ`. -/
def dpStrata (g : ℝ → ℝ) (s : ℕ) : Set (MeasureTheory.Measure ℝ) :=
  {h | ∃ w : Fin s → ℝ, ∃ φ : Fin s → ℝ,
    (∀ l : Fin s, 0 < w l) ∧ (∑ l : Fin s, w l = 1) ∧
      (∀ l l' : Fin s, φ l = φ l' → l = l') ∧ h = dpMixBlockSum g w φ}
