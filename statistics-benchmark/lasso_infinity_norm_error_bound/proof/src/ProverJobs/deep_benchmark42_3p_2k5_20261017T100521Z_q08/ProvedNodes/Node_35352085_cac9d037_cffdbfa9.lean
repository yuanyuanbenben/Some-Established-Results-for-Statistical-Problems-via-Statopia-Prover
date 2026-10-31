import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q08.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q08.Base

open MeasureTheory Matrix ProbabilityTheory

open MeasureTheory Matrix ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_35352085_cac9d037 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n)
    (sigma : ℝ) (hsigma : 0 < sigma)
    (w : Ω → Fin n → ℝ)
    (hw : ∀ a : Fin n → ℝ,
      HasLaw (fun ω ↦ dotProduct a (w ω))
        (gaussianReal 0
          (Real.toNNReal (sigma ^ 2 * dotProduct a a))) P),
    AEMeasurable w P := by
  /- @proof-region region.target-node.session.33a3c2f54eed7f29 begin -/
  intro Ω _ P _ n hn sigma hsigma w hw
  rw [aemeasurable_pi_iff]
  intro i
  obtain ⟨hmeas⟩ := hw (Pi.single i 1)
  have hfun : (fun ω => dotProduct (Pi.single i 1) (w ω)) = (fun ω => w ω i) := by
    funext ω
    simp
  rwa [hfun] at hmeas
  /- @proof-region region.target-node.session.33a3c2f54eed7f29 end -/
