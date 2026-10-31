import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q39.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q39.Base

open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_2868299895_3d47b682 : ∀ {X : Type*} [Fintype X] [DecidableEq X]
    (F : X → ℝ) (mu : X)
    (hmin : ∀ z : X, z ≠ mu → F mu < F z)
    (hC : (Finset.univ.erase mu).Nonempty),
    0 < (Finset.univ.erase mu).inf' hC (fun z => F z - F mu) ∧
      ∀ z : X, z ≠ mu →
        (Finset.univ.erase mu).inf' hC (fun z => F z - F mu) ≤ F z - F mu := by
  /- @proof-region region.target-node.session.f426afc0f1a1463c begin -/
  intro X _ _ F mu hmin hC
  have hpos : ∀ z ∈ Finset.univ.erase mu, 0 < F z - F mu := by
    intro z hz
    have hz' : z ≠ mu := (Finset.mem_erase.mp hz).1
    have hlt : F mu < F z := hmin z hz'
    linarith
  refine ⟨?_, ?_⟩
  · rw [Finset.lt_inf'_iff]
    exact hpos
  · intro z hz
    exact Finset.inf'_le (fun z => F z - F mu) (by simp [Finset.mem_erase, hz])
  /- @proof-region region.target-node.session.f426afc0f1a1463c end -/
