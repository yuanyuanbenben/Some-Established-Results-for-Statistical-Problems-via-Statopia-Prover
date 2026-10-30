import ProverJobs.job_paper_53e951f48c854f4db91e6ecda697ee2b.Vocabulary
import ProverJobs.job_paper_53e951f48c854f4db91e6ecda697ee2b.Base

namespace PaperProofTasks.job_paper_53e951f48c854f4db91e6ecda697ee2b

open Filter Topology MeasureTheory
open scoped Topology ENNReal
open _root_.PaperProofTasks.job_paper_53e951f48c854f4db91e6ecda697ee2b.Statlib.Imported

noncomputable section
open Filter Topology MeasureTheory
open scoped Topology ENNReal
namespace Statlib.Imported
open _root_.Statlib

set_option autoImplicit false in
theorem statopia_math_node_204287509_2babc882 : ∀ (d : ℕ) (U : HMCState d → ℝ)
    (ε : ℝ) (hε : 0 < ε) (L : ℕ) (hL : 1 ≤ L) (x0 p0 : HMCState d),
    
    (∀ i : ℕ,
        leapfrogPosition U ε (i + 1) x0 p0
          = leapfrogPosition U ε i x0 p0
            + ε • (leapfrogMomentum U ε i x0 p0
              - (ε / 2) • gradient U (leapfrogPosition U ε i x0 p0))) ∧
    
      (∀ i : ℕ,
        leapfrogMomentum U ε (i + 1) x0 p0
          = (leapfrogMomentum U ε i x0 p0
              - (ε / 2) • gradient U (leapfrogPosition U ε i x0 p0))
            - (ε / 2) • gradient U (leapfrogPosition U ε (i + 1) x0 p0)) ∧
    
      (∀ i : ℕ,
        leapfrogMomentum U ε (i + 1) x0 p0
            - (ε / 2) • gradient U (leapfrogPosition U ε (i + 1) x0 p0)
          = (leapfrogMomentum U ε i x0 p0
              - (ε / 2) • gradient U (leapfrogPosition U ε i x0 p0))
            - ε • gradient U (leapfrogPosition U ε (i + 1) x0 p0)) ∧
    
      leapfrogMomentum U ε L x0 p0
          = (leapfrogMomentum U ε (L - 1) x0 p0
              - (ε / 2) • gradient U (leapfrogPosition U ε (L - 1) x0 p0))
            - (ε / 2) • gradient U (leapfrogPosition U ε L x0 p0) ∧
    
      (leapfrogMomentum U ε (L - 1) x0 p0
              - (ε / 2) • gradient U (leapfrogPosition U ε (L - 1) x0 p0)
          = ε⁻¹ • (leapfrogPosition U ε L x0 p0 - leapfrogPosition U ε (L - 1) x0 p0)) ∧
    
      leapfrogMomentum U ε L x0 p0
          = ε⁻¹ • (leapfrogPosition U ε L x0 p0 - leapfrogPosition U ε (L - 1) x0 p0)
            - (ε / 2) • gradient U (leapfrogPosition U ε L x0 p0) ∧
    
      ‖leapfrogMomentum U ε L x0 p0‖
        ≥ (ε / 2) * ‖gradient U (leapfrogPosition U ε L x0 p0)‖
          - (1 / ε) * ‖leapfrogPosition U ε L x0 p0
              - leapfrogPosition U ε (L - 1) x0 p0‖ := by
  /- @proof-region region.target-node.session.4ebbb07f5c4682db begin -/
  intro d U ε hε L hL x0 p0
  have hA : ∀ i : ℕ, (leapfrogStep U ε)^[i + 1] (x0, p0)
      = (leapfrogStep U ε)^[i] (leapfrogStep U ε (x0, p0)) := fun i => by simp
  have hB : ∀ (i : ℕ) (a : HMCState d × HMCState d),
      (leapfrogStep U ε)^[i] (leapfrogStep U ε a)
        = leapfrogStep U ε ((leapfrogStep U ε)^[i] a) := by
    intro i
    induction i with
    | zero => intro a; rfl
    | succ k ih => intro a; simp [ih]
  have hiter : ∀ i : ℕ, (leapfrogStep U ε)^[i + 1] (x0, p0)
      = leapfrogStep U ε ((leapfrogStep U ε)^[i] (x0, p0)) := by
    intro i
    rw [hA i, hB i]
  have hpos : ∀ i : ℕ,
      leapfrogPosition U ε (i + 1) x0 p0
        = leapfrogPosition U ε i x0 p0
          + ε • (leapfrogMomentum U ε i x0 p0
            - (ε / 2) • gradient U (leapfrogPosition U ε i x0 p0)) := by
    intro i
    simp only [leapfrogPosition, leapfrogMomentum, hiter i, leapfrogStep]
  have hmom : ∀ i : ℕ,
      leapfrogMomentum U ε (i + 1) x0 p0
        = (leapfrogMomentum U ε i x0 p0
            - (ε / 2) • gradient U (leapfrogPosition U ε i x0 p0))
          - (ε / 2) • gradient U (leapfrogPosition U ε (i + 1) x0 p0) := by
    intro i
    simp only [leapfrogPosition, leapfrogMomentum, hiter i, leapfrogStep]
  have hq : ∀ i : ℕ,
      leapfrogMomentum U ε (i + 1) x0 p0
          - (ε / 2) • gradient U (leapfrogPosition U ε (i + 1) x0 p0)
        = (leapfrogMomentum U ε i x0 p0
            - (ε / 2) • gradient U (leapfrogPosition U ε i x0 p0))
          - ε • gradient U (leapfrogPosition U ε (i + 1) x0 p0) := by
    intro i
    have hsplit : ε • gradient U (leapfrogPosition U ε (i + 1) x0 p0)
        = (ε / 2) • gradient U (leapfrogPosition U ε (i + 1) x0 p0)
          + (ε / 2) • gradient U (leapfrogPosition U ε (i + 1) x0 p0) := by
      rw [← add_smul, show ε / 2 + ε / 2 = ε from by ring]
    rw [hmom i, hsplit]
    abel
  have hLm : L - 1 + 1 = L := Nat.sub_add_cancel hL
  have hlast : leapfrogMomentum U ε L x0 p0
      = (leapfrogMomentum U ε (L - 1) x0 p0
          - (ε / 2) • gradient U (leapfrogPosition U ε (L - 1) x0 p0))
        - (ε / 2) • gradient U (leapfrogPosition U ε L x0 p0) := by
    have h := hmom (L - 1)
    rwa [hLm] at h
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hqL : leapfrogMomentum U ε (L - 1) x0 p0
          - (ε / 2) • gradient U (leapfrogPosition U ε (L - 1) x0 p0)
        = ε⁻¹ • (leapfrogPosition U ε L x0 p0 - leapfrogPosition U ε (L - 1) x0 p0) := by
    have h2 : ε • (leapfrogMomentum U ε (L - 1) x0 p0
          - (ε / 2) • gradient U (leapfrogPosition U ε (L - 1) x0 p0))
        = leapfrogPosition U ε L x0 p0 - leapfrogPosition U ε (L - 1) x0 p0 := by
      have h1 := hpos (L - 1)
      rw [hLm] at h1
      rw [h1]
      abel
    rw [← h2, smul_smul, inv_mul_cancel₀ hεne, one_smul]
  have hmain : leapfrogMomentum U ε L x0 p0
      = ε⁻¹ • (leapfrogPosition U ε L x0 p0 - leapfrogPosition U ε (L - 1) x0 p0)
        - (ε / 2) • gradient U (leapfrogPosition U ε L x0 p0) := by
    rw [hlast, hqL]
  have hbound : ‖leapfrogMomentum U ε L x0 p0‖
      ≥ (ε / 2) * ‖gradient U (leapfrogPosition U ε L x0 p0)‖
        - (1 / ε) * ‖leapfrogPosition U ε L x0 p0
            - leapfrogPosition U ε (L - 1) x0 p0‖ := by
    rw [hmain, norm_sub_rev]
    have htri := norm_sub_norm_le
      ((ε / 2) • gradient U (leapfrogPosition U ε L x0 p0))
      (ε⁻¹ • (leapfrogPosition U ε L x0 p0 - leapfrogPosition U ε (L - 1) x0 p0))
    have hc : ‖(ε / 2) • gradient U (leapfrogPosition U ε L x0 p0)‖
        = (ε / 2) * ‖gradient U (leapfrogPosition U ε L x0 p0)‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ ε / 2)]
    have hw : ‖ε⁻¹ • (leapfrogPosition U ε L x0 p0
          - leapfrogPosition U ε (L - 1) x0 p0)‖
        = (1 / ε) * ‖leapfrogPosition U ε L x0 p0
            - leapfrogPosition U ε (L - 1) x0 p0‖ := by
      rw [norm_smul, Real.norm_of_nonneg (le_of_lt (inv_pos.mpr hε)), one_div]
    rw [hc, hw] at htri
    linarith
  exact ⟨hpos, hmom, hq, hlast, hqL, hmain, hbound⟩
  /- @proof-region region.target-node.session.4ebbb07f5c4682db end -/

end Statlib.Imported
end

