import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M000_Vocabulary
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M001_Base

/- Original module ProverJobs.job_paper_dc88427b52844263b5321fc99eb582d8.ProvedNodes.Node_2617779308_f5c0b9ed_355a9ee0; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported

open Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_2617779308_f5c0b9ed : ∀ (kappa : ℝ) (hkappa_nonneg : 0 ≤ kappa) (hkappa_lt_one : kappa < 1)
    (b : ℝ)
    (hb : b = ⨆ a : Set.Ici (1 : ℝ), (a : ℝ) ^ ((3 : ℝ) / 2) * kappa ^ (a : ℝ))
    (p : ℕ) (hp : 1 ≤ p),
    ((p : ℝ)) ^ ((3 : ℝ) / 2) * kappa ^ ((p : ℝ)) ≤ b := by
  /- @proof-region region.target-node.session.915d81d6cdbf8b6e begin -/
  intro kappa hkappa_nonneg hkappa_lt b hb p hp
  have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  haveI : Nonempty (Set.Ici (1:ℝ)) := ⟨⟨1, by simp⟩⟩
  have memIci : ∀ {x : ℝ}, x ∈ Set.Ici (1:ℝ) → (1:ℝ) ≤ x := by
    intro x hx
    first
      | exact hx
      | (dsimp only [Set.Ici] at hx; exact hx)
  have memIci' : ∀ {x : ℝ}, (1:ℝ) ≤ x → x ∈ Set.Ici (1:ℝ) := by
    intro x hx
    first
      | exact hx
      | (dsimp only [Set.Ici]; exact hx)
  have hbdd : BddAbove (Set.range (fun a : Set.Ici (1:ℝ) => (a:ℝ) ^ ((3:ℝ)/2) * kappa ^ (a:ℝ))) := by
    rcases eq_or_lt_of_le hkappa_nonneg with h0 | hpos
    · obtain rfl : kappa = 0 := h0.symm
      refine ⟨0, ?_⟩
      rintro x ⟨a, rfl⟩
      have ha0 : (a:ℝ) ≠ 0 := by
        have h : (1:ℝ) ≤ (a:ℝ) := memIci a.2
        linarith
      simp [Real.zero_rpow, ha0]
    · set c : ℝ := -Real.log kappa with hcdef
      have hclog : Real.log kappa = -c := by
        rw [hcdef]
        ring
      have hcpos : 0 < c := by
        have hneg : Real.log kappa < 0 := Real.log_neg hpos hkappa_lt
        rw [hcdef]
        linarith
      refine ⟨Real.exp (-(3/2) - (3/2) * Real.log (2*c/3)), ?_⟩
      rintro x ⟨a, rfl⟩
      have ha1 : (1:ℝ) ≤ (a:ℝ) := memIci a.2
      have ha0 : (0:ℝ) < (a:ℝ) := by linarith
      have h2c3 : (0:ℝ) < 2*c/3 := by linarith
      have hposr : (0:ℝ) < (a:ℝ) ^ ((3:ℝ)/2) := Real.rpow_pos_of_pos ha0 _
      have hposk : (0:ℝ) < kappa ^ (a:ℝ) := Real.rpow_pos_of_pos hpos _
      have hfpos : 0 < (a:ℝ) ^ ((3:ℝ)/2) * kappa ^ (a:ℝ) := mul_pos hposr hposk
      have hlog : Real.log ((a:ℝ) ^ ((3:ℝ)/2) * kappa ^ (a:ℝ))
          = (3/2) * Real.log (a:ℝ) + Real.log kappa * (a:ℝ) := by
        rw [Real.log_mul (ne_of_gt hposr) (ne_of_gt hposk), Real.log_rpow ha0, Real.log_rpow hpos]
        ring
      have hprod : (a:ℝ) ^ ((3:ℝ)/2) * kappa ^ (a:ℝ)
          = Real.exp ((3/2) * Real.log (a:ℝ) + Real.log kappa * (a:ℝ)) :=
        (Real.exp_log hfpos).symm.trans (congrArg Real.exp hlog)
      have hle : Real.log (2*c/3 * (a:ℝ)) ≤ 2*c/3 * (a:ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (mul_pos h2c3 ha0)
      have hsplit : Real.log (2*c/3 * (a:ℝ)) = Real.log (2*c/3) + Real.log (a:ℝ) :=
        Real.log_mul (ne_of_gt h2c3) (ne_of_gt ha0)
      have hloga : Real.log (a:ℝ) ≤ 2*c/3 * (a:ℝ) - 1 - Real.log (2*c/3) := by linarith
      have hmain : (3/2) * Real.log (a:ℝ) ≤ c * (a:ℝ) - 3/2 - (3/2) * Real.log (2*c/3) := by
        linarith
      have hka : Real.log kappa * (a:ℝ) = -c * (a:ℝ) := by rw [hclog]
      have hexp : (3/2) * Real.log (a:ℝ) + Real.log kappa * (a:ℝ)
          ≤ -(3/2) - (3/2) * Real.log (2*c/3) := by
        rw [hka]
        linarith
      calc (a:ℝ) ^ ((3:ℝ)/2) * kappa ^ (a:ℝ)
          = Real.exp ((3/2) * Real.log (a:ℝ) + Real.log kappa * (a:ℝ)) := hprod
        _ ≤ Real.exp (-(3/2) - (3/2) * Real.log (2*c/3)) := Real.exp_le_exp.mpr hexp
  have key : ((p:ℝ)) ^ ((3:ℝ)/2) * kappa ^ ((p:ℝ))
      ≤ ⨆ a : Set.Ici (1:ℝ), (a:ℝ) ^ ((3:ℝ)/2) * kappa ^ (a:ℝ) :=
    le_ciSup hbdd ⟨(p:ℝ), hp1⟩
  rw [hb]
  exact key
  /- @proof-region region.target-node.session.915d81d6cdbf8b6e end -/

end

end Statlib.Imported
end DPCompletedProof
