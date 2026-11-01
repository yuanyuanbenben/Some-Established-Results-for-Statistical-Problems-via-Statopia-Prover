import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M042_Candidate
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M031_Vocabulary
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M032_Base
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M033_Node_1445702134_3c8d3810_8f7a15fe
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M037_Node_1797268609_53e08000_06dbe633
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M034_Node_3224678180_5a630a9f_7124eef7
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M036_Node_3788355289_2a3e6b7e_b3f2870a

/- Original module ProverJobs.manual_dp_prior_finish_20261031.TailBound; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported
open MeasureTheory
open Statlib.Imported

noncomputable section
open MeasureTheory
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_3130454126_6f827a50 : ∀ (t : ℝ) (ht : 1 ≤ t)
    (π : ℝ → ℝ) (hπ_meas : Measurable π)
    (hπ_nonneg : ∀ α ∈ Set.Ioi (0 : ℝ), 0 ≤ π α)
    (hπ_prob : ∫⁻ α in Set.Ioi (0 : ℝ), ENNReal.ofReal (π α) = 1)
    (ε₀ δ β : ℝ) (hε₀ : 0 < ε₀) (hδ : 0 < δ) (hβ : 0 < β)
    (hA2 : ∀ α ∈ Set.Ioo (0 : ℝ) ε₀, δ⁻¹ * α ^ β ≤ π α ∧ π α ≤ δ * α ^ β)
    (ε : ℝ) (hε : 0 < ε) (hε_lt : ε < 1 / 2) (hε_le : ε ≤ ε₀)
    (hB1 : δ * ε ^ (β + 1) / (β + 1) ≤ 1 / 2)
    (n s : ℕ) (hs : 1 ≤ s) (hns : (s : ℝ) + t ≤ (n : ℝ)),
    ENNReal.ofReal (∫ α in Set.Ioi ε, α ^ (t + (s : ℝ)) / risingFac α n * π α) ≤
      (ENNReal.ofReal (Gconst t ε δ β * (s : ℝ) / ε ^ s) *
          priorMoment π (t + (s : ℝ) - 1) *
          ENNReal.ofReal
            (lowerGamma (t + (s : ℝ) + β) (ε * Real.log (n : ℝ)) /
              (Real.log ((n : ℝ) / (1 + ε))) ^ s)) *
        ENNReal.ofReal (∫ α in Set.Ioi ε, α ^ t / risingFac α n * π α) +
      ((3 : ENNReal) / 4) *
        (ENNReal.ofReal (Gconst t ε δ β * (s : ℝ) / ε ^ s) *
          priorMoment π (t + (s : ℝ) - 1) *
          ENNReal.ofReal
            (lowerGamma (t + (s : ℝ) + β) (ε * Real.log (n : ℝ)) /
              (Real.log ((n : ℝ) / (1 + ε))) ^ s)) *
        ENNReal.ofReal (∫ α in Set.Ioo (0 : ℝ) ε, α ^ t / risingFac α n * π α) := by
  /- @proof-region region.target-node.session.472ea278b03ef157 begin -/
  intro t ht π hπ_meas hπ_nonneg hπ_prob ε₀ δ β hε₀ hδ hβ hA2 ε hε hε_lt hε_le hB1 n s hs hns
  have hA2ε : ∀ α ∈ Set.Ioo (0 : ℝ) ε, δ⁻¹ * α ^ β ≤ π α ∧ π α ≤ δ * α ^ β := by
    intro α hα
    exact hA2 α ⟨hα.1, lt_of_lt_of_le hα.2 hε_le⟩
  obtain ⟨-, -, -, hBpos, -, -, -, hBt0, -⟩ :=
    statopia_math_node_3788355289_2a3e6b7e t ht π hπ_meas hπ_nonneg hπ_prob ε δ β hε hδ hβ hA2ε n s hs hns
  have hn2 : 2 ≤ n := by
    have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
    have h2 : (2 : ℝ) ≤ (s : ℝ) + t := by linarith
    have h3 : (2 : ℝ) ≤ (n : ℝ) := le_trans h2 hns
    exact_mod_cast h3
  have hnR : (1 : ℝ) < (n : ℝ) := by
    have h3 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    linarith
  have hlogpos : 0 < Real.log ((n : ℝ) / (1 + ε)) := by
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    have h10 : (0 : ℝ) < 1 + ε := by linarith
    rw [Real.log_div (ne_of_gt hn0) (ne_of_gt h10)]
    have h3 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    have hlt : Real.log (1 + ε) < Real.log (n : ℝ) :=
      Real.log_lt_log h10 (by linarith)
    linarith
  have hgampos : 0 < lowerGamma (t + (s : ℝ) + β) (ε * Real.log (n : ℝ)) := by
    refine (statopia_math_node_3224678180_5a630a9f).1 _ _ ?_ ?_
    · linarith
    · exact mul_pos hε (Real.log_pos hnR)
  have hG2pos : 0 < lowerGamma (t + β) (ε * Real.log 2) := by
    refine (statopia_math_node_3224678180_5a630a9f).1 _ _ ?_ ?_
    · linarith
    · exact mul_pos hε (Real.log_pos (by norm_num))
  have hGconstpos : 0 < Gconst t ε δ β := by
    rw [Gconst]
    refine div_pos ?_ ?_
    · exact mul_pos (by norm_num) (pow_pos hδ 2)
    · exact mul_pos (Real.rpow_pos_of_pos hε _) hG2pos
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hGcoefpos : 0 < Gconst t ε δ β * (s : ℝ) / ε ^ s :=
    div_pos (mul_pos hGconstpos hsR) (pow_pos hε s)
  have hLcoefpos :
      0 < lowerGamma (t + (s : ℝ) + β) (ε * Real.log (n : ℝ)) /
        (Real.log ((n : ℝ) / (1 + ε))) ^ s :=
    div_pos hgampos (pow_pos hlogpos s)
  set As := ∫ α in Set.Ioi ε, α ^ (t + (s : ℝ)) / risingFac α n * π α with hAs
  set Bt := ∫ α in Set.Ioi ε, α ^ t / risingFac α n * π α with hBt
  set Bs := ∫ α in Set.Ioo (0 : ℝ) ε, α ^ t / risingFac α n * π α with hBs
  set Gc := Gconst t ε δ β * (s : ℝ) / ε ^ s with hGc
  set Lc := lowerGamma (t + (s : ℝ) + β) (ε * Real.log (n : ℝ)) /
    (Real.log ((n : ℝ) / (1 + ε))) ^ s with hLc
  have hGcpos : 0 < Gc := by rw [hGc]; exact hGcoefpos
  have hLcpos : 0 < Lc := by rw [hLc]; exact hLcoefpos
  have hBspos : 0 < Bs := by rw [hBs]; exact hBpos
  have hBt0' : 0 ≤ Bt := by rw [hBt]; exact hBt0
  have h34 : ((3 : ENNReal) / 4) = ENNReal.ofReal (3 / 4) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
    norm_num
  have hGcne : ENNReal.ofReal Gc ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hGcpos)
  have hLcne : ENNReal.ofReal Lc ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hLcpos)
  have hBsne : ENNReal.ofReal Bs ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hBspos)
  by_cases htop : priorMoment π (t + (s : ℝ) - 1) = ⊤
  · have hT :
        ENNReal.ofReal Gc * priorMoment π (t + (s : ℝ) - 1) * ENNReal.ofReal Lc = ⊤ := by
      rw [htop, ENNReal.mul_top hGcne, ENNReal.top_mul hLcne]
    have h2 : ENNReal.ofReal (3 / 4) * ⊤ * ENNReal.ofReal Bs = ⊤ := by
      rw [ENNReal.mul_top
          (ne_of_gt (ENNReal.ofReal_pos.mpr (by norm_num : (0 : ℝ) < 3 / 4))),
        ENNReal.top_mul hBsne]
    rw [hT, h34, h2]
    simp
  · set E := (priorMoment π (t + (s : ℝ) - 1)).toReal with hE
    have hE0 : 0 ≤ E := by rw [hE]; exact ENNReal.toReal_nonneg
    have hTeq : ENNReal.ofReal Gc * priorMoment π (t + (s : ℝ) - 1) * ENNReal.ofReal Lc
        = ENNReal.ofReal (Gc * E * Lc) := by
      have h1 : priorMoment π (t + (s : ℝ) - 1) = ENNReal.ofReal E := by
        rw [hE]
        exact (ENNReal.ofReal_toReal htop).symm
      rw [h1, ← ENNReal.ofReal_mul (le_of_lt hGcpos),
        ← ENNReal.ofReal_mul (mul_nonneg (le_of_lt hGcpos) hE0)]
    have hK0 : 0 ≤ Gc * E * Lc :=
      mul_nonneg (mul_nonneg (le_of_lt hGcpos) hE0) (le_of_lt hLcpos)
    have hreal : As ≤ Gc * E * Lc * Bt + (3 / 4) * (Gc * E * Lc) * Bs := by
      have hc := statopia_math_node_3249584082_2b6786bc t ht π hπ_meas hπ_nonneg hπ_prob
        δ β ε₀ ε hδ hβ hε₀ hε hε_lt hε_le hA2 hB1 n s hs hns htop
      rw [hAs, hBt, hBs, hGc, hLc, hE]
      simpa using hc
    have hX1 : 0 ≤ Gc * E * Lc * Bt := mul_nonneg hK0 hBt0'
    have hX2 : 0 ≤ (3 / 4) * (Gc * E * Lc) * Bs :=
      mul_nonneg (mul_nonneg (by norm_num) hK0) (le_of_lt hBspos)
    rw [hTeq, h34]
    rw [← ENNReal.ofReal_mul hK0, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3 / 4),
      ← ENNReal.ofReal_mul (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) hK0)]
    rw [← ENNReal.ofReal_add hX1 hX2]
    exact ENNReal.ofReal_le_ofReal hreal
  /- @proof-region region.target-node.session.472ea278b03ef157 end -/

end Statlib.Imported
end
end DPCompletedProof
