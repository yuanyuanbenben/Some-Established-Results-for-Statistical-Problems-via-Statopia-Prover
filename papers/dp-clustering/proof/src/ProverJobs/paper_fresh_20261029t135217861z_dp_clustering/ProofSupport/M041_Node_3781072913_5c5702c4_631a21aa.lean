import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M031_Vocabulary
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M032_Base
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M039_Node_138556644_6aeb8e94_0e7d9f44
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M040_Node_2121685325_82fde9c2_1a92bb26

/- Original module ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_3781072913_5c5702c4_631a21aa; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported
open MeasureTheory
open Statlib.Imported

noncomputable section
open MeasureTheory
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_3781072913_5c5702c4 : ∀ (t ε δ β : ℝ) (n s : ℕ) (π : ℝ → ℝ)
    (ht : 1 ≤ t) (heps : 0 < ε) (heps_lt : ε < 1 / 2)
    (hdelta : 0 < δ) (hbeta : 0 < β) (hs : 1 ≤ s)
    (hns : (s : ℝ) + t ≤ (n : ℝ))
    (hpi_meas : Measurable π)
    (hpi_nonneg : ∀ α ∈ Set.Ioi (0 : ℝ), 0 ≤ π α)
    (hA2 : ∀ α ∈ Set.Ioo (0 : ℝ) ε, δ⁻¹ * α ^ β ≤ π α)
    (hB_int : MeasureTheory.IntegrableOn
      (fun α : ℝ => α ^ t / risingFac α n * π α) (Set.Ioo (0 : ℝ) ε)),
    δ⁻¹ * Real.exp (-1) * (min ε (1 / (1 + Real.log (n : ℝ)))) ^ (t + β) /
        ((t + β) * ((n - 1).factorial : ℝ))
      ≤ ∫ α in Set.Ioo (0 : ℝ) ε, α ^ t / risingFac α n * π α := by
  /- @proof-region region.target-node.session.71f7a31eca995bf0 begin -/
  intro t ε δ β n s π ht heps heps_lt hdelta hbeta hs hns hpi_meas hpi_nonneg hA2 hB_int
  have hn2 : 2 ≤ n := by
    have hs1 : (1:ℝ) ≤ (s:ℝ) := by exact_mod_cast hs
    have h2 : (2:ℝ) ≤ (s:ℝ) + t := by linarith
    have hn2' : (2:ℝ) ≤ (n:ℝ) := le_trans h2 hns
    exact_mod_cast hn2'
  have hcpos : (0:ℝ) < 1 + Real.log (n:ℝ) := by
    have hn1n : (1:ℕ) ≤ n := le_trans (by norm_num) hn2
    have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1n
    have hlog : (0:ℝ) ≤ Real.log (n:ℝ) := Real.log_nonneg hn1
    linarith
  have hFpos : (0:ℝ) < ((n-1).factorial : ℝ) := by
    have hFn : 0 < (n-1).factorial := Nat.factorial_pos _
    exact_mod_cast hFn
  have hcoefnn : (0:ℝ) ≤ δ⁻¹ / ((n-1).factorial : ℝ) :=
    div_nonneg (le_of_lt (inv_pos.mpr hdelta)) (le_of_lt hFpos)
  have hPoint : ∀ α ∈ Set.Ioo (0:ℝ) ε,
      (δ⁻¹ / ((n-1).factorial : ℝ)) * (α^(t+β-1) * Real.exp (-(1 + Real.log (n:ℝ))*α))
        ≤ α^t / risingFac α n * π α :=
    statopia_math_node_138556644_6aeb8e94 t ε δ β n π hn2 hdelta hA2
  have htau : (0:ℝ) < t + β := by linarith
  have hbase_int : MeasureTheory.IntegrableOn (fun α : ℝ => α^(t+β-1) * Real.exp (-(1 + Real.log (n:ℝ))*α)) (Set.Ioo (0:ℝ) ε) :=
    (statopia_math_node_2121685325_82fde9c2 t β ε n heps hn2 htau).1
  have hInt_exp : Real.exp (-1) * (min ε (1/(1+Real.log (n:ℝ))))^(t+β) / (t+β)
      ≤ ∫ α in Set.Ioo (0:ℝ) ε, α^(t+β-1) * Real.exp (-(1 + Real.log (n:ℝ))*α) :=
    (statopia_math_node_2121685325_82fde9c2 t β ε n heps hn2 htau).2
  have hInt_ge : (δ⁻¹ / ((n-1).factorial : ℝ)) *
      (∫ α in Set.Ioo (0:ℝ) ε, α^(t+β-1) * Real.exp (-(1 + Real.log (n:ℝ))*α))
      ≤ ∫ α in Set.Ioo (0:ℝ) ε, α^t / risingFac α n * π α := by
    have hg_int : MeasureTheory.IntegrableOn (fun α : ℝ => (δ⁻¹ / ((n-1).factorial : ℝ)) * (α^(t+β-1) * Real.exp (-(1 + Real.log (n:ℝ))*α))) (Set.Ioo (0:ℝ) ε) :=
      hbase_int.const_mul _
    have hmono : (∫ α in Set.Ioo (0:ℝ) ε, (δ⁻¹ / ((n-1).factorial : ℝ)) * (α^(t+β-1) * Real.exp (-(1 + Real.log (n:ℝ))*α)))
        ≤ ∫ α in Set.Ioo (0:ℝ) ε, α^t / risingFac α n * π α :=
      MeasureTheory.setIntegral_mono_on hg_int hB_int measurableSet_Ioo (fun α hα => hPoint α hα)
    rwa [MeasureTheory.integral_const_mul] at hmono
  have harith : δ⁻¹ * Real.exp (-1) * (min ε (1/(1+Real.log (n:ℝ))))^(t+β) / ((t+β)*((n-1).factorial:ℝ))
      = (δ⁻¹ / ((n-1).factorial : ℝ)) * (Real.exp (-1) * (min ε (1/(1+Real.log (n:ℝ))))^(t+β) / (t+β)) := by
    rw [div_eq_mul_inv, mul_inv_rev]
    ring
  calc δ⁻¹ * Real.exp (-1) * (min ε (1/(1+Real.log (n:ℝ))))^(t+β) / ((t+β)*((n-1).factorial:ℝ))
      = (δ⁻¹ / ((n-1).factorial : ℝ)) * (Real.exp (-1) * (min ε (1/(1+Real.log (n:ℝ))))^(t+β) / (t+β)) := harith
    _ ≤ (δ⁻¹ / ((n-1).factorial : ℝ)) * (∫ α in Set.Ioo (0:ℝ) ε, α^(t+β-1) * Real.exp (-(1 + Real.log (n:ℝ))*α)) :=
        mul_le_mul_of_nonneg_left hInt_exp hcoefnn
    _ ≤ ∫ α in Set.Ioo (0:ℝ) ε, α^t / risingFac α n * π α := hInt_ge
  /- @proof-region region.target-node.session.71f7a31eca995bf0 end -/

end Statlib.Imported
end
end DPCompletedProof
