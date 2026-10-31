import ProverJobs.job_paper_dc88427b52844263b5321fc99eb582d8.Base
open MeasureTheory Filter Topology
open scoped BigOperators
open Statlib.Imported
noncomputable section
namespace OfflineDPPartitionPrior

def concentrationFactor (piDens : ℝ → ℝ) (n k : ℕ) : ℝ :=
  ∫ α : ℝ, (α^k / dpRisingFactorial α n) * piDens α

def partitionKernelSum (g q0 : ℝ → ℝ) (n k : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ A ∈ dpTau n k, ∏ B ∈ A,
    ((B.card - 1).factorial : ℝ) * dpMargLik g q0 x B

/-- The concentration-prior coefficient and the complete kernel partition sum
factor exactly. This is the actual dpNpost, not a replacement posterior. -/
theorem dpNpost_factor (g q0 piDens : ℝ → ℝ) (n k : ℕ) (x : Fin n → ℝ) :
    dpNpost g q0 piDens n k x =
      concentrationFactor piDens n k * partitionKernelSum g q0 n k x := by
  classical
  have hcard : ∀ A ∈ dpTau n k, A.card = k := by
    intro A hA
    exact (Finset.mem_filter.mp hA).2.1
  have hfun : (fun α : ℝ => (∑ A ∈ dpTau n k,
      dpPartPrior α n A * ∏ B ∈ A, dpMargLik g q0 x B) * piDens α) =
      (fun α : ℝ => (α^k / dpRisingFactorial α n * piDens α) *
        partitionKernelSum g q0 n k x) := by
    funext α
    rw [partitionKernelSum, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro A hA
    rw [dpPartPrior, hcard A hA, Finset.prod_mul_distrib]
    ring
  rw [dpNpost, hfun, integral_mul_const]
  rfl

/-- Algebraic cancellation used after proving positivity of the t-partition
contribution and of the posterior's normalization. -/
theorem ratio_of_positive_masses (a b z : ℝ) (hb : 0 < b) (hz : z ≠ 0) :
    (a/z)/(b/z) = a/b := by field_simp

#print axioms dpNpost_factor
end OfflineDPPartitionPrior
