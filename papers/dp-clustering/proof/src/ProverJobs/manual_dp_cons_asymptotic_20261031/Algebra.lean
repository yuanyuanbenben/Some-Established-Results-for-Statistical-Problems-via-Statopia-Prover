import ProverJobs.manual_dp_cor_c_finish_20261031.Main
import ProverJobs.manual_dp_cons_series_20261031.SeriesFinish
open MeasureTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace ManualDPConsAsymptotic

lemma term_factorization (t s : ℕ) (ht : 1 ≤ t)
    (P D d0 eps K rho nu : ℝ) (hrho : rho ≠ 0) (heps : eps ≠ 0) (hd0 : d0 ≠ 0)
    (n : ℕ) (hlog : Real.log ((n : ℝ)/(1+eps)) ≠ 0) :
    (P * 2^s * (s : ℝ) / eps * (Real.log ((n : ℝ)/(1+eps)))⁻¹) *
      (D / rho ^ (t+s-1) * Real.Gamma (nu+(t:ℝ)+(s:ℝ))) *
      ((Real.log (n : ℝ)) ^ ((1:ℝ)/2) / d0 * K^(t+s) / ((t+s).factorial : ℝ)) =
    (P * D * K^t / (eps * d0 * rho^(t-1))) *
      OfflineDPConsSeries.logFactor eps n * OfflineDPConsSeries.gammaTerm nu t K rho s := by
  have hs : t+s-1 = (t-1)+s := by omega
  rw [hs, pow_add rho, pow_add K]
  simp only [OfflineDPConsSeries.logFactor, OfflineDPConsSeries.gammaTerm, mul_pow, div_pow,
    ← Real.sqrt_eq_rpow]
  have hf : (((t+s).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hrho, heps, hd0, hf, hlog]
  <;> ring

#print axioms term_factorization
end ManualDPConsAsymptotic
