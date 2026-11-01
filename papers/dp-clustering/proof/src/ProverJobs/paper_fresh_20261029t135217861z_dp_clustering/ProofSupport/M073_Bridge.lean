import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M029_PosteriorRatio
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M072_Main
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M065_Moments

/- Original module ProverJobs.manual_dp_cons_asymptotic_20261031.Bridge; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported
open MeasureTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace ManualDPConsAsymptotic
open ManualDPCons Statlib.Imported

lemma priorRatio_eq_corC (C : LocationConfig) (prior : ConcentrationPrior)
    (n s : ℕ) (htn : C.t ≤ n) (hs : 1 ≤ s) (hts : C.t+s ≤ n) :
    ENNReal.ofReal (priorRatio prior.dens C.t n s) =
      OfflineCorC.Statlib.Imported.Cratio prior.dens n (C.t:ℝ) s := by
  have hspec := source_concentration_spec C prior n s htn hs hts
  have hnn : ∀ k : ℕ, ∀ᵐ a ∂volume.restrict (Set.Ioi (0:ℝ)),
      0 ≤ (a^k / dpRisingFactorial a n) * prior.dens a := by
    intro k
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    have hf : 0 ≤ dpRisingFactorial a n := by
      unfold dpRisingFactorial
      exact Finset.prod_nonneg (fun i _ => add_nonneg ha.le (Nat.cast_nonneg i))
    exact mul_nonneg (div_nonneg (pow_nonneg ha.le _) hf) (prior.nonneg a ha)
  have hnum : OfflineCorC.Statlib.Imported.priorRatioIntegral prior.dens ((C.t:ℝ)+(s:ℝ)) n =
      ENNReal.ofReal (concentrationIntegral prior.dens n (C.t+s)) := by
    have h := (ofReal_integral_eq_lintegral_ofReal (hspec (C.t+s) (by omega) hts).1 (hnn (C.t+s))).symm
    simpa only [concentrationIntegral, OfflineCorC.Statlib.Imported.priorRatioIntegral,
      OfflineCorC.Statlib.Imported.risingFac, dpRisingFactorial, ← Nat.cast_add, Real.rpow_natCast] using h
  have hden : OfflineCorC.Statlib.Imported.priorRatioIntegral prior.dens (C.t:ℝ) n =
      ENNReal.ofReal (concentrationIntegral prior.dens n C.t) := by
    have h := (ofReal_integral_eq_lintegral_ofReal (hspec C.t C.ht htn).1 (hnn C.t)).symm
    simpa only [concentrationIntegral, OfflineCorC.Statlib.Imported.priorRatioIntegral,
      OfflineCorC.Statlib.Imported.risingFac, dpRisingFactorial, Real.rpow_natCast] using h
  rw [OfflineCorC.Statlib.Imported.Cratio, hnum, hden]
  exact ENNReal.ofReal_div_of_pos (hspec C.t C.ht htn).2

/-- The actual real prior ratio is used, with genuine A3 moments and source-only
configuration constants. No prior-ratio estimate or convergence is assumed. -/
theorem prior_ratio_bound_sum_tendsto_zero (C : LocationConfig) (prior : ConcentrationPrior)
    (D rho nu : ℝ) (hD : 0 < D) (hnu : 0 < nu)
    (hrho : 4 * dpK5 C.U C.m C.c C.theta ≤ rho)
    (hA3_int : ∀ q : ℕ, 1 ≤ q → Integrable (fun a : ℝ => a^q * prior.dens a) volume)
    (hA3 : ∀ q : ℕ, 1 ≤ q → (∫ a : ℝ, a^q * prior.dens a ∂volume) <
      D * rho^(-(q:ℤ)) * Real.Gamma (nu+(q:ℝ)+1)) :
    Tendsto (fun n : ℕ => ∑ s ∈ Finset.Icc 1 (n-C.t),
      ENNReal.ofReal (priorRatio prior.dens C.t n s) *
        ENNReal.ofReal (denominatorLoss C n * (dpK5 C.U C.m C.c C.theta)^(C.t+s) /
          ((C.t+s).factorial:ℝ))) atTop (𝓝 0) := by
  obtain ⟨eps,delta,beta,heps,hdelta,hbeta,hA2⟩ := prior.A2
  have hA2' : ∀ a ∈ Set.Ioo (0:ℝ) eps, delta⁻¹*a^beta ≤ prior.dens a ∧ prior.dens a ≤ delta*a^beta := by
    intro a ha
    simpa only [one_div] using hA2 a ha.1 ha.2
  have hpinorm : ∫⁻ a in Set.Ioi (0:ℝ), ENNReal.ofReal (prior.dens a) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal prior.integrable_dens]
    · rw [prior.norm, ENNReal.ofReal_one]
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
      exact prior.nonneg a ha
  have hK : 0 < dpK5 C.U C.m C.c C.theta := zero_lt_one.trans_le (le_max_left _ _)
  have hd0 : 0 < (C.L * Real.exp (-C.R) * min 1 C.r / 2)^C.t := by
    have hL := C.hL
    have hr := C.hr
    positivity
  have h := corC_prior_sum_tendsto_zero C.t C.ht prior.dens prior.measurable_dens prior.nonneg
    hpinorm eps delta beta heps hdelta hbeta hA2' D rho nu (dpK5 C.U C.m C.c C.theta)
    ((C.L * Real.exp (-C.R) * min 1 C.r / 2)^C.t) hD hnu hK hd0 hrho
    (A3_density_moment prior.dens prior.nonneg prior.zero D rho nu hA3_int hA3)
  apply h.congr'
  filter_upwards [eventually_ge_atTop C.t] with n hn
  apply Finset.sum_congr rfl
  intro s hs
  rw [priorRatio_eq_corC C prior n s hn (Finset.mem_Icc.mp hs).1 (by have := (Finset.mem_Icc.mp hs).2; omega)]
  rfl

/-- The root A3AtRate ENNReal moment contract can be transported directly to this
variant; no conversion to strict real inequalities or moment integrability is required. -/
theorem prior_ratio_bound_sum_tendsto_zero_of_density_A3 (C : LocationConfig) (prior : ConcentrationPrior)
    (D rho nu : ℝ) (hD : 0 < D) (hnu : 0 < nu)
    (hrho : 4 * dpK5 C.U C.m C.c C.theta ≤ rho)
    (hA3_density : ∀ q : ℕ, 1 ≤ q →
      (∫⁻ a in Set.Ioi (0:ℝ), ENNReal.ofReal (a^q * prior.dens a)) ≤
        ENNReal.ofReal (D / rho^q * Real.Gamma (nu+(q:ℝ)+1))) :
    Tendsto (fun n : ℕ => ∑ s ∈ Finset.Icc 1 (n-C.t),
      ENNReal.ofReal (priorRatio prior.dens C.t n s) *
        ENNReal.ofReal (denominatorLoss C n * (dpK5 C.U C.m C.c C.theta)^(C.t+s) /
          ((C.t+s).factorial:ℝ))) atTop (𝓝 0) := by
  obtain ⟨eps,delta,beta,heps,hdelta,hbeta,hA2⟩ := prior.A2
  have hA2' : ∀ a ∈ Set.Ioo (0:ℝ) eps, delta⁻¹*a^beta ≤ prior.dens a ∧ prior.dens a ≤ delta*a^beta := by
    intro a ha
    simpa only [one_div] using hA2 a ha.1 ha.2
  have hpinorm : ∫⁻ a in Set.Ioi (0:ℝ), ENNReal.ofReal (prior.dens a) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal prior.integrable_dens]
    · rw [prior.norm, ENNReal.ofReal_one]
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
      exact prior.nonneg a ha
  have hK : 0 < dpK5 C.U C.m C.c C.theta := zero_lt_one.trans_le (le_max_left _ _)
  have hd0 : 0 < (C.L * Real.exp (-C.R) * min 1 C.r / 2)^C.t := by
    have hL := C.hL
    have hr := C.hr
    positivity
  have h := corC_prior_sum_tendsto_zero C.t C.ht prior.dens prior.measurable_dens prior.nonneg
    hpinorm eps delta beta heps hdelta hbeta hA2' D rho nu (dpK5 C.U C.m C.c C.theta)
    ((C.L * Real.exp (-C.R) * min 1 C.r / 2)^C.t) hD hnu hK hd0 hrho
    hA3_density
  apply h.congr'
  filter_upwards [eventually_ge_atTop C.t] with n hn
  apply Finset.sum_congr rfl
  intro s hs
  rw [priorRatio_eq_corC C prior n s hn (Finset.mem_Icc.mp hs).1 (by have := (Finset.mem_Icc.mp hs).2; omega)]
  rfl

end ManualDPConsAsymptotic
end
end DPCompletedProof
