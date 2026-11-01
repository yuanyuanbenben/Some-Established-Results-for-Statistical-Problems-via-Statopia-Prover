import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M069_Node_296624434_77a29a87_2524619b

/- Original module ProverJobs.manual_dp_cons_series_20261031.SeriesFinish; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal
noncomputable section
namespace OfflineDPConsSeries

/-- The logarithmic prefactor in the source's full overclustering bound. -/
theorem sqrt_log_ratio_tendsto_zero (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => Real.sqrt (Real.log (n : ℝ)) /
      Real.log ((n : ℝ) / (1 + ε))) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hlog
  have hA : Tendsto (fun n : ℕ => (Real.sqrt (Real.log (n : ℝ)))⁻¹) atTop (𝓝 0) :=
    hsqrt.inv_tendsto_atTop
  have hB : Tendsto (fun n : ℕ => Real.log (1 + ε) * (Real.log (n : ℝ))⁻¹) atTop (𝓝 0) := by
    have h := hlog.inv_tendsto_atTop.const_mul (Real.log (1 + ε))
    simpa using h
  have hC : Tendsto (fun n : ℕ => 1 - Real.log (1 + ε) * (Real.log (n : ℝ))⁻¹) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hB
    simpa using h
  have hD : Tendsto (fun n : ℕ => (1 - Real.log (1 + ε) * (Real.log (n : ℝ))⁻¹)⁻¹) atTop (𝓝 1) := by
    have h := hC.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    simpa using h
  have hEqE : (fun n : ℕ => (1 - Real.log (1 + ε) * (Real.log (n : ℝ))⁻¹)⁻¹)
      =ᶠ[atTop] (fun n : ℕ => Real.log (n : ℝ) / Real.log ((n : ℝ) / (1 + ε))) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have h0 : (0 : ℕ) < n := lt_of_lt_of_le (by norm_num) hn
      exact_mod_cast h0
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have h1 : (1 + ε) ≠ 0 := by positivity
    have hL : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hn))
    have hsub : (1 : ℝ) - Real.log (1 + ε) * (Real.log (n : ℝ))⁻¹
        = (Real.log (n : ℝ) - Real.log (1 + ε)) / Real.log (n : ℝ) := by
      rw [sub_div, div_self hL, div_eq_mul_inv]
    rw [hsub, Real.log_div hn0 h1, inv_div]
  have hE : Tendsto (fun n : ℕ => Real.log (n : ℝ) / Real.log ((n : ℝ) / (1 + ε))) atTop (𝓝 1) :=
    hD.congr' hEqE
  have hP : Tendsto (fun n : ℕ => (Real.sqrt (Real.log (n : ℝ)))⁻¹ *
      (Real.log (n : ℝ) / Real.log ((n : ℝ) / (1 + ε)))) atTop (𝓝 0) := by
    have h := hA.mul hE
    simpa using h
  have hEq : (fun n : ℕ => (Real.sqrt (Real.log (n : ℝ)))⁻¹ *
      (Real.log (n : ℝ) / Real.log ((n : ℝ) / (1 + ε))))
      =ᶠ[atTop] (fun n : ℕ => Real.sqrt (Real.log (n : ℝ)) / Real.log ((n : ℝ) / (1 + ε))) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hLpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    set r : ℝ := Real.sqrt (Real.log (n : ℝ)) with hr
    set L : ℝ := Real.log (n : ℝ) with hLdef
    have hrr : r * r = L := by
      rw [hr, hLdef]
      exact Real.mul_self_sqrt (le_of_lt hLpos)
    have hrne : r ≠ 0 := by
      rw [hr]
      exact ne_of_gt (Real.sqrt_pos.2 hLpos)
    rw [← hrr, ← mul_div_assoc, ← mul_assoc, inv_mul_cancel₀ hrne, one_mul]
  exact hP.congr' hEq

def logFactor (ε : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (Real.log (n : ℝ)) / Real.log ((n : ℝ) / (1 + ε))

def gammaTerm (nu : ℝ) (t : ℕ) (K5 rho : ℝ) (s : ℕ) : ℝ :=
  (s : ℝ) * Real.Gamma (nu + (t : ℝ) + (s : ℝ)) *
    (2 * K5 / rho)^s / ((t+s).factorial : ℝ)

/-- A configuration-only threshold rho >= 4 K5 gives a fixed finite bound
for every partial sum of the actual Gamma series. -/
theorem gamma_partial_sums_bounded (t : ℕ) (ht : 1 ≤ t)
    (nu : ℝ) (hnu : 0 < nu) (K5 rho : ℝ) (hK5 : 0 < K5) (hrho : 4*K5 ≤ rho) :
    Summable (gammaTerm nu t K5 rho) ∧
      ∃ S : ℝ, 0 ≤ S ∧ (∑' s, gammaTerm nu t K5 rho s) = S ∧
        ∀ N : ℕ, 0 ≤ ∑ s ∈ Finset.Icc 1 N, gammaTerm nu t K5 rho s ∧
          (∑ s ∈ Finset.Icc 1 N, gammaTerm nu t K5 rho s) ≤ S := by
  have hρ : 0 < rho := lt_of_lt_of_le (by positivity : 0 < 4*K5) hrho
  have hq : 0 < 2*K5/rho := div_pos (by positivity) hρ
  have hqhalf : 2*K5/rho ≤ 1/2 := (div_le_iff₀ hρ).mpr (by linarith)
  exact Statlib.Imported.statopia_math_node_296624434_77a29a87 t ht nu hnu
    (2*K5/rho) hq hqhalf

lemma gammaTerm_nonneg (nu : ℝ) (t : ℕ) (K5 rho : ℝ)
    (hnu : 0 < nu) (hK5 : 0 < K5) (hrho : 4*K5 ≤ rho) (s : ℕ) :
    0 ≤ gammaTerm nu t K5 rho s := by
  have hρ : 0 < rho := lt_of_lt_of_le (by positivity : 0 < 4*K5) hrho
  have hgamma : 0 < Real.Gamma (nu + (t : ℝ) + (s : ℝ)) :=
    Real.Gamma_pos_of_pos (by positivity)
  exact div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hgamma.le)
    (pow_nonneg (div_pos (by positivity) hρ).le _)) (Nat.cast_nonneg _)

lemma logFactor_eventually_nonneg (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 0 ≤ logFactor ε n := by
  have hlarge : ∀ᶠ n : ℕ in atTop, 1+ε < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop (1+ε)
  filter_upwards [hlarge] with n hn
  apply div_nonneg (Real.sqrt_nonneg _)
  exact (Real.log_pos ((one_lt_div (by positivity : 0 < 1+ε)).mpr hn)).le

/-- The complete finite Gamma-series upper bound vanishes; no convergence
assumption is supplied for this sum. -/
theorem concrete_gamma_sum_tendsto_zero (t : ℕ) (ht : 1 ≤ t)
    (nu : ℝ) (hnu : 0 < nu) (K5 rho : ℝ) (hK5 : 0 < K5) (hrho : 4*K5 ≤ rho)
    (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => ∑ s ∈ Finset.Icc 1 (n-t),
      C * logFactor ε n * gammaTerm nu t K5 rho s) atTop (𝓝 0) := by
  obtain ⟨_,S,hS,_,hbound⟩ := gamma_partial_sums_bounded t ht nu hnu K5 rho hK5 hrho
  have hupper : Tendsto (fun n : ℕ => C * logFactor ε n * S) atTop (𝓝 0) := by
    simpa only [zero_mul, mul_zero] using
      ((sqrt_log_ratio_tendsto_zero ε hε).const_mul C).mul_const S
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [logFactor_eventually_nonneg ε hε] with n hn
    exact Finset.sum_nonneg (fun s _ => mul_nonneg (mul_nonneg hC hn)
      (gammaTerm_nonneg nu t K5 rho hnu hK5 hrho s))
  · filter_upwards [logFactor_eventually_nonneg ε hε] with n hn
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hbound (n-t)).2 (mul_nonneg hC hn)

/-- ENNReal version of the concrete bound, suitable for expectations. -/
theorem concrete_gamma_sum_ofReal_tendsto_zero (t : ℕ) (ht : 1 ≤ t)
    (nu : ℝ) (hnu : 0 < nu) (K5 rho : ℝ) (hK5 : 0 < K5) (hrho : 4*K5 ≤ rho)
    (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => ENNReal.ofReal (∑ s ∈ Finset.Icc 1 (n-t),
      C * logFactor ε n * gammaTerm nu t K5 rho s)) atTop (𝓝 0) := by
  simpa only [Function.comp_def, ENNReal.ofReal_zero] using
    (ENNReal.continuous_ofReal.tendsto 0).comp
      (concrete_gamma_sum_tendsto_zero t ht nu hnu K5 rho hK5 hrho C ε hC hε)

/-- Honest per-s bounds imply convergence of the full finite sum. The premise
is a numerical estimate, not the desired aggregate convergence. -/
theorem ennreal_sum_tendsto_zero_of_termwise_bound (t : ℕ) (ht : 1 ≤ t)
    (nu : ℝ) (hnu : 0 < nu) (K5 rho : ℝ) (hK5 : 0 < K5) (hrho : 4*K5 ≤ rho)
    (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) (E : ℕ → ℕ → ℝ≥0∞)
    (hE : ∀ᶠ n : ℕ in atTop, ∀ s ∈ Finset.Icc 1 (n-t),
      E n s ≤ ENNReal.ofReal (C * logFactor ε n * gammaTerm nu t K5 rho s)) :
    Tendsto (fun n : ℕ => ∑ s ∈ Finset.Icc 1 (n-t), E n s) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (concrete_gamma_sum_ofReal_tendsto_zero t ht nu hnu K5 rho hK5 hrho C ε hC hε)
    (Eventually.of_forall (fun n => zero_le _))
  filter_upwards [hE, logFactor_eventually_nonneg ε hε] with n hn hlog
  calc (∑ s ∈ Finset.Icc 1 (n-t), E n s) ≤
      ∑ s ∈ Finset.Icc 1 (n-t), ENNReal.ofReal
        (C * logFactor ε n * gammaTerm nu t K5 rho s) := Finset.sum_le_sum hn
    _ = _ := (ENNReal.ofReal_sum_of_nonneg (fun s _ =>
      mul_nonneg (mul_nonneg hC hlog) (gammaTerm_nonneg nu t K5 rho hnu hK5 hrho s))).symm

end OfflineDPConsSeries
end
end DPCompletedProof
