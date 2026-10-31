import ProverJobs.manual_dp_cons_asymptotic_20261031.Algebra
open MeasureTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace ManualDPConsAsymptotic
local notation "CorC" => OfflineCorC.Statlib.Imported.Cratio
local notation "Mom" => OfflineCorC.Statlib.Imported.priorMoment

lemma moment_index (pi : ℝ → ℝ) (t s : ℕ) (ht : 1 ≤ t) (hs : 1 ≤ s) :
    Mom pi (t:ℝ) s = ∫⁻ a in Set.Ioi (0:ℝ), ENNReal.ofReal (a^(t+s-1) * pi a) := by
  have hc : ((t+s-1:ℕ):ℝ) = (t:ℝ)+(s:ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ t+s), Nat.cast_add, Nat.cast_one]
  simp only [OfflineCorC.Statlib.Imported.priorMoment, ← hc, Real.rpow_natCast]

/-- Source A3 in density form, combined with the genuinely completed Corollary C,
controls the entire overclustering prior-factor sum. -/
theorem corC_prior_sum_tendsto_zero (t : ℕ) (ht : 1 ≤ t)
    (pi : ℝ → ℝ) (hpimeas : Measurable pi)
    (hpi0 : ∀ a ∈ Set.Ioi (0:ℝ), 0 ≤ pi a)
    (hpinorm : ∫⁻ a in Set.Ioi (0:ℝ), ENNReal.ofReal (pi a) = 1)
    (eps delta beta : ℝ) (heps : 0 < eps) (hdelta : 0 < delta) (hbeta : 0 < beta)
    (hA2 : ∀ a ∈ Set.Ioo (0:ℝ) eps, delta⁻¹*a^beta ≤ pi a ∧ pi a ≤ delta*a^beta)
    (D rho nu K d0 : ℝ) (hD : 0 < D) (hnu : 0 < nu) (hK : 0 < K) (hd0 : 0 < d0)
    (hrho : 4*K ≤ rho)
    (hA3 : ∀ q : ℕ, 1 ≤ q →
      (∫⁻ a in Set.Ioi (0:ℝ), ENNReal.ofReal (a^q * pi a)) ≤
        ENNReal.ofReal (D / rho^q * Real.Gamma (nu+(q:ℝ)+1))) :
    Tendsto (fun n : ℕ => ∑ s ∈ Finset.Icc 1 (n-t),
      CorC pi n (t:ℝ) s *
        ENNReal.ofReal ((Real.log (n:ℝ))^((1:ℝ)/2)/d0 * K^(t+s) / ((t+s).factorial:ℝ)))
      atTop (𝓝 0) := by
  have htR : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht
  have hrhop : 0 < rho := (show 0 < 4*K by positivity).trans_le hrho
  obtain ⟨er, ⟨her, her1, herle⟩, hcor⟩ :=
    OfflineCorC.Statlib.Imported.paper_33963587efec4920b10d414c6b312566
      (t:ℝ) htR pi hpimeas hpi0 hpinorm (withDensity_absolutelyContinuous _ _)
      ⟨eps,delta,beta,heps,hdelta,hbeta,hA2⟩ eps delta beta heps hdelta hbeta hA2
  let P := max 0 (OfflineCorC.Statlib.Imported.Gconst (t:ℝ) er delta beta * Real.Gamma ((t:ℝ)+beta+1))
  let C := P * D * K^t / (er*d0*rho^(t-1))
  have hP : 0 ≤ P := le_max_left _ _
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply OfflineDPConsSeries.ennreal_sum_tendsto_zero_of_termwise_bound t ht nu hnu K rho hK hrho C er hC her
  filter_upwards [eventually_ge_atTop 4] with n hn
  intro s hs
  have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
  have hsn : s < n := by have := (Finset.mem_Icc.mp hs).2; omega
  have hnR : (4:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hlogpos : 0 < Real.log ((n:ℝ)/(1+er)) := Real.log_pos ((one_lt_div (by linarith : 0 < 1+er)).mpr (by linarith))
  have hlogn : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by linarith)
  have hcoef0 : 0 ≤ P*2^s*(s:ℝ)/er * (Real.log ((n:ℝ)/(1+er)))⁻¹ := by positivity
  have hmoment0 : 0 ≤ D/rho^(t+s-1)*Real.Gamma (nu+(t:ℝ)+(s:ℝ)) := by
    exact mul_nonneg (by positivity) (Real.Gamma_pos_of_pos (by positivity)).le
  have hB0 : 0 ≤ (Real.log (n:ℝ))^((1:ℝ)/2)/d0 * K^(t+s) / ((t+s).factorial:ℝ) := by positivity
  have hcoeff : ENNReal.ofReal (OfflineCorC.Statlib.Imported.Gconst (t:ℝ) er delta beta *
      Real.Gamma ((t:ℝ)+beta+1) * 2^s*(s:ℝ)/er * (Real.log ((n:ℝ)/(1+er)))⁻¹) ≤
      ENNReal.ofReal (P*2^s*(s:ℝ)/er * (Real.log ((n:ℝ)/(1+er)))⁻¹) := by
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right 0 _) (by positivity : 0 ≤ (2:ℝ)^s)) (Nat.cast_nonneg s)) her.le)
      (inv_nonneg.mpr hlogpos.le)
  have hm : Mom pi (t:ℝ) s ≤ ENNReal.ofReal (D/rho^(t+s-1)*Real.Gamma (nu+(t:ℝ)+(s:ℝ))) := by
    rw [moment_index pi t s ht hs1]
    have hc : ((t+s-1:ℕ):ℝ) = (t:ℝ)+(s:ℝ)-1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ t+s), Nat.cast_add, Nat.cast_one]
    have hh := hA3 (t+s-1) (by omega)
    have he : nu + ((t+s-1:ℕ):ℝ) + 1 = nu+(t:ℝ)+(s:ℝ) := by rw [hc]; ring
    simpa only [he] using hh
  calc
    _ ≤ (ENNReal.ofReal (P*2^s*(s:ℝ)/er * (Real.log ((n:ℝ)/(1+er)))⁻¹) *
          ENNReal.ofReal (D/rho^(t+s-1)*Real.Gamma (nu+(t:ℝ)+(s:ℝ)))) *
        ENNReal.ofReal ((Real.log (n:ℝ))^((1:ℝ)/2)/d0 * K^(t+s) / ((t+s).factorial:ℝ)) := by
      exact mul_le_mul_right' ((hcor n hn s (by omega) hsn).trans (mul_le_mul' hcoeff hm)) _
    _ = ENNReal.ofReal (C * OfflineDPConsSeries.logFactor er n * OfflineDPConsSeries.gammaTerm nu t K rho s) := by
      rw [← ENNReal.ofReal_mul hcoef0, ← ENNReal.ofReal_mul (mul_nonneg hcoef0 hmoment0)]
      congr 1
      exact term_factorization t s ht P D d0 er K rho nu hrhop.ne' her.ne' hd0.ne' n hlogpos.ne'

#print axioms corC_prior_sum_tendsto_zero
end ManualDPConsAsymptotic
