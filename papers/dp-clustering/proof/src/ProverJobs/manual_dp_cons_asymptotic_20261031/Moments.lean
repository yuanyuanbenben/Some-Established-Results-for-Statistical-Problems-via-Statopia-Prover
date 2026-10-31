import ProverJobs.manual_dp_cor_c_finish_20261031.Main
open MeasureTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace ManualDPConsAsymptotic

/-- The real whole-line A3 assumption used by consGeneral implies the exact
restricted ENNReal density-moment estimate, with no lost support or integrability condition. -/
lemma A3_density_moment (pi : ℝ → ℝ)
    (hpi0 : ∀ a, 0 < a → 0 ≤ pi a) (hpizero : ∀ a, a ≤ 0 → pi a = 0)
    (D rho nu : ℝ)
    (hint : ∀ q : ℕ, 1 ≤ q → Integrable (fun a : ℝ => a^q * pi a) volume)
    (hA3 : ∀ q : ℕ, 1 ≤ q → (∫ a : ℝ, a^q * pi a ∂volume) <
      D * rho^(-(q:ℤ)) * Real.Gamma (nu+(q:ℝ)+1)) :
    ∀ q : ℕ, 1 ≤ q →
      (∫⁻ a in Set.Ioi (0:ℝ), ENNReal.ofReal (a^q * pi a)) ≤
        ENNReal.ofReal (D / rho^q * Real.Gamma (nu+(q:ℝ)+1)) := by
  intro q hq
  have hnn : ∀ᵐ a ∂volume.restrict (Set.Ioi (0:ℝ)), 0 ≤ a^q*pi a := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    exact mul_nonneg (pow_nonneg ha.le _) (hpi0 a ha)
  rw [← ofReal_integral_eq_lintegral_ofReal (hint q hq).restrict hnn]
  have heq : (∫ a in Set.Ioi (0:ℝ), a^q*pi a) = ∫ a : ℝ, a^q*pi a := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    exact Eventually.of_forall (fun a ha => by rw [hpizero a (not_lt.mp ha), mul_zero])
  rw [heq]
  apply ENNReal.ofReal_le_ofReal
  have hh := (hA3 q hq).le
  simpa only [zpow_neg, zpow_natCast, ← div_eq_mul_inv] using hh

/-- Direct bridge from the source A3AtRate moment of the actual density prior.
The restricted moment is bounded by the full prior moment, so no extra support premise is needed. -/
lemma A3_measure_to_density (pi : ℝ → ℝ) (hpimeas : Measurable pi) (hpi0 : ∀ a, 0 ≤ pi a)
    (D rho nu : ℝ) (hrho : 0 < rho)
    (hA3 : ∀ q : ℕ, 1 ≤ q →
      (∫⁻ a : ℝ, ENNReal.ofReal (a^q) ∂volume.withDensity (fun a => ENNReal.ofReal (pi a))) <
        ENNReal.ofReal (D * rho^(-(q:ℝ)) * Real.Gamma (nu+(q:ℝ)+1))) :
    ∀ q : ℕ, 1 ≤ q →
      (∫⁻ a in Set.Ioi (0:ℝ), ENNReal.ofReal (a^q * pi a)) ≤
        ENNReal.ofReal (D / rho^q * Real.Gamma (nu+(q:ℝ)+1)) := by
  intro q hq
  calc
    _ ≤ ∫⁻ a : ℝ, ENNReal.ofReal (a^q * pi a) := setLIntegral_le_lintegral _ _
    _ = ∫⁻ a : ℝ, ENNReal.ofReal (a^q) ∂volume.withDensity (fun a => ENNReal.ofReal (pi a)) := by
      rw [lintegral_withDensity_eq_lintegral_mul _ hpimeas.ennreal_ofReal (by fun_prop)]
      apply lintegral_congr
      intro a
      simp only [Pi.mul_apply]
      rw [← ENNReal.ofReal_mul (hpi0 a)]
      congr 1
      ring
    _ ≤ _ := by
      have hh := (hA3 q hq).le
      simpa only [Real.rpow_neg hrho.le, Real.rpow_natCast, ← div_eq_mul_inv] using hh

#print axioms A3_measure_to_density
#print axioms A3_density_moment
end ManualDPConsAsymptotic
