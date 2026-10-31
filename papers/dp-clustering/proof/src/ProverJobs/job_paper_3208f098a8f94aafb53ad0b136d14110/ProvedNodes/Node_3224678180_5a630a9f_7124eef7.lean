import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.Vocabulary
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.Base

open MeasureTheory
open Statlib.Imported

noncomputable section
open MeasureTheory
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_3224678180_5a630a9f : (∀ x y : ℝ, 0 < x → 0 < y → 0 < lowerGamma x y) ∧
    
    (∀ x y : ℝ, 0 < x → 0 < y → lowerGamma x y ≤ y ^ x / x) ∧
    
    (∀ x y : ℝ, 0 < x → 0 < y → Real.exp (-y) * y ^ x / x ≤ lowerGamma x y) ∧
    
    (∀ x y : ℝ, 0 < x → 1 ≤ y → Real.exp (-1) / x ≤ lowerGamma x y) ∧
    
    (∀ x y : ℝ, 0 < x → 0 < y → lowerGamma x y ≤ Real.Gamma x) ∧
    
    (∀ x : ℝ, 0 < x → MonotoneOn (fun y : ℝ => lowerGamma x y) (Set.Ioi (0 : ℝ))) ∧
    
    (∀ N s x : ℝ, 0 < N → 0 < s → 0 < x →
      lowerGamma (N + s) x ≤ x ^ s * lowerGamma N x) ∧
    
    (∀ N s : ℝ, 0 < N → 0 < s →
      MonotoneOn (fun x : ℝ => lowerGamma (N + s) x / lowerGamma N x) (Set.Ioi (0 : ℝ))) := by
  /- @proof-region region.target-node.session.e83a8c10fdd0e42c begin -/
  have hpow : ∀ (x y : ℝ), 0 < x → 0 < y →
      (∫ z in (0 : ℝ)..y, z ^ (x - 1)) = y ^ x / x := by
    intro x y hx hy
    rw [integral_rpow (a := 0) (b := y) (r := x - 1)
      (Or.inl (by linarith : (-1 : ℝ) < x - 1))]
    have h2 : x - 1 + 1 = x := by ring
    rw [h2]
    rw [Real.zero_rpow (ne_of_gt hx)]
    ring
  have hInt : ∀ (x : ℝ), 0 < x → ∀ y : ℝ,
      IntervalIntegrable (fun z : ℝ => z ^ (x - 1) * Real.exp (-z)) volume 0 y := by
    intro x hx y
    exact (intervalIntegral.intervalIntegrable_rpow'
      (by linarith : (-1 : ℝ) < x - 1)).mul_continuousOn
      (Real.continuous_exp.comp_continuousOn continuous_neg.continuousOn)
  have ha : ∀ x y : ℝ, 0 < x → 0 < y → 0 < lowerGamma x y := by
    intro x y hx hy
    unfold lowerGamma
    exact intervalIntegral.intervalIntegral_pos_of_pos_on (hInt x hx y)
      (fun z hz => mul_pos (Real.rpow_pos_of_pos hz.1 (x - 1)) (Real.exp_pos (-z))) hy
  have hb : ∀ x y : ℝ, 0 < x → 0 < y → lowerGamma x y ≤ y ^ x / x := by
    intro x y hx hy
    unfold lowerGamma
    have hle : (∫ z in (0 : ℝ)..y, z ^ (x - 1) * Real.exp (-z)) ≤
        ∫ z in (0 : ℝ)..y, z ^ (x - 1) :=
      intervalIntegral.integral_mono_on_of_le_Ioo (le_of_lt hy) (hInt x hx y)
        (intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < x - 1))
        (fun z hz => by
          have he : Real.exp (-z) ≤ 1 := by
            have h' : Real.exp (-z) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith [hz.1])
            simpa using h'
          exact mul_le_of_le_one_right (Real.rpow_nonneg (le_of_lt hz.1) (x - 1)) he)
    calc (∫ z in (0 : ℝ)..y, z ^ (x - 1) * Real.exp (-z)) ≤
          ∫ z in (0 : ℝ)..y, z ^ (x - 1) := hle
      _ = y ^ x / x := hpow x y hx hy
  have hc : ∀ x y : ℝ, 0 < x → 0 < y → Real.exp (-y) * y ^ x / x ≤ lowerGamma x y := by
    intro x y hx hy
    unfold lowerGamma
    have hint2 : IntervalIntegrable (fun z : ℝ => Real.exp (-y) * z ^ (x - 1)) volume 0 y :=
      (intervalIntegral.intervalIntegrable_rpow'
        (by linarith : (-1 : ℝ) < x - 1)).const_mul (Real.exp (-y))
    have hle : (∫ z in (0 : ℝ)..y, Real.exp (-y) * z ^ (x - 1)) ≤
        ∫ z in (0 : ℝ)..y, z ^ (x - 1) * Real.exp (-z) :=
      intervalIntegral.integral_mono_on_of_le_Ioo (le_of_lt hy) hint2 (hInt x hx y)
        (fun z hz => by
          have he : Real.exp (-y) ≤ Real.exp (-z) := Real.exp_le_exp.mpr (by linarith [hz.2])
          have hmono : Real.exp (-y) * z ^ (x - 1) ≤ Real.exp (-z) * z ^ (x - 1) :=
            mul_le_mul_of_nonneg_right he (Real.rpow_nonneg (le_of_lt hz.1) (x - 1))
          calc Real.exp (-y) * z ^ (x - 1) ≤ Real.exp (-z) * z ^ (x - 1) := hmono
            _ = z ^ (x - 1) * Real.exp (-z) := by ring)
    have heq : Real.exp (-y) * y ^ x / x =
        ∫ z in (0 : ℝ)..y, Real.exp (-y) * z ^ (x - 1) := by
      rw [intervalIntegral.integral_const_mul, hpow x y hx hy]
      ring
    rw [heq]
    exact hle
  have hmonoY : ∀ x : ℝ, 0 < x → MonotoneOn (fun y : ℝ => lowerGamma x y) (Set.Ioi 0) := by
    intro x hx y hy y' hy' hle
    unfold lowerGamma
    have hae : 0 ≤ᶠ[ae (volume.restrict (Set.Ioc (0 : ℝ) y'))]
        fun z : ℝ => z ^ (x - 1) * Real.exp (-z) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with z hz
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt hz.1) (x - 1)) (Real.exp_pos (-z)).le
    exact intervalIntegral.integral_mono_interval (le_refl (0 : ℝ)) (le_of_lt hy) hle hae
      (hInt x hx y')
  have hG : ∀ N s x : ℝ, 0 < N → 0 < s → 0 < x →
      lowerGamma (N + s) x ≤ x ^ s * lowerGamma N x := by
    intro N s x hN hs hx
    unfold lowerGamma
    have hA : IntervalIntegrable (fun z : ℝ => z ^ ((N + s) - 1) * Real.exp (-z)) volume 0 x :=
      hInt (N + s) (by linarith) x
    have hB : IntervalIntegrable (fun z : ℝ => x ^ s * (z ^ (N - 1) * Real.exp (-z))) volume 0 x :=
      (hInt N hN x).const_mul (x ^ s)
    have key : ∀ z ∈ Set.Ioo (0 : ℝ) x,
        z ^ ((N + s) - 1) * Real.exp (-z) ≤ x ^ s * (z ^ (N - 1) * Real.exp (-z)) := by
      intro z hz
      have hzpos : (0 : ℝ) < z := hz.1
      have hsplit : z ^ ((N + s) - 1) = z ^ (N - 1) * z ^ s := by
        rw [show (N + s) - 1 = (N - 1) + s by ring, Real.rpow_add hzpos]
      have hzxs : z ^ s ≤ x ^ s :=
        Real.rpow_le_rpow (le_of_lt hzpos) (le_of_lt hz.2) (le_of_lt hs)
      calc z ^ ((N + s) - 1) * Real.exp (-z)
          = (z ^ (N - 1) * z ^ s) * Real.exp (-z) := by rw [hsplit]
        _ ≤ (z ^ (N - 1) * x ^ s) * Real.exp (-z) := by
            apply mul_le_mul_of_nonneg_right _ (le_of_lt (Real.exp_pos (-z)))
            exact mul_le_mul_of_nonneg_left hzxs (Real.rpow_nonneg (le_of_lt hzpos) (N - 1))
        _ = x ^ s * (z ^ (N - 1) * Real.exp (-z)) := by ring
    have hmain : (∫ z in (0 : ℝ)..x, z ^ ((N + s) - 1) * Real.exp (-z)) ≤
        ∫ z in (0 : ℝ)..x, x ^ s * (z ^ (N - 1) * Real.exp (-z)) :=
      intervalIntegral.integral_mono_on_of_le_Ioo (le_of_lt hx) hA hB key
    rw [intervalIntegral.integral_const_mul] at hmain
    exact hmain
  refine ⟨ha, hb, hc, ?_, ?_, hmonoY, hG, ?_⟩
  · intro x y hx hy1
    have hy : (0 : ℝ) < y := lt_of_lt_of_le zero_lt_one hy1
    have h1 : lowerGamma x 1 ≤ lowerGamma x y :=
      hmonoY x hx (by simp : (1 : ℝ) ∈ Set.Ioi (0 : ℝ))
        (by simpa using hy : y ∈ Set.Ioi (0 : ℝ)) hy1
    have h2 : Real.exp (-1) / x ≤ lowerGamma x 1 := by
      simpa using hc x 1 hx zero_lt_one
    linarith
  · intro x y hx hy
    have hIoi : IntegrableOn (fun z : ℝ => z ^ (x - 1) * Real.exp (-z)) (Set.Ioi 0) volume := by
      have h := integrableOn_rpow_mul_exp_neg_rpow (p := (1 : ℝ)) (s := x - 1)
        (by linarith : (-1 : ℝ) < x - 1) le_rfl
      simpa using h
    have hnonneg : 0 ≤ᶠ[ae (volume.restrict (Set.Ioi (0 : ℝ)))]
        fun z : ℝ => z ^ (x - 1) * Real.exp (-z) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      have hz0 : (0 : ℝ) < z := hz
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt hz0) (x - 1)) (Real.exp_pos (-z)).le
    have hle : (∫ z in Set.Ioc (0 : ℝ) y, z ^ (x - 1) * Real.exp (-z)) ≤
        ∫ z in Set.Ioi (0 : ℝ), z ^ (x - 1) * Real.exp (-z) :=
      MeasureTheory.setIntegral_mono_set hIoi hnonneg (by
        filter_upwards with z hz
        exact hz.1)
    rw [Real.Gamma_eq_integral hx]
    unfold lowerGamma
    rw [intervalIntegral.integral_of_le (le_of_lt hy)]
    calc (∫ z in Set.Ioc (0 : ℝ) y, z ^ (x - 1) * Real.exp (-z))
        ≤ ∫ z in Set.Ioi (0 : ℝ), z ^ (x - 1) * Real.exp (-z) := hle
      _ = ∫ z in Set.Ioi (0 : ℝ), Real.exp (-z) * z ^ (x - 1) := by
          simp only [mul_comm]
  · intro N s hN hs x hx y hy hxy
    have hBx : 0 < lowerGamma N x := ha N x hN hx
    have hAx : lowerGamma (N + s) x ≤ x ^ s * lowerGamma N x := hG N s x hN hs hx
    have hseg : ∀ (r : ℝ), 0 < r →
        IntervalIntegrable (fun z : ℝ => z ^ (r - 1) * Real.exp (-z)) volume x y := by
      intro r hr
      exact (intervalIntegral.intervalIntegrable_rpow'
        (by linarith : (-1 : ℝ) < r - 1)).mul_continuousOn
        (Real.continuous_exp.comp_continuousOn continuous_neg.continuousOn)
    have hsplitA : lowerGamma (N + s) y
        = lowerGamma (N + s) x + ∫ z in x..y, z ^ ((N + s) - 1) * Real.exp (-z) := by
      unfold lowerGamma
      rw [← intervalIntegral.integral_add_adjacent_intervals (hInt (N + s) (by linarith) x)
        (hseg (N + s) (by linarith))]
    have hsplitB : lowerGamma N y
        = lowerGamma N x + ∫ z in x..y, z ^ (N - 1) * Real.exp (-z) := by
      unfold lowerGamma
      rw [← intervalIntegral.integral_add_adjacent_intervals (hInt N hN x) (hseg N hN)]
    have hQnn : 0 ≤ ∫ z in x..y, z ^ (N - 1) * Real.exp (-z) := by
      rw [intervalIntegral.integral_of_le hxy]
      exact MeasureTheory.setIntegral_nonneg measurableSet_Ioc
        (fun z hz => mul_nonneg
          (Real.rpow_nonneg (le_of_lt (lt_trans hx hz.1)) (N - 1))
          (Real.exp_pos (-z)).le)
    have hPQ : x ^ s * (∫ z in x..y, z ^ (N - 1) * Real.exp (-z))
        ≤ ∫ z in x..y, z ^ ((N + s) - 1) * Real.exp (-z) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on_of_le_Ioo hxy
        ((hseg N hN).const_mul (x ^ s)) (hseg (N + s) (by linarith)) ?_
      intro z hz
      have hzpos : (0 : ℝ) < z := lt_trans hx hz.1
      have hzs : x ^ s ≤ z ^ s :=
        Real.rpow_le_rpow (le_of_lt hx) (le_of_lt hz.1) (le_of_lt hs)
      have hsplit : z ^ ((N + s) - 1) = z ^ (N - 1) * z ^ s := by
        rw [show (N + s) - 1 = (N - 1) + s by ring, Real.rpow_add hzpos]
      calc x ^ s * (z ^ (N - 1) * Real.exp (-z))
          = (z ^ (N - 1) * x ^ s) * Real.exp (-z) := by ring
        _ ≤ (z ^ (N - 1) * z ^ s) * Real.exp (-z) := by
            apply mul_le_mul_of_nonneg_right _ (le_of_lt (Real.exp_pos (-z)))
            exact mul_le_mul_of_nonneg_left hzs (Real.rpow_nonneg (le_of_lt hzpos) (N - 1))
        _ = z ^ ((N + s) - 1) * Real.exp (-z) := by rw [hsplit]
    change lowerGamma (N + s) x / lowerGamma N x ≤ lowerGamma (N + s) y / lowerGamma N y
    rw [hsplitA, hsplitB]
    have hBQ : (0 : ℝ) < lowerGamma N x + ∫ z in x..y, z ^ (N - 1) * Real.exp (-z) := by
      linarith
    have step : lowerGamma (N + s) x * (∫ z in x..y, z ^ (N - 1) * Real.exp (-z))
        ≤ (∫ z in x..y, z ^ ((N + s) - 1) * Real.exp (-z)) * lowerGamma N x := by
      have h1 : lowerGamma (N + s) x * (∫ z in x..y, z ^ (N - 1) * Real.exp (-z))
          ≤ (x ^ s * lowerGamma N x) * (∫ z in x..y, z ^ (N - 1) * Real.exp (-z)) :=
        mul_le_mul_of_nonneg_right hAx hQnn
      have h2 : (x ^ s * lowerGamma N x) * (∫ z in x..y, z ^ (N - 1) * Real.exp (-z))
          ≤ (∫ z in x..y, z ^ ((N + s) - 1) * Real.exp (-z)) * lowerGamma N x := by
        have h3 := mul_le_mul_of_nonneg_left hPQ (le_of_lt hBx)
        nlinarith [h3]
      linarith
    have hne1 : lowerGamma N x ≠ 0 := ne_of_gt hBx
    have hne2 : lowerGamma N x + ∫ z in x..y, z ^ (N - 1) * Real.exp (-z) ≠ 0 := ne_of_gt hBQ
    field_simp
    nlinarith [step]
  /- @proof-region region.target-node.session.e83a8c10fdd0e42c end -/

end Statlib.Imported
end
