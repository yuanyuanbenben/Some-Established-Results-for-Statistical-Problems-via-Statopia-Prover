import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M000_Vocabulary
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M001_Base

/- Original module ProverJobs.job_paper_dc88427b52844263b5321fc99eb582d8.ProvedNodes.Node_3968451938_9cda8590_a46b8445; genuine source relocated, namespace-isolated only. -/
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
theorem statopia_math_node_3968451938_9cda8590 : ∀ (c m U : ℝ) (hc : 0 < c) (hm : 0 < m) (hU : 0 < U)
    (a : ℕ) (ha : 1 ≤ a)
    (thetas : ℝ) (phi q0 : ℝ → ℝ)
    (h1 : ∀ θ : ℝ, 0 ≤ phi θ)
    (h2 : ∀ θ : ℝ, phi θ ≤ max 0 (1 - m * |θ - thetas|))
    (h3 : ∀ θ : ℝ, 2 * c ≤ |θ - thetas| → phi θ = 0)
    (h4 : ∀ θ : ℝ, 0 ≤ q0 θ)
    (h5 : ∀ y ∈ Set.Icc (0 : ℝ) (2 * c), q0 (thetas + y) + q0 (thetas - y) ≤ U)
    (h6 : 2 * c * m ≤ 1),
    ∫ θ : ℝ, (phi θ) ^ a * q0 θ ∂volume ≤ U / (m * ((a : ℝ) + 1)) := by
  /- @proof-region region.target-node.session.a46260d62613751d begin -/
  intro c m U hc hm hU a ha thetaS phi q0 h1 h2 h3 h4 h5 h6
  by_cases hInt : Integrable (fun θ : ℝ => (phi θ) ^ a * q0 θ) volume
  ·
    have hIIR : IntervalIntegrable (fun x : ℝ => (phi x) ^ a * q0 x) volume thetaS (thetaS + 2 * c) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : thetaS ≤ thetaS + 2 * c)).mpr
        hInt.integrableOn
    have hIIL : IntervalIntegrable (fun x : ℝ => (phi x) ^ a * q0 x) volume (thetaS - 2 * c) thetaS :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : thetaS - 2 * c ≤ thetaS)).mpr
        hInt.integrableOn
    have hsupp : ∀ θ : ℝ, θ ∉ Set.Ioc (thetaS - 2 * c) (thetaS + 2 * c) →
        (phi θ) ^ a * q0 θ = 0 := by
      intro θ hθ
      have h2c : 2 * c ≤ |θ - thetaS| := by
        rw [Set.mem_Ioc] at hθ
        by_cases h : θ ≤ thetaS - 2 * c
        · rw [abs_sub_comm, abs_of_nonneg (by linarith)]
          linarith
        · push_neg at h
          have h2 : thetaS + 2 * c < θ := by
            by_contra hcon
            push_neg at hcon
            exact hθ ⟨h, hcon⟩
          rw [abs_of_pos (by linarith)]
          linarith
      rw [h3 θ h2c, zero_pow (by omega : a ≠ 0), zero_mul]
    have hstep1 : (∫ x : ℝ, (phi x) ^ a * q0 x ∂volume)
        = ∫ x in (thetaS - 2 * c)..(thetaS + 2 * c), (phi x) ^ a * q0 x ∂volume := by
      rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := Set.Ioc (thetaS - 2 * c) (thetaS + 2 * c)) hsupp]
      exact (intervalIntegral.integral_of_le (by linarith)).symm
    have hAR : IntervalIntegrable (fun y : ℝ => (phi (y + thetaS)) ^ a * q0 (y + thetaS)) volume 0 (2 * c) := by
      have h := IntervalIntegrable.comp_add_right hIIR thetaS
      have e1 : thetaS - thetaS = (0 : ℝ) := by ring
      have e2 : thetaS + 2 * c - thetaS = 2 * c := by ring
      rw [e1, e2] at h
      exact h
    have hBR : IntervalIntegrable (fun y : ℝ => (phi (thetaS - y)) ^ a * q0 (thetaS - y)) volume 0 (2 * c) := by
      have h := IntervalIntegrable.comp_sub_left hIIL thetaS
      have e1 : thetaS - thetaS = (0 : ℝ) := by ring
      have e2 : thetaS - (thetaS - 2 * c) = 2 * c := by ring
      rw [e1, e2] at h
      exact IntervalIntegrable.symm h
    have hright : (∫ x in thetaS..(thetaS + 2 * c), (phi x) ^ a * q0 x ∂volume)
        = ∫ y in (0)..(2 * c), (phi (y + thetaS)) ^ a * q0 (y + thetaS) ∂volume := by
      have h := intervalIntegral.integral_comp_add_right (a := 0) (b := 2 * c)
        (fun x : ℝ => (phi x) ^ a * q0 x) thetaS
      rw [zero_add] at h
      rw [show (2 * c : ℝ) + thetaS = thetaS + 2 * c by ring] at h
      exact h.symm
    have hleft : (∫ x in (thetaS - 2 * c)..thetaS, (phi x) ^ a * q0 x ∂volume)
        = ∫ y in (0)..(2 * c), (phi (thetaS - y)) ^ a * q0 (thetaS - y) ∂volume := by
      have h := intervalIntegral.integral_comp_sub_left (a := 0) (b := 2 * c)
        (fun x : ℝ => (phi x) ^ a * q0 x) thetaS
      rw [sub_zero] at h
      exact h.symm
    have hsplit1 : (∫ x in (thetaS - 2 * c)..(thetaS + 2 * c), (phi x) ^ a * q0 x ∂volume)
        = ∫ x in (thetaS - 2 * c)..thetaS, (phi x) ^ a * q0 x ∂volume
          + ∫ x in thetaS..(thetaS + 2 * c), (phi x) ^ a * q0 x ∂volume :=
      (intervalIntegral.integral_add_adjacent_intervals
        (a := thetaS - 2 * c) (b := thetaS) (c := thetaS + 2 * c) hIIL hIIR).symm
    have hsplit : (∫ x in (thetaS - 2 * c)..(thetaS + 2 * c), (phi x) ^ a * q0 x ∂volume)
        = ∫ y in (0)..(2 * c),
            ((phi (y + thetaS)) ^ a * q0 (y + thetaS) + (phi (thetaS - y)) ^ a * q0 (thetaS - y)) ∂volume := by
      rw [hsplit1, hleft, hright, intervalIntegral.integral_add hAR hBR]
      exact add_comm _ _
    have hnc : (0 : ℝ) ≤ 2 * c := by linarith
    have hbound : (∫ y in (0)..(2 * c),
          ((phi (y + thetaS)) ^ a * q0 (y + thetaS) + (phi (thetaS - y)) ^ a * q0 (thetaS - y)) ∂volume)
        ≤ ∫ y in (0)..(2 * c), U * (1 - m * y) ^ a ∂volume := by
      apply intervalIntegral.integral_mono_on hnc (hAR.add hBR)
      · exact (continuous_const.mul ((continuous_const.sub (continuous_const.mul continuous_id)).pow a)).intervalIntegrable _ _
      · intro y hy
        obtain ⟨hy0, hy2⟩ := hy
        have hmy : m * y ≤ 1 := by
          have hp : m * y ≤ m * (2 * c) := mul_le_mul_of_nonneg_left hy2 (le_of_lt hm)
          nlinarith [h6]
        have hwy : (0 : ℝ) ≤ 1 - m * y := by linarith
        have hAl : (phi (y + thetaS)) ^ a * q0 (y + thetaS) ≤ (1 - m * y) ^ a * q0 (y + thetaS) := by
          have hab : |(y + thetaS) - thetaS| = y := by
            rw [add_sub_cancel_right, abs_of_nonneg hy0]
          have hle : phi (y + thetaS) ≤ 1 - m * y := by
            have hh := h2 (y + thetaS)
            rw [hab, max_eq_right hwy] at hh
            exact hh
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (h1 (y + thetaS)) hle a) (h4 (y + thetaS))
        have hBl : (phi (thetaS - y)) ^ a * q0 (thetaS - y) ≤ (1 - m * y) ^ a * q0 (thetaS - y) := by
          have hab : |(thetaS - y) - thetaS| = y := by
            have e : (thetaS - y) - thetaS = -y := by ring
            rw [e, abs_neg, abs_of_nonneg hy0]
          have hle : phi (thetaS - y) ≤ 1 - m * y := by
            have hh := h2 (thetaS - y)
            rw [hab, max_eq_right hwy] at hh
            exact hh
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (h1 (thetaS - y)) hle a) (h4 (thetaS - y))
        have hp : (1 - m * y) ^ a * (q0 (y + thetaS) + q0 (thetaS - y)) ≤ (1 - m * y) ^ a * U := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg hwy a)
          rw [add_comm y thetaS]
          exact h5 y ⟨hy0, hy2⟩
        calc (phi (y + thetaS)) ^ a * q0 (y + thetaS) + (phi (thetaS - y)) ^ a * q0 (thetaS - y)
            ≤ (1 - m * y) ^ a * q0 (y + thetaS) + (1 - m * y) ^ a * q0 (thetaS - y) := add_le_add hAl hBl
          _ = (1 - m * y) ^ a * (q0 (y + thetaS) + q0 (thetaS - y)) := by ring
          _ ≤ (1 - m * y) ^ a * U := hp
          _ = U * (1 - m * y) ^ a := by ring
    have hconstU : (∫ y in (0)..(2 * c), U * (1 - m * y) ^ a ∂volume)
        = U * ∫ y in (0)..(2 * c), (1 - m * y) ^ a ∂volume :=
      intervalIntegral.integral_const_mul U _
    have hsc : (∫ y in (0)..(2 * c), (1 - m * y) ^ a ∂volume)
        = m⁻¹ * ∫ s in (0)..(2 * c * m), (1 - s) ^ a ∂volume := by
      have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := 2 * c) (c := m)
        (fun s : ℝ => (1 - s) ^ a) (ne_of_gt hm)
      simp only [mul_zero, smul_eq_mul] at h
      rw [show m * (2 * c) = 2 * c * m by ring] at h
      exact h
    have hmono : (∫ s in (0)..(2 * c * m), (1 - s) ^ a ∂volume)
        ≤ ∫ s in (0)..1, (1 - s) ^ a ∂volume := by
      apply intervalIntegral.integral_mono_interval
      · norm_num
      · exact mul_nonneg (by linarith) (le_of_lt hm)
      · exact h6
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
        exact pow_nonneg (by linarith [hs.2]) a
      · exact ((continuous_const.sub continuous_id).pow a).intervalIntegrable _ _
    have hval : (∫ s in (0)..1, (1 - s) ^ a ∂volume) = 1 / ((a : ℝ) + 1) := by
      have h1 : (∫ s in (0)..1, (1 - s) ^ a ∂volume) = ∫ s in (0)..1, s ^ a ∂volume := by
        have h := intervalIntegral.integral_comp_sub_left (a := 0) (b := 1) (fun s : ℝ => s ^ a) 1
        simpa using h
      rw [h1]
      have hz : (0 : ℝ) ^ (a + 1) = 0 := zero_pow (by omega)
      have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
          HasDerivAt (fun s : ℝ => s ^ (a + 1) / ((a : ℝ) + 1)) (x ^ a) x := by
        intro x hx
        have hbase : HasDerivAt (fun s : ℝ => s ^ (a + 1)) (((a : ℝ) + 1) * x ^ a) x := by
          have hp := hasDerivAt_pow (a + 1) x
          simpa [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] using hp
        have hdiv := hbase.div_const ((a : ℝ) + 1)
        have hne : ((a : ℝ) + 1) ≠ 0 := by positivity
        convert hdiv using 1
        field_simp
      have hint : IntervalIntegrable (fun s : ℝ => s ^ a) volume 0 1 :=
        intervalIntegral.intervalIntegrable_pow a
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, one_pow, hz, zero_div, sub_zero]
    calc (∫ x : ℝ, (phi x) ^ a * q0 x ∂volume)
        = ∫ x in (thetaS - 2 * c)..(thetaS + 2 * c), (phi x) ^ a * q0 x ∂volume := hstep1
      _ = ∫ y in (0)..(2 * c),
            ((phi (y + thetaS)) ^ a * q0 (y + thetaS) + (phi (thetaS - y)) ^ a * q0 (thetaS - y)) ∂volume := hsplit
      _ ≤ ∫ y in (0)..(2 * c), U * (1 - m * y) ^ a ∂volume := hbound
      _ = U * ∫ y in (0)..(2 * c), (1 - m * y) ^ a ∂volume := hconstU
      _ = U * (m⁻¹ * ∫ s in (0)..(2 * c * m), (1 - s) ^ a ∂volume) := by rw [hsc]
      _ ≤ U * (m⁻¹ * (1 / ((a : ℝ) + 1))) := by
            have hinner : m⁻¹ * (∫ s in (0)..(2 * c * m), (1 - s) ^ a ∂volume)
                ≤ m⁻¹ * (1 / ((a : ℝ) + 1)) :=
              mul_le_mul_of_nonneg_left (le_trans hmono hval.le) (le_of_lt (inv_pos.mpr hm))
            exact mul_le_mul_of_nonneg_left hinner (le_of_lt hU)
      _ = U / (m * ((a : ℝ) + 1)) := by
            have hm0 : m ≠ 0 := ne_of_gt hm
            have ha0 : ((a : ℝ) + 1) ≠ 0 := by positivity
            field_simp
  · rw [MeasureTheory.integral_undef hInt]
    exact le_of_lt (div_pos hU (mul_pos hm (by positivity)))
  /- @proof-region region.target-node.session.a46260d62613751d end -/

end

end Statlib.Imported
end DPCompletedProof
