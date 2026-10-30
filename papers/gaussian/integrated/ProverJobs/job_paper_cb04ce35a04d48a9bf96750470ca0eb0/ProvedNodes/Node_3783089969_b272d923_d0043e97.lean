import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Vocabulary
import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Base

namespace PaperProofTasks.job_paper_cb04ce35a04d48a9bf96750470ca0eb0

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
open _root_.PaperProofTasks.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Statlib.Imported

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
namespace Statlib.Imported
open _root_.Statlib
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_3783089969_b272d923 : ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (p : ℕ → ℕ) (X : (n : ℕ) → Fin n → Ω → (Fin (p n) → ℝ))
    (hX_meas : ∀ (n : ℕ) (i : Fin n) (j : Fin (p n)),
      AEStronglyMeasurable (fun ω : Ω => X n i ω j) μ)
    (muV : (n : ℕ) → Fin (p n) → ℝ)
    (Sig : (n : ℕ) → Matrix (Fin (p n)) (Fin (p n)) ℝ)
    (tau : ℕ → ℝ) (n : ℕ) (hn1 : 1 ≤ n) (j : Fin (p n))
    (hsigma_pos : 0 < Sig n j j) (htau_lt_one : tau n < 1)
    (q T c : ℝ) (hq2 : 2 ≤ q) (hT : 0 < T)
    (hH : ∫⁻ ω, ENNReal.ofReal (|(Real.sqrt (Sig n j j))⁻¹ *
        ((Real.sqrt (n : ℝ))⁻¹ * ∑ i : Fin n, (X n i ω j - muV n j))| ^ q) ∂μ
      ≤ ENNReal.ofReal ((c * q) ^ q)),
    μ {ω : Ω | T < Svec p X muV n ω j / Real.rpow (Real.sqrt (Sig n j j)) (tau n)}
      ≤ ENNReal.ofReal
          (Real.rpow (Real.sqrt (Sig n j j)) (q * (1 - tau n)) * (c * q) ^ q / T ^ q) := by
  /- @proof-region region.target-node.session.206481c9590cd7e6 begin -/
  intro Ω _ μ _ p X hX_meas muV Sig tau n hn1 j hsigma_pos htau_lt_one q T c hq2 hT hH
  have hσ_root_pos : 0 < Real.sqrt (Sig n j j) := Real.sqrt_pos.mpr hsigma_pos
  set σ : ℝ := Real.sqrt (Sig n j j) with hσ
  have hσpos : 0 < σ := by rw [hσ]; exact hσ_root_pos
  have hσne : σ ≠ 0 := ne_of_gt hσpos
  set A : Ω → ℝ := fun ω => σ⁻¹ * ((Real.sqrt (n : ℝ))⁻¹ * ∑ i : Fin n, (X n i ω j - muV n j)) with hA
  have hH' : ∫⁻ ω, ENNReal.ofReal (|A ω| ^ q) ∂μ ≤ ENNReal.ofReal ((c * q) ^ q) := by
    simpa only [hA, ← hσ] using hH
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    linarith
  have hsqrt_n : Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) = (Real.sqrt (n : ℝ))⁻¹ := by
    change (n : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (n : ℝ))⁻¹
    rw [Real.rpow_neg hn_nonneg (1 / 2), ← Real.sqrt_eq_rpow]
  have hSvec_eq : ∀ ω : Ω, Svec p X muV n ω j = σ * A ω := by
    intro ω
    have h1 : Svec p X muV n ω j
        = (Real.sqrt (n : ℝ))⁻¹ * ∑ i : Fin n, (X n i ω j - muV n j) := by
      simp only [Svec, hsqrt_n]
    rw [h1]
    simp only [hA]
    rw [← mul_assoc, mul_inv_cancel₀ hσne, one_mul]
  have hf_eq : ∀ ω : Ω, ENNReal.ofReal (|Svec p X muV n ω j / Real.rpow σ (tau n)| ^ q)
      = ENNReal.ofReal (Real.rpow σ (q * (1 - tau n))) * ENNReal.ofReal (|A ω| ^ q) := by
    intro ω
    change ENNReal.ofReal (|Svec p X muV n ω j / σ ^ (tau n)| ^ q)
        = ENNReal.ofReal (σ ^ (q * (1 - tau n))) * ENNReal.ofReal (|A ω| ^ q)
    have hstart : Svec p X muV n ω j / σ ^ (tau n) = σ ^ (1 - tau n) * A ω := by
      rw [hSvec_eq ω]
      have hpow : σ ^ (1 - tau n) = σ / σ ^ (tau n) := by
        rw [Real.rpow_sub hσpos, Real.rpow_one]
      rw [hpow]
      ring
    have habs : |σ ^ (1 - tau n) * A ω| ^ q = σ ^ (q * (1 - tau n)) * |A ω| ^ q := by
      calc |σ ^ (1 - tau n) * A ω| ^ q
          = (|σ ^ (1 - tau n)| * |A ω|) ^ q := by rw [abs_mul]
        _ = |σ ^ (1 - tau n)| ^ q * |A ω| ^ q := by
              rw [Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
        _ = (σ ^ (1 - tau n)) ^ q * |A ω| ^ q := by
              rw [abs_of_nonneg (Real.rpow_nonneg hσpos.le (1 - tau n))]
        _ = σ ^ ((1 - tau n) * q) * |A ω| ^ q := by
              rw [← Real.rpow_mul hσpos.le]
        _ = σ ^ (q * (1 - tau n)) * |A ω| ^ q := by
              rw [show (1 - tau n) * q = q * (1 - tau n) by ring]
    rw [hstart, habs, ENNReal.ofReal_mul (Real.rpow_nonneg hσpos.le (q * (1 - tau n)))]
  have hsum : AEMeasurable (fun ω : Ω => ∑ i : Fin n, (X n i ω j - muV n j)) μ :=
    Finset.aemeasurable_fun_sum (Finset.univ : Finset (Fin n)) (f := fun i ω => X n i ω j - muV n j)
      (fun i _ => (hX_meas n i j).aemeasurable.sub aemeasurable_const)
  have hmeas_g : AEMeasurable (fun ω : Ω => ENNReal.ofReal (|A ω| ^ q)) μ := by
    have hA_meas : AEMeasurable A μ := by
      rw [hA]
      exact AEMeasurable.const_mul (AEMeasurable.const_mul hsum ((Real.sqrt (n : ℝ))⁻¹)) σ⁻¹
    have hq0 : (0 : ℝ) ≤ q := by linarith
    have habs : AEMeasurable (fun ω : Ω => |A ω| ^ q) μ :=
      (Real.continuous_rpow_const hq0).measurable.comp_aemeasurable hA_meas.abs
    exact ENNReal.measurable_ofReal.comp_aemeasurable habs
  have hmeas : AEMeasurable
      (fun ω : Ω => ENNReal.ofReal (|Svec p X muV n ω j / Real.rpow σ (tau n)| ^ q)) μ := by
    have hfg : AEMeasurable
        (fun ω : Ω => ENNReal.ofReal (Real.rpow σ (q * (1 - tau n))) * ENNReal.ofReal (|A ω| ^ q)) μ :=
      hmeas_g.const_mul (ENNReal.ofReal (Real.rpow σ (q * (1 - tau n))))
    refine hfg.congr ?_
    filter_upwards with ω
    exact (hf_eq ω).symm
  have hInt : ∫⁻ ω, ENNReal.ofReal (|Svec p X muV n ω j / Real.rpow σ (tau n)| ^ q) ∂μ
      ≤ ENNReal.ofReal (Real.rpow σ (q * (1 - tau n)) * (c * q) ^ q) := by
    have hcongr : ∫⁻ ω, ENNReal.ofReal (|Svec p X muV n ω j / Real.rpow σ (tau n)| ^ q) ∂μ
        = ∫⁻ ω, ENNReal.ofReal (Real.rpow σ (q * (1 - tau n))) * ENNReal.ofReal (|A ω| ^ q) ∂μ := by
      apply lintegral_congr
      intro ω
      exact hf_eq ω
    rw [hcongr, MeasureTheory.lintegral_const_mul''
      (ENNReal.ofReal (Real.rpow σ (q * (1 - tau n)))) hmeas_g]
    refine le_trans (mul_le_mul_left' hH'
      (ENNReal.ofReal (Real.rpow σ (q * (1 - tau n))))) ?_
    change ENNReal.ofReal (σ ^ (q * (1 - tau n))) * ENNReal.ofReal ((c * q) ^ q)
        ≤ ENNReal.ofReal (σ ^ (q * (1 - tau n)) * (c * q) ^ q)
    exact le_of_eq (ENNReal.ofReal_mul (Real.rpow_nonneg hσpos.le (q * (1 - tau n)))).symm
  have hMarkov : μ {ω : Ω | T < Svec p X muV n ω j / Real.rpow σ (tau n)}
      ≤ ENNReal.ofReal (Real.rpow σ (q * (1 - tau n)) * (c * q) ^ q) / ENNReal.ofReal (T ^ q) := by
    have hTq_pos : 0 < T ^ q := Real.rpow_pos_of_pos hT q
    have hε_ne_zero : ENNReal.ofReal (T ^ q) ≠ 0 := by
      intro h
      rw [ENNReal.ofReal_eq_zero] at h
      linarith
    have hε_ne_top : ENNReal.ofReal (T ^ q) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hsubset : {ω : Ω | T < Svec p X muV n ω j / Real.rpow σ (tau n)} ⊆
        {ω : Ω | ENNReal.ofReal (T ^ q) ≤
          ENNReal.ofReal (|Svec p X muV n ω j / Real.rpow σ (tau n)| ^ q)} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      apply ENNReal.ofReal_le_ofReal
      have hT_le : T ≤ |Svec p X muV n ω j / Real.rpow σ (tau n)| :=
        le_trans (le_of_lt hω) (le_abs_self _)
      exact Real.rpow_le_rpow hT.le hT_le (by linarith)
    calc μ {ω : Ω | T < Svec p X muV n ω j / Real.rpow σ (tau n)}
        ≤ μ {ω : Ω | ENNReal.ofReal (T ^ q) ≤
            ENNReal.ofReal (|Svec p X muV n ω j / Real.rpow σ (tau n)| ^ q)} :=
          measure_mono hsubset
      _ ≤ (∫⁻ ω, ENNReal.ofReal (|Svec p X muV n ω j / Real.rpow σ (tau n)| ^ q) ∂μ)
            / ENNReal.ofReal (T ^ q) :=
          MeasureTheory.meas_ge_le_lintegral_div hmeas hε_ne_zero hε_ne_top
      _ ≤ ENNReal.ofReal (Real.rpow σ (q * (1 - tau n)) * (c * q) ^ q) / ENNReal.ofReal (T ^ q) :=
          ENNReal.div_le_div_right hInt (ENNReal.ofReal (T ^ q))
  have hTq_pos : 0 < T ^ q := Real.rpow_pos_of_pos hT q
  have hdiv_eq :
      ENNReal.ofReal (Real.rpow σ (q * (1 - tau n)) * (c * q) ^ q) / ENNReal.ofReal (T ^ q)
        = ENNReal.ofReal (Real.rpow σ (q * (1 - tau n)) * (c * q) ^ q / T ^ q) := by
    rw [ENNReal.ofReal_div_of_pos hTq_pos]
  calc μ {ω : Ω | T < Svec p X muV n ω j / Real.rpow σ (tau n)}
      ≤ ENNReal.ofReal (Real.rpow σ (q * (1 - tau n)) * (c * q) ^ q) / ENNReal.ofReal (T ^ q) := hMarkov
    _ = ENNReal.ofReal (Real.rpow σ (q * (1 - tau n)) * (c * q) ^ q / T ^ q) := hdiv_eq
  /- @proof-region region.target-node.session.206481c9590cd7e6 end -/

end

end Statlib.Imported

