import ProverJobs.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Vocabulary
import ProverJobs.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Base
import ProverJobs.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.ProvedNodes.Node_176343912_26262eb8_a68f9353
import ProverJobs.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.ProvedNodes.Node_2747529702_f88a4914_a9c8f793

namespace PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed


open _root_.PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
universe u₀ u₁

set_option autoImplicit false in
theorem statopia_math_node_412305318_6575e435 : ∀ (p r k : ℕ) (hr : 1 ≤ r) (hrk : r ≤ k)
    (Om : Type*) [MeasurableSpace Om] (P : Measure Om) [IsProbabilityMeasure P]
    (Z : Om → Fin p → ℝ) (hZ : ∀ j : Fin p, Measurable (fun om => Z om j))
    (Q : Matrix (Fin p) (Fin r) ℝ) (hQ : Matrix.transpose Q * Q = 1)
    (c0 : ℝ) (hc0 : 0 < c0)
    (horlicz : ∀ l : Fin r,
      Statlib.StatFoundation.Vocabulary.orliczNorm 1
        (fun om => ∑ j : Fin p, Q j l * Z om j) P ≤ ENNReal.ofReal c0),
    MemLp (fun om => Real.sqrt (∑ l : Fin r, ((Matrix.transpose Q).mulVec (Z om)) l ^ 2)) 4 P ∧
    ∫ om, (Real.sqrt (∑ l : Fin r, ((Matrix.transpose Q).mulVec (Z om)) l ^ 2)) ^ 3 ∂P
      ≤ ((2 : ℝ) ^ ((1 : ℝ) / 4) * (4 / Real.exp 1) * c0) ^ 3 * (k : ℝ) ^ ((3 : ℝ) / 2) := by
  /- @proof-region region.target-node.session.bd92de47a09cc413 begin -/
  intro p r k hr hrk Om instOm P instP Z hZ Q hQ c0 hc0 hsubexp
  have hxi : ∀ l : Fin r, Measurable (fun om => ∑ j : Fin p, Q j l * Z om j) := by
    intro l
    have hsum : ∀ s : Finset (Fin p),
        Measurable (fun om => s.sum (fun j => Q j l * Z om j)) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using (measurable_const : Measurable fun _ : Om => (0 : ℝ))
      | insert a s ha ih =>
          have hfun : (fun om => (insert a s).sum (fun j => Q j l * Z om j))
              = (fun om => Q a l * Z om a + s.sum (fun j => Q j l * Z om j)) := by
            funext om
            exact Finset.sum_insert ha
          rw [hfun]
          exact (measurable_const.mul (hZ a)).add ih
    exact hsum Finset.univ
  have hcoord : ∀ l : Fin r, MemLp (fun om => ∑ j : Fin p, Q j l * Z om j) 4 P ∧
      ∫ om, (∑ j : Fin p, Q j l * Z om j) ^ 4 ∂P ≤ 2 * (4 / Real.exp 1) ^ 4 * c0 ^ 4 :=
    fun l => statopia_math_node_2747529702_f88a4914 Om P
      (fun om => ∑ j : Fin p, Q j l * Z om j) (hxi l) c0 hc0 (hsubexp l)
  have hmem : ∀ l : Fin r, MemLp (fun om => ∑ j : Fin p, Q j l * Z om j) 4 P :=
    fun l => (hcoord l).1
  have hint : ∀ l : Fin r,
      ∫ om, (∑ j : Fin p, Q j l * Z om j) ^ 4 ∂P ≤ 2 * (4 / Real.exp 1) ^ 4 * c0 ^ 4 :=
    fun l => (hcoord l).2
  set Sfun : Om → ℝ := fun om => ∑ l : Fin r, (∑ j : Fin p, Q j l * Z om j) ^ 2 with hSfun
  set Nfun : Om → ℝ := fun om => Real.sqrt (Sfun om) with hNfun
  have hSnn : ∀ om, 0 ≤ Sfun om := fun om => Finset.sum_nonneg fun l _ => sq_nonneg _
  have hNsq : ∀ om, Nfun om ^ 2 = Sfun om := fun om => Real.sq_sqrt (hSnn om)
  have hNpow : ∀ om, Nfun om ^ 4 = Sfun om ^ 2 := by
    intro om
    calc Nfun om ^ 4 = (Nfun om ^ 2) ^ 2 := by ring
      _ = Sfun om ^ 2 := by rw [hNsq om]
  have hsumR : ∀ (g : Fin r → Om → ℝ), (∀ l, Measurable (g l)) →
      Measurable (fun om => ∑ l : Fin r, g l om) := by
    intro g hg
    have h : ∀ s : Finset (Fin r), Measurable (fun om => s.sum (fun l => g l om)) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using (measurable_const : Measurable fun _ : Om => (0 : ℝ))
      | insert a s ha ih =>
          have hfun : (fun om => (insert a s).sum (fun l => g l om))
              = (fun om => g a om + s.sum (fun l => g l om)) := by
            funext om
            exact Finset.sum_insert ha
          rw [hfun]
          exact (hg a).add ih
    exact h Finset.univ
  have hSmeas : Measurable Sfun := by
    rw [hSfun]
    exact hsumR (fun l om => (∑ j : Fin p, Q j l * Z om j) ^ 2)
      (fun l => by simpa only [pow_two] using (hxi l).mul (hxi l))
  have hNmeas : Measurable Nfun := by
    rw [hNfun]
    exact Real.continuous_sqrt.measurable.comp hSmeas
  have hrpowNat : ∀ (a : ℝ) (n : ℕ), a ^ ((n : ℝ)) = a ^ n := fun a n => Real.rpow_natCast a n
  have habs4 : ∀ a : ℝ, |a| ^ 4 = a ^ 4 := by
    intro a
    have h1 : |a| ^ 4 = (|a| ^ 2) ^ 2 := by ring
    rw [h1, sq_abs]
    ring
  have hint4 : ∀ l : Fin r, Integrable (fun om => (∑ j : Fin p, Q j l * Z om j) ^ 4) P := by
    intro l
    have h := (hmem l).integrable_norm_rpow (p := 4) (by norm_num) (by norm_num)
    have habs : ∀ x : Om, ‖∑ j : Fin p, Q j l * Z x j‖ ^ (ENNReal.toReal (4 : ℝ≥0∞))
        = (∑ j : Fin p, Q j l * Z x j) ^ 4 := by
      intro x
      have hto : ENNReal.toReal (4 : ℝ≥0∞) = ((4 : ℕ) : ℝ) := by simp
      calc ‖∑ j : Fin p, Q j l * Z x j‖ ^ (ENNReal.toReal (4 : ℝ≥0∞))
          = |∑ j : Fin p, Q j l * Z x j| ^ (ENNReal.toReal (4 : ℝ≥0∞)) := by
            rw [Real.norm_eq_abs]
        _ = |∑ j : Fin p, Q j l * Z x j| ^ ((4 : ℕ) : ℝ) := by rw [hto]
        _ = |∑ j : Fin p, Q j l * Z x j| ^ 4 := hrpowNat _ 4
        _ = (∑ j : Fin p, Q j l * Z x j) ^ 4 := habs4 _
    simpa only [habs] using h
  have hsumint : Integrable (fun om => ∑ l : Fin r, (∑ j : Fin p, Q j l * Z om j) ^ 4) P := by
    have h : ∀ s : Finset (Fin r),
        Integrable (fun om => s.sum (fun l => (∑ j : Fin p, Q j l * Z om j) ^ 4)) P := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using (integrable_const (0 : ℝ) : Integrable (fun _ : Om => (0 : ℝ)) P)
      | insert a s ha ih =>
          have hfun : (fun om => (insert a s).sum (fun l => (∑ j : Fin p, Q j l * Z om j) ^ 4))
              = (fun om => (∑ j : Fin p, Q j a * Z om j) ^ 4
                  + s.sum (fun l => (∑ j : Fin p, Q j l * Z om j) ^ 4)) := by
            funext om
            exact Finset.sum_insert ha
          rw [hfun]
          exact (hint4 a).add ih
    exact h Finset.univ
  have hSsq : ∀ om, Sfun om ^ 2 ≤ (r : ℝ) * ∑ l : Fin r, (∑ j : Fin p, Q j l * Z om j) ^ 4 := by
    intro om
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin r))
      (fun l : Fin r => (∑ j : Fin p, Q j l * Z om j) ^ 2) (fun _ : Fin r => (1 : ℝ))
    simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hcs
    calc Sfun om ^ 2 = (∑ l : Fin r, (∑ j : Fin p, Q j l * Z om j) ^ 2) ^ 2 := by
          simp only [hSfun]
      _ ≤ (∑ l : Fin r, ((∑ j : Fin p, Q j l * Z om j) ^ 2) ^ 2) * (r : ℝ) := hcs
      _ = (r : ℝ) * ∑ l : Fin r, (∑ j : Fin p, Q j l * Z om j) ^ 4 := by
          rw [mul_comm]
          congr 1
          exact Finset.sum_congr rfl fun l _ => by ring
  have hN4pt : ∀ om, Nfun om ^ 4 ≤ (r : ℝ) * ∑ l : Fin r, (∑ j : Fin p, Q j l * Z om j) ^ 4 :=
    fun om => by rw [hNpow om]; exact hSsq om
  have hdom : Integrable (fun om => (r : ℝ) * ∑ l : Fin r, (∑ j : Fin p, Q j l * Z om j) ^ 4) P :=
    hsumint.const_mul (r : ℝ)
  have hN4meas : Measurable (fun om => Nfun om ^ 4) := by
    have h2 : Measurable (fun om => Nfun om * Nfun om) := hNmeas.mul hNmeas
    have h4 : Measurable (fun om => (Nfun om * Nfun om) * (Nfun om * Nfun om)) := h2.mul h2
    have hfun : (fun om => Nfun om ^ 4)
        = (fun om => (Nfun om * Nfun om) * (Nfun om * Nfun om)) := by
      funext om
      ring
    rw [hfun]
    exact h4
  have hN4int : Integrable (fun om => Nfun om ^ 4) P := by
    refine hdom.mono' (Measurable.aestronglyMeasurable hN4meas) ?_
    filter_upwards with om
    have h1 : ‖Nfun om ^ 4‖ = Nfun om ^ 4 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [h1]
    exact hN4pt om
  have hCnn : (0 : ℝ) ≤ 2 * (4 / Real.exp 1) ^ 4 * c0 ^ 4 := by positivity
  have hsumle : ∫ om, ∑ l : Fin r, (∑ j : Fin p, Q j l * Z om j) ^ 4 ∂P
      ≤ (r : ℝ) * (2 * (4 / Real.exp 1) ^ 4 * c0 ^ 4) := by
    rw [integral_finset_sum (s := Finset.univ)
      (f := fun l om => (∑ j : Fin p, Q j l * Z om j) ^ 4) (fun l _ => hint4 l)]
    calc ∑ l : Fin r, ∫ om, (∑ j : Fin p, Q j l * Z om j) ^ 4 ∂P
        ≤ ∑ _l : Fin r, (2 * (4 / Real.exp 1) ^ 4 * c0 ^ 4) :=
          Finset.sum_le_sum fun l _ => hint l
      _ = (r : ℝ) * (2 * (4 / Real.exp 1) ^ 4 * c0 ^ 4) := by simp
  have hN4le : ∫ om, Nfun om ^ 4 ∂P
      ≤ (k : ℝ) ^ 2 * (2 * (4 / Real.exp 1) ^ 4 * c0 ^ 4) := by
    have h1 : ∫ om, Nfun om ^ 4 ∂P
        ≤ ∫ om, (r : ℝ) * ∑ l : Fin r, (∑ j : Fin p, Q j l * Z om j) ^ 4 ∂P :=
      integral_mono hN4int hdom (fun om => hN4pt om)
    have h2 : ∫ om, (r : ℝ) * ∑ l : Fin r, (∑ j : Fin p, Q j l * Z om j) ^ 4 ∂P
        = (r : ℝ) * ∫ om, ∑ l : Fin r, (∑ j : Fin p, Q j l * Z om j) ^ 4 ∂P :=
      integral_const_mul (r : ℝ) _
    have h3 : (r : ℝ) * ∫ om, ∑ l : Fin r, (∑ j : Fin p, Q j l * Z om j) ^ 4 ∂P
        ≤ (r : ℝ) * ((r : ℝ) * (2 * (4 / Real.exp 1) ^ 4 * c0 ^ 4)) :=
      mul_le_mul_of_nonneg_left hsumle (by positivity)
    have h4 : (r : ℝ) * ((r : ℝ) * (2 * (4 / Real.exp 1) ^ 4 * c0 ^ 4))
        ≤ (k : ℝ) ^ 2 * (2 * (4 / Real.exp 1) ^ 4 * c0 ^ 4) := by
      have hk : (r : ℝ) ≤ (k : ℝ) := by exact_mod_cast hrk
      have hrsq : (r : ℝ) * (r : ℝ) ≤ (k : ℝ) * (k : ℝ) :=
        mul_le_mul hk hk (by positivity) (by positivity)
      have h5 := mul_le_mul_of_nonneg_right hrsq hCnn
      nlinarith [h5]
    calc ∫ om, Nfun om ^ 4 ∂P
        ≤ ∫ om, (r : ℝ) * ∑ l : Fin r, (∑ j : Fin p, Q j l * Z om j) ^ 4 ∂P := h1
      _ = (r : ℝ) * ∫ om, ∑ l : Fin r, (∑ j : Fin p, Q j l * Z om j) ^ 4 ∂P := h2
      _ ≤ (r : ℝ) * ((r : ℝ) * (2 * (4 / Real.exp 1) ^ 4 * c0 ^ 4)) := h3
      _ ≤ (k : ℝ) ^ 2 * (2 * (4 / Real.exp 1) ^ 4 * c0 ^ 4) := h4
  have hNnn : ∀ om, 0 ≤ Nfun om := fun om => Real.sqrt_nonneg _
  have hpt4 : ∀ om, ‖Nfun om‖ₑ ^ ((4 : ℕ) : ℝ) = ENNReal.ofReal (Nfun om ^ 4) := by
    intro om
    rw [Real.enorm_eq_ofReal (hNnn om),
      ENNReal.ofReal_rpow_of_nonneg (hNnn om) (by norm_num : (0 : ℝ) ≤ ((4 : ℕ) : ℝ))]
    exact congrArg ENNReal.ofReal (hrpowNat (Nfun om) 4)
  have hA4nn : (0 : ℝ) ≤ ∫ om, Nfun om ^ 4 ∂P := by
    have h0 : ∫ om, (0 : ℝ) ∂P ≤ ∫ om, Nfun om ^ 4 ∂P :=
      integral_mono (integrable_const (0 : ℝ)) hN4int (fun om => by positivity)
    simpa using h0
  have hlin4 : ∫⁻ om, ‖Nfun om‖ₑ ^ ((4 : ℕ) : ℝ) ∂P
      = ENNReal.ofReal (∫ om, Nfun om ^ 4 ∂P) := by
    rw [lintegral_congr hpt4,
      ← ofReal_integral_eq_lintegral_ofReal hN4int
        (Filter.Eventually.of_forall fun om => by positivity)]
  have hmemN : MemLp Nfun 4 P := by
    refine ⟨Measurable.aestronglyMeasurable hNmeas, ?_⟩
    rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num : (4 : ℝ≥0∞) ≠ 0)
      (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)]
    rw [show ENNReal.toReal (4 : ℝ≥0∞) = ((4 : ℕ) : ℝ) by simp]
    rw [hlin4]
    rw [ENNReal.ofReal_rpow_of_nonneg hA4nn (by norm_num : (0 : ℝ) ≤ 1 / ((4 : ℕ) : ℝ))]
    exact ENNReal.ofReal_lt_top
  have h3le4 : eLpNorm Nfun 3 P ≤ eLpNorm Nfun 4 P :=
    eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (3 : ℝ≥0∞) ≤ 4)
      (Measurable.aestronglyMeasurable hNmeas)
  have hmem3 : MemLp Nfun 3 P :=
    ⟨Measurable.aestronglyMeasurable hNmeas, lt_of_le_of_lt h3le4 hmemN.2⟩
  have hN3int : Integrable (fun om => Nfun om ^ 3) P := by
    have h := hmem3.integrable_norm_rpow (p := 3) (by norm_num) (by norm_num)
    have habs : ∀ x : Om, ‖Nfun x‖ ^ (ENNReal.toReal (3 : ℝ≥0∞)) = Nfun x ^ 3 := by
      intro x
      have hto : ENNReal.toReal (3 : ℝ≥0∞) = ((3 : ℕ) : ℝ) := by simp
      calc ‖Nfun x‖ ^ (ENNReal.toReal (3 : ℝ≥0∞))
          = |Nfun x| ^ (ENNReal.toReal (3 : ℝ≥0∞)) := by rw [Real.norm_eq_abs]
        _ = |Nfun x| ^ ((3 : ℕ) : ℝ) := by rw [hto]
        _ = |Nfun x| ^ 3 := hrpowNat _ 3
        _ = Nfun x ^ 3 := by rw [abs_of_nonneg (hNnn x)]
    simpa only [habs] using h
  have hA3 : (0 : ℝ) ≤ ∫ om, Nfun om ^ 3 ∂P := by
    have h0 : ∫ om, (0 : ℝ) ∂P ≤ ∫ om, Nfun om ^ 3 ∂P :=
      integral_mono (integrable_const (0 : ℝ)) hN3int (fun om => by positivity)
    simpa using h0
  have hpt3 : ∀ om, ‖Nfun om‖ₑ ^ ((3 : ℕ) : ℝ) = ENNReal.ofReal (Nfun om ^ 3) := by
    intro om
    rw [Real.enorm_eq_ofReal (hNnn om),
      ENNReal.ofReal_rpow_of_nonneg (hNnn om) (by norm_num : (0 : ℝ) ≤ ((3 : ℕ) : ℝ))]
    exact congrArg ENNReal.ofReal (hrpowNat (Nfun om) 3)
  have hlin3 : ∫⁻ om, ‖Nfun om‖ₑ ^ ((3 : ℕ) : ℝ) ∂P
      = ENNReal.ofReal (∫ om, Nfun om ^ 3 ∂P) := by
    rw [lintegral_congr hpt3,
      ← ofReal_integral_eq_lintegral_ofReal hN3int
        (Filter.Eventually.of_forall fun om => by positivity)]
  have hpow3 : eLpNorm Nfun 3 P
      = ENNReal.ofReal ((∫ om, Nfun om ^ 3 ∂P) ^ (1 / ((3 : ℕ) : ℝ))) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num : (3 : ℝ≥0∞) ≠ 0)
      (by norm_num : (3 : ℝ≥0∞) ≠ ⊤)]
    rw [show ENNReal.toReal (3 : ℝ≥0∞) = ((3 : ℕ) : ℝ) by simp]
    rw [hlin3]
    exact ENNReal.ofReal_rpow_of_nonneg hA3 (by norm_num : (0 : ℝ) ≤ 1 / ((3 : ℕ) : ℝ))
  have hpow4 : eLpNorm Nfun 4 P
      = ENNReal.ofReal ((∫ om, Nfun om ^ 4 ∂P) ^ (1 / ((4 : ℕ) : ℝ))) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num : (4 : ℝ≥0∞) ≠ 0)
      (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)]
    rw [show ENNReal.toReal (4 : ℝ≥0∞) = ((4 : ℕ) : ℝ) by simp]
    rw [hlin4]
    exact ENNReal.ofReal_rpow_of_nonneg hA4nn (by norm_num : (0 : ℝ) ≤ 1 / ((4 : ℕ) : ℝ))
  have hreal : (∫ om, Nfun om ^ 3 ∂P) ^ (1 / ((3 : ℕ) : ℝ))
      ≤ (∫ om, Nfun om ^ 4 ∂P) ^ (1 / ((4 : ℕ) : ℝ)) := by
    have h1 : eLpNorm Nfun 3 P ≤ eLpNorm Nfun 4 P := h3le4
    rw [hpow3, hpow4] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg hA4nn _)).mp h1
  have hcube : ∫ om, Nfun om ^ 3 ∂P ≤ (∫ om, Nfun om ^ 4 ∂P) ^ ((3 : ℝ) / 4) := by
    have h1 : ((∫ om, Nfun om ^ 3 ∂P) ^ (1 / ((3 : ℕ) : ℝ))) ^ (3 : ℝ)
        ≤ ((∫ om, Nfun om ^ 4 ∂P) ^ (1 / ((4 : ℕ) : ℝ))) ^ (3 : ℝ) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hA3 _) hreal (by norm_num : (0 : ℝ) ≤ 3)
    have e1 : ((∫ om, Nfun om ^ 3 ∂P) ^ (1 / ((3 : ℕ) : ℝ))) ^ (3 : ℝ)
        = ∫ om, Nfun om ^ 3 ∂P := by
      rw [← Real.rpow_mul (x := ∫ om, Nfun om ^ 3 ∂P) hA3 (1 / ((3 : ℕ) : ℝ)) 3,
        show (1 : ℝ) / ((3 : ℕ) : ℝ) * 3 = 1 by norm_num, Real.rpow_one]
    have e2 : ((∫ om, Nfun om ^ 4 ∂P) ^ (1 / ((4 : ℕ) : ℝ))) ^ (3 : ℝ)
        = (∫ om, Nfun om ^ 4 ∂P) ^ ((3 : ℝ) / 4) := by
      rw [← Real.rpow_mul (x := ∫ om, Nfun om ^ 4 ∂P) hA4nn (1 / ((4 : ℕ) : ℝ)) 3,
        show (1 : ℝ) / ((4 : ℕ) : ℝ) * 3 = (3 : ℝ) / 4 by norm_num]
    rwa [e1, e2] at h1
  have hC0nn : (0 : ℝ) ≤ 2 ^ ((1 : ℝ) / 4) * (4 / Real.exp 1) * c0 := by positivity
  have h2pow : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 = 2 := by
    have h1 : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ ((4 : ℕ) : ℝ) = 2 := by
      rw [← Real.rpow_mul (x := (2 : ℝ)) (by norm_num) ((1 : ℝ) / 4) ((4 : ℕ) : ℝ),
        show (1 : ℝ) / 4 * ((4 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
    simpa only [hrpowNat] using h1
  have hC0pow : (2 ^ ((1 : ℝ) / 4) * (4 / Real.exp 1) * c0) ^ 4
      = 2 * (4 / Real.exp 1) ^ 4 * c0 ^ 4 := by
    rw [mul_pow, mul_pow, h2pow]
  have hkey : ((k : ℝ) ^ 2 * (2 * (4 / Real.exp 1) ^ 4 * c0 ^ 4)) ^ ((3 : ℝ) / 4)
      = (2 ^ ((1 : ℝ) / 4) * (4 / Real.exp 1) * c0) ^ 3 * (k : ℝ) ^ ((3 : ℝ) / 2) := by
    set C0 : ℝ := 2 ^ ((1 : ℝ) / 4) * (4 / Real.exp 1) * c0 with hC0def
    have hC0p : C0 ^ 4 = 2 * (4 / Real.exp 1) ^ 4 * c0 ^ 4 := hC0pow
    have hC0n : (0 : ℝ) ≤ C0 := hC0nn
    have hk : (0 : ℝ) ≤ (k : ℝ) := by positivity
    have hsq : (k : ℝ) ^ 2 * (2 * (4 / Real.exp 1) ^ 4 * c0 ^ 4) = ((k : ℝ) * C0 ^ 2) ^ 2 := by
      rw [← hC0p]
      ring
    rw [hsq, ← hrpowNat ((k : ℝ) * C0 ^ 2) 2,
      ← Real.rpow_mul (x := (k : ℝ) * C0 ^ 2) (mul_nonneg hk (sq_nonneg C0)) ((2 : ℕ) : ℝ)
        ((3 : ℝ) / 4),
      show ((2 : ℕ) : ℝ) * ((3 : ℝ) / 4) = (3 : ℝ) / 2 by norm_num,
      Real.mul_rpow hk (sq_nonneg C0),
      ← hrpowNat C0 2,
      ← Real.rpow_mul (x := C0) hC0n ((2 : ℕ) : ℝ) ((3 : ℝ) / 2),
      show ((2 : ℕ) : ℝ) * ((3 : ℝ) / 2) = ((3 : ℕ) : ℝ) by norm_num,
      hrpowNat C0 3]
    ring
  have h4le : (∫ om, Nfun om ^ 4 ∂P) ^ ((3 : ℝ) / 4)
      ≤ ((k : ℝ) ^ 2 * (2 * (4 / Real.exp 1) ^ 4 * c0 ^ 4)) ^ ((3 : ℝ) / 4) :=
    Real.rpow_le_rpow hA4nn hN4le (by norm_num : (0 : ℝ) ≤ (3 : ℝ) / 4)
  refine ⟨?_, ?_⟩
  · exact hmemN
  · show ∫ om, Nfun om ^ 3 ∂P
      ≤ (2 ^ ((1 : ℝ) / 4) * (4 / Real.exp 1) * c0) ^ 3 * (k : ℝ) ^ ((3 : ℝ) / 2)
    calc ∫ om, Nfun om ^ 3 ∂P
        ≤ (∫ om, Nfun om ^ 4 ∂P) ^ ((3 : ℝ) / 4) := hcube
      _ ≤ ((k : ℝ) ^ 2 * (2 * (4 / Real.exp 1) ^ 4 * c0 ^ 4)) ^ ((3 : ℝ) / 4) := h4le
      _ = (2 ^ ((1 : ℝ) / 4) * (4 / Real.exp 1) * c0) ^ 3 * (k : ℝ) ^ ((3 : ℝ) / 2) := hkey

  /- @proof-region region.target-node.session.bd92de47a09cc413 end -/

end
end Statlib.Imported

