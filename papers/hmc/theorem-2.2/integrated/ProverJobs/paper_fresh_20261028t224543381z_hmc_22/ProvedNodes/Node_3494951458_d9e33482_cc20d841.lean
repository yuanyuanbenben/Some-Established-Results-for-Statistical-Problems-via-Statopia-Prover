import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.Vocabulary
import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.Base
import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.ProvedNodes.Node_2434035012_bf892b59_840b5159

namespace PaperProofTasks.paper_fresh_20261028t224543381z_hmc_22

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open _root_.PaperProofTasks.paper_fresh_20261028t224543381z_hmc_22.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace Statlib.Imported
open _root_.Statlib

set_option autoImplicit false in
theorem statopia_math_node_3494951458_d9e33482 : ∀ (d : ℕ) (hd : 0 < d) (U : HMCState d → ℝ) (hU : Differentiable ℝ U)
    (ε : ℝ) (hε : 0 < ε) (L : ℕ) (hL : 1 ≤ L)
    (β : ℝ) (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hgrad : ∀ N : ℝ, ∃ S : ℝ, ∀ z : HMCState d, S ≤ ‖z‖ → N * ‖z‖ ≤ ‖gradient U z‖),
    ∃ η : ℝ, ∀ x0 p0 : HMCState d, η ≤ ‖x0‖ → ‖p0‖ ≤ ‖x0‖ ^ β →
      (∀ i : ℕ, 1 ≤ i → i ≤ L →
        ‖(leapfrogFlow U ε i (x0, p0)).1‖ ≥
          2 * ‖(leapfrogFlow U ε (i - 1) (x0, p0)).1‖) ∧
      ‖(leapfrogFlow U ε L (x0, p0)).1‖ ≥ (2 : ℝ) ^ L * ‖x0‖ ∧
      (∀ i : ℕ, i ≤ L → ‖(leapfrogFlow U ε i (x0, p0)).1‖ ≥ ‖x0‖) := by
  /- @proof-region region.target-node.session.6d9b4c041952c1d0 begin -/
  intro d hd U hU ε hε L hL β hβ_pos hβ_lt_one hgrad
  have hε2pos : (0 : ℝ) < ε ^ 2 := by positivity
  have hε2ne : ε ^ 2 ≠ 0 := ne_of_gt hε2pos
  obtain ⟨S, hS⟩ := hgrad (9 / ε ^ 2)
  have hkeyN : ε ^ 2 * (9 / ε ^ 2) = 9 := by field_simp
  have hNhalf : ε ^ 2 / 2 * (9 / ε ^ 2) = 9 / 2 := by field_simp
  have hgrad9 : ∀ z : HMCState d, S ≤ ‖z‖ → 9 * ‖z‖ ≤ ε ^ 2 * ‖gradient U z‖ := by
    intro z hz
    have h1 : ε ^ 2 * ((9 / ε ^ 2) * ‖z‖) ≤ ε ^ 2 * ‖gradient U z‖ :=
      mul_le_mul_of_nonneg_left (hS z hz) hε2pos.le
    have h2 : ε ^ 2 * ((9 / ε ^ 2) * ‖z‖) = 9 * ‖z‖ := by rw [← mul_assoc, hkeyN]
    linarith [h1, h2]
  have hβm1 : β - 1 < 0 := by linarith
  have hc : (0 : ℝ) < 1 - β := by linarith
  have hεpow : 0 < ε ^ (1 / (1 - β)) := Real.rpow_pos_of_pos hε _
  set T : ℝ := ε ^ (1 / (1 - β)) + 1 with hTdef
  have hTpos : 0 < T := by rw [hTdef]; linarith
  have hεT : ε ≤ T ^ (1 - β) := by
    have hle : ε ^ (1 / (1 - β)) ≤ T := by rw [hTdef]; linarith
    have hmono : (ε ^ (1 / (1 - β))) ^ (1 - β) ≤ T ^ (1 - β) :=
      Real.rpow_le_rpow hεpow.le hle hc.le
    have hX : 1 / (1 - β) * (1 - β) = 1 := by
      rw [one_div, inv_mul_cancel₀ (ne_of_gt hc)]
    have heq : (ε ^ (1 / (1 - β))) ^ (1 - β) = ε := by
      rw [← Real.rpow_mul hε.le, hX, Real.rpow_one]
    linarith [hmono, heq]
  have hprod : T ^ (1 - β) * T ^ (β - 1) = 1 := by
    rw [← Real.rpow_add hTpos]
    rw [show 1 - β + (β - 1) = 0 by ring, Real.rpow_zero]
  have hTβ : ε * T ^ (β - 1) ≤ 1 := by
    calc ε * T ^ (β - 1) ≤ T ^ (1 - β) * T ^ (β - 1) :=
          mul_le_mul_of_nonneg_right hεT (Real.rpow_nonneg hTpos.le _)
      _ = 1 := hprod
  set η : ℝ := max (max S 1) T with hηdef
  have hηS : S ≤ η := by
    rw [hηdef]; exact le_trans (le_max_left S 1) (le_max_left (max S 1) T)
  have hη1 : 1 ≤ η := by
    rw [hηdef]; exact le_trans (le_max_right S 1) (le_max_left (max S 1) T)
  have hηT : T ≤ η := by rw [hηdef]; exact le_max_right (max S 1) T
  have hηpos : 0 < η := lt_of_lt_of_le one_pos hη1
  have hηβ : ε * η ^ (β - 1) ≤ 1 := by
    have hTm : η ^ (β - 1) ≤ T ^ (β - 1) :=
      Real.rpow_le_rpow_of_nonpos hTpos hηT hβm1.le
    have h4 : ε * η ^ (β - 1) ≤ ε * T ^ (β - 1) := mul_le_mul_of_nonneg_left hTm hε.le
    linarith [h4, hTβ]
  refine ⟨η, ?_⟩
  intro x0 p0 hx0 hp0
  let x : ℕ → HMCState d := fun i => (leapfrogFlow U ε i (x0, p0)).1
  obtain ⟨hstep1, hstepi, -, -, h0⟩ := statopia_math_node_2434035012_bf892b59 d U hU ε x0 p0
  have hstep1' : x 1 = x0 - (ε ^ 2 / 2) • gradient U x0 + ε • p0 := hstep1
  have hstepi' : ∀ i : ℕ, 1 ≤ i → x (i + 1) = 2 • x i - x (i - 1) - ε ^ 2 • gradient U (x i) :=
    fun i hi => hstepi i hi
  have hzero : x 0 = x0 := congrArg Prod.fst h0
  have hx0pos : 0 < ‖x0‖ := lt_of_lt_of_le hηpos hx0
  have hpβ : ‖p0‖ ≤ ‖x0‖ * η ^ (β - 1) := by
    have h1 : ‖x0‖ ^ β = ‖x0‖ ^ (1 : ℝ) * ‖x0‖ ^ (β - 1) := by
      rw [← Real.rpow_add hx0pos, show (1 : ℝ) + (β - 1) = β by ring]
    have h2 : ‖x0‖ ^ (β - 1) ≤ η ^ (β - 1) :=
      Real.rpow_le_rpow_of_nonpos hηpos hx0 hβm1.le
    calc ‖p0‖ ≤ ‖x0‖ ^ β := hp0
      _ = ‖x0‖ ^ (1 : ℝ) * ‖x0‖ ^ (β - 1) := h1
      _ = ‖x0‖ * ‖x0‖ ^ (β - 1) := by rw [Real.rpow_one]
      _ ≤ ‖x0‖ * η ^ (β - 1) := mul_le_mul_of_nonneg_left h2 hx0pos.le
  have hmom : ε * ‖p0‖ ≤ ‖x0‖ := by
    have h3 : ε * ‖p0‖ ≤ ε * (‖x0‖ * η ^ (β - 1)) := mul_le_mul_of_nonneg_left hpβ hε.le
    have h4 : ε * (‖x0‖ * η ^ (β - 1)) = (ε * η ^ (β - 1)) * ‖x0‖ := by ring
    have h5 : (ε * η ^ (β - 1)) * ‖x0‖ ≤ 1 * ‖x0‖ :=
      mul_le_mul_of_nonneg_right hηβ (norm_nonneg x0)
    linarith [h3, h4, h5]
  have hpow1 : ∀ i : ℕ, (1 : ℝ) ≤ 2 ^ i := by
    intro i
    induction i with
    | zero => norm_num
    | succ k ih =>
        have hp : (0 : ℝ) < 2 ^ k := pow_pos (by norm_num) k
        rw [pow_succ]
        nlinarith
  have hbasis : 2 ^ 0 * ‖x0‖ ≤ ‖x 0‖ := by
    rw [hzero]
    simp
  have hstepA : 2 * ‖x0‖ ≤ ‖x 1‖ := by
    have hA : ‖(ε ^ 2 / 2) • gradient U x0‖ = (ε ^ 2 / 2) * ‖gradient U x0‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε ^ 2 / 2)]
    have hB : ‖x0 + ε • p0‖ ≤ ‖x0‖ + ε * ‖p0‖ := by
      have hb1 : ‖x0 + ε • p0‖ ≤ ‖x0‖ + ‖ε • p0‖ := norm_add_le (x0) (ε • p0)
      have hb2 : ‖ε • p0‖ = ε * ‖p0‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hε.le]
      linarith [hb1, hb2]
    have hAeq : (ε ^ 2 / 2) • gradient U x0 = (x0 + ε • p0) - x 1 := by
      rw [hstep1']
      abel
    have h5 : ‖(ε ^ 2 / 2) • gradient U x0‖ ≤ ‖x 1‖ + ‖x0 + ε • p0‖ := by
      calc ‖(ε ^ 2 / 2) • gradient U x0‖ = ‖(x0 + ε • p0) - x 1‖ := by rw [hAeq]
        _ ≤ ‖x0 + ε • p0‖ + ‖x 1‖ := norm_sub_le (x0 + ε • p0) (x 1)
        _ = ‖x 1‖ + ‖x0 + ε • p0‖ := by rw [add_comm]
    have hg9A : (9 / 2) * ‖x0‖ ≤ (ε ^ 2 / 2) * ‖gradient U x0‖ := by
      have h1 : 9 * ‖x0‖ ≤ ε ^ 2 * ‖gradient U x0‖ := hgrad9 x0 (le_trans hηS hx0)
      have h2 : (ε ^ 2 * ‖gradient U x0‖) / 2 = (ε ^ 2 / 2) * ‖gradient U x0‖ := by ring
      linarith [h1, h2]
    linarith [h5, hA, hB, hg9A, hmom]
  have hstepB : ∀ j : ℕ, 1 ≤ j → S ≤ ‖x j‖ → 2 * ‖x (j - 1)‖ ≤ ‖x j‖ →
      2 * ‖x j‖ ≤ ‖x (j + 1)‖ := by
    intro j hj1 hjS hjprev
    have hb : x (j + 1) = 2 • x j - x (j - 1) - ε ^ 2 • gradient U (x j) := hstepi' j hj1
    have hA : ‖ε ^ 2 • gradient U (x j)‖ = ε ^ 2 * ‖gradient U (x j)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hε2pos.le]
    have hAeq : ε ^ 2 • gradient U (x j) = 2 • x j - x (j - 1) - x (j + 1) := by
      rw [hb]
      abel
    have hN : ‖2 • x j‖ ≤ 2 * ‖x j‖ := by
      have hadd : 2 • x j = x j + x j := two_nsmul (x j)
      rw [hadd]
      have h2 := norm_add_le (x j) (x j)
      linarith [h2]
    have h5 : ‖ε ^ 2 • gradient U (x j)‖ ≤ ‖2 • x j‖ + ‖x (j - 1)‖ + ‖x (j + 1)‖ := by
      calc ‖ε ^ 2 • gradient U (x j)‖ = ‖2 • x j - x (j - 1) - x (j + 1)‖ := by rw [hAeq]
        _ ≤ ‖2 • x j - x (j - 1)‖ + ‖x (j + 1)‖ :=
              norm_sub_le (2 • x j - x (j - 1)) (x (j + 1))
        _ ≤ ‖2 • x j‖ + ‖x (j - 1)‖ + ‖x (j + 1)‖ := by
              have h2 := norm_sub_le (2 • x j) (x (j - 1))
              linarith [h2]
    have hA9 : 9 * ‖x j‖ ≤ ε ^ 2 * ‖gradient U (x j)‖ := hgrad9 (x j) hjS
    have hC : ‖x (j - 1)‖ ≤ (1 / 2) * ‖x j‖ := by linarith [hjprev]
    linarith [h5, hA, hN, hA9, hC, norm_nonneg (x j)]
  have key : ∀ i : ℕ, i ≤ L →
      (2 ^ i * ‖x0‖ ≤ ‖x i‖ ∧ (1 ≤ i → 2 * ‖x (i - 1)‖ ≤ ‖x i‖)) := by
    intro i
    induction i with
    | zero =>
        intro _
        exact ⟨hbasis, fun h => absurd h (by norm_num)⟩
    | succ n ih =>
        intro hnL
        have hnL' : n ≤ L := Nat.le_of_succ_le hnL
        obtain ⟨ih1, ih2⟩ := ih hnL'
        rcases Nat.eq_zero_or_pos n with h0n | hpos
        · subst h0n
          refine ⟨?_, ?_⟩
          · simpa using hstepA
          · intro _
            simpa [hzero] using hstepA
        · have hjS : S ≤ ‖x n‖ := by
            have h2n : (1 : ℝ) ≤ 2 ^ n := hpow1 n
            have h3 : ‖x0‖ ≤ 2 ^ n * ‖x0‖ := by
              have h4 := mul_le_mul_of_nonneg_right h2n (norm_nonneg x0)
              simpa using h4
            linarith [ih1, h3, hηS, hx0]
          have hdouble : 2 * ‖x n‖ ≤ ‖x (n + 1)‖ := hstepB n hpos hjS (ih2 hpos)
          refine ⟨?_, ?_⟩
          · have h2 : 2 ^ (n + 1) * ‖x0‖ = 2 * (2 ^ n * ‖x0‖) := by rw [pow_succ]; ring
            have h3 : 2 * (2 ^ n * ‖x0‖) ≤ 2 * ‖x n‖ :=
              mul_le_mul_of_nonneg_left ih1 (by norm_num)
            linarith [h2, h3, hdouble]
          · intro _
            simpa using hdouble
  refine ⟨?_, ?_, ?_⟩
  · intro i hi1 hiL
    exact (key i hiL).2 hi1
  · exact (key L le_rfl).1
  · intro i hiL
    have h1 : 2 ^ i * ‖x0‖ ≤ ‖x i‖ := (key i hiL).1
    have h2 : (1 : ℝ) ≤ 2 ^ i := hpow1 i
    have h3 : ‖x0‖ ≤ 2 ^ i * ‖x0‖ := by
      have h4 := mul_le_mul_of_nonneg_right h2 (norm_nonneg x0)
      simpa using h4
    exact le_trans h3 h1
  /- @proof-region region.target-node.session.6d9b4c041952c1d0 end -/

end Statlib.Imported

end

