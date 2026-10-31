import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.Vocabulary
import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.Base
import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.ProvedNodes.Node_2434035012_bf892b59_840b5159
import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.ProvedNodes.Node_3494951458_d9e33482_cc20d841

namespace PaperProofTasks.paper_fresh_20261028t224543381z_hmc_22


open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open _root_.PaperProofTasks.paper_fresh_20261028t224543381z_hmc_22.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace Statlib.Imported


set_option autoImplicit false in
theorem statopia_math_node_1277695823_4133e1d3 : ∀ (d : ℕ) (hd : 0 < d) (U : HMCState d → ℝ) (hU : Differentiable ℝ U)
    (ε : ℝ) (hε : 0 < ε) (L : ℕ) (hL : 1 ≤ L)
    (β : ℝ) (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hgrad : ∀ N : ℝ, ∃ S : ℝ, ∀ z : HMCState d, S ≤ ‖z‖ → N * ‖z‖ ≤ ‖gradient U z‖)
    (hosc : ∃ C : ℝ, ∀ x y : HMCState d, ‖y‖ ≥ 2 * ‖x‖ → C ≤ 2 * ‖x‖ →
      ‖gradient U y‖ ≥ 3 * ‖gradient U x‖)
    (hjoint : ∀ R : ℝ, ∃ K : ℝ, ∀ x y : HMCState d, K ≤ ‖x‖ →
      (2 : ℝ) ^ L * ‖x‖ ≤ ‖y‖ → U x - U y - (1 / 2) * ‖x‖ ^ 2 ≤ -R)
    (δ : ℝ) (hδ : 0 < δ),
    ∃ S : ℝ, ∀ x0 p0 : HMCState d, S ≤ ‖x0‖ → ‖p0‖ ≤ ‖x0‖ ^ β →
      acceptProb U ε L (x0, p0) ≤ δ := by
  /- @proof-region region.target-node.session.2001b82a6144931e begin -/
  intro d hd U hU ε hε L hL β hβ_pos hβ_lt_one hgrad hosc hjoint δ hδ
  by_cases hδ1 : 1 ≤ δ
  · refine ⟨0, fun x0 p0 _ _ => ?_⟩
    exact le_trans (min_le_left 1 _) hδ1
  · obtain ⟨C, hC⟩ := hosc
    obtain ⟨η, hη⟩ :=
      statopia_math_node_3494951458_d9e33482 d hd U hU ε hε L hL β hβ_pos hβ_lt_one hgrad
    set r : ℝ := 1 / 3 with hr
    have hrpos : 0 < r := by rw [hr]; norm_num
    have hrlt1 : r < 1 := by rw [hr]; norm_num
    set cL : ℝ := (ε / 2) * (r ^ (L - 1) - r ^ L) with hcL
    have hcLpos : 0 < cL := by
      have hpos : (0 : ℝ) < r ^ (L - 1) := pow_pos hrpos _
      have hpow : r ^ L = r ^ (L - 1) * r := by rw [← pow_succ]; congr 1; omega
      have hd : 0 < r ^ (L - 1) - r ^ L := by rw [hpow]; nlinarith [hpos, hrlt1]
      rw [hcL]; nlinarith [hε, hd]
    set N : ℝ := 4 / (cL * 2 ^ L) with hN
    obtain ⟨SN, hSN⟩ := hgrad N
    set R : ℝ := -Real.log δ with hR
    obtain ⟨K, hK⟩ := hjoint R
    set S0 : ℝ := max (max (max η SN) K) (max (C / 2) 1) with hS
    refine ⟨S0, ?_⟩
    intro x0 p0 hx0 hp0
    have hηS : η ≤ S0 := by
      rw [hS]; exact le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
    have hSNS : SN ≤ S0 := by
      rw [hS]; exact le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
    have hKS : K ≤ S0 := by
      rw [hS]; exact le_trans (le_max_right _ _) (le_max_left _ _)
    have hC2S : C / 2 ≤ S0 := by
      rw [hS]; exact le_trans (le_max_left _ _) (le_max_right _ _)
    have h1S : 1 ≤ S0 := by
      rw [hS]; exact le_trans (le_max_right _ _) (le_max_right _ _)
    have hx0_η : η ≤ ‖x0‖ := le_trans hηS hx0
    have hx0_K : K ≤ ‖x0‖ := le_trans hKS hx0
    have hx0_C2 : C / 2 ≤ ‖x0‖ := le_trans hC2S hx0
    obtain ⟨hdoub, hxLbig, hxbig⟩ := hη x0 p0 hx0_η hp0
    obtain ⟨est1, estb, estc, estd, est0⟩ :=
      statopia_math_node_2434035012_bf892b59 d U hU ε x0 p0
    let x : ℕ → HMCState d := fun i => (leapfrogFlow U ε i (x0, p0)).1
    let p : ℕ → HMCState d := fun i => (leapfrogFlow U ε i (x0, p0)).2
    have hxLbig' : (2 : ℝ) ^ L * ‖x0‖ ≤ ‖x L‖ := hxLbig
    have hK' : U x0 - U (x L) - (1 / 2) * ‖x0‖ ^ 2 ≤ -R := hK x0 (x L) hx0_K hxLbig'
    have hexpR : Real.exp (-R) = δ := by
      rw [hR]; rw [neg_neg, Real.exp_log hδ]
    have hmain : (1 / 2) * ‖p0‖ ^ 2 - (1 / 2) * ‖p L‖ ^ 2 ≤ -‖x0‖ ^ 2 := by
      set g : ℝ := cL * ‖gradient U (x L)‖ with hg
      set a : ℝ := ‖p0‖ with ha
      set b : ℝ := ‖p L‖ with hb
      set c : ℝ := ‖x0‖ with hc0
      have hmom : g - a ≤ b := by
        have hstep : ∀ i, i < L → ‖gradient U (x i)‖ ≤ r * ‖gradient U (x (i + 1))‖ := by
          intro i hiL
          have h2 : ‖x (i + 1)‖ ≥ 2 * ‖x i‖ := by
            have h := hdoub (i + 1) (by omega) (by omega)
            simpa using h
          have hCi : C ≤ 2 * ‖x i‖ := by
            have hb := hxbig i (by omega)
            linarith only [hx0_C2, hb]
          have h3 := hC (x i) (x (i + 1)) h2 hCi
          rw [hr]; linarith only [h3]
        have hdecay : ∀ i, i ≤ L → ‖gradient U (x i)‖ ≤ r ^ (L - i) * ‖gradient U (x L)‖ := by
          intro i hiL
          have key : ∀ k j, j + k = L → ‖gradient U (x j)‖ ≤ r ^ k * ‖gradient U (x L)‖ := by
            intro k
            induction k with
            | zero =>
              intro j hj; rw [Nat.add_zero] at hj; rw [hj]; simp
            | succ k ih =>
              intro j hj
              have hjL : j < L := by omega
              have hjk : j + 1 + k = L := by omega
              calc ‖gradient U (x j)‖ ≤ r * ‖gradient U (x (j + 1))‖ := hstep j hjL
                _ ≤ r * (r ^ k * ‖gradient U (x L)‖) :=
                      mul_le_mul_of_nonneg_left (ih (j + 1) hjk) (le_of_lt hrpos)
                _ = r ^ (k + 1) * ‖gradient U (x L)‖ := by rw [pow_succ]; ring
          exact key (L - i) i (by omega)
        have hdec0 : ‖gradient U x0‖ ≤ r ^ L * ‖gradient U (x L)‖ := by
          have h := hdecay 0 (Nat.zero_le L)
          have hx0eq : x 0 = x0 := by
            rw [show x 0 = (leapfrogFlow U ε 0 (x0, p0)).1 from rfl, est0]
          rwa [hx0eq, Nat.sub_zero] at h
        have hsumbd : ‖∑ i ∈ Finset.Icc 1 (L - 1), gradient U (x i)‖
            ≤ (∑ i ∈ Finset.Icc 1 (L - 1), r ^ (L - i)) * ‖gradient U (x L)‖ := by
          have h1 := norm_sum_le (s := Finset.Icc 1 (L - 1)) (f := fun i => gradient U (x i))
          have h2 : ∑ i ∈ Finset.Icc 1 (L - 1), ‖gradient U (x i)‖
              ≤ ∑ i ∈ Finset.Icc 1 (L - 1), r ^ (L - i) * ‖gradient U (x L)‖ := by
            apply Finset.sum_le_sum
            intro i hi
            exact hdecay i (by have := (Finset.mem_Icc.mp hi).2; omega)
          have h3 : ∑ i ∈ Finset.Icc 1 (L - 1), r ^ (L - i) * ‖gradient U (x L)‖
              = (∑ i ∈ Finset.Icc 1 (L - 1), r ^ (L - i)) * ‖gradient U (x L)‖ := by
            rw [Finset.sum_mul]
          linarith only [h1, h2, h3]
        have hgeo_k : ∀ k, (∑ i ∈ Finset.Icc 1 k, r ^ ((k + 1) - i)) ≤ (1 / 2) * (1 - r ^ k) := by
          intro k
          induction k with
          | zero => simp
          | succ n ih =>
            have hnot : (n + 1) ∉ Finset.Icc 1 n := by simp only [Finset.mem_Icc]; omega
            have hset : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
              ext z; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
            rw [hset, Finset.sum_insert hnot]
            have hlast : r ^ ((n + 1) + 1 - (n + 1)) = r := by
              rw [show (n + 1) + 1 - (n + 1) = 1 by omega, pow_one]
            have hshift : ∑ i ∈ Finset.Icc 1 n, r ^ ((n + 1) + 1 - i)
                = ∑ i ∈ Finset.Icc 1 n, r * r ^ ((n + 1) - i) := by
              apply Finset.sum_congr rfl
              intro i hi
              have hi' : i ≤ n := (Finset.mem_Icc.mp hi).2
              rw [show (n + 1) + 1 - i = ((n + 1) - i) + 1 by omega, pow_succ']
            rw [hshift, ← Finset.mul_sum, hlast]
            have hstep2 : r * (∑ i ∈ Finset.Icc 1 n, r ^ ((n + 1) - i)) ≤ r * ((1 / 2) * (1 - r ^ n)) :=
              mul_le_mul_of_nonneg_left ih (le_of_lt hrpos)
            have hfin : r + r * ((1 / 2) * (1 - r ^ n)) = (1 / 2) * (1 - r ^ (n + 1)) := by
              rw [pow_succ]; rw [hr]; ring
            linarith only [hstep2, hfin]
        have hgeo : (∑ i ∈ Finset.Icc 1 (L - 1), r ^ (L - i)) ≤ (1 / 2) * (1 - r ^ (L - 1)) := by
          have hk := hgeo_k (L - 1)
          rw [Nat.sub_add_cancel hL] at hk
          exact hk
        have hcoef : cL = ε / 2 - (ε / 2) * r ^ L - ε * ((1 / 2) * (1 - r ^ (L - 1))) := by
          rw [hcL]; ring
        have hpc : p L = p0 - (ε / 2) • gradient U x0 - ε • (∑ i ∈ Finset.Icc 1 (L - 1), gradient U (x i)) - (ε / 2) • gradient U (x L) := estc L hL
        have hnorm : (ε / 2) * ‖gradient U (x L)‖
            ≤ ‖p0‖ + (ε / 2) * ‖gradient U x0‖ + ε * ‖∑ i ∈ Finset.Icc 1 (L - 1), gradient U (x i)‖ + ‖p L‖ := by
          have e : (ε / 2) • gradient U (x L)
              = p0 - (ε / 2) • gradient U x0 - ε • (∑ i ∈ Finset.Icc 1 (L - 1), gradient U (x i)) - p L := by
            rw [hpc]; abel
          have hs1 : ‖(ε / 2) • gradient U (x L)‖ = (ε / 2) * ‖gradient U (x L)‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
          have hs2 : ‖(ε / 2) • gradient U x0‖ = (ε / 2) * ‖gradient U x0‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
          have hs3 : ‖ε • (∑ i ∈ Finset.Icc 1 (L - 1), gradient U (x i))‖
              = ε * ‖∑ i ∈ Finset.Icc 1 (L - 1), gradient U (x i)‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
          calc (ε / 2) * ‖gradient U (x L)‖
              = ‖(ε / 2) • gradient U (x L)‖ := hs1.symm
            _ = ‖p0 - (ε / 2) • gradient U x0 - ε • (∑ i ∈ Finset.Icc 1 (L - 1), gradient U (x i)) - p L‖ := by rw [e]
            _ ≤ ‖p0 - (ε / 2) • gradient U x0 - ε • (∑ i ∈ Finset.Icc 1 (L - 1), gradient U (x i))‖ + ‖p L‖ := norm_sub_le _ _
            _ ≤ (‖p0 - (ε / 2) • gradient U x0‖ + ‖ε • (∑ i ∈ Finset.Icc 1 (L - 1), gradient U (x i))‖) + ‖p L‖ := by
                  apply add_le_add_left; exact norm_sub_le _ _
            _ ≤ ((‖p0‖ + ‖(ε / 2) • gradient U x0‖) + ‖ε • (∑ i ∈ Finset.Icc 1 (L - 1), gradient U (x i))‖) + ‖p L‖ := by
                  apply add_le_add_left; apply add_le_add_left; exact norm_sub_le _ _
            _ = ‖p0‖ + (ε / 2) * ‖gradient U x0‖ + ε * ‖∑ i ∈ Finset.Icc 1 (L - 1), gradient U (x i)‖ + ‖p L‖ := by
                  rw [hs2, hs3]
        have hlow : cL * ‖gradient U (x L)‖ - ‖p0‖ ≤ ‖p L‖ := by
          have hεw : (0 : ℝ) ≤ ε * ‖gradient U (x L)‖ := mul_nonneg hε.le (norm_nonneg _)
          have h3 : (ε / 2) * ‖gradient U x0‖ ≤ (ε / 2) * (r ^ L * ‖gradient U (x L)‖) :=
            mul_le_mul_of_nonneg_left hdec0 (by positivity)
          have h2a : ε * ‖∑ i ∈ Finset.Icc 1 (L - 1), gradient U (x i)‖
              ≤ ε * ((∑ i ∈ Finset.Icc 1 (L - 1), r ^ (L - i)) * ‖gradient U (x L)‖) :=
            mul_le_mul_of_nonneg_left hsumbd hε.le
          have h2b : (∑ i ∈ Finset.Icc 1 (L - 1), r ^ (L - i)) * (ε * ‖gradient U (x L)‖)
              ≤ ((1 / 2) * (1 - r ^ (L - 1))) * (ε * ‖gradient U (x L)‖) :=
            mul_le_mul_of_nonneg_right hgeo hεw
          have h2 : ε * ‖∑ i ∈ Finset.Icc 1 (L - 1), gradient U (x i)‖
              ≤ ε * ((1 / 2) * (1 - r ^ (L - 1))) * ‖gradient U (x L)‖ := by
            calc ε * ‖∑ i ∈ Finset.Icc 1 (L - 1), gradient U (x i)‖
                ≤ ε * ((∑ i ∈ Finset.Icc 1 (L - 1), r ^ (L - i)) * ‖gradient U (x L)‖) := h2a
              _ = (∑ i ∈ Finset.Icc 1 (L - 1), r ^ (L - i)) * (ε * ‖gradient U (x L)‖) := by ring
              _ ≤ ((1 / 2) * (1 - r ^ (L - 1))) * (ε * ‖gradient U (x L)‖) := h2b
              _ = ε * ((1 / 2) * (1 - r ^ (L - 1))) * ‖gradient U (x L)‖ := by ring
          rw [hcoef]
          nlinarith only [hnorm, h3, h2]
        rw [hg, ha, hb]; exact hlow
      have hNpos : 0 < N := by rw [hN]; positivity
      have hxL_SN : SN ≤ ‖x L‖ := by
        have h1 := hxbig L (le_refl L)
        linarith only [hSNS, hx0, h1]
      have hgradL : N * ‖x L‖ ≤ ‖gradient U (x L)‖ := hSN (x L) hxL_SN
      have hNstep : N * (2 ^ L * ‖x0‖) ≤ ‖gradient U (x L)‖ := by
        apply le_trans (mul_le_mul_of_nonneg_left hxLbig' (le_of_lt hNpos)) hgradL
      have hkey : cL * N * 2 ^ L = 4 := by
        rw [hN]
        have hc : cL ≠ 0 := hcLpos.ne'
        have h2 : (2 : ℝ) ^ L ≠ 0 := pow_ne_zero _ (by norm_num)
        field_simp
      have hgbig : 4 * c ≤ g := by
        have h1 : cL * (N * (2 ^ L * ‖x0‖)) ≤ cL * ‖gradient U (x L)‖ :=
          mul_le_mul_of_nonneg_left hNstep (le_of_lt hcLpos)
        have h2 : cL * (N * (2 ^ L * ‖x0‖)) = 4 * ‖x0‖ := by rw [← hkey]; ring
        rw [hc0, hg]; linarith only [h1, h2]
      have hp0_le : a ≤ c := by
        rw [ha, hc0]
        have hx01 : (1 : ℝ) ≤ ‖x0‖ := le_trans h1S hx0
        have hrpow : ‖x0‖ ^ β ≤ ‖x0‖ ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx01 (le_of_lt hβ_lt_one)
        calc ‖p0‖ ≤ ‖x0‖ ^ β := hp0
          _ ≤ ‖x0‖ ^ (1 : ℝ) := hrpow
          _ = ‖x0‖ := Real.rpow_one ‖x0‖
      have hcpos : 0 ≤ c := by rw [hc0]; exact norm_nonneg x0
      have hapos : 0 ≤ a := by rw [ha]; exact norm_nonneg p0
      have hbpos : 0 ≤ b := by rw [hb]; exact norm_nonneg (p L)
      have hgpos : 0 ≤ g := by linarith only [hgbig, hcpos]
      have hgsq : (g - a) ^ 2 ≤ b ^ 2 := by
        have h1 : 0 ≤ g - a := by linarith only [hp0_le, hgbig, hcpos]
        calc (g - a) ^ 2 = (g - a) * (g - a) := by ring
          _ ≤ (g - a) * b := mul_le_mul_of_nonneg_left hmom h1
          _ ≤ b * b := mul_le_mul_of_nonneg_right hmom hbpos
          _ = b ^ 2 := by ring
      have hp0_g4 : a ≤ g / 4 := by linarith only [hp0_le, hgbig]
      have k1 : (1 / 2) * a ^ 2 - (1 / 2) * b ^ 2
          ≤ (1 / 2) * a ^ 2 - (1 / 2) * (g - a) ^ 2 := by linarith only [hgsq]
      have k2 : (1 / 2) * a ^ 2 - (1 / 2) * (g - a) ^ 2 = g * a - g ^ 2 / 2 := by ring
      have k3 : g * a - g ^ 2 / 2 ≤ -g ^ 2 / 4 := by nlinarith only [hp0_g4, hgpos, hapos]
      have k4 : -g ^ 2 / 4 ≤ -c ^ 2 := by nlinarith only [hgbig, hcpos]
      linarith only [k1, k2, k3, k4]
    have hHamDiff :
        hamiltonian U (x0, p0) - hamiltonian U (leapfrogFlow U ε L (x0, p0)) ≤ -R := by
      have hh1 : hamiltonian U (x0, p0) = U x0 + (1 / 2) * ‖p0‖ ^ 2 := by simp [hamiltonian]
      have hh2 : hamiltonian U (leapfrogFlow U ε L (x0, p0)) = U (x L) + (1 / 2) * ‖p L‖ ^ 2 := by
        unfold hamiltonian
        rfl
      rw [hh1, hh2]
      linarith [hmain, hK', sq_nonneg ‖x0‖]
    calc acceptProb U ε L (x0, p0)
        = min 1 (Real.exp (hamiltonian U (x0, p0) - hamiltonian U (leapfrogFlow U ε L (x0, p0)))) := rfl
      _ ≤ Real.exp (hamiltonian U (x0, p0) - hamiltonian U (leapfrogFlow U ε L (x0, p0))) := min_le_right 1 _
      _ ≤ Real.exp (-R) := Real.exp_le_exp.mpr hHamDiff
      _ = δ := hexpR
  /- @proof-region region.target-node.session.2001b82a6144931e end -/

end Statlib.Imported

end

