import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M031_Vocabulary
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M032_Base
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M034_Node_3224678180_5a630a9f_7124eef7

/- Original module ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_2575158844_69083b80_ad81c46d; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported

open MeasureTheory
open Statlib.Imported

noncomputable section
open MeasureTheory
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_2575158844_69083b80 : ∀ (t : ℝ) (ht : 1 ≤ t)
    (delta : ℝ) (hdelta : 0 < delta)
    (beta : ℝ) (hbeta : 0 < beta)
    (eps : ℝ) (heps_pos : 0 < eps) (heps_lt : eps < 1 / 2)
    (hB2 : 2 * delta ^ 2 * (Real.exp 1)⁻¹ * (t + beta) / (t + 1 + beta) *
        eps ^ (-(beta + 1)) ≥ 2)
    (hB3 : 2 * delta ^ 2 * (Real.exp 1)⁻¹ * (t + beta) /
        ((t + 1 + beta) * (Real.log 2) ^ (t + beta)) *
        eps ^ (-(t + 2 * beta + 1)) ≥ 2)
    (n s : ℕ) (hs : 1 ≤ s) (hns : t + (s : ℝ) ≤ (n : ℝ)),
    4 / max 1 ((eps * Real.log (n : ℝ)) ^ s) ≤
        (Gconst t eps delta beta * (s : ℝ) *
            lowerGamma (t + (s : ℝ) + beta) (eps * Real.log (n : ℝ)) /
          (eps ^ s * (Real.log ((n : ℝ) / (1 + eps))) ^ s)) * eps ^ (t - 1) ∧
      2 * min 1 (((eps * Real.log (n : ℝ)) ^ s)⁻¹) ≤
        (Gconst t eps delta beta * (s : ℝ) *
            lowerGamma (t + (s : ℝ) + beta) (eps * Real.log (n : ℝ)) /
          (eps ^ s * (Real.log ((n : ℝ) / (1 + eps))) ^ s)) * eps ^ (t - 1) := by
  /- @proof-region region.target-node.session.1e44aac2fb09fb86 begin -/
  intro t ht δ hdelta β hbeta ε heps_pos heps_lt hB2 hB3 n s hs hn
  obtain ⟨hγpos, hγb, hγc, hγd, hγe, hγf, hγg, hγh⟩ := statopia_math_node_3224678180_5a630a9f
  have htβ : 0 < t + β := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1ε : 0 < 1 + ε := by linarith
  have hsR : (1:ℝ) ≤ (s:ℝ) := by exact_mod_cast hs
  have hspos : (0:ℝ) < (s:ℝ) := by linarith
  have hn2 : (2:ℝ) ≤ (n:ℝ) := by linarith
  have hnpos : (0:ℝ) < (n:ℝ) := by linarith
  have hlog1 : (1:ℝ) < (n:ℝ) := by linarith
  have hlog2ε : 0 < ε * Real.log 2 := mul_pos heps_pos hlog2
  have hlogn : 0 < Real.log (n:ℝ) := Real.log_pos hlog1
  have hndiv_pos : 0 < (n:ℝ) / (1 + ε) := div_pos hnpos h1ε
  have hndiv_gt1 : (1:ℝ) < (n:ℝ) / (1 + ε) := by
    rw [lt_div_iff₀ h1ε]; nlinarith [heps_lt, hn2]
  have hndiv_le : (n:ℝ) / (1 + ε) ≤ (n:ℝ) := by
    rw [div_le_iff₀ h1ε]; nlinarith [mul_pos hnpos heps_pos]
  set u : ℝ := ε * Real.log (n:ℝ) with hudef
  set L : ℝ := Real.log ((n:ℝ) / (1 + ε)) with hLdef
  set c0 : ℝ := lowerGamma (t + β) (ε * Real.log 2) with hc0def
  set Φ : ℝ := lowerGamma (t + (s:ℝ) + β) u with hΦdef
  set W : ℝ := Gconst t ε δ β * (s:ℝ) * Φ / (ε^s * L^s) * ε^(t-1) with hWdef
  have hu_pos : 0 < u := by rw [hudef]; exact mul_pos heps_pos hlogn
  have hL_pos : 0 < L := by rw [hLdef]; exact Real.log_pos hndiv_gt1
  have hL_le : L ≤ Real.log (n:ℝ) := by
    rw [hLdef]; exact Real.log_le_log hndiv_pos hndiv_le
  have hc0pos : 0 < c0 := by
    rw [hc0def]; exact hγpos (t + β) (ε * Real.log 2) htβ hlog2ε
  have hNpos : 0 < t + (s:ℝ) + β := by linarith
  have hΦpos : 0 < Φ := by
    rw [hΦdef]; exact hγpos (t + (s:ℝ) + β) u hNpos hu_pos
  have hεpow : ε ^ (t - 1) * ε ^ (β + 1) = ε ^ (t + β) := by
    rw [← Real.rpow_add heps_pos, show t - 1 + (β + 1) = t + β by ring]
  have hWeq : W = (4 * δ^2 * (s:ℝ) * Φ / (ε^(β+1) * c0 * u^s)) * (Real.log (n:ℝ) / L)^s := by
    rw [hWdef]
    unfold Gconst
    rw [← hc0def]
    rw [hudef, mul_pow, div_pow]
    rw [← hεpow]
    field_simp
  have hρ : (1:ℝ) ≤ (Real.log (n:ℝ) / L)^s := by
    rw [← Real.rpow_natCast]
    apply Real.one_le_rpow
    · rw [le_div_iff₀ hL_pos]; simpa using hL_le
    · exact Nat.cast_nonneg s
  have hRpos : 0 < 4 * δ^2 * (s:ℝ) * Φ / (ε^(β+1) * c0 * u^s) := by
    apply div_pos
    · exact mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos hdelta 2)) hspos) hΦpos
    · exact mul_pos (mul_pos (Real.rpow_pos_of_pos heps_pos _) hc0pos) (pow_pos hu_pos s)
  have hR_le_W : 4 * δ^2 * (s:ℝ) * Φ / (ε^(β+1) * c0 * u^s) ≤ W := by
    rw [hWeq]
    simpa using mul_le_mul_of_nonneg_left hρ (le_of_lt hRpos)
  have hRA : u ≤ 1 → 4 ≤ 4 * δ^2 * (s:ℝ) * Φ / (ε^(β+1) * c0 * u^s) := by
    intro hu1
    have hexp1 : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
    have hlog2le : Real.log 2 ≤ Real.log (n:ℝ) := Real.log_le_log (by norm_num) (by linarith)
    have hulog : ε * Real.log 2 ≤ u := by
      rw [hudef]; exact mul_le_mul_of_nonneg_left hlog2le (le_of_lt heps_pos)
    have hpowmono : (ε * Real.log 2) ^ (t + β) ≤ u ^ (t + β) :=
      Real.rpow_le_rpow (le_of_lt hlog2ε) hulog (le_of_lt htβ)
    have hc0_cl : c0 * (t + β) ≤ (ε * Real.log 2) ^ (t + β) := by
      rw [hc0def]
      exact (le_div_iff₀ htβ).mp (hγb (t + β) (ε * Real.log 2) htβ hlog2ε)
    have hc0u : c0 * (t + β) ≤ u ^ (t + β) := le_trans hc0_cl hpowmono
    have hε : (0:ℝ) < ε^(β+1) := Real.rpow_pos_of_pos heps_pos _
    have hd : (0:ℝ) < t + 1 + β := by linarith
    have hεne : ε^(β+1) ≠ 0 := ne_of_gt hε
    have hR6 : t + (s:ℝ) + β ≤ (s:ℝ) * (t + 1 + β) := by
      have hs1 : (0:ℝ) ≤ (s:ℝ) - 1 := by linarith
      have hp := mul_nonneg (le_of_lt htβ) hs1
      nlinarith [hp]
    have hneg : ε ^ (-(β+1)) * ε ^ (β+1) = 1 := by
      rw [← Real.rpow_add heps_pos, show -(β+1) + (β+1) = 0 by ring, Real.rpow_zero]
    have hPeq : (2 * δ^2 * (Real.exp 1)⁻¹ * (t + β) / (t + 1 + β) * ε ^ (-(β+1))) * ε^(β+1) = 2 * δ^2 * (Real.exp 1)⁻¹ * ((t + β) / (t + 1 + β)) := by
      rw [mul_assoc, hneg, mul_one, mul_div_assoc]
    have hR5 : ε^(β+1) * (t + 1 + β) ≤ δ^2 * (Real.exp 1)⁻¹ * (t + β) := by
      have h1 : 2 * ε^(β+1) ≤ 2 * δ^2 * (Real.exp 1)⁻¹ * ((t + β) / (t + 1 + β)) := by
        have h0 := mul_le_mul_of_nonneg_right hB2 (le_of_lt hε)
        rwa [hPeq] at h0
      have h2 : ε^(β+1) ≤ δ^2 * (Real.exp 1)⁻¹ * ((t + β) / (t + 1 + β)) := by linarith
      rw [← mul_div_assoc] at h2
      exact (le_div_iff₀ hd).mp h2
    have hMN : ε^(β+1) * (t + (s:ℝ) + β) ≤ δ^2 * (s:ℝ) * (Real.exp 1)⁻¹ * (t + β) := by
      have step1 : (s:ℝ) * (ε^(β+1) * (t + 1 + β)) ≤ (s:ℝ) * (δ^2 * (Real.exp 1)⁻¹ * (t + β)) :=
        mul_le_mul_of_nonneg_left hR5 (le_of_lt hspos)
      have step2 : ε^(β+1) * (t + (s:ℝ) + β) ≤ ε^(β+1) * ((s:ℝ) * (t + 1 + β)) :=
        mul_le_mul_of_nonneg_left hR6 (le_of_lt hε)
      calc ε^(β+1) * (t + (s:ℝ) + β) ≤ ε^(β+1) * ((s:ℝ) * (t + 1 + β)) := step2
        _ = (s:ℝ) * (ε^(β+1) * (t + 1 + β)) := by ring
        _ ≤ (s:ℝ) * (δ^2 * (Real.exp 1)⁻¹ * (t + β)) := step1
        _ = δ^2 * (s:ℝ) * (Real.exp 1)⁻¹ * (t + β) := by ring
    have hMaster : ε^(β+1) * c0 * (t + (s:ℝ) + β) ≤ δ^2 * (s:ℝ) * (Real.exp 1)⁻¹ * u^(t+β) := by
      have stepA : c0 * (ε^(β+1) * (t + (s:ℝ) + β)) ≤ c0 * (δ^2 * (s:ℝ) * (Real.exp 1)⁻¹ * (t + β)) :=
        mul_le_mul_of_nonneg_left hMN (le_of_lt hc0pos)
      have hfac : (0:ℝ) ≤ δ^2 * (s:ℝ) * (Real.exp 1)⁻¹ :=
        mul_nonneg (mul_nonneg (le_of_lt (pow_pos hdelta 2)) (le_of_lt hspos))
          (le_of_lt (inv_pos.mpr (Real.exp_pos 1)))
      have hc := mul_le_mul_of_nonneg_left hc0u hfac
      have stepB : c0 * (δ^2 * (s:ℝ) * (Real.exp 1)⁻¹ * (t + β)) ≤ δ^2 * (s:ℝ) * (Real.exp 1)⁻¹ * u^(t+β) := by
        calc c0 * (δ^2 * (s:ℝ) * (Real.exp 1)⁻¹ * (t + β)) = (δ^2 * (s:ℝ) * (Real.exp 1)⁻¹) * (c0 * (t + β)) := by ring
          _ ≤ (δ^2 * (s:ℝ) * (Real.exp 1)⁻¹) * u^(t+β) := hc
          _ = δ^2 * (s:ℝ) * (Real.exp 1)⁻¹ * u^(t+β) := by ring
      calc ε^(β+1) * c0 * (t + (s:ℝ) + β) = c0 * (ε^(β+1) * (t + (s:ℝ) + β)) := by ring
        _ ≤ c0 * (δ^2 * (s:ℝ) * (Real.exp 1)⁻¹ * (t + β)) := stepA
        _ ≤ δ^2 * (s:ℝ) * (Real.exp 1)⁻¹ * u^(t+β) := stepB
    have hexp : Real.exp (-1) ≤ Real.exp (-u) := by
      rw [Real.exp_le_exp]; linarith
    have hnum_le : Real.exp (-1) * u ^ (t + (s:ℝ) + β) ≤ Real.exp (-u) * u ^ (t + (s:ℝ) + β) :=
      mul_le_mul_of_nonneg_right hexp (le_of_lt (Real.rpow_pos_of_pos hu_pos _))
    have hstep1 : Real.exp (-1) * u ^ (t + (s:ℝ) + β) / (t + (s:ℝ) + β) ≤ Real.exp (-u) * u ^ (t + (s:ℝ) + β) / (t + (s:ℝ) + β) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hnum_le (le_of_lt (inv_pos.mpr hNpos))
    have hPhi_lb : Real.exp (-1) * u ^ (t + (s:ℝ) + β) / (t + (s:ℝ) + β) ≤ Φ := by
      rw [hΦdef]; exact le_trans hstep1 (hγc _ _ hNpos hu_pos)
    have huN : u ^ (t + (s:ℝ) + β) = u ^ (t + β) * u ^ s := by
      rw [show t + (s:ℝ) + β = (t + β) + (s:ℝ) by ring, Real.rpow_add hu_pos, Real.rpow_natCast]
    have h4ds : (0:ℝ) < 4 * δ^2 * (s:ℝ) := mul_pos (mul_pos (by norm_num) (pow_pos hdelta 2)) hspos
    have hdenpos : (0:ℝ) < ε^(β+1) * c0 * u^s := mul_pos (mul_pos hε hc0pos) (pow_pos hu_pos s)
    rw [le_div_iff₀ hdenpos]
    have hphase : 4 * δ^2 * (s:ℝ) * (Real.exp (-1) * u ^ (t + (s:ℝ) + β) / (t + (s:ℝ) + β)) ≤ 4 * δ^2 * (s:ℝ) * Φ :=
      mul_le_mul_of_nonneg_left hPhi_lb (le_of_lt h4ds)
    have hkey : 4 * (ε^(β+1) * c0 * u^s) ≤ 4 * δ^2 * (s:ℝ) * (Real.exp (-1) * u ^ (t + (s:ℝ) + β) / (t + (s:ℝ) + β)) := by
      rw [huN]
      rw [← mul_div_assoc]
      rw [le_div_iff₀ hNpos]
      rw [hexp1]
      have h4us : (0:ℝ) ≤ 4 * u^s := le_of_lt (mul_pos (by norm_num) (pow_pos hu_pos s))
      have hmult := mul_le_mul_of_nonneg_left hMaster h4us
      have hL_eq : 4 * (ε^(β+1) * c0 * u^s) * (t + (s:ℝ) + β) = (4 * u^s) * (ε^(β+1) * c0 * (t + (s:ℝ) + β)) := by ring
      have hR_eq : 4 * δ^2 * (s:ℝ) * ((Real.exp 1)⁻¹ * (u ^ (t + β) * u ^ s)) = (4 * u^s) * (δ^2 * (s:ℝ) * (Real.exp 1)⁻¹ * u^(t+β)) := by ring
      rw [hL_eq, hR_eq]
      exact hmult
    linarith [hphase, hkey]
  have hRB : 1 ≤ u → 4 ≤ 4 * δ^2 * (s:ℝ) * Φ / (ε^(β+1) * c0) := by
    intro hu1
    have hexp1 : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
    have hPhiB : Real.exp (-1) / (t + (s:ℝ) + β) ≤ Φ := by
      have h1mem : (1:ℝ) ∈ Set.Ioi 0 := show (0:ℝ) < 1 from by norm_num
      have humem : u ∈ Set.Ioi 0 := hu_pos
      have hmono : lowerGamma (t + (s:ℝ) + β) 1 ≤ lowerGamma (t + (s:ℝ) + β) u :=
        (hγf (t + (s:ℝ) + β) hNpos) h1mem humem hu1
      have hd1 : Real.exp (-1) / (t + (s:ℝ) + β) ≤ lowerGamma (t + (s:ℝ) + β) 1 :=
        hγd (t + (s:ℝ) + β) (1:ℝ) hNpos (le_refl (1:ℝ))
      rw [hΦdef]; exact le_trans hd1 hmono
    have hd : (0:ℝ) < t + 1 + β := by linarith
    have hε3 : (0:ℝ) < ε^(t+2*β+1) := Real.rpow_pos_of_pos heps_pos _
    have hlog2p : (0:ℝ) < (Real.log 2)^(t+β) := Real.rpow_pos_of_pos hlog2 (t+β)
    have hden3 : (0:ℝ) < (t + 1 + β) * (Real.log 2)^(t+β) := mul_pos hd hlog2p
    have hc0_cl2 : c0 * (t + β) ≤ (ε * Real.log 2)^(t+β) := by
      rw [hc0def]
      exact (le_div_iff₀ htβ).mp (hγb (t + β) (ε * Real.log 2) htβ hlog2ε)
    have hneg3 : ε ^ (-(t+2*β+1)) * ε ^ (t+2*β+1) = 1 := by
      rw [← Real.rpow_add heps_pos, show -(t+2*β+1) + (t+2*β+1) = 0 by ring, Real.rpow_zero]
    have hQ3 : (2 * δ^2 * (Real.exp 1)⁻¹ * (t + β) / ((t + 1 + β) * (Real.log 2)^(t+β)) * ε ^ (-(t+2*β+1))) * ε^(t+2*β+1) = 2 * δ^2 * (Real.exp 1)⁻¹ * (t + β) / ((t + 1 + β) * (Real.log 2)^(t+β)) := by
      rw [mul_assoc, hneg3, mul_one]
    have hB3c : ε^(t+2*β+1) * ((t + 1 + β) * (Real.log 2)^(t+β)) ≤ δ^2 * (Real.exp 1)⁻¹ * (t + β) := by
      have h1 : 2 * ε^(t+2*β+1) ≤ 2 * δ^2 * (Real.exp 1)⁻¹ * (t + β) / ((t + 1 + β) * (Real.log 2)^(t+β)) := by
        have h0 := mul_le_mul_of_nonneg_right hB3 (le_of_lt hε3)
        rwa [hQ3] at h0
      have h2 := (le_div_iff₀ hden3).mp h1
      have hhalf := mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ) ≤ (1/2))
      have e1 : (1/2 : ℝ) * ((2 * ε^(t+2*β+1)) * ((t + 1 + β) * (Real.log 2)^(t+β))) = ε^(t+2*β+1) * ((t + 1 + β) * (Real.log 2)^(t+β)) := by ring
      have e2 : (1/2 : ℝ) * (2 * δ^2 * (Real.exp 1)⁻¹ * (t + β)) = δ^2 * (Real.exp 1)⁻¹ * (t + β) := by ring
      rwa [e1, e2] at hhalf
    have hεcomb : ε^(β+1) * (ε * Real.log 2)^(t+β) = ε^(t+2*β+1) * (Real.log 2)^(t+β) := by
      rw [Real.mul_rpow (le_of_lt heps_pos) (le_of_lt hlog2)]
      rw [← mul_assoc, ← Real.rpow_add heps_pos, show β + 1 + (t + β) = t + 2*β + 1 by ring]
    have hPnn : (0:ℝ) ≤ ε^(t+2*β+1) * (Real.log 2)^(t+β) := le_of_lt (mul_pos hε3 hlog2p)
    have hNle : t + (s:ℝ) + β ≤ (s:ℝ) * (t + 1 + β) := by
      have h2 : t + β ≤ (s:ℝ) * (t + β) := by
        calc t + β = (t + β) * 1 := by rw [mul_one]
          _ ≤ (t + β) * (s:ℝ) := mul_le_mul_of_nonneg_left hsR (le_of_lt htβ)
          _ = (s:ℝ) * (t + β) := by rw [mul_comm]
      have e : (s:ℝ) * (t + 1 + β) = (s:ℝ) * (t + β) + (s:ℝ) := by ring
      have e2 : t + (s:ℝ) + β = (t + β) + (s:ℝ) := by ring
      rw [e, e2]
      linarith only [h2]
    have hB3c' : (ε^(t+2*β+1) * (Real.log 2)^(t+β)) * (t + 1 + β) ≤ δ^2 * (Real.exp 1)⁻¹ * (t + β) := by
      calc (ε^(t+2*β+1) * (Real.log 2)^(t+β)) * (t + 1 + β) = ε^(t+2*β+1) * ((t + 1 + β) * (Real.log 2)^(t+β)) := by ring
        _ ≤ δ^2 * (Real.exp 1)⁻¹ * (t + β) := hB3c
    have hMN_B : (ε^(t+2*β+1) * (Real.log 2)^(t+β)) * (t + (s:ℝ) + β) ≤ δ^2 * (s:ℝ) * (Real.exp 1)⁻¹ * (t + β) := by
      have stepa : (ε^(t+2*β+1) * (Real.log 2)^(t+β)) * (t + (s:ℝ) + β) ≤ (ε^(t+2*β+1) * (Real.log 2)^(t+β)) * ((s:ℝ) * (t + 1 + β)) :=
        mul_le_mul_of_nonneg_left hNle hPnn
      have stepb : (ε^(t+2*β+1) * (Real.log 2)^(t+β)) * ((s:ℝ) * (t + 1 + β)) ≤ δ^2 * (s:ℝ) * (Real.exp 1)⁻¹ * (t + β) := by
        have hb := mul_le_mul_of_nonneg_right hB3c' (le_of_lt hspos)
        calc (ε^(t+2*β+1) * (Real.log 2)^(t+β)) * ((s:ℝ) * (t + 1 + β)) = ((ε^(t+2*β+1) * (Real.log 2)^(t+β)) * (t + 1 + β)) * (s:ℝ) := by ring
          _ ≤ (δ^2 * (Real.exp 1)⁻¹ * (t + β)) * (s:ℝ) := hb
          _ = δ^2 * (s:ℝ) * (Real.exp 1)⁻¹ * (t + β) := by ring
      exact le_trans stepa stepb
    have hMBdiv : (ε^(t+2*β+1) * (Real.log 2)^(t+β)) * (t + (s:ℝ) + β) / (t + β) ≤ δ^2 * (s:ℝ) * (Real.exp 1)⁻¹ :=
      (div_le_iff₀ htβ).mpr hMN_B
    have hc0le : c0 ≤ (ε * Real.log 2)^(t+β) / (t + β) := (le_div_iff₀ htβ).mpr hc0_cl2
    have hstep : ε^(β+1) * c0 ≤ (ε^(t+2*β+1) * (Real.log 2)^(t+β)) / (t + β) := by
      calc ε^(β+1) * c0 ≤ ε^(β+1) * ((ε * Real.log 2)^(t+β) / (t + β)) := mul_le_mul_of_nonneg_left hc0le (le_of_lt (Real.rpow_pos_of_pos heps_pos (β+1)))
        _ = (ε^(β+1) * (ε * Real.log 2)^(t+β)) / (t + β) := by rw [← mul_div_assoc]
        _ = (ε^(t+2*β+1) * (Real.log 2)^(t+β)) / (t + β) := by rw [hεcomb]
    have hMB : ε^(β+1) * c0 * (t + (s:ℝ) + β) ≤ δ^2 * (s:ℝ) * (Real.exp 1)⁻¹ := by
      have hmult := mul_le_mul_of_nonneg_right hstep (le_of_lt hNpos)
      have hrearr : ((ε^(t+2*β+1) * (Real.log 2)^(t+β)) / (t + β)) * (t + (s:ℝ) + β) = (ε^(t+2*β+1) * (Real.log 2)^(t+β)) * (t + (s:ℝ) + β) / (t + β) := by ring
      rw [hrearr] at hmult
      exact le_trans hmult hMBdiv
    have h4dsB : (0:ℝ) < 4 * δ^2 * (s:ℝ) := mul_pos (mul_pos (by norm_num) (pow_pos hdelta 2)) hspos
    have hdenpos2 : (0:ℝ) < ε^(β+1) * c0 := mul_pos (Real.rpow_pos_of_pos heps_pos (β+1)) hc0pos
    rw [le_div_iff₀ hdenpos2]
    have hphaseB : 4 * δ^2 * (s:ℝ) * (Real.exp (-1) / (t + (s:ℝ) + β)) ≤ 4 * δ^2 * (s:ℝ) * Φ :=
      mul_le_mul_of_nonneg_left hPhiB (le_of_lt h4dsB)
    have hkeyB : 4 * (ε^(β+1) * c0) ≤ 4 * δ^2 * (s:ℝ) * (Real.exp (-1) / (t + (s:ℝ) + β)) := by
      rw [← mul_div_assoc]
      rw [le_div_iff₀ hNpos]
      rw [hexp1]
      have h4 : (0:ℝ) ≤ 4 := by norm_num
      have hmultB := mul_le_mul_of_nonneg_left hMB h4
      have hL2 : 4 * (ε^(β+1) * c0) * (t + (s:ℝ) + β) = 4 * (ε^(β+1) * c0 * (t + (s:ℝ) + β)) := by ring
      have hR2 : 4 * δ^2 * (s:ℝ) * (Real.exp 1)⁻¹ = 4 * (δ^2 * (s:ℝ) * (Real.exp 1)⁻¹) := by ring
      rw [hL2, hR2]
      exact hmultB
    linarith [hphaseB, hkeyB]

  have hRR2 : 4 * δ^2 * (s:ℝ) * Φ / (ε^(β+1) * c0 * u^s) = (4 * δ^2 * (s:ℝ) * Φ / (ε^(β+1) * c0)) / u^s := by
    rw [div_div]
  have hconj1 : 4 / max 1 (u ^ s) ≤ W := by
    rcases le_total u 1 with hle | hge
    · have hup : u ^ s ≤ 1 := by
        rw [← Real.rpow_natCast]
        have h1 : u ^ ((s:ℝ)) ≤ (1:ℝ) ^ ((s:ℝ)) :=
          Real.rpow_le_rpow (le_of_lt hu_pos) hle (Nat.cast_nonneg s)
        simpa using h1
      have hmaxA : max 1 (u ^ s) = 1 :=
        le_antisymm (max_le le_rfl hup) (le_max_left 1 (u ^ s))
      rw [hmaxA, div_one]
      exact le_trans (hRA hle) hR_le_W
    · have hup : (1:ℝ) ≤ u ^ s := by
        rw [← Real.rpow_natCast]
        have h1 : (1:ℝ) ^ ((s:ℝ)) ≤ u ^ ((s:ℝ)) :=
          Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hge (Nat.cast_nonneg s)
        simpa using h1
      have hmaxB : max 1 (u ^ s) = u ^ s :=
        le_antisymm (max_le hup le_rfl) (le_max_right 1 (u ^ s))
      rw [hmaxB]
      refine le_trans ?_ hR_le_W
      rw [hRR2]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (hRB hge) (le_of_lt (inv_pos.mpr (pow_pos hu_pos s)))
  have hconj2 : 2 * min 1 ((u ^ s)⁻¹) ≤ W := by
    have hu0 : 0 < u ^ s := pow_pos hu_pos s
    have hstep : 2 * min 1 ((u ^ s)⁻¹) ≤ 4 / max 1 (u ^ s) := by
      rcases le_total 1 (u ^ s) with h | h
      · have hmini : min 1 ((u ^ s)⁻¹) ≤ (u ^ s)⁻¹ := min_le_right _ _
        have hmaxa : max 1 (u ^ s) = u ^ s :=
          le_antisymm (max_le h le_rfl) (le_max_right 1 (u ^ s))
        have hinvpos : 0 < (u ^ s)⁻¹ := inv_pos.mpr hu0
        have h2 : 2 * (u ^ s)⁻¹ ≤ 4 * (u ^ s)⁻¹ :=
          mul_le_mul_of_nonneg_right (by norm_num) (le_of_lt hinvpos)
        have hleft : 2 * min 1 ((u ^ s)⁻¹) ≤ 2 * (u ^ s)⁻¹ :=
          mul_le_mul_of_nonneg_left hmini (by norm_num)
        rw [hmaxa, div_eq_mul_inv]
        exact le_trans hleft h2
      · have hmini : min 1 ((u ^ s)⁻¹) ≤ 1 := min_le_left _ _
        have hmaxa : max 1 (u ^ s) = 1 :=
          le_antisymm (max_le le_rfl h) (le_max_left 1 (u ^ s))
        rw [hmaxa, div_one]
        have hleft : 2 * min 1 ((u ^ s)⁻¹) ≤ 2 * 1 :=
          mul_le_mul_of_nonneg_left hmini (by norm_num)
        linarith
    exact le_trans hstep hconj1
  exact ⟨hconj1, hconj2⟩
  /- @proof-region region.target-node.session.1e44aac2fb09fb86 end -/

end Statlib.Imported
end
end DPCompletedProof
