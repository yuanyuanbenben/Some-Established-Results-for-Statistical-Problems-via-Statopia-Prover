import ProverJobs.job_paper_df5fdc450bf24d85b08215e07b20fdad.Vocabulary
import ProverJobs.job_paper_df5fdc450bf24d85b08215e07b20fdad.ProvedNodes
import ProverJobs.job_paper_df5fdc450bf24d85b08215e07b20fdad.Base

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators
namespace Statlib.Imported

theorem paper_df5fdc450bf24d85b08215e07b20fdad :
    ∀ (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1 / 2)
      (c0 : ℝ) (hc0 : 0 < c0)
      (alpha : ℝ) (halpha : 0 < alpha)
      (Csigma : ℝ) (hCsigma : 0 < Csigma)
      (ccirc : ℝ) (hccirc0 : 0 < ccirc) (hccirc1 : ccirc < 1)
      (eps0 : ℝ) (heps0 : 0 < eps0) (heps0' : eps0 < 1)
      (CR : ℝ) (hCR : 0 < CR)
      (tau : ℕ → ℝ) (htau0 : ∀ n, 0 ≤ tau n) (htau1 : ∀ n, tau n < 1)
      (htau_growth : LessTilde (fun _ => (1 : ℝ))
        (fun n => (1 - tau n) * Real.sqrt (Real.log (n : ℝ)))),
    ∃ cSn : ℝ, 0 < cSn ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω]
        (p : ℕ → ℕ) (hp : ∀ n, 1 ≤ p n)
        (μ : Measure Ω) [IsProbabilityMeasure μ]
        (Sigma : (n : ℕ) → Matrix (Fin (p n)) (Fin (p n)) ℝ)
        (hSig_psd : ∀ n, (Sigma n).PosSemidef)
        (hSig_diag : ∀ (n : ℕ) (j : Fin (p n)), 0 < Sigma n j j)
        (mu : (n : ℕ) → Fin (p n) → ℝ)
        (Z : (n : ℕ) → Fin n → Ω → (Fin (p n) → ℝ))
        (X : (n : ℕ) → Fin n → Ω → (Fin (p n) → ℝ))
        (hX_model : ∀ (n : ℕ) (i : Fin n) (ω : Ω) (l : Fin (p n)),
          X n i ω l = mu n l + (Matrix.PosSemidef.sqrt (hSig_psd n)).mulVec (Z n i ω) l)
        (hZ_meas : ∀ (n : ℕ) (i : Fin n), Measurable (Z n i))
        (hZ_indep : ∀ n, iIndepFun (fun i : Fin n => Z n i) μ)
        (hZ_ident : ∀ (n : ℕ) (i j : Fin n), IdentDistrib (Z n i) (Z n j) μ μ)
        (hZ_mem : ∀ (n : ℕ) (i : Fin n), MemLp (Z n i) 2 μ)
        (hZ_mean : ∀ (n : ℕ) (i : Fin n) (l : Fin (p n)), ∫ ω, Z n i ω l ∂μ = 0)
        (hZ_cov : ∀ (n : ℕ) (i : Fin n) (u v : Fin (p n)),
          ∫ ω, Z n i ω u * Z n i ω v ∂μ = if u = v then 1 else 0)
        (hZ_psi : ∀ (n : ℕ) (i : Fin n) (u : Fin (p n) → ℝ), (∑ l, (u l) ^ 2) = 1 →
          psi1Norm (fun ω => ∑ l, u l * Z n i ω l) μ ≤ ENNReal.ofReal c0),
      ∀ n : ℕ, n0 ≤ n → ∀ (q : ℝ), 2 ≤ q → q ≤ Real.sqrt (n : ℝ) → ∀ j : Fin (p n),
        ∫⁻ ω, ENNReal.ofReal (|(sigmaOf p Sigma n j)⁻¹ * Svec p X mu n ω j| ^ q) ∂μ
          ≤ ENNReal.ofReal ((cSn * q) ^ q)
:= by
  /- @proof-region region.root.061152007dcd begin -/
  intro a ha0 ha1 c0 hc0 alpha halpha Csigma hCsigma ccirc hccirc0 hccirc1
    eps0 heps0 heps0' CR hCR tau htau0 htau1 htau_growth
  classical
  obtain ⟨ctau₀, hctau₀pos, N1, hN1ge, hN1₀⟩ := htau_growth
  let ctau : ℝ := ctau₀⁻¹
  have hctau_pos : (0 : ℝ) < ctau := inv_pos.mpr hctau₀pos
  have hN1 : ∀ n : ℕ, N1 ≤ n → ctau ≤ (1 - tau n) * Real.sqrt (Real.log (n : ℝ)) := by
    intro n hn
    have h₁ : (1 : ℝ) ≤ ctau₀ * ((1 - tau n) * Real.sqrt (Real.log (n : ℝ))) := hN1₀ n hn
    have hmul : ctau * 1 ≤ ctau * (ctau₀ * ((1 - tau n) * Real.sqrt (Real.log (n : ℝ)))) :=
      mul_le_mul_of_nonneg_left h₁ (le_of_lt hctau_pos)
    have hsimp : ctau * (ctau₀ * ((1 - tau n) * Real.sqrt (Real.log (n : ℝ)))) =
        (1 - tau n) * Real.sqrt (Real.log (n : ℝ)) := by
      show ctau₀⁻¹ * (ctau₀ * ((1 - tau n) * Real.sqrt (Real.log (n : ℝ)))) =
        (1 - tau n) * Real.sqrt (Real.log (n : ℝ))
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hctau₀pos), one_mul]
    linarith [hmul, hsimp]
  have hlog_eventually : ∀ M : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → M ≤ Real.log (n : ℝ) := by
    intro M
    obtain ⟨M', hM'⟩ := Filter.eventually_atTop.1
      (Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop M))
    exact ⟨Nat.ceil M', fun n hn =>
      hM' (n : ℝ) (le_trans (Nat.le_ceil M') (by exact_mod_cast hn))⟩
  have hthreshold : ∃ n0 : ℕ, 1 ≤ n0 ∧ ∀ n : ℕ, n0 ≤ n →
      qN alpha tau n = Real.log (n : ℝ) ∧
        (qN alpha tau n / max (Real.log (qN alpha tau n)) 1) *
            (n : ℝ) ^ ((-1 / 2 : ℝ) + 1 / qN alpha tau n) ≤ 1 := by
    obtain ⟨N2, hN2⟩ := hlog_eventually (max 3 (max ((2 / (alpha * ctau)) ^ 2) 9))
    obtain ⟨N3, hN3⟩ : ∃ N3 : ℕ, (8 : ℝ) ^ 8 ≤ (N3 : ℝ) :=
      ⟨Nat.ceil ((8 : ℝ) ^ 8), Nat.le_ceil _⟩
    set N0 : ℕ := N1 + N2 + N3 + 1 with hN0
    have hN0ge : 1 ≤ N0 := by omega
    refine ⟨N0, hN0ge, ?_⟩
    intro n hn
    have hnN1 : N1 ≤ n := by omega
    have hnN2 : N2 ≤ n := by omega
    have hnN3 : N3 ≤ n := by omega
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_trans hN0ge hn)
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hlog3 : 3 ≤ Real.log (n : ℝ) := le_trans (le_max_left _ _) (hN2 n hnN2)
    have hA2 : (2 / (alpha * ctau)) ^ 2 ≤ Real.log (n : ℝ) :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (hN2 n hnN2)
    have hlog9 : 9 ≤ Real.log (n : ℝ) :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (hN2 n hnN2)
    have hlogpos : 0 < Real.log (n : ℝ) := by linarith
    have hlog4 : 4 ≤ Real.log (n : ℝ) := by linarith
    have hqN : qN alpha tau n = Real.log (n : ℝ) := by
      have hAle : 2 / (alpha * ctau) ≤ Real.sqrt (Real.log (n : ℝ)) := by
        have h := Real.sqrt_le_sqrt hA2
        rwa [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 / (alpha * ctau))] at h
      have hsqi : Real.sqrt (Real.log (n : ℝ)) * Real.sqrt (Real.log (n : ℝ)) =
          Real.log (n : ℝ) := by
        have := Real.sq_sqrt hlogpos.le
        nlinarith [this]
      have hctau_le : ctau ≤ (1 - tau n) * Real.sqrt (Real.log (n : ℝ)) := hN1 n hnN1
      have hbeta1 : (0 : ℝ) < 1 - tau n := by linarith [htau1 n]
      have hsqnn : (0 : ℝ) ≤ Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_nonneg _
      have h2le : (2 : ℝ) ≤ alpha * ctau * Real.sqrt (Real.log (n : ℝ)) := by
        have h := hAle
        have hac : (0 : ℝ) < alpha * ctau := mul_pos halpha hctau_pos
        rw [div_le_iff₀ hac] at h
        calc (2 : ℝ) ≤ Real.sqrt (Real.log (n : ℝ)) * (alpha * ctau) := h
          _ = alpha * ctau * Real.sqrt (Real.log (n : ℝ)) := by ring
      have hprod : alpha * ctau * Real.sqrt (Real.log (n : ℝ)) ≤
          alpha * (1 - tau n) * Real.log (n : ℝ) := by
        calc alpha * ctau * Real.sqrt (Real.log (n : ℝ))
            ≤ (alpha * ((1 - tau n) * Real.sqrt (Real.log (n : ℝ)))) *
                Real.sqrt (Real.log (n : ℝ)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hctau_le halpha.le) hsqnn
          _ = alpha * (1 - tau n) *
                (Real.sqrt (Real.log (n : ℝ)) * Real.sqrt (Real.log (n : ℝ))) := by ring
          _ = alpha * (1 - tau n) * Real.log (n : ℝ) := by rw [hsqi]
      have hgoal : (2 : ℝ) ≤ alpha * (1 - tau n) * Real.log (n : ℝ) := le_trans h2le hprod
      have hdiv : 2 / (alpha * (1 - tau n)) ≤ Real.log (n : ℝ) := by
        rw [div_le_iff₀ (mul_pos halpha hbeta1)]
        linarith [hgoal]
      unfold qN betaN
      rw [max_eq_left (le_trans hlog3 (le_max_right _ _)), max_eq_right hdiv]
    refine ⟨hqN, ?_⟩
    rw [hqN]
    have hLnn : (0 : ℝ) ≤ Real.log (n : ℝ) := le_of_lt hlogpos
    have hfac1 : Real.log (n : ℝ) / max (Real.log (Real.log (n : ℝ))) 1 ≤ Real.log (n : ℝ) := by
      calc Real.log (n : ℝ) / max (Real.log (Real.log (n : ℝ))) 1 ≤ Real.log (n : ℝ) / 1 :=
            div_le_div_of_nonneg_left hLnn zero_lt_one (le_max_right _ _)
        _ = Real.log (n : ℝ) := by ring
    have hexp_le : (-1 / 2 : ℝ) + 1 / Real.log (n : ℝ) ≤ -1 / 4 := by
      have h1 : 1 / Real.log (n : ℝ) ≤ 1 / 4 :=
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hlog4
      linarith
    have hrpow : (n : ℝ) ^ ((-1 / 2 : ℝ) + 1 / Real.log (n : ℝ)) ≤ (n : ℝ) ^ (-1 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn1 hexp_le
    have hcomb : (n : ℝ) ^ (1 / 8 : ℝ) * (n : ℝ) ^ (-1 / 4 : ℝ) = (n : ℝ) ^ (-1 / 8 : ℝ) := by
      rw [← Real.rpow_add hnpos, show (1 / 8 : ℝ) + (-1 / 4) = -1 / 8 by norm_num]
    have hn88 : (8 : ℝ) ^ 8 ≤ (n : ℝ) := le_trans hN3 (by exact_mod_cast hnN3)
    have hdecay : (n : ℝ) ^ (-1 / 8 : ℝ) ≤ 1 / 8 := by
      rw [Real.rpow_def_of_pos hnpos]
      have hexp : Real.exp (Real.log (n : ℝ) * (-1 / 8)) ≤ Real.exp (Real.log (1 / 8 : ℝ)) := by
        apply Real.exp_le_exp.2
        have hlog88 : Real.log ((8 : ℝ) ^ 8) ≤ Real.log (n : ℝ) :=
          Real.log_le_log (by norm_num) hn88
        rw [show Real.log ((8 : ℝ) ^ 8) = 8 * Real.log 8 by
          rw [Real.log_pow]; push_cast; ring] at hlog88
        rw [show (1 / 8 : ℝ) = (8 : ℝ)⁻¹ by norm_num, Real.log_inv]
        linarith [hlog88]
      rwa [Real.exp_log (by norm_num : (0 : ℝ) < 1 / 8)] at hexp
    have hlog8b : Real.log (n : ℝ) ≤ 8 * (n : ℝ) ^ (1 / 8 : ℝ) := by
      have h := Real.log_le_rpow_div hnpos.le (show (0 : ℝ) < 1 / 8 by norm_num)
      have h2 : (n : ℝ) ^ (1 / 8 : ℝ) / (1 / 8) = 8 * (n : ℝ) ^ (1 / 8 : ℝ) := by
        rw [div_eq_mul_inv, show ((1 : ℝ) / 8)⁻¹ = 8 by norm_num, mul_comm]
      linarith [h, h2]
    have hmain : Real.log (n : ℝ) * (n : ℝ) ^ (-1 / 4 : ℝ) ≤ 1 := by
      have hnn : (0 : ℝ) ≤ (n : ℝ) ^ (-1 / 4 : ℝ) := le_of_lt (Real.rpow_pos_of_pos hnpos _)
      calc Real.log (n : ℝ) * (n : ℝ) ^ (-1 / 4 : ℝ)
          ≤ (8 * (n : ℝ) ^ (1 / 8 : ℝ)) * (n : ℝ) ^ (-1 / 4 : ℝ) :=
            mul_le_mul_of_nonneg_right hlog8b hnn
        _ = 8 * ((n : ℝ) ^ (1 / 8 : ℝ) * (n : ℝ) ^ (-1 / 4 : ℝ)) := by ring
        _ = 8 * (n : ℝ) ^ (-1 / 8 : ℝ) := by rw [hcomb]
        _ ≤ 8 * (1 / 8) := mul_le_mul_of_nonneg_left hdecay (by norm_num)
        _ = 1 := by norm_num
    calc (Real.log (n : ℝ) / max (Real.log (Real.log (n : ℝ))) 1) *
          (n : ℝ) ^ ((-1 / 2 : ℝ) + 1 / Real.log (n : ℝ))
        ≤ Real.log (n : ℝ) * (n : ℝ) ^ (-1 / 4 : ℝ) :=
          mul_le_mul hfac1 hrpow (le_of_lt (Real.rpow_pos_of_pos hnpos _)) hLnn
      _ ≤ 1 := hmain
  obtain ⟨n0, hn0ge, hn0P⟩ := hthreshold
  have hn0P' : ∀ m : ℕ, n0 ≤ m →
      qN alpha tau m = Real.log (m : ℝ) ∧
        (qN alpha tau m / max (Real.log (qN alpha tau m)) 1) *
            (m : ℝ) ^ (-(1 / 2 : ℝ) + 1 / qN alpha tau m) ≤ 1 := by
    intro m hm
    obtain ⟨h1, h2⟩ := hn0P m hm
    refine ⟨h1, ?_⟩
    rw [show (-(1 / 2 : ℝ)) = (-1 / 2 : ℝ) by norm_num]
    exact h2
  obtain ⟨C1, hC1pos, hC1⟩ := statopia_math_node_2505675723_75bd9af6 alpha halpha tau n0 hn0ge hn0P' c0 hc0
  refine ⟨C1, hC1pos, n0, hn0ge, ?_⟩
  intro Ω _inst p hp μ hμ Sigma hSig_psd hSig_diag mu Z X hX_model hZ_meas hZ_indep hZ_ident
    hZ_mem hZ_mean hZ_cov hZ_psi n hn q hq2 hqle j
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have hqne : q ≠ 0 := by linarith
  have h1 : LqNorm (fun ω => (sigmaOf p Sigma n j)⁻¹ * Svec p X mu n ω j) q μ
      ≤ ENNReal.ofReal (C1 * q) :=
    hC1 Ω (fun _ => μ) (fun _ => hμ) p Sigma hSig_psd
      (fun m => Matrix.PosSemidef.sqrt (hSig_psd m)) (fun _ => rfl) hSig_diag mu Z X
      hX_model hZ_meas hZ_indep hZ_mem hZ_mean hZ_cov hZ_psi n hn q hq2 hqle j
  have hone : (1 / q) * q = 1 := by rw [one_div, inv_mul_cancel₀ hqne]
  have hpow : (LqNorm (fun ω => (sigmaOf p Sigma n j)⁻¹ * Svec p X mu n ω j) q μ) ^ q
      = ∫⁻ ω, ENNReal.ofReal (|(sigmaOf p Sigma n j)⁻¹ * Svec p X mu n ω j| ^ q) ∂μ := by
    show ENNReal.rpow (ENNReal.rpow
        (∫⁻ ω, ENNReal.ofReal (|(sigmaOf p Sigma n j)⁻¹ * Svec p X mu n ω j| ^ q) ∂μ)
        (1 / q)) q
      = ∫⁻ ω, ENNReal.ofReal (|(sigmaOf p Sigma n j)⁻¹ * Svec p X mu n ω j| ^ q) ∂μ
    refine Eq.trans (ENNReal.rpow_mul _ (1 / q) q).symm ?_
    rw [hone]
    simp
  calc ∫⁻ ω, ENNReal.ofReal (|(sigmaOf p Sigma n j)⁻¹ * Svec p X mu n ω j| ^ q) ∂μ
      = (LqNorm (fun ω => (sigmaOf p Sigma n j)⁻¹ * Svec p X mu n ω j) q μ) ^ q := hpow.symm
    _ ≤ (ENNReal.ofReal (C1 * q)) ^ q := ENNReal.rpow_le_rpow h1 hq0
    _ = ENNReal.ofReal ((C1 * q) ^ q) :=
        ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hC1pos.le hq0) hq0
  /- @proof-region region.root.061152007dcd end -/

end Statlib.Imported

-- Paper root revision dfdc11fd-fc5e-4d67-b686-1b8cd046344b
