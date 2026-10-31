import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Vocabulary
import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Base
import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.ProvedNodes.Node_19064832_302da345_47147d5c
import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.ProvedNodes.Node_3783089969_b272d923_d0043e97
import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.ProvedNodes.Node_4214122249_d32c5e83_0bd87f24
import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.ProvedNodes.Node_4249859734_bd75d9c7_fed52f15

namespace PaperProofTasks.job_paper_cb04ce35a04d48a9bf96750470ca0eb0
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
open _root_.PaperProofTasks.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Statlib.Imported

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
namespace Statlib.Imported

noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_592878890_3cc8cbb4 : ∀ (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1 / 2)
    (alpha : ℝ) (halpha : 0 < alpha)
    (C_sigma : ℝ) (hC_sigma : 0 < C_sigma)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (p : ℕ → ℕ) (hp : ∀ n, 1 ≤ p n)
    (Sig : (n : ℕ) → Matrix (Fin (p n)) (Fin (p n)) ℝ)
    (hSig_psd : ∀ n, (Sig n).PosSemidef)
    (hSig_diag : ∀ (n : ℕ) (j : Fin (p n)), 0 < Sig n j j)
    (piPerm : (n : ℕ) → Equiv.Perm (Fin (p n)))
    (hpi_sorted : ∀ n, Antitone (fun i : Fin (p n) =>
      Real.sqrt (Sig n (piPerm n i) (piPerm n i))))
    (muV : (n : ℕ) → Fin (p n) → ℝ)
    (X : (n : ℕ) → Fin n → Ω → (Fin (p n) → ℝ))
    (hX_meas : ∀ (n : ℕ) (i : Fin n) (j : Fin (p n)),
      AEStronglyMeasurable (fun ω : Ω => X n i ω j) μ)
    (L : ℕ → ℕ)
    (hL_def : ∀ n, L n = Nat.ceil (min (max 1 ((Real.log (n : ℝ)) ^ (3 : ℕ))) ((p n : ℝ))))
    (hL_le_p : ∀ n, L n ≤ p n)
    (k : ℕ → ℕ)
    (hk_def : ∀ n, k n = Nat.ceil
      (min (max (L n : ℝ) (Real.rpow (n : ℝ) (1 / Real.rpow (Real.log (n : ℝ)) a)))
        ((p n : ℝ))))
    (tau : ℕ → ℝ) (htau0 : ∀ n, 0 ≤ tau n) (htau1 : ∀ n, tau n < 1)
    (beta : ℕ → ℝ) (hbeta_def : ∀ n, beta n = alpha * (1 - tau n))
    (htau_cond : LessTilde (fun _ => (1 : ℝ))
      (fun n => (1 - tau n) * Real.sqrt (Real.log (n : ℝ))))
    (hsigma_upper : ∀ (n : ℕ) (i : Fin (p n)), k n ≤ (i : ℕ) + 1 →
      Real.sqrt (Sig n (piPerm n i) (piPerm n i)) ≤
        C_sigma * Real.rpow (((i : ℕ) + 1 : ℕ) : ℝ) (-alpha))
    (c_Sn : ℝ) (hc_Sn : 0 < c_Sn)
    (n0 : ℕ) (hn0 : 1 ≤ n0)
    (H : ∀ (n : ℕ), n0 ≤ n → ∀ (q : ℝ), 2 ≤ q → q ≤ Real.sqrt (n : ℝ) →
      ∀ j : Fin (p n),
        ∫⁻ ω, ENNReal.ofReal
          (|(Real.sqrt (Sig n j j))⁻¹ *
            ((Real.sqrt (n : ℝ))⁻¹ * ∑ i : Fin n, (X n i ω j - muV n j))| ^ q) ∂μ
          ≤ ENNReal.ofReal ((c_Sn * q) ^ q)),
    ∃ c_thr : ℝ, 0 < c_thr ∧
      ∃ C2 : ℝ, 0 < C2 ∧
        ∃ N2 : ℕ, 1 ≤ N2 ∧
          ∀ n : ℕ, N2 ≤ n →
            μ (Bevent p X muV Sig tau k piPerm n (t1fun k beta c_thr n)) ≤
              ENNReal.ofReal (C2 * Real.rpow (n : ℝ) (-1)) := by
  /- @proof-region region.target-node.session.3b8d3512c4b82d69 begin -/
  intro a ha0 ha1 alpha halpha C_sigma hC_sigma Ω instΩ μ instμ p hp Sig hSig_psd
    hSig_diag piPerm hpi_sorted muV X hX_meas L hL_def hL_le_p k hk_def tau htau0 htau1
    beta hbeta_def htau_cond hsigma_upper c_Sn hc_Sn n0 hn0 H
  obtain ⟨c_τ, hc_τ_pos, n_τ, hn_τ⟩ := htau_cond
  set C1 : ℝ := max C_sigma 1 with hC1
  set C3 : ℝ := 8 + 2 * c_τ / alpha with hC3
  set C2 : ℝ := max 1 (2 * c_Sn * C1) with hC2
  have hC2_ge1 : (1 : ℝ) ≤ C2 := by rw [hC2]; exact le_max_left _ _
  have hC1cSn : 2 * C1 * c_Sn ≤ C2 := by
    rw [hC2]
    have h : 2 * C1 * c_Sn = 2 * c_Sn * C1 := by ring
    rw [h]
    exact le_max_right _ _
  have hC1_ge1 : (1 : ℝ) ≤ C1 := le_max_right _ _
  have hC1_ge : C_sigma ≤ C1 := le_max_left _ _
  have hC1_pos : 0 < C1 := lt_of_lt_of_le zero_lt_one hC1_ge1
  have hC3_pos : 0 < C3 := by rw [hC3]; positivity
  have hC3_ge8 : (8 : ℝ) ≤ C3 := by
    have h2 : 0 ≤ 2 * c_τ / alpha := by positivity
    rw [hC3]
    linarith
  have hC2_pos : 0 < C2 := by rw [hC2]; positivity
  have hcthr_pos : 0 < Real.exp 1 * C2 * C3 := by positivity
  have hkey : ∀ᶠ n : ℕ in Filter.atTop,
      μ (Bevent p X muV Sig tau k piPerm n (t1fun k beta (Real.exp 1 * C2 * C3) n))
        ≤ ENNReal.ofReal (C2 * Real.rpow (n : ℝ) (-1)) := by
    have hbundle : ∀ᶠ n : ℕ in Filter.atTop,
        ((1 : ℝ) ≤ Real.log (n : ℝ)) ∧
        (2 / beta n ≤ (2 * c_τ / alpha) * Real.log (n : ℝ)) ∧
        (Real.log (n : ℝ) + 4 ≤ Real.sqrt (n : ℝ)) ∧
        ((2 * c_τ / alpha) * Real.log (n : ℝ) ≤ Real.sqrt (n : ℝ)) ∧
        ((3 : ℝ) ≤ Real.sqrt (n : ℝ)) ∧
        ((k n : ℝ) ≤ Real.exp 2 * Real.sqrt (n : ℝ)) :=
      statopia_math_node_4249859734_bd75d9c7 a ha0 ha1 alpha halpha p hp L hL_def k hk_def tau
        htau0 htau1 beta hbeta_def c_τ hc_τ_pos n_τ hn_τ
    filter_upwards [eventually_ge_atTop n0, eventually_ge_atTop n_τ, hbundle]
      with n hn0' hnτ' hb
    obtain ⟨hlog, h4, h5, h6, h7, h8⟩ := hb
    have hlogpos : 0 < Real.log (n : ℝ) := by linarith
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      have h : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by linarith
      exact Real.one_le_sqrt.mp h
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hp_pos : (0 : ℝ) < (p n : ℝ) := by
      have h : (1 : ℕ) ≤ p n := hp n
      have h2 : (1 : ℝ) ≤ (p n : ℝ) := by exact_mod_cast h
      linarith
    have hL_pos : (0 : ℝ) < (L n : ℝ) := by
      have h1 : (0 : ℝ) < min (max 1 ((Real.log (n : ℝ)) ^ (3 : ℕ))) ((p n : ℝ)) := by
        refine lt_min ?_ hp_pos
        exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
      have h2 : 1 ≤ Nat.ceil (min (max 1 ((Real.log (n : ℝ)) ^ (3 : ℕ))) ((p n : ℝ))) :=
        Nat.one_le_ceil_iff.mpr h1
      rw [← hL_def n] at h2
      have h3 : (1 : ℝ) ≤ (L n : ℝ) := by exact_mod_cast h2
      linarith
    have hk1 : 1 ≤ k n := by
      have h1 : (0 : ℝ) < min (max (L n : ℝ)
          (Real.rpow (n : ℝ) (1 / Real.rpow (Real.log (n : ℝ)) a))) ((p n : ℝ)) := by
        refine lt_min ?_ hp_pos
        exact lt_of_lt_of_le hL_pos (le_max_left _ _)
      have h2 : 1 ≤ Nat.ceil (min (max (L n : ℝ)
          (Real.rpow (n : ℝ) (1 / Real.rpow (Real.log (n : ℝ)) a))) ((p n : ℝ))) :=
        Nat.one_le_ceil_iff.mpr h1
      rwa [← hk_def n] at h2
    have hk_pos : (0 : ℝ) < (k n : ℝ) := by
      have h : (1 : ℝ) ≤ (k n : ℝ) := by exact_mod_cast hk1
      linarith
    have hbeta_pos : 0 < beta n := by
      have h : 0 < 1 - tau n := by linarith [htau1 n]
      rw [hbeta_def n]
      positivity
    set qn : ℝ := max (max (Real.log (n : ℝ) + 4) (2 / beta n)) 3 with hqn
    have hq3 : 3 ≤ qn := le_max_right _ _
    have hqlog : Real.log (n : ℝ) + 4 ≤ qn := le_trans (le_max_left _ _) (le_max_left _ _)
    have hqbeta : 2 / beta n ≤ qn := le_trans (le_max_right _ _) (le_max_left _ _)
    have hq2 : 2 ≤ qn := le_trans (by norm_num) hq3
    have hqsqrt : qn ≤ Real.sqrt (n : ℝ) := by
      rw [hqn]
      exact max_le_iff.mpr ⟨max_le_iff.mpr ⟨h5, le_trans h4 h6⟩, h7⟩
    have hqbeta2 : 2 ≤ qn * beta n := by
      have h2 : 2 = (2 / beta n) * beta n := by
        rw [div_mul_cancel₀]
        exact ne_of_gt hbeta_pos
      rw [h2]
      exact mul_le_mul_of_nonneg_right hqbeta (le_of_lt hbeta_pos)
    have hC3q : qn ≤ C3 * Real.log (n : ℝ) := by
      rw [hqn]
      refine max_le_iff.mpr ⟨max_le_iff.mpr ⟨?_, ?_⟩, ?_⟩
      · calc Real.log (n : ℝ) + 4 ≤ 5 * Real.log (n : ℝ) := by linarith
          _ ≤ C3 * Real.log (n : ℝ) :=
            mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hlogpos)
      · calc 2 / beta n ≤ (2 * c_τ / alpha) * Real.log (n : ℝ) := h4
          _ ≤ C3 * Real.log (n : ℝ) := by
            refine mul_le_mul_of_nonneg_right ?_ (le_of_lt hlogpos)
            rw [hC3]; linarith
      · have h1 : (3 : ℝ) ≤ 3 * Real.log (n : ℝ) := by linarith
        have h2 : (3 : ℝ) ≤ C3 := by linarith
        exact le_trans h1 (mul_le_mul_of_nonneg_right h2 (le_of_lt hlogpos))
    set T : ℝ := t1fun k beta (Real.exp 1 * C2 * C3) n with hT
    have hT_pos : 0 < T := by
      rw [hT, t1fun]
      refine mul_pos (by positivity) (mul_pos ?_ hlogpos)
      exact Real.rpow_pos_of_pos hk_pos _
    set B : Fin (p n) → Set Ω :=
      fun j => {ω | T < Svec p X muV n ω j / Real.rpow (Real.sqrt (Sig n j j)) (tau n)} with hB
    set S : Finset (Fin (p n)) :=
      Finset.univ.filter (fun j => ¬ (((piPerm n).symm j : ℕ) < k n)) with hS
    have hBevent : Bevent p X muV Sig tau k piPerm n T = ⋃ j ∈ S, B j := by
      ext ω
      simp only [Bevent, hB, hS, Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_iUnion, exists_prop]
    have hunion : μ (Bevent p X muV Sig tau k piPerm n T) ≤ ∑ j ∈ S, μ (B j) := by
      rw [hBevent]
      exact MeasureTheory.measure_biUnion_finset_le S B
    have hn1n : 1 ≤ n := by exact_mod_cast hn1
    have hper : ∀ j ∈ S,
        μ (B j) ≤ ENNReal.ofReal
          (Real.rpow (Real.sqrt (Sig n j j)) (qn * (1 - tau n)) * (c_Sn * qn) ^ qn / T ^ qn) := by
      intro j _
      exact statopia_math_node_3783089969_b272d923 p X hX_meas muV Sig tau n hn1n j
        (hSig_diag n j) (htau1 n) qn T c_Sn hq2 hT_pos (H n hn0' qn hq2 hqsqrt j)
    have hxnonneg : ∀ j : Fin (p n),
        0 ≤ Real.rpow (Real.sqrt (Sig n j j)) (qn * (1 - tau n)) * (c_Sn * qn) ^ qn / T ^ qn := by
      intro j
      have h1 : (0 : ℝ) ≤ Real.rpow (Real.sqrt (Sig n j j)) (qn * (1 - tau n)) :=
        Real.rpow_nonneg (Real.sqrt_nonneg _) _
      have h2 : (0 : ℝ) ≤ (c_Sn * qn) ^ qn := Real.rpow_nonneg (by positivity) _
      have h3 : (0 : ℝ) < T ^ qn := Real.rpow_pos_of_pos hT_pos _
      exact div_nonneg (mul_nonneg h1 h2) (le_of_lt h3)
    have hsumofreal : ∀ s : Finset (Fin (p n)),
        ∑ j ∈ s, ENNReal.ofReal
            (Real.rpow (Real.sqrt (Sig n j j)) (qn * (1 - tau n)) * (c_Sn * qn) ^ qn / T ^ qn)
          = ENNReal.ofReal (∑ j ∈ s,
            Real.rpow (Real.sqrt (Sig n j j)) (qn * (1 - tau n)) * (c_Sn * qn) ^ qn / T ^ qn) := by
      intro s
      induction s using Finset.induction with
      | empty => simp
      | insert a s ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha, ih]
          exact (ENNReal.ofReal_add (hxnonneg a)
            (Finset.sum_nonneg (fun j _ => hxnonneg j))).symm
    have hsum1 : ∑ j ∈ S, μ (B j) ≤ ENNReal.ofReal (∑ j ∈ S,
        Real.rpow (Real.sqrt (Sig n j j)) (qn * (1 - tau n)) * (c_Sn * qn) ^ qn / T ^ qn) := by
      rw [← hsumofreal S]
      exact Finset.sum_le_sum hper
    have hsigsum : ∑ j ∈ S,
          Real.rpow (Real.sqrt (Sig n j j)) (qn * (1 - tau n)) * (c_Sn * qn) ^ qn / T ^ qn
        ≤ Real.rpow C1 qn * Real.rpow (k n : ℝ) (1 - qn * beta n)
          * (c_Sn * qn) ^ qn / T ^ qn := by
      have hsigonly : ∑ j ∈ S, Real.rpow (Real.sqrt (Sig n j j)) (qn * (1 - tau n))
          ≤ Real.rpow C1 qn * Real.rpow (k n : ℝ) (1 - qn * beta n) :=
        statopia_math_node_4214122249_d32c5e83 C1 C_sigma alpha qn p Sig piPerm tau beta k n
          hC_sigma hC1_ge hC1_ge1 (fun i hi => hsigma_upper n i hi) (htau0 n)
          (by linarith [htau1 n]) (hbeta_def n) (by linarith) hqbeta2 hk1
      have hCnn : (0 : ℝ) ≤ (c_Sn * qn) ^ qn / T ^ qn := by
        refine div_nonneg ?_ (le_of_lt (Real.rpow_pos_of_pos hT_pos qn))
        exact Real.rpow_nonneg (le_of_lt (mul_pos hc_Sn (by linarith))) qn
      calc ∑ j ∈ S,
            Real.rpow (Real.sqrt (Sig n j j)) (qn * (1 - tau n)) * (c_Sn * qn) ^ qn / T ^ qn
          = (∑ j ∈ S, Real.rpow (Real.sqrt (Sig n j j)) (qn * (1 - tau n)))
              * ((c_Sn * qn) ^ qn / T ^ qn) := by
            simp only [div_eq_mul_inv]
            rw [← Finset.sum_mul, ← Finset.sum_mul]
            ring
        _ ≤ (Real.rpow C1 qn * Real.rpow (k n : ℝ) (1 - qn * beta n))
              * ((c_Sn * qn) ^ qn / T ^ qn) := mul_le_mul_of_nonneg_right hsigonly hCnn
        _ = Real.rpow C1 qn * Real.rpow (k n : ℝ) (1 - qn * beta n)
              * (c_Sn * qn) ^ qn / T ^ qn := by ring
    have hfinal : Real.rpow C1 qn * Real.rpow (k n : ℝ) (1 - qn * beta n)
          * (c_Sn * qn) ^ qn / T ^ qn ≤ C2 * Real.rpow (n : ℝ) (-1) := by
      have hTeq : T = Real.exp 1 * C2 * C3 *
          (Real.rpow (k n : ℝ) (-(beta n)) * Real.log (n : ℝ)) := by
        rw [hT, t1fun]
      rw [hTeq]
      exact statopia_math_node_19064832_302da345 C1 C2 c_Sn C3 qn k beta n
        hC1_ge1 hc_Sn hC2_ge1 hC1cSn hC3_ge8 hk1 hlogpos h7 hq2 hC3q hqlog hbeta_pos hqbeta2 h8
    calc μ (Bevent p X muV Sig tau k piPerm n T) ≤ ∑ j ∈ S, μ (B j) := hunion
      _ ≤ ENNReal.ofReal (∑ j ∈ S,
            Real.rpow (Real.sqrt (Sig n j j)) (qn * (1 - tau n))
              * (c_Sn * qn) ^ qn / T ^ qn) := hsum1
      _ ≤ ENNReal.ofReal (C2 * Real.rpow (n : ℝ) (-1)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          exact le_trans hsigsum hfinal
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hkey
  exact ⟨Real.exp 1 * C2 * C3, hcthr_pos, C2, hC2_pos, max N0 1, le_max_right _ _,
    fun n hn => hN0 n (le_trans (le_max_left _ _) hn)⟩
  /- @proof-region region.target-node.session.3b8d3512c4b82d69 end -/

end

end Statlib.Imported

