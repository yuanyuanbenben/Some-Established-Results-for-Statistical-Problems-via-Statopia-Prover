import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Vocabulary
import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Base
import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.ProvedNodes.Node_592878890_3cc8cbb4_82568dac
import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.ExternalNodes.Node_66fc8f622811466f9f88

namespace PaperProofTasks.job_paper_cb04ce35a04d48a9bf96750470ca0eb0

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
open _root_.PaperProofTasks.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Statlib.Imported

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
namespace Statlib.Imported

noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_1547769943_b198a36d : ∀ (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1 / 2)
    (α : ℝ) (hα : 0 < α)
    (C_sigma : ℝ) (hC_sigma : 0 < C_sigma)
    (c_circ : ℝ) (hc_circ0 : 0 < c_circ) (hc_circ1 : c_circ < 1)
    (ε0 : ℝ) (hε0_0 : 0 < ε0) (hε0_1 : ε0 < 1)
    (C_R : ℝ) (hC_R : 0 < C_R)
    (c_0 : ℝ) (hc_0 : 0 < c_0)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (p : ℕ → ℕ) (hp : ∀ n, 1 ≤ p n)
    (Sig : (n : ℕ) → Matrix (Fin (p n)) (Fin (p n)) ℝ)
    (hSig_psd : ∀ n, (Sig n).PosSemidef)
    (hSig_diag : ∀ (n : ℕ) (j : Fin (p n)), 0 < Sig n j j)
    (π : (n : ℕ) → Equiv.Perm (Fin (p n)))
    (hπ_sorted : ∀ n, Antitone (fun i : Fin (p n) => Real.sqrt (Sig n (π n i) (π n i))))
    (Z : (n : ℕ) → Fin n → Ω → (Fin (p n) → ℝ))
    (μv : (n : ℕ) → Fin (p n) → ℝ)
    (X : (n : ℕ) → Fin n → Ω → (Fin (p n) → ℝ))
    (hX_model : ∀ (n : ℕ) (i : Fin n) (ω : Ω),
      X n i ω = μv n + (Matrix.PosSemidef.sqrt (hSig_psd n)).mulVec (Z n i ω))
    (hX_mean : ∀ (n : ℕ) (i : Fin n) (j : Fin (p n)), ∫ ω, X n i ω j ∂μ = μv n j)
    (hX_mem : ∀ (n : ℕ) (i : Fin n) (j : Fin (p n)), MemLp (fun ω => X n i ω j) 2 μ)
    (hZ_meas : ∀ (n : ℕ) (i : Fin n), Measurable (Z n i))
    (hZ_indep : ∀ n, iIndepFun (Z n) μ)
    (hZ_ident : ∀ (n : ℕ) (i i' : Fin n), IdentDistrib (Z n i) (Z n i') μ μ)
    (hZ_mem : ∀ (n : ℕ) (i : Fin n) (j : Fin (p n)), MemLp (fun ω => Z n i ω j) 2 μ)
    (hZ_mean : ∀ (n : ℕ) (i : Fin n) (j : Fin (p n)), ∫ ω, Z n i ω j ∂μ = 0)
    (hZ_cov : ∀ (n : ℕ) (i : Fin n) (j j' : Fin (p n)),
      ∫ ω, Z n i ω j * Z n i ω j' ∂μ = if j = j' then 1 else 0)
    (hZ_psi : ∀ (n : ℕ) (i : Fin n) (u : Fin (p n) → ℝ),
      (∑ j : Fin (p n), u j ^ 2) = 1 →
      psi1Norm μ (fun ω => ∑ j : Fin (p n), Z n i ω j * u j) ≤ ENNReal.ofReal c_0)
    (L : ℕ → ℕ)
    (hL_def : ∀ n, L n = Nat.ceil (min (max 1 ((Real.log (n : ℝ)) ^ (3 : ℕ))) ((p n : ℝ))))
    (hL_le_p : ∀ n, L n ≤ p n)
    (k : ℕ → ℕ)
    (hk_def : ∀ n, k n = Nat.ceil
      (min (max (L n : ℝ) (Real.rpow (n : ℝ) (1 / Real.rpow (Real.log (n : ℝ)) a)))
        ((p n : ℝ))))
    (τ : ℕ → ℝ) (hτ0 : ∀ n, 0 ≤ τ n) (hτ1 : ∀ n, τ n < 1)
    (β : ℕ → ℝ) (hβ_def : ∀ n, β n = α * (1 - τ n))
    (hτ_cond : LessTilde (fun _ => (1 : ℝ))
      (fun n => (1 - τ n) * Real.sqrt (Real.log (n : ℝ))))
    (hσ_upper : ∀ (n : ℕ) (i : Fin (p n)), k n ≤ (i : ℕ) + 1 →
      Real.sqrt (Sig n (π n i) (π n i)) ≤
        C_sigma * Real.rpow (((i : ℕ) + 1 : ℕ) : ℝ) (-α))
    (hσ_lower : ∀ (n : ℕ) (i : Fin (p n)), (i : ℕ) + 1 ≤ k n →
      c_circ * Real.rpow (((i : ℕ) + 1 : ℕ) : ℝ) (-α) ≤
        Real.sqrt (Sig n (π n i) (π n i)))
    (hR_off : ∀ (n : ℕ) (i j : Fin (L n)), i ≠ j → corrMat p L Sig π hL_le_p n i j ≤ 1 - ε0)
    (hR_psd : ∀ n, (posPartMat (corrMat p L Sig π hL_le_p n)).PosSemidef)
    (hR_sum : ∀ n, ∑ i : Fin (L n), ∑ j : Fin (L n),
      (if i < j then max (corrMat p L Sig π hL_le_p n i j) 0 else 0) ≤ C_R * (L n : ℝ)),
    ∃ c_thr : ℝ, 0 < c_thr ∧ ∃ C₂ : ℝ, 0 < C₂ ∧ ∃ N₂ : ℕ, 1 ≤ N₂ ∧
      ∀ n : ℕ, N₂ ≤ n →
        μ (Bevent p X μv Sig τ k π n (t1fun k β c_thr n)) ≤
          ENNReal.ofReal (C₂ * Real.rpow (n : ℝ) (-1)) := by
  /- @proof-region region.target-node.session.4c5dd3f4c51b93f4 begin -/
  intro delta hdelta0 hdelta1 a ha0 ha1 alpha halpha C_sigma hC_sigma c_circ hc_circ0 hc_circ1 eps0 heps0_pos heps0_lt C_R hC_R c_0 hc_0
    Ω hΩ μ hμ p hp Sig hSig_psd hSig_diag piPerm hpi_sorted Z μv X hX_model hX_mean hX_mem
    hZ_meas hZ_indep hZ_ident hZ_mem hZ_mean hZ_cov hZ_psi L hL_def hL_le_p k hk_def tau htau0 htau1
    beta hbeta_def htau_cond hsigma_upper hsigma_lower hR_off hR_psd hR_sum
  obtain ⟨c_tau, hc_tau, n_tau, hn_tau⟩ := htau_cond
  have hdeg : ∀ (n : ℕ) (t : ℝ), k n = p n → μ (Bevent p X μv Sig tau k piPerm n t) = 0 := by
    intro n t hk
    have hempty : Bevent p X μv Sig tau k piPerm n t = ∅ := by
      ext ω
      constructor
      · rintro ⟨j, hj, _⟩
        rw [hk] at hj
        exact absurd ((piPerm n).symm j).isLt hj
      · intro h
        simp at h
    rw [hempty, measure_empty]
  have hone_sub_tau_pos : ∀ n, 0 < 1 - tau n := fun n => by linarith [htau1 n]
  have hbeta_pos : ∀ n, 0 < beta n := by
    intro n
    rw [hbeta_def]
    exact mul_pos halpha (hone_sub_tau_pos n)
  have hbeta_le : ∀ n, beta n ≤ alpha := by
    intro n
    rw [hbeta_def]
    exact mul_le_of_le_one_right (le_of_lt halpha) (by linarith [htau0 n])
  have hpR_pos : ∀ n, (0 : ℝ) < (p n : ℝ) := fun n => by
    have h : (1 : ℝ) ≤ (p n : ℝ) := by exact_mod_cast hp n
    linarith
  have hL_pos : ∀ n, 1 ≤ L n := by
    intro n
    rw [hL_def n]
    refine Nat.one_le_ceil_iff.mpr ?_
    have h1 : (0 : ℝ) < max 1 ((Real.log (n : ℝ)) ^ (3 : ℕ)) := by
      linarith [le_max_left (1 : ℝ) ((Real.log (n : ℝ)) ^ (3 : ℕ))]
    exact lt_min h1 (hpR_pos n)
  have hk_pos : ∀ n, 1 ≤ k n := by
    intro n
    rw [hk_def n]
    refine Nat.one_le_ceil_iff.mpr ?_
    have hL1 : (1 : ℝ) ≤ (L n : ℝ) := by exact_mod_cast hL_pos n
    have h2 : (0 : ℝ) <
        max (L n : ℝ) (Real.rpow (n : ℝ) (1 / Real.rpow (Real.log (n : ℝ)) a)) := by
      linarith [le_max_left (L n : ℝ) (Real.rpow (n : ℝ) (1 / Real.rpow (Real.log (n : ℝ)) a))]
    exact lt_min h2 (hpR_pos n)
  have hL_le_k : ∀ n, L n ≤ k n := by
    intro n
    have hle : (L n : ℝ) ≤
        min (max (L n : ℝ) (Real.rpow (n : ℝ) (1 / Real.rpow (Real.log (n : ℝ)) a)))
          ((p n : ℝ)) := by
      refine le_min (le_max_left _ _) ?_
      exact_mod_cast hL_le_p n
    have h1 : Nat.ceil (L n : ℝ) ≤ k n := by
      rw [hk_def n]
      exact Nat.ceil_le_ceil hle
    have h2 : L n ≤ Nat.ceil (L n : ℝ) := by
      have h3 := Nat.le_ceil (L n : ℝ)
      exact_mod_cast h3
    linarith
  set qN : ℕ → ℝ := fun n => max (max (2 / beta n) (Real.log (n : ℝ))) 3 with hqN_def
  have hqN_three : ∀ (n : ℕ), 3 ≤ qN n := fun n => le_max_right _ _
  have hqN_two : ∀ (n : ℕ), 2 ≤ qN n := fun n =>
    le_trans (by norm_num : (2 : ℝ) ≤ 3) (hqN_three n)
  have hqN_log : ∀ (n : ℕ), Real.log (n : ℝ) ≤ qN n := fun (n : ℕ) =>
    le_trans (le_max_right (2 / beta n) (Real.log (n : ℝ))) (le_max_left _ _)
  have hqN_two_div : ∀ (n : ℕ), 2 / beta n ≤ qN n := fun (n : ℕ) =>
    le_trans (le_max_left (2 / beta n) (Real.log (n : ℝ))) (le_max_left _ _)
  have hqN_beta : ∀ (n : ℕ), 2 ≤ qN n * beta n := by
    intro n
    have h1 := hqN_two_div n
    have hb := le_of_lt (hbeta_pos n)
    have hne : beta n ≠ 0 := ne_of_gt (hbeta_pos n)
    have h2 : 2 / beta n * beta n = 2 := by
      field_simp
    calc (2 : ℝ) = 2 / beta n * beta n := h2.symm
      _ ≤ qN n * beta n := mul_le_mul_of_nonneg_right h1 hb
  have hunion : ∀ (n : ℕ) (t : ℝ),
      μ (Bevent p X μv Sig tau k piPerm n t) ≤
        ∑ j : Fin (p n), μ {ω | ¬ (((piPerm n).symm j : ℕ) < k n) ∧
          t < Svec p X μv n ω j / Real.rpow (Real.sqrt (Sig n j j)) (tau n)} := by
    intro n t
    have hsub : Bevent p X μv Sig tau k piPerm n t ⊆
        ⋃ j : Fin (p n), {ω : Ω | ¬ (((piPerm n).symm j : ℕ) < k n) ∧
          t < Svec p X μv n ω j / Real.rpow (Real.sqrt (Sig n j j)) (tau n)} := by
      intro ω hω
      obtain ⟨j, hj⟩ := hω
      exact Set.mem_iUnion.mpr ⟨j, hj⟩
    refine le_trans (measure_mono hsub) ?_
    simpa using measure_iUnion_le (fun j : Fin (p n) => {ω : Ω | ¬ (((piPerm n).symm j : ℕ) < k n) ∧
      t < Svec p X μv n ω j / Real.rpow (Real.sqrt (Sig n j j)) (tau n)})
  have htau_growth : ∃ ctau : ℝ, 0 < ctau ∧ ∃ N0 : ℕ, 1 ≤ N0 ∧
      ∀ n : ℕ, N0 ≤ n → (1 : ℝ) ≤ ctau * ((1 - tau n) * Real.sqrt (Real.log (n : ℝ))) :=
    ⟨c_tau, hc_tau, max n_tau 1, le_max_right n_tau 1,
      fun n hn => hn_tau n (le_trans (le_max_left n_tau 1) hn)⟩
  obtain ⟨cSn, hcSn_pos, n0, hn0_ge, hbound⟩ :=
    PaperProofTasks.job_paper_df5fdc450bf24d85b08215e07b20fdad.Statlib.Imported.paper_df5fdc450bf24d85b08215e07b20fdad
      a ha0 ha1 c_0 hc_0 alpha halpha C_sigma hC_sigma c_circ hc_circ0 hc_circ1 eps0 heps0_pos heps0_lt
      C_R hC_R tau htau0 htau1 htau_growth
  have hbound_inst := hbound Ω p hp
  have hX_model' : ∀ (n : ℕ) (i : Fin n) (ω : Ω) (l : Fin (p n)),
      X n i ω l = μv n l + (Matrix.PosSemidef.sqrt (hSig_psd n)).mulVec (Z n i ω) l :=
    fun n i ω l => congrFun (hX_model n i ω) l
  have hZ_mem_vec : ∀ (n : ℕ) (i : Fin n), MemLp (Z n i) 2 μ := by
    intro n i
    rw [MeasureTheory.memLp_pi_iff]
    intro j
    exact hZ_mem n i j
  have hpsi_le : ∀ (ξ : Ω → ℝ),
      sInf (ENNReal.ofReal '' {t : ℝ | 0 < t ∧
        ∫⁻ ω, ENNReal.ofReal (Real.exp (|ξ ω| / t)) ∂μ ≤ 2}) ≤ psi1Norm μ ξ := by
    intro ξ
    refine le_iInf ?_
    intro t
    exact sInf_le ⟨t.1, t.2, rfl⟩
  have hZ_psi' : ∀ (n : ℕ) (i : Fin n) (u : Fin (p n) → ℝ), (∑ l, u l ^ 2) = 1 →
      sInf (ENNReal.ofReal '' {t : ℝ | 0 < t ∧
        ∫⁻ ω, ENNReal.ofReal (Real.exp (|(fun ω : Ω => ∑ l : Fin (p n), u l * Z n i ω l) ω| / t)) ∂μ
          ≤ 2}) ≤ ENNReal.ofReal c_0 := by
    intro n i u hu
    have hξ : (fun ω : Ω => ∑ l : Fin (p n), u l * Z n i ω l)
        = fun ω : Ω => ∑ j : Fin (p n), Z n i ω j * u j := by
      funext ω
      exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
    rw [hξ]
    exact le_trans (hpsi_le _) (hZ_psi n i u hu)
  have hLq : ∀ (n : ℕ), n0 ≤ n → ∀ (q : ℝ), 2 ≤ q → q ≤ Real.sqrt (n : ℝ) →
      ∀ j : Fin (p n),
      ∫⁻ ω, ENNReal.ofReal
          (|(Real.sqrt (Sig n j j))⁻¹ *
            ((Real.sqrt (n : ℝ))⁻¹ * ∑ i : Fin n, (X n i ω j - μv n j))| ^ q) ∂μ
        ≤ ENNReal.ofReal ((cSn * q) ^ q) := by
    intro n hn q hq2 hqn j
    exact hbound_inst μ Sig hSig_psd hSig_diag μv Z X hX_model' hZ_meas hZ_indep hZ_ident
      hZ_mem_vec hZ_mean hZ_cov hZ_psi' n hn q hq2 hqn j
  have hsig_pos : ∀ (n : ℕ) (j : Fin (p n)), 0 < Real.sqrt (Sig n j j) := fun n j =>
    Real.sqrt_pos.mpr (hSig_diag n j)
  have hX_meas : ∀ (n : ℕ) (i : Fin n) (j : Fin (p n)),
      AEMeasurable (fun ω : Ω => X n i ω j) μ :=
    fun n i j => (hX_mem n i j).aestronglyMeasurable.aemeasurable
  exact statopia_math_node_592878890_3cc8cbb4 a ha0 ha1 alpha halpha C_sigma hC_sigma p hp
    Sig hSig_psd hSig_diag piPerm hpi_sorted μv X
    (fun n i j => (hX_mem n i j).aestronglyMeasurable)
    L hL_def hL_le_p k hk_def tau htau0 htau1 beta hbeta_def
    ⟨c_tau, hc_tau, n_tau, hn_tau⟩ hsigma_upper
    cSn hcSn_pos n0 hn0_ge hLq
  /- @proof-region region.target-node.session.4c5dd3f4c51b93f4 end -/

end

end Statlib.Imported

