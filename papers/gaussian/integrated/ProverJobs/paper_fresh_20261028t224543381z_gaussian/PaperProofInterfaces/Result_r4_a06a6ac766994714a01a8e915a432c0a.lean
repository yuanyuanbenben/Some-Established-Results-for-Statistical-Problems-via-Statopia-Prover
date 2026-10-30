import ProverJobs.job_paper_82217ff9ed45452ea25ea7588fe2ef01.ExternalNodes.Node_5af76655ad784a43bbfd
import ProverJobs.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Vocabulary
import ProverJobs.job_paper_82217ff9ed45452ea25ea7588fe2ef01.ProvedNodes
import ProverJobs.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Base

namespace PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
open PaperProofTasks.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Statlib.Imported
namespace Statlib.Imported
open _root_.Statlib
noncomputable section

theorem paper_82217ff9ed45452ea25ea7588fe2ef01
    (a c0 alpha cvar ccirc eps0 Ccor : ℝ)
    (ha : a ∈ Set.Ioo (0 : ℝ) (1 / 2)) (hc0 : 0 < c0) (halpha : 0 < alpha)
    (hcvar : 0 < cvar) (hccirc : ccirc ∈ Set.Ioo (0 : ℝ) 1)
    (heps0 : eps0 ∈ Set.Ioo (0 : ℝ) 1) (hCcor : 0 < Ccor)
    {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) (1 / 2)) :
    ∃ c1 c2 : ℝ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
        (M : Model Ω μ a) (hM : Model.Assumptions M c0 alpha cvar ccirc eps0 Ccor),
        ∃ n0 : ℕ, 1 ≤ n0 ∧
          ∀ n : ℕ, n0 ≤ n →
            M.In n ≤ c1 * (n : ℝ) ^ (-(1 / 2 : ℝ) + δ) ∧
            M.IIIn n ≤ c2 * (n : ℝ) ^ (-(1 / 2 : ℝ) + δ)
:= by
  /- @proof-region region.root.f926de98daaa begin -/
  classical
  have hpow : ∀ n : ℕ, 1 ≤ n → (0 : ℝ) < (n : ℝ) ^ (-(1 / 2 : ℝ) + δ) := by
    intro n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by
      have h1 : (0 : ℕ) < n := lt_of_lt_of_le Nat.zero_lt_one hn
      exact_mod_cast h1
    exact Real.rpow_pos_of_pos hn0 _
  obtain ⟨Ca, hCa, hbound⟩ :=
    _root_.PaperProofTasks.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Statlib.Imported.paper_cb04ce35a04d48a9bf96750470ca0eb0
      δ hδ.1 hδ.2 a ha.1 ha.2 alpha halpha cvar hcvar ccirc hccirc.1 hccirc.2 eps0 heps0.1
      heps0.2 Ccor hCcor c0 hc0
  obtain ⟨CA, hCA, hAboundAll⟩ :=
    statopia_math_node_2151621483_4d3e915f a c0 alpha cvar ccirc eps0 Ccor halpha hccirc heps0
      hCcor hδ
  refine ⟨Ca + 1, CA + 1, by linarith, by linarith, ?_⟩
  intro Ω inst μ instμ M hM
  have hJ_univ : ∀ n : ℕ, M.J n (M.p n) = Finset.univ := by
    intro n
    refine Finset.ext ?_
    intro j
    constructor
    · intro _
      exact Finset.mem_univ j
    · intro _
      refine Finset.mem_image.mpr ⟨(M.g n).symm j, ?_, Equiv.apply_symm_apply (M.g n) j⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((M.g n).symm j).isLt⟩
  have hMd_univ : ∀ n (ω : Ω), M.Md n (M.p n) ω
      = fmax Finset.univ (fun j => M.S n ω j / (M.sigma n j) ^ (M.tau n)) := by
    intro n ω
    have h : M.Md n (M.p n) ω
        = fmax (M.J n (M.p n)) (fun j => M.S n ω j / (M.sigma n j) ^ (M.tau n)) := rfl
    rw [h, hJ_univ n]
  have htildeMd_univ : ∀ n (w : Fin (M.p n) → ℝ), M.tildeMd n (M.p n) w
      = fmax Finset.univ (fun j => w j / (M.sigma n j) ^ (M.tau n)) := by
    intro n w
    have h : M.tildeMd n (M.p n) w
        = fmax (M.J n (M.p n)) (fun j => w j / (M.sigma n j) ^ (M.tau n)) := rfl
    rw [h, hJ_univ n]
  have hX_mean : ∀ (n : ℕ) (i : Fin n) (j : Fin (M.p n)), ∫ ω, M.X n i ω j ∂μ = M.mu n j := by
    intro n i j
    have hpt : ∀ ω : Ω, M.X n i ω j
        = M.mu n j + ∑ l : Fin (M.p n),
            (Matrix.PosSemidef.sqrt (M.hSigma n)) j l * M.Z n i ω l := by
      intro ω
      rw [M.hmodel n i ω]
      rfl
    calc ∫ ω, M.X n i ω j ∂μ
        = ∫ ω, (M.mu n j + ∑ l : Fin (M.p n),
            (Matrix.PosSemidef.sqrt (M.hSigma n)) j l * M.Z n i ω l) ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = M.mu n j + ∫ ω, ∑ l : Fin (M.p n),
            (Matrix.PosSemidef.sqrt (M.hSigma n)) j l * M.Z n i ω l ∂μ := by
          rw [integral_add (integrable_const _)
            (integrable_finset_sum Finset.univ
              (fun l _ => (M.hZ_int n i l).const_mul _)), integral_const]
          simp
      _ = M.mu n j + ∑ l : Fin (M.p n), ∫ ω,
            (Matrix.PosSemidef.sqrt (M.hSigma n)) j l * M.Z n i ω l ∂μ := by
          rw [integral_finset_sum Finset.univ (fun l _ => (M.hZ_int n i l).const_mul _)]
      _ = M.mu n j + ∑ l : Fin (M.p n), (Matrix.PosSemidef.sqrt (M.hSigma n)) j l * 0 := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro l _
          rw [integral_const_mul, M.hZ_mean n i l]
      _ = M.mu n j := by simp
  obtain ⟨NA, hNA1, hAbound⟩ := hAboundAll M hM
  set c_thr : ℝ := 1 with hc_thr_def
  have hc_thr : 0 < c_thr := by rw [hc_thr_def]; exact one_pos
  obtain ⟨NB, hNB1, hBbound⟩ :=
    statopia_math_node_1110936471_39467c22 a c0 alpha cvar ccirc eps0 Ccor ha halpha M hM c_thr
      hc_thr
  obtain ⟨Nthr, hNthr⟩ :=
    statopia_math_node_70832348_d8d3cb27 a c0 alpha cvar ccirc eps0 Ccor c_thr M
      ha hc0 halpha hcvar hccirc heps0 hCcor hc_thr hM
  have hdK_comm : ∀ (P Q : Measure ℝ), dK P Q = dK Q P := by
    intro P Q
    show sSup (Set.range fun t : ℝ =>
        |(P (Set.Iic t)).toReal - (Q (Set.Iic t)).toReal|)
      = sSup (Set.range fun t : ℝ =>
        |(Q (Set.Iic t)).toReal - (P (Set.Iic t)).toReal|)
    rw [show (fun t : ℝ => |(P (Set.Iic t)).toReal - (Q (Set.Iic t)).toReal|)
        = (fun t : ℝ => |(Q (Set.Iic t)).toReal - (P (Set.Iic t)).toReal|) from by
      funext t
      exact abs_sub_comm _ _]
  have hone_ell_gen : ∀ n : ℕ, 1 ≤ M.ell n := by
    intro n
    have h1 : (1 : ℝ) ≤ min (max (1 : ℝ) ((Real.log (n : ℝ)) ^ 3)) (M.p n : ℝ) :=
      le_min (le_max_left _ _) (by exact_mod_cast M.hp n)
    have h2 : (1 : ℝ) ≤ ((M.ell n : ℕ) : ℝ) :=
      le_trans h1 (Nat.le_ceil (min (max (1 : ℝ) ((Real.log (n : ℝ)) ^ 3)) (M.p n : ℝ)))
    exact_mod_cast h2
  have hone_k_gen : ∀ n : ℕ, 1 ≤ M.kIdx n := by
    intro n
    have h1 : (1 : ℝ) ≤ min (max (M.ell n : ℝ)
        ((n : ℝ) ^ (1 / ((Real.log (n : ℝ)) ^ a)))) (M.p n : ℝ) :=
      le_min (le_trans (by exact_mod_cast hone_ell_gen n) (le_max_left _ _))
        (by exact_mod_cast M.hp n)
    have h2 : (1 : ℝ) ≤ ((M.kIdx n : ℕ) : ℝ) :=
      le_trans h1 (Nat.le_ceil (min (max (M.ell n : ℝ)
        ((n : ℝ) ^ (1 / ((Real.log (n : ℝ)) ^ a)))) (M.p n : ℝ)))
    exact_mod_cast h2
  have hp0_gen : ∀ n : ℕ, 0 < M.p n := fun n => lt_of_lt_of_le Nat.zero_lt_one (M.hp n)
  have hJ0_gen : ∀ n : ℕ, (M.J n (M.kIdx n)).Nonempty := by
    intro n
    refine ⟨M.g n ⟨0, hp0_gen n⟩, Finset.mem_image.mpr ⟨⟨0, hp0_gen n⟩, ?_, rfl⟩⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      lt_of_lt_of_le Nat.zero_lt_one (hone_k_gen n)⟩
  have hJdiff_gen : ∀ n : ℕ, M.kIdx n < M.p n →
      (Finset.univ \ M.J n (M.kIdx n)).Nonempty := by
    intro n hlt
    refine ⟨M.g n ⟨M.kIdx n, hlt⟩, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    intro hmem
    obtain ⟨i, hi, hgi⟩ := Finset.mem_image.mp hmem
    have hik : (i : ℕ) < M.kIdx n := (Finset.mem_filter.mp hi).2
    have hieq : i = ⟨M.kIdx n, hlt⟩ := (M.g n).injective hgi
    rw [hieq] at hik
    simp only [Fin.val_mk] at hik
    exact absurd hik (Nat.lt_irrefl (M.kIdx n))
  have hS_meas : ∀ (n : ℕ) (j : Fin (M.p n)), Measurable (fun ω => M.S n ω j) := by
    intro n j
    have h : (fun ω => M.S n ω j) = fun ω =>
        (Real.sqrt (n : ℝ))⁻¹ * ∑ i : Fin n, (M.X n i ω j - ∫ ω', M.X n i ω' j ∂μ) := rfl
    rw [h]
    exact (measurable_const : Measurable (fun _ : Ω => (Real.sqrt (n : ℝ))⁻¹)).mul
      (Finset.measurable_sum _ (fun i _ =>
        ((measurable_pi_apply j).comp (M.hX n i)).sub measurable_const))
  
  have hIIIn : ∃ c2 : ℝ, c2 = CA + 1 ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → M.IIIn n ≤ (CA + 1) * (n : ℝ) ^ (-(1 / 2 : ℝ) + δ) := by
    refine ⟨CA + 1, rfl, max (max NA NB) (max Nthr 1), ?_, ?_⟩
    · exact le_trans (le_max_right Nthr 1) (le_max_right _ _)
    · intro n hn
      have hn1 : 1 ≤ n := le_trans (le_trans (le_max_right Nthr 1) (le_max_right _ _)) hn
      have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn1
      have hpw : (0 : ℝ) < (n : ℝ) ^ (-(1 / 2 : ℝ) + δ) := hpow n hn1
      have hpos : (0 : ℝ) < CA + 1 := by linarith
      by_cases hcase : M.p n ≤ M.kIdx n
      · obtain ⟨hIn0, hIII0⟩ :=
          statopia_math_node_762516508_6fca4911 a c0 alpha cvar ccirc eps0 Ccor M hM n hcase
        rw [hIII0]
        exact mul_nonneg hpos.le hpw.le
      · have hlt : M.kIdx n < M.p n := lt_of_not_ge hcase
        have hone_ell : 1 ≤ M.ell n := by
          have h1 : (1 : ℝ) ≤ min (max (1 : ℝ) ((Real.log (n : ℝ)) ^ 3)) (M.p n : ℝ) :=
            le_min (le_max_left _ _) (by exact_mod_cast M.hp n)
          have h2 : (1 : ℝ) ≤ ((M.ell n : ℕ) : ℝ) :=
            le_trans h1 (Nat.le_ceil (min (max (1 : ℝ) ((Real.log (n : ℝ)) ^ 3)) (M.p n : ℝ)))
          exact_mod_cast h2
        have hone_k : 1 ≤ M.kIdx n := by
          have h1 : (1 : ℝ) ≤ min (max (M.ell n : ℝ)
              ((n : ℝ) ^ (1 / ((Real.log (n : ℝ)) ^ a)))) (M.p n : ℝ) :=
            le_min (le_trans (by exact_mod_cast hone_ell) (le_max_left _ _))
              (by exact_mod_cast M.hp n)
          have h2 : (1 : ℝ) ≤ ((M.kIdx n : ℕ) : ℝ) :=
            le_trans h1 (Nat.le_ceil (min (max (M.ell n : ℝ)
              ((n : ℝ) ^ (1 / ((Real.log (n : ℝ)) ^ a)))) (M.p n : ℝ)))
          exact_mod_cast h2
        have hp0 : 0 < M.p n := lt_of_lt_of_le Nat.zero_lt_one (M.hp n)
        have hJ0 : (M.J n (M.kIdx n)).Nonempty := by
          refine ⟨M.g n ⟨0, hp0⟩, Finset.mem_image.mpr ⟨⟨0, hp0⟩, ?_, rfl⟩⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            lt_of_lt_of_le Nat.zero_lt_one hone_k⟩
        have hJ0c : (Finset.univ \ M.J n (M.kIdx n)).Nonempty := by
          refine ⟨M.g n ⟨M.kIdx n, hlt⟩, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩⟩
          intro hmem
          obtain ⟨i, hi, hgi⟩ := Finset.mem_image.mp hmem
          have hik : (i : ℕ) < M.kIdx n := (Finset.mem_filter.mp hi).2
          have hieq : i = ⟨M.kIdx n, hlt⟩ := (M.g n).injective hgi
          rw [hieq] at hik
          simp only [Fin.val_mk] at hik
          exact absurd hik (Nat.lt_irrefl (M.kIdx n))
        have hmapmeas : Measurable (fun w : Fin (M.p n) → ℝ =>
            Matrix.mulVec (Matrix.PosSemidef.sqrt (M.hSigma n)) w) := by
          refine measurable_pi_iff.mpr (fun i => ?_)
          have h2 : (fun w : Fin (M.p n) → ℝ =>
              Matrix.mulVec (Matrix.PosSemidef.sqrt (M.hSigma n)) w i)
              = fun w => ∑ j, (Matrix.PosSemidef.sqrt (M.hSigma n)) i j * w j := rfl
          rw [h2]
          exact Finset.measurable_sum _ (fun j _ =>
            (measurable_const : Measurable (fun _ : Fin (M.p n) → ℝ =>
              (Matrix.PosSemidef.sqrt (M.hSigma n)) i j)).mul (measurable_pi_apply j))
        haveI hprob : IsProbabilityMeasure (M.tildeLaw n) := by
          refine ⟨? _⟩
          show ((Model.stdGauss (M.p n)).map (fun w : Fin (M.p n) → ℝ =>
            Matrix.mulVec (Matrix.PosSemidef.sqrt (M.hSigma n)) w)) Set.univ = 1
          rw [Measure.map_apply hmapmeas MeasurableSet.univ]
          simp [Model.stdGauss]
        have hNAle : NA ≤ n := le_trans (le_trans (le_max_left NA NB) (le_max_left _ _)) hn
        have hNBle : NB ≤ n := le_trans (le_trans (le_max_right NA NB) (le_max_left _ _)) hn
        have hNthrle : Nthr ≤ n := le_trans (le_trans (le_max_left Nthr 1) (le_max_right _ _)) hn
        have ht : c_thr * (M.kIdx n : ℝ) ^ (-(alpha * (1 - M.tau n))) * Real.log (n : ℝ)
            ≤ ccirc * ((M.ell n : ℝ) ^ (-(alpha * (1 - M.tau n)))) *
                Real.sqrt (Real.log (M.ell n : ℝ)) := hNthr n hNthrle hlt
        have hcmp :=
          statopia_math_node_4287235009_e1acef55 (P := M.tildeLaw n) (M.p n) (M.hp n)
            (M.J n (M.kIdx n)) hJ0 hJ0c (fun w : Fin (M.p n) → ℝ => w)
            (fun j => measurable_pi_apply j) (M.sigma n) (fun j => hM.hsig_pos n hnpos j)
            (M.tau n)
            (c_thr * (M.kIdx n : ℝ) ^ (-(alpha * (1 - M.tau n))) * Real.log (n : ℝ))
            (ccirc * ((M.ell n : ℝ) ^ (-(alpha * (1 - M.tau n)))) *
              Real.sqrt (Real.log (M.ell n : ℝ)))
            ht
        have hA : ((M.tildeLaw n) {w : Fin (M.p n) → ℝ |
              fmax (M.J n (M.kIdx n)) (fun j => w j / (M.sigma n j) ^ (M.tau n))
                ≤ ccirc * ((M.ell n : ℝ) ^ (-(alpha * (1 - M.tau n)))) *
                    Real.sqrt (Real.log (M.ell n : ℝ))}).toReal
            ≤ CA * (n : ℝ) ^ (-(1 / 2 : ℝ) + δ) := by
          have h := hAbound n hNAle hlt
          calc ((M.tildeLaw n) {w : Fin (M.p n) → ℝ |
                fmax (M.J n (M.kIdx n)) (fun j => w j / (M.sigma n j) ^ (M.tau n))
                  ≤ ccirc * ((M.ell n : ℝ) ^ (-(alpha * (1 - M.tau n)))) *
                      Real.sqrt (Real.log (M.ell n : ℝ))}).toReal
              ≤ (ENNReal.ofReal (CA * (n : ℝ) ^ (-(1 / 2 : ℝ) + δ))).toReal :=
                ENNReal.toReal_mono ENNReal.ofReal_ne_top h
            _ = CA * (n : ℝ) ^ (-(1 / 2 : ℝ) + δ) :=
                ENNReal.toReal_ofReal (le_of_lt (mul_pos hCA (hpow n hn1)))
        have hB : ((M.tildeLaw n) {w : Fin (M.p n) → ℝ |
              fmax (Finset.univ \ M.J n (M.kIdx n))
                  (fun j => w j / (M.sigma n j) ^ (M.tau n))
                > c_thr * (M.kIdx n : ℝ) ^ (-(alpha * (1 - M.tau n))) * Real.log (n : ℝ)}).toReal
            ≤ (n : ℝ) ^ (-1 : ℤ) := by
          have h := hBbound n hNBle hlt
          calc ((M.tildeLaw n) {w : Fin (M.p n) → ℝ |
                fmax (Finset.univ \ M.J n (M.kIdx n))
                    (fun j => w j / (M.sigma n j) ^ (M.tau n))
                  > c_thr * (M.kIdx n : ℝ) ^ (-(alpha * (1 - M.tau n))) * Real.log (n : ℝ)}).toReal
              ≤ (ENNReal.ofReal ((n : ℝ) ^ (-1 : ℤ))).toReal :=
                ENNReal.toReal_mono ENNReal.ofReal_ne_top h
            _ = (n : ℝ) ^ (-1 : ℤ) :=
                ENNReal.toReal_ofReal (zpow_nonneg (by exact_mod_cast Nat.zero_le n : (0:ℝ) ≤ (n:ℝ)) (-1))
        have hzpow : (n : ℝ) ^ (-1 : ℤ) ≤ (n : ℝ) ^ (-(1 / 2 : ℝ) + δ) := by
          have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
          rw [← Real.rpow_intCast]
          exact Real.rpow_le_rpow_of_exponent_le hnR (by push_cast; linarith [hδ.1])
        have hmap : (M.tildeLaw n).map (fun w : Fin (M.p n) → ℝ => M.tildeMd n (M.p n) w)
            = (M.tildeLaw n).map (fun w : Fin (M.p n) → ℝ =>
                fmax Finset.univ (fun j => w j / (M.sigma n j) ^ (M.tau n))) := by
          congr 1
          funext w
          exact htildeMd_univ n w
        have hmap2 : (M.tildeLaw n).map (fun w : Fin (M.p n) → ℝ => M.tildeMd n (M.kIdx n) w)
            = (M.tildeLaw n).map (fun w : Fin (M.p n) → ℝ =>
                fmax (M.J n (M.kIdx n)) (fun j => w j / (M.sigma n j) ^ (M.tau n))) := rfl
        show dK ((M.tildeLaw n).map (fun w : Fin (M.p n) → ℝ => M.tildeMd n (M.kIdx n) w))
            ((M.tildeLaw n).map (fun w : Fin (M.p n) → ℝ => M.tildeMd n (M.p n) w))
          ≤ (CA + 1) * (n : ℝ) ^ (-(1 / 2 : ℝ) + δ)
        rw [hdK_comm, hmap, hmap2]
        calc dK ((M.tildeLaw n).map (fun w : Fin (M.p n) → ℝ =>
                fmax Finset.univ (fun j => w j / (M.sigma n j) ^ (M.tau n))))
              ((M.tildeLaw n).map (fun w : Fin (M.p n) → ℝ =>
                fmax (M.J n (M.kIdx n)) (fun j => w j / (M.sigma n j) ^ (M.tau n))))
            ≤ ((M.tildeLaw n) {w : Fin (M.p n) → ℝ |
                  fmax (M.J n (M.kIdx n)) (fun j => w j / (M.sigma n j) ^ (M.tau n))
                    ≤ ccirc * ((M.ell n : ℝ) ^ (-(alpha * (1 - M.tau n)))) *
                        Real.sqrt (Real.log (M.ell n : ℝ))}).toReal
              + ((M.tildeLaw n) {w : Fin (M.p n) → ℝ |
                  fmax (Finset.univ \ M.J n (M.kIdx n))
                      (fun j => w j / (M.sigma n j) ^ (M.tau n))
                    > c_thr * (M.kIdx n : ℝ) ^ (-(alpha * (1 - M.tau n))) *
                        Real.log (n : ℝ)}).toReal :=
              hcmp
          _ ≤ CA * (n : ℝ) ^ (-(1 / 2 : ℝ) + δ) + (n : ℝ) ^ (-1 : ℤ) := add_le_add hA hB
          _ ≤ CA * (n : ℝ) ^ (-(1 / 2 : ℝ) + δ) + (n : ℝ) ^ (-(1 / 2 : ℝ) + δ) := by linarith
          _ = (CA + 1) * (n : ℝ) ^ (-(1 / 2 : ℝ) + δ) := by ring
  
  let SigB : (n : ℕ) → Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ :=
    fun n => @Nat.rec (fun m => Matrix (Fin (M.p m)) (Fin (M.p m)) ℝ)
      (Matrix.diagonal (fun j : Fin (M.p 0) =>
        (cvar * ((((M.g 0).symm j : ℕ) : ℝ) + 1) ^ (-alpha)) ^ 2))
      (fun k _ => M.Sigma (k + 1)) n
  let hSigB : ∀ n, (SigB n).PosSemidef :=
    fun n => @Nat.rec (fun m => (SigB m).PosSemidef)
      (Matrix.PosSemidef.diagonal (fun j : Fin (M.p 0) =>
        sq_nonneg (cvar * ((((M.g 0).symm j : ℕ) : ℝ) + 1) ^ (-alpha))))
      (fun k _ => M.hSigma (k + 1)) n
  have hb := hbound M.p M.hp SigB hSigB (fun n j => by
    cases n with
    | zero =>
      have hd : (0 : ℝ) < cvar * ((((M.g 0).symm j : ℕ) : ℝ) + 1) ^ (-alpha) :=
        mul_pos hcvar (Real.rpow_pos_of_pos (by positivity) _)
      simpa [SigB, Matrix.diagonal] using pow_pos hd 2
    | succ k =>
      have hn1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
      have h := (statopia_math_node_3076116109_992c70da a c0 alpha cvar ccirc eps0 Ccor M hM
        (k + 1) hn1 j j j).2.2
      show (0 : ℝ) < M.Sigma (k + 1) j j
      rw [← h]
      exact pow_pos (hM.hsig_pos (k + 1) (Nat.succ_pos k) j) 2) M.g (fun n => by
    cases n with
    | zero =>
      intro i i' hii
      have key : ∀ i : Fin (M.p 0), Real.sqrt (SigB 0 (M.g 0 i) (M.g 0 i))
          = cvar * (((i : ℕ) : ℝ) + 1) ^ (-alpha) := by
        intro i
        have hsymm : (M.g 0).symm (M.g 0 i) = i := Equiv.symm_apply_apply (M.g 0) i
        have hval : SigB 0 (M.g 0 i) (M.g 0 i)
            = (cvar * (((i : ℕ) : ℝ) + 1) ^ (-alpha)) ^ 2 := by
          simp [SigB, Matrix.diagonal, hsymm]
        rw [hval]
        exact Real.sqrt_sq (le_of_lt (mul_pos hcvar (Real.rpow_pos_of_pos (by positivity) _)))
      show Real.sqrt (SigB 0 (M.g 0 i') (M.g 0 i')) ≤ Real.sqrt (SigB 0 (M.g 0 i) (M.g 0 i))
      rw [key i', key i]
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hcvar)
      exact Real.rpow_le_rpow_of_nonpos (by positivity)
        (by
          have hle : ((i : ℕ) : ℝ) ≤ ((i' : ℕ) : ℝ) := by exact_mod_cast hii
          linarith) (neg_nonpos.mpr halpha.le)
    | succ k =>
      intro i i' hii
      have hn0 : 0 < k + 1 := Nat.succ_pos k
      have hn1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
      have hsq : ∀ j : Fin (M.p (k + 1)),
          M.Sigma (k + 1) j j = (M.sigma (k + 1) j) ^ 2 := fun j =>
        ((statopia_math_node_3076116109_992c70da a c0 alpha cvar ccirc eps0 Ccor M hM
          (k + 1) hn1 j j j).2.2).symm
      have h1 : Real.sqrt (M.Sigma (k + 1) (M.g (k + 1) i') (M.g (k + 1) i'))
          = M.sigma (k + 1) (M.g (k + 1) i') := by
        rw [hsq (M.g (k + 1) i')]
        exact Real.sqrt_sq (le_of_lt (hM.hsig_pos (k + 1) hn0 _))
      have h2 : Real.sqrt (M.Sigma (k + 1) (M.g (k + 1) i) (M.g (k + 1) i))
          = M.sigma (k + 1) (M.g (k + 1) i) := by
        rw [hsq (M.g (k + 1) i)]
        exact Real.sqrt_sq (le_of_lt (hM.hsig_pos (k + 1) hn0 _))
      show Real.sqrt (M.Sigma (k + 1) (M.g (k + 1) i') (M.g (k + 1) i'))
        ≤ Real.sqrt (M.Sigma (k + 1) (M.g (k + 1) i) (M.g (k + 1) i))
      rw [h1, h2]
      exact hM.hg_sorted (k + 1) i i' hii)
    M.Z M.mu M.X (fun n i ω => by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.pos_iff_ne_zero.mp (Nat.lt_of_le_of_lt (Nat.zero_le (i : ℕ)) i.isLt))
      exact M.hmodel (k + 1) i ω) hX_mean M.hX_memLp M.hZ M.hindep M.hident
    (fun n i j => by
      have hmeas : Measurable (fun ω => M.Z n i ω j) := (measurable_pi_apply j).comp (M.hZ n i)
      exact (MeasureTheory.memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).mpr (by
      simpa [pow_two] using M.hZ_cov_int n i j j)) M.hZ_mean M.hZ_cov (fun n i u hu => by
        have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le (i : ℕ)) i.isLt
        obtain ⟨t, ht_pos, ht_le, ht_int, ht_bd⟩ := hM.hpsi n hnpos u hu
        have hΦ : Measurable (fun v : Fin (M.p n) → ℝ =>
            ENNReal.ofReal (Real.exp (|∑ j : Fin (M.p n), u j * v j| / t))) := by
          refine ENNReal.measurable_ofReal.comp ?_
          have hlin : Measurable (fun v : Fin (M.p n) → ℝ =>
              ∑ j : Fin (M.p n), u j * v j) :=
            Finset.measurable_sum _ (fun j _ =>
              (measurable_const : Measurable (fun _ : Fin (M.p n) → ℝ => u j)).mul
                (measurable_pi_apply j))
          exact Real.measurable_exp.comp (hlin.abs.div
            (measurable_const : Measurable (fun _ : Fin (M.p n) → ℝ => t)))
        have h0 : ∫⁻ ω, ENNReal.ofReal
              (Real.exp (|∑ j : Fin (M.p n), u j * M.Z n ⟨0, hnpos⟩ ω j| / t)) ∂μ ≤ 2 := by
          rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal ht_int
            (Filter.Eventually.of_forall (fun ω => (Real.exp_pos _).le))]
          calc ENNReal.ofReal (∫ ω, Real.exp
                (|∑ j : Fin (M.p n), u j * M.Z n ⟨0, hnpos⟩ ω j| / t) ∂μ)
              ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal ht_bd
            _ = 2 := by simp
        have h1 : ∫⁻ ω, ENNReal.ofReal
              (Real.exp (|∑ j : Fin (M.p n), u j * M.Z n i ω j| / t)) ∂μ
            = ∫⁻ ω, ENNReal.ofReal
              (Real.exp (|∑ j : Fin (M.p n), u j * M.Z n ⟨0, hnpos⟩ ω j| / t)) ∂μ :=
          ((M.hident n i ⟨0, hnpos⟩).comp hΦ).lintegral_eq
        have hFeq : (fun ω : Ω =>
              ENNReal.ofReal (Real.exp (|∑ j : Fin (M.p n), M.Z n i ω j * u j| / t)))
            = fun ω => ENNReal.ofReal
              (Real.exp (|∑ j : Fin (M.p n), u j * M.Z n i ω j| / t)) := by
          funext ω
          rw [Finset.sum_congr rfl (fun j _ => mul_comm (M.Z n i ω j) (u j))]
        have hadm : ∫⁻ ω, ENNReal.ofReal
              (Real.exp (|∑ j : Fin (M.p n), M.Z n i ω j * u j| / t)) ∂μ ≤ 2 := by
          rw [hFeq, h1]
          exact h0
        exact le_trans (ciInf_le ⟨⊥, fun _ _ => bot_le⟩ ⟨t, ht_pos, hadm⟩)
          (ENNReal.ofReal_le_ofReal ht_le))
    M.ell (fun n => rfl) M.ell_le_p M.kIdx (fun n => rfl) M.tau
    (fun n => (hM.htau_mem n).1) (fun n => (hM.htau_mem n).2) (fun n => alpha * (1 - M.tau n))
    (fun n => rfl) (by
      obtain ⟨ct, hct, hev⟩ := hM.htau_cond
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
      refine ⟨ct⁻¹, inv_pos.mpr hct, N, ?_⟩
      intro n hn
      have h1 : ct ≤ (1 - M.tau n) * Real.sqrt (Real.log (n : ℝ)) := hN n hn
      have h2 : ct⁻¹ * ct ≤ ct⁻¹ * ((1 - M.tau n) * Real.sqrt (Real.log (n : ℝ))) :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt (inv_pos.mpr hct))
      rw [inv_mul_cancel₀ (ne_of_gt hct)] at h2
      exact h2)
    (fun n i hi => by
      cases n with
      | zero =>
        have hkey : Real.sqrt (SigB 0 (M.g 0 i) (M.g 0 i))
            = cvar * (((i : ℕ) : ℝ) + 1) ^ (-alpha) := by
          have hsymm : (M.g 0).symm (M.g 0 i) = i := Equiv.symm_apply_apply (M.g 0) i
          have hval : SigB 0 (M.g 0 i) (M.g 0 i)
              = (cvar * (((i : ℕ) : ℝ) + 1) ^ (-alpha)) ^ 2 := by
            simp [SigB, Matrix.diagonal, hsymm]
          rw [hval]
          exact Real.sqrt_sq (le_of_lt (mul_pos hcvar (Real.rpow_pos_of_pos (by positivity) _)))
        have hcast : (((i : ℕ) + 1 : ℕ) : ℝ) = ((i : ℕ) : ℝ) + 1 := by
          rw [Nat.cast_add, Nat.cast_one]
        rw [hkey, hcast]
        exact le_rfl
      | succ k =>
        have hn0 : 0 < k + 1 := Nat.succ_pos k
        have hn1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
        have hsq : M.Sigma (k + 1) (M.g (k + 1) i) (M.g (k + 1) i)
            = (M.sigma (k + 1) (M.g (k + 1) i)) ^ 2 :=
          ((statopia_math_node_3076116109_992c70da a c0 alpha cvar ccirc eps0 Ccor M hM
            (k + 1) hn1 (M.g (k + 1) i) (M.g (k + 1) i) (M.g (k + 1) i)).2.2).symm
        have h1 : Real.sqrt (SigB (k + 1) (M.g (k + 1) i) (M.g (k + 1) i))
            = M.sigma (k + 1) (M.g (k + 1) i) := by
          show Real.sqrt (M.Sigma (k + 1) (M.g (k + 1) i) (M.g (k + 1) i)) = _
          rw [hsq]
          exact Real.sqrt_sq (le_of_lt (hM.hsig_pos (k + 1) hn0 _))
        rw [h1]
        exact hM.hsig_upper (k + 1) hn0 i hi)
    (fun n i hi => by
      cases n with
      | zero =>
        have hkey : Real.sqrt (SigB 0 (M.g 0 i) (M.g 0 i))
            = cvar * (((i : ℕ) : ℝ) + 1) ^ (-alpha) := by
          have hsymm : (M.g 0).symm (M.g 0 i) = i := Equiv.symm_apply_apply (M.g 0) i
          have hval : SigB 0 (M.g 0 i) (M.g 0 i)
              = (cvar * (((i : ℕ) : ℝ) + 1) ^ (-alpha)) ^ 2 := by
            simp [SigB, Matrix.diagonal, hsymm]
          rw [hval]
          exact Real.sqrt_sq (le_of_lt (mul_pos hcvar (Real.rpow_pos_of_pos (by positivity) _)))
        have hcast : (((i : ℕ) + 1 : ℕ) : ℝ) = ((i : ℕ) : ℝ) + 1 := by
          rw [Nat.cast_add, Nat.cast_one]
        have hcc : ccirc ≤ cvar := by
          have hk1 : 1 ≤ M.kIdx 1 := hone_k_gen 1
          have hkp : M.kIdx 1 ≤ M.p 1 := M.kIdx_le_p 1
          have hlt1 : M.kIdx 1 - 1 < M.p 1 := by omega
          have hlow := hM.hsig_lower 1 (by norm_num) (⟨M.kIdx 1 - 1, hlt1⟩ : Fin (M.p 1))
            (le_of_eq (Nat.sub_add_cancel hk1))
          have hup := hM.hsig_upper 1 (by norm_num) (⟨M.kIdx 1 - 1, hlt1⟩ : Fin (M.p 1))
            (le_of_eq (Nat.sub_add_cancel hk1).symm)
          have hpos : (0 : ℝ) < (((M.kIdx 1 - 1 : ℕ) + 1 : ℕ) : ℝ) ^ (-alpha) :=
            Real.rpow_pos_of_pos (by exact_mod_cast Nat.succ_pos (M.kIdx 1 - 1)) _
          exact le_of_mul_le_mul_right (le_trans hlow hup) hpos
        rw [hkey, hcast]
        exact mul_le_mul_of_nonneg_right hcc
          (le_of_lt (Real.rpow_pos_of_pos (by positivity) _))
      | succ k =>
        have hn0 : 0 < k + 1 := Nat.succ_pos k
        have hn1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
        have hsq : M.Sigma (k + 1) (M.g (k + 1) i) (M.g (k + 1) i)
            = (M.sigma (k + 1) (M.g (k + 1) i)) ^ 2 :=
          ((statopia_math_node_3076116109_992c70da a c0 alpha cvar ccirc eps0 Ccor M hM
            (k + 1) hn1 (M.g (k + 1) i) (M.g (k + 1) i) (M.g (k + 1) i)).2.2).symm
        have h1 : Real.sqrt (SigB (k + 1) (M.g (k + 1) i) (M.g (k + 1) i))
            = M.sigma (k + 1) (M.g (k + 1) i) := by
          show Real.sqrt (M.Sigma (k + 1) (M.g (k + 1) i) (M.g (k + 1) i)) = _
          rw [hsq]
          exact Real.sqrt_sq (le_of_lt (hM.hsig_pos (k + 1) hn0 _))
        rw [h1]
        exact hM.hsig_lower (k + 1) hn0 i hi)
    (fun n i j hij => by
      cases n with
      | zero =>
        have hell0 : M.ell 0 ≤ 1 := by
          refine Nat.ceil_le.mpr ?_
          refine le_trans (min_le_left _ _) ?_
          have hlog : Real.log ((0 : ℕ) : ℝ) = 0 := by
            rw [show ((0 : ℕ) : ℝ) = (0 : ℝ) by norm_num, Real.log_zero]
          rw [hlog]
          norm_num
        have hi := i.isLt
        have hj := j.isLt
        exact absurd (Fin.ext (by omega)) hij
      | succ k =>
        have hn0 : 0 < k + 1 := Nat.succ_pos k
        have hn1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
        let A : Fin (M.p (k + 1)) := M.g (k + 1) (Fin.castLE (M.ell_le_p (k + 1)) i)
        let B : Fin (M.p (k + 1)) := M.g (k + 1) (Fin.castLE (M.ell_le_p (k + 1)) j)
        show M.Sigma (k + 1) A B /
            (Real.sqrt (M.Sigma (k + 1) A A) * Real.sqrt (M.Sigma (k + 1) B B)) ≤ 1 - eps0
        have hcov : M.covX (k + 1) A B = M.Sigma (k + 1) A B :=
          (statopia_math_node_3076116109_992c70da a c0 alpha cvar ccirc eps0 Ccor M hM
            (k + 1) hn1 A B A).1
        have hsqA : (M.sigma (k + 1) A) ^ 2 = M.Sigma (k + 1) A A :=
          (statopia_math_node_3076116109_992c70da a c0 alpha cvar ccirc eps0 Ccor M hM
            (k + 1) hn1 A A A).2.2
        have hsqB : (M.sigma (k + 1) B) ^ 2 = M.Sigma (k + 1) B B :=
          (statopia_math_node_3076116109_992c70da a c0 alpha cvar ccirc eps0 Ccor M hM
            (k + 1) hn1 B B B).2.2
        have hsigA : Real.sqrt (M.Sigma (k + 1) A A) = M.sigma (k + 1) A := by
          rw [← hsqA]
          exact Real.sqrt_sq (le_of_lt (hM.hsig_pos (k + 1) hn0 A))
        have hsigB : Real.sqrt (M.Sigma (k + 1) B B) = M.sigma (k + 1) B := by
          rw [← hsqB]
          exact Real.sqrt_sq (le_of_lt (hM.hsig_pos (k + 1) hn0 B))
        have hentry : M.Sigma (k + 1) A B /
              (Real.sqrt (M.Sigma (k + 1) A A) * Real.sqrt (M.Sigma (k + 1) B B))
            = M.corrEntry (k + 1) A B := by
          show M.Sigma (k + 1) A B /
              (Real.sqrt (M.Sigma (k + 1) A A) * Real.sqrt (M.Sigma (k + 1) B B))
            = M.covX (k + 1) A B / (M.sigma (k + 1) A * M.sigma (k + 1) B)
          rw [hcov, hsigA, hsigB]
        rw [hentry]
        have hne : Fin.castLE (M.ell_le_p (k + 1)) i ≠ Fin.castLE (M.ell_le_p (k + 1)) j := by
          intro hh
          exact hij (Fin.ext (by
            have h2 := congrArg Fin.val hh
            simpa using h2))
        exact hM.hcorr_max (k + 1) (Fin.castLE (M.ell_le_p (k + 1)) i)
          (Fin.castLE (M.ell_le_p (k + 1)) j) i.isLt j.isLt hne)
    (fun n => by
      cases n with
      | zero =>
        have hell0 : M.ell 0 ≤ 1 := by
          refine Nat.ceil_le.mpr ?_
          refine le_trans (min_le_left _ _) ?_
          have hlog : Real.log ((0 : ℕ) : ℝ) = 0 := by
            rw [show ((0 : ℕ) : ℝ) = (0 : ℝ) by norm_num, Real.log_zero]
          rw [hlog]
          norm_num
        have heq : posPartMat (corrMat M.p M.ell SigB M.g M.ell_le_p 0)
            = Matrix.diagonal (fun _ : Fin (M.ell 0) => (1 : ℝ)) := by
          ext i j
          obtain rfl : i = j := Fin.ext (by
            have hi := i.isLt
            have hj := j.isLt
            omega)
          have hdiag : SigB 0 (M.g 0 (Fin.castLE (M.ell_le_p 0) i))
              (M.g 0 (Fin.castLE (M.ell_le_p 0) i))
              = (cvar * ((((M.g 0).symm (M.g 0 (Fin.castLE (M.ell_le_p 0) i)) : ℕ) : ℝ) + 1)
                  ^ (-alpha)) ^ 2 := by
            have hS : SigB 0 = Matrix.diagonal (fun j : Fin (M.p 0) =>
                (cvar * ((((M.g 0).symm j : ℕ) : ℝ) + 1) ^ (-alpha)) ^ 2) := rfl
            rw [hS]
            simp [Matrix.diagonal]
          have hpos : (0 : ℝ) < SigB 0 (M.g 0 (Fin.castLE (M.ell_le_p 0) i))
              (M.g 0 (Fin.castLE (M.ell_le_p 0) i)) := by
            rw [hdiag]
            exact pow_pos (mul_pos hcvar
              (Real.rpow_pos_of_pos (by positivity) _)) 2
          have hentry : corrMat M.p M.ell SigB M.g M.ell_le_p 0 i i = 1 := by
            show SigB 0 (M.g 0 (Fin.castLE (M.ell_le_p 0) i))
                (M.g 0 (Fin.castLE (M.ell_le_p 0) i)) /
              (Real.sqrt (SigB 0 (M.g 0 (Fin.castLE (M.ell_le_p 0) i))
                  (M.g 0 (Fin.castLE (M.ell_le_p 0) i))) *
                Real.sqrt (SigB 0 (M.g 0 (Fin.castLE (M.ell_le_p 0) i))
                  (M.g 0 (Fin.castLE (M.ell_le_p 0) i)))) = 1
            have h2 : Real.sqrt (SigB 0 (M.g 0 (Fin.castLE (M.ell_le_p 0) i))
                  (M.g 0 (Fin.castLE (M.ell_le_p 0) i)))
                * Real.sqrt (SigB 0 (M.g 0 (Fin.castLE (M.ell_le_p 0) i))
                  (M.g 0 (Fin.castLE (M.ell_le_p 0) i)))
                = SigB 0 (M.g 0 (Fin.castLE (M.ell_le_p 0) i))
                  (M.g 0 (Fin.castLE (M.ell_le_p 0) i)) := by
              rw [← pow_two, Real.sq_sqrt (le_of_lt hpos)]
            rw [h2, div_self (ne_of_gt hpos)]
          show max (corrMat M.p M.ell SigB M.g M.ell_le_p 0 i i) 0
            = (Matrix.diagonal (fun _ : Fin (M.ell 0) => (1 : ℝ))) i i
          rw [hentry]
          have hmax : max (1 : ℝ) 0 = 1 :=
            le_antisymm (max_le le_rfl zero_le_one) (le_max_left _ _)
          rw [hmax]
          simp [Matrix.diagonal]
        rw [heq]
        exact Matrix.PosSemidef.diagonal (fun _ => zero_le_one)
      | succ k =>
        have hn0 : 0 < k + 1 := Nat.succ_pos k
        have hn1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
        have hentry : ∀ i j : Fin (M.ell (k + 1)),
            corrMat M.p M.ell SigB M.g M.ell_le_p (k + 1) i j
              = M.corrMat (k + 1) (M.ell (k + 1)) (M.ell_le_p (k + 1)) i j := by
          intro i j
          let A : Fin (M.p (k + 1)) := M.g (k + 1) (Fin.castLE (M.ell_le_p (k + 1)) i)
          let B : Fin (M.p (k + 1)) := M.g (k + 1) (Fin.castLE (M.ell_le_p (k + 1)) j)
          have hcov : M.covX (k + 1) A B = M.Sigma (k + 1) A B :=
            (statopia_math_node_3076116109_992c70da a c0 alpha cvar ccirc eps0 Ccor M hM
              (k + 1) hn1 A B A).1
          have hsqA : (M.sigma (k + 1) A) ^ 2 = M.Sigma (k + 1) A A :=
            (statopia_math_node_3076116109_992c70da a c0 alpha cvar ccirc eps0 Ccor M hM
              (k + 1) hn1 A A A).2.2
          have hsqB : (M.sigma (k + 1) B) ^ 2 = M.Sigma (k + 1) B B :=
            (statopia_math_node_3076116109_992c70da a c0 alpha cvar ccirc eps0 Ccor M hM
              (k + 1) hn1 B B B).2.2
          have hsigA : Real.sqrt (M.Sigma (k + 1) A A) = M.sigma (k + 1) A := by
            rw [← hsqA]
            exact Real.sqrt_sq (le_of_lt (hM.hsig_pos (k + 1) hn0 A))
          have hsigB : Real.sqrt (M.Sigma (k + 1) B B) = M.sigma (k + 1) B := by
            rw [← hsqB]
            exact Real.sqrt_sq (le_of_lt (hM.hsig_pos (k + 1) hn0 B))
          show M.Sigma (k + 1) A B /
              (Real.sqrt (M.Sigma (k + 1) A A) * Real.sqrt (M.Sigma (k + 1) B B))
            = M.corrEntry (k + 1) A B
          show M.Sigma (k + 1) A B /
              (Real.sqrt (M.Sigma (k + 1) A A) * Real.sqrt (M.Sigma (k + 1) B B))
            = M.covX (k + 1) A B / (M.sigma (k + 1) A * M.sigma (k + 1) B)
          rw [hcov, hsigA, hsigB]
        have hmat : posPartMat (corrMat M.p M.ell SigB M.g M.ell_le_p (k + 1))
            = M.corrMatPos (k + 1) (M.ell (k + 1)) (M.ell_le_p (k + 1)) := by
          ext i j
          show max (corrMat M.p M.ell SigB M.g M.ell_le_p (k + 1) i j) 0
            = max (M.corrMat (k + 1) (M.ell (k + 1)) (M.ell_le_p (k + 1)) i j) 0
          rw [hentry i j]
        rw [hmat]
        exact hM.hcorr_psd (k + 1))
    (fun n => by
      have step1 : (∑ i : Fin (M.ell n), ∑ j : Fin (M.ell n),
            (if i < j then max (corrMat M.p M.ell SigB M.g M.ell_le_p n i j) 0 else 0))
          = ∑ q ∈ (Finset.univ : Finset (Fin (M.ell n) × Fin (M.ell n))).filter
              (fun q => q.1 < q.2),
              max (corrMat M.p M.ell SigB M.g M.ell_le_p n q.1 q.2) 0 := by
        simp only [Finset.sum_filter, Fintype.sum_prod_type]
      have step2 : (∑ q ∈ (Finset.univ : Finset (Fin (M.ell n) × Fin (M.ell n))).filter
              (fun q => q.1 < q.2),
              max (corrMat M.p M.ell SigB M.g M.ell_le_p n q.1 q.2) 0)
          = ∑ q ∈ (Finset.univ : Finset (Fin (M.p n) × Fin (M.p n))).filter
              (fun q => (q.1 : ℕ) < M.ell n ∧ (q.2 : ℕ) < M.ell n ∧ q.1 < q.2),
              max (M.corrEntry n (M.g n q.1) (M.g n q.2)) 0 := by
        refine Finset.sum_nbij
          (fun q : Fin (M.ell n) × Fin (M.ell n) =>
            (Fin.castLE (M.ell_le_p n) q.1, Fin.castLE (M.ell_le_p n) q.2)) ?_ ?_ ?_ ?_
        · intro a ha
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, a.1.isLt, a.2.isLt, (Finset.mem_filter.mp ha).2⟩
        · intro a _ a' _ heq
          refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
          · have h := congrArg (fun q : Fin (M.p n) × Fin (M.p n) => (q.1 : ℕ)) heq
            simpa using h
          · have h := congrArg (fun q : Fin (M.p n) × Fin (M.p n) => (q.2 : ℕ)) heq
            simpa using h
        · intro b hb
          obtain ⟨hb1, hb2, hb3⟩ := (Finset.mem_filter.mp hb).2
          exact ⟨(⟨b.1.1, hb1⟩, ⟨b.2.1, hb2⟩),
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb3⟩, rfl⟩
        · intro q hq
          cases n with
          | zero =>
            exfalso
            have hell0 : M.ell 0 ≤ 1 := by
              refine Nat.ceil_le.mpr ?_
              refine le_trans (min_le_left _ _) ?_
              have hlog : Real.log ((0 : ℕ) : ℝ) = 0 := by
                rw [show ((0 : ℕ) : ℝ) = (0 : ℝ) by norm_num, Real.log_zero]
              rw [hlog]
              norm_num
            have hq2 : ((q.1 : ℕ)) < ((q.2 : ℕ)) := (Finset.mem_filter.mp hq).2
            have h1 : ((q.1 : ℕ)) < M.ell 0 := q.1.isLt
            have h2 : ((q.2 : ℕ)) < M.ell 0 := q.2.isLt
            omega
          | succ k =>
            have hn0 : 0 < k + 1 := Nat.succ_pos k
            let A : Fin (M.p (k + 1)) := M.g (k + 1) (Fin.castLE (M.ell_le_p (k + 1)) q.1)
            let B : Fin (M.p (k + 1)) := M.g (k + 1) (Fin.castLE (M.ell_le_p (k + 1)) q.2)
            have hcov : M.covX (k + 1) A B = M.Sigma (k + 1) A B :=
              (statopia_math_node_3076116109_992c70da a c0 alpha cvar ccirc eps0 Ccor M hM
                (k + 1) (Nat.succ_le_succ (Nat.zero_le k)) A B A).1
            have hsqA : (M.sigma (k + 1) A) ^ 2 = M.Sigma (k + 1) A A :=
              (statopia_math_node_3076116109_992c70da a c0 alpha cvar ccirc eps0 Ccor M hM
                (k + 1) (Nat.succ_le_succ (Nat.zero_le k)) A A A).2.2
            have hsqB : (M.sigma (k + 1) B) ^ 2 = M.Sigma (k + 1) B B :=
              (statopia_math_node_3076116109_992c70da a c0 alpha cvar ccirc eps0 Ccor M hM
                (k + 1) (Nat.succ_le_succ (Nat.zero_le k)) B B B).2.2
            have hsigA : Real.sqrt (M.Sigma (k + 1) A A) = M.sigma (k + 1) A := by
              rw [← hsqA]
              exact Real.sqrt_sq (le_of_lt (hM.hsig_pos (k + 1) hn0 A))
            have hsigB : Real.sqrt (M.Sigma (k + 1) B B) = M.sigma (k + 1) B := by
              rw [← hsqB]
              exact Real.sqrt_sq (le_of_lt (hM.hsig_pos (k + 1) hn0 B))
            have hentry' : corrMat M.p M.ell SigB M.g M.ell_le_p (k + 1) q.1 q.2
                = M.corrEntry (k + 1) (M.g (k + 1) (Fin.castLE (M.ell_le_p (k + 1)) q.1))
                    (M.g (k + 1) (Fin.castLE (M.ell_le_p (k + 1)) q.2)) := by
              show M.Sigma (k + 1) A B /
                  (Real.sqrt (M.Sigma (k + 1) A A) * Real.sqrt (M.Sigma (k + 1) B B))
                = M.covX (k + 1) A B / (M.sigma (k + 1) A * M.sigma (k + 1) B)
              rw [hcov, hsigA, hsigB]
            rw [hentry']
      rw [step1, step2]
      exact hM.hcorr_sum n)
  obtain ⟨cIII, hcIII, n0III, hn0III, hIII⟩ := hIIIn
  obtain ⟨c_thr, hc_thr, Cb, hCb, N₂, hN₂1, hBnd⟩ := hb.1
  obtain ⟨N₁, hN₁1, hAnd⟩ := hb.2
  obtain ⟨Nthr, hNthr⟩ :=
    statopia_math_node_70832348_d8d3cb27 a c0 alpha cvar ccirc eps0 Ccor c_thr M
      ha hc0 halpha hcvar hccirc heps0 hCcor hc_thr hM
  have hIn : ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → M.In n ≤ (Ca + 1) * (n : ℝ) ^ (-(1 / 2 : ℝ) + δ) := by
    refine ⟨max (max (max N₁ N₂) (max Nthr 1)) (Nat.ceil (Cb ^ (1 / ((1 : ℝ) / 2 + δ)))), ?_,
      ?_⟩
    · exact le_trans (le_trans (le_max_right Nthr 1) (le_max_right _ _)) (le_max_left _ _)
    · intro n hn
      have hinner : max (max N₁ N₂) (max Nthr 1) ≤ n := le_trans (le_max_left _ _) hn
      have hn1 : 1 ≤ n := le_trans (le_trans (le_max_right Nthr 1) (le_max_right _ _)) hinner
      have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn1
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      have hpw : (0 : ℝ) < (n : ℝ) ^ (-(1 / 2 : ℝ) + δ) := hpow n hn1
      have hpos : (0 : ℝ) < Ca + 1 := by linarith
      by_cases hcase : M.p n ≤ M.kIdx n
      · obtain ⟨hIn0, hIn0b⟩ :=
          statopia_math_node_762516508_6fca4911 a c0 alpha cvar ccirc eps0 Ccor M hM n hcase
        rw [hIn0]
        exact mul_nonneg hpos.le hpw.le
      · have hlt : M.kIdx n < M.p n := lt_of_not_ge hcase
        have hN₁le : N₁ ≤ n := le_trans (le_trans (le_max_left N₁ N₂) (le_max_left _ _)) hinner
        have hN₂le : N₂ ≤ n := le_trans (le_trans (le_max_right N₁ N₂) (le_max_left _ _)) hinner
        have hNthrle : Nthr ≤ n := le_trans (le_trans (le_max_left Nthr 1) (le_max_right _ _)) hinner
        have hCble : Cb ≤ (n : ℝ) ^ ((1 : ℝ) / 2 + δ) := by
          have h1 : Cb ^ (1 / ((1 : ℝ) / 2 + δ))
              ≤ ((Nat.ceil (Cb ^ (1 / ((1 : ℝ) / 2 + δ))) : ℕ) : ℝ) := Nat.le_ceil _
          have h2 : ((Nat.ceil (Cb ^ (1 / ((1 : ℝ) / 2 + δ))) : ℕ) : ℝ) ≤ (n : ℝ) := by
            exact_mod_cast le_trans (le_max_right _ _) hn
          have h3 : (Cb ^ (1 / ((1 : ℝ) / 2 + δ))) ^ ((1 : ℝ) / 2 + δ)
              ≤ (n : ℝ) ^ ((1 : ℝ) / 2 + δ) :=
            Real.rpow_le_rpow (Real.rpow_nonneg hCb.le _) (le_trans h1 h2)
              (by linarith [hδ.1])
          have h4 : (Cb ^ (1 / ((1 : ℝ) / 2 + δ))) ^ ((1 : ℝ) / 2 + δ) = Cb := by
            rw [← Real.rpow_mul hCb.le]
            have h5 : (1 / ((1 : ℝ) / 2 + δ)) * ((1 : ℝ) / 2 + δ) = 1 := by
              rw [one_div,
                inv_mul_cancel₀ (ne_of_gt (by linarith [hδ.1] : (0 : ℝ) < (1 : ℝ) / 2 + δ))]
            rw [h5, Real.rpow_one]
          rwa [h4] at h3
        have hBterm : Cb * (n : ℝ) ^ (-1 : ℝ) ≤ (n : ℝ) ^ (-(1 / 2 : ℝ) + δ) := by
          have hnpos' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
          have hsplit : (n : ℝ) ^ (-(1 / 2 : ℝ) + δ)
              = (n : ℝ) ^ ((1 : ℝ) / 2 + δ) * (n : ℝ) ^ (-1 : ℝ) := by
            rw [← Real.rpow_add hnpos']
            congr 1
            ring
          rw [hsplit]
          exact mul_le_mul_of_nonneg_right hCble (le_of_lt (Real.rpow_pos_of_pos hnpos' _))
        have ht : c_thr * (M.kIdx n : ℝ) ^ (-(alpha * (1 - M.tau n))) * Real.log (n : ℝ)
            ≤ ccirc * ((M.ell n : ℝ) ^ (-(alpha * (1 - M.tau n)))) *
                Real.sqrt (Real.log (M.ell n : ℝ)) := hNthr n hNthrle hlt
        have hcmp :
            dK (μ.map (fun ω => fmax Finset.univ
                (fun j => M.S n ω j / (M.sigma n j) ^ (M.tau n))))
              (μ.map (fun ω => fmax (M.J n (M.kIdx n))
                (fun j => M.S n ω j / (M.sigma n j) ^ (M.tau n))))
            ≤ (μ {ω : Ω | fmax (M.J n (M.kIdx n))
                  (fun j => M.S n ω j / (M.sigma n j) ^ (M.tau n))
                  ≤ ccirc * ((M.ell n : ℝ) ^ (-(alpha * (1 - M.tau n)))) *
                      Real.sqrt (Real.log (M.ell n : ℝ))}).toReal
              + (μ {ω : Ω | fmax (Finset.univ \ M.J n (M.kIdx n))
                    (fun j => M.S n ω j / (M.sigma n j) ^ (M.tau n))
                  > c_thr * (M.kIdx n : ℝ) ^ (-(alpha * (1 - M.tau n))) *
                      Real.log (n : ℝ)}).toReal :=
          statopia_math_node_4287235009_e1acef55 (P := μ) (M.p n) (M.hp n)
            (M.J n (M.kIdx n)) (hJ0_gen n) (hJdiff_gen n hlt) (M.S n)
            (fun j => hS_meas n j) (M.sigma n) (fun j => hM.hsig_pos n hnpos j)
            (M.tau n)
            (c_thr * (M.kIdx n : ℝ) ^ (-(alpha * (1 - M.tau n))) * Real.log (n : ℝ))
            (ccirc * ((M.ell n : ℝ) ^ (-(alpha * (1 - M.tau n)))) *
              Real.sqrt (Real.log (M.ell n : ℝ)))
            ht
        have hmap : μ.map (fun ω => M.Md n (M.p n) ω)
            = μ.map (fun ω => fmax Finset.univ
                (fun j => M.S n ω j / (M.sigma n j) ^ (M.tau n))) := by
          congr 1
          funext ω
          exact hMd_univ n ω
        have hmap2 : μ.map (fun ω => M.Md n (M.kIdx n) ω)
            = μ.map (fun ω => fmax (M.J n (M.kIdx n))
                (fun j => M.S n ω j / (M.sigma n j) ^ (M.tau n))) := rfl
        have hsigS : ∀ (n : ℕ), 1 ≤ n → ∀ j : Fin (M.p n), Real.sqrt (SigB n j j) = M.sigma n j := by
          intro n hn j
          obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
          have hn0 : 0 < k + 1 := Nat.succ_pos k
          have hsq : M.Sigma (k + 1) j j = (M.sigma (k + 1) j) ^ 2 :=
            ((statopia_math_node_3076116109_992c70da a c0 alpha cvar ccirc eps0 Ccor M hM
              (k + 1) hn j j j).2.2).symm
          show Real.sqrt (M.Sigma (k + 1) j j) = M.sigma (k + 1) j
          rw [hsq]
          exact Real.sqrt_sq (le_of_lt (hM.hsig_pos (k + 1) hn0 j))
        have hSvecS : ∀ (n : ℕ), 1 ≤ n → ∀ (ω' : Ω) (j : Fin (M.p n)),
            Svec M.p M.X M.mu n ω' j = M.S n ω' j := by
          intro n hn ω' j
          have hpos' : (0 : ℝ) < (n : ℝ) := by
            exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hn
          have hpow_eq : (n : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (n : ℝ))⁻¹ := by
            rw [show -(1 / 2 : ℝ) = (1 / 2 : ℝ) * (-1) by ring,
              Real.rpow_mul (le_of_lt hpos'), ← Real.sqrt_eq_rpow, Real.rpow_neg_one]
          show (n : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ i : Fin n, (M.X n i ω' j - M.mu n j)
            = (Real.sqrt (n : ℝ))⁻¹ * ∑ i : Fin n, (M.X n i ω' j - ∫ ω'', M.X n i ω'' j ∂μ)
          rw [hpow_eq]
          congr 1
          exact Finset.sum_congr rfl (fun i _ => by rw [hX_mean n i j])
        have hmemJ : ∀ (n : ℕ) (j : Fin (M.p n)),
            (j ∈ M.J n (M.kIdx n)) ↔ ((M.g n).symm j : ℕ) < M.kIdx n := by
          intro n j
          constructor
          · intro hmem
            obtain ⟨i, hi, hgi⟩ := Finset.mem_image.mp hmem
            have hik : (i : ℕ) < M.kIdx n := (Finset.mem_filter.mp hi).2
            rw [← hgi, Equiv.symm_apply_apply]
            exact hik
          · intro hltj
            exact Finset.mem_image.mpr ⟨(M.g n).symm j,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hltj⟩, Equiv.apply_symm_apply (M.g n) j⟩
        have hfmaxLe : ∀ (n : ℕ) (ω' : Ω) (t : ℝ), 0 ≤ t →
            (fmax (M.J n (M.kIdx n))
                (fun j => M.S n ω' j / (M.sigma n j) ^ (M.tau n)) ≤ t
              ↔ ∀ j ∈ M.J n (M.kIdx n),
                  M.S n ω' j / (M.sigma n j) ^ (M.tau n) ≤ t) := by
          intro n ω' t ht0
          constructor
          · intro hs j hj
            exact le_trans (le_csSup ((M.J n (M.kIdx n)).finite_toSet.image _).bddAbove
              (Set.mem_image_of_mem _ hj)) hs
          · intro hs
            refine Real.sSup_le (fun x hx => ?_) ht0
            simp only [Set.mem_image, Finset.mem_coe] at hx
            obtain ⟨j, hj, rfl⟩ := hx
            exact hs j hj
        have hA : (μ {ω : Ω | fmax (M.J n (M.kIdx n))
              (fun j => M.S n ω j / (M.sigma n j) ^ (M.tau n))
              ≤ ccirc * ((M.ell n : ℝ) ^ (-(alpha * (1 - M.tau n)))) *
                  Real.sqrt (Real.log (M.ell n : ℝ))}).toReal
            ≤ Ca * (n : ℝ) ^ (-(1 / 2 : ℝ) + δ) := by
          have ht0 : (0 : ℝ) ≤ ccirc * ((M.ell n : ℝ) ^ (-(alpha * (1 - M.tau n)))) *
              Real.sqrt (Real.log (M.ell n : ℝ)) :=
            mul_nonneg (mul_nonneg hccirc.1.le
              (le_of_lt (Real.rpow_pos_of_pos (by exact_mod_cast hone_ell_gen n) _)))
              (Real.sqrt_nonneg _)
          have hset : {ω' : Ω | fmax (M.J n (M.kIdx n))
                (fun j => M.S n ω' j / (M.sigma n j) ^ (M.tau n))
                ≤ ccirc * ((M.ell n : ℝ) ^ (-(alpha * (1 - M.tau n)))) *
                    Real.sqrt (Real.log (M.ell n : ℝ))}
              = Aevent M.p M.X M.mu SigB M.tau M.kIdx M.g n
                  (t2fun M.ell (fun m => alpha * (1 - M.tau m)) ccirc n) := by
            ext ω'
            simp only [Set.mem_setOf_eq, Aevent, t2fun, hSvecS n hn1 ω', hsigS n hn1, mul_assoc]
            rw [hfmaxLe n ω' _
              (mul_nonneg hccirc.1.le (mul_nonneg
                (le_of_lt (Real.rpow_pos_of_pos (by exact_mod_cast hone_ell_gen n) _))
                (Real.sqrt_nonneg _)))]
            constructor
            · intro hs j hj
              exact hs j ((hmemJ n j).mpr hj)
            · intro hs j hj
              exact hs j ((hmemJ n j).mp hj)
          rw [hset]
          have hkey := hAnd n hN₁le hlt
          calc (μ (Aevent M.p M.X M.mu SigB M.tau M.kIdx M.g n
                (t2fun M.ell (fun m => alpha * (1 - M.tau m)) ccirc n))).toReal
              ≤ (ENNReal.ofReal (Ca * (n : ℝ) ^ (-(1 / 2 : ℝ) + δ))).toReal :=
                ENNReal.toReal_mono ENNReal.ofReal_ne_top hkey
            _ = Ca * (n : ℝ) ^ (-(1 / 2 : ℝ) + δ) :=
                ENNReal.toReal_ofReal (le_of_lt (mul_pos hCa (hpow n hn1)))
        have hB : (μ {ω : Ω | fmax (Finset.univ \ M.J n (M.kIdx n))
              (fun j => M.S n ω j / (M.sigma n j) ^ (M.tau n))
              > c_thr * (M.kIdx n : ℝ) ^ (-(alpha * (1 - M.tau n))) * Real.log (n : ℝ)}).toReal
            ≤ Cb * (n : ℝ) ^ (-1 : ℝ) := by
          have hnpos' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
          have hk1 : (0 : ℝ) < (M.kIdx n : ℝ) := by
            exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (hone_k_gen n)
          have hT : (0 : ℝ) ≤ c_thr * ((M.kIdx n : ℝ) ^ (-(alpha * (1 - M.tau n))) *
              Real.log (n : ℝ)) :=
            mul_nonneg hc_thr.le (mul_nonneg (le_of_lt (Real.rpow_pos_of_pos hk1 _))
              (Real.log_nonneg hnR))
          have hfmaxLec : ∀ (ω' : Ω), (fmax (Finset.univ \ M.J n (M.kIdx n))
                (fun j => M.S n ω' j / (M.sigma n j) ^ (M.tau n))
                ≤ c_thr * ((M.kIdx n : ℝ) ^ (-(alpha * (1 - M.tau n))) * Real.log (n : ℝ)))
              ↔ ∀ j ∈ Finset.univ \ M.J n (M.kIdx n),
                  M.S n ω' j / (M.sigma n j) ^ (M.tau n)
                    ≤ c_thr * ((M.kIdx n : ℝ) ^ (-(alpha * (1 - M.tau n))) * Real.log (n : ℝ)) := by
            intro ω'
            constructor
            · intro hs j hj
              exact le_trans (le_csSup
                (((Finset.univ \ M.J n (M.kIdx n))).finite_toSet.image _).bddAbove
                (Set.mem_image_of_mem _ hj)) hs
            · intro hs
              exact Real.sSup_le (fun x hx => by
                simp only [Set.mem_image, Finset.mem_coe] at hx
                obtain ⟨j, hj, rfl⟩ := hx
                exact hs j hj) hT
          have hgt : ∀ (ω' : Ω), (fmax (Finset.univ \ M.J n (M.kIdx n))
                (fun j => M.S n ω' j / (M.sigma n j) ^ (M.tau n))
                > c_thr * ((M.kIdx n : ℝ) ^ (-(alpha * (1 - M.tau n))) * Real.log (n : ℝ)))
              ↔ (∃ j : Fin (M.p n), ¬ (j ∈ M.J n (M.kIdx n)) ∧
                  c_thr * ((M.kIdx n : ℝ) ^ (-(alpha * (1 - M.tau n))) * Real.log (n : ℝ))
                    < M.S n ω' j / (M.sigma n j) ^ (M.tau n)) := by
            intro ω'
            have hle : (fmax (Finset.univ \ M.J n (M.kIdx n))
                  (fun j => M.S n ω' j / (M.sigma n j) ^ (M.tau n))
                  ≤ c_thr * ((M.kIdx n : ℝ) ^ (-(alpha * (1 - M.tau n))) * Real.log (n : ℝ)))
                ↔ ∀ j, ¬ (j ∈ M.J n (M.kIdx n)) →
                    M.S n ω' j / (M.sigma n j) ^ (M.tau n)
                      ≤ c_thr * ((M.kIdx n : ℝ) ^ (-(alpha * (1 - M.tau n))) * Real.log (n : ℝ)) := by
              rw [hfmaxLec ω']
              constructor
              · intro h j hj
                exact h j (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj⟩)
              · intro h j hj
                exact h j (Finset.mem_sdiff.mp hj).2
            have hright : (∃ j : Fin (M.p n), ¬ (j ∈ M.J n (M.kIdx n)) ∧
                  c_thr * ((M.kIdx n : ℝ) ^ (-(alpha * (1 - M.tau n))) * Real.log (n : ℝ))
                    < M.S n ω' j / (M.sigma n j) ^ (M.tau n))
                ↔ ¬ (∀ j, ¬ (j ∈ M.J n (M.kIdx n)) →
                    M.S n ω' j / (M.sigma n j) ^ (M.tau n)
                      ≤ c_thr * ((M.kIdx n : ℝ) ^ (-(alpha * (1 - M.tau n))) * Real.log (n : ℝ))) := by
              constructor
              · rintro ⟨j, hj, hlt⟩ hall
                exact absurd (hall j hj) (not_le.mpr hlt)
              · intro h
                by_contra hc
                refine h (fun j hj => ?_)
                by_contra h2
                exact hc ⟨j, hj, not_le.mp h2⟩
            rw [show (fmax (Finset.univ \ M.J n (M.kIdx n))
                  (fun j => M.S n ω' j / (M.sigma n j) ^ (M.tau n))
                  > c_thr * ((M.kIdx n : ℝ) ^ (-(alpha * (1 - M.tau n))) * Real.log (n : ℝ)))
                ↔ ¬ (fmax (Finset.univ \ M.J n (M.kIdx n))
                  (fun j => M.S n ω' j / (M.sigma n j) ^ (M.tau n))
                  ≤ c_thr * ((M.kIdx n : ℝ) ^ (-(alpha * (1 - M.tau n))) * Real.log (n : ℝ))) from
              not_le.symm]
            rw [hle, hright]
          have hset : {ω' : Ω | fmax (Finset.univ \ M.J n (M.kIdx n))
                (fun j => M.S n ω' j / (M.sigma n j) ^ (M.tau n))
                > c_thr * (M.kIdx n : ℝ) ^ (-(alpha * (1 - M.tau n))) * Real.log (n : ℝ)}
              = Bevent M.p M.X M.mu SigB M.tau M.kIdx M.g n
                  (t1fun M.kIdx (fun m => alpha * (1 - M.tau m)) c_thr n) := by
            ext ω'
            simp only [Set.mem_setOf_eq, Bevent, t1fun, hSvecS n hn1 ω', hsigS n hn1, mul_assoc]
            rw [hgt ω']
            constructor
            · rintro ⟨j, hj, hlt⟩
              exact ⟨j, fun hltk => hj ((hmemJ n j).mpr hltk), hlt⟩
            · rintro ⟨j, hj, hlt⟩
              exact ⟨j, fun hmem => hj ((hmemJ n j).mp hmem), hlt⟩
          rw [hset]
          have hkey := hBnd n hN₂le
          calc (μ (Bevent M.p M.X M.mu SigB M.tau M.kIdx M.g n
                (t1fun M.kIdx (fun m => alpha * (1 - M.tau m)) c_thr n))).toReal
              ≤ (ENNReal.ofReal (Cb * (n : ℝ) ^ (-1 : ℝ))).toReal :=
                ENNReal.toReal_mono ENNReal.ofReal_ne_top hkey
            _ = Cb * (n : ℝ) ^ (-1 : ℝ) :=
                ENNReal.toReal_ofReal (le_of_lt (mul_pos hCb (Real.rpow_pos_of_pos hnpos' _)))
        have hz : (n : ℝ) ^ (-1 : ℝ) ≤ (n : ℝ) ^ (-(1 / 2 : ℝ) + δ) :=
          Real.rpow_le_rpow_of_exponent_le hnR (by linarith [hδ.1])
        have hInEq : M.In n = dK (μ.map (fun ω => fmax Finset.univ
                (fun j => M.S n ω j / (M.sigma n j) ^ (M.tau n))))
              (μ.map (fun ω => fmax (M.J n (M.kIdx n))
                (fun j => M.S n ω j / (M.sigma n j) ^ (M.tau n)))) := by
          show dK (μ.map (fun ω => M.Md n (M.p n) ω))
              (μ.map (fun ω => M.Md n (M.kIdx n) ω)) = _
          rw [hmap, hmap2]
        rw [hInEq]
        calc dK (μ.map (fun ω => fmax Finset.univ
                (fun j => M.S n ω j / (M.sigma n j) ^ (M.tau n))))
              (μ.map (fun ω => fmax (M.J n (M.kIdx n))
                (fun j => M.S n ω j / (M.sigma n j) ^ (M.tau n))))
            ≤ (μ {ω : Ω | fmax (M.J n (M.kIdx n))
                  (fun j => M.S n ω j / (M.sigma n j) ^ (M.tau n))
                  ≤ ccirc * ((M.ell n : ℝ) ^ (-(alpha * (1 - M.tau n)))) *
                      Real.sqrt (Real.log (M.ell n : ℝ))}).toReal
              + (μ {ω : Ω | fmax (Finset.univ \ M.J n (M.kIdx n))
                    (fun j => M.S n ω j / (M.sigma n j) ^ (M.tau n))
                  > c_thr * (M.kIdx n : ℝ) ^ (-(alpha * (1 - M.tau n))) *
                      Real.log (n : ℝ)}).toReal := hcmp
          _ ≤ Ca * (n : ℝ) ^ (-(1 / 2 : ℝ) + δ) + Cb * (n : ℝ) ^ (-1 : ℝ) :=
              add_le_add hA hB
          _ ≤ Ca * (n : ℝ) ^ (-(1 / 2 : ℝ) + δ) + (n : ℝ) ^ (-(1 / 2 : ℝ) + δ) := by
              linarith [hBterm]
          _ = (Ca + 1) * (n : ℝ) ^ (-(1 / 2 : ℝ) + δ) := by ring
  obtain ⟨n0In, hn0In, hInb⟩ := hIn
  exact ⟨max n0In n0III, le_trans hn0In (le_max_left _ _), fun n hn => ⟨
    hInb n (le_trans (le_max_left _ _) hn),
    hIII n (le_trans (le_max_right _ _) hn)⟩⟩
  /- @proof-region region.root.f926de98daaa end -/

end

-- Paper root revision de202f14-188c-4170-a986-5b9f211855d4

