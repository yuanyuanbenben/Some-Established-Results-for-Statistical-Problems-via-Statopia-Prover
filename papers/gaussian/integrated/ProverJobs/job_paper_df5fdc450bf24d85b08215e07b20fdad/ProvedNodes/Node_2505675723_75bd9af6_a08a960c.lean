import ProverJobs.job_paper_df5fdc450bf24d85b08215e07b20fdad.Vocabulary
import ProverJobs.job_paper_df5fdc450bf24d85b08215e07b20fdad.Base
import ProverJobs.job_paper_df5fdc450bf24d85b08215e07b20fdad.ProvedNodes.Node_1142492082_c5c8b49c_02948ae9
import ProverJobs.job_paper_df5fdc450bf24d85b08215e07b20fdad.ProvedNodes.Node_3045670844_0a1a6b78_4871f488
import ProverJobs.job_paper_df5fdc450bf24d85b08215e07b20fdad.ProvedNodes.Node_637763047_1341bf7c_2025c604
import ProverJobs.job_paper_df5fdc450bf24d85b08215e07b20fdad.ExternalNodes.Node_0a6b8bd7afa182dd69d9
import ProverJobs.job_paper_df5fdc450bf24d85b08215e07b20fdad.ExternalNodes.Node_4e38c0b212aeaf238af1

namespace PaperProofTasks.job_paper_df5fdc450bf24d85b08215e07b20fdad





open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators
open _root_.PaperProofTasks.job_paper_df5fdc450bf24d85b08215e07b20fdad.Statlib.Imported

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators
namespace Statlib.Imported
open _root_.Statlib

set_option autoImplicit false in
theorem statopia_math_node_2505675723_75bd9af6 : ∀ (alpha : ℝ) (halpha : 0 < alpha)
    (tau : ℕ → ℝ)
    (n0 : ℕ) (hn0 : 1 ≤ n0)
    (hP : ∀ n : ℕ, n0 ≤ n →
      (qN alpha tau n = Real.log (n : ℝ) ∧
        (qN alpha tau n / max (Real.log (qN alpha tau n)) 1) *
          (n : ℝ) ^ (-(1 / 2 : ℝ) + 1 / qN alpha tau n) ≤ 1))
    (c0 : ℝ) (hc0 : 0 < c0),
    ∃ C1 : ℝ, 0 < C1 ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω]
        (muP : ℕ → Measure Ω) (hmuP : ∀ n, IsProbabilityMeasure (muP n))
        (p : ℕ → ℕ)
        (Sigma : (n : ℕ) → Matrix (Fin (p n)) (Fin (p n)) ℝ)
        (hSigma : ∀ n, (Sigma n).PosSemidef)
        (SigmaHalf : (n : ℕ) → Matrix (Fin (p n)) (Fin (p n)) ℝ)
        (hSigmaHalf : ∀ n, SigmaHalf n = Matrix.PosSemidef.sqrt (hSigma n))
        (hsigma : ∀ (n : ℕ) (j : Fin (p n)), 0 < Sigma n j j)
        (mu : (n : ℕ) → Fin (p n) → ℝ)
        (Z : (n : ℕ) → Fin n → Ω → (Fin (p n) → ℝ))
        (X : (n : ℕ) → Fin n → Ω → (Fin (p n) → ℝ))
        (hX_model : ∀ (n : ℕ) (i : Fin n) (ω : Ω) (l : Fin (p n)),
          X n i ω l = mu n l + (SigmaHalf n).mulVec (Z n i ω) l)
        (hZ_meas : ∀ (n : ℕ) (i : Fin n), Measurable (Z n i))
        (hZ_indep : ∀ n, iIndepFun (fun i : Fin n => Z n i) (muP n))
        (hZ_mem : ∀ (n : ℕ) (i : Fin n), MemLp (Z n i) 2 (muP n))
        (hZ_mean : ∀ (n : ℕ) (i : Fin n) (l : Fin (p n)),
          ∫ ω, Z n i ω l ∂(muP n) = 0)
        (hZ_cov : ∀ (n : ℕ) (i : Fin n) (u v : Fin (p n)),
          ∫ ω, Z n i ω u * Z n i ω v ∂(muP n) = if u = v then (1 : ℝ) else 0)
        (hZ_psi : ∀ (n : ℕ) (i : Fin n) (u : Fin (p n) → ℝ), (∑ l, (u l) ^ 2) = 1 →
          psi1Norm (fun ω => ∑ l, u l * Z n i ω l) (muP n) ≤ ENNReal.ofReal c0),
        ∀ n : ℕ, n0 ≤ n → ∀ (q : ℝ), 2 ≤ q → q ≤ Real.sqrt (n : ℝ) → ∀ j : Fin (p n),
          LqNorm (fun ω => (sigmaOf p Sigma n j)⁻¹ * Svec p X mu n ω j) q (muP n)
            ≤ ENNReal.ofReal (C1 * q) := by
  /- @proof-region region.target-node.session.8f2a725f9530f40b begin -/
  intro alpha halpha tau n0 hn0 hP c0 hc0
  obtain ⟨cR, hcR, hRos⟩ := ExternalRevision_b6071945cf90850933f075b907c86da3bc0900ed9d0e2c5e428f11284eee47a4.citation
  obtain ⟨C2, hC2, hM2⟩ := ext_model_2
  refine ⟨max (cR * (1 + 3 * C2)) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro Ω _ muP hmuP p Sigma hSigma SigmaHalf hSigmaHalf hsigma mu Z X hX_model
    hZ_meas hZ_indep hZ_mem hZ_mean hZ_cov hZ_psi n hn q hq2 hqle j
  let μP : ℕ → Measure Ω := muP
  have hμP : ∀ n, IsProbabilityMeasure (μP n) := fun n => hmuP n
  have hX_def : ∀ (n : ℕ) (i : Fin n) (ω : Ω) (l : Fin (p n)),
      X n i ω l = mu n l + (SigmaHalf n).mulVec (Z n i ω) l := hX_model
  have hsigma_pos : ∀ (n : ℕ) (j : Fin (p n)), 0 < Sigma n j j := hsigma
  have hZ_L2 : ∀ (n : ℕ) (i : Fin n), MemLp (Z n i) 2 (μP n) := hZ_mem
  haveI : IsProbabilityMeasure (μP n) := hμP n
  have hRosPin := hRos (1 : ℝ) 1 Ω (μP n) le_rfl le_rfl (hμP n)
  have hM2Pin := hM2 Ω (μP n) (fun _ => (0 : ℝ)) measurable_const
  let s : ℝ := sigmaOf p Sigma n j
  have hs : 0 < s := Real.sqrt_pos.2 (hsigma_pos n j)
  let u : Fin (p n) → ℝ := fun l => s⁻¹ * SigmaHalf n j l
  let ξ : Fin n → Ω → ℝ := fun i ω => ∑ l, u l * Z n i ω l
  have hu : ∑ l, u l ^ 2 = 1 := by
    have hSpair :=
      statopia_math_node_1142492082_c5c8b49c (Fin (p n)) (Sigma n) (hSigma n)
    have hsq : SigmaHalf n * SigmaHalf n = Sigma n := by
      rw [hSigmaHalf n]
      exact hSpair.2
    have hH : (SigmaHalf n).IsHermitian := by
      rw [hSigmaHalf n]
      exact hSpair.1
    have hrow : ∑ l, SigmaHalf n j l ^ 2 = Sigma n j j := by
      have hsym : ∀ l : Fin (p n), SigmaHalf n j l = SigmaHalf n l j := fun l =>
        (hH.apply j l).symm
      calc ∑ l, SigmaHalf n j l ^ 2
          = ∑ l, SigmaHalf n j l * SigmaHalf n l j := by
            refine Finset.sum_congr rfl (fun l _ => ?_)
            rw [← hsym l]
            ring
        _ = (SigmaHalf n * SigmaHalf n) j j := by
            rw [Matrix.mul_apply]
        _ = Sigma n j j := by rw [hsq]
    have hsum : ∑ l, u l ^ 2 = s⁻¹ ^ 2 * ∑ l, SigmaHalf n j l ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      show (s⁻¹ * SigmaHalf n j l) ^ 2 = s⁻¹ ^ 2 * SigmaHalf n j l ^ 2
      ring
    rw [hsum, hrow]
    have hspos : 0 < Sigma n j j := hsigma_pos n j
    have hs2 : s ^ 2 = Sigma n j j := by
      show Real.sqrt (Sigma n j j) ^ 2 = Sigma n j j
      exact Real.sq_sqrt (le_of_lt hspos)
    have hsne : s ≠ 0 := ne_of_gt hs
    rw [← hs2, ← mul_pow, inv_mul_cancel₀ hsne, one_pow]
  have hVform : ∀ ω, s⁻¹ * Svec p X mu n ω j = (Real.sqrt (n : ℝ))⁻¹ * ∑ i, ξ i ω := by
    have hmv : ∀ (i : Fin n) (ω : Ω),
        (SigmaHalf n).mulVec (Z n i ω) j = ∑ l, SigmaHalf n j l * Z n i ω l := by
      intro i ω
      rfl
    have hXj : ∀ (i : Fin n) (ω : Ω),
        X n i ω j = mu n j + ∑ l, SigmaHalf n j l * Z n i ω l := by
      intro i ω
      rw [hX_def n i ω j, hmv i ω]
    intro ω
    have h2 : ∀ i : Fin n, (X n i ω j - mu n j) = ∑ l, SigmaHalf n j l * Z n i ω l := by
      intro i
      rw [hXj i ω]
      ring
    have h3 : ∀ i : Fin n, (∑ l, SigmaHalf n j l * Z n i ω l) = s * ξ i ω := by
      intro i
      have hξi : ξ i ω = ∑ l, u l * Z n i ω l := rfl
      rw [hξi, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      show SigmaHalf n j l * Z n i ω l = s * ((s⁻¹ * SigmaHalf n j l) * Z n i ω l)
      rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hs), one_mul]
    calc s⁻¹ * Svec p X mu n ω j
        = s⁻¹ * ((Real.sqrt (n : ℝ))⁻¹ * ∑ i : Fin n, (X n i ω j - mu n j)) := by
            simp only [Svec]
      _ = s⁻¹ * ((Real.sqrt (n : ℝ))⁻¹ *
            ∑ i : Fin n, ∑ l, SigmaHalf n j l * Z n i ω l) := by
            rw [Finset.sum_congr rfl (fun i _ => h2 i)]
      _ = s⁻¹ * ((Real.sqrt (n : ℝ))⁻¹ * (s * ∑ i : Fin n, ξ i ω)) := by
            rw [Finset.sum_congr rfl (fun i _ => h3 i), ← Finset.mul_sum]
      _ = (Real.sqrt (n : ℝ))⁻¹ * ∑ i : Fin n, ξ i ω := by
            rw [← mul_assoc, ← mul_assoc, mul_right_comm (s⁻¹) ((Real.sqrt (n : ℝ))⁻¹) s,
              inv_mul_cancel₀ (ne_of_gt hs), one_mul]
  have hξmeas : ∀ i, Measurable (ξ i) := by
    intro i
    exact Finset.measurable_sum _ (fun l _ =>
      measurable_const.mul ((measurable_pi_apply l).comp (hZ_meas n i)))
  have hξindep : iIndepFun ξ (μP n) := by
    have hg : ∀ i : Fin n, Measurable (fun v : Fin (p n) → ℝ => ∑ l, u l * v l) := fun _ =>
      Finset.measurable_sum _ (fun l _ => measurable_const.mul (measurable_pi_apply l))
    exact (hZ_indep n).comp (fun _ v => ∑ l, u l * v l) hg
  have hξsub : ∀ i, psi1Norm (ξ i) (μP n) ≤ ENNReal.ofReal c0 := by
    intro i
    exact hZ_psi n i u hu
  have hexp : ∀ i, ∫⁻ ω, ENNReal.ofReal (Real.exp (|ξ i ω| / (2 * c0))) ∂(μP n) ≤ 2 := by
    intro i
    have hc2 : 0 < 2 * c0 := by linarith
    have hdef : psi1Norm (ξ i) (μP n)
        = sInf (ENNReal.ofReal '' {t : ℝ | 0 < t ∧
            ∫⁻ ω, ENNReal.ofReal (Real.exp (|ξ i ω| / t)) ∂(μP n) ≤ 2}) := rfl
    have hlt : sInf (ENNReal.ofReal '' {t : ℝ | 0 < t ∧
        ∫⁻ ω, ENNReal.ofReal (Real.exp (|ξ i ω| / t)) ∂(μP n) ≤ 2}) < ENNReal.ofReal (2 * c0) := by
      rw [← hdef]
      exact lt_of_le_of_lt (hξsub i) ((ENNReal.ofReal_lt_ofReal_iff').mpr ⟨by linarith, hc2⟩)
    have hex : ∃ t : ℝ, 0 < t ∧ (∫⁻ ω, ENNReal.ofReal (Real.exp (|ξ i ω| / t)) ∂(μP n)) ≤ 2 ∧
        t ≤ 2 * c0 := by
      by_contra hcon
      have hall : ∀ b ∈ ENNReal.ofReal '' {t : ℝ | 0 < t ∧
          ∫⁻ ω, ENNReal.ofReal (Real.exp (|ξ i ω| / t)) ∂(μP n) ≤ 2},
          ENNReal.ofReal (2 * c0) ≤ b := by
        rintro b ⟨t, ⟨htpos, htI⟩, rfl⟩
        apply ENNReal.ofReal_le_ofReal
        by_contra htn
        push_neg at htn
        exact hcon ⟨t, htpos, htI, le_of_lt htn⟩
      exact absurd (le_sInf hall) (not_le.mpr hlt)
    obtain ⟨t, htpos, htI, ht2⟩ := hex
    refine le_trans ?_ htI
    apply lintegral_mono
    intro ω
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hdiv : |ξ i ω| / (2 * c0) ≤ |ξ i ω| / t := by
      gcongr <;> linarith
    exact hdiv
  have hmom : ∀ i, ∀ r : ℝ, 1 ≤ r → LqNorm (ξ i) r (μP n) ≤ ENNReal.ofReal (C2 * r) := by
    intro i r hr
    obtain ⟨K2, -, hK2C, hK2bound⟩ :=
      (hM2 Ω (μP n) (ξ i) (hξmeas i)).2.2.2.2.2.2.2.2.2.1 ⟨2 * c0, by linarith, hexp i⟩
    exact le_trans (hK2bound r hr)
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hK2C (by linarith)))
  have hξmean : ∀ i, ∫ ω, ξ i ω ∂(μP n) = 0 := by
    intro i
    have hcoord : ∀ l : Fin (p n), MemLp (fun ω => Z n i ω l) 2 (μP n) := by
      intro l
      exact (hZ_L2 n i).of_le (((measurable_pi_apply l).comp (hZ_meas n i)).aestronglyMeasurable)
        (Filter.Eventually.of_forall (fun ω => norm_le_pi_norm (Z n i ω) l))
    have hint : ∀ l : Fin (p n), Integrable (fun ω => u l * Z n i ω l) (μP n) := by
      intro l
      exact Integrable.const_mul ((hcoord l).integrable (by norm_num)) (u l)
    have hzero : ∀ l : Fin (p n), ∫ ω, u l * Z n i ω l ∂(μP n) = 0 := by
      intro l
      rw [integral_const_mul, hZ_mean n i l, mul_zero]
    calc ∫ ω, ξ i ω ∂(μP n)
        = ∑ l, ∫ ω, u l * Z n i ω l ∂(μP n) := by
          rw [show ξ i = (fun ω => ∑ l, u l * Z n i ω l) from rfl]
          exact integral_finset_sum Finset.univ (fun l _ => hint l)
      _ = 0 := by simp [hzero]
  have hvar : ∀ i, ∫ ω, ξ i ω ^ 2 ∂(μP n) = 1 := by
    intro i
    have hcoord : ∀ l : Fin (p n), MemLp (fun ω => Z n i ω l) 2 (μP n) := by
      intro l
      exact (hZ_L2 n i).of_le (((measurable_pi_apply l).comp (hZ_meas n i)).aestronglyMeasurable)
        (Filter.Eventually.of_forall (fun ω => norm_le_pi_norm (Z n i ω) l))
    have hpoint : ∀ ω : Ω, ξ i ω ^ 2
        = ∑ l, ∑ m, (u l * u m) * (Z n i ω l * Z n i ω m) := by
      intro ω
      have hξω : ξ i ω = ∑ l, u l * Z n i ω l := rfl
      rw [hξω, sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun m _ => ?_))
      ring
    have hint : ∀ l m : Fin (p n),
        Integrable (fun ω => (u l * u m) * (Z n i ω l * Z n i ω m)) (μP n) := by
      intro l m
      exact (MemLp.integrable_mul (hcoord l) (hcoord m)).const_mul (u l * u m)
    calc ∫ ω, ξ i ω ^ 2 ∂(μP n)
        = ∫ ω, ∑ l, ∑ m, (u l * u m) * (Z n i ω l * Z n i ω m) ∂(μP n) := by
            simp only [hpoint]
      _ = ∑ l, ∫ ω, ∑ m, (u l * u m) * (Z n i ω l * Z n i ω m) ∂(μP n) := by
            exact integral_finset_sum Finset.univ
              (fun l _ => integrable_finset_sum Finset.univ (fun m _ => hint l m))
      _ = ∑ l, ∑ m, ∫ ω, (u l * u m) * (Z n i ω l * Z n i ω m) ∂(μP n) := by
            refine Finset.sum_congr rfl (fun l _ => ?_)
            exact integral_finset_sum Finset.univ (fun m _ => hint l m)
      _ = ∑ l, ∑ m, (u l * u m) * (if l = m then 1 else 0) := by
            refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun m _ => ?_))
            rw [integral_const_mul, hZ_cov n i l m]
      _ = ∑ l, u l ^ 2 := by
            refine Finset.sum_congr rfl (fun l _ => ?_)
            have hfun : ∀ m : Fin (p n),
                (u l * u m) * (if l = m then 1 else 0) = (if l = m then (u l * u m) else 0) := by
              intro m
              by_cases h : l = m <;> simp [h]
            refine Eq.trans (Finset.sum_congr rfl (fun m _ => hfun m)) ?_
            rw [Finset.sum_ite_eq]
            simp only [Finset.mem_univ, if_true]
            ring
      _ = 1 := hu
  have hsum2 : LqNorm (fun ω => ∑ i, ξ i ω) 2 (μP n) ≤ ENNReal.ofReal (Real.sqrt (n : ℝ)) := by
    have hcoord : ∀ (i : Fin n) (l : Fin (p n)), MemLp (fun ω => Z n i ω l) 2 (μP n) := by
      intro i l
      exact (hZ_L2 n i).of_le (((measurable_pi_apply l).comp (hZ_meas n i)).aestronglyMeasurable)
        (Filter.Eventually.of_forall (fun ω => norm_le_pi_norm (Z n i ω) l))
    have hterm : ∀ (i k : Fin n) (l m : Fin (p n)),
        Integrable (fun ω => (u l * u m) * (Z n i ω l * Z n k ω m)) (μP n) := by
      intro i k l m
      exact (MemLp.integrable_mul (hcoord i l) (hcoord k m)).const_mul (u l * u m)
    have hprod : ∀ i k : Fin n, Integrable (fun ω => ξ i ω * ξ k ω) (μP n) := by
      intro i k
      have hpoint : (fun ω => ξ i ω * ξ k ω)
          = fun ω => ∑ l, ∑ m, (u l * u m) * (Z n i ω l * Z n k ω m) := by
        funext ω
        have h1 : ξ i ω = ∑ l, u l * Z n i ω l := rfl
        have h2 : ξ k ω = ∑ m, u m * Z n k ω m := rfl
        rw [h1, h2, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun m _ => ?_))
        ring
      rw [hpoint]
      exact integrable_finset_sum Finset.univ
        (fun l _ => integrable_finset_sum Finset.univ (fun m _ => hterm i k l m))
    have hvalue : ∫ ω, (∑ i, ξ i ω) ^ 2 ∂(μP n) = (n : ℝ) := by
      have hsqexp : ∀ ω : Ω, (∑ i, ξ i ω) ^ 2 = ∑ i, ∑ k, ξ i ω * ξ k ω := by
        intro ω
        rw [sq, Finset.sum_mul_sum]
      calc ∫ ω, (∑ i, ξ i ω) ^ 2 ∂(μP n)
          = ∫ ω, ∑ i, ∑ k, ξ i ω * ξ k ω ∂(μP n) := by simp only [hsqexp]
        _ = ∑ i, ∫ ω, ∑ k, ξ i ω * ξ k ω ∂(μP n) :=
              integral_finset_sum Finset.univ
                (fun i _ => integrable_finset_sum Finset.univ (fun k _ => hprod i k))
        _ = ∑ i, ∑ k, ∫ ω, ξ i ω * ξ k ω ∂(μP n) := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              exact integral_finset_sum Finset.univ (fun k _ => hprod i k)
        _ = ∑ i, ∑ k, (if i = k then (1 : ℝ) else 0) := by
              refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
              by_cases hik : i = k
              · rw [hik]
                rw [show (fun ω => ξ k ω * ξ k ω) = fun ω => ξ k ω ^ 2 from by funext ω; ring]
                simpa using hvar k
              · have hind : ProbabilityTheory.IndepFun (ξ i) (ξ k) (μP n) := hξindep.indepFun hik
                rw [hind.integral_fun_mul_eq_mul_integral (hξmeas i).aestronglyMeasurable
                  (hξmeas k).aestronglyMeasurable, hξmean i, hξmean k, mul_zero]
                simp [hik]
        _ = (n : ℝ) := by
              have hinner : ∀ i : Fin n, (∑ k, (if i = k then (1 : ℝ) else 0)) = 1 := by
                intro i
                rw [Finset.sum_ite_eq]
                simp
              refine Eq.trans (Finset.sum_congr rfl (fun i _ => hinner i)) ?_
              simp
    have hsqint : Integrable (fun ω => (∑ i, ξ i ω) ^ 2) (μP n) := by
      have hsqexp : ∀ ω : Ω, (∑ i, ξ i ω) ^ 2 = ∑ i, ∑ k, ξ i ω * ξ k ω := by
        intro ω
        rw [sq, Finset.sum_mul_sum]
      rw [funext hsqexp]
      exact integrable_finset_sum Finset.univ
        (fun i _ => integrable_finset_sum Finset.univ (fun k _ => hprod i k))
    have hpt : ∀ ω : Ω, |∑ i, ξ i ω| ^ (2 : ℝ) = (∑ i, ξ i ω) ^ 2 := by
      intro ω
      rw [Real.rpow_two, sq_abs]
    have hne : ∫⁻ ω, ENNReal.ofReal ((∑ i, ξ i ω) ^ 2) ∂(μP n) ≠ ⊤ :=
      (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hsqint.aestronglyMeasurable
        (Filter.Eventually.of_forall (fun ω => sq_nonneg _))).mpr hsqint
    have htoReal : (∫⁻ ω, ENNReal.ofReal ((∑ i, ξ i ω) ^ 2) ∂(μP n)).toReal = (n : ℝ) := by
      rw [← Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.integral_eq_lintegral_toReal_of_nonneg
        (Filter.Eventually.of_forall (fun ω => sq_nonneg _)) hsqint]
      exact hvalue
    have hlin : ∫⁻ ω, ENNReal.ofReal ((∑ i, ξ i ω) ^ 2) ∂(μP n) = ENNReal.ofReal (n : ℝ) := by
      rw [← ENNReal.ofReal_toReal hne, htoReal]
    have hL : ∫⁻ ω, ENNReal.ofReal (|∑ i, ξ i ω| ^ (2 : ℝ)) ∂(μP n) = ENNReal.ofReal (n : ℝ) := by
      rw [show (∫⁻ ω, ENNReal.ofReal (|∑ i, ξ i ω| ^ (2 : ℝ)) ∂(μP n))
          = ∫⁻ ω, ENNReal.ofReal ((∑ i, ξ i ω) ^ 2) ∂(μP n) from by simp only [hpt]]
      exact hlin
    have hpow : ENNReal.rpow (ENNReal.ofReal (n : ℝ)) (1 / 2)
        = ENNReal.ofReal (Real.sqrt (n : ℝ)) := by
      rw [show ENNReal.rpow (ENNReal.ofReal (n : ℝ)) (1 / 2)
          = ENNReal.ofReal ((n : ℝ) ^ (1 / 2 : ℝ)) from
            ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg n) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      congr 1
      rw [Real.sqrt_eq_rpow]
    simp only [LqNorm]
    rw [hL, hpow]
  have hros : ∀ r : ℝ, 2 < r →
      LqNorm (fun ω => ∑ i, ξ i ω) r (μP n)
        ≤ ENNReal.ofReal (cR * (r / max (Real.log r) 1) *
            max (Real.sqrt (n : ℝ)) ((n : ℝ) ^ (1 / r) * (C2 * r))) := by
    intro r hr
    have hr1 : 1 ≤ r := by linarith
    have hfin : ∀ j : Fin n, ∫⁻ ω, ENNReal.ofReal (|ξ j ω| ^ r) ∂(μP n) ≠ ⊤ := by
      intro j htop
      have hm := hmom j r hr1
      simp only [LqNorm] at hm
      have htop' : (⊤ : ℝ≥0∞).rpow (1 / r) = ⊤ :=
        ENNReal.top_rpow_of_pos (one_div_pos.mpr (by linarith : (0 : ℝ) < r))
      rw [htop, htop'] at hm
      exact absurd hm (not_le.mpr ENNReal.ofReal_lt_top)
    have hint : ∀ j : Fin n, Integrable (fun ω => |ξ j ω| ^ r) (μP n) := by
      intro j
      have hmeas : AEStronglyMeasurable (fun ω => |ξ j ω| ^ r) (μP n) := by
        have hcont : Continuous (fun x : ℝ => |x| ^ r) :=
          (Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ r)).comp continuous_abs
        exact hcont.comp_aestronglyMeasurable (hξmeas j).aestronglyMeasurable
      have hnn : 0 ≤ᶠ[ae (μP n)] (fun ω => |ξ j ω| ^ r) :=
        Filter.Eventually.of_forall (fun ω => Real.rpow_nonneg (abs_nonneg (ξ j ω)) r)
      exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmeas hnn).mp (hfin j)
    have hn1n : 1 ≤ n := le_trans hn0 hn
    have hB : LqNorm (fun ω => (∑ j, |ξ j ω| ^ r) ^ (1 / r)) r (μP n)
        ≤ ENNReal.ofReal ((n : ℝ) ^ (1 / r) * (C2 * r)) := by
      have hr0 : 0 ≤ r := le_of_lt (by linarith : (0 : ℝ) < r)
      have hc2r : (0 : ℝ) ≤ C2 * r := mul_nonneg hC2.le hr0
      have hpt : ∀ ω : Ω, |(∑ j, |ξ j ω| ^ r) ^ (1 / r)| ^ r = ∑ j, |ξ j ω| ^ r := by
        intro ω
        have hS0 : (0 : ℝ) ≤ ∑ j, |ξ j ω| ^ r :=
          Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (abs_nonneg (ξ j ω)) r)
        rw [abs_of_nonneg (Real.rpow_nonneg hS0 (1 / r)),
          ← Real.rpow_mul hS0 (1 / r) r, one_div,
          inv_mul_cancel₀ (ne_of_gt (by linarith : (0 : ℝ) < r)), Real.rpow_one]
      have hterm : ∀ j : Fin n, ∫⁻ ω, ENNReal.ofReal (|ξ j ω| ^ r) ∂(μP n)
          ≤ ENNReal.ofReal ((C2 * r) ^ r) := by
        intro j
        have hm := hmom j r hr1
        simp only [LqNorm] at hm
        have h1 : ((∫⁻ ω, ENNReal.ofReal (|ξ j ω| ^ r) ∂(μP n)) ^ (1 / r)) ^ r
            = ∫⁻ ω, ENNReal.ofReal (|ξ j ω| ^ r) ∂(μP n) := by
          rw [← ENNReal.rpow_mul, one_div,
            inv_mul_cancel₀ (ne_of_gt (by linarith : (0 : ℝ) < r)), ENNReal.rpow_one]
        calc ∫⁻ ω, ENNReal.ofReal (|ξ j ω| ^ r) ∂(μP n)
            = ((∫⁻ ω, ENNReal.ofReal (|ξ j ω| ^ r) ∂(μP n)) ^ (1 / r)) ^ r := h1.symm
          _ ≤ (ENNReal.ofReal (C2 * r)) ^ r := ENNReal.rpow_le_rpow hm hr0
          _ = ENNReal.ofReal ((C2 * r) ^ r) := ENNReal.ofReal_rpow_of_nonneg hc2r hr0
      have hmeas : ∀ j : Fin n, Measurable (fun ω => ENNReal.ofReal (|ξ j ω| ^ r)) := by
        intro j
        have hcont : Continuous (fun x : ℝ => |x| ^ r) :=
          (Real.continuous_rpow_const hr0).comp continuous_abs
        exact (hcont.measurable.comp (hξmeas j)).ennreal_ofReal
      have hsum_pt : ∀ ω : Ω, ENNReal.ofReal (∑ j, |ξ j ω| ^ r)
          = ∑ j, ENNReal.ofReal (|ξ j ω| ^ r) := fun ω =>
        ENNReal.ofReal_sum_of_nonneg (fun j _ => Real.rpow_nonneg (abs_nonneg (ξ j ω)) r)
      have hlint : ∫⁻ ω, ENNReal.ofReal (∑ j, |ξ j ω| ^ r) ∂(μP n)
          = ∑ j : Fin n, ∫⁻ ω, ENNReal.ofReal (|ξ j ω| ^ r) ∂(μP n) := by
        calc ∫⁻ ω, ENNReal.ofReal (∑ j, |ξ j ω| ^ r) ∂(μP n)
            = ∫⁻ ω, ∑ j : Fin n, ENNReal.ofReal (|ξ j ω| ^ r) ∂(μP n) := by
                simp only [hsum_pt]
          _ = ∑ j : Fin n, ∫⁻ ω, ENNReal.ofReal (|ξ j ω| ^ r) ∂(μP n) :=
                lintegral_finset_sum Finset.univ (fun j _ => hmeas j)
      have hbound : ∑ j : Fin n, ∫⁻ ω, ENNReal.ofReal (|ξ j ω| ^ r) ∂(μP n)
          ≤ ENNReal.ofReal ((n : ℝ) * (C2 * r) ^ r) := by
        calc ∑ j : Fin n, ∫⁻ ω, ENNReal.ofReal (|ξ j ω| ^ r) ∂(μP n)
            ≤ ∑ _j : Fin n, ENNReal.ofReal ((C2 * r) ^ r) :=
                Finset.sum_le_sum (fun j _ => hterm j)
          _ = ENNReal.ofReal ((n : ℝ) * (C2 * r) ^ r) := by
              rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => Real.rpow_nonneg hc2r r)]
              congr 1
              simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hnr : (0 : ℝ) ≤ (n : ℝ) * (C2 * r) ^ r :=
        mul_nonneg (Nat.cast_nonneg n) (Real.rpow_nonneg hc2r r)
      have hr1' : 0 ≤ 1 / r := by positivity
      simp only [LqNorm]
      calc (∫⁻ ω, ENNReal.ofReal (|(∑ j, |ξ j ω| ^ r) ^ (1 / r)| ^ r) ∂(μP n)) ^ (1 / r)
          = (∫⁻ ω, ENNReal.ofReal (∑ j, |ξ j ω| ^ r) ∂(μP n)) ^ (1 / r) := by
              simp only [hpt]
        _ = (∑ j : Fin n, ∫⁻ ω, ENNReal.ofReal (|ξ j ω| ^ r) ∂(μP n)) ^ (1 / r) := by
              rw [hlint]
        _ ≤ (ENNReal.ofReal ((n : ℝ) * (C2 * r) ^ r)) ^ (1 / r) :=
              ENNReal.rpow_le_rpow hbound hr1'
        _ = ENNReal.ofReal ((n : ℝ) ^ (1 / r) * (C2 * r)) := by
              rw [ENNReal.ofReal_rpow_of_nonneg hnr hr1']
              congr 1
              rw [Real.mul_rpow (Nat.cast_nonneg n) (Real.rpow_nonneg hc2r r)]
              congr 1
              rw [← Real.rpow_mul hc2r r (1 / r), one_div,
                mul_inv_cancel₀ (ne_of_gt (by linarith : (0 : ℝ) < r)), Real.rpow_one]
    have hcite := (hRos r n Ω (μP n) hr1 hn1n (hμP n) ξ hξmeas hξindep hint).2 ⟨hr, hξmean⟩
    have hAmax : LqNorm (fun ω => ∑ i, ξ i ω) 2 (μP n)
        ≤ ENNReal.ofReal (max (Real.sqrt (n : ℝ)) ((n : ℝ) ^ (1 / r) * (C2 * r))) :=
      le_trans hsum2 (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    have hBmax : LqNorm (fun ω => (∑ j, |ξ j ω| ^ r) ^ (1 / r)) r (μP n)
        ≤ ENNReal.ofReal (max (Real.sqrt (n : ℝ)) ((n : ℝ) ^ (1 / r) * (C2 * r))) :=
      le_trans hB (ENNReal.ofReal_le_ofReal (le_max_right _ _))
    refine le_trans hcite ?_
    refine le_trans (mul_le_mul_left' (max_le hAmax hBmax) _) ?_
    rw [ENNReal.ofReal_mul (mul_nonneg hcR.le
      (div_nonneg (by linarith) (le_trans zero_le_one (le_max_right (Real.log r) 1))))]
  have hhom : ∀ (c : ℝ), 0 ≤ c → ∀ (g : Ω → ℝ) (r : ℝ), 0 < r →
      LqNorm (fun ω => c * g ω) r (μP n) = ENNReal.ofReal c * LqNorm g r (μP n) := by
    intro c hc g r hr
    have hr1 : 0 ≤ 1 / r := by positivity
    have hcr : 0 ≤ c ^ r := Real.rpow_nonneg hc r
    have hpt : ∀ ω : Ω, |c * g ω| ^ r = c ^ r * |g ω| ^ r := by
      intro ω
      rw [abs_mul, abs_of_nonneg hc, Real.mul_rpow hc (abs_nonneg (g ω))]
    have hlim : ∫⁻ ω, ENNReal.ofReal (|c * g ω| ^ r) ∂(μP n)
        = ENNReal.ofReal (c ^ r) * ∫⁻ ω, ENNReal.ofReal (|g ω| ^ r) ∂(μP n) := by
      calc ∫⁻ ω, ENNReal.ofReal (|c * g ω| ^ r) ∂(μP n)
          = ∫⁻ ω, ENNReal.ofReal (c ^ r * |g ω| ^ r) ∂(μP n) := by simp only [hpt]
        _ = ∫⁻ ω, ENNReal.ofReal (c ^ r) * ENNReal.ofReal (|g ω| ^ r) ∂(μP n) := by
              simp only [ENNReal.ofReal_mul hcr]
        _ = ENNReal.ofReal (c ^ r) * ∫⁻ ω, ENNReal.ofReal (|g ω| ^ r) ∂(μP n) :=
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    have hpow : ENNReal.ofReal (c ^ r) ^ (1 / r) = ENNReal.ofReal c := by
      have h1 : ENNReal.ofReal (c ^ r) ^ (1 / r) = ENNReal.ofReal ((c ^ r) ^ (1 / r)) := by
        first
          | rw [ENNReal.ofReal_rpow_of_nonneg hcr hr1]
          | rw [← ENNReal.ofReal_rpow_of_nonneg hcr hr1]
      rw [h1, ← Real.rpow_mul hc r (1 / r), one_div, mul_inv_cancel₀ (ne_of_gt hr),
        Real.rpow_one]
    simp only [LqNorm]
    rw [hlim]
    change (ENNReal.ofReal (c ^ r) * ∫⁻ ω, ENNReal.ofReal (|g ω| ^ r) ∂(μP n)) ^ (1 / r)
      = ENNReal.ofReal c * (∫⁻ ω, ENNReal.ofReal (|g ω| ^ r) ∂(μP n)) ^ (1 / r)
    rw [ENNReal.mul_rpow_of_nonneg _ _ hr1, hpow]
  have hqpos : 0 < q := by linarith
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := by
    have h2 : (2 : ℝ) ≤ Real.sqrt (n : ℝ) := le_trans hq2 hqle
    linarith
  have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt hsqrt_pos
  have hAC : ENNReal.ofReal ((Real.sqrt (n : ℝ))⁻¹) * ENNReal.ofReal (Real.sqrt (n : ℝ)) = 1 := by
    rw [← ENNReal.ofReal_mul' (le_of_lt hsqrt_pos), inv_mul_cancel₀ hsqrt_ne, ENNReal.ofReal_one]
  rw [show (fun ω => s⁻¹ * Svec p X mu n ω j)
      = (fun ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ i, ξ i ω) from funext hVform]
  rw [hhom ((Real.sqrt (n : ℝ))⁻¹) (inv_nonneg.mpr hsqrt_pos.le) (fun ω => ∑ i, ξ i ω) q hqpos]
  rcases lt_or_eq_of_le hq2 with hq_gt | hq_eq
  · have hn1 : 1 ≤ n := le_trans hn0 hn
    have hpre : (q / max (Real.log q) 1) * (n : ℝ) ^ (-(1 / 2 : ℝ) + 1 / q) ≤ 3 :=
      statopia_math_node_3045670844_0a1a6b78 n q hn1 hq2 hqle
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have h1n : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      linarith
    have hsplit : (Real.sqrt (n : ℝ))⁻¹ * (n : ℝ) ^ (1 / q)
        = (n : ℝ) ^ (-(1 / 2 : ℝ) + 1 / q) := by
      rw [Real.sqrt_eq_rpow]
      simp only [Real.rpow_def_of_pos hnpos]
      rw [← Real.exp_neg, ← Real.exp_add]
      congr 1
      ring
    have hA0 : 0 ≤ cR * (q / max (Real.log q) 1) :=
      mul_nonneg hcR.le (div_nonneg hqpos.le (le_trans zero_le_one (le_max_right (Real.log q) 1)))
    have hmax : max (Real.sqrt (n : ℝ)) ((n : ℝ) ^ (1 / q) * (C2 * q))
        ≤ Real.sqrt (n : ℝ) + (n : ℝ) ^ (1 / q) * (C2 * q) := by
      refine max_le ?_ ?_
      · have h0 : (0 : ℝ) ≤ (n : ℝ) ^ (1 / q) * (C2 * q) :=
          mul_nonneg (Real.rpow_nonneg (le_of_lt hnpos) (1 / q)) (mul_nonneg hC2.le hqpos.le)
        linarith
      · linarith [hsqrt_pos]
    have hstep : (Real.sqrt (n : ℝ))⁻¹ *
        (cR * (q / max (Real.log q) 1) *
          max (Real.sqrt (n : ℝ)) ((n : ℝ) ^ (1 / q) * (C2 * q)))
        ≤ cR * (q / max (Real.log q) 1) +
          cR * (q / max (Real.log q) 1) *
            ((Real.sqrt (n : ℝ))⁻¹ * ((n : ℝ) ^ (1 / q) * (C2 * q))) := by
      have e1 : (Real.sqrt (n : ℝ))⁻¹ *
          (cR * (q / max (Real.log q) 1) *
            max (Real.sqrt (n : ℝ)) ((n : ℝ) ^ (1 / q) * (C2 * q)))
          = cR * (q / max (Real.log q) 1) *
            ((Real.sqrt (n : ℝ))⁻¹ *
              max (Real.sqrt (n : ℝ)) ((n : ℝ) ^ (1 / q) * (C2 * q))) := by
        ring
      have e2 : (Real.sqrt (n : ℝ))⁻¹ *
            max (Real.sqrt (n : ℝ)) ((n : ℝ) ^ (1 / q) * (C2 * q))
          ≤ (Real.sqrt (n : ℝ))⁻¹ *
            (Real.sqrt (n : ℝ) + (n : ℝ) ^ (1 / q) * (C2 * q)) :=
        mul_le_mul_of_nonneg_left hmax (le_of_lt (inv_pos.mpr hsqrt_pos))
      have e3 : (Real.sqrt (n : ℝ))⁻¹ *
            (Real.sqrt (n : ℝ) + (n : ℝ) ^ (1 / q) * (C2 * q))
          = 1 + (Real.sqrt (n : ℝ))⁻¹ * ((n : ℝ) ^ (1 / q) * (C2 * q)) := by
        rw [mul_add, inv_mul_cancel₀ hsqrt_ne]
      rw [e1]
      calc cR * (q / max (Real.log q) 1) *
              ((Real.sqrt (n : ℝ))⁻¹ *
                max (Real.sqrt (n : ℝ)) ((n : ℝ) ^ (1 / q) * (C2 * q)))
          ≤ cR * (q / max (Real.log q) 1) *
              ((Real.sqrt (n : ℝ))⁻¹ *
                (Real.sqrt (n : ℝ) + (n : ℝ) ^ (1 / q) * (C2 * q))) :=
            mul_le_mul_of_nonneg_left e2 hA0
        _ = cR * (q / max (Real.log q) 1) *
              (1 + (Real.sqrt (n : ℝ))⁻¹ * ((n : ℝ) ^ (1 / q) * (C2 * q))) := by rw [e3]
        _ = cR * (q / max (Real.log q) 1) +
              cR * (q / max (Real.log q) 1) *
                ((Real.sqrt (n : ℝ))⁻¹ * ((n : ℝ) ^ (1 / q) * (C2 * q))) := by
            rw [mul_add, mul_one]
    have h2q : cR * (q / max (Real.log q) 1) ≤ cR * q :=
      mul_le_mul_of_nonneg_left (div_le_self hqpos.le (le_max_right _ _)) hcR.le
    have h4q : cR * (q / max (Real.log q) 1) *
          ((Real.sqrt (n : ℝ))⁻¹ * ((n : ℝ) ^ (1 / q) * (C2 * q)))
        ≤ 3 * (cR * C2) * q := by
      have h4' : (q / max (Real.log q) 1) *
            ((Real.sqrt (n : ℝ))⁻¹ * (n : ℝ) ^ (1 / q)) ≤ 3 := by
        rw [hsplit]
        exact hpre
      have hpos : (0 : ℝ) ≤ cR * (C2 * q) :=
        mul_nonneg hcR.le (mul_nonneg hC2.le hqpos.le)
      have h5 := mul_le_mul_of_nonneg_left h4' hpos
      calc cR * (q / max (Real.log q) 1) *
            ((Real.sqrt (n : ℝ))⁻¹ * ((n : ℝ) ^ (1 / q) * (C2 * q)))
          = cR * (C2 * q) *
              ((q / max (Real.log q) 1) *
                ((Real.sqrt (n : ℝ))⁻¹ * (n : ℝ) ^ (1 / q))) := by ring
        _ ≤ cR * (C2 * q) * 3 := h5
        _ = 3 * (cR * C2) * q := by ring
    have hW : (Real.sqrt (n : ℝ))⁻¹ *
        (cR * (q / max (Real.log q) 1) *
          max (Real.sqrt (n : ℝ)) ((n : ℝ) ^ (1 / q) * (C2 * q)))
        ≤ max (cR * (1 + 3 * C2)) 1 * q := by
      calc (Real.sqrt (n : ℝ))⁻¹ *
            (cR * (q / max (Real.log q) 1) *
              max (Real.sqrt (n : ℝ)) ((n : ℝ) ^ (1 / q) * (C2 * q)))
          ≤ cR * (q / max (Real.log q) 1) +
              cR * (q / max (Real.log q) 1) *
                ((Real.sqrt (n : ℝ))⁻¹ * ((n : ℝ) ^ (1 / q) * (C2 * q))) := hstep
        _ ≤ cR * q + 3 * (cR * C2) * q := by linarith [h2q, h4q]
        _ = cR * (1 + 3 * C2) * q := by ring
        _ ≤ max (cR * (1 + 3 * C2)) 1 * q :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hqpos.le
    calc ENNReal.ofReal ((Real.sqrt (n : ℝ))⁻¹) * LqNorm (fun ω => ∑ i, ξ i ω) q (μP n)
        ≤ ENNReal.ofReal ((Real.sqrt (n : ℝ))⁻¹) *
            ENNReal.ofReal (cR * (q / max (Real.log q) 1) *
              max (Real.sqrt (n : ℝ)) ((n : ℝ) ^ (1 / q) * (C2 * q))) :=
          mul_le_mul_left' (hros q hq_gt) _
      _ = ENNReal.ofReal ((Real.sqrt (n : ℝ))⁻¹ *
            (cR * (q / max (Real.log q) 1) *
              max (Real.sqrt (n : ℝ)) ((n : ℝ) ^ (1 / q) * (C2 * q)))) := by
          rw [ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hsqrt_pos))]
      _ ≤ ENNReal.ofReal (max (cR * (1 + 3 * C2)) 1 * q) := ENNReal.ofReal_le_ofReal hW
  · rw [← hq_eq]
    calc ENNReal.ofReal ((Real.sqrt (n : ℝ))⁻¹) * LqNorm (fun ω => ∑ i, ξ i ω) 2 (μP n)
        ≤ ENNReal.ofReal ((Real.sqrt (n : ℝ))⁻¹) * ENNReal.ofReal (Real.sqrt (n : ℝ)) :=
          mul_le_mul_left' hsum2 _
      _ = 1 := hAC
      _ ≤ ENNReal.ofReal (max (cR * (1 + 3 * C2)) 1 * 2) := by
          rw [← ENNReal.ofReal_one]
          apply ENNReal.ofReal_le_ofReal
          have h1 : (1 : ℝ) ≤ max (cR * (1 + 3 * C2)) 1 := le_max_right _ _
          nlinarith [h1]
  /- @proof-region region.target-node.session.8f2a725f9530f40b end -/

end Statlib.Imported

