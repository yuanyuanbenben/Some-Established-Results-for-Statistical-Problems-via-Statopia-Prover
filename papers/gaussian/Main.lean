import ProverJobs.paper_fresh_20261028t224543381z_gaussian.ExternalNodes.Node_11878c4ffd7b4b0ab9fa
import ProverJobs.paper_fresh_20261028t224543381z_gaussian.ExternalNodes.Node_7ffce43095914ff89c69
import ProverJobs.paper_fresh_20261028t224543381z_gaussian.Vocabulary
import ProverJobs.paper_fresh_20261028t224543381z_gaussian.ProvedNodes
import ProverJobs.paper_fresh_20261028t224543381z_gaussian.Base

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace Statlib.Imported

theorem Theorem_3_1_Gaussian_approximation_THM_G :
    ∀ (delta : ℝ), 0 < delta → delta < 1 / 2 →
    ∀ (a : ℝ), 0 < a → a < 1 / 2 →
    ∀ (c0 alpha cvar ccirc eps0 Ccor : ℝ),
      0 < c0 → 0 < alpha → 0 < cvar → 0 < ccirc → ccirc < 1 →
      0 < eps0 → eps0 < 1 → 0 < Ccor →
    ∃ Cbound : ℝ, 0 < Cbound ∧
    ∀ (Omega : Type) [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
        (p : ℕ → ℕ) (hp : ∀ n, 0 < p n)
        (Sigma : ∀ n, Matrix (Fin (p n)) (Fin (p n)) ℝ) (hSigma : ∀ n, (Sigma n).PosSemidef)
        (mu : ∀ n, Fin (p n) → ℝ),

    ∀ (Z : ∀ n, Fin n → Omega → Fin (p n) → ℝ),
      (∀ n i, Measurable (Z n i)) →
      (∀ n, iIndepFun (fun i => Z n i) P) →
      (∀ n (i i' : Fin n), IdentDistrib (Z n i) (Z n i') P P) →
      (∀ n (i : Fin n) (j : Fin (p n)), Integrable (fun ω => Z n i ω j) P) →
      (∀ n (i : Fin n) (j : Fin (p n)), ∫ ω, Z n i ω j ∂P = 0) →
      (∀ n (i : Fin n) (k l : Fin (p n)),
        Integrable (fun ω => Z n i ω k * Z n i ω l) P) →
      (∀ n (i : Fin n) (k l : Fin (p n)),
        ∫ ω, Z n i ω k * Z n i ω l ∂P = if k = l then 1 else 0) →
      (∀ n (i : Fin n) (u : Fin (p n) → ℝ), (∑ j : Fin (p n), (u j) ^ 2) = 1 →
        Statlib.StatFoundation.Vocabulary.subexponentialOrliczNorm
          (fun ω => ∑ j : Fin (p n), u j * Z n i ω j) P ≤ ENNReal.ofReal c0) →
    ∀ (tau : ℕ → ℝ), (∀ n, 0 ≤ tau n) → (∀ n, tau n < 1) →
      (∃ ctau : ℝ, 0 < ctau ∧
        ∀ᶠ n in atTop, ctau ≤ (1 - tau n) * Real.sqrt (Real.log (n : ℝ))) →
    ∀ (perm : ∀ n, Equiv.Perm (Fin (p n))),
      (∀ n (i i' : Fin (p n)), (i : ℕ) ≤ (i' : ℕ) →
        sigmaSD p Sigma n (perm n i') ≤ sigmaSD p Sigma n (perm n i)) →
      (∀ n (j : Fin (p n)), 0 < sigmaSD p Sigma n j) →
      (∀ n (j : Fin (p n)), kN (p n) a n ≤ (j : ℕ) + 1 →
        sigmaSD p Sigma n (perm n j) ≤ cvar * ((j : ℝ) + 1) ^ (-alpha)) →
      (∀ n (j : Fin (p n)), (j : ℕ) + 1 ≤ kN (p n) a n →
        ccirc * ((j : ℝ) + 1) ^ (-alpha) ≤ sigmaSD p Sigma n (perm n j)) →
      (∀ n (i j : Fin (ellN (p n) n)), i ≠ j →
        corrEntry p Sigma perm n (ellN (p n) n) (ellN_le_p (p n) n) i j ≤ 1 - eps0) →
      (∀ n, (corrPos p Sigma perm n (ellN (p n) n) (ellN_le_p (p n) n)).PosSemidef) →
      (∀ n, (∑ i : Fin (ellN (p n) n), ∑ j : Fin (ellN (p n) n),
        (if i < j then corrPos p Sigma perm n (ellN (p n) n) (ellN_le_p (p n) n) i j else 0))
        ≤ Ccor * ((ellN (p n) n : ℕ) : ℝ)) →

    ∀ (gaussLaw : ∀ n, Measure (Fin (p n) → ℝ)),
      (∀ n, IsProbabilityMeasure (gaussLaw n)) →
      (∀ n, IsGaussian (gaussLaw n)) →
      (∀ n (j : Fin (p n)), Integrable (fun s : Fin (p n) → ℝ => s j) (gaussLaw n)) →
      (∀ n (j : Fin (p n)), ∫ s, s j ∂(gaussLaw n) = 0) →
      (∀ n (k l : Fin (p n)),
        Integrable (fun s : Fin (p n) → ℝ => s k * s l) (gaussLaw n)) →
      (∀ n (k l : Fin (p n)), ∫ s, s k * s l ∂(gaussLaw n) = Sigma n k l) →
    ∃ n0 : ℕ, 1 ≤ n0 ∧ ∀ n : ℕ, n0 ≤ n →
      dK (P.map (fun ω => Mstat (hp n) (sigmaSD p Sigma n) (tau n)
              (fun j => Scoord p Sigma hSigma mu Z n j ω)))
          ((gaussLaw n).map (fun s => Mstat (hp n) (sigmaSD p Sigma n) (tau n) s))
        ≤ Cbound * (n : ℝ) ^ (-(1 / 2 : ℝ) + delta)
:= by
  /- @proof-region region.root.b49ab0343b06 begin -/
  intro delta hdelta hdeltalt a ha halt c0 alpha cvar ccirc eps0 Ccor hc0 halpha hcvar hccirc hccirclt heps0 heps0lt hCcor
  obtain ⟨cII, hcIIpos, hcII⟩ := PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.paper_e9c0500526fe4a15b7473a5f9efc21ed delta a c0 alpha cvar ccirc eps0 Ccor hdelta hdeltalt ha halt hc0 halpha hcvar hccirc hccirclt heps0 heps0lt hCcor; obtain ⟨c1, c2, hc1, hc2, hmain⟩ := PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.paper_82217ff9ed45452ea25ea7588fe2ef01.{0} a c0 alpha cvar ccirc eps0 Ccor ⟨ha, halt⟩ hc0 halpha hcvar ⟨hccirc, hccirclt⟩ ⟨heps0, heps0lt⟩ hCcor (δ := delta) ⟨hdelta, hdeltalt⟩; refine ⟨c1 + cII + c2, by linarith, ?_⟩
  intro Omega instOmega P instP p hp Sigma hSigma mu
    Z hZmeas hZindep hZident hZint hZmean hZint2 hZcov hZsubg
    tau htau0 htau1 htauN perm hperm hsigpos hub hlb hRoff hRpsd hRsum
    gaussLaw hgprob hggauss hgint1 hgmean hgint2 hgcov
  have hp1 : ∀ n, 1 ≤ p n := fun n => Nat.succ_le_of_lt (hp n)
  have htau1' : ∀ n, 0 ≤ tau n ∧ tau n < 1 := fun n => ⟨htau0 n, htau1 n⟩
  have htau2' : ∃ c : ℝ, 0 < c ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → c ≤ (1 - tau n) * Real.sqrt (Real.log (n : ℝ)) := by
    obtain ⟨ct, hct0, hctev⟩ := htauN
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hctev
    exact ⟨ct, hct0, max N 1, le_max_right _ _, fun n hn => hN n (le_trans (le_max_left _ _) hn)⟩
  have hstdprob : ∀ n, IsProbabilityMeasure
      (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.stdGaussianLaw (p n)) :=
    fun n => by
      show IsProbabilityMeasure (Measure.pi (fun _ : Fin (p n) => gaussianReal 0 1))
      infer_instance
  have hZmeas' : ∀ (n : ℕ) (i : Fin n) (j : Fin (p n)), Measurable (fun om => Z n i om j) :=
    fun n i j => (measurable_pi_apply j).comp (hZmeas n i)
  have hXvec_meas : ∀ (n : ℕ) (i : Fin n) (j : Fin (p n)),
      Measurable (fun ω => Xvec p Sigma hSigma mu Z n i ω j) := by
    intro n i j
    have hcont : Continuous (Matrix.mulVecLin (Matrix.PosSemidef.sqrt (hSigma n))) :=
      LinearMap.continuous_of_finiteDimensional _
    have hmul : Measurable
        (fun ω : Omega => Matrix.mulVec (Matrix.PosSemidef.sqrt (hSigma n)) (Z n i ω)) :=
      hcont.measurable.comp (hZmeas n i)
    have hcoord : Measurable
        (fun ω : Omega => (Matrix.mulVec (Matrix.PosSemidef.sqrt (hSigma n)) (Z n i ω)) j) :=
      (measurable_pi_apply j).comp hmul
    simpa only [Xvec] using hcoord.add measurable_const
  have hellN : ∀ n : ℕ, ellN (p n) n =
      PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.ellIdx p n :=
    fun n => rfl
  have hkN : ∀ n : ℕ, kN (p n) a n =
      PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n :=
    fun n => rfl
  have hXsum : ∀ (n : ℕ) (i : Fin n) (ω : Omega) (j : Fin (p n)),
      Xvec p Sigma hSigma mu Z n i ω j
        = mu n j + ∑ k : Fin (p n),
            (Matrix.PosSemidef.sqrt (hSigma n)) j k * Z n i ω k := by
    intro n i ω j
    have hdot : Matrix.mulVec (Matrix.PosSemidef.sqrt (hSigma n)) (Z n i ω) j
        = ∑ k : Fin (p n), (Matrix.PosSemidef.sqrt (hSigma n)) j k * Z n i ω k := rfl
    simp only [Xvec, Pi.add_apply, hdot]
    exact add_comm _ _
  have hmeanX : ∀ (n : ℕ) (i : Fin n) (j : Fin (p n)),
      ∫ ω, Xvec p Sigma hSigma mu Z n i ω j ∂P = mu n j := by
    intro n i j
    have hInt : ∀ k : Fin (p n), Integrable (fun ω : Omega =>
        (Matrix.PosSemidef.sqrt (hSigma n)) j k * Z n i ω k) P :=
      fun k => (hZint n i k).const_mul _
    simp only [hXsum]
    rw [MeasureTheory.integral_add (integrable_const _)
      (MeasureTheory.integrable_finset_sum Finset.univ (fun k _ => hInt k))]
    rw [MeasureTheory.integral_finset_sum Finset.univ (fun k _ => hInt k)]
    simp only [MeasureTheory.integral_const_mul, hZmean n i, mul_zero, Finset.sum_const_zero,
      add_zero]
    simp
  
  have hSnVec_eq : ∀ (n : ℕ) (ω : Omega) (j : Fin (p n)),
      PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.SnVec
          (Xvec p Sigma hSigma mu Z n) (mu n) ω j
        = Scoord p Sigma hSigma mu Z n j ω := by
    intro n ω j
    simp only [PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.SnVec,
      Scoord]
    ring
  have hvarCore : ∀ (n : ℕ) (hn : 1 ≤ n) (j : Fin (p n)),
      Integrable (fun ω => (Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω j - mu n j) ^ 2) P ∧
        ∫ ω, (Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω j - mu n j) ^ 2 ∂P = Sigma n j j := by
    intro n hn j
    have h := (statopia_math_node_1229864006_d7a2d2e8 Omega P p Sigma hSigma mu Z hZint2 hZcov).1 n hn j
    have hsub : ∀ ω : Omega, Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω j - mu n j
        = (Matrix.mulVec (Matrix.PosSemidef.sqrt (hSigma n)) (Z n ⟨0, hn⟩ ω)) j := by
      intro ω
      simp only [Xvec, Pi.add_apply, add_sub_cancel_right]
    exact ⟨by simpa only [hsub] using h.1, by simpa only [hsub] using h.2⟩
  have hcovCore : ∀ (n : ℕ) (hn : 1 ≤ n) (i j : Fin (p n)),
      Integrable (fun ω => (Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω i - mu n i) *
        (Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω j - mu n j)) P ∧
        ∫ ω, (Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω i - mu n i) *
          (Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω j - mu n j) ∂P = Sigma n i j := by
    intro n hn i j
    have h := (statopia_math_node_1229864006_d7a2d2e8 Omega P p Sigma hSigma mu Z hZint2 hZcov).2 n hn i j
    have hsubi : ∀ ω : Omega, Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω i - mu n i
        = (Matrix.mulVec (Matrix.PosSemidef.sqrt (hSigma n)) (Z n ⟨0, hn⟩ ω)) i := by
      intro ω
      simp only [Xvec, Pi.add_apply, add_sub_cancel_right]
    have hsubj : ∀ ω : Omega, Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω j - mu n j
        = (Matrix.mulVec (Matrix.PosSemidef.sqrt (hSigma n)) (Z n ⟨0, hn⟩ ω)) j := by
      intro ω
      simp only [Xvec, Pi.add_apply, add_sub_cancel_right]
    exact ⟨by simpa only [hsubi, hsubj] using h.1,
      by simpa only [hsubi, hsubj] using h.2⟩
  
  
  
  
  obtain ⟨nII, hnII, hIIb⟩ :=
    hcII p hp1 (fun _ => Omega) (fun _ => P) (fun _ => inferInstance) mu Sigma hSigma Z hZmeas'
      (fun m => Xvec p Sigma hSigma mu Z m)
      (fun n i om j => by
        simp only [Xvec, PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sqrtCovMat]
        ring)
      hZindep hZident
      (fun n hn j => ⟨hZint n ⟨0, hn⟩ j, hZmean n ⟨0, hn⟩ j⟩)
      (fun n hn i j => ⟨hZint2 n ⟨0, hn⟩ i j, hZcov n ⟨0, hn⟩ i j⟩)
      (fun n hn u hu => by
        have hnn : 0 ≤ ∑ j : Fin (p n), u j ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (u i)
        have h1 : ∑ j : Fin (p n), u j ^ 2 = 1 := by
          have h2 : (Real.sqrt (∑ j : Fin (p n), u j ^ 2)) ^ 2 = 1 := by
            rw [hu]
            norm_num
          rwa [Real.sq_sqrt hnn] at h2
        simpa only [Statlib.StatFoundation.Vocabulary.subexponentialOrliczNorm]
          using hZsubg n ⟨0, hn⟩ u h1)
      (fun n hn j => hXvec_meas n ⟨0, hn⟩ j)
      (fun n hn j => hvarCore n hn j)
      (fun n j => by
        simpa only [PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf,
          sigmaSD] using hsigpos n j)
      perm
      (fun n i i' h => by
        simpa only [PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf,
          sigmaSD] using hperm n i i' h)
      (fun n => ⟨
        (fun j hj => by
          simpa only [PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf,
            sigmaSD, Nat.cast_add_one]
            using hub n j (by simpa only [hkN] using hj)),
        (fun j => by
          have h2 : (j : ℕ) + 1 ≤
              PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n := by
            have := j.isLt
            omega
          have hj : ((PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.posIn
              (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx_le p a n) j :
                Fin (p n)) : ℕ) + 1 ≤ kN (p n) a n := by
            simpa only [hkN,
              PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.posIn]
              using h2
          simpa only [PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf,
            sigmaSD, Nat.cast_add_one,
            PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.posIn]
            using hlb n (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.posIn
              (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx_le p a n) j) hj)⟩)
      (fun n i j hij => hRoff n i j hij) (fun n => hRpsd n) (fun n => hRsum n)
      tau htau1' htau2' (fun m => Fin (p m) → ℝ)
      (fun m => PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.stdGaussianLaw (p m))
      hstdprob (fun _ => id) (fun _ => measurable_id) (fun _ => Measure.map_id)
  let M : PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.Model Omega P a :=
    { p := p
      hp := hp1
      X := Xvec p Sigma hSigma mu Z
      hX := fun n i => measurable_pi_iff.mpr (fun j => hXvec_meas n i j)
      Z := Z
      hZ := hZmeas
      mu := mu
      Sigma := Sigma
      hSigma := hSigma
      hmodel := by
        intro n i ω
        funext j
        simp only [Xvec, Pi.add_apply]
        exact add_comm _ _
      hindep := hZindep
      hident := hZident
      hZ_int := hZint
      hZ_mean := hZmean
      hZ_cov_int := hZint2
      hZ_cov := hZcov
      hX_int := by
        intro n i j
        have hsum : ∀ ω : Omega, Xvec p Sigma hSigma mu Z n i ω j
            = mu n j + ∑ k : Fin (p n),
                (Matrix.PosSemidef.sqrt (hSigma n)) j k * Z n i ω k := by
          intro ω
          have hdot : Matrix.mulVec (Matrix.PosSemidef.sqrt (hSigma n)) (Z n i ω) j
              = ∑ k : Fin (p n),
                  (Matrix.PosSemidef.sqrt (hSigma n)) j k * Z n i ω k := rfl
          simp only [Xvec, Pi.add_apply, hdot]
          exact add_comm _ _
        have h1 : Integrable (fun ω : Omega => ∑ k : Fin (p n),
            (Matrix.PosSemidef.sqrt (hSigma n)) j k * Z n i ω k) P :=
          MeasureTheory.integrable_finset_sum Finset.univ
            (fun k _ => (hZint n i k).const_mul ((Matrix.PosSemidef.sqrt (hSigma n)) j k))
        have h2 : Integrable (fun _ : Omega => mu n j) P := integrable_const _
        simpa only [hsum] using h2.add h1
      hX_memLp := by
        intro n i j
        have hZmem : ∀ k : Fin (p n), MemLp (fun ω : Omega => Z n i ω k) 2 P := by
          intro k
          refine (MeasureTheory.memLp_two_iff_integrable_sq
            (hZmeas' n i k).aestronglyMeasurable).mpr ?_
          simpa only [pow_two] using hZint2 n i k k
        have hsum_mem : MemLp (fun ω : Omega =>
            ∑ k : Fin (p n), (Matrix.PosSemidef.sqrt (hSigma n)) j k * Z n i ω k) 2 P :=
          MeasureTheory.memLp_finset_sum Finset.univ (fun k _ => (hZmem k).const_mul _)
        have hconst_mem : MemLp (fun _ : Omega => mu n j) 2 P := by
          refine (MeasureTheory.memLp_two_iff_integrable_sq
            (measurable_const : Measurable fun _ : Omega => mu n j).aestronglyMeasurable).mpr ?_
          simpa only [pow_two] using integrable_const (mu n j * mu n j)
        have hpt : MemLp (fun ω : Omega => mu n j +
            ∑ k : Fin (p n), (Matrix.PosSemidef.sqrt (hSigma n)) j k * Z n i ω k) 2 P :=
          hconst_mem.add hsum_mem
        simpa only [hXsum] using hpt
      tau := tau
      g := perm }
  have hsigma_eq : ∀ (n : ℕ) (hn : 0 < n) (j : Fin (p n)),
      M.sigma n j = sigmaSD p Sigma n j := by
    intro n hn j
    have hsig : M.sigma n j
        = Real.sqrt (variance (fun ω => Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω j) P) := by
      simp only [PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.Model.sigma]
      exact dif_pos hn
    rw [hsig]
    have hv : variance (fun ω => Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω j) P = Sigma n j j := by
      rw [ProbabilityTheory.variance_eq_integral (hXvec_meas n ⟨0, hn⟩ j).aemeasurable,
        hmeanX n ⟨0, hn⟩ j]
      exact (hvarCore n (Nat.succ_le_of_lt hn) j).2
    rw [hv]
    simp only [sigmaSD]
  have hcov_eq : ∀ (n : ℕ) (hn : 0 < n) (i j : Fin (p n)),
      M.covX n i j = Sigma n i j := by
    intro n hn i j
    have hn1 : 1 ≤ n := Nat.succ_le_of_lt hn
    have hIntConst : ∀ c : ℝ, ∫ _ : Omega, c ∂P = c := by
      intro c
      rw [MeasureTheory.integral_const]
      simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
    have hci : M.covX n i j
        = covariance (fun ω => Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω i)
            (fun ω => Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω j) P := by
      simp only [PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.Model.covX]
      exact dif_pos hn
    have hSS : Integrable (fun ω => (Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω i - mu n i) *
        (Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω j - mu n j)) P := (hcovCore n hn1 i j).1
    have hA : Integrable (fun ω => mu n i * Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω j) P :=
      (M.hX_int n ⟨0, hn⟩ j).const_mul _
    have hB : Integrable (fun ω =>
        mu n j * (Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω i - mu n i)) P :=
      ((M.hX_int n ⟨0, hn⟩ i).sub (integrable_const _)).const_mul _
    have hSi : ∫ ω, (Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω i - mu n i) ∂P = 0 := by
      rw [MeasureTheory.integral_sub (M.hX_int n ⟨0, hn⟩ i) (integrable_const _),
        hmeanX n ⟨0, hn⟩ i, hIntConst (mu n i), sub_self]
    have hpt : ∀ ω : Omega,
        Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω i * Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω j
          = (Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω i - mu n i) *
              (Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω j - mu n j)
            + mu n i * Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω j
            + mu n j * (Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω i - mu n i) := by
      intro ω
      ring
    have hXX : ∫ ω,
          Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω i * Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω j ∂P
        = Sigma n i j + mu n i * mu n j := by
      have h1 : ∫ ω,
            Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω i * Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω j ∂P
          = ∫ ω, ((Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω i - mu n i) *
                (Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω j - mu n j)
              + mu n i * Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω j
              + mu n j * (Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω i - mu n i)) ∂P := by
        simp only [hpt]
      have e1 : ∫ ω, ((Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω i - mu n i) *
                (Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω j - mu n j)
              + mu n i * Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω j
              + mu n j * (Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω i - mu n i)) ∂P
          = (∫ ω, ((Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω i - mu n i) *
                (Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω j - mu n j)
              + mu n i * Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω j) ∂P)
            + ∫ ω, mu n j * (Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω i - mu n i) ∂P :=
        MeasureTheory.integral_add (hSS.add hA) hB
      have e2 : ∫ ω, ((Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω i - mu n i) *
                (Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω j - mu n j)
              + mu n i * Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω j) ∂P
          = (∫ ω, (Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω i - mu n i) *
                (Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω j - mu n j) ∂P)
            + ∫ ω, mu n i * Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω j ∂P :=
        MeasureTheory.integral_add hSS hA
      have e3 : ∫ ω, (Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω i - mu n i) *
            (Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω j - mu n j) ∂P = Sigma n i j :=
        (hcovCore n hn1 i j).2
      have e4 : ∫ ω, mu n i * Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω j ∂P
          = mu n i * mu n j := by
        rw [MeasureTheory.integral_const_mul, hmeanX n ⟨0, hn⟩ j]
      have e5 : ∫ ω, mu n j * (Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω i - mu n i) ∂P = 0 := by
        rw [MeasureTheory.integral_const_mul, hSi, mul_zero]
      rw [h1, e1, e2, e3, e4, e5]
      ring
    rw [hci, ProbabilityTheory.covariance_eq_sub (M.hX_memLp n ⟨0, hn⟩ i)
      (M.hX_memLp n ⟨0, hn⟩ j)]
    have hbprod : ∫ (x : Omega),
          ((fun ω => Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω i) *
            (fun ω => Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω j)) x ∂P
        = ∫ ω, Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω i *
            Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω j ∂P := rfl
    have hbi : ∫ (x : Omega),
          (fun ω => Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω i) x ∂P = mu n i := by
      rw [show (∫ (x : Omega), (fun ω => Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω i) x ∂P)
        = ∫ ω, Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω i ∂P from rfl, hmeanX n ⟨0, hn⟩ i]
    have hbj : ∫ (x : Omega),
          (fun ω => Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω j) x ∂P = mu n j := by
      rw [show (∫ (x : Omega), (fun ω => Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω j) x ∂P)
        = ∫ ω, Xvec p Sigma hSigma mu Z n ⟨0, hn⟩ ω j ∂P from rfl, hmeanX n ⟨0, hn⟩ j]
    rw [hbprod, hbi, hbj, hXX]
    ring
  have hcutsum : ∀ (pn : ℕ) (m : ℕ) (hm : m ≤ pn) (φ : Fin pn → ℝ),
      (∑ i : Fin pn, (if (i : ℕ) < m then φ i else 0))
        = ∑ i : Fin m, φ (Fin.castLE hm i) := by
    intro pn m hm φ
    rw [← Finset.sum_filter]
    have hfilter_eq : (Finset.univ.filter (fun i : Fin pn => (i : ℕ) < m))
        = (Finset.univ : Finset (Fin m)).map
            ⟨Fin.castLE hm, fun a b hab => Fin.ext (by simpa using congrArg Fin.val hab)⟩ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      exact ⟨fun hi => ⟨⟨i.1, hi⟩, Fin.ext rfl⟩,
        fun ⟨b, hb⟩ => by rw [← hb]; exact b.2⟩
    rw [hfilter_eq, Finset.sum_map]
    rfl
  have hpush_ite : ∀ (pn : ℕ) (A : Prop) [Decidable A] (g : Fin pn → ℝ),
      (∑ j : Fin pn, (if A then g j else 0)) = if A then ∑ j : Fin pn, g j else 0 := by
    intro pn A _ g
    by_cases hA : A <;> simp [hA]
  
  
  have hMA :
      PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.Model.Assumptions
        M c0 alpha cvar ccirc eps0 Ccor :=
    { hpsi := fun n hn u hu =>
        statopia_math_node_919475896_8a352a02 Omega P
          (fun ω : Omega => ∑ j : Fin (p n), u j * Z n ⟨0, hn⟩ ω j) c0
          (Finset.measurable_sum Finset.univ
            (fun j _ => (hZmeas' n ⟨0, hn⟩ j).const_mul (u j)))
          hc0 (hZsubg n ⟨0, hn⟩ u hu)
      hsig_pos := fun n hn j => by
        rw [hsigma_eq n hn j]
        exact hsigpos n j
      hg_sorted := fun n i j hij => by
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · subst h0
          have hz : ∀ x : Fin (M.p 0), M.sigma 0 x = 0 := fun x => by
            simp only [PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.Model.sigma]
            exact dif_neg (Nat.lt_irrefl 0)
          rw [hz ((M.g 0) j), hz ((M.g 0) i)]
        · rw [hsigma_eq n hpos (M.g n j), hsigma_eq n hpos (M.g n i)]
          exact hperm n i j hij
      hsig_upper := fun n hn i hi => by
        have hk : M.kIdx n = kN (p n) a n := rfl
        rw [hsigma_eq n hn (M.g n i)]
        simpa only [Nat.cast_add, Nat.cast_one] using hub n i (hk ▸ hi)
      hsig_lower := fun n hn i hi => by
        have hk : M.kIdx n = kN (p n) a n := rfl
        rw [hsigma_eq n hn (M.g n i)]
        simpa only [Nat.cast_add, Nat.cast_one] using hlb n i (hk ▸ hi)
      hcorr_max := fun n i j hi hj hij => by
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · subst h0
          have hz : M.corrEntry 0 (M.g 0 i) (M.g 0 j) = 0 := by
            simp only [PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.Model.corrEntry,
              PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.Model.covX,
              PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.Model.sigma]
            rw [dif_neg (Nat.lt_irrefl 0), dif_neg (Nat.lt_irrefl 0), dif_neg (Nat.lt_irrefl 0)]
            exact zero_div (0 * 0)
          rw [hz]
          linarith
        · have hg : ∀ x : Fin (p n), M.g n x = perm n x := fun x => rfl
          have hq1 : posIn (ellN_le_p (p n) n) (⟨i.1, hi⟩ : Fin (ellN (p n) n)) = i := rfl
          have hq2 : posIn (ellN_le_p (p n) n) (⟨j.1, hj⟩ : Fin (ellN (p n) n)) = j := rfl
          have h1 : M.corrEntry n (M.g n i) (M.g n j)
              = corrEntry p Sigma perm n (ellN (p n) n) (ellN_le_p (p n) n)
                  ⟨i.1, hi⟩ ⟨j.1, hj⟩ := by
            simp only [PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.Model.corrEntry,
              hcov_eq n hpos (M.g n i) (M.g n j),
              hsigma_eq n hpos (M.g n i), hsigma_eq n hpos (M.g n j)]
            simp only [corrEntry, hg, hq1, hq2]
          rw [h1]
          exact hRoff n ⟨i.1, hi⟩ ⟨j.1, hj⟩
            (fun h => hij (Fin.ext (by simpa using congrArg Fin.val h)))
      hcorr_psd := fun n => by
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · subst h0
          have hsig0 : ∀ a : Fin (M.p 0), M.sigma 0 a = 0 := fun a => by
            simp only [PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.Model.sigma]
            exact dif_neg (Nat.lt_irrefl 0)
          have hcov0 : ∀ a b : Fin (M.p 0), M.covX 0 a b = 0 := fun a b => by
            simp only [PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.Model.covX]
            exact dif_neg (Nat.lt_irrefl 0)
          have hce0 : ∀ a b : Fin (M.p 0), M.corrEntry 0 a b = 0 := by
            intro a b
            simp only [PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.Model.corrEntry,
              hcov0 a b, hsig0 a, hsig0 b]
            exact zero_div (0 * 0)
          have hz : M.corrMatPos 0 (M.ell 0) (M.ell_le_p 0) = 0 := by
            ext i j
            show max (M.corrEntry 0 (M.g 0 (Fin.castLE (M.ell_le_p 0) i))
              (M.g 0 (Fin.castLE (M.ell_le_p 0) j))) 0 = 0
            simp only [hce0, max_self]
          rw [hz]
          refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
          · simp
          · intro x
            simp
        · have hg : ∀ x : Fin (p n), M.g n x = perm n x := fun x => rfl
          have hcl : ∀ x : Fin (M.ell n),
              Fin.castLE (M.ell_le_p n) x = posIn (ellN_le_p (p n) n) x :=
            fun x => Fin.ext rfl
          have hentry : ∀ (i j : Fin (M.ell n)),
              M.corrMatPos n (M.ell n) (M.ell_le_p n) i j
                = corrPos p Sigma perm n (ellN (p n) n) (ellN_le_p (p n) n) i j := by
            intro i j
            have hci : M.corrEntry n (M.g n (posIn (ellN_le_p (p n) n) i))
                  (M.g n (posIn (ellN_le_p (p n) n) j))
                = corrEntry p Sigma perm n (ellN (p n) n) (ellN_le_p (p n) n) i j := by
              simp only [PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.Model.corrEntry,
                hcov_eq n hpos (M.g n (posIn (ellN_le_p (p n) n) i))
                  (M.g n (posIn (ellN_le_p (p n) n) j)),
                hsigma_eq n hpos (M.g n (posIn (ellN_le_p (p n) n) i)),
                hsigma_eq n hpos (M.g n (posIn (ellN_le_p (p n) n) j))]
              simp only [corrEntry, hg]
            show max (M.corrEntry n (M.g n (Fin.castLE (M.ell_le_p n) i))
                  (M.g n (Fin.castLE (M.ell_le_p n) j))) 0
                = max (corrEntry p Sigma perm n (ellN (p n) n) (ellN_le_p (p n) n) i j) 0
            rw [hcl i, hcl j, hci]
          have hmat : M.corrMatPos n (M.ell n) (M.ell_le_p n)
              = corrPos p Sigma perm n (ellN (p n) n) (ellN_le_p (p n) n) :=
            Matrix.ext hentry
          rw [hmat]
          exact hRpsd n
      hcorr_sum := fun n => by
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · subst h0
          have hzero : ∀ q ∈ (Finset.univ : Finset (Fin (M.p 0) × Fin (M.p 0))).filter
              (fun q => (q.1 : ℕ) < M.ell 0 ∧ (q.2 : ℕ) < M.ell 0 ∧ q.1 < q.2),
              max (M.corrEntry 0 (M.g 0 q.1) (M.g 0 q.2)) 0 = 0 := by
            intro q _
            have hce : M.corrEntry 0 (M.g 0 q.1) (M.g 0 q.2) = 0 := by
              simp only [PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.Model.corrEntry,
                PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.Model.covX,
                PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.Model.sigma]
              rw [dif_neg (Nat.lt_irrefl 0), dif_neg (Nat.lt_irrefl 0), dif_neg (Nat.lt_irrefl 0)]
              exact zero_div (0 * 0)
            rw [hce, max_self]
          rw [Finset.sum_congr rfl hzero]
          simp only [Finset.sum_const_zero]
          exact mul_nonneg (le_of_lt hCcor) (by positivity)
        · have hterm : ∀ (i j : Fin (M.ell n)),
              max (M.corrEntry n (M.g n (Fin.castLE (M.ell_le_p n) i))
                (M.g n (Fin.castLE (M.ell_le_p n) j))) 0
                = corrPos p Sigma perm n (ellN (p n) n) (ellN_le_p (p n) n) i j := by
            intro i j
            have hg : ∀ x : Fin (p n), M.g n x = perm n x := fun x => rfl
            have hcl : ∀ x : Fin (M.ell n),
                Fin.castLE (M.ell_le_p n) x = posIn (ellN_le_p (p n) n) x :=
              fun x => Fin.ext rfl
            have hci : M.corrEntry n (M.g n (posIn (ellN_le_p (p n) n) i))
                  (M.g n (posIn (ellN_le_p (p n) n) j))
                = corrEntry p Sigma perm n (ellN (p n) n) (ellN_le_p (p n) n) i j := by
              simp only [PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.Model.corrEntry,
                hcov_eq n hpos (M.g n (posIn (ellN_le_p (p n) n) i))
                  (M.g n (posIn (ellN_le_p (p n) n) j)),
                hsigma_eq n hpos (M.g n (posIn (ellN_le_p (p n) n) i)),
                hsigma_eq n hpos (M.g n (posIn (ellN_le_p (p n) n) j))]
              simp only [corrEntry, hg]
            show max (M.corrEntry n (M.g n (Fin.castLE (M.ell_le_p n) i))
                  (M.g n (Fin.castLE (M.ell_le_p n) j))) 0
                = max (corrEntry p Sigma perm n (ellN (p n) n) (ellN_le_p (p n) n) i j) 0
            rw [hcl i, hcl j, hci]
          have hpair : ∀ (f : Fin (p n) → Fin (p n) → ℝ),
              (∑ q ∈ (Finset.univ : Finset (Fin (p n) × Fin (p n))).filter
                  (fun q => (q.1 : ℕ) < M.ell n ∧ (q.2 : ℕ) < M.ell n ∧ q.1 < q.2), f q.1 q.2)
                = ∑ i : Fin (M.ell n), ∑ j : Fin (M.ell n),
                    (if i < j then f (Fin.castLE (M.ell_le_p n) i)
                      (Fin.castLE (M.ell_le_p n) j) else 0) := by
            intro f
            rw [Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]
            have step1 : (∑ i : Fin (p n), ∑ j : Fin (p n),
                (if ((i : ℕ) < M.ell n ∧ ((j : ℕ) < M.ell n ∧ i < j)) then f i j else 0))
                = ∑ i : Fin (p n), (if (i : ℕ) < M.ell n then
                    (∑ j : Fin (p n),
                      (if ((j : ℕ) < M.ell n ∧ i < j) then f i j else 0)) else 0) := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              have hpt : ∀ j : Fin (p n),
                  (if ((i : ℕ) < M.ell n ∧ ((j : ℕ) < M.ell n ∧ i < j)) then f i j else 0)
                    = (if ((i : ℕ) < M.ell n) then
                        (if ((j : ℕ) < M.ell n ∧ i < j) then f i j else 0) else 0) := by
                intro j
                by_cases hA : (i : ℕ) < M.ell n <;> simp [hA]
              rw [Finset.sum_congr rfl (fun j _ => hpt j)]
              exact hpush_ite (p n) ((i : ℕ) < M.ell n)
                (fun j => if ((j : ℕ) < M.ell n ∧ i < j) then f i j else 0)
            rw [step1]
            rw [hcutsum (p n) (M.ell n) (M.ell_le_p n)
              (fun i => ∑ j : Fin (p n),
                (if ((j : ℕ) < M.ell n ∧ i < j) then f i j else 0))]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            have hpt : ∀ j : Fin (p n),
                (if ((j : ℕ) < M.ell n ∧ (Fin.castLE (M.ell_le_p n) i) < j) then
                    f (Fin.castLE (M.ell_le_p n) i) j else 0)
                  = (if ((j : ℕ) < M.ell n) then
                      (if (Fin.castLE (M.ell_le_p n) i) < j then
                        f (Fin.castLE (M.ell_le_p n) i) j else 0) else 0) := by
              intro j
              by_cases hB : (j : ℕ) < M.ell n <;> simp [hB]
            rw [Finset.sum_congr rfl (fun j _ => hpt j)]
            rw [hcutsum (p n) (M.ell n) (M.ell_le_p n)
              (fun j => if (Fin.castLE (M.ell_le_p n) i) < j then
                f (Fin.castLE (M.ell_le_p n) i) j else 0)]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            by_cases hij : i < j
            · rw [if_pos (show (Fin.castLE (M.ell_le_p n) i) <
                  (Fin.castLE (M.ell_le_p n) j) from hij), if_pos hij]
            · rw [if_neg (show ¬ ((Fin.castLE (M.ell_le_p n) i) <
                  (Fin.castLE (M.ell_le_p n) j)) from hij), if_neg hij]
          rw [hpair (fun a b => max (M.corrEntry n (M.g n a) (M.g n b)) 0)]
          have hfin : (∑ i : Fin (M.ell n), ∑ j : Fin (M.ell n),
              (if i < j then max (M.corrEntry n (M.g n (Fin.castLE (M.ell_le_p n) i))
                (M.g n (Fin.castLE (M.ell_le_p n) j))) 0 else 0))
              = ∑ i : Fin (M.ell n), ∑ j : Fin (M.ell n),
                  (if i < j then corrPos p Sigma perm n (ellN (p n) n) (ellN_le_p (p n) n) i j
                    else 0) := by
            refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
            by_cases hij : i < j
            · rw [if_pos hij, if_pos hij, hterm i j]
            · rw [if_neg hij, if_neg hij]
          rw [hfin]
          exact hRsum n
      htau_mem := fun n => ⟨htau0 n, htau1 n⟩
      htau_cond := htauN }
  obtain ⟨nT, hnT, hT⟩ := hmain M hMA
  refine ⟨max nII nT, le_trans hnII (le_max_left _ _), ?_⟩
  intro n hn
  have hmap_mass : ∀ {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
      (m : Measure α) (f : α → β), m Set.univ ≤ 1 → (Measure.map f m) Set.univ ≤ 1 := by
    intro α β _ _ m f hm
    by_cases hf : AEMeasurable f m
    · rw [Measure.map_apply_of_aemeasurable hf MeasurableSet.univ]
      simpa using hm
    · rw [Measure.map_of_not_aemeasurable hf]
      simp
  have hIcc : ∀ (mu' : Measure ℝ), mu' Set.univ ≤ 1 → ∀ t : ℝ,
      mu'.real (Set.Iic t) ∈ Set.Icc (0 : ℝ) 1 := by
    intro mu' hmu' t
    simp only [Measure.real]
    refine ⟨ENNReal.toReal_nonneg, ?_⟩
    have hne : mu' Set.univ ≠ ∞ := ne_top_of_le_ne_top (by simp) hmu'
    have hmono : mu' (Set.Iic t) ≤ mu' Set.univ := measure_mono (Set.subset_univ (Set.Iic t))
    calc (mu' (Set.Iic t)).toReal ≤ (mu' Set.univ).toReal := ENNReal.toReal_mono hne hmono
      _ ≤ (1 : ℝ≥0∞).toReal := ENNReal.toReal_mono (by simp) hmu'
      _ = 1 := ENNReal.toReal_one
  have hstdmass :
      (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.stdGaussianLaw (p n))
        Set.univ ≤ 1 := by
    haveI : IsProbabilityMeasure
        (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.stdGaussianLaw (p n)) := by
      show IsProbabilityMeasure (Measure.pi (fun _ : Fin (p n) => gaussianReal 0 1))
      infer_instance
    exact le_of_eq measure_univ
  let A : Measure ℝ := P.map (fun ω => Mstat (hp n) (sigmaSD p Sigma n) (tau n)
    (fun j => Scoord p Sigma hSigma mu Z n j ω))
  let B : Measure ℝ := P.map (fun om =>
    PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.maxOverJ (perm n)
      (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n)
      (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sigma n))
      (tau n)
      (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.SnVec
        (Xvec p Sigma hSigma mu Z n) (mu n) om))
  let C : Measure ℝ :=
    (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.stdGaussianLaw (p n)).map
      (fun w =>
        PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.maxOverJ (perm n)
          (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n)
          (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sigma n))
          (tau n)
          (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.StildeVec
            (hSigma n) id w))
  let D : Measure ℝ := (gaussLaw n).map (Mstat (hp n) (sigmaSD p Sigma n) (tau n))
  have htri : dK A D ≤ dK A B + dK B C + dK C D := by
    have hA : ∀ t : ℝ, A.real (Set.Iic t) ∈ Set.Icc (0 : ℝ) 1 :=
      hIcc A (hmap_mass P _ (le_of_eq instP.measure_univ))
    have hB : ∀ t : ℝ, B.real (Set.Iic t) ∈ Set.Icc (0 : ℝ) 1 :=
      hIcc B (hmap_mass P _ (le_of_eq instP.measure_univ))
    have hC : ∀ t : ℝ, C.real (Set.Iic t) ∈ Set.Icc (0 : ℝ) 1 :=
      hIcc C (hmap_mass
        (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.stdGaussianLaw (p n))
        _ hstdmass)
    have hD : ∀ t : ℝ, D.real (Set.Iic t) ∈ Set.Icc (0 : ℝ) 1 :=
      hIcc D (hmap_mass (gaussLaw n) _ (le_of_eq (hgprob n).measure_univ))
    have h1 : dK A D ≤ dK A C + dK C D :=
      statopia_math_node_550003712_e9ee920c A D C hA hD hC
    have h2 : dK A C ≤ dK A B + dK B C :=
      statopia_math_node_550003712_e9ee920c A C B hA hC hB
    linarith [h1, h2]
  show dK A D ≤ (c1 + cII + c2) * (n : ℝ) ^ (-(1 / 2) + delta)
  have hn1 : 1 ≤ n := le_trans hnII (le_trans (le_max_left _ _) hn)
  have hnpos : 0 < n := hn1
  have hsup_fmax : ∀ (ι : Type) [Fintype ι] (f : ι → ℝ) (h : (Finset.univ : Finset ι).Nonempty),
      PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.fmax
          (Finset.univ : Finset ι) f
        = (Finset.univ : Finset ι).sup' h f := by
    intro ι _ f h
    have hne : (f '' (↑(Finset.univ : Finset ι) : Set ι)).Nonempty := by
      have h2 : (Finset.univ : Finset ι).Nonempty := h
      obtain ⟨b, hb⟩ := h2
      exact ⟨f b, b, hb, rfl⟩
    have hbdd : BddAbove (f '' (↑(Finset.univ : Finset ι) : Set ι)) := by
      have hb : BddAbove (↑(Finset.univ.image f) : Set ℝ) := Finset.bddAbove _
      rwa [Finset.coe_image] at hb
    refine le_antisymm ?_ ?_
    · show sSup (f '' (↑(Finset.univ : Finset ι) : Set ι)) ≤ (Finset.univ : Finset ι).sup' h f
      exact csSup_le hne (fun x hx => by
        obtain ⟨b, hb, rfl⟩ := hx
        exact Finset.le_sup' f hb)
    · have hM : (Finset.univ : Finset ι).sup' h f ∈ f '' (↑(Finset.univ : Finset ι) : Set ι) := by
        obtain ⟨b, hb, hMb⟩ :=
          (Finset.le_sup'_iff h (f := f) (a := (Finset.univ : Finset ι).sup' h f)).mp le_rfl
        exact ⟨b, hb, le_antisymm (Finset.le_sup' f hb) hMb⟩
      exact le_csSup hbdd hM
  have hS_SnVec : ∀ (ω : Omega) (j : Fin (p n)), M.S n ω j
      = PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.SnVec
          (Xvec p Sigma hSigma mu Z n) (mu n) ω j := by
    intro ω j
    have hX : (PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.Model.X M)
        = Xvec p Sigma hSigma mu Z := rfl
    simp only [PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.Model.S,
      PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.SnVec, hX]
    simp only [hmeanX]
  have hS_Scoord : ∀ (ω : Omega) (j : Fin (p n)),
      M.S n ω j = Scoord p Sigma hSigma mu Z n j ω :=
    fun ω j => (hS_SnVec ω j).trans (hSnVec_eq n ω j)
  have hJ_univ : M.J n (M.p n) = Finset.univ := by
    ext i
    simp only [PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.Model.J,
      Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun _ => trivial,
      fun _ => ⟨(M.g n).symm i, ((M.g n).symm i).isLt, (M.g n).apply_symm_apply i⟩⟩
  have htau : ∀ m : ℕ,
      (PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.Model.tau M) m
        = tau m := fun m => rfl
  have hgm : (fun i : Fin (p n) => M.g n i) = (⇑(perm n) : Fin (p n) → Fin (p n)) := rfl
  have hkm : M.kIdx n
      = PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n := rfl
  have hsdm : ∀ j : Fin (p n),
      PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sigma n) j
        = sigmaSD p Sigma n j := fun j => rfl
  have hMd_p : ∀ ω : Omega, M.Md n (M.p n) ω
      = Mstat (hp n) (sigmaSD p Sigma n) (tau n)
          (fun j => Scoord p Sigma hSigma mu Z n j ω) := by
    intro ω
    have h1 : M.Md n (M.p n) ω
        = PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.fmax
            (Finset.univ : Finset (Fin (M.p n)))
            (fun j => Scoord p Sigma hSigma mu Z n j ω / (sigmaSD p Sigma n j) ^ (tau n)) := by
      simp only [PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.Model.Md,
        hJ_univ, hS_Scoord ω, hsigma_eq n hnpos, htau]
    rw [h1]
    exact hsup_fmax (Fin (M.p n)) _ ⟨⟨0, hp n⟩, Finset.mem_univ _⟩
  have hMd_k : ∀ ω : Omega, M.Md n (M.kIdx n) ω
      = PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.maxOverJ
          (perm n)
          (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n)
          (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sigma n))
          (tau n)
          (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.SnVec
            (Xvec p Sigma hSigma mu Z n) (mu n) ω) := by
    have hJk : M.J n (M.kIdx n)
        = PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.Jset
            (perm n)
            (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n) :=
      rfl
    intro ω
    simp only [PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.Model.Md,
      PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.fmax,
      hJk,
      PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.maxOverJ,
      hS_SnVec ω, hsigma_eq n hnpos, htau, hsdm, Finset.coe_image]
    rfl
  
  have hIn : PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.Model.In M n
      = dK A B := by
    have h1 : (fun ω : Omega => M.Md n (M.p n) ω)
        = (fun ω : Omega => Mstat (hp n) (sigmaSD p Sigma n) (tau n)
            (fun j => Scoord p Sigma hSigma mu Z n j ω)) := funext hMd_p
    have h2 : (fun ω : Omega => M.Md n (M.kIdx n) ω)
        = (fun om : Omega =>
            PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.maxOverJ
              (perm n)
              (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n)
              (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sigma n))
              (tau n)
              (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.SnVec
                (Xvec p Sigma hSigma mu Z n) (mu n) om)) := funext hMd_k
    have hA : (P.map (fun ω : Omega => Mstat (hp n) (sigmaSD p Sigma n) (tau n)
        (fun j => Scoord p Sigma hSigma mu Z n j ω))) = A := rfl
    have hB : (P.map (fun om : Omega =>
        PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.maxOverJ
          (perm n)
          (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n)
          (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sigma n))
          (tau n)
          (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.SnVec
            (Xvec p Sigma hSigma mu Z n) (mu n) om))) = B := rfl
    show dK (P.map (fun ω : Omega => M.Md n (M.p n) ω))
        (P.map (fun ω : Omega => M.Md n (M.kIdx n) ω)) = dK A B
    rw [h1, h2, hA, hB]
  have hIIIn : PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.Model.IIIn M n
      = dK C D := by
    have hTilde : M.tildeLaw n = gaussLaw n :=
      (statopia_math_node_2438113123_5c8212d8 (p n) (Sigma n) (hSigma n) (gaussLaw n)
        (hgprob n) (hggauss n) (hgint1 n) (hgmean n) (hgint2 n) (hgcov n)).symm
    have hTP : ∀ w : Fin (p n) → ℝ, M.tildeMd n (M.p n) w
        = Mstat (hp n) (sigmaSD p Sigma n) (tau n) w := by
      intro w
      have h1 : M.tildeMd n (M.p n) w
          = PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.fmax
              (Finset.univ : Finset (Fin (M.p n)))
              (fun j => w j / (sigmaSD p Sigma n j) ^ (tau n)) := by
        simp only [PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.Model.tildeMd,
          hJ_univ, hsigma_eq n hnpos, htau]
      rw [h1]
      exact hsup_fmax (Fin (M.p n)) _ ⟨⟨0, hp n⟩, Finset.mem_univ _⟩
    have hTK : ∀ w : Fin (p n) → ℝ, M.tildeMd n (M.kIdx n) w
        = PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.maxOverJ
            (perm n)
            (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n)
            (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sigma n))
            (tau n) w := by
      have hJk : M.J n (M.kIdx n)
          = PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.Jset
              (perm n)
              (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n) :=
        rfl
      intro w
      simp only [PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.Model.tildeMd,
        PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.fmax,
        hJk,
        PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.maxOverJ,
        hsigma_eq n hnpos, htau, hsdm, Finset.coe_image]
      rfl
    have hDside : (M.tildeLaw n).map (fun w => M.tildeMd n (M.p n) w) = D := by
      rw [hTilde]
      exact Measure.map_congr (Filter.Eventually.of_forall hTP)
    have hCside : (M.tildeLaw n).map (fun w => M.tildeMd n (M.kIdx n) w) = C := by
      have hTL : M.tildeLaw n
          = (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.stdGaussianLaw (p n)).map
              (fun w : Fin (p n) → ℝ =>
                Matrix.mulVec (Matrix.PosSemidef.sqrt (hSigma n)) w) := rfl
      have hk1 : 1 ≤ PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n := by
        have h := statopia_math_node_3367399074_28af528b (p n) n a (hp n)
        rw [← hkN n]
        exact le_trans h.1 h.2.1
      have hfmeas : Measurable (fun w : Fin (p n) → ℝ =>
          Matrix.mulVec (Matrix.PosSemidef.sqrt (hSigma n)) w) := by
        have hcont : Continuous (Matrix.mulVecLin (Matrix.PosSemidef.sqrt (hSigma n))) :=
          LinearMap.continuous_of_finiteDimensional _
        simpa only [Matrix.mulVecLin_apply] using hcont.measurable
      have hJne : (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.Jset
          (perm n)
          (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n)).Nonempty := by
        refine ⟨perm n ⟨0, hp n⟩, ?_⟩
        simp only [PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.Jset,
          PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.Jpos,
          Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨⟨0, hp n⟩, by simpa using hk1, rfl⟩
      have hgmeas : Measurable (fun w : Fin (p n) → ℝ => M.tildeMd n (M.kIdx n) w) := by
        have hfun : (fun w : Fin (p n) → ℝ => M.tildeMd n (M.kIdx n) w)
            = (fun v : Fin (p n) → ℝ =>
                PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.maxOverJ
                  (perm n)
                  (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n)
                  (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sigma n))
                  (tau n) v) := funext hTK
        rw [hfun]
        have hbridge : ∀ v : Fin (p n) → ℝ,
            PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.maxOverJ
                (perm n)
                (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n)
                (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sigma n))
                (tau n) v
              = (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.Jset
                  (perm n)
                  (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n)).sup'
                  hJne
                  (fun j => v j / (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sigma n) j) ^ (tau n)) := by
          intro v
          rw [show PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.maxOverJ
                (perm n)
                (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n)
                (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sigma n))
                (tau n) v
              = sSup (↑(Finset.image
                  (fun j => v j / (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sigma n) j) ^ (tau n))
                  (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.Jset (perm n)
                    (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n))) : Set ℝ) from rfl,
            Finset.coe_image]
          have hbdd : BddAbove ((fun j => v j / (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sigma n) j) ^ (tau n)) ''
              ↑(PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.Jset (perm n)
                (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n))) := by
            have h := Finset.bddAbove (Finset.image
              (fun j => v j / (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sigma n) j) ^ (tau n))
              (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.Jset (perm n)
                (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n)))
            rwa [Finset.coe_image] at h
          refine le_antisymm ?_ ?_
          · refine csSup_le ?_ ?_
            · obtain ⟨b, hb⟩ := hJne
              exact ⟨_, ⟨b, by simpa using hb, rfl⟩⟩
            · rintro _ ⟨b, hb, rfl⟩
              exact Finset.le_sup' (fun j => v j / (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sigma n) j) ^ (tau n)) (by simpa using hb)
          · refine (Finset.sup'_le_iff hJne _).mpr (fun b hb => ?_)
            exact le_csSup hbdd ⟨b, by simpa using hb, rfl⟩
        have hfun2 : (fun v : Fin (p n) → ℝ =>
              PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.maxOverJ
                (perm n)
                (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n)
                (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sigma n))
                (tau n) v)
            = (fun v : Fin (p n) → ℝ =>
                (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.Jset
                  (perm n)
                  (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n)).sup'
                  hJne
                  (fun j => v j / (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sigma n) j) ^ (tau n))) :=
          funext hbridge
        rw [hfun2]
        refine measurable_of_Iic (fun t => ?_)
        have hEq : (fun v : Fin (p n) → ℝ =>
              (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.Jset
                (perm n)
                (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n)).sup'
                hJne
                (fun j => v j / (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sigma n) j) ^ (tau n))) ⁻¹'
              Set.Iic t
            = ⋂ j : Fin (p n), {v : Fin (p n) → ℝ |
                j ∈ PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.Jset
                  (perm n)
                  (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n) →
                v j / (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sigma n) j) ^ (tau n) ≤ t} := by
          ext v
          simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_iInter, Set.mem_setOf_eq]
          exact Finset.sup'_le_iff hJne
            (fun j => v j / (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sigma n) j) ^ (tau n))
        rw [hEq]
        refine MeasurableSet.iInter (fun j => ?_)
        by_cases hj : j ∈ PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.Jset
            (perm n)
            (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n)
        · have hset : {v : Fin (p n) → ℝ |
              j ∈ PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.Jset
                (perm n)
                (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n) →
              v j / (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sigma n) j) ^ (tau n) ≤ t}
              = {v : Fin (p n) → ℝ |
                v j / (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sigma n) j) ^ (tau n) ≤ t} := by
            ext v
            simp only [Set.mem_setOf_eq]
            exact ⟨fun h => h hj, fun h _ => h⟩
          rw [hset]
          exact measurableSet_Iic.preimage (Measurable.div_const (measurable_pi_apply j) _)
        · have hset : {v : Fin (p n) → ℝ |
              j ∈ PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.Jset
                (perm n)
                (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n) →
              v j / (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sigma n) j) ^ (tau n) ≤ t} = Set.univ := by
            ext v
            simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
            exact fun h => absurd h hj
          rw [hset]
          exact MeasurableSet.univ
      rw [hTL, Measure.map_map hgmeas hfmeas]
      refine Measure.map_congr (Filter.Eventually.of_forall (fun w => ?_))
      show M.tildeMd n (M.kIdx n) (Matrix.mulVec (Matrix.PosSemidef.sqrt (hSigma n)) w)
        = PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.maxOverJ
            (perm n)
            (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n)
            (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sigma n))
            (tau n)
            (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.StildeVec
              (hSigma n) id w)
      rw [hTK]
      rfl
    show dK ((M.tildeLaw n).map (fun w => M.tildeMd n (M.kIdx n) w))
        ((M.tildeLaw n).map (fun w => M.tildeMd n (M.p n) w)) = dK C D
    rw [hCside, hDside]
  have hIk : dK A B ≤ c1 * (n : ℝ) ^ (-(1 / 2) + delta) := by
    rw [← hIn]
    exact (hT n (le_trans (le_max_right _ _) hn)).1
  have hIIk : dK B C ≤ cII * (n : ℝ) ^ (-(1 / 2) + delta) := by
    simpa only [dK,
      PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.IIn,
      PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kolmogorovDist,
      Measure.real] using hIIb n (le_trans (le_max_left _ _) hn)
  have hIIIk : dK C D ≤ c2 * (n : ℝ) ^ (-(1 / 2) + delta) := by
    rw [← hIIIn]
    exact (hT n (le_trans (le_max_right _ _) hn)).2
  have hsum : dK A B + dK B C + dK C D ≤ (c1 + cII + c2) * (n : ℝ) ^ (-(1 / 2) + delta) := by
    have hv : c1 * (n : ℝ) ^ (-(1 / 2) + delta) + cII * (n : ℝ) ^ (-(1 / 2) + delta)
        + c2 * (n : ℝ) ^ (-(1 / 2) + delta)
        = (c1 + cII + c2) * (n : ℝ) ^ (-(1 / 2) + delta) := by ring
    linarith
  exact htri.trans hsum
  /- @proof-region region.root.b49ab0343b06 end -/

end Statlib.Imported

-- Paper root revision fafd4245-d82a-4362-858e-2778a01dcef0
