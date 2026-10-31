import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.Vocabulary
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.Base
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.ProvedNodes.Node_2396133380_7d1999f1_13c63973
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.ProvedNodes.Node_2427644982_7294da19_198768f7
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.ProvedNodes.Node_3799861955_1c292e8a_9afb9068

namespace PaperProofTasks.job_paper_de3065fb922748188f3a0354eba90ed9


open _root_.PaperProofTasks.job_paper_de3065fb922748188f3a0354eba90ed9.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

set_option autoImplicit false in
theorem statopia_math_node_2646130728_f6109688 : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℕ) (hp : 1 ≤ p)
    (X : Ω → Fin p → ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (hGauss : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ X Sigma)
    (hL2 : ∀ j : Fin p, MemLp (fun ω => X ω j) 2 μ)
    (hpos : ∀ j : Fin p, 0 < ∫ ω, (X ω j) ^ 2 ∂μ)
    (hInt : Integrable (fun ω => ⨆ j : Fin p, X ω j / coordStdDev μ X j) μ)
    (x : ℝ) (ε : ℝ) (hε : 0 < ε)
    (S : Finset (Fin p)) (hS_ne : S.Nonempty)
    (hS_corr : ∀ j ∈ S, ∀ k ∈ S, j ≠ k →
      covariance (fun ω => X ω j / coordStdDev μ X j)
          (fun ω => X ω k / coordStdDev μ X k) μ /
        (Real.sqrt (variance (fun ω => X ω j / coordStdDev μ X j) μ) *
          Real.sqrt (variance (fun ω => X ω k / coordStdDev μ X k) μ)) < 1)
    (hS_W : μ {ω | (⨆ j : ↥S,
          X ω (j : Fin p) / coordStdDev μ X (j : Fin p) +
            x * ((if 0 ≤ x then 1 / sigmaUnder μ X else 1 / sigmaOver μ X) -
              1 / coordStdDev μ X (j : Fin p))) =
        (⨆ j : Fin p, X ω j / coordStdDev μ X j +
          x * ((if 0 ≤ x then 1 / sigmaUnder μ X else 1 / sigmaOver μ X) -
            1 / coordStdDev μ X j))} = 1)
    (hS_X : μ {ω | (⨆ j : ↥S, X ω (j : Fin p) / coordStdDev μ X (j : Fin p)) =
        (⨆ j : Fin p, X ω j / coordStdDev μ X j)} = 1),
    μ {ω | |(⨆ j : Fin p, (X ω j - x) / coordStdDev μ X j)| ≤ ε / sigmaUnder μ X} ≤
      ENNReal.ofReal
        (4 * ε / sigmaUnder μ X *
          ((1 / sigmaUnder μ X - 1 / sigmaOver μ X) * |x| + standardizedMaxMean μ X + 1)) := by
  /- @proof-region region.target-node.session.55276ce0e5764afc begin -/
  intro Ω _inst μ _ p hp X Sigma hGauss hL2 hpos hInt x ε hε S hS_ne hS_corr hS_W hS_X
  have key := statopia_math_node_2427644982_7294da19 μ p hp X Sigma hGauss hL2 hpos hInt x
  dsimp only at key
  obtain ⟨hmu_range, hWsub, hWmv, hGaussData, hIdents⟩ := key
  obtain ⟨hIsGauss, hSigmaZ_ex, hVarZ⟩ := hGaussData
  obtain ⟨hId1, hId2, hId3, hId4⟩ := hIdents
  have hσpos : ∀ j : Fin p, 0 < coordStdDev μ X j := fun j => Real.sqrt_pos.mpr (hpos j)
  haveI : Nonempty (Fin p) := ⟨⟨0, by omega⟩⟩
  have hσunder_le : ∀ j : Fin p, sigmaUnder μ X ≤ coordStdDev μ X j := by
    intro j
    exact ciInf_le (Finite.bddBelow_range (fun j => coordStdDev μ X j)) j
  have hσunder_pos : 0 < sigmaUnder μ X := by
    have hne : (Finset.univ : Finset (Fin p)).Nonempty := Finset.univ_nonempty
    have heq : sigmaUnder μ X = (Finset.univ : Finset (Fin p)).inf' hne (fun j => coordStdDev μ X j) := by
      rw [sigmaUnder]
      exact (Finset.inf'_univ_eq_ciInf (coordStdDev μ X)).symm
    rw [heq, Finset.lt_inf'_iff]
    exact fun j _ => hσpos j
  have hσ_le_over : ∀ j : Fin p, coordStdDev μ X j ≤ sigmaOver μ X := by
    intro j
    exact le_ciSup (Finite.bddAbove_range (fun j => coordStdDev μ X j)) j
  have hσunder_le_over : sigmaUnder μ X ≤ sigmaOver μ X :=
    le_trans (hσunder_le ⟨0, by omega⟩) (hσ_le_over ⟨0, by omega⟩)
  have hσover_pos : 0 < sigmaOver μ X :=
    lt_of_lt_of_le (hσpos ⟨0, by omega⟩) (hσ_le_over ⟨0, by omega⟩)
  have hδ_nonneg : 0 ≤ 1 / sigmaUnder μ X - 1 / sigmaOver μ X := by
    have h' : 1 / sigmaOver μ X ≤ 1 / sigmaUnder μ X :=
      one_div_le_one_div_of_le hσunder_pos hσunder_le_over
    linarith
  have hb_nonneg : 0 ≤ (1 / sigmaUnder μ X - 1 / sigmaOver μ X) * |x| :=
    mul_nonneg hδ_nonneg (abs_nonneg x)
  let q : ℕ := S.card
  have hq : 1 ≤ q := by
    have hc : 0 < S.card := Finset.card_pos.mpr hS_ne
    show 1 ≤ S.card
    omega
  let e : Fin q ≃ ↥S := (Finset.equivFin S).symm
  let b : ℝ := (1 / sigmaUnder μ X - 1 / sigmaOver μ X) * |x|
  let nu' : Fin q → ℝ := fun k =>
    x * ((if 0 ≤ x then 1 / sigmaUnder μ X else 1 / sigmaOver μ X) - 1 / coordStdDev μ X (e k : Fin p))
  let V : Ω → Fin q → ℝ := fun ω k =>
    X ω (e k : Fin p) / coordStdDev μ X (e k : Fin p) +
      x * ((if 0 ≤ x then 1 / sigmaUnder μ X else 1 / sigmaOver μ X) - 1 / coordStdDev μ X (e k : Fin p))
  let SigmaQ : Matrix (Fin q) (Fin q) ℝ := fun k l => ∫ ω, (V ω k - nu' k) * (V ω l - nu' l) ∂μ
  have hb : 0 ≤ b := hb_nonneg
  have hVar : ∀ k : Fin q, SigmaQ k k = 1 := by
    intro k
    have hk1 : ∫ ω, (V ω k - nu' k) ^ 2 ∂μ = variance (fun ω => V ω k) μ := (hWmv (e k : Fin p)).2.1
    have hk2 : variance (fun ω => V ω k) μ = 1 := (hWmv (e k : Fin p)).2.2
    change ∫ ω, (V ω k - nu' k) * (V ω k - nu' k) ∂μ = 1
    have hsq2 : (fun ω => (V ω k - nu' k) * (V ω k - nu' k)) = (fun ω => (V ω k - nu' k) ^ 2) := by
      funext ω; ring
    rw [hsq2, hk1, hk2]
  have hMean : ∀ k : Fin q, nu' k = ∫ ω, V ω k ∂μ := fun k => ((hWmv (e k : Fin p)).1).symm
  have hCov : ∀ k l : Fin q, SigmaQ k l = ∫ ω, (V ω k - nu' k) * (V ω l - nu' l) ∂μ := fun k l => rfl
  have hnu_nonneg : ∀ k : Fin q, 0 ≤ nu' k := fun k => (hmu_range (e k : Fin p)).1
  have hnu_le : ∀ k : Fin q, nu' k ≤ b := fun k => (hmu_range (e k : Fin p)).2
  have hV : Measurable V := by
    have hXm : Measurable (fun ω j => X ω j) := hGauss.measurable
    have hcoord : ∀ j : Fin p, Measurable (fun ω => X ω j) := measurable_pi_iff.mp hXm
    rw [measurable_pi_iff]
    intro k
    exact ((hcoord (e k : Fin p)).mul_const (coordStdDev μ X (e k : Fin p))⁻¹).add_const (x * ((if 0 ≤ x then 1 / sigmaUnder μ X else 1 / sigmaOver μ X) - 1 / coordStdDev μ X (e k : Fin p)))
  have hGauss : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ (fun ω k => V ω k - nu' k) SigmaQ := by
    obtain ⟨SigmaZ, hZ⟩ := hSigmaZ_ex
    have hinj : Function.Injective (fun k : Fin q => (e k : Fin p)) := by
      intro a b hab
      apply e.injective
      exact Subtype.ext hab
    have hres := statopia_math_node_2396133380_7d1999f1 μ p hp
      (fun ω j => (X ω j / coordStdDev μ X j +
          x * ((if 0 ≤ x then 1 / sigmaUnder μ X else 1 / sigmaOver μ X) - 1 / coordStdDev μ X j)) -
          x * ((if 0 ≤ x then 1 / sigmaUnder μ X else 1 / sigmaOver μ X) - 1 / coordStdDev μ X j))
      SigmaZ hZ q hq (fun k => (e k : Fin p)) hinj
    exact hres
  have hL2V : ∀ k : Fin q, MemLp (fun ω => V ω k) 2 μ := by
    intro k
    have h2 : MemLp (fun _ : Ω => x * ((if 0 ≤ x then 1 / sigmaUnder μ X else 1 / sigmaOver μ X) - 1 / coordStdDev μ X (e k : Fin p))) 2 μ :=
      memLp_const _
    exact ((hL2 (e k : Fin p)).mul_const (coordStdDev μ X (e k : Fin p))⁻¹).add h2
  have hCorr : ∀ k l : Fin q, k ≠ l → SigmaQ k l < 1 := by
    intro k l hkl
    have hfk : ∀ ω, V ω k - nu' k = X ω (e k : Fin p) / coordStdDev μ X (e k : Fin p) := by
      intro ω; simp only [V, nu']; ring
    have hgl : ∀ ω, V ω l - nu' l = X ω (e l : Fin p) / coordStdDev μ X (e l : Fin p) := by
      intro ω; simp only [V, nu']; ring
    have hAEmf : AEMeasurable (fun ω => X ω (e k : Fin p) / coordStdDev μ X (e k : Fin p)) μ :=
      ((hL2 (e k : Fin p)).mul_const (coordStdDev μ X (e k : Fin p))⁻¹).aemeasurable
    have hAEg : AEMeasurable (fun ω => X ω (e l : Fin p) / coordStdDev μ X (e l : Fin p)) μ :=
      ((hL2 (e l : Fin p)).mul_const (coordStdDev μ X (e l : Fin p))⁻¹).aemeasurable
    have hSQ : SigmaQ k l = ∫ ω, (X ω (e k : Fin p) / coordStdDev μ X (e k : Fin p)) * (X ω (e l : Fin p) / coordStdDev μ X (e l : Fin p)) ∂μ := by
      rw [hCov k l]
      exact integral_congr_ae (Filter.EventuallyEq.of_eq (by funext ω; rw [hfk ω, hgl ω]))
    have hfk0 : ∫ ω, X ω (e k : Fin p) / coordStdDev μ X (e k : Fin p) ∂μ = 0 := by
      have h1 : ∫ ω, X ω (e k : Fin p) / coordStdDev μ X (e k : Fin p) ∂μ = ∫ ω, (V ω k - nu' k) ∂μ :=
        integral_congr_ae (Filter.EventuallyEq.of_eq (by funext ω; exact (hfk ω).symm))
      rw [h1, integral_sub ((hL2V k).integrable (by norm_num)) (integrable_const (nu' k)), (hMean k).symm]
      rw [MeasureTheory.integral_const]; simp
    have hgl0 : ∫ ω, X ω (e l : Fin p) / coordStdDev μ X (e l : Fin p) ∂μ = 0 := by
      have h1 : ∫ ω, X ω (e l : Fin p) / coordStdDev μ X (e l : Fin p) ∂μ = ∫ ω, (V ω l - nu' l) ∂μ :=
        integral_congr_ae (Filter.EventuallyEq.of_eq (by funext ω; exact (hgl ω).symm))
      rw [h1, integral_sub ((hL2V l).integrable (by norm_num)) (integrable_const (nu' l)), (hMean l).symm]
      rw [MeasureTheory.integral_const]; simp
    have hfk2 : ∫ ω, (X ω (e k : Fin p) / coordStdDev μ X (e k : Fin p)) ^ 2 ∂μ = 1 := by
      have hh := hVar k
      have hS : SigmaQ k k = ∫ ω, (X ω (e k : Fin p) / coordStdDev μ X (e k : Fin p)) ^ 2 ∂μ := by
        rw [hCov k k]
        exact integral_congr_ae (Filter.EventuallyEq.of_eq (by funext ω; rw [hfk ω]; ring))
      rwa [hS] at hh
    have hgl2 : ∫ ω, (X ω (e l : Fin p) / coordStdDev μ X (e l : Fin p)) ^ 2 ∂μ = 1 := by
      have hh := hVar l
      have hS : SigmaQ l l = ∫ ω, (X ω (e l : Fin p) / coordStdDev μ X (e l : Fin p)) ^ 2 ∂μ := by
        rw [hCov l l]
        exact integral_congr_ae (Filter.EventuallyEq.of_eq (by funext ω; rw [hgl ω]; ring))
      rwa [hS] at hh
    have hVf : variance (fun ω => X ω (e k : Fin p) / coordStdDev μ X (e k : Fin p)) μ = 1 := by
      rw [ProbabilityTheory.variance_eq_integral hAEmf]
      simp only [hfk0, sub_zero]; exact hfk2
    have hVg : variance (fun ω => X ω (e l : Fin p) / coordStdDev μ X (e l : Fin p)) μ = 1 := by
      rw [ProbabilityTheory.variance_eq_integral hAEg]
      simp only [hgl0, sub_zero]; exact hgl2
    have hcov : covariance (fun ω => X ω (e k : Fin p) / coordStdDev μ X (e k : Fin p)) (fun ω => X ω (e l : Fin p) / coordStdDev μ X (e l : Fin p)) μ = ∫ ω, (X ω (e k : Fin p) / coordStdDev μ X (e k : Fin p)) * (X ω (e l : Fin p) / coordStdDev μ X (e l : Fin p)) ∂μ := by
      rw [show covariance (fun ω => X ω (e k : Fin p) / coordStdDev μ X (e k : Fin p)) (fun ω => X ω (e l : Fin p) / coordStdDev μ X (e l : Fin p)) μ = ∫ ω, ((fun ω => X ω (e k : Fin p) / coordStdDev μ X (e k : Fin p)) ω - ∫ x, (fun ω => X ω (e k : Fin p) / coordStdDev μ X (e k : Fin p)) x ∂μ) * ((fun ω => X ω (e l : Fin p) / coordStdDev μ X (e l : Fin p)) ω - ∫ x, (fun ω => X ω (e l : Fin p) / coordStdDev μ X (e l : Fin p)) x ∂μ) ∂μ from rfl]
      simp only [hfk0, hgl0, sub_zero]
    have hene : (e k : Fin p) ≠ (e l : Fin p) := by
      intro h; exact hkl (e.injective (Subtype.ext h))
    have hc := hS_corr (e k : Fin p) (e k).2 (e l : Fin p) (e l).2 hene
    rw [hVf, hVg, Real.sqrt_one, mul_one, div_one] at hc
    rw [hSQ, ← hcov]
    exact hc
  have hpointV : ∀ (ω : Ω) (k : Fin q), V ω k - nu' k = X ω (e k : Fin p) / coordStdDev μ X (e k : Fin p) := by
    intro ω k; simp only [V, nu']; ring
  have hIntV : Integrable (fun ω => coordMax (fun ω' k => V ω' k - nu' k) ω) μ := by
    let k0 : Fin q := ⟨0, by omega⟩
    haveI hne : Nonempty (Fin q) := ⟨k0⟩
    have hAEm : AEMeasurable (fun ω => coordMax (fun ω' k => V ω' k - nu' k) ω) μ := by
      have heq : (fun ω => coordMax (fun ω' k => V ω' k - nu' k) ω) = (fun ω => ⨆ k : Fin q, (V ω k - nu' k)) := by
        funext ω; simp only [coordMax]
      rw [heq]
      exact AEMeasurable.iSup (fun k => ((hL2V k).aestronglyMeasurable.sub aestronglyMeasurable_const).aemeasurable)
    have hmeas : AEStronglyMeasurable (fun ω => coordMax (fun ω' k => V ω' k - nu' k) ω) μ := hAEm.aestronglyMeasurable
    have hVint : Integrable (fun ω => V ω k0) μ := (hL2V k0).integrable (by norm_num)
    have hY0int : Integrable (fun ω => ‖V ω k0 - nu' k0‖) μ := (hVint.sub (integrable_const (nu' k0))).norm
    have hgint : Integrable (fun ω => ‖⨆ j : Fin p, X ω j / coordStdDev μ X j‖) μ := hInt.norm
    have hbound_int : Integrable (fun ω => ‖⨆ j : Fin p, X ω j / coordStdDev μ X j‖ + ‖V ω k0 - nu' k0‖) μ :=
      hgint.add hY0int
    refine Integrable.mono hbound_int hmeas ?_
    filter_upwards with ω
    have hY0f : V ω k0 - nu' k0 ≤ coordMax (fun ω' k => V ω' k - nu' k) ω := by
      simp only [coordMax]
      exact le_ciSup (Finite.bddAbove_range (fun k => V ω k - nu' k)) k0
    have hfg : coordMax (fun ω' k => V ω' k - nu' k) ω ≤ ⨆ j : Fin p, X ω j / coordStdDev μ X j := by
      simp only [coordMax]
      rw [iSup_congr (fun k => hpointV ω k)]
      exact ciSup_le (fun k => le_ciSup (Finite.bddAbove_range (fun j => X ω j / coordStdDev μ X j)) (e k : Fin p))
    have hval : ‖(fun ω => ‖⨆ j : Fin p, X ω j / coordStdDev μ X j‖ + ‖V ω k0 - nu' k0‖) ω‖ = ‖⨆ j : Fin p, X ω j / coordStdDev μ X j‖ + ‖V ω k0 - nu' k0‖ :=
      Real.norm_of_nonneg (by positivity)
    rw [hval]
    simp only [Real.norm_eq_abs]
    refine abs_le.mpr ⟨?_, ?_⟩
    · nlinarith [hY0f, neg_abs_le (V ω k0 - nu' k0), abs_nonneg (⨆ j : Fin p, X ω j / coordStdDev μ X j)]
    · nlinarith [hfg, le_abs_self (⨆ j : Fin p, X ω j / coordStdDev μ X j), abs_nonneg (V ω k0 - nu' k0)]
  have ht : 0 < ε / sigmaUnder μ X := div_pos hε hσunder_pos
  have hbound := statopia_math_node_3799861955_1c292e8a μ q hq V hV SigmaQ nu' b hb hVar hMean hCov hGauss hL2V hCorr hnu_nonneg hnu_le hIntV (x * ((if 0 ≤ x then 1 / sigmaUnder μ X else 1 / sigmaOver μ X))) (ε / sigmaUnder μ X) ht
  haveI hqne : Nonempty (Fin q) := ⟨⟨0, by omega⟩⟩
  haveI hSne : Nonempty ↥S := ⟨e ⟨0, by omega⟩⟩
  have hreindex : ∀ (a : ↥S → ℝ), (⨆ k : Fin q, a (e k)) = ⨆ j : ↥S, a j := by
    intro a
    apply le_antisymm
    · refine ciSup_le (fun k => le_ciSup (Finite.bddAbove_range a) (e k))
    · refine ciSup_le (fun j => ?_)
      have hsymm : a j = a (e (e.symm j)) := by simp
      rw [hsymm]
      exact le_ciSup (Finite.bddAbove_range (fun k => a (e k))) (e.symm j)
  let FFX : Ω → ℝ := fun ω => ⨆ j : Fin p, X ω j / coordStdDev μ X j
  let SSX : Ω → ℝ := fun ω => ⨆ j : ↥S, X ω (j : Fin p) / coordStdDev μ X (j : Fin p)
  have hSSX_aes : AEStronglyMeasurable SSX μ := by
    apply AEMeasurable.aestronglyMeasurable
    exact AEMeasurable.iSup (fun j : ↥S => ((hL2 (j : Fin p)).mul_const (coordStdDev μ X (j : Fin p))⁻¹).aemeasurable)
  have hFFX_aes : AEStronglyMeasurable FFX μ := by
    apply AEMeasurable.aestronglyMeasurable
    exact AEMeasurable.iSup (fun j : Fin p => ((hL2 j).mul_const (coordStdDev μ X j)⁻¹).aemeasurable)
  have hSX_ae : ∀ᵐ ω ∂μ, SSX ω = FFX ω :=
    (MeasureTheory.mem_ae_iff_prob_eq_one₀ (AEStronglyMeasurable.nullMeasurableSet_eq_fun hSSX_aes hFFX_aes)).mpr hS_X
  have hã : ∫ ω, coordMax (fun ω' k => V ω' k - nu' k) ω ∂μ = standardizedMaxMean μ X := by
    have hres : (fun ω => coordMax (fun ω' k => V ω' k - nu' k) ω) =ᵐ[μ] SSX := by
      apply Filter.EventuallyEq.of_eq
      funext ω
      have e1 : coordMax (fun ω' k => V ω' k - nu' k) ω = ⨆ k : Fin q, X ω (e k : Fin p) / coordStdDev μ X (e k : Fin p) := by
        rw [show coordMax (fun ω' k => V ω' k - nu' k) ω = ⨆ k : Fin q, (V ω k - nu' k) from rfl, iSup_congr (fun k => hpointV ω k)]
      have e2 : (⨆ k : Fin q, X ω (e k : Fin p) / coordStdDev μ X (e k : Fin p)) = SSX ω :=
        hreindex (fun j : ↥S => X ω (j : Fin p) / coordStdDev μ X (j : Fin p))
      exact e1.trans e2
    have h1 : ∫ ω, coordMax (fun ω' k => V ω' k - nu' k) ω ∂μ = ∫ ω, SSX ω ∂μ := integral_congr_ae hres
    have h2 : ∫ ω, SSX ω ∂μ = ∫ ω, FFX ω ∂μ := integral_congr_ae hSX_ae
    have h3 : ∫ ω, FFX ω ∂μ = standardizedMaxMean μ X := rfl
    rw [h1, h2, h3]
  let SS : Ω → ℝ := fun ω => ⨆ j : ↥S, (X ω (j : Fin p) / coordStdDev μ X (j : Fin p) + x * ((if 0 ≤ x then 1 / sigmaUnder μ X else 1 / sigmaOver μ X) - 1 / coordStdDev μ X (j : Fin p)))
  let FF : Ω → ℝ := fun ω => ⨆ j : Fin p, (X ω j / coordStdDev μ X j + x * ((if 0 ≤ x then 1 / sigmaUnder μ X else 1 / sigmaOver μ X) - 1 / coordStdDev μ X j))
  have hcmax : ∀ ω, coordMax V ω = SS ω := by
    intro ω
    exact hreindex (fun j : ↥S => X ω (j : Fin p) / coordStdDev μ X (j : Fin p) + x * ((if 0 ≤ x then 1 / sigmaUnder μ X else 1 / sigmaOver μ X) - 1 / coordStdDev μ X (j : Fin p)))
  have hSS_aes : AEStronglyMeasurable SS μ := by
    apply AEMeasurable.aestronglyMeasurable
    exact AEMeasurable.iSup (fun j : ↥S => (((hL2 (j : Fin p)).mul_const (coordStdDev μ X (j : Fin p))⁻¹).add (memLp_const (x * ((if 0 ≤ x then 1 / sigmaUnder μ X else 1 / sigmaOver μ X) - 1 / coordStdDev μ X (j : Fin p))))).aestronglyMeasurable.aemeasurable)
  have hFF_aes : AEStronglyMeasurable FF μ := by
    apply AEMeasurable.aestronglyMeasurable
    exact AEMeasurable.iSup (fun j : Fin p => (((hL2 j).mul_const (coordStdDev μ X j)⁻¹).add (memLp_const (x * ((if 0 ≤ x then 1 / sigmaUnder μ X else 1 / sigmaOver μ X) - 1 / coordStdDev μ X j)))).aestronglyMeasurable.aemeasurable)
  have hSW_ae : ∀ᵐ ω ∂μ, SS ω = FF ω :=
    (MeasureTheory.mem_ae_iff_prob_eq_one₀ (AEStronglyMeasurable.nullMeasurableSet_eq_fun hSS_aes hFF_aes)).mpr hS_W
  have hEaeq : {ω | |(⨆ j : Fin p, (X ω j - x) / coordStdDev μ X j)| ≤ ε / sigmaUnder μ X} =ᶠ[ae μ] {ω | |coordMax V ω - x * (if 0 ≤ x then 1 / sigmaUnder μ X else 1 / sigmaOver μ X)| ≤ ε / sigmaUnder μ X} := by
    filter_upwards [hSW_ae] with ω hω
    have h1 : coordMax V ω - x * (if 0 ≤ x then 1 / sigmaUnder μ X else 1 / sigmaOver μ X) = ⨆ j : Fin p, (X ω j - x) / coordStdDev μ X j := by
      rw [hcmax ω, hω]
      exact hId1 ω
    show (|(⨆ j : Fin p, (X ω j - x) / coordStdDev μ X j)| ≤ ε / sigmaUnder μ X) = (|coordMax V ω - x * (if 0 ≤ x then 1 / sigmaUnder μ X else 1 / sigmaOver μ X)| ≤ ε / sigmaUnder μ X)
    rw [h1]
  have hμeq : μ {ω | |(⨆ j : Fin p, (X ω j - x) / coordStdDev μ X j)| ≤ ε / sigmaUnder μ X} = μ {ω | |coordMax V ω - x * (if 0 ≤ x then 1 / sigmaUnder μ X else 1 / sigmaOver μ X)| ≤ ε / sigmaUnder μ X} :=
    MeasureTheory.measure_congr hEaeq
  have hRHS : ENNReal.ofReal (4 * (ε / sigmaUnder μ X) * (b + (∫ ω, coordMax (fun ω' k => V ω' k - nu' k) ω ∂μ) + 1)) = ENNReal.ofReal (4 * ε / sigmaUnder μ X * ((1 / sigmaUnder μ X - 1 / sigmaOver μ X) * |x| + standardizedMaxMean μ X + 1)) := by
    congr 1
    rw [hã]
    simp only [b]
    ring
  rw [hμeq, ← hRHS]
  exact hbound
  /- @proof-region region.target-node.session.55276ce0e5764afc end -/

end Statlib.Imported

