import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.Vocabulary
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.Base
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.ProvedNodes.Node_2606212885_28c76b68_e993dd06

namespace PaperProofTasks.job_paper_ea9c51e8f7d246ef967b6629540eeb01

open _root_.PaperProofTasks.job_paper_ea9c51e8f7d246ef967b6629540eeb01.Statlib.Imported
open MeasureTheory ProbabilityTheory

namespace Statlib.Imported

open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_2966747390_db21bd2d : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℕ) (hp : 0 < p)
    (X Y : Ω → Fin p → ℝ)
    (SigmaX SigmaY : Matrix (Fin p) (Fin p) ℝ)
    (hX : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ X SigmaX)
    (hY : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ Y SigmaY)
    (β : ℝ) (hβ : 0 < β)
    (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g)
    (hg1 : BddAbove (Set.range fun z : ℝ => |deriv g z|)),
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (μ' : Measure Ω'),
      IsProbabilityMeasure μ' ∧
      ∃ (X' Y' : Ω' → Fin p → ℝ),
        Measurable X' ∧
        Measurable Y' ∧
        (∃ SigmaS : Matrix (Fin (p + p)) (Fin (p + p)) ℝ,
          Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ'
            (fun ω' (i : Fin (p + p)) => Fin.append (X' ω') (Y' ω') i) SigmaS) ∧
        (∀ j k : Fin p, Integrable (fun ω' => X' ω' j * X' ω' k) μ' ∧
            ∫ ω', X' ω' j * X' ω' k ∂μ' = (2 : ℝ)⁻¹ * (SigmaX j k + SigmaX k j)) ∧
        (∀ j k : Fin p, Integrable (fun ω' => Y' ω' j * Y' ω' k) μ' ∧
            ∫ ω', Y' ω' j * Y' ω' k ∂μ' = (2 : ℝ)⁻¹ * (SigmaY j k + SigmaY k j)) ∧
        (∀ j k : Fin p, Integrable (fun ω' => X' ω' j * Y' ω' k) μ' ∧
            ∫ ω', X' ω' j * Y' ω' k ∂μ' = 0) ∧
        Integrable (fun ω => g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (X ω)))) μ ∧
        Integrable (fun ω => g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (Y ω)))) μ ∧
        Integrable (fun ω' => g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (X' ω')))) μ' ∧
        Integrable (fun ω' => g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (Y' ω')))) μ' ∧
        expSmoothMaxDiff μ X Y β g = expSmoothMaxDiff μ' X' Y' β g := by
  /- @proof-region region.target-node.session.cddbfc34feedc590 begin -/
  intro Ω _ μ _ p hp X Y SigmaX SigmaY hX hY β hβ g hg hg1
  have hmeasX : Measurable X := hX.1
  have hmeasY : Measurable Y := hY.1
  have hmax0 : Statlib.StatFoundation.Vocabulary.maxCoord (0 : EuclideanSpace ℝ (Fin p)) = 0 := by
    simp [Statlib.StatFoundation.Vocabulary.maxCoord]
  set SX : Matrix (Fin p) (Fin p) ℝ := (2 : ℝ)⁻¹ • (SigmaX + Matrix.transpose SigmaX) with hSX
  set SY : Matrix (Fin p) (Fin p) ℝ := (2 : ℝ)⁻¹ • (SigmaY + Matrix.transpose SigmaY) with hSY
  set MS : Matrix (Fin p ⊕ Fin p) (Fin p ⊕ Fin p) ℝ :=
    fun i j => Sum.casesOn i (fun a => Sum.casesOn j (fun b => SX a b) (fun _ => 0))
      (fun a => Sum.casesOn j (fun _ => 0) (fun b => SY a b)) with hMS
  set ee : Fin (p + p) ≃ (Fin p ⊕ Fin p) := finSumFinEquiv.symm with hee
  set SigS : Matrix (Fin (p + p)) (Fin (p + p)) ℝ := fun i j => MS (ee i) (ee j) with hSigS
  set S : (Fin (p + p) → ℝ) → Fin (p + p) → ℝ :=
    Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector SigS with hS
  set X' : (Fin (p + p) → ℝ) → Fin p → ℝ := fun ω' j => S ω' (Fin.castAdd p j) with hX'
  set Y' : (Fin (p + p) → ℝ) → Fin p → ℝ := fun ω' k => S ω' (Fin.natAdd p k) with hY'
  set muz : Measure (Fin (p + p) → ℝ) :=
    Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (p + p) with hmuz
  haveI hmuzprob : IsProbabilityMeasure muz := by
    rw [hmuz]
    refine ⟨?hmuz_univ⟩
    simp [Statlib.StatFoundation.RandomVariable.Gaussian.standardPi]
  have hSXpsd : SX.PosSemidef := by
    rw [hSX]
    exact hX.posSemidef_symmetrizedCovariance (by omega : 1 ≤ p)
  have hSYpsd : SY.PosSemidef := by
    rw [hSY]
    exact hY.posSemidef_symmetrizedCovariance (by omega : 1 ≤ p)
  have hSXsym : ∀ a b : Fin p, SX a b = SX b a := by
    intro a b
    simp only [hSX, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
    ring
  have hSYsym : ∀ a b : Fin p, SY a b = SY b a := by
    intro a b
    simp only [hSY, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
    ring
  have hMSherm : MS.IsHermitian := by
    simp only [Matrix.IsHermitian]
    ext i j
    cases i with
    | inl a =>
      cases j with
      | inl b => simpa [hMS] using (hSXsym a b).symm
      | inr b => simp [hMS]
    | inr a =>
      cases j with
      | inl b => simp [hMS]
      | inr b => simpa [hMS] using (hSYsym a b).symm
  have hMSpsd : MS.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hMSherm ?_
    intro x
    have h1 := hSXpsd.dotProduct_mulVec_nonneg (fun a => x (Sum.inl a))
    have h2 := hSYpsd.dotProduct_mulVec_nonneg (fun b => x (Sum.inr b))
    have key : star x ⬝ᵥ MS.mulVec x
        = star (fun a => x (Sum.inl a)) ⬝ᵥ SX.mulVec (fun a => x (Sum.inl a))
          + star (fun b => x (Sum.inr b)) ⬝ᵥ SY.mulVec (fun b => x (Sum.inr b)) := by
      simp [dotProduct, Matrix.mulVec, hMS]
    rw [key]
    linarith
  have hPSD : SigS.PosSemidef := hMSpsd.submatrix ee
  have hSGauss : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector muz S SigS := by
    rw [hS]
    exact Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector_isCenteredGaussianVector
      (by omega : 0 < p + p) SigS hPSD
  have hfun : (fun ω' (i : Fin (p + p)) => Fin.append (X' ω') (Y' ω') i) = S := by
    funext ω' i
    simp only [hX', hY']
    obtain ⟨s, hs⟩ := Equiv.surjective finSumFinEquiv i
    rw [← hs]
    cases s with
    | inl j => simp [finSumFinEquiv_apply_left, Fin.append_left]
    | inr k => rw [finSumFinEquiv_apply_right, Fin.append_right]
  have hcast : ∀ j : Fin p, ee (Fin.castAdd p j) = Sum.inl j := by
    intro j
    rw [hee]
    exact finSumFinEquiv_symm_apply_castAdd j
  have hnat : ∀ j : Fin p, ee (Fin.natAdd p j) = Sum.inr j := by
    intro j
    rw [hee]
    exact finSumFinEquiv_symm_apply_natAdd j
  have hentXX : ∀ j k : Fin p, SigS (Fin.castAdd p j) (Fin.castAdd p k) = SX j k := by
    intro j k
    simp only [hSigS, hMS, hcast j, hcast k]
  have hentYY : ∀ j k : Fin p, SigS (Fin.natAdd p j) (Fin.natAdd p k) = SY j k := by
    intro j k
    simp only [hSigS, hMS, hnat j, hnat k]
  have hentXY : ∀ j k : Fin p, SigS (Fin.castAdd p j) (Fin.natAdd p k) = 0 := by
    intro j k
    simp only [hSigS, hMS, hcast j, hnat k]
  have hentYX : ∀ j k : Fin p, SigS (Fin.natAdd p j) (Fin.castAdd p k) = 0 := by
    intro j k
    simp only [hSigS, hMS, hnat j, hcast k]
  have hcoord : ∀ i : Fin (p + p), Measurable (fun ω' => S ω' i) :=
    fun i => (measurable_pi_apply i).comp hSGauss.1
  have hQ1 : Measurable X' := by
    rw [hX']
    exact measurable_pi_iff.mpr (fun j => hcoord (Fin.castAdd p j))
  have hQ2 : Measurable Y' := by
    rw [hY']
    exact measurable_pi_iff.mpr (fun j => hcoord (Fin.natAdd p j))
  have hQ3 : ∃ SigmaS : Matrix (Fin (p + p)) (Fin (p + p)) ℝ,
      Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector muz
        (fun ω' (i : Fin (p + p)) => Fin.append (X' ω') (Y' ω') i) SigmaS :=
    ⟨SigS, by rw [hfun]; exact hSGauss⟩
  have hQ4 : ∀ j k : Fin p, Integrable (fun ω' => X' ω' j * X' ω' k) muz ∧
      ∫ ω', X' ω' j * X' ω' k ∂muz = (2 : ℝ)⁻¹ * (SigmaX j k + SigmaX k j) := by
    intro j k
    have hd := statopia_math_node_2606212885_28c76b68 muz (p + p) (by omega) S SigS hSGauss
      (Fin.castAdd p j) (Fin.castAdd p k)
    refine ⟨?_, ?_⟩
    · simpa only [hX'] using hd.1
    · rw [show (∫ ω', X' ω' j * X' ω' k ∂muz)
            = ∫ ω', S ω' (Fin.castAdd p j) * S ω' (Fin.castAdd p k) ∂muz from by simp only [hX'],
          hd.2.1, hentXX j k, hentXX k j]
      simp only [hSX, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
      ring
  have hQ5 : ∀ j k : Fin p, Integrable (fun ω' => Y' ω' j * Y' ω' k) muz ∧
      ∫ ω', Y' ω' j * Y' ω' k ∂muz = (2 : ℝ)⁻¹ * (SigmaY j k + SigmaY k j) := by
    intro j k
    have hd := statopia_math_node_2606212885_28c76b68 muz (p + p) (by omega) S SigS hSGauss
      (Fin.natAdd p j) (Fin.natAdd p k)
    refine ⟨?_, ?_⟩
    · simpa only [hY'] using hd.1
    · rw [show (∫ ω', Y' ω' j * Y' ω' k ∂muz)
            = ∫ ω', S ω' (Fin.natAdd p j) * S ω' (Fin.natAdd p k) ∂muz from by simp only [hY'],
          hd.2.1, hentYY j k, hentYY k j]
      simp only [hSY, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
      ring
  have hQ6 : ∀ j k : Fin p, Integrable (fun ω' => X' ω' j * Y' ω' k) muz ∧
      ∫ ω', X' ω' j * Y' ω' k ∂muz = 0 := by
    intro j k
    have hd := statopia_math_node_2606212885_28c76b68 muz (p + p) (by omega) S SigS hSGauss
      (Fin.castAdd p j) (Fin.natAdd p k)
    refine ⟨?_, ?_⟩
    · simpa only [hX', hY'] using hd.1
    · rw [show (∫ ω', X' ω' j * Y' ω' k ∂muz)
            = ∫ ω', S ω' (Fin.castAdd p j) * S ω' (Fin.natAdd p k) ∂muz from by simp only [hX', hY'],
          hd.2.1, hentXY j k, hentYX k j]
      ring
  have hXsq : ∀ j k : Fin p, Integrable (fun ω => X ω j * X ω k) μ :=
    fun j k => (statopia_math_node_2606212885_28c76b68 μ p hp X SigmaX hX j k).1
  have hYsq : ∀ j k : Fin p, Integrable (fun ω => Y ω j * Y ω k) μ :=
    fun j k => (statopia_math_node_2606212885_28c76b68 μ p hp Y SigmaY hY j k).1
  obtain ⟨M, hM⟩ := hg1
  have hderiv : ∀ y : ℝ, |deriv g y| ≤ M := fun y => hM ⟨y, rfl⟩
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (deriv g 0)) (hderiv 0)
  have hgd : ∀ y : ℝ, DifferentiableAt ℝ g y := fun y => hg.differentiable (by norm_num) y
  have hLip : ∀ a b : ℝ, |g a - g b| ≤ M * |a - b| := by
    intro a b
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (G := ℝ) (f := g) (s := Set.univ)
      (x := b) (y := a) (C := M) (fun y _ => hgd y) (fun y _ => by simpa using hderiv y)
      convex_univ (Set.mem_univ b) (Set.mem_univ a)
    simpa using h
  have hc : (0:ℝ) ≤ Real.log (p:ℝ) / β := by
    have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
    have hl : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg hp1
    positivity
  have hofLp : ∀ (w : Fin p → ℝ) (j : Fin p), (WithLp.toLp 2 w).ofLp j = w j := fun w j => rfl
  have hstep : ∀ z : EuclideanSpace ℝ (Fin p),
      |g (Statlib.StatFoundation.Convergence.smoothMax β z)|
        ≤ |g 0| + M * ((∑ j, ‖z.ofLp j‖ ^ 2) + 1 + Real.log (p:ℝ) / β) := by
    intro z
    obtain ⟨hlo, hhi⟩ := Statlib.StatFoundation.Convergence.smoothMax_bounds_max_log_card p hp β hβ z
    have hdist := (lipschitzWith_iff_dist_le_mul.mp
      (Statlib.StatFoundation.Convergence.maxCoord_lipschitz p)) z 0
    have hmaxz : |Statlib.StatFoundation.Vocabulary.maxCoord z| ≤ ‖z‖ := by
      simpa [Real.dist_eq, hmax0] using hdist
    obtain ⟨hm1, hm2⟩ := abs_le.mp hmaxz
    have hF : |Statlib.StatFoundation.Convergence.smoothMax β z| ≤ ‖z‖ + Real.log (p:ℝ) / β := by
      rw [abs_le]
      constructor <;> nlinarith [hm1, hm2, hlo, hhi]
    have hz1 : ‖z‖ ≤ (∑ j, ‖z.ofLp j‖ ^ 2) + 1 := by
      nlinarith [EuclideanSpace.norm_sq_eq (𝕜 := ℝ) z, sq_nonneg (‖z‖ - 1), norm_nonneg z]
    have hgF : |g (Statlib.StatFoundation.Convergence.smoothMax β z)|
        ≤ |g 0| + M * |Statlib.StatFoundation.Convergence.smoothMax β z| := by
      have h := hLip (Statlib.StatFoundation.Convergence.smoothMax β z) 0
      simp only [sub_zero] at h
      obtain ⟨h1, h2⟩ := abs_le.mp h
      rw [abs_le]
      constructor <;> nlinarith [neg_abs_le (g 0), le_abs_self (g 0)]
    have hF2 : |Statlib.StatFoundation.Convergence.smoothMax β z|
        ≤ (∑ j, ‖z.ofLp j‖ ^ 2) + 1 + Real.log (p:ℝ) / β := by linarith
    nlinarith [hM0, hF2, abs_nonneg (g 0)]
  have hmeasTgt : Measurable (fun z : Fin p → ℝ =>
      g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z))) := by
    have hsm : Measurable (Statlib.StatFoundation.Convergence.smoothMax β) :=
      (Statlib.StatFoundation.Convergence.smoothMax_def_measurable_continuous hp hβ).2
    have htl : Measurable (fun z : Fin p → ℝ => WithLp.toLp 2 z) :=
      WithLp.measurable_toLp 2 (Fin p → ℝ)
    exact hg.continuous.measurable.comp (hsm.comp htl)
  have hQ7 : Integrable (fun ω => g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (X ω)))) μ := by
    have h1 : Integrable (fun ω => ∑ j, ‖X ω j‖ ^ 2) μ := by
      have h := integrable_finset_sum (s := Finset.univ) (f := fun j (ω : Ω) => ‖X ω j‖ ^ 2)
        (fun j _ => by simpa [pow_two, sq_abs] using hXsq j j)
      simpa using h
    have hdom : Integrable (fun ω => |g 0| + M * ((∑ j, ‖X ω j‖ ^ 2) + 1 + Real.log (p:ℝ) / β)) μ := by
      have h2 : Integrable (fun ω => (∑ j, ‖X ω j‖ ^ 2) + 1 + Real.log (p:ℝ) / β) μ :=
        (h1.add (integrable_const (1:ℝ))).add (integrable_const (Real.log (p:ℝ) / β))
      exact (integrable_const (|g 0|)).add (h2.const_mul M)
    have haesm : AEStronglyMeasurable
        (fun ω => g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (X ω)))) μ :=
      hmeasTgt.comp hmeasX |>.aestronglyMeasurable
    have hle : ∀ᵐ ω ∂μ, ‖g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (X ω)))‖
        ≤ |g 0| + M * ((∑ j, ‖X ω j‖ ^ 2) + 1 + Real.log (p:ℝ) / β) := by
      filter_upwards with ω
      have h := hstep (WithLp.toLp 2 (X ω))
      simpa [hofLp] using h
    exact Integrable.mono' hdom haesm hle
  have hQ8 : Integrable (fun ω => g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (Y ω)))) μ := by
    have h1 : Integrable (fun ω => ∑ j, ‖Y ω j‖ ^ 2) μ := by
      have h := integrable_finset_sum (s := Finset.univ) (f := fun j (ω : Ω) => ‖Y ω j‖ ^ 2)
        (fun j _ => by simpa [pow_two, sq_abs] using hYsq j j)
      simpa using h
    have hdom : Integrable (fun ω => |g 0| + M * ((∑ j, ‖Y ω j‖ ^ 2) + 1 + Real.log (p:ℝ) / β)) μ := by
      have h2 : Integrable (fun ω => (∑ j, ‖Y ω j‖ ^ 2) + 1 + Real.log (p:ℝ) / β) μ :=
        (h1.add (integrable_const (1:ℝ))).add (integrable_const (Real.log (p:ℝ) / β))
      exact (integrable_const (|g 0|)).add (h2.const_mul M)
    have haesm : AEStronglyMeasurable
        (fun ω => g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (Y ω)))) μ :=
      hmeasTgt.comp hmeasY |>.aestronglyMeasurable
    have hle : ∀ᵐ ω ∂μ, ‖g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (Y ω)))‖
        ≤ |g 0| + M * ((∑ j, ‖Y ω j‖ ^ 2) + 1 + Real.log (p:ℝ) / β) := by
      filter_upwards with ω
      have h := hstep (WithLp.toLp 2 (Y ω))
      simpa [hofLp] using h
    exact Integrable.mono' hdom haesm hle
  have hQ9 : Integrable (fun ω' => g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (X' ω')))) muz := by
    have h1 : Integrable (fun ω' => ∑ j, ‖X' ω' j‖ ^ 2) muz := by
      have h := integrable_finset_sum (s := Finset.univ)
        (f := fun j (ω' : Fin (p + p) → ℝ) => ‖X' ω' j‖ ^ 2)
        (fun j _ => by simpa [pow_two, sq_abs] using (hQ4 j j).1)
      simpa using h
    have hdom : Integrable (fun ω' => |g 0| + M * ((∑ j, ‖X' ω' j‖ ^ 2) + 1 + Real.log (p:ℝ) / β)) muz := by
      have h2 : Integrable (fun ω' => (∑ j, ‖X' ω' j‖ ^ 2) + 1 + Real.log (p:ℝ) / β) muz :=
        (h1.add (integrable_const (1:ℝ))).add (integrable_const (Real.log (p:ℝ) / β))
      exact (integrable_const (|g 0|)).add (h2.const_mul M)
    have haesm : AEStronglyMeasurable
        (fun ω' => g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (X' ω')))) muz :=
      hmeasTgt.comp hQ1 |>.aestronglyMeasurable
    have hle : ∀ᵐ ω' ∂muz, ‖g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (X' ω')))‖
        ≤ |g 0| + M * ((∑ j, ‖X' ω' j‖ ^ 2) + 1 + Real.log (p:ℝ) / β) := by
      filter_upwards with ω'
      have h := hstep (WithLp.toLp 2 (X' ω'))
      simpa [hofLp] using h
    exact Integrable.mono' hdom haesm hle
  have hQ10 : Integrable (fun ω' => g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (Y' ω')))) muz := by
    have h1 : Integrable (fun ω' => ∑ j, ‖Y' ω' j‖ ^ 2) muz := by
      have h := integrable_finset_sum (s := Finset.univ)
        (f := fun j (ω' : Fin (p + p) → ℝ) => ‖Y' ω' j‖ ^ 2)
        (fun j _ => by simpa [pow_two, sq_abs] using (hQ5 j j).1)
      simpa using h
    have hdom : Integrable (fun ω' => |g 0| + M * ((∑ j, ‖Y' ω' j‖ ^ 2) + 1 + Real.log (p:ℝ) / β)) muz := by
      have h2 : Integrable (fun ω' => (∑ j, ‖Y' ω' j‖ ^ 2) + 1 + Real.log (p:ℝ) / β) muz :=
        (h1.add (integrable_const (1:ℝ))).add (integrable_const (Real.log (p:ℝ) / β))
      exact (integrable_const (|g 0|)).add (h2.const_mul M)
    have haesm : AEStronglyMeasurable
        (fun ω' => g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (Y' ω')))) muz :=
      hmeasTgt.comp hQ2 |>.aestronglyMeasurable
    have hle : ∀ᵐ ω' ∂muz, ‖g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (Y' ω')))‖
        ≤ |g 0| + M * ((∑ j, ‖Y' ω' j‖ ^ 2) + 1 + Real.log (p:ℝ) / β) := by
      filter_upwards with ω'
      have h := hstep (WithLp.toLp 2 (Y' ω'))
      simpa [hofLp] using h
    exact Integrable.mono' hdom haesm hle
  set A : Matrix (Fin p) (Fin (p + p)) ℝ := fun j i => if i = Fin.castAdd p j then 1 else 0 with hA
  set B : Matrix (Fin p) (Fin (p + p)) ℝ := fun k i => if i = Fin.natAdd p k then 1 else 0 with hB
  have hrow : ∀ (C : Matrix (Fin p) (Fin (p + p)) ℝ) (a : Fin p → Fin (p + p)),
      (∀ j i, C j i = if i = a j then 1 else 0) →
      ∀ (j : Fin p) (f : Fin (p + p) → ℝ), (∑ i, C j i * f i) = f (a j) := by
    intro C a hC j f
    simp only [hC, ite_mul, one_mul, zero_mul]
    simp
  have hArow : ∀ (j : Fin p) (f : Fin (p + p) → ℝ), (∑ i, A j i * f i) = f (Fin.castAdd p j) :=
    hrow A (fun j => Fin.castAdd p j) (fun j i => by simp only [hA])
  have hBrow : ∀ (k : Fin p) (f : Fin (p + p) → ℝ), (∑ i, B k i * f i) = f (Fin.natAdd p k) :=
    hrow B (fun k => Fin.natAdd p k) (fun j i => by simp only [hB])
  have hAmv : ∀ (ω' : Fin (p + p) → ℝ), A.mulVec (S ω') = X' ω' := by
    intro ω'
    rw [hX']
    funext j
    simp only [Matrix.mulVec, dotProduct]
    exact hArow j (fun i => S ω' i)
  have hBmv : ∀ (ω' : Fin (p + p) → ℝ), B.mulVec (S ω') = Y' ω' := by
    intro ω'
    rw [hY']
    funext k
    simp only [Matrix.mulVec, dotProduct]
    exact hBrow k (fun i => S ω' i)
  have hMA : A * SigS * A.transpose = SX := by
    ext j k
    have h1 : ∀ i : Fin (p + p), (A * SigS) j i = SigS (Fin.castAdd p j) i := by
      intro i
      exact hArow j (fun l => SigS l i)
    calc (A * SigS * A.transpose) j k
        = ∑ i, (A * SigS) j i * A.transpose i k := by rw [Matrix.mul_apply]
      _ = ∑ i, (A * SigS) j i * A k i := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [show A.transpose i k = A k i from rfl]
      _ = ∑ i, SigS (Fin.castAdd p j) i * A k i :=
            Finset.sum_congr rfl (fun i _ => by rw [h1 i])
      _ = ∑ i, A k i * SigS (Fin.castAdd p j) i :=
            Finset.sum_congr rfl (fun i _ => mul_comm _ _)
      _ = SigS (Fin.castAdd p j) (Fin.castAdd p k) := hArow k (fun i => SigS (Fin.castAdd p j) i)
      _ = SX j k := hentXX j k
  have hMB : B * SigS * B.transpose = SY := by
    ext j k
    have h1 : ∀ i : Fin (p + p), (B * SigS) j i = SigS (Fin.natAdd p j) i := by
      intro i
      exact hBrow j (fun l => SigS l i)
    calc (B * SigS * B.transpose) j k
        = ∑ i, (B * SigS) j i * B.transpose i k := by rw [Matrix.mul_apply]
      _ = ∑ i, (B * SigS) j i * B k i := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [show B.transpose i k = B k i from rfl]
      _ = ∑ i, SigS (Fin.natAdd p j) i * B k i :=
            Finset.sum_congr rfl (fun i _ => by rw [h1 i])
      _ = ∑ i, B k i * SigS (Fin.natAdd p j) i :=
            Finset.sum_congr rfl (fun i _ => mul_comm _ _)
      _ = SigS (Fin.natAdd p j) (Fin.natAdd p k) := hBrow k (fun i => SigS (Fin.natAdd p j) i)
      _ = SY j k := hentYY j k
  have hMsymX : (2:ℝ)⁻¹ • ((A * SigS * A.transpose) + (A * SigS * A.transpose).transpose) = SX := by
    rw [hMA]
    ext j k
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
    rw [hSXsym k j]
    ring
  have hMsymY : (2:ℝ)⁻¹ • ((B * SigS * B.transpose) + (B * SigS * B.transpose).transpose) = SY := by
    rw [hMB]
    ext j k
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
    rw [hSYsym k j]
    ring
  have hX'cent : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector muz X'
      (A * SigS * A.transpose) := by
    have hlin := Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.linearImage
      muz S SigS hSGauss A
    rw [show (fun ω' => A.mulVec (S ω')) = X' from funext hAmv] at hlin
    exact hlin
  have hY'cent : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector muz Y'
      (B * SigS * B.transpose) := by
    have hlin := Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.linearImage
      muz S SigS hSGauss B
    rw [show (fun ω' => B.mulVec (S ω')) = Y' from funext hBmv] at hlin
    exact hlin
  have hmapX' : Measure.map X' muz = Measure.map
      (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector SX)
      (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi p) := by
    rw [Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.map_eq_canonicalGaussianVector
      hX'cent (by omega : 1 ≤ p), hMsymX]
  have hmapX : Measure.map X μ = Measure.map
      (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector SX)
      (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi p) := by
    rw [Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.map_eq_canonicalGaussianVector
      hX (by omega : 1 ≤ p), ← hSX]
  have hmapXX' : Measure.map X μ = Measure.map X' muz := hmapX.trans hmapX'.symm
  have hmapY' : Measure.map Y' muz = Measure.map
      (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector SY)
      (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi p) := by
    rw [Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.map_eq_canonicalGaussianVector
      hY'cent (by omega : 1 ≤ p), hMsymY]
  have hmapY : Measure.map Y μ = Measure.map
      (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector SY)
      (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi p) := by
    rw [Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.map_eq_canonicalGaussianVector
      hY (by omega : 1 ≤ p), ← hSY]
  have hmapYY' : Measure.map Y μ = Measure.map Y' muz := hmapY.trans hmapY'.symm

  have hIX : ∫ ω, g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (X ω))) ∂μ
      = ∫ ω', g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (X' ω'))) ∂muz := by
    have e1 : ∫ ω, g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (X ω))) ∂μ
        = ∫ y, g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 y)) ∂(Measure.map X μ) :=
      (MeasureTheory.integral_map hmeasX.aemeasurable hmeasTgt.aestronglyMeasurable).symm
    have e2 : ∫ y, g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 y)) ∂(Measure.map X μ)
        = ∫ y, g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 y)) ∂(Measure.map X' muz) := by
      rw [hmapXX']
    have e3 : ∫ y, g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 y)) ∂(Measure.map X' muz)
        = ∫ ω', g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (X' ω'))) ∂muz :=
      MeasureTheory.integral_map hQ1.aemeasurable hmeasTgt.aestronglyMeasurable
    rw [e1, e2, e3]
  have hIY : ∫ ω, g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (Y ω))) ∂μ
      = ∫ ω', g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (Y' ω'))) ∂muz := by
    have e1 : ∫ ω, g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (Y ω))) ∂μ
        = ∫ y, g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 y)) ∂(Measure.map Y μ) :=
      (MeasureTheory.integral_map hmeasY.aemeasurable hmeasTgt.aestronglyMeasurable).symm
    have e2 : ∫ y, g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 y)) ∂(Measure.map Y μ)
        = ∫ y, g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 y)) ∂(Measure.map Y' muz) := by
      rw [hmapYY']
    have e3 : ∫ y, g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 y)) ∂(Measure.map Y' muz)
        = ∫ ω', g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (Y' ω'))) ∂muz :=
      MeasureTheory.integral_map hQ2.aemeasurable hmeasTgt.aestronglyMeasurable
    rw [e1, e2, e3]
  have hQ11 : expSmoothMaxDiff μ X Y β g = expSmoothMaxDiff muz X' Y' β g := by
    simp only [expSmoothMaxDiff]
    rw [integral_sub hQ7 hQ8, integral_sub hQ9 hQ10, hIX, hIY]
  exact ⟨Fin (p + p) → ℝ, inferInstance, muz, hmuzprob, X', Y', hQ1, hQ2, hQ3, hQ4, hQ5, hQ6,
    hQ7, hQ8, hQ9, hQ10, hQ11⟩
  /- @proof-region region.target-node.session.cddbfc34feedc590 end -/

end Statlib.Imported

