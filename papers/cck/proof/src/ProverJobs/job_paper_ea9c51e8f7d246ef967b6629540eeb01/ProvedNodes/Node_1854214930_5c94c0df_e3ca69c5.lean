import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.Vocabulary
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.Base
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.ProvedNodes.Node_2606212885_28c76b68_e993dd06
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.ProvedNodes.Node_3156732339_a370e2ae_9f516c41
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.ExternalNodes.Node_6515c10a3b2a6920f75d

namespace PaperProofTasks.job_paper_ea9c51e8f7d246ef967b6629540eeb01



open _root_.PaperProofTasks.job_paper_ea9c51e8f7d246ef967b6629540eeb01.Statlib.Imported
open MeasureTheory ProbabilityTheory
open PaperProofTasks.job_paper_a86aea8c92ff4120874a0fdca6db77c5.Statlib.Imported
open scoped BigOperators

namespace Statlib.Imported

open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_1854214930_5c94c0df : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℕ) (hp : 0 < p)
    (X Y : Ω → Fin p → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (SigmaX SigmaY : Matrix (Fin p) (Fin p) ℝ)
    (hSigmaX : SigmaX = SigmaX.transpose) (hSigmaY : SigmaY = SigmaY.transpose)
    (SigmaXY : Matrix (Fin (p + p)) (Fin (p + p)) ℝ)
    (hXY : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ
      (fun ω : Ω => Fin.append (X ω) (Y ω)) SigmaXY)
    (hintX : ∀ j k : Fin p, Integrable (fun ω => X ω j * X ω k) μ)
    (hintY : ∀ j k : Fin p, Integrable (fun ω => Y ω j * Y ω k) μ)
    (hintXY : ∀ j k : Fin p, Integrable (fun ω => X ω j * Y ω k) μ)
    (hmomX : ∀ j k : Fin p, ∫ ω, X ω j * X ω k ∂μ = SigmaX j k)
    (hmomY : ∀ j k : Fin p, ∫ ω, Y ω j * Y ω k ∂μ = SigmaY j k)
    (hmomXY : ∀ j k : Fin p, ∫ ω, X ω j * Y ω k ∂μ = 0)
    (β : ℝ) (hβ : 0 < β) (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g)
    (hg1 : BddAbove (Set.range fun z : ℝ => |deriv g z|))
    (hg2 : BddAbove (Set.range fun z : ℝ => |deriv (deriv g) z|))
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) (j : Fin p),
    ∫ ω, (fderiv ℝ (fun z : Fin p → ℝ =>
        g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z)))
        (fun i => Real.sqrt t * X ω i + Real.sqrt (1 - t) * Y ω i)) (Pi.single j 1)
      * (t ^ (-(1 / 2) : ℝ) * X ω j - (1 - t) ^ (-(1 / 2) : ℝ) * Y ω j) ∂μ
    = ∑ k : Fin p, (SigmaX j k - SigmaY j k) *
        ∫ ω, coordPartial k (coordPartial j (compSmoothMax (p := p) g β))
          (fun i => Real.sqrt t * X ω i + Real.sqrt (1 - t) * Y ω i) ∂μ := by
  /- @proof-region region.target-node.session.d72322dcb4a40f6f begin -/
  intro Ω _ μ _ p hp X Y hX hY SigmaX SigmaY hSigmaX hSigmaY SigmaXY hXY hintX hintY hintXY
    hmomX hmomY hmomXY β hβ g hg hg1 hg2 t ht j
  obtain ⟨ht0, ht1⟩ := ht
  set m : (Fin p → ℝ) → ℝ := compSmoothMax (p := p) g β with hm
  have hmM : m = fun z : Fin p → ℝ =>
      g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z)) := by
    rw [hm]
    funext z
    simp [compSmoothMax, smoothMaxFun, Statlib.StatFoundation.Convergence.smoothMax]
  have hproj : ∀ l : Fin p, ContDiff ℝ 2 (fun z : Fin p → ℝ => z l) := fun l =>
    ContinuousLinearMap.contDiff (ContinuousLinearMap.proj l : (Fin p → ℝ) →L[ℝ] ℝ)
  have hS : ContDiff ℝ 2 (fun z : Fin p → ℝ => ∑ l, Real.exp (β * z l)) := by
    refine ContDiff.sum (fun l _ => ?_)
    exact Real.contDiff_exp.comp (ContDiff.mul contDiff_const (hproj l))
  have hSpos : ∀ z : Fin p → ℝ, 0 < ∑ l, Real.exp (β * z l) := by
    intro z
    exact Finset.sum_pos (fun l _ => Real.exp_pos _) ⟨⟨0, hp⟩, Finset.mem_univ _⟩
  have hlogcont : ContDiff ℝ 2 (fun z : Fin p → ℝ => Real.log (∑ l, Real.exp (β * z l))) :=
    ContDiff.log hS (fun z => ne_of_gt (hSpos z))
  have hsmfun : ContDiff ℝ 2 (fun z : Fin p → ℝ => smoothMaxFun β z) := by
    simp only [smoothMaxFun]
    exact ContDiff.mul contDiff_const hlogcont
  have hm2 : ContDiff ℝ 2 m := by
    rw [hm]
    have h : ContDiff ℝ 2 (fun z : Fin p → ℝ => g (smoothMaxFun β z)) := hg.comp hsmfun
    simpa only [compSmoothMax] using h
  have hA1 : ∀ z : Fin p → ℝ, coordPartial j m z = (fderiv ℝ m z) (Pi.single j 1) := by
    intro z
    have hd : HasFDerivAt m (fderiv ℝ m z) z :=
      ((hm2.contDiffAt).differentiableAt (by norm_num)).hasFDerivAt
    have hzeq : Function.update z j (z j) = z := by
      funext i
      by_cases hi : i = j
      · subst hi
        simp
      · simp [Function.update_apply, hi]
    have hd' : HasFDerivAt m (fderiv ℝ m z) (Function.update z j (z j)) := by
      rw [hzeq]
      exact hd
    have hcomp : HasDerivAt (fun s : ℝ => m (Function.update z j s))
        ((fderiv ℝ m z) (Pi.single j 1)) (z j) :=
      HasFDerivAt.comp_hasDerivAt (z j) hd' (hasDerivAt_update z j (z j))
    exact hcomp.deriv
  have hfd : ContDiff ℝ 1 (fun z : Fin p → ℝ => fderiv ℝ m z) := by
    have hun : ContDiff ℝ 2 (Function.uncurry (fun (_ : Fin p → ℝ) => m)) := by
      simpa only [Function.uncurry, Function.comp_apply] using hm2.comp contDiff_snd
    have hid : ContDiff ℝ 1 (fun z : Fin p → ℝ => z) := contDiff_id
    have h := ContDiff.fderiv (𝕜 := ℝ) (f := fun (_ : Fin p → ℝ) => m)
      (g := fun z : Fin p → ℝ => z) hun hid (by norm_num)
    simpa using h
  have htail : ContDiff ℝ 1
      (fun w : EuclideanSpace ℝ (Fin (p + 1)) => fun i : Fin p => w.ofLp (Fin.succ i)) := by
    refine contDiff_pi' (fun i => ?_)
    exact contDiff_piLp_apply (2 : ENNReal) (n := (1 : WithTop ℕ∞)) (i := Fin.succ i)
  have hfderiv : ContDiff ℝ 1 (fun w : EuclideanSpace ℝ (Fin (p + 1)) =>
      fderiv ℝ m (fun i : Fin p => w.ofLp (Fin.succ i))) := hfd.comp htail
  have hf' : ContDiff ℝ 1 (fun w : EuclideanSpace ℝ (Fin (p + 1)) =>
      (fderiv ℝ m (fun i : Fin p => w.ofLp (Fin.succ i))) (Pi.single j 1)) :=
    hfderiv.clm_apply contDiff_const
  have hf : ContDiff ℝ 1 (fun w : EuclideanSpace ℝ (Fin (p + 1)) =>
      coordPartial j m (fun i : Fin p => w.ofLp (Fin.succ i))) := by
    have heq : (fun w : EuclideanSpace ℝ (Fin (p + 1)) =>
        coordPartial j m (fun i : Fin p => w.ofLp (Fin.succ i)))
        = fun w => (fderiv ℝ m (fun i : Fin p => w.ofLp (Fin.succ i))) (Pi.single j 1) := by
      funext w
      exact hA1 _
    rw [heq]
    exact hf'
  set A : Matrix (Fin (p + 1)) (Fin (p + p)) ℝ :=
    Fin.cons
      (fun a => (if a = Fin.castAdd p j then t ^ (-(1 / 2) : ℝ) else 0) -
        (if a = Fin.natAdd p j then (1 - t) ^ (-(1 / 2) : ℝ) else 0))
      (fun i a => (if a = Fin.castAdd p i then Real.sqrt t else 0) +
        (if a = Fin.natAdd p i then Real.sqrt (1 - t) else 0)) with hA
  set W : Ω → Fin (p + 1) → ℝ :=
    fun ω i => ∑ a, A i a * Fin.append (X ω) (Y ω) a with hWdef
  have happX : ∀ (ω : Ω) (i : Fin p), Fin.append (X ω) (Y ω) (Fin.castAdd p i) = X ω i :=
    fun ω i => Fin.append_left' (X ω) (Y ω) i
  have happY : ∀ (ω : Ω) (i : Fin p), Fin.append (X ω) (Y ω) (Fin.natAdd p i) = Y ω i :=
    fun ω i => Fin.append_right (X ω) (Y ω) i
  have hsingle : ∀ (c : Fin (p + p)) (α : ℝ) (v : Fin (p + p) → ℝ),
      (∑ a, (if a = c then α else 0) * v a) = α * v c := by
    intro c α v
    rw [Finset.sum_eq_single c]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_univ c) h
  have hzero_row : A 0 = fun a => (if a = Fin.castAdd p j then t ^ (-(1 / 2) : ℝ) else 0) -
      (if a = Fin.natAdd p j then (1 - t) ^ (-(1 / 2) : ℝ) else 0) := by
    rw [hA]
    exact Fin.cons_zero _ _
  have hsucc_row : ∀ i : Fin p, A (Fin.succ i) = fun a =>
      (if a = Fin.castAdd p i then Real.sqrt t else 0) +
        (if a = Fin.natAdd p i then Real.sqrt (1 - t) else 0) := by
    intro i
    rw [hA]
    exact Fin.cons_succ _ _ i
  have hW0 : ∀ ω : Ω,
      W ω 0 = t ^ (-(1 / 2) : ℝ) * X ω j - (1 - t) ^ (-(1 / 2) : ℝ) * Y ω j := by
    intro ω
    simp only [hWdef, hzero_row, sub_mul, Finset.sum_sub_distrib]
    rw [hsingle (Fin.castAdd p j) (t ^ (-(1 / 2) : ℝ)) (Fin.append (X ω) (Y ω)),
      hsingle (Fin.natAdd p j) ((1 - t) ^ (-(1 / 2) : ℝ)) (Fin.append (X ω) (Y ω)),
      happX ω j, happY ω j]
  have hWsucc : ∀ (ω : Ω) (i : Fin p),
      W ω (Fin.succ i) = Real.sqrt t * X ω i + Real.sqrt (1 - t) * Y ω i := by
    intro ω i
    simp only [hWdef, hsucc_row i, add_mul, Finset.sum_add_distrib]
    rw [hsingle (Fin.castAdd p i) (Real.sqrt t) (Fin.append (X ω) (Y ω)),
      hsingle (Fin.natAdd p i) (Real.sqrt (1 - t)) (Fin.append (X ω) (Y ω)),
      happX ω i, happY ω i]
  have hWu : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ W
      (A * SigmaXY * A.transpose) :=
    Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.linearImage
      μ (fun ω => Fin.append (X ω) (Y ω)) SigmaXY hXY A
  set Zt : Ω → Fin p → ℝ := fun ω i => Real.sqrt t * X ω i + Real.sqrt (1 - t) * Y ω i
    with hZtdef
  set F : (Fin (p + 1) → ℝ) → ℝ := fun w => coordPartial j m (fun i => w (Fin.succ i))
    with hF
  have hslice : ∀ (ω : Ω) (i : Fin p) (s : ℝ),
      (fun i' : Fin p => (Function.update (W ω) (Fin.succ i) s) (Fin.succ i'))
        = Function.update (Zt ω) i s := by
    intro ω i s
    funext i'
    simp only [Function.update_apply, Fin.succ_inj, hWsucc, hZtdef]
  have hderiv_succ : ∀ (ω : Ω) (i : Fin p),
      deriv (fun s : ℝ => F (Function.update (W ω) (Fin.succ i) s)) (W ω (Fin.succ i))
        = coordPartial i (coordPartial j m) (Zt ω) := by
    intro ω i
    have h1 : (fun s : ℝ => F (Function.update (W ω) (Fin.succ i) s))
        = fun s => coordPartial j m (Function.update (Zt ω) i s) := by
      funext s
      simp only [hF, hslice ω i s]
    have h2 : W ω (Fin.succ i) = Zt ω i := by
      simp only [hWsucc, hZtdef]
    rw [h1, h2]
    rfl
  have hderiv_zero : ∀ ω : Ω,
      deriv (fun s : ℝ => F (Function.update (W ω) 0 s)) (W ω 0) = 0 := by
    intro ω
    have hconst : (fun s : ℝ => F (Function.update (W ω) 0 s)) = fun _ => F (W ω) := by
      funext s
      have hfun : (fun i : Fin p => (Function.update (W ω) 0 s) (Fin.succ i))
          = fun i => W ω (Fin.succ i) := by
        funext i
        simp [Function.update_apply, Fin.succ_ne_zero]
      show coordPartial j m (fun i : Fin p => (Function.update (W ω) 0 s) (Fin.succ i))
        = coordPartial j m (fun i : Fin p => W ω (Fin.succ i))
      rw [hfun]
    rw [hconst]
    simp
  have hZmeas : Measurable Zt := by
    rw [hZtdef]
    refine measurable_pi_iff.mpr (fun i => ?_)
    have h1 : Measurable (fun ω : Ω => Real.sqrt t * X ω i) :=
      measurable_const.mul ((measurable_pi_iff.mp hX) i)
    have h2 : Measurable (fun ω : Ω => Real.sqrt (1 - t) * Y ω i) :=
      measurable_const.mul ((measurable_pi_iff.mp hY) i)
    exact h1.add h2
  have hZint : ∀ i : Fin p,
      Integrable (fun ω => coordPartial i (coordPartial j m) (Zt ω)) μ :=
    fun i =>
      (statopia_math_node_3156732339_a370e2ae μ p hp Zt hZmeas β hβ g hg hg1 hg2).2.1 i j
  have hint : ∀ k : Fin (p + 1),
      Integrable (fun ω => |deriv (fun s : ℝ => F (Function.update (W ω) k s)) (W ω k)|) μ := by
    intro k
    refine Fin.cases ?_ (fun i => ?_) k
    · have hzero : (fun ω : Ω => |deriv (fun s : ℝ => F (Function.update (W ω) 0 s)) (W ω 0)|)
          = fun _ => (0 : ℝ) := by
        funext ω
        rw [hderiv_zero ω]
        simp
      rw [hzero]
      exact integrable_const (μ := μ) (0 : ℝ)
    · have heq : (fun ω : Ω =>
          |deriv (fun s : ℝ => F (Function.update (W ω) (Fin.succ i) s)) (W ω (Fin.succ i))|)
          = fun ω => |coordPartial i (coordPartial j m) (Zt ω)| := by
        funext ω
        rw [hderiv_succ ω i]
      rw [heq]
      exact (hZint i).abs
  have hac : t ^ (-(1 / 2) : ℝ) * Real.sqrt t = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht0,
      show (-(1 / 2) : ℝ) + 1 / 2 = 0 by norm_num, Real.rpow_zero]
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have hbd : (1 - t) ^ (-(1 / 2) : ℝ) * Real.sqrt (1 - t) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add h1t,
      show (-(1 / 2) : ℝ) + 1 / 2 = 0 by norm_num, Real.rpow_zero]
  have hsmul : ∀ (c y : ℝ), c * y = y • c := by
    intro c y
    show c * y = y * c
    rw [mul_comm]
  have halg : ∀ (a b c d X1 X2 Y1 Y2 : ℝ), a * c = 1 → b * d = 1 →
      (a * X1 - b * Y1) * (c * X2 + d * Y2)
        = (X1 * X2 - Y1 * Y2) + ((a * d) * (X1 * Y2) - (b * c) * (Y1 * X2)) := by
    intro a b c d X1 X2 Y1 Y2 h1 h2
    calc (a * X1 - b * Y1) * (c * X2 + d * Y2)
        = a * c * (X1 * X2) + a * d * (X1 * Y2) - b * c * (Y1 * X2)
            - b * d * (Y1 * Y2) := by ring
      _ = (X1 * X2 - Y1 * Y2) + ((a * d) * (X1 * Y2) - (b * c) * (Y1 * X2)) := by
          rw [h1, h2]
          ring
  have hcov : ∀ i : Fin p,
      ∫ ω, W ω 0 * W ω (Fin.succ i) ∂μ = SigmaX j i - SigmaY j i := by
    intro i
    have hI1 : Integrable (fun ω => X ω j * X ω i) μ := hintX j i
    have hI2 : Integrable (fun ω => Y ω j * Y ω i) μ := hintY j i
    have hI3 : Integrable (fun ω => X ω j * Y ω i) μ := hintXY j i
    have hI4 : Integrable (fun ω => Y ω j * X ω i) μ :=
      (hintXY i j).congr (Filter.Eventually.of_forall (fun ω => mul_comm (X ω i) (Y ω j)))
    have hYX : ∫ ω, Y ω j * X ω i ∂μ = 0 := by
      rw [funext (fun ω : Ω => mul_comm (Y ω j) (X ω i))]
      exact hmomXY i j
    have hI3s : Integrable (fun ω =>
        (X ω j * Y ω i) • (t ^ (-(1 / 2) : ℝ) * Real.sqrt (1 - t))) μ := by
      rw [show (fun ω : Ω => (X ω j * Y ω i) • (t ^ (-(1 / 2) : ℝ) * Real.sqrt (1 - t)))
          = fun ω => (t ^ (-(1 / 2) : ℝ) * Real.sqrt (1 - t)) * (X ω j * Y ω i) from
        funext (fun ω => (hsmul _ _).symm)]
      exact hI3.const_mul _
    have hI4s : Integrable (fun ω =>
        (Y ω j * X ω i) • ((1 - t) ^ (-(1 / 2) : ℝ) * Real.sqrt t)) μ := by
      rw [show (fun ω : Ω => (Y ω j * X ω i) • ((1 - t) ^ (-(1 / 2) : ℝ) * Real.sqrt t))
          = fun ω => ((1 - t) ^ (-(1 / 2) : ℝ) * Real.sqrt t) * (Y ω j * X ω i) from
        funext (fun ω => (hsmul _ _).symm)]
      exact hI4.const_mul _
    have hAs : Integrable (fun ω => X ω j * X ω i - Y ω j * Y ω i) μ := hI1.sub hI2
    have hBs : Integrable (fun ω =>
        (X ω j * Y ω i) • (t ^ (-(1 / 2) : ℝ) * Real.sqrt (1 - t))
          - (Y ω j * X ω i) • ((1 - t) ^ (-(1 / 2) : ℝ) * Real.sqrt t)) μ :=
      hI3s.sub hI4s
    have hpt2 : ∀ ω : Ω, W ω 0 * W ω (Fin.succ i)
        = (X ω j * X ω i - Y ω j * Y ω i)
          + ((X ω j * Y ω i) • (t ^ (-(1 / 2) : ℝ) * Real.sqrt (1 - t))
             - (Y ω j * X ω i) • ((1 - t) ^ (-(1 / 2) : ℝ) * Real.sqrt t)) := by
      intro ω
      rw [hW0 ω, hWsucc ω i,
        (hsmul (t ^ (-(1 / 2) : ℝ) * Real.sqrt (1 - t)) (X ω j * Y ω i)).symm,
        (hsmul ((1 - t) ^ (-(1 / 2) : ℝ) * Real.sqrt t) (Y ω j * X ω i)).symm]
      exact halg _ _ _ _ _ _ _ _ hac hbd
    have h1 : (fun ω : Ω => W ω 0 * W ω (Fin.succ i))
        = fun ω => (X ω j * X ω i - Y ω j * Y ω i)
          + ((X ω j * Y ω i) • (t ^ (-(1 / 2) : ℝ) * Real.sqrt (1 - t))
             - (Y ω j * X ω i) • ((1 - t) ^ (-(1 / 2) : ℝ) * Real.sqrt t)) :=
      funext hpt2
    calc ∫ ω, W ω 0 * W ω (Fin.succ i) ∂μ
        = ∫ ω, ((X ω j * X ω i - Y ω j * Y ω i)
            + ((X ω j * Y ω i) • (t ^ (-(1 / 2) : ℝ) * Real.sqrt (1 - t))
               - (Y ω j * X ω i) • ((1 - t) ^ (-(1 / 2) : ℝ) * Real.sqrt t))) ∂μ := by
          rw [h1]
      _ = SigmaX j i - SigmaY j i := by
          rw [integral_add hAs hBs, integral_sub hI1 hI2, integral_sub hI3s hI4s,
            integral_smul_const (fun ω : Ω => X ω j * Y ω i)
              (t ^ (-(1 / 2) : ℝ) * Real.sqrt (1 - t)),
            integral_smul_const (fun ω : Ω => Y ω j * X ω i)
              ((1 - t) ^ (-(1 / 2) : ℝ) * Real.sqrt t),
            hmomX j i, hmomY j i, hmomXY j i, hYX]
          simp
  have hWtail : ∀ ω : Ω, (fun i : Fin p => W ω (Fin.succ i)) = Zt ω := by
    intro ω
    funext i
    simp only [hWsucc, hZtdef]
  have hWtail : ∀ ω : Ω, (fun i : Fin p => W ω (Fin.succ i)) = Zt ω := by
    intro ω
    funext i
    simp only [hWsucc, hZtdef]
  have hFval : ∀ ω : Ω, F (W ω) = coordPartial j m (Zt ω) := by
    intro ω
    show coordPartial j m (fun i : Fin p => W ω (Fin.succ i)) = coordPartial j m (Zt ω)
    rw [hWtail ω]
  have hfF : ContDiff ℝ 1 (fun z : EuclideanSpace ℝ (Fin (p + 1)) => F (WithLp.ofLp z)) := hf
  have hstein := ext_model_1 μ (p + 1) (Nat.succ_pos p) W (A * SigmaXY * A.transpose)
    hWu F hfF hint 0
  have hzero_int :
      ∫ ω, deriv (fun t : ℝ => F (Function.update (W ω) 0 t)) (W ω 0) ∂μ = 0 := by
    have h0 : (fun ω : Ω => deriv (fun t : ℝ => F (Function.update (W ω) 0 t)) (W ω 0))
        = fun _ => 0 := by
      funext ω
      exact hderiv_zero ω
    rw [h0]
    simp
  have hmain : ∫ ω, W ω 0 * F (W ω) ∂μ
      = ∑ i : Fin p, (SigmaX j i - SigmaY j i)
          * ∫ ω, coordPartial i (coordPartial j m) (Zt ω) ∂μ := by
    rw [hstein, Fin.sum_univ_succ, hzero_int, mul_zero, zero_add]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hfun : (fun ω : Ω => deriv (fun s : ℝ => F (Function.update (W ω) (Fin.succ i) s))
          (W ω (Fin.succ i))) = fun ω => coordPartial i (coordPartial j m) (Zt ω) :=
      funext (fun ω => hderiv_succ ω i)
    rw [hcov i, hfun]
  have hLHS : ∫ ω, (fderiv ℝ (fun z : Fin p → ℝ =>
        g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z)))
        (Zt ω)) (Pi.single j 1)
      * (t ^ (-(1 / 2) : ℝ) * X ω j - (1 - t) ^ (-(1 / 2) : ℝ) * Y ω j) ∂μ
      = ∫ ω, W ω 0 * F (W ω) ∂μ := by
    have hfun : (fun ω : Ω => (fderiv ℝ (fun z : Fin p → ℝ =>
          g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z))) (Zt ω))
          (Pi.single j 1)
          * (t ^ (-(1 / 2) : ℝ) * X ω j - (1 - t) ^ (-(1 / 2) : ℝ) * Y ω j))
        = fun ω => W ω 0 * F (W ω) := by
      funext ω
      rw [← hmM, ← hA1, ← hW0 ω, hFval ω, mul_comm]
    rw [hfun]
  exact hLHS.trans hmain
  /- @proof-region region.target-node.session.d72322dcb4a40f6f end -/

end Statlib.Imported

