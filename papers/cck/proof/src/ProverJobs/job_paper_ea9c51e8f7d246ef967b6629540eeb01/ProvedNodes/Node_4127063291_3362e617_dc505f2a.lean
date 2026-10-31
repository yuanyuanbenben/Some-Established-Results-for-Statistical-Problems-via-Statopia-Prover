import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.Vocabulary
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.Base
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.ProvedNodes.Node_1904015730_8e8aa481_1d108aa5
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.ProvedNodes.Node_2074902041_7cdeb16b_c8de600c
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.ProvedNodes.Node_3156732339_a370e2ae_9f516c41
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.ExternalNodes.Node_af0332c83cb34e8cac43

namespace PaperProofTasks.job_paper_ea9c51e8f7d246ef967b6629540eeb01




open _root_.PaperProofTasks.job_paper_ea9c51e8f7d246ef967b6629540eeb01.Statlib.Imported
open MeasureTheory ProbabilityTheory

namespace Statlib.Imported

open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_4127063291_3362e617 : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℕ) (hp : 0 < p)
    (X Y : Ω → Fin p → ℝ)
    (SigmaX SigmaY : Matrix (Fin p) (Fin p) ℝ)
    (hSigmaX : SigmaX = SigmaX.transpose) (hSigmaY : SigmaY = SigmaY.transpose)
    (hX : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ X SigmaX)
    (hY : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ Y SigmaY)
    (SigmaXY : Matrix (Fin (p + p)) (Fin (p + p)) ℝ)
    (hXY : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ
      (fun ω : Ω => Fin.append (X ω) (Y ω)) SigmaXY)
    (hintX : ∀ j k : Fin p, Integrable (fun ω => X ω j * X ω k) μ)
    (hintY : ∀ j k : Fin p, Integrable (fun ω => Y ω j * Y ω k) μ)
    (hintXY : ∀ j k : Fin p, Integrable (fun ω => X ω j * Y ω k) μ)
    (hmomX : ∀ j k : Fin p, ∫ ω, X ω j * X ω k ∂μ = SigmaX j k)
    (hmomY : ∀ j k : Fin p, ∫ ω, Y ω j * Y ω k ∂μ = SigmaY j k)
    (hmomXY : ∀ j k : Fin p, ∫ ω, X ω j * Y ω k ∂μ = 0)
    (β : ℝ) (hβ : 0 < β)
    (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g)
    (hg1 : BddAbove (Set.range fun z : ℝ => |deriv g z|))
    (hg2 : BddAbove (Set.range fun z : ℝ => |deriv (deriv g) z|))
    (Delta : ℝ) (hDelta : ∀ j k : Fin p, |SigmaX j k - SigmaY j k| ≤ Delta),
    |expSmoothMaxDiff μ X Y β g| ≤
      Delta * (supNormR (deriv (deriv g)) / 2 + β * supNormR (deriv g)) := by
  /- @proof-region region.target-node.session.a2a8a1ccb4ad81d0 begin -/
  intro Ω _instΩ μ _instμ p hp X Y SigmaX SigmaY hSigmaX hSigmaY hX hY SigmaXY hXY hintX hintY hintXY hmomX hmomY hmomXY β hβ g hg hg1 hg2 Delta hDelta
  let W : ℝ → Ω → Fin p → ℝ := fun t ω i => Real.sqrt t * X ω i + Real.sqrt (1 - t) * Y ω i
  let PsiF : ℝ → ℝ := fun s => ∫ ω, g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (W s ω))) ∂μ
  let CP : (Fin p → ℝ) → Fin p → Fin p → ℝ := fun z j k =>
    PaperProofTasks.job_paper_a86aea8c92ff4120874a0fdca6db77c5.Statlib.Imported.coordPartial j
      (PaperProofTasks.job_paper_a86aea8c92ff4120874a0fdca6db77c5.Statlib.Imported.coordPartial k
        (PaperProofTasks.job_paper_a86aea8c92ff4120874a0fdca6db77c5.Statlib.Imported.compSmoothMax (p := p) g β)) z
  let MM : ℝ := Delta * (supNormR (deriv (deriv g)) / 2 + β * supNormR (deriv g))
  have hXm : Measurable X := hX.measurable
  have hYm : Measurable Y := hY.measurable
  have hXmeas : ∀ j : Fin p, Measurable (fun ω : Ω => X ω j) := fun j => measurable_pi_iff.mp hXm j
  have hYmeas : ∀ j : Fin p, Measurable (fun ω : Ω => Y ω j) := fun j => measurable_pi_iff.mp hYm j
  have hXint : ∀ j : Fin p, Integrable (fun ω : Ω => X ω j) μ := by
    intro j
    have hdom : Integrable (fun ω : Ω => 1 + X ω j * X ω j) μ :=
      (integrable_const (1 : ℝ)).add (hintX j j)
    refine Integrable.mono' hdom ((hXmeas j).aestronglyMeasurable) ?_
    filter_upwards with ω
    have habs : |X ω j| ≤ 1 + X ω j * X ω j := by
      have hsq : |X ω j| * |X ω j| = X ω j * X ω j := by
        rw [← abs_mul, abs_of_nonneg (mul_self_nonneg (X ω j))]
      nlinarith [abs_nonneg (X ω j), sq_nonneg (|X ω j| - 1 / 2)]
    simpa only [Real.norm_eq_abs] using habs
  have hYint : ∀ j : Fin p, Integrable (fun ω : Ω => Y ω j) μ := by
    intro j
    have hdom : Integrable (fun ω : Ω => 1 + Y ω j * Y ω j) μ :=
      (integrable_const (1 : ℝ)).add (hintY j j)
    refine Integrable.mono' hdom ((hYmeas j).aestronglyMeasurable) ?_
    filter_upwards with ω
    have habs : |Y ω j| ≤ 1 + Y ω j * Y ω j := by
      have hsq : |Y ω j| * |Y ω j| = Y ω j * Y ω j := by
        rw [← abs_mul, abs_of_nonneg (mul_self_nonneg (Y ω j))]
      nlinarith [abs_nonneg (Y ω j), sq_nonneg (|Y ω j| - 1 / 2)]
    simpa only [Real.norm_eq_abs] using habs
  have hDelta_nn : 0 ≤ Delta := by
    have h1 := hDelta ⟨0, hp⟩ ⟨0, hp⟩
    have h2 : (0 : ℝ) ≤ |SigmaX ⟨0, hp⟩ ⟨0, hp⟩ - SigmaY ⟨0, hp⟩ ⟨0, hp⟩| := abs_nonneg _
    linarith
  have hSb_nn : 0 ≤ supNormR (deriv (deriv g)) + 2 * β * supNormR (deriv g) := by
    have h := (statopia_math_node_3156732339_a370e2ae μ p hp (fun _ : Ω => fun _ : Fin p => (0 : ℝ)) measurable_const β hβ g hg hg1 hg2).1 (0 : Fin p → ℝ)
    have h' : ∑ j : Fin p, ∑ k : Fin p, |CP (0 : Fin p → ℝ) j k| ≤ supNormR (deriv (deriv g)) + 2 * β * supNormR (deriv g) := h
    have h0 : (0 : ℝ) ≤ ∑ j : Fin p, ∑ k : Fin p, |CP (0 : Fin p → ℝ) j k| :=
      Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => abs_nonneg _))
    linarith
  have hC_nn : 0 ≤ supNormR (deriv (deriv g)) / 2 + β * supNormR (deriv g) := by
    linarith [hSb_nn]
  have hM_nn : 0 ≤ MM := mul_nonneg hDelta_nn hC_nn
  have hg1' : ContDiff ℝ 1 g := by
    refine ContDiff.of_le hg ?_
    first
      | norm_num
      | simp
      | decide
      | exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2)
      | exact WithTop.coe_le_coe.mpr (by norm_num)
  have hcont : ContinuousOn PsiF (Set.Icc (0 : ℝ) 1) :=
    (statopia_math_node_1904015730_8e8aa481 μ p hp X Y hXm hYm hXint hYint β hβ g hg1' hg1).2.1
  have hintEnd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Integrable (fun ω : Ω => g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (W t ω)))) μ :=
    (statopia_math_node_1904015730_8e8aa481 μ p hp X Y hXm hYm hXint hYint β hβ g hg1' hg1).1
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt PsiF ((1 / 2 : ℝ) * ∑ j : Fin p, ∑ k : Fin p, (SigmaX j k - SigmaY j k) * ∫ ω, CP (W t ω) j k ∂μ) t := by
    intro t ht
    exact (statopia_math_node_2074902041_7cdeb16b μ p hp X Y hXm hYm SigmaX SigmaY hSigmaX hSigmaY SigmaXY hXY hintX hintY hintXY hmomX hmomY hmomXY β hβ g hg hg1 hg2 t ht).2
  have hbound : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      |(1 / 2 : ℝ) * ∑ j : Fin p, ∑ k : Fin p, (SigmaX j k - SigmaY j k) * ∫ ω, CP (W t ω) j k ∂μ| ≤ MM := by
    intro t ht
    have hZmeas : Measurable (W t) := by
      rw [measurable_pi_iff]
      intro i
      show Measurable (fun ω : Ω => Real.sqrt t * X ω i + Real.sqrt (1 - t) * Y ω i)
      exact ((hXmeas i).const_mul (Real.sqrt t)).add ((hYmeas i).const_mul (Real.sqrt (1 - t)))
    have hH := statopia_math_node_3156732339_a370e2ae μ p hp (W t) hZmeas β hβ g hg hg1 hg2
    have hsum : ∑ j : Fin p, ∑ k : Fin p, |∫ ω, CP (W t ω) j k ∂μ|
        ≤ supNormR (deriv (deriv g)) + 2 * β * supNormR (deriv g) := hH.2.2
    have h1 : |(1 / 2 : ℝ) * ∑ j : Fin p, ∑ k : Fin p, (SigmaX j k - SigmaY j k) * ∫ ω, CP (W t ω) j k ∂μ|
        ≤ (1 / 2 : ℝ) * ∑ j : Fin p, ∑ k : Fin p, Delta * |∫ ω, CP (W t ω) j k ∂μ| := by
      rw [abs_mul, show |(1 / 2 : ℝ)| = 1 / 2 from by norm_num]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      calc |∑ j : Fin p, ∑ k : Fin p, (SigmaX j k - SigmaY j k) * ∫ ω, CP (W t ω) j k ∂μ|
          ≤ ∑ j : Fin p, |∑ k : Fin p, (SigmaX j k - SigmaY j k) * ∫ ω, CP (W t ω) j k ∂μ| :=
              Finset.abs_sum_le_sum_abs (s := Finset.univ)
                (f := fun j : Fin p => ∑ k : Fin p, (SigmaX j k - SigmaY j k) * ∫ ω, CP (W t ω) j k ∂μ)
        _ ≤ ∑ j : Fin p, ∑ k : Fin p, |(SigmaX j k - SigmaY j k) * ∫ ω, CP (W t ω) j k ∂μ| :=
              Finset.sum_le_sum (fun j _ => Finset.abs_sum_le_sum_abs (s := Finset.univ)
                (f := fun k : Fin p => (SigmaX j k - SigmaY j k) * ∫ ω, CP (W t ω) j k ∂μ))
        _ = ∑ j : Fin p, ∑ k : Fin p, |SigmaX j k - SigmaY j k| * |∫ ω, CP (W t ω) j k ∂μ| := by
              simp only [abs_mul]
        _ ≤ ∑ j : Fin p, ∑ k : Fin p, Delta * |∫ ω, CP (W t ω) j k ∂μ| := by
              refine Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => ?_))
              exact mul_le_mul_of_nonneg_right (hDelta j k) (abs_nonneg _)
    have h2 : (∑ j : Fin p, ∑ k : Fin p, Delta * |∫ ω, CP (W t ω) j k ∂μ|)
        = Delta * ∑ j : Fin p, ∑ k : Fin p, |∫ ω, CP (W t ω) j k ∂μ| := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.mul_sum]
    have h3 : Delta * ∑ j : Fin p, ∑ k : Fin p, |∫ ω, CP (W t ω) j k ∂μ|
        ≤ Delta * (supNormR (deriv (deriv g)) + 2 * β * supNormR (deriv g)) :=
      mul_le_mul_of_nonneg_left hsum hDelta_nn
    calc |(1 / 2 : ℝ) * ∑ j : Fin p, ∑ k : Fin p, (SigmaX j k - SigmaY j k) * ∫ ω, CP (W t ω) j k ∂μ|
        ≤ (1 / 2 : ℝ) * ∑ j : Fin p, ∑ k : Fin p, Delta * |∫ ω, CP (W t ω) j k ∂μ| := h1
      _ = (1 / 2 : ℝ) * (Delta * ∑ j : Fin p, ∑ k : Fin p, |∫ ω, CP (W t ω) j k ∂μ|) := by rw [h2]
      _ ≤ (1 / 2 : ℝ) * (Delta * (supNormR (deriv (deriv g)) + 2 * β * supNormR (deriv g))) := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 1 / 2)
            exact h3
      _ = MM := by
            show (1 / 2 : ℝ) * (Delta * (supNormR (deriv (deriv g)) + 2 * β * supNormR (deriv g)))
              = Delta * (supNormR (deriv (deriv g)) / 2 + β * supNormR (deriv g))
            ring
  have hMvt : ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ y ∈ Set.Ioo (0 : ℝ) 1, |PsiF y - PsiF x| ≤ MM * |y - x| := by
    intro x hx y hy
    have hconv : Convex ℝ (Set.Ioo (0 : ℝ) 1) := convex_Ioo 0 1
    have hdiff : ∀ s ∈ Set.Ioo (0 : ℝ) 1, DifferentiableAt ℝ PsiF s := fun s hs => (hderiv s hs).differentiableAt
    have hbnd : ∀ s ∈ Set.Ioo (0 : ℝ) 1, ‖deriv PsiF s‖ ≤ MM := by
      intro s hs
      rw [(hderiv s hs).deriv]
      simpa only [Real.norm_eq_abs] using hbound s hs
    have key := hconv.norm_image_sub_le_of_norm_deriv_le (f := PsiF) (C := MM) hdiff hbnd hy hx
    simpa only [Real.norm_eq_abs, abs_sub_comm] using key
  have hW1 : ∀ ω : Ω, W 1 ω = X ω := by
    intro ω
    funext i
    show Real.sqrt 1 * X ω i + Real.sqrt (1 - 1) * Y ω i = X ω i
    simp [Real.sqrt_one, Real.sqrt_zero]
  have hW0 : ∀ ω : Ω, W 0 ω = Y ω := by
    intro ω
    funext i
    show Real.sqrt 0 * X ω i + Real.sqrt (1 - 0) * Y ω i = Y ω i
    simp [Real.sqrt_one, Real.sqrt_zero]
  have hPsi1 : PsiF 1 = ∫ ω, g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (X ω))) ∂μ := by
    show (∫ ω, g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (W 1 ω))) ∂μ) = _
    simp only [hW1]
  have hPsi0 : PsiF 0 = ∫ ω, g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (Y ω))) ∂μ := by
    show (∫ ω, g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (W 0 ω))) ∂μ) = _
    simp only [hW0]
  have hX1 : Integrable (fun ω : Ω => g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (X ω)))) μ := by
    have h := hintEnd 1 (by norm_num : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    simpa only [hW1] using h
  have hY1 : Integrable (fun ω : Ω => g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (Y ω)))) μ := by
    have h := hintEnd 0 (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    simpa only [hW0] using h
  have hendpoint : |(∫ ω, g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (X ω))) ∂μ) - (∫ ω, g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (Y ω))) ∂μ)| ≤ MM := by
    rw [← hPsi1, ← hPsi0]
    have hε : ∀ ε : ℝ, 0 < ε → |PsiF 1 - PsiF 0| ≤ MM + ε := by
      intro ε hε
      have hε3 : 0 < ε / 3 := by linarith
      obtain ⟨δ1, hδ1pos, hδ1⟩ :=
        Metric.continuousWithinAt_iff.mp (hcont 0 (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1)) (ε / 3) hε3
      obtain ⟨δ2, hδ2pos, hδ2⟩ :=
        Metric.continuousWithinAt_iff.mp (hcont 1 (by norm_num : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)) (ε / 3) hε3
      let a : ℝ := min (1 / 8) (δ1 / 2)
      have ha_def : a = min (1 / 8) (δ1 / 2) := rfl
      let b : ℝ := 1 - min (1 / 8) (δ2 / 2)
      have hb_def : b = 1 - min (1 / 8) (δ2 / 2) := rfl
      have hmin1_pos : 0 < min (1 / 8 : ℝ) (δ1 / 2) := lt_min (by norm_num) (by linarith)
      have hmin1_le : min (1 / 8 : ℝ) (δ1 / 2) ≤ 1 / 8 := min_le_left _ _
      have hmin1_lt : min (1 / 8 : ℝ) (δ1 / 2) < δ1 := by
        have h := min_le_right (1 / 8 : ℝ) (δ1 / 2)
        linarith
      have hmin2_pos : 0 < min (1 / 8 : ℝ) (δ2 / 2) := lt_min (by norm_num) (by linarith)
      have hmin2_le : min (1 / 8 : ℝ) (δ2 / 2) ≤ 1 / 8 := min_le_left _ _
      have hmin2_lt : min (1 / 8 : ℝ) (δ2 / 2) < δ2 := by
        have h := min_le_right (1 / 8 : ℝ) (δ2 / 2)
        linarith
      have ha_pos : 0 < a := by linarith [ha_def, hmin1_pos]
      have ha_lt : a < 1 := by linarith [ha_def, hmin1_le]
      have haδ : a < δ1 := by linarith [ha_def, hmin1_lt]
      have hb_pos : 0 < b := by linarith [hb_def, hmin2_le]
      have hb_lt : b < 1 := by linarith [hb_def, hmin2_pos]
      have hbδ : 1 - b < δ2 := by linarith [hb_def, hmin2_lt]
      have haIoo : a ∈ Set.Ioo (0 : ℝ) 1 := ⟨ha_pos, ha_lt⟩
      have hbIoo : b ∈ Set.Ioo (0 : ℝ) 1 := ⟨hb_pos, hb_lt⟩
      have haIcc : a ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt ha_pos, le_of_lt ha_lt⟩
      have hbIcc : b ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hb_pos, le_of_lt hb_lt⟩
      have hba0 : 0 < b - a := by linarith [ha_def, hb_def, hmin1_le, hmin2_le]
      have hba1 : |b - a| ≤ 1 := by
        rw [abs_of_pos hba0]
        linarith [hb_lt, ha_pos]
      have hc0 : |PsiF a - PsiF 0| < ε / 3 := by
        have hd : dist a 0 < δ1 := by
          rw [Real.dist_eq, sub_zero, abs_of_pos ha_pos]
          exact haδ
        simpa only [Real.dist_eq] using hδ1 haIcc hd
      have hc1 : |PsiF 1 - PsiF b| < ε / 3 := by
        have hd : dist b 1 < δ2 := by
          rw [Real.dist_eq, abs_of_neg (by linarith : b - 1 < 0),
            show -(b - 1) = 1 - b from by ring]
          exact hbδ
        have hh := hδ2 hbIcc hd
        rw [Real.dist_eq] at hh
        rwa [abs_sub_comm] at hh
      have hc2 : |PsiF b - PsiF a| ≤ MM := by
        have hm := hMvt a haIoo b hbIoo
        calc |PsiF b - PsiF a| ≤ MM * |b - a| := hm
          _ ≤ MM * 1 := mul_le_mul_of_nonneg_left hba1 hM_nn
          _ = MM := by ring
      have htri : |PsiF 1 - PsiF 0| ≤ |PsiF 1 - PsiF b| + |PsiF b - PsiF a| + |PsiF a - PsiF 0| := by
        have h1 := dist_triangle (PsiF 1) (PsiF b) (PsiF 0)
        have h2 := dist_triangle (PsiF b) (PsiF a) (PsiF 0)
        simp only [Real.dist_eq] at h1 h2
        linarith
      linarith
    by_contra hcon
    rw [not_le] at hcon
    have hpos : 0 < (|PsiF 1 - PsiF 0| - MM) / 2 := by linarith
    have hfin := hε _ hpos
    linarith
  simp only [expSmoothMaxDiff]
  rw [integral_sub hX1 hY1]
  exact hendpoint
  /- @proof-region region.target-node.session.a2a8a1ccb4ad81d0 end -/

end Statlib.Imported

