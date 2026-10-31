import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.Vocabulary
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.Base
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.ProvedNodes.Node_1363480033_de485796_5ea260ff
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.ProvedNodes.Node_3426360121_2b3d487b_26518c41
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.ProvedNodes.Node_45620975_1ba6532d_3adc54e6

namespace PaperProofTasks.job_paper_ea9c51e8f7d246ef967b6629540eeb01
open _root_.PaperProofTasks.job_paper_ea9c51e8f7d246ef967b6629540eeb01.Statlib.Imported
open MeasureTheory ProbabilityTheory

namespace Statlib.Imported

open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_3051679456_55e9e66b : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℕ) (hp : 0 < p) (X Y : Ω → Fin p → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXint : ∀ j : Fin p, Integrable (fun ω => X ω j) μ)
    (hYint : ∀ j : Fin p, Integrable (fun ω => Y ω j) μ)
    (β : ℝ) (hβ : 0 < β) (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
    (hg_bdd : BddAbove (Set.range fun z : ℝ => |deriv g z|)),
    ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt
        (fun s : ℝ => ∫ ω, g (Statlib.StatFoundation.Convergence.smoothMax β
            (WithLp.toLp 2 (fun j : Fin p => Real.sqrt s * X ω j + Real.sqrt (1 - s) * Y ω j))) ∂μ)
        ((1/2 : ℝ) * ∑ j : Fin p, ∫ ω,
            (fderiv ℝ (fun z : Fin p → ℝ =>
                g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z)))
              (fun j : Fin p => Real.sqrt t * X ω j + Real.sqrt (1 - t) * Y ω j))
            (Pi.single j (1 : ℝ)) *
            (t ^ (-(1/2) : ℝ) * X ω j - (1 - t) ^ (-(1/2) : ℝ) * Y ω j) ∂μ)
        t := by
  /- @proof-region region.target-node.session.782a91d39c9de1cd begin -/
  intro Ω _ μ _ p hp X Y hX hY hXint hYint β hβ g hg hg_bdd t ht
  obtain ⟨ht0, ht1⟩ := ht
  obtain ⟨M, hM⟩ := hg_bdd
  have hMle : ∀ z : ℝ, |deriv g z| ≤ M := fun z => hM ⟨z, rfl⟩
  obtain ⟨a, ha0, hat⟩ := exists_between ht0
  obtain ⟨b, htb, hb1⟩ := exists_between ht1
  set G : (Fin p → ℝ) → ℝ := fun z => g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z)) with hG
  set Z : ℝ → Ω → Fin p → ℝ := fun s ω j => Real.sqrt s * X ω j + Real.sqrt (1 - s) * Y ω j with hZ
  set F : ℝ → Ω → ℝ := fun s ω => G (Z s ω) with hF
  set F' : ℝ → Ω → ℝ := fun s ω => ∑ j : Fin p, (fderiv ℝ G (Z s ω)) (Pi.single j (1 : ℝ)) * ((1 / 2 : ℝ) * (s ^ (-(1 / 2) : ℝ) * X ω j - (1 - s) ^ (-(1 / 2) : ℝ) * Y ω j)) with hF'
  have hkey : ∀ (z : Fin p → ℝ) (j : Fin p), ‖(fderiv ℝ G z) (Pi.single j (1 : ℝ))‖ ≤ M := by
    obtain ⟨-, hformula⟩ := statopia_math_node_3426360121_2b3d487b hp hβ hg
    have hM0 : 0 ≤ M := le_trans (abs_nonneg (deriv g 0)) (hMle 0)
    intro z j
    have hweight := Statlib.StatFoundation.Convergence.softmax_weights_sum_nonneg (β := β) hp (WithLp.toLp 2 z)
    have h1 : (fderiv ℝ G z) (Pi.single j (1 : ℝ))
        = deriv g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z))
          * Statlib.StatFoundation.Convergence.softmaxWeight β (WithLp.toLp 2 z) j := by
      rw [hG]
      exact hformula z j
    have h2 : Statlib.StatFoundation.Convergence.softmaxWeight β (WithLp.toLp 2 z) j ≤ 1 := by
      have hsingle : Statlib.StatFoundation.Convergence.softmaxWeight β (WithLp.toLp 2 z) j
          ≤ ∑ i : Fin p, Statlib.StatFoundation.Convergence.softmaxWeight β (WithLp.toLp 2 z) i :=
        Finset.single_le_sum (fun i _ => hweight.1 i) (Finset.mem_univ j)
      simpa only [hweight.2] using hsingle
    rw [h1, Real.norm_eq_abs, abs_mul]
    have h3 : |deriv g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z))| ≤ M := hMle _
    have h4 : |Statlib.StatFoundation.Convergence.softmaxWeight β (WithLp.toLp 2 z) j| ≤ 1 := by
      rw [abs_of_nonneg (hweight.1 j)]
      exact h2
    calc |deriv g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z))|
            * |Statlib.StatFoundation.Convergence.softmaxWeight β (WithLp.toLp 2 z) j|
        ≤ M * 1 := mul_le_mul h3 h4 (abs_nonneg _) hM0
      _ = M := mul_one M
  have hXabs : ∀ j : Fin p, Integrable (fun ω => |X ω j|) μ := fun j => by
    simpa only [Real.norm_eq_abs] using (hXint j).norm
  have hYabs : ∀ j : Fin p, Integrable (fun ω => |Y ω j|) μ := fun j => by
    simpa only [Real.norm_eq_abs] using (hYint j).norm
  have hXY_int : Integrable (fun ω => ∑ j : Fin p, (|X ω j| + |Y ω j|)) μ := by
    have h2 : ∀ j ∈ (Finset.univ : Finset (Fin p)), Integrable (fun ω => |X ω j| + |Y ω j|) μ :=
      fun j _ => (hXabs j).add (hYabs j)
    exact integrable_finset_sum (Finset.univ) (f := fun (j : Fin p) (ω : Ω) => |X ω j| + |Y ω j|) h2
  have hZm : ∀ s : ℝ, Measurable (fun ω => Z s ω) := by
    intro s
    refine measurable_pi_iff.mpr (fun j => ?_)
    simp only [hZ]
    exact ((measurable_pi_iff.mp hX j).const_mul (Real.sqrt s)).add ((measurable_pi_iff.mp hY j).const_mul (Real.sqrt (1 - s)))
  have hsmMeas : Measurable (Statlib.StatFoundation.Convergence.smoothMax β) :=
    (Statlib.StatFoundation.Convergence.smoothMax_def_measurable_continuous hp hβ).2
  have hFmeas : ∀ s : ℝ, Measurable (fun ω => F s ω) := by
    intro s
    simp only [hF, hG]
    exact hg.continuous.measurable.comp (hsmMeas.comp ((WithLp.measurable_toLp 2 (Fin p → ℝ)).comp (hZm s)))
  have hbound : ∀ᵐ ω ∂μ, ∀ s ∈ Set.Ioo a b, ‖F' s ω‖ ≤ (1 / 2 * M * (1 / Real.sqrt a + 1 / Real.sqrt (1 - b))) * ∑ j : Fin p, (|X ω j| + |Y ω j|) := by
    have hrpow : ∀ {x : ℝ}, 0 < x → x ^ (-(1 / 2) : ℝ) = 1 / Real.sqrt x := by
      intro x hx
      rw [Real.rpow_neg (le_of_lt hx), ← Real.sqrt_eq_rpow, inv_eq_one_div]
    have hsa : 0 < Real.sqrt a := by
      simpa only [Real.sqrt_eq_rpow] using Real.rpow_pos_of_pos ha0 (1 / 2)
    have hsb : 0 < Real.sqrt (1 - b) := by
      simpa only [Real.sqrt_eq_rpow] using Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < 1 - b) (1 / 2)
    have hMnn : 0 ≤ M := le_trans (abs_nonneg (deriv g 0)) (hMle 0)
    refine Filter.Eventually.of_forall (fun ω => ?_)
    intro s hs
    have hs0 : 0 < s := lt_trans ha0 hs.1
    have hspos : 0 < 1 - s := by linarith [hs.2, hb1]
    have hsle : s ^ (-(1 / 2) : ℝ) ≤ 1 / Real.sqrt a := by
      rw [hrpow hs0]
      exact one_div_le_one_div_of_le hsa (Real.sqrt_le_sqrt (le_of_lt hs.1))
    have hsle2 : (1 - s) ^ (-(1 / 2) : ℝ) ≤ 1 / Real.sqrt (1 - b) := by
      rw [hrpow hspos]
      exact one_div_le_one_div_of_le hsb (Real.sqrt_le_sqrt (by linarith [hs.2] : 1 - b ≤ 1 - s))
    have hterm : ∀ j : Fin p, ‖(fderiv ℝ G (Z s ω)) (Pi.single j (1 : ℝ))
        * ((1 / 2 : ℝ) * (s ^ (-(1 / 2) : ℝ) * X ω j - (1 - s) ^ (-(1 / 2) : ℝ) * Y ω j))‖
        ≤ (1 / 2 * M * (1 / Real.sqrt a + 1 / Real.sqrt (1 - b))) * (|X ω j| + |Y ω j|) := by
      intro j
      have hLj : ‖(fderiv ℝ G (Z s ω)) (Pi.single j (1 : ℝ))‖ ≤ M := hkey _ j
      have hspos' : 0 < s ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hs0 _
      have hspos2 : 0 < (1 - s) ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hspos _
      have hinner : ‖(1 / 2 : ℝ) * (s ^ (-(1 / 2) : ℝ) * X ω j - (1 - s) ^ (-(1 / 2) : ℝ) * Y ω j)‖
          ≤ (1 / 2) * ((1 / Real.sqrt a) * |X ω j| + (1 / Real.sqrt (1 - b)) * |Y ω j|) := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        have h1 : |s ^ (-(1 / 2) : ℝ) * X ω j - (1 - s) ^ (-(1 / 2) : ℝ) * Y ω j|
            ≤ |s ^ (-(1 / 2) : ℝ) * X ω j| + |(1 - s) ^ (-(1 / 2) : ℝ) * Y ω j| := by
          have hab := abs_add_le (s ^ (-(1 / 2) : ℝ) * X ω j) (-((1 - s) ^ (-(1 / 2) : ℝ) * Y ω j))
          simpa only [sub_eq_add_neg, abs_neg] using hab
        have h2 : |s ^ (-(1 / 2) : ℝ) * X ω j| = s ^ (-(1 / 2) : ℝ) * |X ω j| := by
          rw [abs_mul, abs_of_pos hspos']
        have h3 : |(1 - s) ^ (-(1 / 2) : ℝ) * Y ω j| = (1 - s) ^ (-(1 / 2) : ℝ) * |Y ω j| := by
          rw [abs_mul, abs_of_pos hspos2]
        have h4 : s ^ (-(1 / 2) : ℝ) * |X ω j| ≤ (1 / Real.sqrt a) * |X ω j| :=
          mul_le_mul_of_nonneg_right hsle (abs_nonneg _)
        have h5 : (1 - s) ^ (-(1 / 2) : ℝ) * |Y ω j| ≤ (1 / Real.sqrt (1 - b)) * |Y ω j| :=
          mul_le_mul_of_nonneg_right hsle2 (abs_nonneg _)
        calc (1 / 2) * |s ^ (-(1 / 2) : ℝ) * X ω j - (1 - s) ^ (-(1 / 2) : ℝ) * Y ω j|
            ≤ (1 / 2) * (|s ^ (-(1 / 2) : ℝ) * X ω j| + |(1 - s) ^ (-(1 / 2) : ℝ) * Y ω j|) :=
              mul_le_mul_of_nonneg_left h1 (by norm_num)
          _ = (1 / 2) * (s ^ (-(1 / 2) : ℝ) * |X ω j| + (1 - s) ^ (-(1 / 2) : ℝ) * |Y ω j|) := by
              rw [h2, h3]
          _ ≤ (1 / 2) * ((1 / Real.sqrt a) * |X ω j| + (1 / Real.sqrt (1 - b)) * |Y ω j|) :=
              mul_le_mul_of_nonneg_left (add_le_add h4 h5) (by norm_num)
      rw [norm_mul]
      have hXj : 0 ≤ |X ω j| := abs_nonneg _
      have hYj : 0 ≤ |Y ω j| := abs_nonneg _
      have hA : 0 ≤ 1 / Real.sqrt a := le_of_lt (one_div_pos.mpr hsa)
      have hB : 0 ≤ 1 / Real.sqrt (1 - b) := le_of_lt (one_div_pos.mpr hsb)
      have hcombo : 1 / Real.sqrt a * |X ω j| + 1 / Real.sqrt (1 - b) * |Y ω j|
          ≤ (1 / Real.sqrt a + 1 / Real.sqrt (1 - b)) * (|X ω j| + |Y ω j|) := by
        nlinarith [mul_nonneg hA hYj, mul_nonneg hB hXj]
      refine le_trans (mul_le_mul hLj hinner (norm_nonneg _) hMnn) ?_
      have hhalf : (1 / 2) * (1 / Real.sqrt a * |X ω j| + 1 / Real.sqrt (1 - b) * |Y ω j|)
          ≤ (1 / 2) * ((1 / Real.sqrt a + 1 / Real.sqrt (1 - b)) * (|X ω j| + |Y ω j|)) :=
        mul_le_mul_of_nonneg_left hcombo (by norm_num)
      calc M * ((1 / 2) * (1 / Real.sqrt a * |X ω j| + 1 / Real.sqrt (1 - b) * |Y ω j|))
          ≤ M * ((1 / 2) * ((1 / Real.sqrt a + 1 / Real.sqrt (1 - b)) * (|X ω j| + |Y ω j|))) :=
            mul_le_mul_of_nonneg_left hhalf hMnn
        _ = (1 / 2 * M * (1 / Real.sqrt a + 1 / Real.sqrt (1 - b))) * (|X ω j| + |Y ω j|) := by ring
    rw [hF']
    refine le_trans (norm_sum_le Finset.univ (fun j : Fin p => (fderiv ℝ G (Z s ω)) (Pi.single j (1 : ℝ))
      * ((1 / 2 : ℝ) * (s ^ (-(1 / 2) : ℝ) * X ω j - (1 - s) ^ (-(1 / 2) : ℝ) * Y ω j)))) ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => hterm j)
  have hbound_int : Integrable (fun ω => (1 / 2 * M * (1 / Real.sqrt a + 1 / Real.sqrt (1 - b))) * ∑ j : Fin p, (|X ω j| + |Y ω j|)) μ := by
    simpa only [smul_eq_mul] using hXY_int.const_mul (1 / 2 * M * (1 / Real.sqrt a + 1 / Real.sqrt (1 - b)))
  have hderiv : ∀ᵐ ω ∂μ, ∀ s ∈ Set.Ioo a b, HasDerivAt (fun s => F s ω) (F' s ω) s := by
    refine Filter.Eventually.of_forall (fun ω => ?_)
    intro s hs
    have hs' : s ∈ Set.Ioo (0 : ℝ) 1 := ⟨ha0.trans hs.1, lt_trans hs.2 hb1⟩
    simpa only [hF, hG, hZ] using
      statopia_math_node_1363480033_de485796 hp hβ hg (X ω) (Y ω) hs'
  have hmeasF : ∀ᶠ s in nhds t, AEStronglyMeasurable (F s) μ :=
    Filter.Eventually.of_forall (fun s => (hFmeas s).aestronglyMeasurable)
  have hintF : Integrable (F t) μ := by
    obtain ⟨C, hC0, hC⟩ := statopia_math_node_45620975_1ba6532d hp hβ hg M hMle
    have hst : Real.sqrt t ≤ 1 := by
      simpa using Real.sqrt_le_sqrt (le_of_lt ht1)
    have hs1t : Real.sqrt (1 - t) ≤ 1 := by
      simpa using Real.sqrt_le_sqrt (by linarith : 1 - t ≤ 1)
    have hbig : Integrable (fun ω => C * (1 + ∑ j : Fin p, (|X ω j| + |Y ω j|))) μ := by
      have h1 : Integrable (fun ω => 1 + ∑ j : Fin p, (|X ω j| + |Y ω j|)) μ :=
        (integrable_const (1 : ℝ)).add hXY_int
      simpa only [smul_eq_mul] using h1.const_mul C
    refine Integrable.mono' hbig (hFmeas t).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    have hZle : ∀ j : Fin p, |Z t ω j| ≤ |X ω j| + |Y ω j| := by
      intro j
      have h1 : Z t ω j = Real.sqrt t * X ω j + Real.sqrt (1 - t) * Y ω j := by
        simp only [hZ]
      rw [h1]
      have h2 : |Real.sqrt t * X ω j| = Real.sqrt t * |X ω j| := by
        rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      have h3 : |Real.sqrt (1 - t) * Y ω j| = Real.sqrt (1 - t) * |Y ω j| := by
        rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      have h4 : |Real.sqrt t * X ω j + Real.sqrt (1 - t) * Y ω j|
          ≤ |Real.sqrt t * X ω j| + |Real.sqrt (1 - t) * Y ω j| := abs_add_le _ _
      rw [h2, h3] at h4
      have h5 : Real.sqrt t * |X ω j| ≤ 1 * |X ω j| :=
        mul_le_mul_of_nonneg_right hst (abs_nonneg _)
      have h6 : Real.sqrt (1 - t) * |Y ω j| ≤ 1 * |Y ω j| :=
        mul_le_mul_of_nonneg_right hs1t (abs_nonneg _)
      linarith
    have hb := hC (Z t ω)
    have hsum_le : ∑ j : Fin p, |Z t ω j| ≤ ∑ j : Fin p, (|X ω j| + |Y ω j|) :=
      Finset.sum_le_sum (fun j _ => hZle j)
    have hb2 : C * (1 + ∑ j : Fin p, |Z t ω j|) ≤ C * (1 + ∑ j : Fin p, (|X ω j| + |Y ω j|)) := by
      refine mul_le_mul_of_nonneg_left ?_ hC0
      linarith
    have hb3 : ‖F t ω‖ = |g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (Z t ω)))| := by
      simp only [hF, hG, Real.norm_eq_abs]
    rw [hb3]
    exact le_trans hb hb2
  obtain ⟨hcd, -⟩ := statopia_math_node_3426360121_2b3d487b hp hβ hg
  have hcdG : ContDiff ℝ 1 G := by
    rw [hG]
    exact hcd
  have hcont : ∀ j : Fin p, Continuous (fun z : Fin p → ℝ => (fderiv ℝ G z) (Pi.single j (1 : ℝ))) := by
    intro j
    exact ((hcdG.contDiff_fderiv_apply (m := 0) (by decide)).continuous).comp
      (continuous_id.prodMk continuous_const)
  have hLmeas : ∀ (s : ℝ) (j : Fin p), Measurable (fun ω => (fderiv ℝ G (Z s ω)) (Pi.single j (1 : ℝ))) := by
    intro s j
    exact (hcont j).measurable.comp (hZm s)
  have hDmeas : ∀ (s : ℝ) (j : Fin p),
      Measurable (fun ω => s ^ (-(1 / 2) : ℝ) * X ω j - (1 - s) ^ (-(1 / 2) : ℝ) * Y ω j) := by
    intro s j
    exact ((measurable_pi_iff.mp hX j).const_mul _).sub ((measurable_pi_iff.mp hY j).const_mul _)
  have hmeasF' : AEStronglyMeasurable (F' t) μ := by
    have hsummand : ∀ j : Fin p, Measurable (fun ω => (fderiv ℝ G (Z t ω)) (Pi.single j (1 : ℝ))
        * ((1 / 2 : ℝ) * (t ^ (-(1 / 2) : ℝ) * X ω j - (1 - t) ^ (-(1 / 2) : ℝ) * Y ω j))) := by
      intro j
      exact (hLmeas t j).mul ((hDmeas t j).const_mul _)
    have hm : Measurable (fun ω => F' t ω) := by
      simp only [hF']
      exact Finset.measurable_sum (Finset.univ) (fun j _ => hsummand j)
    exact hm.aestronglyMeasurable
  obtain ⟨-, hmain⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (bound := fun ω => (1 / 2 * M * (1 / Real.sqrt a + 1 / Real.sqrt (1 - b))) * ∑ j : Fin p, (|X ω j| + |Y ω j|)) (F := F) (x₀ := t) (s := Set.Ioo a b) (F' := F') (isOpen_Ioo.mem_nhds ⟨hat, htb⟩) hmeasF hintF hmeasF' hbound hbound_int hderiv
  have hsummand_int : ∀ j : Fin p, Integrable (fun ω => (fderiv ℝ G (Z t ω)) (Pi.single j (1 : ℝ))
      * ((1 / 2 : ℝ) * (t ^ (-(1 / 2) : ℝ) * X ω j - (1 - t) ^ (-(1 / 2) : ℝ) * Y ω j))) μ := by
    intro j
    have hMnn : 0 ≤ M := le_trans (abs_nonneg (deriv g 0)) (hMle 0)
    have hXj : Integrable (fun ω => t ^ (-(1 / 2) : ℝ) * |X ω j|) μ := (hXabs j).const_mul _
    have hYj : Integrable (fun ω => (1 - t) ^ (-(1 / 2) : ℝ) * |Y ω j|) μ := (hYabs j).const_mul _
    have hcomp : Integrable (fun ω =>
        1 / 2 * M * (t ^ (-(1 / 2) : ℝ) * |X ω j| + (1 - t) ^ (-(1 / 2) : ℝ) * |Y ω j|)) μ := by
      simpa only [smul_eq_mul] using (hXj.add hYj).const_mul (1 / 2 * M)
    refine Integrable.mono' hcomp ((hLmeas t j).mul ((hDmeas t j).const_mul _)).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    have hLj : |(fderiv ℝ G (Z t ω)) (Pi.single j (1 : ℝ))| ≤ M := by
      simpa only [Real.norm_eq_abs] using hkey (Z t ω) j
    have hDle : |t ^ (-(1 / 2) : ℝ) * X ω j - (1 - t) ^ (-(1 / 2) : ℝ) * Y ω j|
        ≤ t ^ (-(1 / 2) : ℝ) * |X ω j| + (1 - t) ^ (-(1 / 2) : ℝ) * |Y ω j| := by
      have h1 : |t ^ (-(1 / 2) : ℝ) * X ω j - (1 - t) ^ (-(1 / 2) : ℝ) * Y ω j|
          ≤ |t ^ (-(1 / 2) : ℝ) * X ω j| + |(1 - t) ^ (-(1 / 2) : ℝ) * Y ω j| := by
        have hab := abs_add_le (t ^ (-(1 / 2) : ℝ) * X ω j) (-((1 - t) ^ (-(1 / 2) : ℝ) * Y ω j))
        simpa only [sub_eq_add_neg, abs_neg] using hab
      have h2 : |t ^ (-(1 / 2) : ℝ) * X ω j| = t ^ (-(1 / 2) : ℝ) * |X ω j| := by
        rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (le_of_lt ht0) _)]
      have h3 : |(1 - t) ^ (-(1 / 2) : ℝ) * Y ω j| = (1 - t) ^ (-(1 / 2) : ℝ) * |Y ω j| := by
        rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 - t) _)]
      rw [h2, h3] at h1
      exact h1
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    calc |(fderiv ℝ G (Z t ω)) (Pi.single j (1 : ℝ))|
            * ((1 / 2) * |t ^ (-(1 / 2) : ℝ) * X ω j - (1 - t) ^ (-(1 / 2) : ℝ) * Y ω j|)
        ≤ M * ((1 / 2) * (t ^ (-(1 / 2) : ℝ) * |X ω j| + (1 - t) ^ (-(1 / 2) : ℝ) * |Y ω j|)) := by
          have hnn : 0 ≤ (1 / 2 : ℝ) := by norm_num
          exact mul_le_mul hLj (mul_le_mul_of_nonneg_left hDle hnn)
            (mul_nonneg hnn (abs_nonneg _)) hMnn
      _ = 1 / 2 * M * (t ^ (-(1 / 2) : ℝ) * |X ω j| + (1 - t) ^ (-(1 / 2) : ℝ) * |Y ω j|) := by ring
  have hint : ∫ ω, F' t ω ∂μ = (1 / 2 : ℝ) * ∑ j : Fin p, ∫ ω, (fderiv ℝ G (Z t ω)) (Pi.single j (1 : ℝ)) * (t ^ (-(1 / 2) : ℝ) * X ω j - (1 - t) ^ (-(1 / 2) : ℝ) * Y ω j) ∂μ := by
    rw [hF', integral_finset_sum Finset.univ (fun j _ => hsummand_int j), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hcongr : ∫ ω, (fderiv ℝ G (Z t ω)) (Pi.single j (1 : ℝ))
          * ((1 / 2 : ℝ) * (t ^ (-(1 / 2) : ℝ) * X ω j - (1 - t) ^ (-(1 / 2) : ℝ) * Y ω j)) ∂μ
        = ∫ ω, (1 / 2 : ℝ) * ((fderiv ℝ G (Z t ω)) (Pi.single j (1 : ℝ))
          * (t ^ (-(1 / 2) : ℝ) * X ω j - (1 - t) ^ (-(1 / 2) : ℝ) * Y ω j)) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall (fun ω => by ring))
    rw [hcongr, integral_const_mul]
  simpa only [hint, hF, hG, hZ] using hmain
  /- @proof-region region.target-node.session.782a91d39c9de1cd end -/

end Statlib.Imported

