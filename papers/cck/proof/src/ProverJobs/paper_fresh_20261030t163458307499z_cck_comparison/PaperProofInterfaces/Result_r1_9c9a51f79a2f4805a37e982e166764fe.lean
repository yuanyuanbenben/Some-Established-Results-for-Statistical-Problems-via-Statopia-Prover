import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.Vocabulary
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.ProvedNodes
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.Base

namespace PaperProofTasks.job_paper_de3065fb922748188f3a0354eba90ed9

namespace Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

theorem paper_de3065fb922748188f3a0354eba90ed9
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℕ) (hp : 1 ≤ p)
    (X : Ω → Fin p → ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (hGauss : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ X Sigma)
    (hL2 : ∀ j : Fin p, MemLp (fun ω => X ω j) 2 μ)

    (hpos : ∀ j : Fin p, 0 < ∫ ω, (X ω j) ^ 2 ∂μ)
    (hInt : Integrable (fun ω => ⨆ j : Fin p, X ω j / coordStdDev μ X j) μ) :
    ((sigmaUnder μ X = sigmaOver μ X →
        ∀ ε : ℝ, 0 < ε →
          levyConcentration μ (coordMax X) ε ≤
            4 * ε * (standardizedMaxMean μ X + 1) / sigmaUnder μ X) ∧
      (sigmaUnder μ X < sigmaOver μ X →
        ∃ C : ℝ → ℝ → ℝ,
          (∀ s t : ℝ, 0 < s → s ≤ t → 0 < C s t) ∧
          ∀ ε : ℝ, 0 < ε →
            levyConcentration μ (coordMax X) ε ≤
              C (sigmaUnder μ X) (sigmaOver μ X) * ε *
                (standardizedMaxMean μ X +
                  Real.sqrt (max 1 (Real.log (sigmaUnder μ X / ε))))))
:= by
  /- @proof-region region.root.b332bd30ec5e begin -/
  haveI : Nonempty (Fin p) := ⟨⟨0, by omega⟩⟩
  have hσpos : ∀ j : Fin p, 0 < coordStdDev μ X j := fun j => Real.sqrt_pos.2 (hpos j)
  obtain ⟨j₀, hj₀⟩ := exists_eq_ciInf_of_finite (f := fun j : Fin p => coordStdDev μ X j)
  obtain ⟨j₁, hj₁⟩ := exists_eq_ciSup_of_finite (f := fun j : Fin p => coordStdDev μ X j)
  have hσUpos : 0 < sigmaUnder μ X := by
    have h : 0 < ⨅ j : Fin p, coordStdDev μ X j := by rw [← hj₀]; exact hσpos j₀
    simpa only [sigmaUnder] using h
  have hσUle : sigmaUnder μ X ≤ sigmaOver μ X := by
    have hbdd : BddAbove (Set.range fun j : Fin p => coordStdDev μ X j) :=
      Finite.bddAbove_range _
    have h : coordStdDev μ X j₀ ≤ ⨆ j : Fin p, coordStdDev μ X j := le_ciSup hbdd j₀
    calc sigmaUnder μ X = coordStdDev μ X j₀ := hj₀.symm
      _ ≤ ⨆ j : Fin p, coordStdDev μ X j := h
      _ = sigmaOver μ X := rfl
  have hσOpos : 0 < sigmaOver μ X := lt_of_lt_of_le hσUpos hσUle
  have ha : 0 ≤ standardizedMaxMean μ X := by
    have hsum : (fun ω => ∑ j, (Pi.single j₀ (1 : ℝ) : Fin p → ℝ) j * X ω j) =
        fun ω => X ω j₀ := by
      funext ω
      rw [Finset.sum_eq_single j₀]
      · rw [Pi.single_eq_same, one_mul]
      · intro b _ hb
        rw [Pi.single_eq_of_ne hb, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ j₀) h
    have hmean : ∫ ω, X ω j₀ ∂μ = 0 := by
      have hA : ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)).PosSemidef :=
        hGauss.posSemidef_symmetrizedCovariance hp
      have hc :=
        Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector_isCenteredGaussianVector
          (by omega : 0 < p) ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) hA
      have hYm := hc.measurable
      have hev : Measurable (fun v : Fin p → ℝ => v j₀) := by measurability
      have hsm : StronglyMeasurable (fun v : Fin p → ℝ => v j₀) := hev.stronglyMeasurable
      have hmap := hGauss.map_eq_canonicalGaussianVector hp
      haveI : IsProbabilityMeasure
          (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi p) := by
        have h1 : IsProbabilityMeasure (Measure.map X μ) :=
          Measure.isProbabilityMeasure_map hGauss.measurable.aemeasurable
        rw [hmap] at h1
        exact (Measure.isProbabilityMeasure_map_iff hYm.aemeasurable).mp h1
      have hsum2 : (fun z => ∑ j, (Pi.single j₀ (1 : ℝ) : Fin p → ℝ) j *
          Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector
            ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) z j) =
          fun z => Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector
            ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) z j₀ := by
        funext z
        rw [Finset.sum_eq_single j₀]
        · rw [Pi.single_eq_same, one_mul]
        · intro b _ hb
          rw [Pi.single_eq_of_ne hb, zero_mul]
        · intro h
          exact absurd (Finset.mem_univ j₀) h
      have hlaw :=
        Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.map_linearCombination
          (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi p)
          (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector
            ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)))
          ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) hc hA (Pi.single j₀ (1 : ℝ) : Fin p → ℝ)
      rw [hsum2] at hlaw
      have e1 : ∫ v, v j₀ ∂(Measure.map X μ) = ∫ ω, X ω j₀ ∂μ :=
        integral_map_of_stronglyMeasurable hGauss.measurable hsm
      have e2 : ∫ v, v j₀ ∂(Measure.map
            (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector
              ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)))
            (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi p)) =
          ∫ z, Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector
              ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) z j₀
            ∂(Statlib.StatFoundation.RandomVariable.Gaussian.standardPi p) :=
        integral_map_of_stronglyMeasurable hYm hsm
      have e4 : ∫ y, y ∂(Measure.map
            (fun z => Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector
              ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) z j₀)
            (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi p)) =
          ∫ z, Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector
              ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) z j₀
            ∂(Statlib.StatFoundation.RandomVariable.Gaussian.standardPi p) :=
        integral_map_of_stronglyMeasurable (hev.comp hYm) stronglyMeasurable_id
      rw [hlaw, integral_id_gaussianReal] at e4
      rw [← e1, hmap, e2, ← e4]
    have hle : ∀ ω, X ω j₀ / coordStdDev μ X j₀ ≤ ⨆ j : Fin p, X ω j / coordStdDev μ X j :=
      fun ω => le_ciSup (Finite.bddAbove_range (fun j : Fin p => X ω j / coordStdDev μ X j)) j₀
    have hint1 : Integrable (fun ω => X ω j₀ / coordStdDev μ X j₀) μ :=
      (MeasureTheory.MemLp.integrable (by norm_num) (hL2 j₀)).div_const _
    have hmono : ∫ ω, X ω j₀ / coordStdDev μ X j₀ ∂μ ≤
        ∫ ω, ⨆ j : Fin p, X ω j / coordStdDev μ X j ∂μ := integral_mono hint1 hInt hle
    have hzero : ∫ ω, X ω j₀ / coordStdDev μ X j₀ ∂μ = 0 := by
      rw [MeasureTheory.integral_div, hmean, zero_div]
    rw [hzero] at hmono
    simpa only [standardizedMaxMean] using hmono
  constructor
  · intro hEq ε hε
    have hδ0 : 1 / sigmaUnder μ X - 1 / sigmaOver μ X = 0 := by rw [hEq]; ring
    have htw : 0 ≤ 4 * ε * (standardizedMaxMean μ X + 1) / sigmaUnder μ X :=
      div_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 4 * ε)
        (by linarith : (0:ℝ) ≤ standardizedMaxMean μ X + 1)) hσUpos.le
    have hkey : ∀ x : ℝ,
        (μ {ω | |coordMax X ω - x| ≤ ε}).toReal ≤
          4 * ε * (standardizedMaxMean μ X + 1) / sigmaUnder μ X := by
      intro x
      have hb := statopia_math_node_966165858_9b26162f μ p hp X Sigma hGauss hL2 hpos hInt x ε hε
      have harg : 4 * ε / sigmaUnder μ X *
            ((1 / sigmaUnder μ X - 1 / sigmaOver μ X) * |x| + standardizedMaxMean μ X + 1) =
          4 * ε * (standardizedMaxMean μ X + 1) / sigmaUnder μ X := by
        rw [hδ0]; ring
      rw [harg] at hb
      exact ENNReal.toReal_le_of_le_ofReal htw hb
    exact ciSup_le hkey
  · intro hLt
    refine ⟨fun s t => (4 * (t / s + (t / s - 1) * Real.sqrt 2 + (2 - s / t)) + 1) / s, ?_, ?_⟩
    · intro s t hs hst
      have hn := statopia_math_node_654656712_8367084e s t hs hst
      dsimp only at hn
      exact hn.1.1
    · intro ε hε
      set R : ℝ := Real.sqrt (max 1 (Real.log (sigmaUnder μ X / ε))) with hR
      change levyConcentration μ (coordMax X) ε ≤
        (4 * (sigmaOver μ X / sigmaUnder μ X + (sigmaOver μ X / sigmaUnder μ X - 1) * Real.sqrt 2 +
          (2 - sigmaUnder μ X / sigmaOver μ X)) + 1) / sigmaUnder μ X * ε *
            (standardizedMaxMean μ X + R)
      set Cv : ℝ := (4 * (sigmaOver μ X / sigmaUnder μ X + (sigmaOver μ X / sigmaUnder μ X - 1) * Real.sqrt 2 +
          (2 - sigmaUnder μ X / sigmaOver μ X)) + 1) / sigmaUnder μ X with hCv
      have hnode := statopia_math_node_654656712_8367084e (sigmaUnder μ X) (sigmaOver μ X) hσUpos hσUle
      dsimp only at hnode
      obtain ⟨hCpos, hCs, _, hCle⟩ := hnode.1
      have hCposCv : 0 < Cv := by rw [hCv]; exact hCpos
      have hCsCv : Cv * sigmaUnder μ X = 4 * (sigmaOver μ X / sigmaUnder μ X +
          (sigmaOver μ X / sigmaUnder μ X - 1) * Real.sqrt 2 + (2 - sigmaUnder μ X / sigmaOver μ X)) + 1 := by
        rw [hCv]; exact hCs
      have hCleCv : 1 / sigmaUnder μ X ≤ Cv := by rw [hCv]; exact hCle
      have hC0nonneg : 0 ≤ sigmaOver μ X / sigmaUnder μ X +
          (sigmaOver μ X / sigmaUnder μ X - 1) * Real.sqrt 2 + (2 - sigmaUnder μ X / sigmaOver μ X) := by
        have h1 : (1:ℝ) ≤ sigmaOver μ X / sigmaUnder μ X := (one_le_div hσUpos).mpr hσUle
        have h4 : sigmaUnder μ X / sigmaOver μ X ≤ 1 := (div_le_one hσOpos).mpr hσUle
        have h2 : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
        have h3 : (0:ℝ) ≤ sigmaOver μ X / sigmaUnder μ X - 1 := by linarith
        nlinarith [mul_nonneg h3 h2]
      have h4C0 : 4 * (sigmaOver μ X / sigmaUnder μ X + (sigmaOver μ X / sigmaUnder μ X - 1) * Real.sqrt 2 +
          (2 - sigmaUnder μ X / sigmaOver μ X)) / sigmaUnder μ X ≤ Cv := by
        rw [div_le_iff₀ hσUpos]
        rw [hCsCv]
        linarith
      have hkey : ∀ x : ℝ,
          (μ {ω | |coordMax X ω - x| ≤ ε}).toReal ≤ Cv * ε * (standardizedMaxMean μ X + R) := by
        intro x
        by_cases hcase : ε ≤ sigmaUnder μ X
        · have hL0 : 0 ≤ Real.log (sigmaUnder μ X / ε) :=
            Real.log_nonneg ((one_le_div hε).mpr hcase)
          have hnode2 :=
            hnode.2 (standardizedMaxMean μ X) (Real.log (sigmaUnder μ X / ε)) ε ha hL0 hε hcase
          obtain ⟨hR1', _, hδ0, hmid⟩ := hnode2
          rw [← hR] at hmid
          have hR1 : (1:ℝ) ≤ R := by rw [hR]; exact hR1'
          have haR : 0 ≤ standardizedMaxMean μ X + R := by linarith
          have hδnonneg : 0 ≤ 1 / sigmaUnder μ X - 1 / sigmaOver μ X := by
            have h : 1 / sigmaOver μ X ≤ 1 / sigmaUnder μ X :=
              one_div_le_one_div_of_le hσUpos hσUle
            linarith
          by_cases hx : ε + sigmaOver μ X *
              (standardizedMaxMean μ X + Real.sqrt (2 * Real.log (sigmaUnder μ X / ε))) ≤ |x|
          · have hfar :=
              statopia_math_node_2065093509_40b0bf1d μ p hp X Sigma hGauss hL2 hpos hInt ε hε hcase x hx
            have h1 : (μ {ω | |coordMax X ω - x| ≤ ε}).toReal ≤ ε / sigmaUnder μ X :=
              ENNReal.toReal_le_of_le_ofReal (by positivity) hfar
            have hεc : ε / sigmaUnder μ X ≤ Cv * ε := by
              have h2 : ε * (1 / sigmaUnder μ X) ≤ ε * Cv :=
                mul_le_mul_of_nonneg_left hCleCv hε.le
              calc ε / sigmaUnder μ X = ε * (1 / sigmaUnder μ X) := by ring
                _ ≤ ε * Cv := h2
                _ = Cv * ε := by ring
            have h4 : 0 ≤ Cv * ε := mul_nonneg hCposCv.le hε.le
            have h5 : (1:ℝ) ≤ standardizedMaxMean μ X + R := by linarith
            calc (μ {ω | |coordMax X ω - x| ≤ ε}).toReal ≤ ε / sigmaUnder μ X := h1
              _ ≤ Cv * ε := hεc
              _ ≤ Cv * ε * (standardizedMaxMean μ X + R) := le_mul_of_one_le_right h4 h5
          · have hx' : |x| ≤ ε + sigmaOver μ X *
                (standardizedMaxMean μ X + Real.sqrt (2 * Real.log (sigmaUnder μ X / ε))) :=
              le_of_lt (lt_of_not_ge hx)
            have hmidb :=
              statopia_math_node_966165858_9b26162f μ p hp X Sigma hGauss hL2 hpos hInt x ε hε
            have hδT : (1 / sigmaUnder μ X - 1 / sigmaOver μ X) * |x| ≤
                (1 / sigmaUnder μ X - 1 / sigmaOver μ X) * (ε + sigmaOver μ X *
                  (standardizedMaxMean μ X + Real.sqrt (2 * Real.log (sigmaUnder μ X / ε)))) :=
              mul_le_mul_of_nonneg_left hx' hδnonneg
            have hbr : (1 / sigmaUnder μ X - 1 / sigmaOver μ X) * |x| +
                standardizedMaxMean μ X + 1 ≤ (sigmaOver μ X / sigmaUnder μ X +
                  (sigmaOver μ X / sigmaUnder μ X - 1) * Real.sqrt 2 +
                    (2 - sigmaUnder μ X / sigmaOver μ X)) * (standardizedMaxMean μ X + R) := by
              linarith [hδT, hmid]
            have hgnn : 0 ≤ 4 * ε / sigmaUnder μ X := by positivity
            have hnn : 0 ≤ 4 * ε / sigmaUnder μ X * ((sigmaOver μ X / sigmaUnder μ X +
                (sigmaOver μ X / sigmaUnder μ X - 1) * Real.sqrt 2 +
                  (2 - sigmaUnder μ X / sigmaOver μ X)) * (standardizedMaxMean μ X + R)) :=
              mul_nonneg hgnn (mul_nonneg hC0nonneg haR)
            have hstep1 : 4 * ε / sigmaUnder μ X *
                  ((1 / sigmaUnder μ X - 1 / sigmaOver μ X) * |x| + standardizedMaxMean μ X + 1) ≤
                4 * ε / sigmaUnder μ X * ((sigmaOver μ X / sigmaUnder μ X +
                  (sigmaOver μ X / sigmaUnder μ X - 1) * Real.sqrt 2 +
                    (2 - sigmaUnder μ X / sigmaOver μ X)) * (standardizedMaxMean μ X + R)) :=
              mul_le_mul_of_nonneg_left hbr hgnn
            have h1 : (μ {ω | |coordMax X ω - x| ≤ ε}).toReal ≤ 4 * ε / sigmaUnder μ X *
                ((sigmaOver μ X / sigmaUnder μ X + (sigmaOver μ X / sigmaUnder μ X - 1) * Real.sqrt 2 +
                  (2 - sigmaUnder μ X / sigmaOver μ X)) * (standardizedMaxMean μ X + R)) :=
              ENNReal.toReal_le_of_le_ofReal hnn
                (le_trans hmidb (ENNReal.ofReal_le_ofReal hstep1))
            have hstep2 : 4 * ε / sigmaUnder μ X * ((sigmaOver μ X / sigmaUnder μ X +
                  (sigmaOver μ X / sigmaUnder μ X - 1) * Real.sqrt 2 +
                    (2 - sigmaUnder μ X / sigmaOver μ X)) * (standardizedMaxMean μ X + R)) ≤
                Cv * ε * (standardizedMaxMean μ X + R) := by
              have hεR : 0 ≤ ε * (standardizedMaxMean μ X + R) := mul_nonneg hε.le haR
              have heq : 4 * ε / sigmaUnder μ X * ((sigmaOver μ X / sigmaUnder μ X +
                    (sigmaOver μ X / sigmaUnder μ X - 1) * Real.sqrt 2 +
                      (2 - sigmaUnder μ X / sigmaOver μ X)) * (standardizedMaxMean μ X + R)) =
                  (4 * (sigmaOver μ X / sigmaUnder μ X + (sigmaOver μ X / sigmaUnder μ X - 1) *
                      Real.sqrt 2 + (2 - sigmaUnder μ X / sigmaOver μ X)) / sigmaUnder μ X) *
                    (ε * (standardizedMaxMean μ X + R)) := by ring
              rw [heq]
              calc (4 * (sigmaOver μ X / sigmaUnder μ X + (sigmaOver μ X / sigmaUnder μ X - 1) *
                      Real.sqrt 2 + (2 - sigmaUnder μ X / sigmaOver μ X)) / sigmaUnder μ X) *
                    (ε * (standardizedMaxMean μ X + R))
                  ≤ Cv * (ε * (standardizedMaxMean μ X + R)) :=
                    mul_le_mul_of_nonneg_right h4C0 hεR
                _ = Cv * ε * (standardizedMaxMean μ X + R) := by ring
            linarith
        · have hgt : sigmaUnder μ X < ε := lt_of_not_ge hcase
          have hR1 : R = 1 := by
            rw [hR]
            have hlt : sigmaUnder μ X / ε < 1 := by
              rw [div_lt_one hε]
              exact hgt
            have hlog : Real.log (sigmaUnder μ X / ε) < 0 := Real.log_neg (by positivity) hlt
            rw [max_eq_left (by linarith : Real.log (sigmaUnder μ X / ε) ≤ 1), Real.sqrt_one]
          have hmu1 : (μ {ω | |coordMax X ω - x| ≤ ε}).toReal ≤ 1 := by
            have hle1 : (μ {ω | |coordMax X ω - x| ≤ ε}) ≤ 1 := by
              calc μ {ω | |coordMax X ω - x| ≤ ε} ≤ μ Set.univ := measure_mono (Set.subset_univ _)
                _ = 1 := measure_univ
            calc (μ {ω | |coordMax X ω - x| ≤ ε}).toReal ≤ (1 : ℝ≥0∞).toReal :=
                  ENNReal.toReal_mono ENNReal.one_ne_top hle1
              _ = 1 := ENNReal.toReal_one
          have hCε : (1:ℝ) ≤ Cv * ε := by
            have h1 : (1:ℝ) ≤ Cv * sigmaUnder μ X := by rw [hCsCv]; linarith
            nlinarith [h1, hCposCv, hgt]
          have hstep : (1:ℝ) ≤ Cv * ε * (standardizedMaxMean μ X + R) := by
            rw [hR1]
            have ha1 : (1:ℝ) ≤ standardizedMaxMean μ X + 1 := by linarith
            calc (1:ℝ) = 1 * 1 := by ring
              _ ≤ (Cv * ε) * (standardizedMaxMean μ X + 1) :=
                  mul_le_mul hCε ha1 (by norm_num) (mul_nonneg hCposCv.le hε.le)
              _ = Cv * ε * (standardizedMaxMean μ X + 1) := by ring
          linarith
      exact ciSup_le hkey
  /- @proof-region region.root.b332bd30ec5e end -/

end Statlib.Imported

