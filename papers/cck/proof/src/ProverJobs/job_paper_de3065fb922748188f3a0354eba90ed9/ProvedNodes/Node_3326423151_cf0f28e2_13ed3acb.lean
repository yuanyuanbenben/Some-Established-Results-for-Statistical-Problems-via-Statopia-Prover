import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.Vocabulary
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.Base
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.ProvedNodes.Node_2103973696_3a1ca2b0_181d2773
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.ProvedNodes.Node_328380164_659dc211_868ab021
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.ProvedNodes.Node_4284577856_99606abc_3db080b6

namespace PaperProofTasks.job_paper_de3065fb922748188f3a0354eba90ed9
open _root_.PaperProofTasks.job_paper_de3065fb922748188f3a0354eba90ed9.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

set_option autoImplicit false in
theorem statopia_math_node_3326423151_cf0f28e2 : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : ℕ) (hq : 1 ≤ q)
    (V : Ω → Fin q → ℝ) (hV : Measurable V)
    (Sigma : Matrix (Fin q) (Fin q) ℝ) (nu : Fin q → ℝ)
    (hVar : ∀ k : Fin q, Sigma k k = 1)
    (hMean : ∀ k : Fin q, nu k = ∫ ω, V ω k ∂μ)
    (hCov : ∀ k l : Fin q, Sigma k l = ∫ ω, (V ω k - nu k) * (V ω l - nu l) ∂μ)
    (hGauss : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ
      (fun ω k => V ω k - nu k) Sigma)
    (hL2 : ∀ k : Fin q, MemLp (fun ω => V ω k) 2 μ)
    (j : Fin q),
    (∀ (g : ({k : Fin q // k ≠ j} → ℝ) → ℝ), Measurable g →
      (∃ C : ℝ, ∀ y, |g y| ≤ C) →
      ∀ B : Set ℝ, MeasurableSet B →
        (∫ ω in {ω | V ω j ∈ B}, g (fun k => V ω k.1) ∂μ) =
          ∫ z in B,
            (∫ y, g y ∂
              (Statlib.Imported.gaussianVecMeasure
                (fun k : {k : Fin q // k ≠ j} => nu k.1 + (z - nu j) * Sigma k.1 j)
                (fun k l : {k : Fin q // k ≠ j} =>
                  Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j)))
            ∂(Measure.map (fun ω => V ω j) μ)) ∧
      (∀ B : Set ℝ, MeasurableSet B →
        μ ({ω | V ω j ∈ B} ∩ {ω | ∀ k : {k : Fin q // k ≠ j}, V ω k.1 ≤ V ω j}) =
          ∫⁻ z in B,
            (Statlib.Imported.gaussianVecMeasure
              (fun k : {k : Fin q // k ≠ j} => nu k.1 + (z - nu j) * Sigma k.1 j)
              (fun k l : {k : Fin q // k ≠ j} =>
                Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j))
            {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ z}
            ∂(Measure.map (fun ω => V ω j) μ)) ∧
      (∀ᵐ z ∂(Measure.map (fun ω => V ω j) μ),
        (Measure.map (fun ω => (V ω j, fun k : {k : Fin q // k ≠ j} => V ω k.1)) μ).condKernel z
            {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ z} =
          (Statlib.Imported.gaussianVecMeasure
            (fun k : {k : Fin q // k ≠ j} => nu k.1 + (z - nu j) * Sigma k.1 j)
            (fun k l : {k : Fin q // k ≠ j} =>
              Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j))
          {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ z}) := by
  /- @proof-region region.target-node.session.78bd25700c881525 begin -/
  intro Ω _ μ _ q hq V hV Sigma nu hVar hMean hCov hGauss hL2 j
  classical
  have hpair : Measurable
      (fun ω : Ω => (V ω j, fun k : {k : Fin q // k ≠ j} => V ω k.1)) := by
    refine Measurable.prod ?_ ?_
    · exact (measurable_pi_apply j).comp hV
    · rw [measurable_pi_iff]
      intro k
      exact (measurable_pi_apply (k : Fin q)).comp hV
  have hbox : ∀ z : ℝ,
      MeasurableSet {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ z} := by
    intro z
    have hk : ∀ k : {k : Fin q // k ≠ j},
        Measurable (fun y : {k : Fin q // k ≠ j} → ℝ => y k) :=
      fun k => measurable_pi_apply k
    have hz : Measurable (fun _ : {k : Fin q // k ≠ j} → ℝ => z) := measurable_const
    have hint : MeasurableSet (⋂ k : {k : Fin q // k ≠ j}, {y : {k : Fin q // k ≠ j} → ℝ | y k ≤ z}) :=
      MeasurableSet.iInter (fun k => measurableSet_le (hk k) hz)
    have hset : (⋂ k : {k : Fin q // k ≠ j}, {y : {k : Fin q // k ≠ j} → ℝ | y k ≤ z})
        = {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ z} := by
      ext y
      simp
    rw [hset] at hint
    exact hint
  have hpairj : Measurable (fun ω : Ω => V ω j) := (measurable_pi_apply j).comp hV
  have hρfst :
      (Measure.map (fun ω : Ω => (V ω j, fun k : {k : Fin q // k ≠ j} => V ω k.1)) μ).fst
        = Measure.map (fun ω => V ω j) μ := by
    ext s hs
    have hs' : MeasurableSet (Prod.fst ⁻¹' s : Set (ℝ × ({k : Fin q // k ≠ j} → ℝ))) :=
      hs.preimage measurable_fst
    have hpre : (fun ω : Ω => (V ω j, fun k : {k : Fin q // k ≠ j} => V ω k.1)) ⁻¹'
        (Prod.fst ⁻¹' s : Set (ℝ × ({k : Fin q // k ≠ j} → ℝ))) = (fun ω => V ω j) ⁻¹' s := by
      ext ω
      simp
    rw [Measure.fst_apply hs, Measure.map_apply hpair hs', hpre, Measure.map_apply hpairj hs]
  have hjoint : ∀ B : Set ℝ, MeasurableSet B →
      MeasurableSet {p : ℝ × ({k : Fin q // k ≠ j} → ℝ) | p.1 ∈ B ∧ ∀ k, p.2 k ≤ p.1} := by
    intro B hB
    have hk : ∀ k : {k : Fin q // k ≠ j},
        Measurable (fun p : ℝ × ({k : Fin q // k ≠ j} → ℝ) => p.2 k) :=
      fun k => (measurable_pi_apply k).comp measurable_snd
    have hfst : Measurable (fun p : ℝ × ({k : Fin q // k ≠ j} → ℝ) => p.1) := measurable_fst
    refine MeasurableSet.inter ?_ ?_
    · exact hB.preimage measurable_fst
    · have hint : MeasurableSet (⋂ k : {k : Fin q // k ≠ j},
          {p : ℝ × ({k : Fin q // k ≠ j} → ℝ) | p.2 k ≤ p.1}) :=
        MeasurableSet.iInter (fun k => measurableSet_le (hk k) hfst)
      have hset : (⋂ k : {k : Fin q // k ≠ j},
          {p : ℝ × ({k : Fin q // k ≠ j} → ℝ) | p.2 k ≤ p.1})
          = {p : ℝ × ({k : Fin q // k ≠ j} → ℝ) | ∀ k, p.2 k ≤ p.1} := by
        ext p
        simp
      rw [hset] at hint
      exact hint
  have hρbox : ∀ B : Set ℝ, MeasurableSet B →
      (Measure.map (fun ω : Ω => (V ω j, fun k : {k : Fin q // k ≠ j} => V ω k.1)) μ)
        {p : ℝ × ({k : Fin q // k ≠ j} → ℝ) | p.1 ∈ B ∧ ∀ k, p.2 k ≤ p.1}
      = μ ({ω | V ω j ∈ B} ∩ {ω | ∀ k : {k : Fin q // k ≠ j}, V ω k.1 ≤ V ω j}) := by
    intro B hB
    rw [Measure.map_apply hpair (hjoint B hB)]
    congr 1
  have hSigmaSymm : Sigma.IsSymm := by
    ext k l
    rw [Matrix.transpose_apply, hCov l k, hCov k l]
    simp only [mul_comm]
  have hSigmaPSD : (((2 : ℝ)⁻¹) • (Sigma + Sigma.transpose)).PosSemidef :=
    Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.posSemidef_symmetrizedCovariance
      hGauss hq
  have hSigmaPSD' : Sigma.PosSemidef := by
    have hsym : (((2 : ℝ)⁻¹) • (Sigma + Sigma.transpose)) = Sigma := by
      have h : Sigma.transpose = Sigma := hSigmaSymm
      rw [h]
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    exact hsym ▸ hSigmaPSD
  have hlaw : Measure.map (fun ω : Ω => (fun k => V ω k - nu k)) μ
      = Measure.map
          (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector
            (((2 : ℝ)⁻¹) • (Sigma + Sigma.transpose)))
          (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi q) :=
    hGauss.map_eq_canonicalGaussianVector hq
  have hΦ : Measurable (fun x : Fin q → ℝ =>
      (x j + nu j, fun k : {k : Fin q // k ≠ j} => x k.1 + nu k.1)) := by
    refine Measurable.prod ?_ ?_
    · exact (measurable_pi_apply j).add measurable_const
    · rw [measurable_pi_iff]
      intro k
      exact (measurable_pi_apply (k : Fin q)).add measurable_const
  have hpairlaw :
      Measure.map (fun ω : Ω => (V ω j, fun k : {k : Fin q // k ≠ j} => V ω k.1)) μ
        = Measure.map (fun x : Fin q → ℝ =>
            (x j + nu j, fun k : {k : Fin q // k ≠ j} => x k.1 + nu k.1))
          (Measure.map
            (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector
              (((2 : ℝ)⁻¹) • (Sigma + Sigma.transpose)))
            (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi q)) := by
    have h1 : (fun ω : Ω => (V ω j, fun k : {k : Fin q // k ≠ j} => V ω k.1))
        = (fun x : Fin q → ℝ =>
            (x j + nu j, fun k : {k : Fin q // k ≠ j} => x k.1 + nu k.1))
          ∘ (fun ω : Ω => (fun k => V ω k - nu k)) := by
      funext ω
      simp [sub_add_cancel]
    have hshift : Measurable (fun ω : Ω => (fun k => V ω k - nu k)) := by
      simpa using hV.sub (measurable_const : Measurable (fun _ : Ω => nu))
    calc Measure.map (fun ω : Ω => (V ω j, fun k : {k : Fin q // k ≠ j} => V ω k.1)) μ
        = Measure.map ((fun x : Fin q → ℝ =>
              (x j + nu j, fun k : {k : Fin q // k ≠ j} => x k.1 + nu k.1))
            ∘ (fun ω : Ω => (fun k => V ω k - nu k))) μ := by rw [h1]
      _ = Measure.map (fun x : Fin q → ℝ =>
              (x j + nu j, fun k : {k : Fin q // k ≠ j} => x k.1 + nu k.1))
            (Measure.map (fun ω : Ω => (fun k => V ω k - nu k)) μ) := by
          rw [Measure.map_map hΦ hshift]
      _ = Measure.map (fun x : Fin q → ℝ =>
              (x j + nu j, fun k : {k : Fin q // k ≠ j} => x k.1 + nu k.1))
            (Measure.map
              (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector
                (((2 : ℝ)⁻¹) • (Sigma + Sigma.transpose)))
              (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi q)) := by
          rw [hlaw]
  have hLHS1 : ∀ (g : ({k : Fin q // k ≠ j} → ℝ) → ℝ) (B : Set ℝ), Measurable g →
      MeasurableSet B →
      (∫ ω in {ω | V ω j ∈ B}, g (fun k => V ω k.1) ∂μ)
        = ∫ p in {p : ℝ × ({k : Fin q // k ≠ j} → ℝ) | p.1 ∈ B}, g p.2
            ∂(Measure.map (fun ω : Ω => (V ω j, fun k : {k : Fin q // k ≠ j} => V ω k.1)) μ) := by
    intro g B hg hB
    have hset : MeasurableSet {p : ℝ × ({k : Fin q // k ≠ j} → ℝ) | p.1 ∈ B} :=
      hB.preimage measurable_fst
    have hf : AEStronglyMeasurable (fun p : ℝ × ({k : Fin q // k ≠ j} → ℝ) => g p.2)
        (Measure.map (fun ω : Ω => (V ω j, fun k : {k : Fin q // k ≠ j} => V ω k.1)) μ) :=
      (hg.comp measurable_snd).aestronglyMeasurable
    rw [setIntegral_map hset hf hpair.aemeasurable]
    rfl
  have hLHS2 : ∀ (g : ({k : Fin q // k ≠ j} → ℝ) → ℝ) (B : Set ℝ),
      (∃ C : ℝ, ∀ y, |g y| ≤ C) → Measurable g → MeasurableSet B →
      (∫ p in {p : ℝ × ({k : Fin q // k ≠ j} → ℝ) | p.1 ∈ B}, g p.2
          ∂(Measure.map (fun ω : Ω => (V ω j, fun k : {k : Fin q // k ≠ j} => V ω k.1)) μ))
        = ∫ z in B,
            (∫ y, g y ∂((Measure.map (fun ω : Ω => (V ω j, fun k : {k : Fin q // k ≠ j} => V ω k.1)) μ).condKernel z))
            ∂(Measure.map (fun ω => V ω j) μ) := by
    intro g B hb hg hB
    obtain ⟨C, hC⟩ := hb
    have hbound : ∀ᵐ p ∂(Measure.map (fun ω : Ω => (V ω j, fun k : {k : Fin q // k ≠ j} => V ω k.1)) μ),
        ‖g p.2‖ ≤ C :=
      Filter.Eventually.of_forall (fun p => by simpa [Real.norm_eq_abs] using hC p.2)
    have hInt_all : Integrable (fun p : ℝ × ({k : Fin q // k ≠ j} → ℝ) => g p.2)
        (Measure.map (fun ω : Ω => (V ω j, fun k : {k : Fin q // k ≠ j} => V ω k.1)) μ) :=
      Integrable.of_bound (hg.comp measurable_snd).aestronglyMeasurable C hbound
    have hInt : IntegrableOn (fun p : ℝ × ({k : Fin q // k ≠ j} → ℝ) => g p.2)
        (B ×ˢ (Set.univ : Set ({k : Fin q // k ≠ j} → ℝ)))
        (Measure.map (fun ω : Ω => (V ω j, fun k : {k : Fin q // k ≠ j} => V ω k.1)) μ) :=
      hInt_all.integrableOn
    have huniv : (B ×ˢ (Set.univ : Set ({k : Fin q // k ≠ j} → ℝ)))
        = {p : ℝ × ({k : Fin q // k ≠ j} → ℝ) | p.1 ∈ B} := by
      ext p
      simp
    have key := Measure.setIntegral_condKernel_univ_right
      (ρ := Measure.map (fun ω : Ω => (V ω j, fun k : {k : Fin q // k ≠ j} => V ω k.1)) μ)
      (f := fun p : ℝ × ({k : Fin q // k ≠ j} → ℝ) => g p.2) hB hInt
    rw [huniv, hρfst] at key
    exact key.symm
  have hcondbox : ∀ B : Set ℝ, MeasurableSet B →
      ∫⁻ z in B,
        ((Measure.map (fun ω : Ω => (V ω j, fun k : {k : Fin q // k ≠ j} => V ω k.1)) μ).condKernel z)
          {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ z} ∂(Measure.map (fun ω => V ω j) μ)
      = (Measure.map (fun ω : Ω => (V ω j, fun k : {k : Fin q // k ≠ j} => V ω k.1)) μ)
          {p : ℝ × ({k : Fin q // k ≠ j} → ℝ) | p.1 ∈ B ∧ ∀ k, p.2 k ≤ p.1} := by
    intro B hB
    have hS : MeasurableSet
        {p : ℝ × ({k : Fin q // k ≠ j} → ℝ) | p.1 ∈ B ∧ ∀ k, p.2 k ≤ p.1} := hjoint B hB
    have hg : Measurable
        ({p : ℝ × ({k : Fin q // k ≠ j} → ℝ) | p.1 ∈ B ∧ ∀ k, p.2 k ≤ p.1}.indicator
          (fun _ => (1 : ℝ≥0∞))) := measurable_const.indicator hS
    have key := Measure.setLIntegral_condKernel_univ_right
      (ρ := Measure.map (fun ω : Ω => (V ω j, fun k : {k : Fin q // k ≠ j} => V ω k.1)) μ)
      (f := {p : ℝ × ({k : Fin q // k ≠ j} → ℝ) | p.1 ∈ B ∧ ∀ k, p.2 k ≤ p.1}.indicator
        (fun _ => (1 : ℝ≥0∞))) hg hB
    rw [hρfst] at key
    have hstep1 : ∫⁻ z in B,
        ((Measure.map (fun ω : Ω => (V ω j, fun k : {k : Fin q // k ≠ j} => V ω k.1)) μ).condKernel z)
          {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ z} ∂(Measure.map (fun ω => V ω j) μ)
        = ∫⁻ b in B, ∫⁻ ω, ({p : ℝ × ({k : Fin q // k ≠ j} → ℝ) | p.1 ∈ B ∧ ∀ k, p.2 k ≤ p.1}.indicator
            (fun _ => (1 : ℝ≥0∞))) (b, ω)
            ∂((Measure.map (fun ω : Ω => (V ω j, fun k : {k : Fin q // k ≠ j} => V ω k.1)) μ).condKernel b)
          ∂(Measure.map (fun ω => V ω j) μ) := by
      rw [← MeasureTheory.lintegral_indicator hB, ← MeasureTheory.lintegral_indicator hB]
      refine lintegral_congr (fun b => ?_)
      by_cases hb : b ∈ B
      · rw [Set.indicator_of_mem hb, Set.indicator_of_mem hb]
        have hfun : (fun ω : {k : Fin q // k ≠ j} → ℝ =>
            ({p : ℝ × ({k : Fin q // k ≠ j} → ℝ) | p.1 ∈ B ∧ ∀ k, p.2 k ≤ p.1}.indicator
              (fun _ => (1 : ℝ≥0∞))) (b, ω))
            = ({y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ b}).indicator (fun _ => (1 : ℝ≥0∞)) := by
          funext ω
          by_cases hbw : ω ∈ {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ b}
          · rw [Set.indicator_of_mem hbw,
              Set.indicator_of_mem (show (b, ω) ∈ {p : ℝ × ({k : Fin q // k ≠ j} → ℝ) | p.1 ∈ B ∧ ∀ k, p.2 k ≤ p.1} from ⟨hb, hbw⟩)]
          · have hmem : (b, ω) ∉ {p : ℝ × ({k : Fin q // k ≠ j} → ℝ) | p.1 ∈ B ∧ ∀ k, p.2 k ≤ p.1} :=
              fun h => hbw h.2
            simp only [Set.indicator, hmem, hbw]
        rw [hfun, MeasureTheory.lintegral_indicator (hbox b)]
        simp
      · simp only [Set.indicator, hb]
        rfl
    have hstep2 : ∫⁻ x in (B ×ˢ (Set.univ : Set ({k : Fin q // k ≠ j} → ℝ))),
        ({p : ℝ × ({k : Fin q // k ≠ j} → ℝ) | p.1 ∈ B ∧ ∀ k, p.2 k ≤ p.1}.indicator
          (fun _ => (1 : ℝ≥0∞))) x
          ∂(Measure.map (fun ω : Ω => (V ω j, fun k : {k : Fin q // k ≠ j} => V ω k.1)) μ)
        = (Measure.map (fun ω : Ω => (V ω j, fun k : {k : Fin q // k ≠ j} => V ω k.1)) μ)
            {p : ℝ × ({k : Fin q // k ≠ j} → ℝ) | p.1 ∈ B ∧ ∀ k, p.2 k ≤ p.1} := by
      have hsub : {p : ℝ × ({k : Fin q // k ≠ j} → ℝ) | p.1 ∈ B ∧ ∀ k, p.2 k ≤ p.1}
          ⊆ (B ×ˢ (Set.univ : Set ({k : Fin q // k ≠ j} → ℝ))) := by
        intro p hp
        exact ⟨hp.1, Set.mem_univ _⟩
      have hfun : (fun x : ℝ × ({k : Fin q // k ≠ j} → ℝ) =>
            (B ×ˢ (Set.univ : Set ({k : Fin q // k ≠ j} → ℝ))).indicator
              ({p : ℝ × ({k : Fin q // k ≠ j} → ℝ) | p.1 ∈ B ∧ ∀ k, p.2 k ≤ p.1}.indicator
                (fun _ => (1 : ℝ≥0∞))) x)
          = ({p : ℝ × ({k : Fin q // k ≠ j} → ℝ) | p.1 ∈ B ∧ ∀ k, p.2 k ≤ p.1}.indicator
              (fun _ => (1 : ℝ≥0∞))) := by
        funext x
        by_cases hx : x ∈ {p : ℝ × ({k : Fin q // k ≠ j} → ℝ) | p.1 ∈ B ∧ ∀ k, p.2 k ≤ p.1}
        · rw [Set.indicator_of_mem (hsub hx), Set.indicator_of_mem hx]
        · by_cases hx' : x ∈ (B ×ˢ (Set.univ : Set ({k : Fin q // k ≠ j} → ℝ)))
          · rw [Set.indicator_of_mem hx']
          · simp only [Set.indicator, hx', hx]
            rfl
      rw [← MeasureTheory.lintegral_indicator (hB.prod MeasurableSet.univ), hfun,
        MeasureTheory.lintegral_indicator hS]
      simp
    rw [hstep1, key, hstep2]
  have hSschur := statopia_math_node_2103973696_3a1ca2b0 q j Sigma hSigmaPSD' hVar
  have hSsym := hSschur.2
  have hgauss_unfold : ∀ z : ℝ,
      Statlib.Imported.gaussianVecMeasure
        (fun k : {k : Fin q // k ≠ j} => nu k.1 + (z - nu j) * Sigma k.1 j)
        (fun k l : {k : Fin q // k ≠ j} => Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j)
        = Measure.map (fun y : {k : Fin q // k ≠ j} → ℝ =>
            (fun k : {k : Fin q // k ≠ j} => nu k.1 + (z - nu j) * Sigma k.1 j)
              + Matrix.mulVec (Matrix.PosSemidef.sqrt hSsym) y)
            (Statlib.Imported.stdGaussianPi {k : Fin q // k ≠ j}) := by
    intro z
    rw [Statlib.Imported.gaussianVecMeasure, dif_pos hSsym]
  have hSqrtCont : Continuous (fun y : {k : Fin q // k ≠ j} → ℝ =>
      Matrix.mulVec (Matrix.PosSemidef.sqrt hSsym) y) :=
    LinearMap.continuous_of_finiteDimensional (Matrix.mulVecLin (Matrix.PosSemidef.sqrt hSsym))
  have hSqrtMeas : Measurable (fun y : {k : Fin q // k ≠ j} → ℝ =>
      Matrix.mulVec (Matrix.PosSemidef.sqrt hSsym) y) := hSqrtCont.measurable
  have haffMeas : ∀ m : {k : Fin q // k ≠ j} → ℝ,
      Measurable (fun y : {k : Fin q // k ≠ j} → ℝ =>
        m + Matrix.mulVec (Matrix.PosSemidef.sqrt hSsym) y) :=
    fun m => measurable_const.add hSqrtMeas
  have hjointAff : Measurable (fun p : ℝ × ({k : Fin q // k ≠ j} → ℝ) =>
      (fun k : {k : Fin q // k ≠ j} => nu k.1 + (p.1 - nu j) * Sigma k.1 j)
        + Matrix.mulVec (Matrix.PosSemidef.sqrt hSsym) p.2) := by
    refine Measurable.add ?_ ?_
    · rw [measurable_pi_iff]
      intro k
      exact measurable_const.add
        ((measurable_fst.sub measurable_const).mul measurable_const)
    · exact hSqrtMeas.comp measurable_snd

  have hgauss_univ : ∀ z : ℝ,
      (Statlib.Imported.gaussianVecMeasure
        (fun k : {k : Fin q // k ≠ j} => nu k.1 + (z - nu j) * Sigma k.1 j)
        (fun k l : {k : Fin q // k ≠ j} => Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j))
        (Set.univ : Set ({k : Fin q // k ≠ j} → ℝ)) = 1 := by
    intro z
    rw [hgauss_unfold z, Measure.map_apply (haffMeas _) MeasurableSet.univ]
    simp [Statlib.Imported.stdGaussianPi]
  haveI hstdprob : IsProbabilityMeasure (Statlib.Imported.stdGaussianPi {k : Fin q // k ≠ j}) := by
    rw [Statlib.Imported.stdGaussianPi]
    infer_instance
  have hprob : ∀ z : ℝ, IsProbabilityMeasure
      (Statlib.Imported.gaussianVecMeasure
        (fun k : {k : Fin q // k ≠ j} => nu k.1 + (z - nu j) * Sigma k.1 j)
        (fun k l : {k : Fin q // k ≠ j} => Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j)) := by
    intro z
    rw [hgauss_unfold z]
    exact MeasureTheory.Measure.isProbabilityMeasure_map ((haffMeas _).aemeasurable)
  have hprobκ : ∀ z : ℝ, IsProbabilityMeasure
      ((Measure.map (fun ω : Ω => (V ω j, fun k : {k : Fin q // k ≠ j} => V ω k.1)) μ).condKernel z) :=
    fun z => inferInstance
  have hRmeas : Measurable (fun ω : Ω => fun k : {k : Fin q // k ≠ j} =>
      (V ω k.1 - nu k.1) - Sigma k.1 j * (V ω j - nu j)) := by
    rw [measurable_pi_iff]
    intro k
    have h1 : Measurable (fun ω : Ω => V ω k.1 - nu k.1) :=
      ((measurable_pi_apply (k : Fin q)).comp hV).sub measurable_const
    have h2 : Measurable (fun ω : Ω => Sigma k.1 j * (V ω j - nu j)) :=
      measurable_const.mul (((measurable_pi_apply j).comp hV).sub measurable_const)
    exact h1.sub h2
  have hdecomp : ∀ (ω : Ω) (k : {k : Fin q // k ≠ j}),
      V ω k.1 = (nu k.1 + (V ω j - nu j) * Sigma k.1 j)
        + ((V ω k.1 - nu k.1) - Sigma k.1 j * (V ω j - nu j)) := by
    intro ω k
    ring
  have hDpsd : (Sigma.submatrix (fun k : {k : Fin q // k ≠ j} => k.1)
      (fun k : {k : Fin q // k ≠ j} => k.1)).PosSemidef :=
    hSigmaPSD'.submatrix (fun k : {k : Fin q // k ≠ j} => k.1)
  have hRgauss : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ
      (fun ω => Matrix.mulVec
        (Matrix.of (fun k a : Fin q => (if k = a then (1 : ℝ) else 0)
          - Sigma k j * (if a = j then (1 : ℝ) else 0)))
        (fun k => V ω k - nu k))
      ((Matrix.of (fun k a : Fin q => (if k = a then (1 : ℝ) else 0)
          - Sigma k j * (if a = j then (1 : ℝ) else 0)))
        * Sigma
        * (Matrix.of (fun k a : Fin q => (if k = a then (1 : ℝ) else 0)
          - Sigma k j * (if a = j then (1 : ℝ) else 0))).transpose) :=
    Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.linearImage
      μ (fun ω k => V ω k - nu k) Sigma hGauss
      (Matrix.of (fun k a : Fin q => (if k = a then (1 : ℝ) else 0)
        - Sigma k j * (if a = j then (1 : ℝ) else 0)))
  have hΘmeas : Measurable (fun p : ℝ × ({k : Fin q // k ≠ j} → ℝ) =>
      (p.1, fun k : {k : Fin q // k ≠ j} =>
        (nu k.1 + (p.1 - nu j) * Sigma k.1 j) + p.2 k)) := by
    refine Measurable.prod measurable_fst ?_
    rw [measurable_pi_iff]
    intro k
    exact (measurable_const.add
      ((measurable_fst.sub measurable_const).mul measurable_const)).add
      ((measurable_pi_apply k).comp measurable_snd)
  have hpairViaResid :
      Measure.map (fun ω : Ω => (V ω j, fun k : {k : Fin q // k ≠ j} => V ω k.1)) μ
        = Measure.map (fun p : ℝ × ({k : Fin q // k ≠ j} → ℝ) =>
            (p.1, fun k : {k : Fin q // k ≠ j} =>
              (nu k.1 + (p.1 - nu j) * Sigma k.1 j) + p.2 k))
          (Measure.map (fun ω : Ω => (V ω j, fun k : {k : Fin q // k ≠ j} =>
              (V ω k.1 - nu k.1) - Sigma k.1 j * (V ω j - nu j))) μ) := by
    have h1 : (fun ω : Ω => (V ω j, fun k : {k : Fin q // k ≠ j} => V ω k.1))
        = (fun p : ℝ × ({k : Fin q // k ≠ j} → ℝ) =>
            (p.1, fun k : {k : Fin q // k ≠ j} =>
              (nu k.1 + (p.1 - nu j) * Sigma k.1 j) + p.2 k))
          ∘ (fun ω : Ω => (V ω j, fun k : {k : Fin q // k ≠ j} =>
              (V ω k.1 - nu k.1) - Sigma k.1 j * (V ω j - nu j))) := by
      funext ω
      refine Prod.ext rfl ?_
      funext k
      exact hdecomp ω k
    have hRpairMeas : Measurable (fun ω : Ω => (V ω j,
        fun k : {k : Fin q // k ≠ j} =>
          (V ω k.1 - nu k.1) - Sigma k.1 j * (V ω j - nu j))) :=
      Measurable.prod hpairj hRmeas
    rw [h1]
    exact (Measure.map_map hΘmeas hRpairMeas).symm
  have hsumU : ∀ f : Fin q → ℝ, (∑ k, (if k = j then (1 : ℝ) else 0) * f k) = f j := by
    intro f
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      rw [if_neg hk, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hvar : (∑ i, ∑ l, (if i = j then (1 : ℝ) else 0) * Sigma i l
      * (if l = j then (1 : ℝ) else 0)) = 1 := by
    have hpull : ∀ i : Fin q,
        (∑ l, (if i = j then (1 : ℝ) else 0) * Sigma i l
          * (if l = j then (1 : ℝ) else 0))
          = (if i = j then (1 : ℝ) else 0)
            * (∑ l, Sigma i l * (if l = j then (1 : ℝ) else 0)) := by
      intro i
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun l _ => by ring)
    have hone : (∑ l, Sigma j l * (if l = j then (1 : ℝ) else 0)) = 1 := by
      rw [Finset.sum_eq_single j]
      · simp [hVar j]
      · intro l _ hl
        rw [if_neg hl, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
    simp only [hpull]
    rw [hsumU (fun i => ∑ l, Sigma i l * (if l = j then (1 : ℝ) else 0)), hone]
  have hcent_marg : Measure.map (fun ω : Ω => V ω j - nu j) μ = gaussianReal 0 1 := by
    have key :=
      Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.map_linearCombination
        μ (fun ω k => V ω k - nu k) Sigma hGauss hSigmaPSD'
        (fun k => if k = j then (1 : ℝ) else 0)
    have hfun : (fun ω : Ω => ∑ k, (if k = j then (1 : ℝ) else 0) * (V ω k - nu k))
        = fun ω => V ω j - nu j := by
      funext ω
      exact hsumU (fun k => V ω k - nu k)
    rw [hfun] at key
    simpa only [hvar] using key
  have hmarg : Measure.map (fun ω : Ω => V ω j) μ = gaussianReal (nu j) 1 := by
    have hfac : (fun ω : Ω => V ω j)
        = (fun x : ℝ => x + nu j) ∘ (fun ω : Ω => V ω j - nu j) := by
      funext ω
      simp
    have hmeas_add : Measurable (fun x : ℝ => x + nu j) := measurable_id.add measurable_const
    have hmeas_sub : Measurable (fun ω : Ω => V ω j - nu j) := hpairj.sub measurable_const
    calc Measure.map (fun ω : Ω => V ω j) μ
        = Measure.map ((fun x : ℝ => x + nu j) ∘ (fun ω : Ω => V ω j - nu j)) μ := by
          rw [hfac]
      _ = Measure.map (fun x : ℝ => x + nu j)
            (Measure.map (fun ω : Ω => V ω j - nu j) μ) := by
          rw [Measure.map_map hmeas_add hmeas_sub]
      _ = Measure.map (fun x : ℝ => x + nu j) (gaussianReal 0 1) := by rw [hcent_marg]
      _ = gaussianReal (0 + nu j) 1 := by rw [ProbabilityTheory.gaussianReal_map_add_const]
      _ = gaussianReal (nu j) 1 := by rw [zero_add]
  have hkernel' : ∀ᵐ z ∂(Measure.map (fun ω => V ω j) μ),
      (Measure.map (fun ω => (V ω j, fun k : {k : Fin q // k ≠ j} => V ω k.1)) μ).condKernel z
        = Measure.map (fun y : {k : Fin q // k ≠ j} → ℝ =>
            (fun k : {k : Fin q // k ≠ j} => nu k.1 + (z - nu j) * Sigma k.1 j)
              + Matrix.mulVec (Matrix.PosSemidef.sqrt hSsym) y)
            (Statlib.Imported.stdGaussianPi {k : Fin q // k ≠ j}) := by
    have hindep : (fun ω : Ω => V ω j) ⟂ᵢ[μ]
        (fun ω : Ω => fun k : {k : Fin q // k ≠ j} =>
          (V ω k.1 - nu k.1) - Sigma k.1 j * (V ω j - nu j)) := by
      have hsum1 : ∀ (a : Fin q) (f : Fin q → ℝ),
          (∑ k, (if k = a then (1 : ℝ) else 0) * f k) = f a := by
        intro a f
        rw [Finset.sum_eq_single a]
        · simp
        · intro k _ hk
          rw [if_neg hk, zero_mul]
        · intro h
          exact absurd (Finset.mem_univ a) h
      have hzero : ∀ (a : Fin 1) (b : Fin q), (∑ k, ∑ l,
          (Matrix.of (fun (_ : Fin 1) (k : Fin q) => if k = j then (1 : ℝ) else 0)) a k
            * Sigma k l
            * (Matrix.of (fun (k : Fin q) (a : Fin q) => (if k = a then (1 : ℝ) else 0)
              - Sigma k j * (if a = j then (1 : ℝ) else 0))) b l) = 0 := by
        intro a b
        show (∑ k, ∑ l, (if k = j then (1 : ℝ) else 0) * Sigma k l
          * ((if b = l then (1 : ℝ) else 0)
            - Sigma b j * (if l = j then (1 : ℝ) else 0))) = 0
        have hpull : ∀ k : Fin q,
            (∑ l, (if k = j then (1 : ℝ) else 0) * Sigma k l
              * ((if b = l then (1 : ℝ) else 0)
                - Sigma b j * (if l = j then (1 : ℝ) else 0)))
              = (if k = j then (1 : ℝ) else 0)
                * (∑ l, Sigma k l * ((if b = l then (1 : ℝ) else 0)
                  - Sigma b j * (if l = j then (1 : ℝ) else 0))) := by
          intro k
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun l _ => by ring)
        simp only [hpull]
        rw [hsum1 j (fun k => ∑ l, Sigma k l * ((if b = l then (1 : ℝ) else 0)
          - Sigma b j * (if l = j then (1 : ℝ) else 0)))]
        have h1 : (∑ l, Sigma j l * (if b = l then (1 : ℝ) else 0)) = Sigma j b := by
          rw [Finset.sum_eq_single b]
          · simp
          · intro l _ hl
            rw [if_neg (fun h : b = l => hl h.symm), mul_zero]
          · intro h
            exact absurd (Finset.mem_univ b) h
        have h2 : (∑ l, Sigma j l * (Sigma b j * (if l = j then (1 : ℝ) else 0)))
            = Sigma b j := by
          rw [Finset.sum_eq_single j]
          · rw [if_pos rfl, hVar j]
            ring
          · intro l _ hl
            rw [if_neg hl, mul_zero, mul_zero]
          · intro h
            exact absurd (Finset.mem_univ j) h
        have h3 : (∑ l, Sigma j l * ((if b = l then (1 : ℝ) else 0)
            - Sigma b j * (if l = j then (1 : ℝ) else 0)))
            = (∑ l, Sigma j l * (if b = l then (1 : ℝ) else 0))
              - (∑ l, Sigma j l * (Sigma b j * (if l = j then (1 : ℝ) else 0))) := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun l _ => by ring)
        rw [h3, h1, h2]
        have hsym : Sigma j b = Sigma b j := congrFun (congrFun hSigmaSymm b) j
        rw [hsym, sub_self]
      have hindep0 :=
        Statlib.StatFoundation.RandomVariable.Gaussian.centeredGaussian_linearImages_indep
          μ (fun ω k => V ω k - nu k) Sigma hGauss hSigmaPSD'
          (Matrix.of (fun (_ : Fin 1) (k : Fin q) => if k = j then (1 : ℝ) else 0))
          (Matrix.of (fun (k : Fin q) (a : Fin q) => (if k = a then (1 : ℝ) else 0)
            - Sigma k j * (if a = j then (1 : ℝ) else 0)))
          hzero
      have hAcongr : ((fun y : Fin 1 → ℝ => y 0)
          ∘ (fun ω : Ω => Matrix.mulVec
              (Matrix.of (fun (_ : Fin 1) (k : Fin q) => if k = j then (1 : ℝ) else 0))
              (fun k => V ω k - nu k)))
          = fun ω : Ω => V ω j - nu j := by
        funext ω
        exact hsum1 j (fun k => V ω k - nu k)
      have hBcongr : ((fun y : Fin q → ℝ => fun k : {k : Fin q // k ≠ j} => y k.1)
          ∘ (fun ω : Ω => Matrix.mulVec
              (Matrix.of (fun (k : Fin q) (a : Fin q) => (if k = a then (1 : ℝ) else 0)
                - Sigma k j * (if a = j then (1 : ℝ) else 0)))
              (fun k => V ω k - nu k)))
          = fun ω : Ω => fun k : {k : Fin q // k ≠ j} =>
            (V ω k.1 - nu k.1) - Sigma k.1 j * (V ω j - nu j) := by
        funext ω k
        show (∑ a, ((if (k : Fin q) = a then (1 : ℝ) else 0)
          - Sigma (k : Fin q) j * (if a = j then (1 : ℝ) else 0)) * (V ω a - nu a))
          = (V ω k.1 - nu k.1) - Sigma k.1 j * (V ω j - nu j)
        have hsplit : (∑ a, ((if (k : Fin q) = a then (1 : ℝ) else 0)
            - Sigma (k : Fin q) j * (if a = j then (1 : ℝ) else 0)) * (V ω a - nu a))
            = (∑ a, (if (k : Fin q) = a then (1 : ℝ) else 0) * (V ω a - nu a))
              - (∑ a, Sigma (k : Fin q) j * (if a = j then (1 : ℝ) else 0)
                * (V ω a - nu a)) := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun a _ => by ring)
        have h2 : (∑ a, Sigma (k : Fin q) j * (if a = j then (1 : ℝ) else 0)
            * (V ω a - nu a)) = Sigma (k : Fin q) j * (V ω j - nu j) := by
          have hcongr : (∑ a, Sigma (k : Fin q) j * (if a = j then (1 : ℝ) else 0)
              * (V ω a - nu a))
              = ∑ a, Sigma (k : Fin q) j
                * ((if a = j then (1 : ℝ) else 0) * (V ω a - nu a)) :=
            Finset.sum_congr rfl (fun a _ => by ring)
          rw [hcongr, ← Finset.mul_sum, hsum1 j (fun a => V ω a - nu a)]
        have hsum1' : ∀ (a : Fin q) (f : Fin q → ℝ),
            (∑ k, (if a = k then (1 : ℝ) else 0) * f k) = f a := by
          intro a f
          rw [Finset.sum_eq_single a]
          · simp
          · intro k _ hk
            rw [if_neg (fun h : a = k => hk h.symm), zero_mul]
          · intro h
            exact absurd (Finset.mem_univ a) h
        rw [hsplit, hsum1' (k : Fin q) (fun a => V ω a - nu a), h2]
      have hindep2 : ((fun y : Fin 1 → ℝ => y 0)
            ∘ (fun ω : Ω => Matrix.mulVec
                (Matrix.of (fun (_ : Fin 1) (k : Fin q) => if k = j then (1 : ℝ) else 0))
                (fun k => V ω k - nu k)))
          ⟂ᵢ[μ] ((fun y : Fin q → ℝ => fun k : {k : Fin q // k ≠ j} => y k.1)
            ∘ (fun ω : Ω => Matrix.mulVec
                (Matrix.of (fun (k : Fin q) (a : Fin q) => (if k = a then (1 : ℝ) else 0)
                  - Sigma k j * (if a = j then (1 : ℝ) else 0)))
                (fun k => V ω k - nu k))) :=
        ProbabilityTheory.IndepFun.comp (φ := fun y : Fin 1 → ℝ => y 0)
          (ψ := fun y : Fin q → ℝ => fun k : {k : Fin q // k ≠ j} => y k.1)
          hindep0 (measurable_pi_apply (0 : Fin 1)) (by
            rw [measurable_pi_iff]
            intro k
            exact measurable_pi_apply (k : Fin q))
      have hindep3 : (fun ω : Ω => V ω j - nu j) ⟂ᵢ[μ]
          (fun ω : Ω => fun k : {k : Fin q // k ≠ j} =>
            (V ω k.1 - nu k.1) - Sigma k.1 j * (V ω j - nu j)) := by
        simpa only [hAcongr, hBcongr] using hindep2
      have hindep4 : ((fun x : ℝ => x + nu j) ∘ (fun ω : Ω => V ω j - nu j)) ⟂ᵢ[μ]
          ((fun y : {k : Fin q // k ≠ j} → ℝ => y)
            ∘ (fun ω : Ω => fun k : {k : Fin q // k ≠ j} =>
              (V ω k.1 - nu k.1) - Sigma k.1 j * (V ω j - nu j))) :=
        ProbabilityTheory.IndepFun.comp (φ := fun x : ℝ => x + nu j)
          (ψ := fun y : {k : Fin q // k ≠ j} → ℝ => y) hindep3
          (measurable_id.add measurable_const) measurable_id
      have hshift2 : ((fun x : ℝ => x + nu j) ∘ (fun ω : Ω => V ω j - nu j))
          = fun ω : Ω => V ω j := by
        funext ω
        simp
      have hRid : ((fun y : {k : Fin q // k ≠ j} → ℝ => y)
          ∘ (fun ω : Ω => fun k : {k : Fin q // k ≠ j} =>
            (V ω k.1 - nu k.1) - Sigma k.1 j * (V ω j - nu j)))
          = fun ω : Ω => fun k : {k : Fin q // k ≠ j} =>
            (V ω k.1 - nu k.1) - Sigma k.1 j * (V ω j - nu j) := by
        funext ω
        rfl
      simpa only [hshift2, hRid] using hindep4
    have hRlaw :
        Measure.map (fun ω : Ω => fun k : {k : Fin q // k ≠ j} =>
            (V ω k.1 - nu k.1) - Sigma k.1 j * (V ω j - nu j)) μ
          = Measure.map (fun y : {k : Fin q // k ≠ j} → ℝ =>
              Matrix.mulVec (Matrix.PosSemidef.sqrt hSsym) y)
            (Statlib.Imported.stdGaussianPi {k : Fin q // k ≠ j}) := by
      have hSymm : ∀ k l : Fin q, Sigma k l = Sigma l k := by
        intro k l
        exact congrFun (congrFun hSigmaSymm l) k
      have hX : Measurable (fun ω : Ω => fun k : Fin q => V ω k - nu k) :=
        hV.sub measurable_const
      have key := statopia_math_node_4284577856_99606abc μ q hq
        (fun ω : Ω => fun k : Fin q => V ω k - nu k) hX Sigma hSymm hSigmaPSD' hVar hGauss j
      refine key.trans ?_
      rw [Statlib.Imported.gaussianVecMeasure, dif_pos hSsym]
      simp
    have hprod : Measure.map (fun ω : Ω => (V ω j, fun k : {k : Fin q // k ≠ j} =>
          (V ω k.1 - nu k.1) - Sigma k.1 j * (V ω j - nu j))) μ
        = (Measure.map (fun ω => V ω j) μ).prod
            (Measure.map (fun ω : Ω => fun k : {k : Fin q // k ≠ j} =>
              (V ω k.1 - nu k.1) - Sigma k.1 j * (V ω j - nu j)) μ) :=
      Statlib.HypothesisTesting.indepFun_map_pair hpairj.aemeasurable hRmeas.aemeasurable hindep
    have hchild := statopia_math_node_328380164_659dc211 (ι := {k : Fin q // k ≠ j}) μ
      (fun ω : Ω => V ω j)
      (fun ω : Ω => fun k : {k : Fin q // k ≠ j} =>
        (V ω k.1 - nu k.1) - Sigma k.1 j * (V ω j - nu j))
      (fun z : ℝ => fun k : {k : Fin q // k ≠ j} => nu k.1 + (z - nu j) * Sigma k.1 j)
      hpairj hRmeas hΘmeas hprod
    have hbeta : Measure.map (fun ω : Ω =>
        (V ω j, (fun z : ℝ => fun k : {k : Fin q // k ≠ j} =>
            nu k.1 + (z - nu j) * Sigma k.1 j) (V ω j)
          + (fun ω : Ω => fun k : {k : Fin q // k ≠ j} =>
              (V ω k.1 - nu k.1) - Sigma k.1 j * (V ω j - nu j)) ω)) μ
        = Measure.map (fun ω : Ω => (V ω j, fun k : {k : Fin q // k ≠ j} => V ω k.1)) μ := by
      refine Measure.map_congr (Filter.Eventually.of_forall (fun ω => ?_))
      refine Prod.ext rfl ?_
      funext k
      exact (hdecomp ω k).symm
    filter_upwards [hchild] with z hz
    have hshift : Measurable (fun r : {k : Fin q // k ≠ j} → ℝ =>
        (fun k : {k : Fin q // k ≠ j} => nu k.1 + (z - nu j) * Sigma k.1 j) + r) :=
      measurable_const.add measurable_id
    have hz2 : (Measure.map (fun ω : Ω => (V ω j, fun k : {k : Fin q // k ≠ j} => V ω k.1)) μ).condKernel z
        = Measure.map (fun r : {k : Fin q // k ≠ j} → ℝ =>
            (fun k : {k : Fin q // k ≠ j} => nu k.1 + (z - nu j) * Sigma k.1 j) + r)
          (Measure.map (fun ω : Ω => fun k : {k : Fin q // k ≠ j} =>
            (V ω k.1 - nu k.1) - Sigma k.1 j * (V ω j - nu j)) μ) := by
      simpa only [← hbeta] using hz
    rw [hz2, hRlaw, Measure.map_map hshift hSqrtMeas]
    rfl
  have hkernel : ∀ᵐ z ∂(Measure.map (fun ω => V ω j) μ),
      (Measure.map (fun ω => (V ω j, fun k : {k : Fin q // k ≠ j} => V ω k.1)) μ).condKernel z
        = Statlib.Imported.gaussianVecMeasure
          (fun k : {k : Fin q // k ≠ j} => nu k.1 + (z - nu j) * Sigma k.1 j)
          (fun k l : {k : Fin q // k ≠ j} =>
            Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j) := by
    filter_upwards [hkernel'] with z hz
    rw [hz, hgauss_unfold z]
  have hker3 : ∀ᵐ z ∂(Measure.map (fun ω => V ω j) μ),
      (Measure.map (fun ω => (V ω j, fun k : {k : Fin q // k ≠ j} => V ω k.1)) μ).condKernel z
          {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ z} =
        (Statlib.Imported.gaussianVecMeasure
          (fun k : {k : Fin q // k ≠ j} => nu k.1 + (z - nu j) * Sigma k.1 j)
          (fun k l : {k : Fin q // k ≠ j} =>
            Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j))
        {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ z} := by
    filter_upwards [hkernel] with z hz
    rw [hz]
  refine ⟨?_, ?_, ?_⟩
  · intro g hg hb B hB
    rw [hLHS1 g B hg hB, hLHS2 g B hb hg hB]
    rw [← MeasureTheory.integral_indicator hB, ← MeasureTheory.integral_indicator hB]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hkernel] with z hz
    simp only [Set.indicator, hz]
  · intro B hB
    rw [← hρbox B hB, ← hcondbox B hB]
    rw [← MeasureTheory.lintegral_indicator hB, ← MeasureTheory.lintegral_indicator hB]
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [hker3] with z hz
    simp only [Set.indicator, hz]
  · exact hker3
  /- @proof-region region.target-node.session.78bd25700c881525 end -/

end Statlib.Imported

