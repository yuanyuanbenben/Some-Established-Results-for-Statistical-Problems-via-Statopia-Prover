import ProverJobs.manual_dp_weakcons_repair_20261031.NativeContraction
import ProverJobs.manual_dp_weakcons_repair_20261031.BoxedWeakCons.ProperKL
import ProverJobs.manual_dp_weakcons_repair_20261031.BoxedWeakCons.CorrectedGeometry

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators
open OfflineCorrectedDP.Statlib.Imported
open OfflineCorrectedDP.OfflineDPConsumer
open OfflineDPPredictive OfflineDPNativeContraction
noncomputable section
namespace OfflineDPUndersmoothing

variable {X Θ : Type*} [MeasurableSpace X] [MeasurableSpace Θ]
variable [MetricSpace X] [BorelSpace X] [MeasureSpace X] [CompleteSpace X]
  [SecondCountableTopology X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
  [MetricSpace Θ] [BorelSpace Θ] [StandardBorelSpace Θ] [ProperSpace Θ]

/-- Corrected undersmoothing proof, using source H1-H3 and proper parameter KL
support. No consistency or evidence bound is assumed as a free premise. -/
theorem undersmoothing_fixed_truth (M : DPMModel X Θ)
    (hmu_finite : ∀ K : Set X, IsCompact K → M.μ K < ∞)
    (hexhaustion : ∃ K : ℕ → Set Θ,
      (∀ m, IsCompact (K m)) ∧ Monotone K ∧ (⋃ m, K m) = Set.univ)
    (t : ℕ) (ht : 1 ≤ t) (p : Fin t → ℝ)
    (hp : ∀ j, 0 < p j) (hp1 : ∑ j, p j = 1)
    (θs : Fin t → Θ) (hinj : Function.Injective θs)
    (H : ProperBranchHAt M t θs p) :
    ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun n =>
      (Measure.pi (fun _ : Fin n => mixtureMeasure M p θs))
        {xs | ε < underPi M t n xs}) atTop (𝓝 0) := by
  classical
  haveI : IsFiniteMeasureOnCompacts M.μ := ⟨fun {K} hK => hmu_finite K hK⟩
  haveI : SigmaFinite M.μ := inferInstance
  have htruth := statopia_math_node_2986921194_82fe1497 M t ht p θs hp hp1
    (fun j => M.kdens_prob (θs j))
  let p0 : X → ℝ≥0∞ := fun x => ENNReal.ofReal (mixDens M p θs x)
  have hp0 : Measurable p0 := by
    apply ENNReal.measurable_ofReal.comp
    apply Finset.measurable_sum
    intro j _
    exact (M.hk_meas.comp (measurable_const.prodMk measurable_id)).const_mul (p j)
  have hp0int : ∫⁻ x, p0 x ∂M.μ = 1 := by
    have h := htruth.2.1.measure_univ
    rw [htruth.1, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
    exact h
  have hH2div : ∀ θ : ℕ → Θ, Tendsto θ atTop (cocompact Θ) →
      ∀ K : Set X, IsCompact K →
        Tendsto (fun i => M.kernel (θ i) K) atTop (𝓝 0) := by
    intro θ hθ K hK
    have h := H.H2_div θ (fun i => by rw [M.Θset_univ]; trivial) hθ K hK
    simpa only [DPMModel.kernel, kernelMeasure, withDensity_apply _ hK.measurableSet] using h
  have hH2dirac : ∀ θbar : Θ, θbar ∈ singularBoundary M → ∀ θ : ℕ → Θ,
      Tendsto θ atTop (𝓝 θbar) →
        ∃ xstar : X, WeakTendsto (fun i => M.kernel (θ i)) (Measure.dirac xstar) := by
    intro θbar hbar θ hθ
    exact H.H2_dirac θ (fun i => by rw [M.Θset_univ]; trivial) θbar hbar hθ
  have hH3 : ∀ s : ℕ, 1 ≤ s → s < t → ∀ q : Fin s → ℝ, ∀ θ : Fin s → Θ,
      (∀ j, 0 < q j) → (∑ j, q j = 1) → Function.Injective θ →
        ¬ (∀ᵐ x ∂M.μ, mixDens M p θs x = mixDens M q θ x) := by
    intro s hs hst q θ hq hq1 hθ
    exact H.H3 p θs hp hp1 (fun i j hij heq => hij (hinj heq)) s hst q θ
      hq hq1 (fun i j hij heq => hij (hθ heq))
  have hSB : singularBoundary M = ∅ := by
    ext θ
    simp [singularBoundary, M.Θset_univ]
  obtain ⟨U, hUopen, hUmem, hUdisj, _⟩ :=
    statopia_math_node_2851582091_10c14bea M hmu_finite hexhaustion t ht p hp hp1 θs hinj
      (mixtureMeasure M p θs) htruth.2.1 rfl H.H1_cont hH2div hH2dirac hH3
      (Or.inr hSB) H.H1_closed (by simp [hSB]) (by simp [M.Θset_univ])
  have hTests : FullLatentTestingTarget M t (mixtureMeasure M p θs) := by
    apply OfflineCorrectedDP.OfflineDPTesting.full_latent_testing M
      (⟨mixtureMeasure M p θs, htruth.2.1⟩ : ProbabilityMeasure X) t
      (θs ⟨0, by omega⟩) U (hUopen.mem_nhds hUmem)
    intro s hs hst Q hQ hRep
    have hInt : Q ∈ U ∩ {ν : ProbabilityMeasure X | ∃ q : Fin s → ℝ, ∃ θ : Fin s → Θ,
        (∀ j, 0 < q j) ∧ (∑ j, q j = 1) ∧ Function.Injective θ ∧
        (∀ j, θ j ∈ M.Θset) ∧ (ν : Measure X) = mixtureMeasure M q θ} := ⟨hQ, hRep⟩
    rw [hUdisj s hs hst] at hInt
    exact hInt
  rw [htruth.1] at hTests ⊢
  apply underPi_converges_from_tests_and_evidence M t p0 hp0 hp0int
    (fun x => ENNReal.ofReal_ne_top) hTests
  intro δ hδ
  exact latentEvidence_bad_probability M p0 hp0 hp0int H.H4_at δ hδ


/-- Original truth measures and mixture weights, with the two corrected model
contracts: the DP moment denominator and parameter-space H4. -/
theorem undersmoothing_source (M : DPMModel X Θ)
    (hmu_finite : ∀ K : Set X, IsCompact K → M.μ K < ∞)
    (hexhaustion : ∃ K : ℕ → Set Θ,
      (∀ m, IsCompact (K m)) ∧ Monotone K ∧ (⋃ m, K m) = Set.univ)
    (t : ℕ) (ht : 1 ≤ t)
    (R : Fin t → Measure X) (hR : ∀ j, IsProbabilityMeasure (R j))
    (hRne : ∀ i j, i ≠ j → R i ≠ R j)
    (p : Fin t → ℝ) (hp : ∀ j, 0 < p j) (hp1 : ∑ j, p j = 1)
    (hp_lt : ∀ j, p j < 1)
    (θs : Fin t → Θ) (hθsupp : ∀ j, θs j ∈ M.Q0.support)
    (hwellspec : ∀ j, R j = M.kernel (θs j))
    (hbranch : Nonempty (BranchB M t θs) ∨ BranchHProper M t θs) :
    ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun n =>
      (Measure.pi (fun _ : Fin n => ∑ j, ENNReal.ofReal (p j) • R j))
        {xs | ε < underPi M t n xs}) atTop (𝓝 0) := by
  have hinj := true_parameters_injective M t R θs hRne hwellspec
  have H := repaired_branch_to_proper_at M hmu_finite t θs p ht hp hp1 hinj hθsupp hbranch
  have htrue : (∑ j, ENNReal.ofReal (p j) • R j) = mixtureMeasure M p θs := by
    simp only [mixtureMeasure, hwellspec]
  simp_rw [htrue]
  exact undersmoothing_fixed_truth M hmu_finite hexhaustion t ht p hp hp1 θs hinj H

#print axioms undersmoothing_fixed_truth
#print axioms undersmoothing_source

end OfflineDPUndersmoothing
