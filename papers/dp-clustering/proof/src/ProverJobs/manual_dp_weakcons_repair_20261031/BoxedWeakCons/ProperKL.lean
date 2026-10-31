import Statlib.StatFoundation.BasicAnalysis.ENNRealBridge
import ProverJobs.manual_dp_weakcons_repair_20261031.ConsumerBound
import ProverJobs.manual_dp_weakcons_repair_20261031.Predictive
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open OfflineCorrectedDP.Statlib.Imported
open OfflineDPPredictive
noncomputable section
namespace OfflineCorrectedDP.OfflineDPConsumer

variable {X Θ : Type*} [MeasurableSpace X] [MeasurableSpace Θ]
variable [MetricSpace X] [BorelSpace X] [MeasureSpace X] [CompleteSpace X]
  [SecondCountableTopology X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
  [MetricSpace Θ] [BorelSpace Θ] [StandardBorelSpace Θ] [ProperSpace Θ]

/-- Genuine pushforward of the proper real mixing probability. -/
def branchMapProb (M : DPMModel X Θ) (t : ℕ) (θs : Fin t → Θ)
    (hB : BranchB M t θs) (P : ProbabilityMeasure ℝ) : ProbabilityMeasure Θ :=
  ⟨Measure.map (hB.eTheta.symm : ℝ → Θ) (P : Measure ℝ),
    Measure.isProbabilityMeasure_map hB.eTheta.symm.measurable.aemeasurable⟩

lemma branchMapProb_measurable (M : DPMModel X Θ) (t : ℕ) (θs : Fin t → Θ)
    (hB : BranchB M t θs) : Measurable (branchMapProb M t θs hB) := by
  have hcoe : Measurable (fun P : ProbabilityMeasure ℝ =>
      (branchMapProb M t θs hB P : Measure Θ)) :=
    (Measure.measurable_map _ hB.eTheta.symm.measurable).comp measurable_subtype_coe
  exact hcoe.subtype_mk

lemma map_bind_explicit {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (m : Measure A) (f : A → Measure B) (g : B → C)
    (hf : AEMeasurable f m) (hg : Measurable g) :
    (m.bind f).map g = m.bind (fun a => (f a).map g) := by
  have hdir : Measurable (fun x : B => Measure.dirac (g x)) := Measure.measurable_dirac.comp hg
  calc
    (m.bind f).map g = (m.bind f).bind (fun x => Measure.dirac (g x)) :=
      (Measure.bind_dirac_eq_map _ hg).symm
    _ = m.bind (fun a => (f a).bind (fun x => Measure.dirac (g x))) :=
      Measure.bind_bind hf hdir.aemeasurable
    _ = _ := by
      congr 1
      funext a
      exact Measure.bind_dirac_eq_map _ hg

lemma branch_mixingPrior_map (M : DPMModel X Θ) (t : ℕ) (θs : Fin t → Θ)
    (hB : BranchB M t θs) :
    mixingPrior M = (hB.pi.bind hB.Lambdafun).map (branchMapProb M t θs hB) := by
  let F : ProbabilityMeasure ℝ → Measure Θ := fun P =>
    Measure.map (hB.eTheta.symm : ℝ → Θ) (P : Measure ℝ)
  have hF : Measurable F :=
    (Measure.measurable_map _ hB.eTheta.symm.measurable).comp measurable_subtype_coe
  have hpos : ∀ᵐ α ∂hB.pi, 0 < α := by
    rw [← hB.hpiAlpha]
    exact M.piAlpha_pos
  have hζ : mixingMeasure M = (hB.pi.bind hB.Lambdafun).map F := by
    change M.piAlpha.bind M.dpLaw = _
    rw [hB.hpiAlpha]
    calc
      hB.pi.bind M.dpLaw = hB.pi.bind (fun α => (hB.Lambdafun α).map F) :=
        Measure.bind_congr_right (hpos.mono (fun α hα => hB.hdpLaw α hα))
      _ = _ := (map_bind_explicit _ _ _ hB.hLam_aemeas hF).symm
  rw [mixingPrior, hζ, Measure.map_map (toProbFallback_measurable M) hF]
  congr 1
  funext P
  have hFP : IsProbabilityMeasure (F P) :=
    Measure.isProbabilityMeasure_map hB.eTheta.symm.measurable.aemeasurable
  apply Subtype.ext
  simp only [Function.comp_apply, toProbFallback, dif_pos hFP]
  rfl

lemma branch_density_eq (M : DPMModel X Θ) (t : ℕ) (θs : Fin t → Θ)
    (hB : BranchB M t θs) (P : ProbabilityMeasure ℝ) (x : X) :
    density M (branchMapProb M t θs hB P) x =
      ENNReal.ofReal (∫ θ, hB.g (hB.eX x - θ) ∂(P : Measure ℝ)) := by
  obtain ⟨m, U, hm, hbdd⟩ := hB.T1
  have hU : 0 < U := by
    have h := hbdd 0 ⟨by linarith [hB.hc], hB.hc.le⟩
    linarith
  have hgU : ∀ y, hB.g y ≤ U := by
    intro y
    by_cases hy : y ∈ Set.Icc (-hB.c) hB.c
    · exact (hbdd y hy).2
    · rw [hB.hB1_zero y hy]; exact hU.le
  have hreal : (∫⁻ θ, ENNReal.ofReal (hB.g (hB.eX x - θ)) ∂(P : Measure ℝ)).toReal =
      ∫ θ, hB.g (hB.eX x - θ) ∂(P : Measure ℝ) := by
    refine Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.lintegral_toReal_eq_integral_of_nonneg
      (Filter.Eventually.of_forall (fun θ => hB.hg_nonneg _)) ?_
    refine Integrable.of_bound ?_ U ?_
    · exact (hB.hg_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · filter_upwards with θ
      rw [Real.norm_eq_abs, abs_of_nonneg (hB.hg_nonneg _)]
      exact hgU _
  have hen : ennDensity M (branchMapProb M t θs hB P) x =
      ∫⁻ θ, ENNReal.ofReal (hB.g (hB.eX x - θ)) ∂(P : Measure ℝ) := by
    change (∫⁻ θ, ENNReal.ofReal (M.kdens θ x)
      ∂(Measure.map (hB.eTheta.symm : ℝ → Θ) (P : Measure ℝ))) = _
    simp_rw [hB.hloc]
    have hmeas : Measurable (fun θ : Θ => ENNReal.ofReal (hB.g (hB.eX x - hB.eTheta θ))) :=
      ENNReal.measurable_ofReal.comp (hB.hg_meas.comp (measurable_const.sub hB.eTheta.measurable))
    rw [lintegral_map hmeas hB.eTheta.symm.measurable]
    simp only [hB.eTheta.apply_symm_apply]
  rw [density, hen, hreal]


lemma equiv_map_withDensity (e : X ≃ᵐ ℝ) (w : ℝ → ℝ≥0∞) (hw : Measurable w) :
    Measure.map (e.symm : ℝ → X) (volume.withDensity w) =
      (Measure.map (e.symm : ℝ → X) volume).withDensity (fun x => w (e x)) := by
  refine Measure.ext (fun s hs => ?_)
  have hwt : Measurable (fun x : X => w (e x)) := hw.comp e.measurable
  have hpre : MeasurableSet ((e.symm : ℝ → X) ⁻¹' s) := e.symm.measurable hs
  rw [Measure.map_apply e.symm.measurable hs, withDensity_apply w hpre,
    withDensity_apply (fun x : X => w (e x)) hs,
    setLIntegral_map hs hwt e.symm.measurable]
  simp

lemma branch_kl_eq (M : DPMModel X Θ) (t : ℕ) (θs : Fin t → Θ)
    (hB : BranchB M t θs) (p : Fin t → ℝ) (P : ProbabilityMeasure ℝ) :
    InformationTheory.klDiv
      (M.μ.withDensity (fun x => ENNReal.ofReal (mixDens M p θs x)))
      (M.μ.withDensity (density M (branchMapProb M t θs hB P))) =
    InformationTheory.klDiv
      (volume.withDensity fun y => ENNReal.ofReal (∑ j, p j * hB.g (y - hB.eTheta (θs j))))
      (volume.withDensity fun y => ENNReal.ofReal (∫ θ, hB.g (y - θ) ∂(P : Measure ℝ))) := by
  have hf : Measurable (fun y : ℝ => ENNReal.ofReal (∑ j, p j * hB.g (y - hB.eTheta (θs j)))) := by
    apply ENNReal.measurable_ofReal.comp
    exact Finset.measurable_sum Finset.univ (fun j _ => measurable_const.mul
      (hB.hg_meas.comp (measurable_id.sub measurable_const)))
  have hh : Measurable (fun y : ℝ => ENNReal.ofReal (∫ θ, hB.g (y - θ) ∂(P : Measure ℝ))) := by
    exact ENNReal.measurable_ofReal.comp
      ((hB.hg_meas.comp (measurable_fst.sub measurable_snd)).stronglyMeasurable.integral_prod_right').measurable
  have htruth : M.μ.withDensity (fun x => ENNReal.ofReal (mixDens M p θs x)) =
      Measure.map (hB.eX.symm : ℝ → X)
        (volume.withDensity fun y => ENNReal.ofReal (∑ j, p j * hB.g (y - hB.eTheta (θs j)))) := by
    rw [hB.hμ]
    have heq : (fun x => ENNReal.ofReal (mixDens M p θs x)) =
        (fun x => ENNReal.ofReal (∑ j, p j * hB.g (hB.eX x - hB.eTheta (θs j)))) := by
      funext x
      simp only [mixDens, hB.hloc]
    rw [heq]
    exact (equiv_map_withDensity hB.eX _ hf).symm
  have hcand : M.μ.withDensity (density M (branchMapProb M t θs hB P)) =
      Measure.map (hB.eX.symm : ℝ → X)
        (volume.withDensity fun y => ENNReal.ofReal (∫ θ, hB.g (y - θ) ∂(P : Measure ℝ))) := by
    have heq : density M (branchMapProb M t θs hB P) =
        (fun x => ENNReal.ofReal (∫ θ, hB.g (hB.eX x - θ) ∂(P : Measure ℝ))) :=
      funext (branch_density_eq M t θs hB P)
    rw [hB.hμ, heq]
    exact (equiv_map_withDensity hB.eX _ hh).symm
  haveI : SigmaFinite (volume.withDensity fun y => ENNReal.ofReal (∑ j, p j * hB.g (y - hB.eTheta (θs j)))) :=
    SigmaFinite.withDensity_of_ne_top (Filter.Eventually.of_forall (fun y => ENNReal.ofReal_ne_top))
  haveI : SigmaFinite (volume.withDensity fun y => ENNReal.ofReal (∫ θ, hB.g (y - θ) ∂(P : Measure ℝ))) :=
    SigmaFinite.withDensity_of_ne_top (Filter.Eventually.of_forall (fun y => ENNReal.ofReal_ne_top))
  rw [htruth, hcand]
  exact statopia_math_node_1335231141_76912540 hB.eX.symm _ _

/-- Proper parameter-space KL support follows from original BranchB/T4 at true atoms. -/
theorem branchB_parametric_KL_support (M : DPMModel X Θ) (t : ℕ) (θs : Fin t → Θ)
    (hB : BranchB M t θs) (p : Fin t → ℝ) (ht : 1 ≤ t)
    (hp : ∀ j, 0 < p j) (hp1 : ∑ j, p j = 1)
    (hinj : Function.Injective θs) (hsupp : ∀ j, θs j ∈ M.Q0.support) :
    ParametricKLSupport M p θs := by
  intro eps heps
  rw [branch_mixingPrior_map M t θs hB]
  have hmass := branchB_parametric_R_KL_bound M t θs hB p ht hp hp1 hinj hsupp eps heps
  apply lt_of_lt_of_le hmass
  refine le_trans (measure_mono ?_) (Measure.le_map_apply (branchMapProb_measurable M t θs hB).aemeasurable _)
  intro P hP
  change InformationTheory.klDiv
    (M.μ.withDensity (fun x => ENNReal.ofReal (mixDens M p θs x)))
    (M.μ.withDensity (density M (branchMapProb M t θs hB P))) < ENNReal.ofReal eps
  rw [branch_kl_eq M t θs hB p P]
  exact hP

/-- Source H1-H3 geometry, with no function-space KL clause. -/
structure BranchHGeometryAt (M : DPMModel X Θ) (t : ℕ) (θs : Fin t → Θ) : Prop where
  hμ : (∀ x : X, M.μ {x} = 0) ∨ M.μ = Measure.count
  H1_cont : ∀ θbar ∈ M.Θset, θbar ∉ singularBoundary M →
    ∀ᵐ x ∂M.μ, ∃ A : Set Θ, A ∈ 𝓝 θbar ∧ A ⊆ M.Θset \ singularBoundary M ∧
      ContinuousOn (fun θ => M.kdens θ x) A
  H1_closed : IsClosed (singularBoundary M)
  H2_div : ∀ (θ : ℕ → Θ), (∀ i, θ i ∈ M.Θset) → Tendsto θ atTop (cocompact Θ) →
    ∀ K : Set X, IsCompact K →
      Tendsto (fun i => ∫⁻ x in K, ENNReal.ofReal (M.kdens (θ i) x) ∂M.μ) atTop (𝓝 0)
  H2_dirac : ∀ (θ : ℕ → Θ) (hθ : ∀ i, θ i ∈ M.Θset) (θbar : Θ),
    θbar ∈ singularBoundary M → Tendsto θ atTop (𝓝 θbar) →
      ∃ xstar : X,
        WeakTendsto (fun i => M.kernel (θ i)) (Measure.dirac xstar)
  H3 : ∀ (q : Fin t → ℝ) (θ : Fin t → Θ), (∀ j, 0 < q j) → (∑ j, q j = 1) →
    (∀ i j : Fin t, i ≠ j → θ i ≠ θ j) →
    ∀ (s : ℕ), s < t → ∀ (q' : Fin s → ℝ) (θ' : Fin s → Θ),
      (∀ j, 0 < q' j) → (∑ j, q' j = 1) →
      (∀ i j : Fin s, i ≠ j → θ' i ≠ θ' j) →
      ¬ ∀ᵐ x ∂M.μ, mixDens M q θ x = mixDens M q' θ' x

/-- Fixed-truth H contract with a proper mixing-parameter KL clause. -/
structure ProperBranchHAt (M : DPMModel X Θ) (t : ℕ) (θs : Fin t → Θ)
    (p : Fin t → ℝ) : Prop extends BranchHGeometryAt M t θs where
  H4_at : ParametricKLSupport M p θs

/-- Corrected supplemental branch: H4 is stated on the proper parameter prior.
This is a repaired contract, not a theorem inferred from the old raw priorH H4. -/
structure BranchHProper (M : DPMModel X Θ) (t : ℕ) (θs : Fin t → Θ) : Prop
    extends BranchHGeometryAt M t θs where
  H4 : ∀ (s : ℕ), 0 < s → ∀ (q : Fin s → ℝ) (θ : Fin s → Θ),
    (∀ j, 0 < q j) → (∑ j, q j = 1) → (∀ i j : Fin s, i ≠ j → θ i ≠ θ j) →
    (∀ j, θ j ∈ M.Q0.support) → ParametricKLSupport M q θ

/-- Discard only the raw KL clause when retaining already-proved geometry. -/
lemma branchHAt_to_geometry (M : DPMModel X Θ) (t : ℕ) (θs : Fin t → Θ)
    (p : Fin t → ℝ) (H : BranchHAt M t θs p) : BranchHGeometryAt M t θs :=
  ⟨H.hμ, H.H1_cont, H.H1_closed, H.H2_div, H.H2_dirac, H.H3⟩

/-- The genuine B producer supplies both geometry and proper H4 at truth. -/
theorem branchB_to_proper_at (M : DPMModel X Θ)
    (hmu_finite : ∀ K : Set X, IsCompact K → M.μ K < ∞)
    (t : ℕ) (θs : Fin t → Θ) (hB : BranchB M t θs) (p : Fin t → ℝ) (ht : 1 ≤ t)
    (hp : ∀ j, 0 < p j) (hp1 : ∑ j, p j = 1)
    (hinj : Function.Injective θs) (hsupp : ∀ j, θs j ∈ M.Q0.support) :
    ProperBranchHAt M t θs p :=
  ⟨branchHAt_to_geometry M t θs p (branchB_to_at_bound M hmu_finite t θs hB p ht hp hp1 hinj hsupp),
    branchB_parametric_KL_support M t θs hB p ht hp hp1 hinj hsupp⟩

/-- B or the corrected proper-H source assumption yields the fixed-truth contract. -/
theorem repaired_branch_to_proper_at (M : DPMModel X Θ)
    (hmu_finite : ∀ K : Set X, IsCompact K → M.μ K < ∞)
    (t : ℕ) (θs : Fin t → Θ) (p : Fin t → ℝ) (ht : 1 ≤ t)
    (hp : ∀ j, 0 < p j) (hp1 : ∑ j, p j = 1)
    (hinj : Function.Injective θs) (hsupp : ∀ j, θs j ∈ M.Q0.support)
    (hbranch : Nonempty (BranchB M t θs) ∨ BranchHProper M t θs) :
    ProperBranchHAt M t θs p := by
  rcases hbranch with hB | H
  · obtain ⟨hB⟩ := hB
    exact branchB_to_proper_at M hmu_finite t θs hB p ht hp hp1 hinj hsupp
  · exact ⟨H.toBranchHGeometryAt, H.H4 t (by omega) p θs hp hp1
      (fun i j hij heq => hij (hinj heq)) hsupp⟩
end OfflineCorrectedDP.OfflineDPConsumer
