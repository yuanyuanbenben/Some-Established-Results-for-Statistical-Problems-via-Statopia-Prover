import ProverJobs.manual_dp_weakcons_repair_20261031.GenericEvidence
import ProverJobs.manual_dp_weakcons_repair_20261031.BoxedWeakCons.CorrectedConsumerBundle
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open OfflineCorrectedDP.Statlib.Imported
noncomputable section
namespace OfflineDPPredictive

variable {X Θ : Type*} [MeasurableSpace X] [MeasurableSpace Θ]

/-- Native mixing prior on measures, without a function-space pushforward. -/
def mixingMeasure (M : DPMModel X Θ) : Measure (Measure Θ) := M.piAlpha.bind M.dpLaw

/-- Measurable total extension into probability measures; fallback is source Q0. -/
def toProbFallback (M : DPMModel X Θ) (nu : Measure Θ) : ProbabilityMeasure Θ := by
  classical
  exact if h : IsProbabilityMeasure nu then ⟨nu, h⟩ else ⟨M.Q0, M.Q0_prob⟩

lemma toProbFallback_measurable (M : DPMModel X Θ) : Measurable (toProbFallback M) := by
  classical
  have hcoe : Measurable (fun nu : Measure Θ => (toProbFallback M nu : Measure Θ)) := by
    have heq : (fun nu : Measure Θ => (toProbFallback M nu : Measure Θ)) =
        (fun nu : Measure Θ => if IsProbabilityMeasure nu then nu else M.Q0) := by
      funext nu
      by_cases h : IsProbabilityMeasure nu <;> simp [toProbFallback, h]
    rw [heq]
    exact measurable_id.ite ProbabilityMeasure.measurableSet_isProbabilityMeasure measurable_const
  exact hcoe.subtype_mk

lemma mixingMeasure_prob (M : DPMModel X Θ) : IsProbabilityMeasure (mixingMeasure M) := by
  haveI := M.piAlpha_prob
  constructor
  rw [mixingMeasure, Measure.bind_apply MeasurableSet.univ M.dpLaw_meas.aemeasurable]
  simp_rw [(M.dpLaw_prob _).measure_univ]
  simp

lemma mixingMeasure_ae_prob (M : DPMModel X Θ) :
    ∀ᵐ nu ∂(mixingMeasure M), IsProbabilityMeasure nu := by
  classical
  rw [ae_iff]
  change (mixingMeasure M) {nu : Measure Θ | IsProbabilityMeasure nu}ᶜ = 0
  rw [mixingMeasure, Measure.bind_apply
    ProbabilityMeasure.measurableSet_isProbabilityMeasure.compl M.dpLaw_meas.aemeasurable]
  have hae : ∀ᵐ alpha ∂M.piAlpha,
      M.dpLaw alpha {nu : Measure Θ | ¬ IsProbabilityMeasure nu} = 0 := by
    filter_upwards [M.piAlpha_pos] with alpha halpha
    apply ae_iff.mp
    exact ((M.dpLaw_dirichlet alpha halpha).1).mono (fun nu hnu => ⟨hnu⟩)
  change (∫⁻ alpha, M.dpLaw alpha {nu : Measure Θ | ¬ IsProbabilityMeasure nu} ∂M.piAlpha) = 0
  rw [lintegral_congr_ae hae, lintegral_zero]

/-- Proper mixing-probability parameter prior. -/
def mixingPrior (M : DPMModel X Θ) : Measure (ProbabilityMeasure Θ) :=
  (mixingMeasure M).map (toProbFallback M)

lemma mixingPrior_prob (M : DPMModel X Θ) : IsProbabilityMeasure (mixingPrior M) := by
  haveI := mixingMeasure_prob M
  exact Measure.isProbabilityMeasure_map (toProbFallback_measurable M).aemeasurable

/-- Genuine nonnegative mixture density on the proper parameter. -/
def ennDensity (M : DPMModel X Θ) (P : ProbabilityMeasure Θ) (x : X) : ℝ≥0∞ :=
  ∫⁻ theta, ENNReal.ofReal (M.kdens theta x) ∂(P : Measure Θ)

lemma ennDensity_joint_measurable (M : DPMModel X Θ) :
    Measurable (Function.uncurry (ennDensity M)) := by
  let kappa : Kernel (ProbabilityMeasure Θ × X) Θ :=
    ⟨fun z => (z.1 : Measure Θ), measurable_subtype_coe.comp measurable_fst⟩
  haveI : IsMarkovKernel kappa :=
    ⟨fun z => show IsProbabilityMeasure (z.1 : Measure Θ) from inferInstance⟩
  have hfun : Measurable (Function.uncurry (fun z : ProbabilityMeasure Θ × X =>
      fun theta : Θ => ENNReal.ofReal (M.kdens theta z.2))) := by
    exact ENNReal.measurable_ofReal.comp (M.hk_meas.comp
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
  exact hfun.lintegral_kernel_prod_right (κ := kappa)

/-- Finite version, equal to the genuine ENNReal mixture almost everywhere in x. -/
def density (M : DPMModel X Θ) (P : ProbabilityMeasure Θ) (x : X) : ℝ≥0∞ :=
  ENNReal.ofReal ((ennDensity M P x).toReal)

lemma density_joint_measurable (M : DPMModel X Θ) :
    Measurable (Function.uncurry (density M)) :=
  ENNReal.measurable_ofReal.comp (ennDensity_joint_measurable M).ennreal_toReal

lemma kernel_normalized (M : DPMModel X Θ) (theta : Θ) :
    ∫⁻ x, ENNReal.ofReal (M.kdens theta x) ∂M.μ = 1 := by
  have hm := (M.kdens_prob theta).measure_univ
  change (M.μ.withDensity (fun x => ENNReal.ofReal (M.kdens theta x))) Set.univ = 1 at hm
  simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using hm

lemma ennDensity_normalized (M : DPMModel X Θ) [SigmaFinite M.μ]
    (P : ProbabilityMeasure Θ) : ∫⁻ x, ennDensity M P x ∂M.μ = 1 := by
  dsimp only [ennDensity]
  have hf : Measurable (Function.uncurry (fun x : X => fun theta : Θ =>
      ENNReal.ofReal (M.kdens theta x))) :=
    (M.hk_meas.ennreal_ofReal).comp measurable_swap
  rw [lintegral_lintegral_swap hf.aemeasurable]
  simp_rw [kernel_normalized M]
  simp

lemma density_ae_eq (M : DPMModel X Θ) [SigmaFinite M.μ]
    (P : ProbabilityMeasure Θ) : density M P =ᵐ[M.μ] ennDensity M P := by
  have hmeas : Measurable (ennDensity M P) :=
    (ennDensity_joint_measurable M).comp measurable_prodMk_left
  have hfin := ae_lt_top hmeas (by rw [ennDensity_normalized M P]; exact ENNReal.one_ne_top)
  exact hfin.mono (fun x hx => ENNReal.ofReal_toReal (ne_of_lt hx))

lemma density_normalized (M : DPMModel X Θ) [SigmaFinite M.μ]
    (P : ProbabilityMeasure Θ) : ∫⁻ x, density M P x ∂M.μ = 1 := by
  rw [lintegral_congr_ae (density_ae_eq M P), ennDensity_normalized M P]

/-- Source-faithful KL support on a measurable mixing-probability parameter. -/
def ParametricKLSupport (M : DPMModel X Θ) {t : ℕ}
    (p : Fin t → ℝ) (thetaS : Fin t → Θ) : Prop :=
  ∀ delta : ℝ, 0 < delta → 0 < (mixingPrior M)
    {P : ProbabilityMeasure Θ |
      InformationTheory.klDiv
        (M.μ.withDensity (fun x => ENNReal.ofReal (mixDens M p thetaS x)))
        (M.μ.withDensity (density M P)) < ENNReal.ofReal delta}

/-- Canonical latent evidence, before truth-density normalization. -/
def latentEvidence (M : DPMModel X Θ) (n : ℕ) (xs : Fin n → X) : ℝ≥0∞ :=
  ∫⁻ theta, dpmLikelihood M.kdens n xs theta ∂(M.priorLatent n)

lemma latentEvidence_ne_zero_top (M : DPMModel X Θ) (n : ℕ) (xs : Fin n → X) :
    latentEvidence M n xs ≠ 0 ∧ latentEvidence M n xs ≠ ⊤ := by
  haveI := M.posterior_markov n
  have h := M.posterior_bayes n xs Set.univ MeasurableSet.univ
  simp only [measure_univ, Measure.restrict_univ] at h
  change (1 : ℝ≥0∞) = latentEvidence M n xs / latentEvidence M n xs at h
  constructor
  · intro hz
    rw [hz, ENNReal.zero_div] at h
    exact one_ne_zero h
  · intro hz
    simp [hz, div_eq_mul_inv] at h

#print axioms ParametricKLSupport
#print axioms density_normalized
#print axioms mixingMeasure_ae_prob
#print axioms latentEvidence_ne_zero_top

lemma toProbFallback_coe (M : DPMModel X Θ) (nu : Measure Θ)
    (hnu : IsProbabilityMeasure nu) : (toProbFallback M nu : Measure Θ) = nu := by
  classical
  simp [toProbFallback, hnu]

/-- Finite iid product is measurable on the proper probability parameter space. -/
lemma probability_pi_measurable (n : ℕ) :
    Measurable (fun P : ProbabilityMeasure Θ => Measure.pi (fun _ : Fin n => (P : Measure Θ))) := by
  classical
  refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    generateFrom_pi.symm isPiSystem_pi ?_
  rintro _ ⟨sets, hsets, rfl⟩
  have hm : ∀ i : Fin n, MeasurableSet (sets i) := fun i => hsets i (Set.mem_univ i)
  simp_rw [Measure.pi_pi]
  exact Finset.measurable_prod Finset.univ (fun i _ =>
    (Measure.measurable_coe (hm i)).comp measurable_subtype_coe)

/-- The native latent prior is the mixture of iid products under the proper parameter prior. -/
lemma priorLatent_mixing_law (M : DPMModel X Θ) (n : ℕ) :
    M.priorLatent n = (mixingPrior M).bind
      (fun P : ProbabilityMeasure Θ => Measure.pi (fun _ : Fin n => (P : Measure Θ))) := by
  classical
  let F : ProbabilityMeasure Θ → Measure (Fin n → Θ) := fun P => Measure.pi (fun _ => (P : Measure Θ))
  let G : Measure Θ → Measure (Fin n → Θ) := fun nu => F (toProbFallback M nu)
  have hF : Measurable F := probability_pi_measurable n
  have hG : Measurable G := hF.comp (toProbFallback_measurable M)
  have hMapBind : (mixingPrior M).bind F = (mixingMeasure M).bind G := by
    apply Measure.ext
    intro S hS
    rw [Measure.bind_apply hS hF.aemeasurable, mixingPrior,
      Measure.bind_apply hS hG.aemeasurable]
    exact lintegral_map (f := fun P : ProbabilityMeasure Θ => F P S)
      ((Measure.measurable_coe hS).comp hF) (toProbFallback_measurable M)
  rw [hMapBind]
  calc M.priorLatent n = M.piAlpha.bind (fun alpha =>
      (M.dpLaw alpha).bind (fun nu => Measure.pi (fun _ : Fin n => nu))) := M.priorLatent_law n
    _ = M.piAlpha.bind (fun alpha => (M.dpLaw alpha).bind G) := by
      apply Measure.bind_congr_right
      filter_upwards [M.piAlpha_pos] with alpha halpha
      apply Measure.bind_congr_right
      filter_upwards [(M.dpLaw_dirichlet alpha halpha).1] with nu hnu
      have hprob : IsProbabilityMeasure nu := ⟨hnu⟩
      simp only [G, F, toProbFallback_coe M nu hprob]
    _ = (mixingMeasure M).bind G :=
      (Measure.bind_bind M.dpLaw_meas.aemeasurable hG.aemeasurable).symm

/-- Genuine finite-product Fubini identity, with no uniform kernel bound. -/
lemma lintegral_fin_product (nu : Measure Θ) [SigmaFinite nu] :
    ∀ (n : ℕ) (f : Fin n → Θ → ℝ≥0∞), (∀ i, Measurable (f i)) →
      ∫⁻ theta : Fin n → Θ, ∏ i : Fin n, f i (theta i)
        ∂(Measure.pi (fun _ : Fin n => nu)) = ∏ i : Fin n, ∫⁻ theta, f i theta ∂nu := by
intro n
induction n with
| zero =>
    intro f _hf
    have huniv : (Measure.pi (fun _ : Fin 0 => nu)) Set.univ = 1 := by
      simpa using Measure.pi_pi (fun _ : Fin 0 => nu) (fun _ => Set.univ)
    first
      | simp only [Finset.univ_eq_empty, Finset.prod_empty, lintegral_const, one_mul, huniv]
      | simp [huniv]
| succ n ih =>
    intro f hf
    have hmp : MeasurePreserving
        (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Θ) (0 : Fin (n + 1))))
        (Measure.pi (fun _ : Fin (n + 1) => nu))
        (nu.prod (Measure.pi (fun _ : Fin n => nu))) := by
      simpa using measurePreserving_piFinSuccAbove (μ := fun _ : Fin (n + 1) => nu)
        (0 : Fin (n + 1))
    have hL := MeasurePreserving.lintegral_map_equiv
      (fun p : Θ × (Fin n → Θ) =>
        ∏ i : Fin (n + 1), f i ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Θ) 0).symm p i))
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Θ) 0) hmp
    have h1 : ∫⁻ θ : Fin (n + 1) → Θ, (∏ i : Fin (n + 1), f i (θ i))
          ∂(Measure.pi (fun _ : Fin (n + 1) => nu))
        = ∫⁻ p : Θ × (Fin n → Θ),
            (∏ i : Fin (n + 1),
              f i ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Θ) 0).symm p i))
          ∂(nu.prod (Measure.pi (fun _ : Fin n => nu))) := by
      refine Eq.trans ?_ hL.symm
      first
        | exact lintegral_congr fun θ => by simp
        | simp
    have hsplit : ∀ p : Θ × (Fin n → Θ),
        (∏ i : Fin (n + 1),
          f i ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Θ) 0).symm p i))
          = f 0 p.1 * (∏ j : Fin n, f (Fin.succ j) (p.2 j)) := by
      intro p
      first
        | (rw [Fin.prod_univ_succ]; simp)
        | (rw [Fin.prod_univ_succ]; simp [Fin.succAbove])
        | (rw [Fin.prod_univ_succ]; simp [Fin.succAbove_zero])
    have h2 : ∫⁻ p : Θ × (Fin n → Θ),
            (∏ i : Fin (n + 1),
              f i ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Θ) 0).symm p i))
          ∂(nu.prod (Measure.pi (fun _ : Fin n => nu)))
        = (∫⁻ θ : Θ, f 0 θ ∂nu) *
          (∫⁻ ω : Fin n → Θ, (∏ j : Fin n, f (Fin.succ j) (ω j))
            ∂(Measure.pi (fun _ : Fin n => nu))) := by
      rw [lintegral_congr fun p => hsplit p]
      refine lintegral_prod_mul (μ := nu) (ν := Measure.pi (fun _ : Fin n => nu))
        (f := fun θ => f 0 θ) (g := fun ω => ∏ j : Fin n, f (Fin.succ j) (ω j))
        (hf 0).aemeasurable ?_
      have htail : Measurable (fun ω : Fin n → Θ => ∏ j : Fin n, f (Fin.succ j) (ω j)) := by
        have hπ : Measurable (fun ω : Fin n → Θ => fun j : Fin n => f (Fin.succ j) (ω j)) :=
          measurable_pi_lambda _
            (fun j => (hf (Fin.succ j)).comp (measurable_pi_apply j))
        have hprod : Measurable (fun y : Fin n → ℝ≥0∞ => ∏ j : Fin n, y j) := by
          have h := Finset.measurable_prod
            (f := fun (j : Fin n) (y : Fin n → ℝ≥0∞) => y j)
            (Finset.univ : Finset (Fin n)) (fun j _ => measurable_pi_apply j)
          simpa using h
        simpa using hprod.comp hπ
      exact htail.aemeasurable
    rw [h1, h2, ih (fun j => f (Fin.succ j)) (fun j => hf (Fin.succ j)), Fin.prod_univ_succ]

lemma latentEvidence_eq_enn_predictive (M : DPMModel X Θ) (n : ℕ) (xs : Fin n → X) :
    latentEvidence M n xs =
      ∫⁻ P : ProbabilityMeasure Θ, ∏ i : Fin n, ennDensity M P (xs i) ∂(mixingPrior M) := by
  have hlike : Measurable (fun theta : Fin n → Θ => dpmLikelihood M.kdens n xs theta) := by
    apply Finset.measurable_prod
    intro i hi
    have hpair : Measurable (fun theta : Fin n → Θ => (theta i, xs i)) :=
      (measurable_pi_apply i).prodMk measurable_const
    have hk := M.hk_meas.comp hpair
    exact ENNReal.measurable_ofReal.comp hk
  rw [latentEvidence, priorLatent_mixing_law M n,
    Measure.lintegral_bind (probability_pi_measurable n).aemeasurable hlike.aemeasurable]
  apply lintegral_congr
  intro P
  exact lintegral_fin_product (P : Measure Θ) n
    (fun i theta => ENNReal.ofReal (M.kdens theta (xs i)))
    (fun i => ENNReal.measurable_ofReal.comp
      (M.hk_meas.comp (measurable_id.prodMk measurable_const)))

#print axioms priorLatent_mixing_law
#print axioms latentEvidence_eq_enn_predictive

/-- Real-valued and ENNReal mixing densities agree for almost every data vector. -/
lemma latentEvidence_ae_predictive (M : DPMModel X Θ) [SigmaFinite M.μ]
    (P0 : Measure X) [IsProbabilityMeasure P0] (habs : P0 ≪ M.μ) (n : ℕ) :
    latentEvidence M n =ᵐ[Measure.pi (fun _ : Fin n => P0)]
      (fun xs => ∫⁻ P : ProbabilityMeasure Θ, ∏ i : Fin n, density M P (xs i) ∂mixingPrior M) := by
  haveI := mixingPrior_prob M
  have hmeas : MeasurableSet {z : ProbabilityMeasure Θ × X |
      density M z.1 z.2 = ennDensity M z.1 z.2} :=
    measurableSet_eq_fun (density_joint_measurable M) (ennDensity_joint_measurable M)
  have hgood : ∀ᵐ x ∂M.μ, ∀ᵐ P ∂mixingPrior M,
      density M P x = ennDensity M P x :=
    (Measure.ae_ae_comm hmeas).mp (Eventually.of_forall (density_ae_eq M))
  have hdata : ∀ᵐ xs ∂Measure.pi (fun _ : Fin n => P0),
      ∀ i : Fin n, ∀ᵐ P ∂mixingPrior M, density M P (xs i) = ennDensity M P (xs i) :=
    eventually_all.mpr (fun i => (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => P0) (i := i)).eventually (habs.ae_le hgood))
  filter_upwards [hdata] with xs hxs
  rw [latentEvidence_eq_enn_predictive]
  apply lintegral_congr_ae
  filter_upwards [eventually_all.mpr hxs] with P hP
  exact Finset.prod_congr rfl (fun i _ => (hP i).symm)

lemma normalized_predictive_eq (M : DPMModel X Θ) (p0 : X → ℝ≥0∞)
    (n : ℕ) (xs : Fin n → X) (hfinite : ∀ i, p0 (xs i) ≠ ⊤) :
    (∫⁻ P : ProbabilityMeasure Θ, ∏ i : Fin n,
        density M P (xs i) * (p0 (xs i))⁻¹ ∂mixingPrior M) =
      (∫⁻ P : ProbabilityMeasure Θ, ∏ i : Fin n, density M P (xs i) ∂mixingPrior M) /
        (∏ i : Fin n, p0 (xs i)) := by
  simp_rw [Finset.prod_mul_distrib]
  rw [lintegral_mul_const]
  · rw [div_eq_mul_inv, ENNReal.prod_inv_distrib (fun i _ j _ _ => Or.inr (hfinite j))]
  · apply Finset.measurable_prod
    intro i hi
    exact (density_joint_measurable M).comp (measurable_id.prodMk measurable_const)

/-- Actual latent evidence denominator, normalized by the truth density product. -/
theorem latentEvidence_bad_probability (M : DPMModel X Θ) [SigmaFinite M.μ]
    (p0 : X → ℝ≥0∞) (hp0 : Measurable p0) (hp0_int : ∫⁻ x, p0 x ∂M.μ = 1)
    (hKL : ∀ delta : ℝ, 0 < delta → 0 < (mixingPrior M)
      {P : ProbabilityMeasure Θ | InformationTheory.klDiv (M.μ.withDensity p0)
        (M.μ.withDensity (density M P)) < ENNReal.ofReal delta})
    (delta : ℝ) (hdelta : 0 < delta) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n => M.μ.withDensity p0))
      {xs : Fin n → X | latentEvidence M n xs / (∏ i : Fin n, p0 (xs i)) <
        ENNReal.ofReal (Real.exp (-(n : ℝ) * delta))}) atTop (𝓝 0) := by
  haveI := mixingPrior_prob M
  haveI : IsProbabilityMeasure (M.μ.withDensity p0) := ⟨by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hp0_int]⟩
  have hgeneric := OfflineDPEvidence.generic_KL_bad_probability M.μ p0 hp0 hp0_int
    (mixingPrior M) (density M) (density_joint_measurable M)
    (fun P => Eventually.of_forall (fun x => ENNReal.ofReal_ne_top))
    (Eventually.of_forall (fun P => le_of_eq (density_normalized M P))) hKL delta hdelta
  convert hgeneric using 1
  funext n
  apply measure_congr
  have hfinite : ∀ᵐ x ∂M.μ.withDensity p0, p0 x ≠ ⊤ :=
    (withDensity_absolutelyContinuous M.μ p0).ae_le
      ((ae_lt_top hp0 (by rw [hp0_int]; exact ENNReal.one_ne_top)).mono (fun x hx => ne_of_lt hx))
  have hfinxs : ∀ᵐ xs ∂Measure.pi (fun _ : Fin n => M.μ.withDensity p0),
      ∀ i : Fin n, p0 (xs i) ≠ ⊤ :=
    eventually_all.mpr (fun i => (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => M.μ.withDensity p0) (i := i)).eventually hfinite)
  filter_upwards [latentEvidence_ae_predictive M (M.μ.withDensity p0)
    (withDensity_absolutelyContinuous M.μ p0) n, hfinxs] with xs hxs hfinxs
  change (_ < _) = (_ < _)
  rw [hxs, normalized_predictive_eq M p0 n xs hfinxs]

#print axioms latentEvidence_ae_predictive
#print axioms latentEvidence_bad_probability

end OfflineDPPredictive
