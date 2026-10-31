import ProverJobs.manual_dp_weakcons_repair_20261031.LatentPosterior
import ProverJobs.manual_dp_weakcons_repair_20261031.Predictive
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators
open OfflineCorrectedDP.Statlib.Imported
noncomputable section
namespace OfflineDPNativeContraction

set_option autoImplicit false in
theorem statopia_math_node_4214285044_678a16cb : ∀ (Θ : Type*) [MeasurableSpace Θ] [MetricSpace Θ] [BorelSpace Θ] [ProperSpace Θ]
    (n : ℕ),
    (∀ t : ℕ, MeasurableSet {θ : Fin n → Θ | clusterCard θ < t}) ∧

      (∀ s : ℕ, MeasurableSet {θ : Fin n → Θ | (Set.range θ).ncard ≤ s}) := by
  /- @proof-region region.target-node.session.fd5319a0481bf31d begin -/
  intro Θ _ _ _ _ n
  have hB : ∀ s : ℕ, MeasurableSet {θ : Fin n → Θ | (Set.range θ).ncard ≤ s} := by
    intro s
    have hC : ∀ σ : Fin n → Fin s,
        MeasurableSet {θ : Fin n → Θ | ∀ i j, σ i = σ j → θ i = θ j} := by
      intro σ
      have hpair : ∀ i j : Fin n, MeasurableSet {θ : Fin n → Θ | θ i = θ j} := by
        intro i j
        exact measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)
      have heqc : {θ : Fin n → Θ | ∀ i j, σ i = σ j → θ i = θ j}
          = ⋂ i : Fin n, ⋂ j : Fin n,
              (if σ i = σ j then {θ : Fin n → Θ | θ i = θ j} else Set.univ) := by
        ext θ
        simp only [Set.mem_setOf_eq, Set.mem_iInter]
        constructor
        · intro h i j
          by_cases hij : σ i = σ j
          · rw [if_pos hij]; exact h i j hij
          · rw [if_neg hij]; trivial
        · intro h i j hij
          have h' := h i j
          rw [if_pos hij] at h'
          exact h'
      rw [heqc]
      refine MeasurableSet.iInter (fun i => ?_)
      refine MeasurableSet.iInter (fun j => ?_)
      by_cases hij : σ i = σ j
      · rw [if_pos hij]; exact hpair i j
      · rw [if_neg hij]; exact MeasurableSet.univ
    have heq : {θ : Fin n → Θ | (Set.range θ).ncard ≤ s}
        = ⋃ σ ∈ (Finset.univ : Finset (Fin n → Fin s)),
            {θ : Fin n → Θ | ∀ i j, σ i = σ j → θ i = θ j} := by
      ext θ
      rw [Set.mem_setOf_eq]
      rw [show (θ ∈ ⋃ σ ∈ (Finset.univ : Finset (Fin n → Fin s)),
              {θ : Fin n → Θ | ∀ i j, σ i = σ j → θ i = θ j})
            ↔ ∃ σ : Fin n → Fin s, ∀ i j, σ i = σ j → θ i = θ j from by
          simp [Set.mem_iUnion, Set.mem_setOf_eq]]
      constructor
      · intro h
        classical
        have hSfin : (Set.range θ).Finite := Set.finite_range θ
        haveI : Fintype ↥(Set.range θ) := Set.Finite.fintype hSfin
        have hcard : (Set.range θ).ncard = Fintype.card ↥(Set.range θ) := by
          rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
        have hle : Fintype.card ↥(Set.range θ) ≤ s := by
          rw [← hcard]; exact h
        let e : ↥(Set.range θ) → Fin s :=
          fun x => Fin.castLE hle ((Fintype.equivFin ↥(Set.range θ)) x)
        have he : Function.Injective e := by
          intro a b hab
          simp only [e] at hab
          exact (Fintype.equivFin ↥(Set.range θ)).injective (Fin.castLE_injective hle hab)
        refine ⟨fun i => e ⟨θ i, Set.mem_range_self i⟩, ?_⟩
        intro i j hij
        have hh : (⟨θ i, Set.mem_range_self i⟩ : ↥(Set.range θ)) =
            ⟨θ j, Set.mem_range_self j⟩ := he hij
        simpa using congrArg Subtype.val hh
      · rintro ⟨σ, hσ⟩
        classical
        have hTfin : (Set.range σ).Finite := Set.finite_range σ
        haveI : Fintype ↥(Set.range σ) := Set.Finite.fintype hTfin
        let c : ↥(Set.range σ) → Θ := fun a => θ (Classical.choose a.2)
        have hr : Set.range θ = c '' Set.univ := by
          ext x
          constructor
          · intro hx
            rw [Set.mem_range] at hx
            obtain ⟨i, rfl⟩ := hx
            rw [Set.mem_image]
            refine ⟨⟨σ i, Set.mem_range_self i⟩, Set.mem_univ _, ?_⟩
            simp only [c]
            exact hσ _ i (Classical.choose_spec ((⟨σ i, Set.mem_range_self i⟩ : ↥(Set.range σ)).2))
          · intro hx
            simp only [Set.mem_image, Set.mem_univ, true_and] at hx
            obtain ⟨a, rfl⟩ := hx
            rw [Set.mem_range]
            exact ⟨Classical.choose a.2, rfl⟩
        have hUF : (Set.univ : Set ↥(Set.range σ)).ncard = Fintype.card ↥(Set.range σ) := by
          rw [Set.ncard_univ, Nat.card_eq_fintype_card]
        have hTcard : Fintype.card ↥(Set.range σ) ≤ s := by
          calc Fintype.card ↥(Set.range σ) ≤ Fintype.card (Fin s) :=
                Fintype.card_le_of_injective (fun a : ↥(Set.range σ) => a.1)
                  (fun a b hh => Subtype.ext hh)
            _ = s := Fintype.card_fin s
        calc (Set.range θ).ncard = (c '' Set.univ).ncard := by rw [hr]
          _ ≤ (Set.univ : Set ↥(Set.range σ)).ncard := Set.ncard_image_le
          _ = Fintype.card ↥(Set.range σ) := hUF
          _ ≤ s := hTcard
    rw [heq]
    exact Finset.measurableSet_biUnion _ (fun σ _ => hC σ)
  constructor
  · intro t
    have hAeq : {θ : Fin n → Θ | clusterCard θ < t}
        = ⋃ e ∈ Finset.range t, {θ : Fin n → Θ | (Set.range θ).ncard ≤ e} := by
      ext θ
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range, clusterCard]
      constructor
      · rintro h
        exact ⟨_, h, le_rfl⟩
      · rintro ⟨e, he, hle⟩
        exact lt_of_le_of_lt hle he
    rw [hAeq]
    exact Finset.measurableSet_biUnion _ (fun e _ => hB e)
  · exact hB
  /- @proof-region region.target-node.session.fd5319a0481bf31d end -/

variable {X Θ : Type*} [MeasurableSpace X] [MeasurableSpace Θ]

def sampleDensity (p0 : X → ℝ≥0∞) (n : ℕ) (xs : Fin n → X) : ℝ≥0∞ :=
  ∏ i, p0 (xs i)

def normalizedNumerator (M : DPMModel X Θ) (t : ℕ) (p0 : X → ℝ≥0∞)
    (n : ℕ) (xs : Fin n → X) : ℝ≥0∞ :=
  ∫⁻ θ in {θ : Fin n → Θ | clusterCard θ < t},
    dpmLikelihood M.kdens n xs θ / sampleDensity p0 n xs ∂M.priorLatent n

def normalizedEvidence (M : DPMModel X Θ) (p0 : X → ℝ≥0∞)
    (n : ℕ) (xs : Fin n → X) : ℝ≥0∞ :=
  OfflineDPPredictive.latentEvidence M n xs / sampleDensity p0 n xs

lemma likelihood_measurable (M : DPMModel X Θ) (n : ℕ) :
    Measurable (Function.uncurry (fun (xs : Fin n → X) (θ : Fin n → Θ) =>
      dpmLikelihood M.kdens n xs θ)) := by
  change Measurable (fun z : (Fin n → X) × (Fin n → Θ) =>
    ∏ i : Fin n, ENNReal.ofReal (M.kdens (z.2 i) (z.1 i)))
  apply Finset.measurable_prod
  intro i _
  have hmtheta : Measurable (fun z : (Fin n → X) × (Fin n → Θ) => z.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  have hmx : Measurable (fun z : (Fin n → X) × (Fin n → Θ) => z.1 i) :=
    (measurable_pi_apply i).comp measurable_fst
  exact ENNReal.measurable_ofReal.comp (M.hk_meas.comp (hmtheta.prodMk hmx))

lemma sampleDensity_measurable (p0 : X → ℝ≥0∞) (hp0 : Measurable p0) (n : ℕ) :
    Measurable (sampleDensity p0 n) :=
  Finset.measurable_prod _ (fun i _ => hp0.comp (measurable_pi_apply i))

lemma normalizedNumerator_measurable (M : DPMModel X Θ) (t : ℕ)
    (p0 : X → ℝ≥0∞) (hp0 : Measurable p0) (n : ℕ) :
    Measurable (normalizedNumerator M t p0 n) := by
  haveI := M.priorLatent_prob n
  exact ((likelihood_measurable M n).div
    ((sampleDensity_measurable p0 hp0 n).comp measurable_fst)).lintegral_prod_right

lemma sampleDensity_ae_ne_zero (μ : Measure X) (p0 : X → ℝ≥0∞)
    (hp0 : Measurable p0) (hp0_int : ∫⁻ x, p0 x ∂μ = 1) (n : ℕ) :
    ∀ᵐ xs ∂Measure.pi (fun _ : Fin n => μ.withDensity p0), sampleDensity p0 n xs ≠ 0 := by
  haveI : IsProbabilityMeasure (μ.withDensity p0) := ⟨by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hp0_int]⟩
  have hp : ∀ᵐ x ∂μ.withDensity p0, p0 x ≠ 0 := by
    rw [ae_withDensity_iff hp0]
    exact Filter.Eventually.of_forall (fun x hx => hx)
  have hcoords : ∀ᵐ xs ∂Measure.pi (fun _ : Fin n => μ.withDensity p0),
      ∀ i : Fin n, p0 (xs i) ≠ 0 :=
    eventually_all.mpr (fun i => (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin n => μ.withDensity p0) (i := i)).eventually hp)
  filter_upwards [hcoords] with xs hxs
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => hxs i)

lemma normalized_bayes_ae (M : DPMModel X Θ) (t : ℕ)
    (p0 : X → ℝ≥0∞) (hp0 : Measurable p0) (hp0_int : ∫⁻ x, p0 x ∂M.μ = 1) (hp0_finite : ∀ x, p0 x ≠ ∞)
    [MetricSpace Θ] [BorelSpace Θ] [ProperSpace Θ] (n : ℕ) :
    ∀ᵐ xs ∂Measure.pi (fun _ : Fin n => M.μ.withDensity p0),
      underPi M t n xs = normalizedNumerator M t p0 n xs / normalizedEvidence M p0 n xs := by
  have hB := (statopia_math_node_4214285044_678a16cb Θ n).1 t
  filter_upwards [sampleDensity_ae_ne_zero M.μ p0 hp0 hp0_int n] with xs hxs
  rw [underPi, M.posterior_bayes n xs _ hB]
  have hLm : Measurable (fun θ : Fin n → Θ => dpmLikelihood M.kdens n xs θ) :=
    (likelihood_measurable M n).comp (measurable_const.prodMk measurable_id)
  have hNorm : normalizedNumerator M t p0 n xs =
      (∫⁻ θ in {θ : Fin n → Θ | clusterCard θ < t},
        dpmLikelihood M.kdens n xs θ ∂M.priorLatent n) / sampleDensity p0 n xs := by
    simp only [normalizedNumerator, div_eq_mul_inv]
    rw [lintegral_mul_const _ hLm]
  rw [hNorm, normalizedEvidence,
    OfflineDPContraction.normalized_bayes_quotient _ _ _ hxs
      (ENNReal.prod_ne_top (fun i _ => hp0_finite (xs i)))]
  rfl


/-- Actual latent Bayes contraction once tests and the separately proved evidence
estimate have been supplied. Both arguments are intermediate obligations. -/
theorem underPi_converges_from_tests_and_evidence
    (M : DPMModel X Θ) (t : ℕ)
    [MetricSpace X] [BorelSpace X] [MeasureSpace X] [CompleteSpace X]
    [SecondCountableTopology X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
    [MetricSpace Θ] [BorelSpace Θ] [StandardBorelSpace Θ] [ProperSpace Θ]
    (p0 : X → ℝ≥0∞) (hp0 : Measurable p0)
    (hp0_int : ∫⁻ x, p0 x ∂M.μ = 1) (hp0_finite : ∀ x, p0 x ≠ ∞)
    (hTesting : OfflineCorrectedDP.OfflineDPConsumer.FullLatentTestingTarget M t
      (M.μ.withDensity p0))
    (hEvidence : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n => (Measure.pi (fun _ : Fin n => M.μ.withDensity p0))
        {xs | normalizedEvidence M p0 n xs <
          ENNReal.ofReal (Real.exp (-(n : ℝ) * δ))}) atTop (𝓝 0)) :
    ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun n =>
      (Measure.pi (fun _ : Fin n => M.μ.withDensity p0))
        {xs | ε < underPi M t n xs}) atTop (𝓝 0) := by
  obtain ⟨c, hc, T, hTm, hTypeI, hTypeII⟩ := hTesting
  have hExp : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (-(n : ℝ) * c)))
      atTop (𝓝 0) := by
    have hReal : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ) * c)) atTop (𝓝 0) := by
      have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
        (le_of_lt (Real.exp_pos (-c))) (Real.exp_lt_one_iff.mpr (by linarith : -c < 0))
      convert hpow using 1
      funext n
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    simpa using (ENNReal.continuous_ofReal.tendsto 0).comp hReal
  have hTest : Tendsto (fun n =>
      (Measure.pi (fun _ : Fin n => M.μ.withDensity p0)) (T n)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hExp
      (Filter.Eventually.of_forall (fun n => zero_le _))
    simpa only [neg_mul] using hTypeI
  have hSmall : ∀ᶠ n in atTop,
      ∫⁻ xs in (T n)ᶜ, normalizedNumerator M t p0 n xs
        ∂Measure.pi (fun _ : Fin n => M.μ.withDensity p0) ≤
          ENNReal.ofReal (Real.exp (-(n : ℝ) * c)) := by
    filter_upwards [hTypeII] with n hn
    haveI := M.priorLatent_prob n
    have hkint : ∀ θ, ∫⁻ x, ENNReal.ofReal (M.kdens θ x) ∂M.μ = 1 := by
      intro θ
      have h := (M.kdens_prob θ).measure_univ
      simpa only [kernelMeasure, withDensity_apply _ MeasurableSet.univ,
        Measure.restrict_univ] using h
    exact OfflineDPLatentPosterior.integrated_test_bound M.μ M.kdens M.hk_meas hkint
      p0 hp0 hp0_int hp0_finite n (M.priorLatent n)
      {θ | clusterCard θ < t} ((statopia_math_node_4214285044_678a16cb Θ n).1 t)
      (T n) (hTm n) _ (by simpa only [DPMModel.kernel, neg_mul] using hn)
  exact OfflineDPContraction.posterior_tendsto_zero
    (fun n => Measure.pi (fun _ : Fin n => M.μ.withDensity p0))
    (fun n => underPi M t n) (normalizedNumerator M t p0) (normalizedEvidence M p0)
    T hTm (fun n => (normalizedNumerator_measurable M t p0 hp0 n).aemeasurable)
    (normalized_bayes_ae M t p0 hp0 hp0_int hp0_finite) c hc hTest
    (hEvidence (c / 2) (by linarith)) hSmall

end OfflineDPNativeContraction
