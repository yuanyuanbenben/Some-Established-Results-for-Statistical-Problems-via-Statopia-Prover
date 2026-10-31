import Statlib.StatFoundation.Concentration.ExponentialType.hoeffding_mgf_le
import Statlib.StatFoundation.Concentration.ExponentialType.hoeffding_sum_meas_abs_ge_le_two_exp
import ProverJobs.manual_dp_weakcons_repair_20261031.BoxedWeakCons.CorrectedConsumerBundle
import Lean

/- Genuine source ProverJobs.job_paper_80f79a059f3741e883a5b36dc8747f99.ProvedNodes.Node_2986921194_82fe1497_a11eef21; only namespace isolation. -/

namespace OfflineCorrectedDP

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.OfflineCorrectedDP.Statlib.Imported
open _root_.OfflineCorrectedDP.Statlib.Imported.DPMModel

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
variable {X Θ : Type*} [MeasurableSpace X] [MeasurableSpace Θ]
variable [MetricSpace X] [BorelSpace X] [MeasureSpace X] [CompleteSpace X]
  [SecondCountableTopology X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
  [MetricSpace Θ] [BorelSpace Θ] [StandardBorelSpace Θ] [ProperSpace Θ]

set_option autoImplicit false in
theorem statopia_math_node_2986921194_82fe1497 : ∀ {X Θ : Type*} [MeasurableSpace X] [MeasurableSpace Θ]
    (M : DPMModel X Θ) (s : ℕ) (hs : 1 ≤ s)
    (q : Fin s → ℝ) (theta : Fin s → Θ)
    (hq_pos : ∀ j : Fin s, 0 < q j)
    (hq_sum : ∑ j : Fin s, q j = 1)
    (hk_prob : ∀ j : Fin s, IsProbabilityMeasure (M.kernel (theta j))),
    (mixtureMeasure M q theta
        = M.μ.withDensity (fun x : X => ENNReal.ofReal (mixDens M q theta x))) ∧
      IsProbabilityMeasure (mixtureMeasure M q theta) ∧
      (Function.Injective theta →
        ((∀ j : Fin s, 0 < q j) ∧ (∑ j : Fin s, q j = 1) ∧
          (∀ i j : Fin s, i ≠ j → theta i ≠ theta j)) ∧
          mixDens M q theta ∈ Gset M s) := by
  /- @proof-region region.target-node.session.96d65505966e4659 begin -/
  intro X Θ _ _ M s hs q θ hqpos hqsum hKprob
  have hkmeas : ∀ j : Fin s, Measurable (fun x : X => M.kdens (θ j) x) := by
    intro j
    have hpair : Measurable (fun x : X => (θ j, x)) :=
      Measurable.prodMk (f := fun _ : X => θ j) (g := fun x : X => x)
        measurable_const measurable_id
    exact M.hk_meas.comp hpair
  have hmeas : ∀ j : Fin s, Measurable (fun x : X => ENNReal.ofReal (M.kdens (θ j) x)) :=
    fun j => ENNReal.measurable_ofReal.comp (hkmeas j)
  have hFmeas : ∀ j : Fin s,
      Measurable (fun x : X => ENNReal.ofReal (q j) * ENNReal.ofReal (M.kdens (θ j) x)) :=
    fun j => Measurable.const_mul (hmeas j) (ENNReal.ofReal (q j))
  have hzero : M.μ.withDensity (0 : X → ℝ≥0∞) = 0 := by
    refine Measure.ext (fun t ht => ?_)
    rw [MeasureTheory.withDensity_apply _ ht]
    simp
  have hsum : ∀ t : Finset (Fin s),
      (∑ j ∈ t, M.μ.withDensity
          (fun x : X => ENNReal.ofReal (q j) * ENNReal.ofReal (M.kdens (θ j) x)))
        = M.μ.withDensity
          (fun x : X => ∑ j ∈ t, ENNReal.ofReal (q j) * ENNReal.ofReal (M.kdens (θ j) x)) := by
    intro t
    refine Finset.induction (motive := fun u : Finset (Fin s) =>
      (∑ j ∈ u, M.μ.withDensity
          (fun x : X => ENNReal.ofReal (q j) * ENNReal.ofReal (M.kdens (θ j) x)))
        = M.μ.withDensity
          (fun x : X => ∑ j ∈ u, ENNReal.ofReal (q j) * ENNReal.ofReal (M.kdens (θ j) x)))
      ?_ ?_ t
    · simpa only [Finset.sum_empty] using hzero.symm
    · intro a u ha ih
      have hfun : (fun x : X => ∑ j ∈ insert a u,
            ENNReal.ofReal (q j) * ENNReal.ofReal (M.kdens (θ j) x))
          = (fun x : X => ENNReal.ofReal (q a) * ENNReal.ofReal (M.kdens (θ a) x))
            + (fun x : X => ∑ j ∈ u,
                ENNReal.ofReal (q j) * ENNReal.ofReal (M.kdens (θ j) x)) := by
        funext x
        show (∑ j ∈ insert a u, ENNReal.ofReal (q j) * ENNReal.ofReal (M.kdens (θ j) x))
            = ENNReal.ofReal (q a) * ENNReal.ofReal (M.kdens (θ a) x)
              + ∑ j ∈ u, ENNReal.ofReal (q j) * ENNReal.ofReal (M.kdens (θ j) x)
        rw [Finset.sum_insert ha]
      rw [Finset.sum_insert ha, hfun,
        MeasureTheory.withDensity_add_left (f := fun x : X =>
          ENNReal.ofReal (q a) * ENNReal.ofReal (M.kdens (θ a) x)) (hFmeas a), ih]
  have hsum_apply : ∀ (t : Finset (Fin s)) (g : Fin s → Measure X),
      (∑ j ∈ t, g j) Set.univ = ∑ j ∈ t, g j Set.univ := by
    intro t g
    refine Finset.induction (motive := fun u : Finset (Fin s) =>
      (∑ j ∈ u, g j) Set.univ = ∑ j ∈ u, g j Set.univ) ?_ ?_ t
    · simp
    · intro a u ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
      simp
  have hA : mixtureMeasure M q θ =
      M.μ.withDensity (fun x : X => ENNReal.ofReal (mixDens M q θ x)) := by
    have step1 : mixtureMeasure M q θ =
        ∑ j : Fin s,
          M.μ.withDensity
            (fun x : X => ENNReal.ofReal (q j) * ENNReal.ofReal (M.kdens (θ j) x)) := by
      simp only [mixtureMeasure, kernel, kernelMeasure]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have hsm : (ENNReal.ofReal (q j) • (fun x : X => ENNReal.ofReal (M.kdens (θ j) x)))
          = (fun x : X => ENNReal.ofReal (q j) * ENNReal.ofReal (M.kdens (θ j) x)) := by
        funext x
        first
          | rfl
          | simp
      rw [← hsm]
      exact (MeasureTheory.withDensity_smul' (ENNReal.ofReal (q j))
        (fun x : X => ENNReal.ofReal (M.kdens (θ j) x)) ENNReal.ofReal_ne_top).symm
    have step2 : (∑ j : Fin s,
          M.μ.withDensity
            (fun x : X => ENNReal.ofReal (q j) * ENNReal.ofReal (M.kdens (θ j) x))) =
        M.μ.withDensity (fun x : X =>
          ∑ j ∈ Finset.univ, ENNReal.ofReal (q j) * ENNReal.ofReal (M.kdens (θ j) x)) :=
      hsum Finset.univ
    have step3 : (fun x : X =>
          ∑ j ∈ Finset.univ, ENNReal.ofReal (q j) * ENNReal.ofReal (M.kdens (θ j) x)) =
        fun x : X => ENNReal.ofReal (mixDens M q θ x) := by
      funext x
      simp only [mixDens]
      rw [ENNReal.ofReal_sum_of_nonneg
        (s := Finset.univ)
        (f := fun j : Fin s => q j * M.kdens (θ j) x)
        (fun j _ => mul_nonneg (le_of_lt (hqpos j)) (M.kdens_nonneg (θ j) x))]
      exact Finset.sum_congr rfl (fun j _ => (ENNReal.ofReal_mul (le_of_lt (hqpos j))).symm)
    rw [step1, step2, step3]
  have hB : IsProbabilityMeasure (mixtureMeasure M q θ) := by
    refine ⟨?_⟩
    have h1 : (mixtureMeasure M q θ) Set.univ = ∑ j : Fin s, ENNReal.ofReal (q j) := by
      rw [mixtureMeasure, hsum_apply]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Measure.smul_apply, (hKprob j).measure_univ]
      simp
    rw [h1, ← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ) (f := q)
      (fun j _ => le_of_lt (hqpos j)), hqsum]
    simp
  refine ⟨hA, hB, ?_⟩
  intro hinj
  refine ⟨⟨hqpos, hqsum, fun i j hij h => hij (hinj h)⟩, ?_⟩
  exact ⟨q, θ, hqpos, hqsum, fun i j hij h => hij (hinj h), rfl⟩
  /- @proof-region region.target-node.session.96d65505966e4659 end -/

end Statlib.Imported


end OfflineCorrectedDP

/- Genuine source ProverJobs.manual_dp_weakcons_repair_20261031.FullLatentTesting; only namespace isolation. -/

namespace OfflineCorrectedDP

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal MeasureTheory Topology BigOperators
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.OfflineCorrectedDP.Statlib.Imported

noncomputable section
namespace OfflineDPTesting
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `OfflineDPTesting then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.OfflineDPTesting))

/-- Source primitive copies below depend only on generic measure theory.
They are kept in this namespace to avoid loading a second incompatible model Base. -/
def kernelMixDensity {Θ X : Type*} (k : Θ → X → ℝ) {s : ℕ}
    (q : Fin s → ℝ) (θs : Fin s → Θ) : X → ℝ :=
  fun x => ∑ j : Fin s, q j * k (θs j) x

def IsKernelMixture {Θ X : Type*} [MeasurableSpace X] (μ : Measure X) (k : Θ → X → ℝ)
    {s : ℕ} (q : Fin s → ℝ) (θs : Fin s → Θ) (P : Measure X) : Prop :=
  (∀ j : Fin s, 0 < q j) ∧ (∑ j : Fin s, q j = 1) ∧ Function.Injective θs ∧
    P = μ.withDensity (fun x => ENNReal.ofReal (kernelMixDensity k q θs x))

def KernelGSet {Θ X : Type*} [MeasurableSpace X] (μ : Measure X) (k : Θ → X → ℝ) (s : ℕ) :
    Set (ProbabilityMeasure X) :=
  {P | ∃ (q : Fin s → ℝ) (θs : Fin s → Θ), IsKernelMixture μ k q θs P.toMeasure}

set_option autoImplicit false in
theorem statopia_math_node_2358127001_21193b79 : ∀ (n : ℕ) (hn : 0 < n) (M : ℝ) (hM : 0 < M)
    (Ω : Fin n → Type*) [∀ i, MeasurableSpace (Ω i)]
    (μ : (i : Fin n) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (Y : (i : Fin n) → Ω i → ℝ) (hY : ∀ i, Measurable (Y i))
    (hYb : ∀ (i : Fin n) (ω : Ω i), |Y i ω| ≤ M)
    (t : ℝ) (ht : 0 < t),
    Measure.pi μ {ω : (i : Fin n) → Ω i |
        t ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, Y i (ω i)) -
             (n : ℝ)⁻¹ * (∑ i : Fin n, ∫ x, Y i x ∂(μ i))|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * t ^ 2 / (2 * M ^ 2))) := by
  /- @proof-region region.target-node.session.b6a4f8f479c52f18 begin -/
  intro n hn M hM Ω _ μ _ Y hY hYb t ht
  classical
  haveI : IsProbabilityMeasure (Measure.pi μ) := inferInstance
  set m : Fin n → ℝ := fun i => ∫ x, Y i x ∂μ i with hm
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hnt : (0 : ℝ) < (n : ℝ) * t := mul_pos hnpos ht
  have hmeas : ∀ i, Measurable (fun ω : (i : Fin n) → Ω i => Y i (ω i) - m i) := by
    intro i
    exact ((hY i).comp (measurable_pi_apply i)).sub
      (measurable_const : Measurable fun _ : (i : Fin n) → Ω i => m i)
  have hintY : ∀ i, Integrable (Y i) (μ i) := by
    intro i
    refine Integrable.of_bound (hY i).aestronglyMeasurable M ?_
    filter_upwards with x
    simpa [Real.norm_eq_abs] using hYb i x
  have hmabs : ∀ i, |m i| ≤ M := by
    intro i
    have hle : ∫ x, Y i x ∂μ i ≤ M := by
      have h := integral_mono_ae (hintY i) (integrable_const M)
        (Eventually.of_forall (fun x => (abs_le.mp (hYb i x)).2))
      simpa using h
    have hge : -M ≤ ∫ x, Y i x ∂μ i := by
      have h := integral_mono_ae (integrable_const (-M)) (hintY i)
        (Eventually.of_forall (fun x => (abs_le.mp (hYb i x)).1))
      simpa using h
    have hmval : m i = ∫ x, Y i x ∂μ i := by rw [hm]
    rw [hmval, abs_le]
    exact ⟨hge, hle⟩
  have hintPi : ∀ i, Integrable (fun x : (j : Fin n) → Ω j => Y i (x i)) (Measure.pi μ) := by
    intro i
    refine Integrable.of_bound ((hY i).comp (measurable_pi_apply i)).aestronglyMeasurable M ?_
    filter_upwards with x
    simpa [Real.norm_eq_abs] using hYb i (x i)
  have hmean : ∀ i, ∫ ω : (i : Fin n) → Ω i, (Y i (ω i) - m i) ∂(Measure.pi μ) = 0 := by
    intro i
    have hmap : Measure.map (Function.eval i) (Measure.pi μ) = μ i := by
      rw [Measure.pi_map_eval]
      simp
    have hcomp : ∫ ω : (i : Fin n) → Ω i, Y i (ω i) ∂(Measure.pi μ) = m i := by
      have hi : ∫ y, Y i y ∂(Measure.map (Function.eval i) (Measure.pi μ)) =
          ∫ x, Y i (Function.eval i x) ∂(Measure.pi μ) :=
        integral_map (measurable_pi_apply i).aemeasurable (hY i).aestronglyMeasurable
      rw [hmap] at hi
      rw [hm]
      exact hi.symm
    calc ∫ ω : (i : Fin n) → Ω i, (Y i (ω i) - m i) ∂(Measure.pi μ)
        = (∫ ω : (i : Fin n) → Ω i, Y i (ω i) ∂(Measure.pi μ)) -
            ∫ ω : (i : Fin n) → Ω i, m i ∂(Measure.pi μ) :=
          integral_sub (hintPi i) (integrable_const (m i))
      _ = m i - m i := by rw [hcomp]; simp
      _ = 0 := by ring
  have hindep : iIndepFun (fun i (x : (j : Fin n) → Ω j) => Y i (x i) - m i) (Measure.pi μ) := by
    unfold iIndepFun
    exact iIndepFun_pi
      (fun i => ((hY i).sub (measurable_const : Measurable fun _ : Ω i => m i)).aemeasurable)
  have hsub : ∀ i, HasSubgaussianMGF (fun x : (i : Fin n) → Ω i => Y i (x i) - m i)
      ⟨M ^ 2, sq_nonneg M⟩ (Measure.pi μ) := by
    intro i
    refine Statlib.StatFoundation.Concentration.ExponentialType.hoeffding_mgf_le (Measure.pi μ)
      (fun x : (i : Fin n) → Ω i => Y i (x i) - m i) (hmeas i) (-M - m i) (M - m i) ?_ (hmean i)
      ⟨M ^ 2, sq_nonneg M⟩ ?_
    · filter_upwards with x
      have h1 := abs_le.mp (hYb i (x i))
      have h2 := abs_le.mp (hmabs i)
      constructor <;> linarith
    · have hd : M - m i - (-M - m i) = 2 * M := by ring
      rw [hd]
      push_cast
      ring
  have hstep := Statlib.StatFoundation.Concentration.ExponentialType.hoeffding_sum_meas_abs_ge_le_two_exp
    (Measure.pi μ) n (fun i (x : (i : Fin n) → Ω i) => Y i (x i) - m i) (fun _ => M)
    (fun _ => ⟨M ^ 2, sq_nonneg M⟩) (fun i => rfl) hindep hsub ((n : ℝ) * t) hnt
  have hset : {ω : (i : Fin n) → Ω i |
        t ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, Y i (ω i)) -
             (n : ℝ)⁻¹ * (∑ i : Fin n, ∫ x, Y i x ∂μ i)|} ⊆
      {ω : (i : Fin n) → Ω i | (n : ℝ) * t ≤ |∑ i : Fin n, (Y i (ω i) - m i)|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have hsumsub : ∑ i : Fin n, (Y i (ω i) - m i) =
        (∑ i : Fin n, Y i (ω i)) - (∑ i : Fin n, m i) :=
      Finset.sum_sub_distrib (s := Finset.univ) (f := fun i => Y i (ω i)) (g := fun i => m i)
    have hmval : (∑ i : Fin n, m i) = (∑ i : Fin n, ∫ x, Y i x ∂μ i) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [hm]
    rw [hsumsub, hmval]
    have hfac : (n : ℝ)⁻¹ * (∑ i : Fin n, Y i (ω i)) -
          (n : ℝ)⁻¹ * (∑ i : Fin n, ∫ x, Y i x ∂μ i) =
        (n : ℝ)⁻¹ * ((∑ i : Fin n, Y i (ω i)) - (∑ i : Fin n, ∫ x, Y i x ∂μ i)) := by ring
    rw [hfac] at hω
    have habs : |(n : ℝ)⁻¹ * ((∑ i : Fin n, Y i (ω i)) -
          (∑ i : Fin n, ∫ x, Y i x ∂μ i))| =
        (n : ℝ)⁻¹ * |(∑ i : Fin n, Y i (ω i)) - (∑ i : Fin n, ∫ x, Y i x ∂μ i)| := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr hnpos)]
    rw [habs] at hω
    have hmul := mul_le_mul_of_nonneg_left hω (le_of_lt hnpos)
    rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hnpos), one_mul] at hmul
  refine le_trans (measure_mono hset) ?_
  refine le_trans hstep ?_
  have hsum : ∑ i : Fin n, M ^ 2 = (n : ℝ) * M ^ 2 := by
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcalc : -((n : ℝ) * t) ^ 2 / (2 * ((n : ℝ) * M ^ 2)) =
      -(n : ℝ) * t ^ 2 / (2 * M ^ 2) := by
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have hM0 : M ≠ 0 := ne_of_gt hM
    field_simp
  rw [hsum, hcalc]
  /- @proof-region region.target-node.session.b6a4f8f479c52f18 end -/

set_option autoImplicit false in
theorem statopia_math_node_2781295325_3f1c8bad : ∀ {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    (P : Measure X) [IsProbabilityMeasure P]
    (r : ℕ) (hr : 1 ≤ r)
    (ψ : Fin r → X → ℝ) (hψ_cont : ∀ j : Fin r, Continuous (ψ j))
    (M : ℝ) (hM : 0 < M)
    (hM_def : M = ⨆ j : Fin r, ⨆ x : X, |ψ j x|)
    (hψ_bound : ∀ (j : Fin r) (x : X), |ψ j x| ≤ M)
    (ε : ℝ) (hε : 0 < ε),
    (∀ (n : ℕ) (hn : 0 < n),
      Measure.pi (fun _ : Fin n => P)
        {x : Fin n → X |
          ε / 2 ≤ ⨆ j : Fin r,
            |(n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x' : X, ψ j x' ∂P|}
        ≤ ENNReal.ofReal (2 * (r : ℝ) * Real.exp (-(n : ℝ) * (ε ^ 2 / (8 * M ^ 2)))))
    ∧
    (∀ (n : ℕ) (hn : 0 < n) (ν : Fin n → Measure X)
        (hν : ∀ i : Fin n, IsProbabilityMeasure (ν i)),
      (∃ j : Fin r,
        ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, ∫ x' : X, ψ j x' ∂(ν i))
              - ∫ x' : X, ψ j x' ∂P|) →
      Measure.pi ν
        {x : Fin n → X |
          ⨆ j : Fin r,
            |(n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x' : X, ψ j x' ∂P| < ε / 2}
        ≤ ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * (ε ^ 2 / (8 * M ^ 2))))) := by
  /- @proof-region region.target-node.session.976874c3f5b5e3ff begin -/
  intro X _ _ _ P _ r hr ψ hψ M hM hM_def hψ_bound ε hε
  have hexp : ∀ n : ℕ, -(n : ℝ) * (ε / 2) ^ 2 / (2 * M ^ 2) = -(n : ℝ) * (ε ^ 2 / (8 * M ^ 2)) := by
    intro n
    have hkey : (ε / 2) ^ 2 / (2 * M ^ 2) = ε ^ 2 / (8 * M ^ 2) := by
      have h1 : (2 * M ^ 2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
      have h2 : (8 * M ^ 2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
      rw [div_eq_div_iff h1 h2]
      ring
    calc -(n : ℝ) * (ε / 2) ^ 2 / (2 * M ^ 2)
        = -(n : ℝ) * ((ε / 2) ^ 2 / (2 * M ^ 2)) := by rw [mul_div_assoc]
      _ = -(n : ℝ) * (ε ^ 2 / (8 * M ^ 2)) := by rw [hkey]
  have hmean : ∀ (n : ℕ) (_ : 0 < n) (j : Fin r),
      (n : ℝ)⁻¹ * (∑ i : Fin n, (∫ x, ψ j x ∂P)) = ∫ y, ψ j y ∂P := by
    intro n hn j
    have hn0 : (n : ℝ) ≠ 0 := by
      have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      exact ne_of_gt hpos
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hn0, one_mul]
  have ht : (0 : ℝ) < ε / 2 := by linarith
  constructor
  · intro n hn
    haveI : ∀ i : Fin n, IsProbabilityMeasure ((fun _ : Fin n => P) i) := fun i => inferInstance
    have hkey : ∀ j : Fin r, Measure.pi (fun _ : Fin n => P) {x : Fin n → X | ε / 2 ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x' : X, ψ j x' ∂P|} ≤ ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * (ε ^ 2 / (8 * M ^ 2)))) := by
      intro j
      have h := statopia_math_node_2358127001_21193b79 n hn M hM (fun _ : Fin n => X) (fun _ => P) (fun _ => ψ j) (fun i => (hψ j).measurable) (fun i ω => hψ_bound j ω) (ε / 2) ht
      rw [hmean n hn j, hexp n] at h
      exact h
    have hsub : {x : Fin n → X | ε / 2 ≤ ⨆ j : Fin r, |(n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x' : X, ψ j x' ∂P|} ⊆ ⋃ j : Fin r, {x : Fin n → X | ε / 2 ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x' : X, ψ j x' ∂P|} := by
      intro x hx
      simp only [Set.mem_setOf_eq] at hx
      haveI : Nonempty (Fin r) := ⟨⟨0, lt_of_lt_of_le Nat.zero_lt_one hr⟩⟩
      have hne : (Finset.univ : Finset (Fin r)).Nonempty := ⟨⟨0, lt_of_lt_of_le Nat.zero_lt_one hr⟩, Finset.mem_univ _⟩
      rw [← Finset.sup'_univ_eq_ciSup (fun j : Fin r => |(n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x' : X, ψ j x' ∂P|)] at hx
      obtain ⟨j, -, hj⟩ := (Finset.le_sup'_iff hne).mp hx
      simp only [Set.mem_iUnion]
      exact ⟨j, hj⟩
    have hunion : Measure.pi (fun _ : Fin n => P) (⋃ j : Fin r, {x : Fin n → X | ε / 2 ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x' : X, ψ j x' ∂P|}) ≤ ∑ j : Fin r, Measure.pi (fun _ : Fin n => P) {x : Fin n → X | ε / 2 ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x' : X, ψ j x' ∂P|} := by
      have hle := measure_biUnion_finset_le (μ := Measure.pi (fun _ : Fin n => P)) (Finset.univ : Finset (Fin r)) (fun j => {x : Fin n → X | ε / 2 ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x' : X, ψ j x' ∂P|})
      simpa using hle
    have hsum : (∑ j : Fin r, ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * (ε ^ 2 / (8 * M ^ 2))))) = ENNReal.ofReal (2 * (r : ℝ) * Real.exp (-(n : ℝ) * (ε ^ 2 / (8 * M ^ 2)))) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    calc Measure.pi (fun _ : Fin n => P) {x : Fin n → X | ε / 2 ≤ ⨆ j : Fin r, |(n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x' : X, ψ j x' ∂P|}
        ≤ Measure.pi (fun _ : Fin n => P) (⋃ j : Fin r, {x : Fin n → X | ε / 2 ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x' : X, ψ j x' ∂P|}) := measure_mono hsub
      _ ≤ ∑ j : Fin r, Measure.pi (fun _ : Fin n => P) {x : Fin n → X | ε / 2 ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x' : X, ψ j x' ∂P|} := hunion
      _ ≤ ∑ j : Fin r, ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * (ε ^ 2 / (8 * M ^ 2)))) := Finset.sum_le_sum (fun j _ => hkey j)
      _ = ENNReal.ofReal (2 * (r : ℝ) * Real.exp (-(n : ℝ) * (ε ^ 2 / (8 * M ^ 2)))) := hsum
  · intro n hn ν hν h
    haveI : ∀ i : Fin n, IsProbabilityMeasure (ν i) := hν
    rcases h with ⟨j, hj⟩
    have hhoef := statopia_math_node_2358127001_21193b79 n hn M hM (fun _ : Fin n => X)
      ν (fun _ => ψ j) (fun i => (hψ j).measurable) (fun i ω => hψ_bound j ω) (ε / 2) ht
    rw [hexp n] at hhoef
    refine le_trans (measure_mono ?_) hhoef
    intro x hx
    have hsup_lt : ⨆ j : Fin r, |(n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x' : X, ψ j x' ∂P| < ε / 2 := by
      simpa only [Set.mem_setOf_eq] using hx
    have hbdd : BddAbove (Set.range (fun j : Fin r => |(n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x' : X, ψ j x' ∂P|)) :=
      Finite.bddAbove_range _
    have hgj : |(n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x' : X, ψ j x' ∂P| < ε / 2 :=
      lt_of_le_of_lt (le_ciSup (f := fun j : Fin r => |(n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x' : X, ψ j x' ∂P|) hbdd j) hsup_lt
    have htri : |(n : ℝ)⁻¹ * (∑ i : Fin n, (∫ x', ψ j x' ∂(ν i))) - ∫ x', ψ j x' ∂P|
        ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, (∫ x', ψ j x' ∂(ν i))) - (n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i))|
          + |(n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x', ψ j x' ∂P| := by
      have h := abs_add_le
        ((n : ℝ)⁻¹ * (∑ i : Fin n, (∫ x', ψ j x' ∂(ν i))) - (n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)))
        ((n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x', ψ j x' ∂P)
      rwa [show
        ((n : ℝ)⁻¹ * (∑ i : Fin n, (∫ x', ψ j x' ∂(ν i))) - (n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)))
          + ((n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x', ψ j x' ∂P)
          = (n : ℝ)⁻¹ * (∑ i : Fin n, (∫ x', ψ j x' ∂(ν i))) - ∫ x', ψ j x' ∂P by ring] at h
    have hge : |(n : ℝ)⁻¹ * (∑ i : Fin n, (∫ x', ψ j x' ∂(ν i))) - (n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i))| ≥ ε / 2 := by
      linarith [htri, hj, hgj]
    simp only [Set.mem_setOf_eq]
    rw [abs_sub_comm]
    exact hge
  /- @proof-region region.target-node.session.976874c3f5b5e3ff end -/

set_option autoImplicit false in
theorem statopia_math_node_3257560511_130c2ed0 : ∀ {Θ X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Θ]
    (μ : Measure X)
    (k : Θ → X → ℝ) (hk_nonneg : ∀ (θ : Θ) (x : X), 0 ≤ k θ x)
    (hk_meas : Measurable (Function.uncurry k))
    (hk_int : ∀ θ : Θ, ∫⁻ x, ENNReal.ofReal (k θ x) ∂μ = 1)
    (P : ProbabilityMeasure X)
    (U : Set (ProbabilityMeasure X)) (hU : U ∈ 𝓝 P)
    (t : ℕ) (ht : 2 ≤ t)
    (theta0 : Θ)
    (hsep : ∀ s : ℕ, 1 ≤ s → s < t → U ∩ KernelGSet μ k s = ∅),
    ∃ (r : ℕ) (ψ : Fin r → BoundedContinuousFunction X ℝ) (ε M c : ℝ),
      1 ≤ r ∧ 0 < ε ∧
      M = (⨆ j : Fin r, ⨆ x : X, |(ψ j : X → ℝ) x|) ∧
      0 < M ∧
      c = ε ^ 2 / (8 * M ^ 2) ∧ 0 < c ∧
      (∀ Q : ProbabilityMeasure X,
        (∀ j : Fin r,
          |∫ x, (ψ j : X → ℝ) x ∂Q.toMeasure
            - ∫ x, (ψ j : X → ℝ) x ∂P.toMeasure| < ε) → Q ∈ U) ∧
      (∀ (s : ℕ), 1 ≤ s → s < t → ∀ Q : ProbabilityMeasure X,
        Q ∈ KernelGSet μ k s →
          ¬ (∀ j : Fin r,
            |∫ x, (ψ j : X → ℝ) x ∂Q.toMeasure
              - ∫ x, (ψ j : X → ℝ) x ∂P.toMeasure| < ε)) := by
  /- @proof-region region.target-node.session.64d9ae89f20dd9d5 begin -/
  intro Θ X _ _ _ _ μ k hk_nonneg hk_meas hk_int P U hU t ht theta0 hsep
  classical
  haveI hXne : Nonempty X := by
    rcases isEmpty_or_nonempty X with hX | hX
    · exfalso
      haveI := hX
      have h0 : (P : Measure X) Set.univ = 1 := measure_univ
      have h2 : (Set.univ : Set X) = ∅ := Set.univ_eq_empty_iff.mpr hX
      rw [h2, measure_empty] at h0
      exact zero_ne_one h0
    · exact hX
  have hchar : ∀ F : Filter (ProbabilityMeasure X),
      F ≤ 𝓝 P ↔ ∀ (f : BoundedContinuousFunction X ℝ),
        F ≤ comap (fun Q : ProbabilityMeasure X => ∫ ω, f ω ∂(Q : Measure X))
          (𝓝 (∫ ω, f ω ∂(P : Measure X))) := by
    intro F
    have hkey := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto (F := F) (μs := id) (μ := P)
    constructor
    · intro hF f
      have hid : Tendsto id F (𝓝 P) := by simpa [Filter.Tendsto] using hF
      exact Filter.map_le_iff_le_comap.mp (hkey.mp hid f)
    · intro hF
      have hid : Tendsto id F (𝓝 P) := hkey.mpr (fun f => Filter.map_le_iff_le_comap.mpr (hF f))
      simpa [Filter.Tendsto] using hid
  have hEq : 𝓝 P = ⨅ (f : BoundedContinuousFunction X ℝ),
      comap (fun Q : ProbabilityMeasure X => ∫ ω, f ω ∂(Q : Measure X))
        (𝓝 (∫ ω, f ω ∂(P : Measure X))) :=
    le_antisymm (le_iInf fun f => (hchar (𝓝 P)).mp le_rfl f) ((hchar _).mpr fun f => iInf_le _ f)
  have hUm : U ∈ ⨅ (f : BoundedContinuousFunction X ℝ),
      comap (fun Q : ProbabilityMeasure X => ∫ ω, f ω ∂(Q : Measure X))
        (𝓝 (∫ ω, f ω ∂(P : Measure X))) := by
    rw [← hEq]
    exact hU
  rw [Filter.mem_iInf] at hUm
  obtain ⟨I, hIfin, V, hV, hUV⟩ := hUm
  have hstep : ∀ i : ↑I, ∃ δ : ℝ, 0 < δ ∧ ∀ Q : ProbabilityMeasure X,
      |∫ ω, (i : BoundedContinuousFunction X ℝ) ω ∂(Q : Measure X)
        - ∫ ω, (i : BoundedContinuousFunction X ℝ) ω ∂(P : Measure X)| < δ → Q ∈ V i := by
    intro i
    obtain ⟨W, hWmem, hWV⟩ := Filter.mem_comap.mp (hV i)
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hWmem
    refine ⟨δ, hδ, fun Q hQ => hWV ?_⟩
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq]
    exact hQ
  choose δ hδpos hδdef using hstep
  haveI : Fintype ↑I := hIfin.fintype
  obtain ⟨ε, hεpos, hεle⟩ : ∃ ε : ℝ, 0 < ε ∧ ∀ i : ↑I, ε ≤ δ i := by
    rcases isEmpty_or_nonempty (↑I) with h | h
    · exact ⟨1, one_pos, fun i => (h.false i).elim⟩
    · obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image (Finset.univ : Finset ↑I) δ Finset.univ_nonempty
      exact ⟨δ i0, hδpos i0, fun i => hi0 i (Finset.mem_univ i)⟩
  set G : Option ↑I → BoundedContinuousFunction X ℝ := fun o =>
    match o with
    | none => 1
    | some i => (i : BoundedContinuousFunction X ℝ) with hG
  let ψ : Fin (Fintype.card (Option ↑I)) → BoundedContinuousFunction X ℝ :=
    fun j => G ((Fintype.equivFin (Option ↑I)).symm j)
  have hVsub : ∀ Q : ProbabilityMeasure X,
      (∀ j : Fin (Fintype.card (Option ↑I)),
        |∫ x, (ψ j : X → ℝ) x ∂Q.toMeasure - ∫ x, (ψ j : X → ℝ) x ∂P.toMeasure| < ε) →
        Q ∈ U := by
    intro Q hQ
    have hmem : ∀ i : ↑I, Q ∈ V i := by
      intro i
      refine hδdef i Q (lt_of_lt_of_le ?_ (hεle i))
      have h2 := hQ ((Fintype.equivFin (Option ↑I)) (some i))
      simpa [ψ, hG] using h2
    have hmemU : Q ∈ ⋂ i : ↑I, V i := Set.mem_iInter.mpr hmem
    rw [← hUV] at hmemU
    exact hmemU
  have hr : 1 ≤ Fintype.card (Option ↑I) := by
    have hc : Fintype.card (Option ↑I) = Fintype.card ↑I + 1 := Fintype.card_option
    omega
  have hMpos : 0 < ⨆ j : Fin (Fintype.card (Option ↑I)), ⨆ x : X, |(ψ j : X → ℝ) x| := by
    obtain ⟨x0⟩ := hXne
    set j0 : Fin (Fintype.card (Option ↑I)) := Fintype.equivFin (Option ↑I) none with hj0
    have hψ0b : ψ j0 = (1 : BoundedContinuousFunction X ℝ) := by
      simp [ψ, hj0, hG]
    have hψ0 : ((ψ j0 : BoundedContinuousFunction X ℝ) : X → ℝ) = fun _ => (1 : ℝ) := by
      funext x
      rw [hψ0b]
      simp
    have hbddIn : BddAbove (Set.range fun x : X => |(ψ j0 : X → ℝ) x|) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨x, rfl⟩
      rw [hψ0]
      simp
    have hbddOut : BddAbove (Set.range fun j : Fin (Fintype.card (Option ↑I)) =>
        ⨆ x : X, |(ψ j : X → ℝ) x|) :=
      (Set.finite_range (fun j : Fin (Fintype.card (Option ↑I)) =>
        ⨆ x : X, |(ψ j : X → ℝ) x|)).bddAbove
    have h1 : (1 : ℝ) ≤ ⨆ j : Fin (Fintype.card (Option ↑I)), ⨆ x : X, |(ψ j : X → ℝ) x| := by
      refine le_trans ?_ (le_ciSup hbddOut j0)
      calc (1 : ℝ) = |(ψ j0 : X → ℝ) x0| := by rw [hψ0]; simp
        _ ≤ ⨆ x : X, |(ψ j0 : X → ℝ) x| := le_ciSup hbddIn x0
    exact lt_of_lt_of_le one_pos h1
  have hcpos : 0 < ε ^ 2 /
      (8 * (⨆ j : Fin (Fintype.card (Option ↑I)), ⨆ x : X, |(ψ j : X → ℝ) x|) ^ 2) :=
    div_pos (pow_pos hεpos 2) (mul_pos (by norm_num) (pow_pos hMpos 2))
  refine ⟨Fintype.card (Option ↑I), ψ, ε,
    (⨆ j : Fin (Fintype.card (Option ↑I)), ⨆ x : X, |(ψ j : X → ℝ) x|),
    ε ^ 2 / (8 * (⨆ j : Fin (Fintype.card (Option ↑I)), ⨆ x : X, |(ψ j : X → ℝ) x|) ^ 2),
    hr, hεpos, rfl, hMpos, rfl, hcpos, hVsub, ?_⟩
  intro s hs hst Q hQ hV
  have hUQ : Q ∈ U := hVsub Q hV
  have hmem : Q ∈ U ∩ KernelGSet μ k s := ⟨hUQ, hQ⟩
  rw [hsep s hs hst] at hmem
  exact hmem
  /- @proof-region region.target-node.session.64d9ae89f20dd9d5 end -/

theorem full_vector_typeII {Θ X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Θ]
    (μ : Measure X) (k : Θ → X → ℝ)
    (hk_nonneg : ∀ (θ : Θ) (x : X), 0 ≤ k θ x)
    (hk_meas : Measurable (Function.uncurry k))
    (hk_int : ∀ θ : Θ, ∫⁻ x, ENNReal.ofReal (k θ x) ∂μ = 1)
    (P : ProbabilityMeasure X) (t : ℕ) (ht : 2 ≤ t)
    (n : ℕ) (hn : 0 < n) (r : ℕ) (hr : 1 ≤ r)
    (psi : Fin r → X → ℝ) (hpsi_cont : ∀ j, Continuous (psi j))
    (M : ℝ) (hM_def : M = ⨆ j : Fin r, ⨆ x : X, |psi j x|)
    (hM : 0 < M) (hpsi_bound : ∀ j x, |psi j x| ≤ M)
    (eps : ℝ) (heps : 0 < eps) (c : ℝ) (hc : c = eps ^ 2 / (8 * M ^ 2))
    (hsep : ∀ s : ℕ, 1 ≤ s → s < t → ∀ Q : ProbabilityMeasure X,
      Q ∈ KernelGSet μ k s →
        ¬ (∀ j : Fin r, |∫ x, psi j x ∂Q.toMeasure - ∫ x, psi j x ∂P.toMeasure| < eps))
    (theta : Fin n → Θ) (htheta : (Set.range theta).ncard < t) :
    Measure.pi (fun i : Fin n => μ.withDensity (fun x => ENNReal.ofReal (k (theta i) x)))
      {x : Fin n → X | (⨆ j : Fin r,
        |(n : ℝ)⁻¹ * (∑ i : Fin n, psi j (x i)) - ∫ y, psi j y ∂P.toMeasure|) < eps / 2}
      ≤ ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * c)) := by
  classical
  set ν : Fin n → Measure X := fun i => μ.withDensity (fun x => ENNReal.ofReal (k (theta i) x)) with hνdef
  have hνprob : ∀ i : Fin n, IsProbabilityMeasure (ν i) := by
    intro i
    have h2 : (ν i) Set.univ = 1 := by
      have h3 : ν i = μ.withDensity (fun x => ENNReal.ofReal (k (theta i) x)) := by rw [hνdef]
      rw [h3, MeasureTheory.withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      exact hk_int (theta i)
    exact ⟨h2⟩
  haveI hνsf : ∀ i : Fin n, SigmaFinite (ν i) := fun i => by
    haveI := hνprob i
    infer_instance
  set t' : Finset Θ := Finset.univ.image theta with ht'def
  set e : Fin t'.card ≃ ↥t' := (Finset.equivFin t').symm with hedef
  set ϑ : Fin t'.card → Θ := fun j => (e j).1 with hϑdef
  set m : Fin t'.card → ℕ := fun j => (Finset.univ.filter (fun i : Fin n => theta i = ϑ j)).card with hmdef
  set q : Fin t'.card → ℝ := fun j => (m j : ℝ) / (n : ℝ) with hqdef
  have hrange_coe : Set.range theta = ↑t' := by
    rw [ht'def]
    simp [Finset.coe_image, Set.image_univ]
  have ht'ne : t'.Nonempty := by
    refine ⟨theta ⟨0, hn⟩, ?_⟩
    rw [ht'def]
    exact Finset.mem_image.mpr ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩
  have hϑinj : Function.Injective ϑ := by
    intro a b hab
    exact e.injective (Subtype.ext hab)
  have hϑrange : Set.range ϑ = Set.range theta := by
    ext y
    constructor
    · rintro ⟨j, rfl⟩
      rw [hrange_coe]
      exact (e j).2
    · intro hy
      rw [hrange_coe] at hy
      refine ⟨e.symm ⟨y, hy⟩, ?_⟩
      show (e (e.symm ⟨y, hy⟩)).1 = y
      rw [Equiv.apply_symm_apply]
  have hs1 : 1 ≤ t'.card := Finset.card_pos.mpr ht'ne
  have hst : t'.card < t := by
    have hncard : (Set.range theta).ncard = t'.card := by
      rw [hrange_coe]
      exact Set.ncard_coe_finset t'
    rw [← hncard]
    exact htheta
  have hcount : ∀ i : Fin n, ∃ j : Fin t'.card, theta i = ϑ j := by
    intro i
    have hmem : theta i ∈ Set.range ϑ := by
      rw [hϑrange]
      exact ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := hmem
    exact ⟨j, hj.symm⟩
  have hfiber : ∀ x : X, (∑ i : Fin n, k (theta i) x)
      = ∑ j : Fin t'.card, (m j : ℝ) * k (ϑ j) x := by
    intro x
    calc (∑ i : Fin n, k (theta i) x)
        = ∑ i : Fin n, (∑ j : Fin t'.card, (if theta i = ϑ j then k (ϑ j) x else 0)) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          obtain ⟨j₀, hj₀⟩ := hcount i
          refine ((Finset.sum_eq_single j₀ ?_ ?_).trans ?_).symm
          · intro b _ hb
            exact if_neg (fun h => hb (hϑinj (by rw [← h]; exact hj₀)))
          · intro h
            exact absurd (Finset.mem_univ j₀) h
          · rw [if_pos hj₀, hj₀]
      _ = ∑ j : Fin t'.card, ∑ i : Fin n, (if theta i = ϑ j then k (ϑ j) x else 0) :=
          Finset.sum_comm
      _ = ∑ j : Fin t'.card, (m j : ℝ) * k (ϑ j) x := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

  have hdens : ∀ x : X, kernelMixDensity k q ϑ x = (n : ℝ)⁻¹ * (∑ i : Fin n, k (theta i) x) := by
    intro x
    have h₁ : (∑ j : Fin t'.card, q j * k (ϑ j) x)
        = (n : ℝ)⁻¹ * (∑ j : Fin t'.card, (m j : ℝ) * k (ϑ j) x) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [hqdef]
      ring
    have h₂ : (∑ j : Fin t'.card, (m j : ℝ) * k (ϑ j) x) = ∑ i : Fin n, k (theta i) x :=
      (hfiber x).symm
    simp only [kernelMixDensity]
    rw [h₁, h₂]

  have hfib_ne : ∀ j : Fin t'.card,
      (Finset.univ.filter (fun i : Fin n => theta i = ϑ j)).Nonempty := by
    intro j
    have hj : ϑ j ∈ Set.range theta := by
      rw [← hϑrange]
      exact ⟨j, rfl⟩
    obtain ⟨i, hi⟩ := hj
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hqpos : ∀ j : Fin t'.card, 0 < q j := by
    intro j
    have hm1 : 0 < m j := Finset.card_pos.mpr (hfib_ne j)
    simp only [hqdef]
    exact div_pos (Nat.cast_pos.mpr hm1) hnR
  have hmass_n : (∑ j : Fin t'.card, m j) = n := by
    calc (∑ j : Fin t'.card, m j)
        = ∑ j : Fin t'.card, ∑ i : Fin n, (if theta i = ϑ j then 1 else 0) := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          simp only [hmdef]
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      _ = ∑ i : Fin n, ∑ j : Fin t'.card, (if theta i = ϑ j then 1 else 0) := Finset.sum_comm
      _ = ∑ i : Fin n, 1 := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          obtain ⟨j₀, hj₀⟩ := hcount i
          refine (Finset.sum_eq_single j₀ ?_ ?_).trans ?_
          · intro b _ hb
            exact if_neg (fun h => hb (hϑinj (by rw [← h]; exact hj₀)))
          · intro h
            exact absurd (Finset.mem_univ j₀) h
          · rw [if_pos hj₀]
      _ = n := by simp
  have hqsum : ∑ j : Fin t'.card, q j = 1 := by
    have hcast : (∑ j : Fin t'.card, (m j : ℝ)) = (n : ℝ) := by
      rw [← Nat.cast_sum, hmass_n]
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
    simp only [hqdef]
    rw [← Finset.sum_div, hcast, div_self hn0]
  have hex : ∃ j : Fin r,
      eps ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, (∫ y, psi j y ∂(ν i))) - ∫ y, psi j y ∂(P.toMeasure)| := by
    set g : X → ℝ≥0∞ := fun x => ENNReal.ofReal (kernelMixDensity k q ϑ x) with hgdef
    have hterm_meas : ∀ j : Fin t'.card,
        Measurable (fun x : X => ENNReal.ofReal (q j * k (ϑ j) x)) := by
      intro j
      exact ((hk_meas.comp (measurable_prodMk_left (x := ϑ j))).const_mul (q j)).ennreal_ofReal
    have hpoint : ∀ x : X, g x = ∑ j : Fin t'.card, ENNReal.ofReal (q j * k (ϑ j) x) := by
      intro x
      simp only [hgdef, kernelMixDensity]
      exact ENNReal.ofReal_sum_of_nonneg
        (fun j _ => mul_nonneg (le_of_lt (hqpos j)) (hk_nonneg (ϑ j) x))
    have hgmass : ∫⁻ x, g x ∂μ = 1 := by
      simp only [hpoint]
      rw [MeasureTheory.lintegral_finset_sum Finset.univ (fun j _ => hterm_meas j)]
      have hstep : ∀ j : Fin t'.card,
          ∫⁻ x, ENNReal.ofReal (q j * k (ϑ j) x) ∂μ = ENNReal.ofReal (q j) := by
        intro j
        have hmk : Measurable (fun x : X => ENNReal.ofReal (k (ϑ j) x)) :=
          (hk_meas.comp (measurable_prodMk_left (x := ϑ j))).ennreal_ofReal
        have hcongr : (fun x : X => ENNReal.ofReal (q j * k (ϑ j) x))
            = fun x : X => ENNReal.ofReal (q j) * ENNReal.ofReal (k (ϑ j) x) := by
          funext x
          exact ENNReal.ofReal_mul (le_of_lt (hqpos j))
        rw [hcongr,
          MeasureTheory.lintegral_const_mul (r := ENNReal.ofReal (q j))
            (f := fun x : X => ENNReal.ofReal (k (ϑ j) x)) hmk,
          hk_int (ϑ j), mul_one]
      rw [Finset.sum_congr rfl (fun j _ => hstep j),
        ← ENNReal.ofReal_sum_of_nonneg (fun j _ => le_of_lt (hqpos j)), hqsum]
      simp
    let Q : ProbabilityMeasure X := ⟨μ.withDensity g, ⟨by
      rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      exact hgmass⟩⟩
    have hQmem : Q ∈ KernelGSet μ k t'.card := by
      refine ⟨q, ϑ, ?_⟩
      exact ⟨hqpos, hqsum, hϑinj, rfl⟩
    have hnot := hsep t'.card hs1 hst Q hQmem
    rw [not_forall] at hnot
    obtain ⟨j, hj⟩ := hnot
    rw [not_lt] at hj
    refine ⟨j, ?_⟩
    set C : ℝ := M with hCdef
    have hCnn : 0 ≤ C := le_of_lt hM
    have hCle : ∀ x : X, |psi j x| ≤ C := fun x => hpsi_bound j x
    have hInt : ∀ i : Fin n, Integrable (fun x : X => k (theta i) x * psi j x) μ := by
      intro i
      have hbk : Measurable (fun x : X => k (theta i) x) :=
        hk_meas.comp (measurable_prodMk_left (x := theta i))
      have hg : Integrable (fun x : X => C * k (theta i) x) μ := by
        have hnn : 0 ≤ᶠ[ae μ] (fun x : X => C * k (theta i) x) :=
          Filter.Eventually.of_forall (fun x => mul_nonneg hCnn (hk_nonneg (theta i) x))
        rw [← MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
          (hbk.const_mul C).aestronglyMeasurable hnn]
        have hcongr : (fun x : X => ENNReal.ofReal (C * k (theta i) x))
            = fun x : X => ENNReal.ofReal C * ENNReal.ofReal (k (theta i) x) := by
          funext x
          exact ENNReal.ofReal_mul hCnn
        rw [hcongr, MeasureTheory.lintegral_const_mul (r := ENNReal.ofReal C)
          (f := fun x : X => ENNReal.ofReal (k (theta i) x)) hbk.ennreal_ofReal,
          hk_int (theta i), mul_one]
        exact ENNReal.ofReal_ne_top
      refine MeasureTheory.Integrable.mono' hg
        (hbk.mul (hpsi_cont j).measurable).aestronglyMeasurable ?_
      refine Filter.Eventually.of_forall (fun x => ?_)
      have h1 : ‖k (theta i) x * psi j x‖ = k (theta i) x * |psi j x| := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hk_nonneg (theta i) x)]
      rw [h1]
      calc k (theta i) x * |psi j x| ≤ k (theta i) x * C :=
            mul_le_mul_of_nonneg_left (hCle x) (hk_nonneg (theta i) x)
        _ = C * k (theta i) x := mul_comm _ _
    have hνint : ∀ i : Fin n, ∫ y, psi j y ∂(ν i) = ∫ y, k (theta i) y * psi j y ∂μ := by
      intro i
      have hνi : (ν i) = μ.withDensity (fun x : X => ENNReal.ofReal (k (theta i) x)) := by
        rw [hνdef]
      rw [hνi]
      have hmk : Measurable (fun x : X => ENNReal.ofReal (k (theta i) x)) :=
        (hk_meas.comp (measurable_prodMk_left (x := theta i))).ennreal_ofReal
      rw [integral_withDensity_eq_integral_toReal_smul
        (f := fun x : X => ENNReal.ofReal (k (theta i) x)) hmk
        (Filter.Eventually.of_forall (fun x => by simp)) (psi j)]
      have hcongr : (fun y : X => ENNReal.toReal (ENNReal.ofReal (k (theta i) y)) • psi j y)
          = fun y : X => k (theta i) y * psi j y := by
        funext y
        rw [ENNReal.toReal_ofReal (hk_nonneg (theta i) y)]
        simp
      rw [hcongr]
    have hdp_meas : Measurable (fun y : X => kernelMixDensity k q ϑ y) := by
      simp only [kernelMixDensity]
      exact Finset.measurable_sum Finset.univ
        (fun j' _ => (hk_meas.comp (measurable_prodMk_left (x := ϑ j'))).const_mul (q j'))
    have hdp_nn : ∀ y : X, 0 ≤ kernelMixDensity k q ϑ y := by
      intro y
      simp only [kernelMixDensity]
      exact Finset.sum_nonneg
        (fun j' _ => mul_nonneg (le_of_lt (hqpos j')) (hk_nonneg (ϑ j') y))
    have hQint : ∫ y, psi j y ∂(↑Q) = ∫ y, kernelMixDensity k q ϑ y * psi j y ∂μ := by
      show ∫ y, psi j y ∂(μ.withDensity g) = ∫ y, kernelMixDensity k q ϑ y * psi j y ∂μ
      rw [integral_withDensity_eq_integral_toReal_smul hdp_meas.ennreal_ofReal
        (Filter.Eventually.of_forall (fun x => by simp)) (psi j)]
      have hcongr : (fun y : X => ENNReal.toReal (g y) • psi j y)
          = fun y : X => kernelMixDensity k q ϑ y * psi j y := by
        funext y
        simp only [hgdef]
        rw [ENNReal.toReal_ofReal (hdp_nn y)]
        simp
      rw [hcongr]
    have hkey : (∫ y, psi j y ∂(↑Q)) = (n : ℝ)⁻¹ * ∑ i : Fin n, ∫ y, psi j y ∂(ν i) := by
      rw [hQint]
      have hcongr : (fun y : X => kernelMixDensity k q ϑ y * psi j y)
          = fun y : X => (n : ℝ)⁻¹ * ∑ i : Fin n, k (theta i) y * psi j y := by
        funext y
        have hT : (∑ i : Fin n, k (theta i) y * psi j y)
            = (∑ i : Fin n, k (theta i) y) * psi j y := by
          rw [Finset.sum_mul]
        rw [hdens y, hT]
        ring
      rw [hcongr, MeasureTheory.integral_const_mul]
      congr 1
      rw [MeasureTheory.integral_finset_sum Finset.univ (fun i _ => hInt i)]
      exact Finset.sum_congr rfl (fun i _ => (hνint i).symm)
    rw [hkey] at hj
    exact hj

  obtain ⟨j, hj⟩ := hex
  have hdep := (statopia_math_node_2781295325_3f1c8bad (↑P) r hr psi hpsi_cont M hM hM_def
    hpsi_bound eps heps).2 n hn ν hνprob ⟨j, hj⟩
  rw [hc]
  exact hdep


/-- A separated weak neighbourhood supplies genuine full-latent uniform tests.
No posterior consistency premise or fixed-first-t surrogate is used. -/
theorem full_latent_testing_of_separated_neighborhood
    {X Θ : Type*} [MeasurableSpace X] [MeasurableSpace Θ]
    [MetricSpace X] [BorelSpace X] [MeasureSpace X] [CompleteSpace X]
    [SecondCountableTopology X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
    [MetricSpace Θ] [BorelSpace Θ] [StandardBorelSpace Θ] [ProperSpace Θ]
    (M : DPMModel X Θ) (P : ProbabilityMeasure X) (t : ℕ) (ht : 2 ≤ t)
    (theta0 : Θ) (U : Set (ProbabilityMeasure X)) (hU : U ∈ 𝓝 P)
    (hsep : ∀ s : ℕ, 1 ≤ s → s < t → ∀ Q ∈ U,
      ¬ ∃ (q : Fin s → ℝ) (theta : Fin s → Θ),
        (∀ j, 0 < q j) ∧ (∑ j, q j = 1) ∧ Function.Injective theta ∧
          (∀ j, theta j ∈ M.Θset) ∧ (Q : Measure X) = mixtureMeasure M q theta) :
    OfflineDPConsumer.FullLatentTestingTarget M t (P : Measure X) := by
  classical
  have hk_int : ∀ theta : Θ, ∫⁻ x, ENNReal.ofReal (M.kdens theta x) ∂M.μ = 1 := by
    intro theta
    have hmass := (M.kdens_prob theta).measure_univ
    change (M.μ.withDensity (fun x => ENNReal.ofReal (M.kdens theta x))) Set.univ = 1 at hmass
    simpa only [MeasureTheory.withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ] using hmass
  have hsep_raw : ∀ s : ℕ, 1 ≤ s → s < t → U ∩ KernelGSet M.μ M.kdens s = ∅ := by
    intro s hs hst
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro Q hQ
    obtain ⟨q, theta, hq, hqsum, hinj, hQdens⟩ := hQ.2
    have hident := statopia_math_node_2986921194_82fe1497 M s hs q theta hq hqsum
      (fun j => M.kdens_prob (theta j))
    have hQM : (Q : Measure X) = mixtureMeasure M q theta := by
      exact hQdens.trans hident.1.symm
    exact hsep s hs hst Q hQ.1 ⟨q, theta, hq, hqsum, hinj,
      (fun j => by rw [M.Θset_univ]; exact Set.mem_univ _), hQM⟩
  obtain ⟨r, psi, eps, B, c, hr, heps, hBdef, hB, hcdef, hc, hVsub, htestsep⟩ :=
    statopia_math_node_3257560511_130c2ed0 M.μ M.kdens M.kdens_nonneg M.hk_meas
      hk_int P U hU t ht theta0 hsep_raw
  have hpsi_cont : ∀ j : Fin r, Continuous (fun x => (psi j : X → ℝ) x) :=
    fun j => (psi j).continuous
  have hpsi_bound : ∀ j : Fin r, ∀ x : X, |(psi j : X → ℝ) x| ≤ B := by
    intro j x
    rw [hBdef]
    have hbddIn : BddAbove (Set.range (fun x : X => |(psi j : X → ℝ) x|)) := by
      refine ⟨‖psi j‖, ?_⟩
      rintro _ ⟨x, rfl⟩
      simpa using BoundedContinuousFunction.norm_coe_le_norm (psi j) x
    have hbddOut : BddAbove (Set.range (fun j : Fin r => ⨆ x : X, |(psi j : X → ℝ) x|)) :=
      (Set.finite_range _).bddAbove
    exact le_trans (le_ciSup hbddIn x) (le_ciSup hbddOut j)
  let A : (n : ℕ) → Set (Fin n → X) := fun n =>
    {xs | (⨆ j : Fin r, |(n : ℝ)⁻¹ * (∑ i : Fin n, (psi j : X → ℝ) (xs i)) -
      ∫ y, (psi j : X → ℝ) y ∂(P : Measure X)|) < eps / 2}
  have hAmeas : ∀ n, MeasurableSet (A n) := by
    intro n
    have hforall : A n = {xs : Fin n → X | ∀ j : Fin r,
      |(n : ℝ)⁻¹ * (∑ i : Fin n, (psi j : X → ℝ) (xs i)) -
        ∫ y, (psi j : X → ℝ) y ∂(P : Measure X)| < eps / 2} := by
      ext xs
      have hne : (Finset.univ : Finset (Fin r)).Nonempty :=
        ⟨⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hr⟩, Finset.mem_univ _⟩
      haveI : Nonempty (Fin r) := ⟨⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hr⟩⟩
      dsimp only [A, Set.mem_setOf_eq]
      rw [← Finset.sup'_univ_eq_ciSup]
      exact (Finset.sup'_lt_iff hne).trans (by simp)
    rw [hforall, Set.setOf_forall]
    apply MeasurableSet.iInter
    intro j
    have hmean : Measurable (fun xs : Fin n → X =>
        (n : ℝ)⁻¹ * (∑ i : Fin n, (psi j : X → ℝ) (xs i)) -
          ∫ y, (psi j : X → ℝ) y ∂(P : Measure X)) := by
      have hsum : Measurable (fun xs : Fin n → X => ∑ i : Fin n, (psi j : X → ℝ) (xs i)) :=
        Finset.measurable_sum Finset.univ (fun i _ =>
          (hpsi_cont j).measurable.comp (measurable_pi_apply i))
      exact (hsum.const_mul ((n : ℝ)⁻¹)).sub measurable_const
    exact measurableSet_preimage hmean.abs measurableSet_Iio
  have htypeI := (statopia_math_node_2781295325_3f1c8bad (P : Measure X) r hr
    (fun j => (psi j : X → ℝ)) hpsi_cont B hB hBdef hpsi_bound eps heps).1
  have htypeII : ∀ n : ℕ, 0 < n → ∀ theta : Fin n → Θ, clusterCard theta < t →
      (Measure.pi (fun i : Fin n => M.kernel (theta i))) (A n) ≤
        ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * c)) := by
    intro n hn theta htheta
    exact full_vector_typeII M.μ M.kdens M.kdens_nonneg M.hk_meas hk_int P t ht n hn
      r hr (fun j => (psi j : X → ℝ)) hpsi_cont B hBdef hB hpsi_bound eps heps
      c hcdef htestsep theta htheta
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hcoef : 0 < 2 * (r : ℝ) := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * Real.log (2 * (r : ℝ)) / c)
  have habsorb : ∀ n : ℕ, N ≤ n →
      2 * (r : ℝ) * Real.exp (-(n : ℝ) * c) ≤ Real.exp (-((n : ℝ) * (c / 2))) := by
    intro n hn
    have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hquot : 2 * Real.log (2 * (r : ℝ)) / c < (n : ℝ) := lt_of_lt_of_le hN hcast
    have hmul := (div_lt_iff₀ hc).mp hquot
    rw [← Real.exp_log hcoef, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  refine ⟨c / 2, by positivity, fun n => (A n)ᶜ, fun n => (hAmeas n).compl, ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop N, eventually_gt_atTop 0] with n hnN hn
    have hbound := htypeI n hn
    have hset : (A n)ᶜ = {xs : Fin n → X | eps / 2 ≤ ⨆ j : Fin r,
        |(n : ℝ)⁻¹ * (∑ i : Fin n, (psi j : X → ℝ) (xs i)) -
          ∫ y, (psi j : X → ℝ) y ∂(P : Measure X)|} := by
      ext xs
      simp only [A, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
    rw [hset]
    exact le_trans hbound (ENNReal.ofReal_le_ofReal (by
      rw [← hcdef]
      exact habsorb n hnN))
  · filter_upwards [eventually_ge_atTop N, eventually_gt_atTop 0] with n hnN hn
    intro theta htheta
    simp only [compl_compl]
    exact le_trans (htypeII n hn theta htheta) (ENNReal.ofReal_le_ofReal (le_trans
      (by nlinarith [Real.exp_pos (-(n : ℝ) * c)]) (habsorb n hnN)))

#print axioms full_latent_testing_of_separated_neighborhood

/-- At most one required atom is a trivial occupied-cluster lower bound. -/
theorem full_latent_testing_trivial
    {X Θ : Type*} [MeasurableSpace X] [MeasurableSpace Θ]
    [MetricSpace X] [BorelSpace X] [MeasureSpace X] [CompleteSpace X]
    [SecondCountableTopology X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
    [MetricSpace Θ] [BorelSpace Θ] [StandardBorelSpace Θ] [ProperSpace Θ]
    (M : DPMModel X Θ) (P : Measure X) (t : ℕ) (ht : t ≤ 1) :
    OfflineDPConsumer.FullLatentTestingTarget M t P := by
  refine ⟨1, zero_lt_one, fun _ => ∅, fun _ => MeasurableSet.empty, ?_, ?_⟩
  · filter_upwards with n
    simp only [measure_empty]
    exact zero_le _
  · filter_upwards [eventually_gt_atTop 0] with n hn
    intro theta htheta
    have hfin : (Set.range theta).Finite := Set.finite_range theta
    have hne : (Set.range theta).Nonempty := ⟨theta ⟨0, hn⟩, ⟨⟨0, hn⟩, rfl⟩⟩
    have hcard : 0 < (Set.range theta).ncard := (Set.ncard_pos hfin).2 hne
    change (Set.range theta).ncard < t at htheta
    omega

/-- Full usable result; no extra assumption for the t=0/1 cases. -/
theorem full_latent_testing
    {X Θ : Type*} [MeasurableSpace X] [MeasurableSpace Θ]
    [MetricSpace X] [BorelSpace X] [MeasureSpace X] [CompleteSpace X]
    [SecondCountableTopology X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
    [MetricSpace Θ] [BorelSpace Θ] [StandardBorelSpace Θ] [ProperSpace Θ]
    (M : DPMModel X Θ) (P : ProbabilityMeasure X) (t : ℕ)
    (theta0 : Θ) (U : Set (ProbabilityMeasure X)) (hU : U ∈ 𝓝 P)
    (hsep : ∀ s : ℕ, 1 ≤ s → s < t → ∀ Q ∈ U,
      ¬ ∃ (q : Fin s → ℝ) (theta : Fin s → Θ),
        (∀ j, 0 < q j) ∧ (∑ j, q j = 1) ∧ Function.Injective theta ∧
          (∀ j, theta j ∈ M.Θset) ∧ (Q : Measure X) = mixtureMeasure M q theta) :
    OfflineDPConsumer.FullLatentTestingTarget M t (P : Measure X) := by
  by_cases ht : 2 ≤ t
  · exact full_latent_testing_of_separated_neighborhood M P t ht theta0 U hU hsep
  · exact full_latent_testing_trivial M (P : Measure X) t (by omega)

#print axioms full_latent_testing
#print axioms full_vector_typeII

end OfflineDPTesting


