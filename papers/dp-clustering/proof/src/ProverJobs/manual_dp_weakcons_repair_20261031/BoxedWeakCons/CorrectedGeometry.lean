import Statlib.StatFoundation.BasicAnalysis.ENNRealBridge
import ProverJobs.manual_dp_weakcons_repair_20261031.BoxedWeakCons.CorrectedTesting
import Lean

/- Genuine source ProverJobs.job_paper_80f79a059f3741e883a5b36dc8747f99.ProvedNodes.Node_3376410386_6fc2e54c_bd65a175; namespace isolation only; retained external axioms remain explicit. -/

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
theorem statopia_math_node_3376410386_6fc2e54c : ∀ {X Θ : Type*}
    [MeasurableSpace X] [MeasurableSpace Θ]
    [MetricSpace X] [BorelSpace X] [MeasureSpace X] [CompleteSpace X]
    [SecondCountableTopology X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
    [MetricSpace Θ] [BorelSpace Θ] [StandardBorelSpace Θ] [ProperSpace Θ]
    (P0 : Measure X) [IsProbabilityMeasure P0]
    (M : DPMModel X Θ)
    (t s : ℕ) (ht : 1 ≤ t) (hs : 1 ≤ s) (hst : s < t)
    (q : ℕ → Fin s → ℝ)
    (hqpos : ∀ (i : ℕ) (j : Fin s), 0 < q i j)
    (hqsum : ∀ (i : ℕ), ∑ j : Fin s, q i j = 1)
    (thetaSeq : ℕ → Fin s → Θ)
    (hinj : ∀ (i : ℕ), Function.Injective (thetaSeq i))
    (hmem : ∀ (i : ℕ) (j : Fin s), thetaSeq i j ∈ M.Θset)
    (hweak : ∀ (φ : X → ℝ), Continuous φ → (∃ B : ℝ, ∀ x : X, |φ x| ≤ B) →
      Tendsto (fun i : ℕ =>
          ∫ x, φ x ∂(∑ j : Fin s, ENNReal.ofReal (q i j) • M.kernel (thetaSeq i j)))
        atTop (𝓝 (∫ x, φ x ∂P0)))
    (hqlim : ∀ (j : Fin s), 0 < Filter.liminf (fun i : ℕ => q i j) atTop)
    (hdiv : ∀ (vartheta : ℕ → Θ), Tendsto vartheta atTop (cocompact Θ) →
      ∀ (Kset : Set X), IsCompact Kset →
        Tendsto (fun i : ℕ => M.kernel (vartheta i) Kset) atTop (𝓝 0)),
    ∀ (theta0 : Θ) (j0 : Fin s) (phi : ℕ → ℕ), StrictMono phi →
      (∀ r : ℝ, ∀ᶠ n in atTop, thetaSeq (phi n) j0 ∉ Metric.closedBall theta0 r) →
      False := by
  /- @proof-region region.target-node.session.19a22b88cb633600 begin -/
  intros X Θ imX imΘ iX iBX iMXX iCX iSC iXp iSep iT iBT iSB iTp P0 hP0prob M t s ht hs hst q hqpos hqsum thetaSeq hInj hMem hweak hqlim hdiv theta0 j0 phi hmono hesc
  set L : ℝ := liminf (fun i : ℕ => q i j0) atTop with hL
  have hLpos : 0 < L := by
    rw [hL]
    exact hqlim j0
  have hweight : ∀ᶠ n in atTop, L / 2 ≤ q (phi n) j0 := by
    have hmem : ∀ᶠ i in atTop, L / 2 ≤ q i j0 := by
      have hS : L / 2 < liminf (fun i : ℕ => q i j0) atTop := by
        rw [← hL]
        linarith
      unfold Filter.liminf Filter.limsInf at hS
      have hneS : ({a : ℝ | ∀ᶠ (n : ℝ) in map (fun i : ℕ => q i j0) atTop, a ≤ n} : Set ℝ).Nonempty := by
        refine ⟨0, ?_⟩
        exact Filter.Eventually.of_forall fun i => (hqpos i j0).le
      obtain ⟨a, haS, hLa⟩ := exists_lt_of_lt_csSup hneS hS
      have ha' : ∀ᶠ i in atTop, a ≤ q i j0 := haS
      filter_upwards [ha'] with i hi
      linarith
    exact hmono.tendsto_atTop.eventually hmem
  have hXne : Nonempty X := by
    rcases isEmpty_or_nonempty X with h | h
    · exfalso
      haveI := h
      have h1 : P0 (Set.univ : Set X) = 1 := measure_univ
      have h2 : (Set.univ : Set X) = ∅ := by
        ext x
        exact ⟨fun _ => h.false x, fun _ => trivial⟩
      rw [h2, measure_empty] at h1
      exact zero_ne_one h1
    · exact h
  let x0 : X := Classical.choice hXne
  have htight : ∃ m : ℕ, P0 ((Metric.closedBall x0 (m : ℝ))ᶜ) ≤ ENNReal.ofReal (L / 8) := by
    have hanti : Antitone (fun m : ℕ => (Metric.closedBall x0 (m : ℝ))ᶜ) := by
      intro a b hab
      exact Set.compl_subset_compl.mpr fun y hy =>
        Metric.mem_closedBall.mpr (le_trans (Metric.mem_closedBall.mp hy) (by exact_mod_cast hab))
    have hInter : (⋂ m : ℕ, (Metric.closedBall x0 (m : ℝ))ᶜ) = (∅ : Set X) := by
      ext x
      constructor
      · intro hx
        rw [Set.mem_iInter] at hx
        obtain ⟨n, hn⟩ := exists_nat_ge (dist x x0)
        exact absurd (Metric.mem_closedBall.mpr hn) (hx n)
      · intro hx
        exact absurd hx (by simp)
    have hmeas : ∀ m : ℕ, NullMeasurableSet ((Metric.closedBall x0 (m : ℝ))ᶜ) P0 :=
      fun m => (Metric.isClosed_closedBall.measurableSet.compl).nullMeasurableSet
    have hne : ∃ m : ℕ, P0 ((Metric.closedBall x0 (m : ℝ))ᶜ) ≠ ⊤ :=
      ⟨0, measure_ne_top P0 _⟩
    have htend := MeasureTheory.tendsto_measure_iInter_atTop
      (μ := P0) (s := fun m : ℕ => (Metric.closedBall x0 (m : ℝ))ᶜ) hmeas hanti hne
    have htend0 : Tendsto (fun m : ℕ => P0 ((Metric.closedBall x0 (m : ℝ))ᶜ)) atTop (𝓝 0) := by
      simpa [hInter] using htend
    have heps : (0 : ENNReal) < ENNReal.ofReal (L / 8) := ENNReal.ofReal_pos.mpr (by linarith)
    have hev := (ENNReal.tendsto_nhds_zero.mp htend0) (ENNReal.ofReal (L / 8)) heps
    exact hev.exists
  obtain ⟨m, hm⟩ := htight
  let χ : X → ℝ := fun x => max 0 (min 1 (dist x x0 - (m : ℝ)))
  have hχ_nonneg : ∀ x : X, 0 ≤ χ x := by
    intro x
    show (0 : ℝ) ≤ max 0 (min 1 (dist x x0 - (m : ℝ)))
    exact le_max_left _ _
  have hχ_le_one : ∀ x : X, χ x ≤ 1 := by
    intro x
    show max 0 (min 1 (dist x x0 - (m : ℝ))) ≤ 1
    exact max_le zero_le_one (min_le_left _ _)
  have hχ_abs : ∀ x : X, |χ x| ≤ 1 := by
    intro x
    rw [abs_of_nonneg (hχ_nonneg x)]
    exact hχ_le_one x
  have hχ_norm : ∀ x : X, ‖χ x‖ ≤ 1 := by
    intro x
    simpa [Real.norm_eq_abs] using hχ_abs x
  have hχ_cont : Continuous χ := by
    show Continuous fun x : X => max 0 (min 1 (dist x x0 - (m : ℝ)))
    first
      | fun_prop
      | exact (continuous_const : Continuous fun _ : X => (0 : ℝ)).max
          ((continuous_const : Continuous fun _ : X => (1 : ℝ)).min
            ((continuous_id.dist (continuous_const : Continuous fun _ : X => x0)).sub continuous_const))
  have hχ_int : ∀ (μ : Measure X) [IsFiniteMeasure μ], Integrable χ μ := by
    intro μ _
    exact MeasureTheory.Integrable.of_bound hχ_cont.measurable.aestronglyMeasurable 1
      (Filter.Eventually.of_forall hχ_norm)
  have hP0small : ∫ x, χ x ∂P0 ≤ L / 8 := by
    have hmeas_s : MeasurableSet ((Metric.closedBall x0 (m : ℝ))ᶜ) :=
      Metric.isClosed_closedBall.measurableSet.compl
    have hptw : ∀ x : X, χ x ≤ ((Metric.closedBall x0 (m : ℝ))ᶜ).indicator (1 : X → ℝ) x := by
      intro x
      by_cases hx : x ∈ (Metric.closedBall x0 (m : ℝ))ᶜ
      · rw [Set.indicator_of_mem hx]
        exact hχ_le_one x
      · have hx' : x ∈ Metric.closedBall x0 (m : ℝ) := by simpa using hx
        have hd : dist x x0 - (m : ℝ) ≤ 0 := by
          have hle := Metric.mem_closedBall.mp hx'
          linarith
        have hmin : min 1 (dist x x0 - (m : ℝ)) ≤ 0 := le_trans (min_le_right _ _) hd
        have hzero : χ x = 0 := by
          show max 0 (min 1 (dist x x0 - (m : ℝ))) = 0
          exact max_eq_left hmin
        rw [hzero]
        simp [Set.indicator, hx]
    have hInt_ind : Integrable (((Metric.closedBall x0 (m : ℝ))ᶜ).indicator (1 : X → ℝ)) P0 := by
      refine MeasureTheory.Integrable.of_bound (aestronglyMeasurable_const.indicator hmeas_s) 1 ?_
      refine Filter.Eventually.of_forall fun x => ?_
      by_cases hx : x ∈ (Metric.closedBall x0 (m : ℝ))ᶜ
      · rw [Set.indicator_of_mem hx]
        simp
      · simp [Set.indicator, hx]
    have hmono : ∫ x, χ x ∂P0 ≤
        ∫ x, ((Metric.closedBall x0 (m : ℝ))ᶜ).indicator (1 : X → ℝ) x ∂P0 :=
      MeasureTheory.integral_mono (hχ_int P0) hInt_ind hptw
    rw [MeasureTheory.integral_indicator_one hmeas_s] at hmono
    have hreal : (P0 ((Metric.closedBall x0 (m : ℝ))ᶜ)).toReal ≤ L / 8 := by
      have h1 : (P0 ((Metric.closedBall x0 (m : ℝ))ᶜ)).toReal ≤ (ENNReal.ofReal (L / 8)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
      rwa [ENNReal.toReal_ofReal (by linarith)] at h1
    calc ∫ x, χ x ∂P0 ≤ P0.real ((Metric.closedBall x0 (m : ℝ))ᶜ) := hmono
      _ = (P0 ((Metric.closedBall x0 (m : ℝ))ᶜ)).toReal := by simp [Measure.real]
      _ ≤ L / 8 := hreal
  have hϑcoc : Tendsto (fun n : ℕ => thetaSeq (phi n) j0) atTop (cocompact Θ) := by
    intro s hs
    rw [Filter.mem_map]
    obtain ⟨r, hr⟩ := (Metric.mem_cocompact_iff_closedBall_compl_subset theta0).mp hs
    filter_upwards [hesc r] with n hn
    exact hr hn
  have hKmass : ∀ᶠ n in atTop, (1 : ℝ) / 2 ≤ ∫ x, χ x ∂(M.kernel (thetaSeq (phi n) j0)) := by
    have hball_c : IsCompact (Metric.closedBall x0 ((m : ℝ) + 2)) := by
      first
        | exact Metric.isCompact_of_isClosed_isBounded Metric.isClosed_closedBall
            Metric.isBounded_closedBall
        | exact ProperSpace.isCompact_closedBall x0 ((m : ℝ) + 2)
        | exact Metric.isCompact_closedBall
        | exact isCompact_closedBall
    have hball_meas : MeasurableSet (Metric.closedBall x0 ((m : ℝ) + 2)) :=
      Metric.isClosed_closedBall.measurableSet
    have htend := hdiv (fun n : ℕ => thetaSeq (phi n) j0) hϑcoc
      (Metric.closedBall x0 ((m : ℝ) + 2)) hball_c
    have heps : (0 : ENNReal) < ENNReal.ofReal (1 / 2) := ENNReal.ofReal_pos.mpr (by norm_num)
    filter_upwards [(ENNReal.tendsto_nhds_zero.mp htend) (ENNReal.ofReal (1 / 2)) heps] with n hn
    have hprob : IsProbabilityMeasure (M.kernel (thetaSeq (phi n) j0)) :=
      M.kdens_prob (thetaSeq (phi n) j0)
    haveI := hprob
    have hptw : ∀ x : X, ((Metric.closedBall x0 ((m : ℝ) + 2))ᶜ).indicator (1 : X → ℝ) x ≤ χ x := by
      intro x
      by_cases hx : x ∈ (Metric.closedBall x0 ((m : ℝ) + 2))ᶜ
      · rw [Set.indicator_of_mem hx]
        have hxd : (m : ℝ) + 2 < dist x x0 := by
          have h1 : ¬ (dist x x0 ≤ (m : ℝ) + 2) := by
            simpa [Metric.mem_closedBall] using hx
          exact not_le.mp h1
        have hmin : min 1 (dist x x0 - (m : ℝ)) = 1 := by
          apply min_eq_left
          linarith
        show (1 : ℝ) ≤ max 0 (min 1 (dist x x0 - (m : ℝ)))
        rw [hmin]
        exact le_max_right 0 1
      · simpa [Set.indicator, hx] using hχ_nonneg x
    have hInt_ind : Integrable (((Metric.closedBall x0 ((m : ℝ) + 2))ᶜ).indicator (1 : X → ℝ))
        (M.kernel (thetaSeq (phi n) j0)) := by
      refine MeasureTheory.Integrable.of_bound
        (aestronglyMeasurable_const.indicator hball_meas.compl) 1 ?_
      refine Filter.Eventually.of_forall fun x => ?_
      by_cases hx : x ∈ (Metric.closedBall x0 ((m : ℝ) + 2))ᶜ
      · rw [Set.indicator_of_mem hx]
        simp
      · simp [Set.indicator, hx]
    have hmono : ∫ x, ((Metric.closedBall x0 ((m : ℝ) + 2))ᶜ).indicator (1 : X → ℝ) x
        ∂(M.kernel (thetaSeq (phi n) j0)) ≤ ∫ x, χ x ∂(M.kernel (thetaSeq (phi n) j0)) :=
      MeasureTheory.integral_mono hInt_ind (hχ_int (M.kernel (thetaSeq (phi n) j0))) hptw
    rw [MeasureTheory.integral_indicator_one hball_meas.compl] at hmono
    have hcompl : (M.kernel (thetaSeq (phi n) j0)) ((Metric.closedBall x0 ((m : ℝ) + 2))ᶜ)
        = 1 - (M.kernel (thetaSeq (phi n) j0)) (Metric.closedBall x0 ((m : ℝ) + 2)) := by
      first
        | rw [MeasureTheory.prob_compl hball_meas]
        | rw [MeasureTheory.measure_compl hball_meas (measure_ne_top _ _), measure_univ]
    have hle1 : (M.kernel (thetaSeq (phi n) j0)) (Metric.closedBall x0 ((m : ℝ) + 2)) ≤ 1 := by
      have hsub := measure_mono (Set.subset_univ _ :
        (Metric.closedBall x0 ((m : ℝ) + 2)) ⊆ (Set.univ : Set X))
        (μ := M.kernel (thetaSeq (phi n) j0))
      rwa [measure_univ] at hsub
    have hle2 : ((M.kernel (thetaSeq (phi n) j0)) (Metric.closedBall x0 ((m : ℝ) + 2))).toReal
        ≤ 1 / 2 := by
      have h1 : ((M.kernel (thetaSeq (phi n) j0)) (Metric.closedBall x0 ((m : ℝ) + 2))).toReal
          ≤ (ENNReal.ofReal (1 / 2)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hn
      rwa [ENNReal.toReal_ofReal (by norm_num)] at h1
    have hreal : (1 : ℝ) / 2 ≤
        ((M.kernel (thetaSeq (phi n) j0)) ((Metric.closedBall x0 ((m : ℝ) + 2))ᶜ)).toReal := by
      rw [hcompl, ENNReal.toReal_sub_of_le hle1 ENNReal.one_ne_top, ENNReal.toReal_one]
      linarith
    calc (1 : ℝ) / 2 ≤
        ((M.kernel (thetaSeq (phi n) j0)) ((Metric.closedBall x0 ((m : ℝ) + 2))ᶜ)).toReal := hreal
      _ = (M.kernel (thetaSeq (phi n) j0)).real ((Metric.closedBall x0 ((m : ℝ) + 2))ᶜ) := by
          simp [Measure.real]
      _ ≤ ∫ x, χ x ∂(M.kernel (thetaSeq (phi n) j0)) := hmono
  have hmix : ∀ᶠ n in atTop,
      L / 4 ≤ ∫ x, χ x ∂(∑ j : Fin s, ENNReal.ofReal (q (phi n) j) • M.kernel (thetaSeq (phi n) j)) := by
    have hident : ∀ n : ℕ,
        ∫ x, χ x ∂(∑ j : Fin s, ENNReal.ofReal (q (phi n) j) • M.kernel (thetaSeq (phi n) j))
          = ∑ j : Fin s, q (phi n) j * ∫ x, χ x ∂(M.kernel (thetaSeq (phi n) j)) := by
      intro n
      have hsmul_fin : ∀ j : Fin s,
          IsFiniteMeasure (ENNReal.ofReal (q (phi n) j) • M.kernel (thetaSeq (phi n) j)) := by
        intro j
        have hprobj : IsProbabilityMeasure (M.kernel (thetaSeq (phi n) j)) :=
          M.kdens_prob (thetaSeq (phi n) j)
        haveI := hprobj
        refine ⟨?_⟩
        have hpt : (ENNReal.ofReal (q (phi n) j) • M.kernel (thetaSeq (phi n) j)) Set.univ
            = ENNReal.ofReal (q (phi n) j) * (M.kernel (thetaSeq (phi n) j)) Set.univ := by
          simp
        rw [hpt]
        first
          | exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
          | exact ENNReal.mul_lt_top_iff.mpr ⟨ENNReal.ofReal_lt_top, measure_lt_top _ _⟩
      have h1 : ∫ x, χ x ∂(∑ j : Fin s, ENNReal.ofReal (q (phi n) j) • M.kernel (thetaSeq (phi n) j))
          = ∑ j : Fin s,
              ∫ x, χ x ∂(ENNReal.ofReal (q (phi n) j) • M.kernel (thetaSeq (phi n) j)) :=
        MeasureTheory.integral_finset_sum_measure (fun j _ => by
          haveI := hsmul_fin j
          exact hχ_int _)
      rw [h1]
      refine Finset.sum_congr rfl ?_
      intro j _
      simp only [MeasureTheory.integral_smul_measure,
        ENNReal.toReal_ofReal (le_of_lt (hqpos (phi n) j)), smul_eq_mul]
    filter_upwards [hweight, hKmass] with n hn1 hn2
    rw [hident n]
    have hint_nonneg : ∀ j : Fin s, 0 ≤ ∫ x, χ x ∂(M.kernel (thetaSeq (phi n) j)) := by
      intro j
      first
        | exact MeasureTheory.integral_nonneg fun x => hχ_nonneg x
        | exact MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => hχ_nonneg x)
    have hterm : q (phi n) j0 * ∫ x, χ x ∂(M.kernel (thetaSeq (phi n) j0))
        ≤ ∑ j : Fin s, q (phi n) j * ∫ x, χ x ∂(M.kernel (thetaSeq (phi n) j)) :=
      Finset.single_le_sum
        (f := fun j : Fin s => q (phi n) j * ∫ x, χ x ∂(M.kernel (thetaSeq (phi n) j)))
        (fun j _ => mul_nonneg (le_of_lt (hqpos (phi n) j)) (hint_nonneg j)) (Finset.mem_univ j0)
    have hlow : L / 4 ≤ q (phi n) j0 * ∫ x, χ x ∂(M.kernel (thetaSeq (phi n) j0)) := by
      have hmul := mul_le_mul hn1 hn2 (by norm_num : (0 : ℝ) ≤ 1 / 2) (le_of_lt (hqpos (phi n) j0))
      linarith
    linarith
  have hconv : Tendsto
      (fun n : ℕ => ∫ x, χ x ∂(∑ j : Fin s, ENNReal.ofReal (q (phi n) j) • M.kernel (thetaSeq (phi n) j)))
      atTop (𝓝 (∫ x, χ x ∂P0)) :=
    (hweak χ hχ_cont ⟨1, hχ_abs⟩).comp hmono.tendsto_atTop
  have hge : L / 4 ≤ ∫ x, χ x ∂P0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hconv hmix
  linarith
  /- @proof-region region.target-node.session.19a22b88cb633600 end -/

end Statlib.Imported


end OfflineCorrectedDP


/- Genuine source ProverJobs.job_paper_80f79a059f3741e883a5b36dc8747f99.ProvedNodes.Node_1004612324_aae1fc53_b1ea52e8; namespace isolation only; retained external axioms remain explicit. -/

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
theorem statopia_math_node_1004612324_aae1fc53 : ∀ {X Θ : Type*} [MeasurableSpace X] [MeasurableSpace Θ]
    [MetricSpace X] [BorelSpace X] [MeasureSpace X] [CompleteSpace X]
    [SecondCountableTopology X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
    [MetricSpace Θ] [BorelSpace Θ] [StandardBorelSpace Θ] [ProperSpace Θ]
    (P0 : Measure X) [IsProbabilityMeasure P0]
    (M : DPMModel X Θ)
    (t s : ℕ) (ht : 1 ≤ t) (hs : 1 ≤ s) (hst : s < t)
    (q : ℕ → Fin s → ℝ)
    (hqpos : ∀ (i : ℕ) (j : Fin s), 0 < q i j)
    (hqsum : ∀ (i : ℕ), ∑ j : Fin s, q i j = 1)
    (thetaSeq : ℕ → Fin s → Θ)
    (hinj : ∀ (i : ℕ), Function.Injective (thetaSeq i))
    (hmem : ∀ (i : ℕ) (j : Fin s), thetaSeq i j ∈ M.Θset)
    (hweak : ∀ (φ : X → ℝ), Continuous φ → (∃ B : ℝ, ∀ x : X, |φ x| ≤ B) →
      Tendsto (fun i : ℕ =>
          ∫ x, φ x ∂(∑ j : Fin s, ENNReal.ofReal (q i j) • M.kernel (thetaSeq i j)))
        atTop (𝓝 (∫ x, φ x ∂P0)))
    (hqlim : ∀ (j : Fin s), 0 < Filter.liminf (fun i : ℕ => q i j) atTop)
    (hdiv : ∀ (vartheta : ℕ → Θ), Tendsto vartheta atTop (cocompact Θ) →
      ∀ (Kset : Set X), IsCompact Kset →
        Tendsto (fun i : ℕ => M.kernel (vartheta i) Kset) atTop (𝓝 0)),
    (∀ (j : Fin s), ∃ K : Set Θ, IsCompact K ∧ ∀ᶠ i : ℕ in atTop, thetaSeq i j ∈ K) ∧
    (∃ C : Set Θ, IsCompact C ∧
      ∃ i0 : ℕ, ∀ i : ℕ, i0 ≤ i → ∀ j : Fin s, thetaSeq i j ∈ C) ∧
    (¬ ∃ (j : Fin s) (phi : ℕ → ℕ),
      StrictMono phi ∧ Tendsto (fun i : ℕ => thetaSeq (phi i) j) atTop (cocompact Θ)) := by
  /- @proof-region region.target-node.session.fc1a90200d107b44 begin -/
  classical
  intro X Θ
  intros
  rename_i P0 hP0 M t s ht hs1 hst q hqpos hqsum thetaSeq hThetaInj hThetaMem hweak hqlim hdiv
  obtain ⟨θ0, _⟩ := M.Θset_ne
  haveI hprob : IsProbabilityMeasure P0 := hP0
  have hnoball : ∀ (j₀ : Fin s) (phi : ℕ → ℕ), StrictMono phi →
      (∀ r : ℝ, ∀ᶠ n in atTop, thetaSeq (phi n) j₀ ∉ Metric.closedBall θ0 r) → False := by
    intro j₀ phi hmono hesc
    exact statopia_math_node_3376410386_6fc2e54c P0 M t s ht hs1 hst q hqpos hqsum thetaSeq
      hThetaInj hThetaMem hweak hqlim hdiv θ0 j₀ phi hmono hesc
  have hnoesc : ¬ ∃ (j : Fin s) (phi : ℕ → ℕ), StrictMono phi ∧
      Tendsto (fun i : ℕ => thetaSeq (phi i) j) atTop (cocompact Θ) := by
    rintro ⟨j₀, phi, hmono, htend⟩
    refine hnoball j₀ phi hmono (fun r => ?_)
    have hmem : (Metric.closedBall θ0 r)ᶜ ∈ Filter.cocompact Θ :=
      Metric.mem_cocompact_of_closedBall_compl_subset θ0 ⟨r, fun x hx => hx⟩
    exact htend.eventually hmem
  have hcomp : ∀ j : Fin s, ∃ K : Set Θ, IsCompact K ∧ ∀ᶠ i in atTop, thetaSeq i j ∈ K := by
    intro j
    by_contra hcon
    have hnotball : ∀ r : ℝ, ¬ ∀ᶠ i in atTop, thetaSeq i j ∈ Metric.closedBall θ0 r := by
      intro r hev
      exact hcon ⟨Metric.closedBall θ0 r,
        Metric.isCompact_of_isClosed_isBounded Metric.isClosed_closedBall Metric.isBounded_closedBall,
        hev⟩
    have hfreqA : ∀ r : ℝ, ∃ᶠ i in atTop, thetaSeq i j ∉ Metric.closedBall θ0 r := by
      intro r
      rw [Filter.frequently_atTop]
      intro x
      by_contra hb
      push_neg at hb
      exact hnotball r (Filter.eventually_atTop.2 ⟨x, fun i hi => hb i hi⟩)
    have hstep : ∀ (n N : ℕ), ∃ b : ℕ, N < b ∧ thetaSeq b j ∉ Metric.closedBall θ0 (n : ℝ) := by
      intro n N
      obtain ⟨b, hb, hbP⟩ := (Filter.frequently_atTop.1 (hfreqA (n : ℝ))) (N + 1)
      exact ⟨b, lt_of_lt_of_le (Nat.lt_succ_self N) hb, hbP⟩
    let phi : ℕ → ℕ := fun n => Nat.rec (Classical.choose (hstep 0 0))
      (fun k ih => Classical.choose (hstep (k + 1) (ih + 1))) n
    have hspecS : ∀ n : ℕ, thetaSeq (phi (n + 1)) j ∉ Metric.closedBall θ0 ((n + 1 : ℕ) : ℝ) :=
      fun n => (Classical.choose_spec (hstep (n + 1) (phi n + 1))).2
    have hstepmono : ∀ n : ℕ, phi n < phi (n + 1) := by
      intro n
      exact lt_trans (Nat.lt_succ_self (phi n))
        (Classical.choose_spec (hstep (n + 1) (phi n + 1))).1
    have hmono : StrictMono phi := strictMono_nat_of_lt_succ hstepmono
    have hesc : ∀ r : ℝ, ∀ᶠ n in atTop, thetaSeq (phi n) j ∉ Metric.closedBall θ0 r := by
      intro r
      obtain ⟨N, hN⟩ := exists_nat_ge r
      refine Filter.eventually_atTop.2 ⟨max N 1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 1 := ⟨n - 1, by omega⟩
      have hnk : N ≤ k + 1 := le_trans (le_max_left N 1) hn
      have hle : r ≤ ((k + 1 : ℕ) : ℝ) := le_trans hN (by exact_mod_cast hnk)
      intro hmem
      have hd : dist (thetaSeq (phi (k + 1)) j) θ0 ≤ ((k + 1 : ℕ) : ℝ) := by
        have h1 : dist (thetaSeq (phi (k + 1)) j) θ0 ≤ r := by
          simpa only [dist_comm] using Metric.mem_closedBall.1 hmem
        linarith
      exact hspecS k (by simpa only [dist_comm] using Metric.mem_closedBall.2 hd)
    exact hnoball j phi hmono hesc
  refine ⟨hcomp, ?_, hnoesc⟩
  choose K hK hKev using hcomp
  choose r hr using fun j : Fin s =>
    (Metric.isBounded_iff_subset_closedBall (s := K j) θ0).1 (hK j).isBounded
  choose N hN using fun j : Fin s => Filter.eventually_atTop.1 (hKev j)
  have hrle : ∀ j : Fin s, r j ≤ ∑ j' : Fin s, |r j'| := by
    intro j
    have h1 : |r j| ≤ ∑ j' : Fin s, |r j'| :=
      Finset.single_le_sum (fun i _ => abs_nonneg (r i)) (Finset.mem_univ j)
    linarith [le_abs_self (r j)]
  refine ⟨Metric.closedBall θ0 (∑ j : Fin s, |r j|),
    Metric.isCompact_of_isClosed_isBounded Metric.isClosed_closedBall Metric.isBounded_closedBall,
    Finset.univ.sup N, ?_⟩
  intro i hi j
  have hmem : thetaSeq i j ∈ K j :=
    hN j i (le_trans (Finset.le_sup (f := N) (Finset.mem_univ j)) hi)
  have h2 : thetaSeq i j ∈ Metric.closedBall θ0 (r j) := hr j hmem
  exact Metric.mem_closedBall.mpr (le_trans (Metric.mem_closedBall.mp h2) (hrle j))
  /- @proof-region region.target-node.session.fc1a90200d107b44 end -/

end Statlib.Imported


end OfflineCorrectedDP


/- Genuine source ProverJobs.job_paper_80f79a059f3741e883a5b36dc8747f99.ProvedNodes.Node_2713798316_cec71e42_74666179; namespace isolation only; retained external axioms remain explicit. -/

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
theorem statopia_math_node_2713798316_cec71e42 : ∀ {X Θ : Type*} [MeasurableSpace X] [MeasurableSpace Θ] [MetricSpace Θ]
    (M : DPMModel X Θ) (s : ℕ)
    (qbar : Fin s → ℝ) (thbar : Fin s → Θ)
    (hthbar : ∀ j : Fin s, thbar j ∈ M.Θset \ singularBoundary M)
    (qseq : ℕ → Fin s → ℝ) (thseq : ℕ → Fin s → Θ)
    (hq : ∀ j : Fin s, Tendsto (fun i : ℕ => qseq i j) atTop (𝓝 (qbar j)))
    (hth : ∀ j : Fin s, Tendsto (fun i : ℕ => thseq i j) atTop (𝓝 (thbar j)))
    (hcont : ∀ theta_bar, theta_bar ∈ M.Θset → theta_bar ∉ singularBoundary M →
      ∃ N : Set X, M.μ N = 0 ∧ ∀ x : X, x ∉ N →
        ∃ A : Set Θ, A ∈ 𝓝 theta_bar ∧ A ⊆ M.Θset \ singularBoundary M ∧
          ContinuousOn (fun th : Θ => M.kdens th x) A),
    (∀ᵐ x ∂M.μ, Tendsto (fun i : ℕ => mixDens M (qseq i) (thseq i) x) atTop
        (𝓝 (mixDens M qbar thbar x)))
      ∧ AEMeasurable (fun x : X => mixDens M qbar thbar x) M.μ := by
  /- @proof-region region.target-node.session.876246e3369f77c0 begin -/
  intro X Θ _instX _instΘ _instΘmet M s qbar thbar hthbar qseq thseq hq hth hcont
  choose Nj hNj using fun j : Fin s => hcont (thbar j) (hthbar j).1 (hthbar j).2
  have hNnull : M.μ (⋃ j : Fin s, Nj j) = 0 := by
    rw [MeasureTheory.measure_iUnion_null_iff]
    exact fun j => (hNj j).1
  have hae : ∀ᵐ x ∂M.μ, x ∉ (⋃ j : Fin s, Nj j) := by
    rw [MeasureTheory.ae_iff]
    have hEq : {a : X | ¬ a ∉ (⋃ j : Fin s, Nj j)} = ⋃ j : Fin s, Nj j := by
      ext a
      simp
    rw [hEq]
    exact hNnull
  refine ⟨?_, ?_⟩
  · filter_upwards [hae] with x hx
    simp only [Set.mem_iUnion, not_exists] at hx
    have hcontj : ∀ j : Fin s,
        Tendsto (fun i : ℕ => M.kdens (thseq i j) x) atTop (𝓝 (M.kdens (thbar j) x)) := by
      intro j
      obtain ⟨A, hA, -, hcontA⟩ := (hNj j).2 x (hx j)
      have hc' : Tendsto (fun th : Θ => M.kdens th x) (𝓝 (thbar j)) (𝓝 (M.kdens (thbar j) x)) :=
        hcontA.continuousAt hA
      exact hc'.comp (hth j)
    have hterm : ∀ j : Fin s,
        Tendsto (fun i : ℕ => qseq i j * M.kdens (thseq i j) x) atTop
          (𝓝 (qbar j * M.kdens (thbar j) x)) := by
      intro j
      exact (hq j).mul (hcontj j)
    have hsum : ∀ t : Finset (Fin s),
        Tendsto (fun i : ℕ => ∑ j ∈ t, qseq i j * M.kdens (thseq i j) x) atTop
          (𝓝 (∑ j ∈ t, qbar j * M.kdens (thbar j) x)) := by
      intro t
      refine Finset.induction_on t ?_ ?_
      · simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (0 : ℝ)))
      · intro a t ha ih
        simp only [Finset.sum_insert ha]
        exact (hterm a).add ih
    simpa [mixDens] using hsum Finset.univ
  · have hmeas_each : ∀ j : Fin s, Measurable (fun x : X => M.kdens (thbar j) x) := by
      intro j
      have hm : Measurable (fun x : X => (thbar j, x)) := by measurability
      simpa using M.hk_meas.comp hm
    have hmeas_sum : ∀ t : Finset (Fin s),
        Measurable (fun x : X => ∑ j ∈ t, qbar j * M.kdens (thbar j) x) := by
      intro t
      refine Finset.induction_on t ?_ ?_
      · simpa using (measurable_const : Measurable fun _ : X => (0 : ℝ))
      · intro a t ha ih
        simp only [Finset.sum_insert ha]
        exact (measurable_const.mul (hmeas_each a)).add ih
    have hlim : Measurable (fun x : X => mixDens M qbar thbar x) := by
      simpa [mixDens] using hmeas_sum Finset.univ
    exact hlim.aemeasurable
  /- @proof-region region.target-node.session.876246e3369f77c0 end -/

end Statlib.Imported


end OfflineCorrectedDP


/- Genuine source ProverJobs.job_paper_80f79a059f3741e883a5b36dc8747f99.ProvedNodes.Node_2077380816_7e90d538_c0ecaebd; namespace isolation only; retained external axioms remain explicit. -/

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
theorem statopia_math_node_2077380816_7e90d538 : ∀ {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α]
    (μ : Measure α) (d : ℕ → α → ℝ) (h : α → ℝ)
    (hd_meas : ∀ i : ℕ, AEMeasurable (d i) μ)
    (hd_nonneg : ∀ i : ℕ, 0 ≤ᵐ[μ] d i)
    (hh_meas : AEMeasurable h μ)
    (hh_nonneg : 0 ≤ᵐ[μ] h)
    (hd_mass : ∀ i : ℕ, ∫⁻ x, ENNReal.ofReal (d i x) ∂μ = 1)
    (hh_mass : ∫⁻ x, ENNReal.ofReal (h x) ∂μ = 1)
    (hconv : ∀ᵐ x ∂μ, Filter.Tendsto (fun i : ℕ => d i x) Filter.atTop (nhds (h x))),
    ∀ (φ : α → ℝ), Continuous φ → (∃ B : ℝ, ∀ x : α, |φ x| ≤ B) →
      Filter.Tendsto
        (fun i : ℕ => ∫ x, φ x ∂(μ.withDensity (fun x => ENNReal.ofReal (d i x))))
        Filter.atTop
        (nhds (∫ x, φ x ∂(μ.withDensity (fun x => ENNReal.ofReal (h x))))) := by
  /- @proof-region region.target-node.session.2e68201df8c01acd begin -/
  classical
  intro α _ _ _ μ d h hd_meas hd_nonneg hh_meas hh_nonneg hd_mass hh_mass hconv φ hcont hbdd
  obtain ⟨B₀, hB₀⟩ := hbdd
  have hB : ∀ x : α, |φ x| ≤ |B₀| := fun x => le_trans (hB₀ x) (le_abs_self B₀)
  have hint_d : ∀ i : ℕ, Integrable (d i) μ := by
    intro i
    refine ⟨(hd_meas i).aestronglyMeasurable, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal (hd_nonneg i), hd_mass i]
    exact ENNReal.one_lt_top
  have hint_h : Integrable h μ := by
    refine ⟨hh_meas.aestronglyMeasurable, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal hh_nonneg, hh_mass]
    exact ENNReal.one_lt_top
  have hmass_d : ∀ i : ℕ, ∫ x, d i x ∂μ = 1 := by
    intro i
    have h := Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.integral_eq_lintegral_toReal_of_nonneg (hd_nonneg i) (hint_d i)
    simpa [hd_mass i] using h
  have hmass_h : ∫ x, h x ∂μ = 1 := by
    have h := Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.integral_eq_lintegral_toReal_of_nonneg hh_nonneg hint_h
    simpa [hh_mass] using h
  have hconv_d : ∀ i : ℕ,
      ∫ x, φ x ∂(μ.withDensity (fun x => ENNReal.ofReal (d i x))) = ∫ x, d i x * φ x ∂μ := by
    intro i
    rw [integral_withDensity_eq_integral_toReal_smul₀]
    · apply MeasureTheory.integral_congr_ae
      filter_upwards [hd_nonneg i] with x hx
      simp only [ENNReal.toReal_ofReal hx, smul_eq_mul]
    · exact (hd_meas i).ennreal_ofReal
    · exact Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)
  have hconv_h : ∫ x, φ x ∂(μ.withDensity (fun x => ENNReal.ofReal (h x))) = ∫ x, h x * φ x ∂μ := by
    rw [integral_withDensity_eq_integral_toReal_smul₀]
    · apply MeasureTheory.integral_congr_ae
      filter_upwards [hh_nonneg] with x hx
      simp only [ENNReal.toReal_ofReal hx, smul_eq_mul]
    · exact hh_meas.ennreal_ofReal
    · exact Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)
  have hdiff : ∀ i : ℕ, ∫ x, (d i x - h x) ∂μ = 0 := by
    intro i
    rw [MeasureTheory.integral_sub (hint_d i) hint_h, hmass_d i, hmass_h]
    norm_num
  have hF_meas : ∀ i : ℕ, AEStronglyMeasurable (fun x : α => max (h x - d i x) 0) μ := by
    intro i
    exact ((hh_meas.sub (hd_meas i)).max aemeasurable_const).aestronglyMeasurable
  have hφbdd : ∀ᵐ x ∂μ, ‖φ x‖ ≤ |B₀| :=
    Filter.Eventually.of_forall (fun x => by simpa [Real.norm_eq_abs] using hB x)
  have hF_bound : ∀ i : ℕ, ∀ᵐ x ∂μ, ‖max (h x - d i x) 0‖ ≤ h x := by
    intro i
    filter_upwards [hd_nonneg i, hh_nonneg] with x hd hh
    have hdle : (0 : ℝ) ≤ d i x := by simpa using hd
    have hhle : (0 : ℝ) ≤ h x := by simpa using hh
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right (h x - d i x) 0)]
    exact max_le (by linarith) hhle
  have hF_conv : ∀ᵐ x ∂μ, Tendsto (fun i : ℕ => max (h x - d i x) 0) atTop (𝓝 0) := by
    filter_upwards [hconv] with x hx
    have hsub : Tendsto (fun i : ℕ => h x - d i x) atTop (𝓝 0) := by
      have h1 : Tendsto (fun i : ℕ => h x - d i x) atTop (𝓝 (h x - h x)) :=
        tendsto_const_nhds.sub hx
      simpa using h1
    have hcm : Continuous fun t : ℝ => max t 0 := continuous_id.max continuous_const
    simpa using (hcm.tendsto 0).comp hsub
  have hScheffe : Tendsto (fun i : ℕ => ∫ x, max (h x - d i x) 0 ∂μ) atTop (𝓝 0) := by
    have hdc := MeasureTheory.tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun i x => max (h x - d i x) 0) (f := fun _ => (0 : ℝ)) h hF_meas hint_h hF_bound hF_conv
    simpa using hdc
  have hpt : ∀ (i : ℕ) (x : α), |d i x - h x| = (d i x - h x) + 2 * max (h x - d i x) 0 := by
    intro i x
    by_cases hle : (0 : ℝ) ≤ d i x - h x
    · rw [max_eq_right (by linarith), abs_of_nonneg hle]
      ring
    · have hlt : d i x - h x < 0 := by linarith
      rw [max_eq_left (by linarith), abs_of_neg hlt]
      ring
  have hint_max : ∀ i : ℕ, Integrable (fun x : α => max (h x - d i x) 0) μ := by
    intro i
    refine Integrable.mono hint_h (hF_meas i) ?_
    filter_upwards [hF_bound i] with x hx
    calc ‖max (h x - d i x) 0‖ ≤ h x := hx
      _ = ‖h x‖ := by rw [Real.norm_eq_abs, abs_of_nonneg (le_trans (norm_nonneg _) hx)]
  have hform : ∀ i : ℕ, ∫ x, |d i x - h x| ∂μ = 2 * ∫ x, max (h x - d i x) 0 ∂μ := by
    intro i
    have h1 : ∫ x, ((d i x - h x) + 2 * max (h x - d i x) 0) ∂μ
        = ∫ x, (d i x - h x) ∂μ + ∫ x, 2 * max (h x - d i x) 0 ∂μ :=
      MeasureTheory.integral_add ((hint_d i).sub hint_h) ((hint_max i).const_mul 2)
    have h2 : ∫ x, (d i x - h x) ∂μ + ∫ x, 2 * max (h x - d i x) 0 ∂μ
        = 0 + 2 * ∫ x, max (h x - d i x) 0 ∂μ := by
      rw [hdiff i, MeasureTheory.integral_const_mul]
    calc ∫ x, |d i x - h x| ∂μ
        = ∫ x, ((d i x - h x) + 2 * max (h x - d i x) 0) ∂μ := by
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall (fun x => hpt i x)
      _ = ∫ x, (d i x - h x) ∂μ + ∫ x, 2 * max (h x - d i x) 0 ∂μ := h1
      _ = 2 * ∫ x, max (h x - d i x) 0 ∂μ := by
          rw [h2]
          ring
  have hL1 : Tendsto (fun i : ℕ => ∫ x, |d i x - h x| ∂μ) atTop (𝓝 0) := by
    have h2 : Tendsto (fun i : ℕ => 2 * ∫ x, max (h x - d i x) 0 ∂μ) atTop (𝓝 0) := by
      have h := hScheffe.const_mul 2
      simpa using h
    simpa only [hform] using h2
  have hstep : Tendsto (fun i : ℕ => ∫ x, φ x * (d i x - h x) ∂μ) atTop (𝓝 0) := by
    have hle : ∀ i : ℕ, ‖∫ x, φ x * (d i x - h x) ∂μ‖ ≤ |B₀| * ∫ x, |d i x - h x| ∂μ := by
      intro i
      have hg : Integrable (fun x : α => φ x * (d i x - h x)) μ :=
        ((hint_d i).sub hint_h).bdd_mul hcont.aestronglyMeasurable hφbdd
      have h1 : Integrable (fun x : α => ‖φ x * (d i x - h x)‖) μ := hg.norm
      have h2 : Integrable (fun x : α => |B₀| * |d i x - h x|) μ := by
        have h3 := ((hint_d i).sub hint_h).norm
        simpa using h3.const_mul |B₀|
      have h4 : ∀ᵐ x ∂μ, ‖φ x * (d i x - h x)‖ ≤ |B₀| * |d i x - h x| := by
        apply Filter.Eventually.of_forall
        intro x
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hB x) (abs_nonneg _)
      calc ‖∫ x, φ x * (d i x - h x) ∂μ‖
          ≤ ∫ x, ‖φ x * (d i x - h x)‖ ∂μ :=
            MeasureTheory.norm_integral_le_integral_norm (fun x => φ x * (d i x - h x))
        _ ≤ ∫ x, |B₀| * |d i x - h x| ∂μ := MeasureTheory.integral_mono_ae h1 h2 h4
        _ = |B₀| * ∫ x, |d i x - h x| ∂μ := MeasureTheory.integral_const_mul |B₀| _
    have hglim : Tendsto (fun i : ℕ => |B₀| * ∫ x, |d i x - h x| ∂μ) atTop (𝓝 0) := by
      have h := hL1.const_mul |B₀|
      simpa using h
    have hsq : Tendsto
        (fun i : ℕ => ∫ x, φ x * (d i x - h x) ∂μ + |B₀| * ∫ x, |d i x - h x| ∂μ)
        atTop (𝓝 0) := by
      have hnn : ∀ i : ℕ, 0 ≤ ∫ x, φ x * (d i x - h x) ∂μ + |B₀| * ∫ x, |d i x - h x| ∂μ := by
        intro i
        have hab := abs_le.mp (by simpa using hle i)
        linarith [hab.1]
      have hle2 : ∀ i : ℕ,
          ∫ x, φ x * (d i x - h x) ∂μ + |B₀| * ∫ x, |d i x - h x| ∂μ
            ≤ 2 * (|B₀| * ∫ x, |d i x - h x| ∂μ) := by
        intro i
        have hab := abs_le.mp (by simpa using hle i)
        linarith [hab.2]
      have h2g : Tendsto (fun i : ℕ => 2 * (|B₀| * ∫ x, |d i x - h x| ∂μ)) atTop (𝓝 0) := by
        have h := hglim.const_mul 2
        simpa using h
      exact squeeze_zero hnn hle2 h2g
    have hlast : Tendsto
        (fun i : ℕ => (∫ x, φ x * (d i x - h x) ∂μ + |B₀| * ∫ x, |d i x - h x| ∂μ)
          - |B₀| * ∫ x, |d i x - h x| ∂μ) atTop (𝓝 (0 - 0)) :=
      hsq.sub hglim
    simpa using hlast
  have hswap : ∀ i : ℕ, ∫ x, d i x * φ x ∂μ = ∫ x, φ x * d i x ∂μ := by
    intro i
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => (mul_comm (φ x) (d i x)).symm)
  have hswap' : ∫ x, h x * φ x ∂μ = ∫ x, φ x * h x ∂μ := by
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => mul_comm (h x) (φ x))
  have hmain : Tendsto (fun i : ℕ => ∫ x, φ x * d i x ∂μ) atTop (𝓝 (∫ x, φ x * h x ∂μ)) := by
    have hintφd : ∀ i : ℕ, Integrable (fun x : α => φ x * d i x) μ := fun i =>
      (hint_d i).bdd_mul hcont.aestronglyMeasurable hφbdd
    have hintφh : Integrable (fun x : α => φ x * h x) μ :=
      hint_h.bdd_mul hcont.aestronglyMeasurable hφbdd
    have hsub : ∀ i : ℕ,
        ∫ x, φ x * (d i x - h x) ∂μ = ∫ x, φ x * d i x ∂μ - ∫ x, φ x * h x ∂μ := by
      intro i
      have h1 : ∫ x, (φ x * d i x - φ x * h x) ∂μ
          = ∫ x, φ x * d i x ∂μ - ∫ x, φ x * h x ∂μ :=
        MeasureTheory.integral_sub (hintφd i) hintφh
      rw [← h1]
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by ring)
    have h0 : Tendsto
        (fun i : ℕ => ∫ x, φ x * d i x ∂μ - ∫ x, φ x * h x ∂μ) atTop (𝓝 0) := by
      simpa only [hsub] using hstep
    have h2 : Tendsto
        (fun i : ℕ => (∫ x, φ x * d i x ∂μ - ∫ x, φ x * h x ∂μ) + ∫ x, φ x * h x ∂μ)
        atTop (𝓝 (0 + ∫ x, φ x * h x ∂μ)) :=
      h0.add tendsto_const_nhds
    simpa using h2
  have hgoal : Tendsto (fun i : ℕ => ∫ x, d i x * φ x ∂μ) atTop (𝓝 (∫ x, h x * φ x ∂μ)) := by
    have h1 : Tendsto (fun i : ℕ => ∫ x, d i x * φ x ∂μ) atTop (𝓝 (∫ x, φ x * h x ∂μ)) := by
      simpa only [hswap] using hmain
    simpa only [hswap'] using h1
  simpa only [hconv_d, hconv_h] using hgoal
  /- @proof-region region.target-node.session.2e68201df8c01acd end -/

end Statlib.Imported


end OfflineCorrectedDP


/- Genuine source ProverJobs.job_paper_80f79a059f3741e883a5b36dc8747f99.ProvedNodes.Node_3732645458_2f14fac8_4fa6aa4b; namespace isolation only; retained external axioms remain explicit. -/

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
theorem statopia_math_node_3732645458_2f14fac8 : ∀ {X : Type*} [MeasurableSpace X] [MetricSpace X] [BorelSpace X]
    (μ : Measure X) (P0 : Measure X) (hP0 : IsProbabilityMeasure P0)
    (d : ℕ → X → ℝ) (h : X → ℝ)
    (hd_meas : ∀ i : ℕ, AEMeasurable (d i) μ)
    (hd_nonneg : ∀ i : ℕ, 0 ≤ᵐ[μ] d i)
    (hh_meas : AEMeasurable h μ)
    (hh_nonneg : 0 ≤ᵐ[μ] h)
    (hd_mass : ∀ i : ℕ, ∫⁻ x, ENNReal.ofReal (d i x) ∂μ = 1)
    (hh_mass : ∫⁻ x, ENNReal.ofReal (h x) ∂μ = 1)
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun i : ℕ => d i x) atTop (𝓝 (h x)))
    (hweak : ∀ (φ : X → ℝ), Continuous φ → (∃ B : ℝ, ∀ x : X, |φ x| ≤ B) →
      Tendsto (fun i : ℕ => ∫ x, φ x ∂(μ.withDensity (fun x => ENNReal.ofReal (d i x))))
        atTop (𝓝 (∫ x, φ x ∂P0))),
    P0 = μ.withDensity (fun x : X => ENNReal.ofReal (h x)) := by
  /- @proof-region region.target-node.session.7faa4fc44e04d633 begin -/
  intro X _ _ _ μ P0 hP0 d h hd_meas hd_nonneg hh_meas hh_nonneg hd_mass hh_mass hconv hweak
  have hν_prob : IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (h x))) := by
    constructor
    rw [MeasureTheory.withDensity_apply (fun x => ENNReal.ofReal (h x)) MeasurableSet.univ]
    simpa using hh_mass
  haveI : IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (h x))) := hν_prob
  have hkey : ∀ (φ : X → ℝ), Continuous φ → (∃ B : ℝ, ∀ x : X, |φ x| ≤ B) →
      ∫ x, φ x ∂P0 = ∫ x, φ x ∂(μ.withDensity (fun x => ENNReal.ofReal (h x))) := by
    intro φ hφ hbdd
    refine tendsto_nhds_unique (hweak φ hφ hbdd) ?_
    exact statopia_math_node_2077380816_7e90d538 μ d h hd_meas hd_nonneg hh_meas hh_nonneg
      hd_mass hh_mass hconv φ hφ hbdd
  refine MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure (μ := P0)
    (ν := μ.withDensity (fun x => ENNReal.ofReal (h x))) (fun φ => ?_)
  have hcont : Continuous (φ : X → ℝ) := φ.continuous
  have hbdd : ∃ B : ℝ, ∀ x : X, |φ x| ≤ B :=
    ⟨‖φ‖, fun x => by simpa [Real.norm_eq_abs] using BoundedContinuousFunction.norm_coe_le_norm φ x⟩
  exact hkey (φ : X → ℝ) hcont hbdd
  /- @proof-region region.target-node.session.7faa4fc44e04d633 end -/

end Statlib.Imported


end OfflineCorrectedDP


/- Genuine source ProverJobs.job_paper_80f79a059f3741e883a5b36dc8747f99.ProvedNodes.Node_908059601_53fbebb9_445c7d97; namespace isolation only; retained external axioms remain explicit. -/

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
theorem statopia_math_node_908059601_53fbebb9 : ∀ {Θ : Type*} [MetricSpace Θ]
    (C : Set Θ) (s : ℕ)
    (qseq : ℕ → Fin s → ℝ) (thseq : ℕ → Fin s → Θ)
    (hC : IsCompact C)
    (hq_nonneg : ∀ (i : ℕ) (j : Fin s), 0 ≤ qseq i j)
    (hq_sum : ∀ i : ℕ, ∑ j : Fin s, qseq i j = 1)
    (hliminf : ∀ j : Fin s, 0 < Filter.liminf (fun i : ℕ => qseq i j) atTop)
    (hth_mem : ∀ (i : ℕ) (j : Fin s), thseq i j ∈ C),
    ∃ (φ : ℕ → ℕ) (qb : Fin s → ℝ) (thb : Fin s → Θ),
      StrictMono φ ∧
      (∀ j : Fin s, 0 < qb j) ∧
      (∑ j : Fin s, qb j = 1) ∧
      (∀ j : Fin s, thb j ∈ C) ∧
      (∀ j : Fin s, Tendsto (fun i : ℕ => qseq (φ i) j) atTop (𝓝 (qb j))) ∧
      (∀ j : Fin s, Tendsto (fun i : ℕ => thseq (φ i) j) atTop (𝓝 (thb j))) := by
  /- @proof-region region.target-node.session.21644d7771c46702 begin -/
  intro Θ instΘ C s qseq thseq hC hq_nonneg hq_sum hliminf hth_mem
  classical
  rcases Nat.eq_zero_or_pos s with hs0 | _hspos
  · subst hs0
    exact absurd (hq_sum 0) (by simp)
  have hKc : IsCompact (Set.pi Set.univ (fun _ : Fin s => Set.Icc (0 : ℝ) 1) ×ˢ
      Set.pi Set.univ (fun _ : Fin s => C)) := by
    refine IsCompact.prod ?_ ?_
    · exact isCompact_univ_pi (fun _ => isCompact_Icc)
    · exact isCompact_univ_pi (fun _ => hC)
  have hmem : ∀ i : ℕ, ((qseq i, thseq i) : (Fin s → ℝ) × (Fin s → Θ)) ∈
      (Set.pi Set.univ (fun _ : Fin s => Set.Icc (0 : ℝ) 1) ×ˢ
        Set.pi Set.univ (fun _ : Fin s => C)) := by
    intro i
    refine ⟨?_, ?_⟩
    · intro j _
      exact ⟨hq_nonneg i j, by
        have hle : qseq i j ≤ ∑ k : Fin s, qseq i k :=
          Finset.single_le_sum (fun k _ => hq_nonneg i k) (Finset.mem_univ j)
        linarith [hq_sum i]⟩
    · intro j _
      exact hth_mem i j
  obtain ⟨⟨qb, thb⟩, haK, φ, hφmono, hconv⟩ :=
    hKc.tendsto_subseq (x := fun i : ℕ => ((qseq i, thseq i) : (Fin s → ℝ) × (Fin s → Θ))) hmem
  have hqlim : Tendsto (fun i : ℕ => qseq (φ i)) atTop (𝓝 qb) := by
    have h1 : Tendsto (fun p : (Fin s → ℝ) × (Fin s → Θ) => p.1) (𝓝 (qb, thb)) (𝓝 qb) :=
      continuous_fst.tendsto (qb, thb)
    exact h1.comp hconv
  have hthlim : Tendsto (fun i : ℕ => thseq (φ i)) atTop (𝓝 thb) := by
    have h1 : Tendsto (fun p : (Fin s → ℝ) × (Fin s → Θ) => p.2) (𝓝 (qb, thb)) (𝓝 thb) :=
      continuous_snd.tendsto (qb, thb)
    exact h1.comp hconv
  have hqconv : ∀ j : Fin s, Tendsto (fun i : ℕ => qseq (φ i) j) atTop (𝓝 (qb j)) := by
    intro j
    exact ((continuous_apply j).tendsto qb).comp hqlim
  have hthconv : ∀ j : Fin s, Tendsto (fun i : ℕ => thseq (φ i) j) atTop (𝓝 (thb j)) := by
    intro j
    exact ((continuous_apply j).tendsto thb).comp hthlim
  have hsum1 : (∑ j : Fin s, qb j) = 1 := by
    have hcont : Continuous (fun q : Fin s → ℝ => ∑ j : Fin s, q j) := by
      simpa using continuous_finset_sum (s := (Finset.univ : Finset (Fin s)))
        (f := fun (j : Fin s) (q : Fin s → ℝ) => q j) (fun j _ => continuous_apply j)
    have hsum_tendsto : Tendsto (fun i : ℕ => ∑ j : Fin s, qseq (φ i) j) atTop
        (𝓝 (∑ j : Fin s, qb j)) := hcont.tendsto qb |>.comp hqlim
    have hconst : Tendsto (fun i : ℕ => ∑ j : Fin s, qseq (φ i) j) atTop (𝓝 (1 : ℝ)) := by
      have heq : (fun i : ℕ => ∑ j : Fin s, qseq (φ i) j) = fun _ => (1 : ℝ) := by
        funext i
        exact hq_sum (φ i)
      rw [heq]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hsum_tendsto hconst
  have hthC : ∀ j : Fin s, thb j ∈ C := by
    intro j
    exact haK.2 j (Set.mem_univ j)
  have hpos : ∀ j : Fin s, 0 < qb j := by
    intro j
    have hneS : ({a : ℝ | ∀ᶠ i in atTop, a ≤ qseq i j}).Nonempty :=
      ⟨0, by filter_upwards with i; exact hq_nonneg i j⟩
    have hkey : (0 : ℝ) < sSup {a : ℝ | ∀ᶠ i in atTop, a ≤ qseq i j} := hliminf j
    obtain ⟨c, hc_mem, hc_pos⟩ : ∃ c : ℝ, (∀ᶠ i in atTop, c ≤ qseq i j) ∧ 0 < c := by
      refine Classical.byContradiction fun hcon => ?_
      have hbdd : sSup {a : ℝ | ∀ᶠ i in atTop, a ≤ qseq i j} ≤ 0 := by
        refine csSup_le hneS ?_
        intro b hb
        exact le_of_not_gt fun hb0 => hcon ⟨b, hb, hb0⟩
      linarith
    have hφge : ∀ n : ℕ, n ≤ φ n := by
      intro n
      induction n with
      | zero => exact Nat.zero_le _
      | succ k ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hφmono (Nat.lt_succ_self k)))
    have hev : ∀ᶠ i in atTop, c ≤ qseq (φ i) j := by
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hc_mem
      exact Filter.eventually_atTop.2 ⟨N, fun i hi => hN (φ i) (le_trans hi (hφge i))⟩
    exact lt_of_lt_of_le hc_pos (le_of_tendsto_of_tendsto tendsto_const_nhds (hqconv j) hev)
  exact ⟨φ, qb, thb, hφmono, hpos, hsum1, hthC, hqconv, hthconv⟩
  /- @proof-region region.target-node.session.21644d7771c46702 end -/

end Statlib.Imported


end OfflineCorrectedDP


/- Genuine source ProverJobs.job_paper_80f79a059f3741e883a5b36dc8747f99.ExternalNodes.Node_f9016d0889b0c03e9436; namespace isolation only; retained external axioms remain explicit. -/

namespace OfflineCorrectedDP

-- External DAG node: ext_model_5 (AXIOM)
example : Prop := (open MeasureTheory ProbabilityTheory Filter Topology in (open scoped ENNReal in (∀ (Ω : Type*) [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [PolishSpace Ω]
    (φ : ProbabilityMeasure Ω) (φi : ℕ → ProbabilityMeasure Ω) (k : ℕ)
    (hweak : ∀ f : Ω → ℝ, Continuous f → (∃ B : ℝ, ∀ x : Ω, |f x| ≤ B) →
      Tendsto (fun i => ∫ x, f x ∂(φi i : Measure Ω)) atTop (𝓝 (∫ x, f x ∂(φ : Measure Ω))))
    (hsupp : ∀ i : ℕ, (Measure.support (φi i : Measure Ω)).encard ≤ (k : ℕ∞)),
    (Measure.support (φ : Measure Ω)).encard ≤ (k : ℕ∞))))
axiom ext_model_5 : (open MeasureTheory ProbabilityTheory Filter Topology in (open scoped ENNReal in (∀ (Ω : Type*) [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [PolishSpace Ω]
    (φ : ProbabilityMeasure Ω) (φi : ℕ → ProbabilityMeasure Ω) (k : ℕ)
    (hweak : ∀ f : Ω → ℝ, Continuous f → (∃ B : ℝ, ∀ x : Ω, |f x| ≤ B) →
      Tendsto (fun i => ∫ x, f x ∂(φi i : Measure Ω)) atTop (𝓝 (∫ x, f x ∂(φ : Measure Ω))))
    (hsupp : ∀ i : ℕ, (Measure.support (φi i : Measure Ω)).encard ≤ (k : ℕ∞)),
    (Measure.support (φ : Measure Ω)).encard ≤ (k : ℕ∞))))


end OfflineCorrectedDP


/- Genuine source ProverJobs.job_paper_80f79a059f3741e883a5b36dc8747f99.ProvedNodes.Node_1347167438_985a96d2_671270a4; namespace isolation only; retained external axioms remain explicit. -/

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
theorem statopia_math_node_1347167438_985a96d2 : ∀ {X Θ : Type*} [MeasurableSpace X] [MeasurableSpace Θ]
    [MetricSpace X] [BorelSpace X] [CompleteSpace X] [SecondCountableTopology X]
    [MetricSpace Θ] [BorelSpace Θ] [PolishSpace Θ]
    (M : DPMModel X Θ) (s : ℕ) (hs : 1 ≤ s)
    (qseq : ℕ → Fin s → ℝ) (thseq : ℕ → Fin s → Θ)
    (hq_pos : ∀ (i : ℕ) (j : Fin s), 0 < qseq i j)
    (hq_sum : ∀ (i : ℕ), ∑ j : Fin s, qseq i j = 1)
    (hth_inj : ∀ (i : ℕ), Function.Injective (thseq i))
    (hth_mem : ∀ (i : ℕ) (j : Fin s), thseq i j ∈ M.Θset)
    (P0 : Measure X) (hP0_prob : IsProbabilityMeasure P0)
    (hweak : ∀ φ : X → ℝ, Continuous φ → (∃ B : ℝ, ∀ x : X, |φ x| ≤ B) →
      Tendsto (fun i : ℕ => ∫ x, φ x ∂(mixtureMeasure M (qseq i) (thseq i))) atTop
        (𝓝 (∫ x, φ x ∂P0)))
    (hliminf : ∀ j : Fin s, 0 < Filter.liminf (fun i : ℕ => qseq i j) atTop)
    (hcompact : ∃ C : Set Θ, IsCompact C ∧ (∀ (i : ℕ) (j : Fin s), thseq i j ∈ C) ∧
      C ∩ closure M.Θset ⊆ M.Θset \ singularBoundary M)
    (hcont : ∀ theta_bar ∈ M.Θset, theta_bar ∉ singularBoundary M →
      ∃ N : Set X, M.μ N = 0 ∧ ∀ x : X, x ∉ N →
        ∃ A : Set Θ, A ∈ 𝓝 theta_bar ∧ A ⊆ M.Θset \ singularBoundary M ∧
          ContinuousOn (fun th : Θ => M.kdens th x) A),
    ∃ (qb : Fin s → ℝ) (thb : Fin s → Θ),
      (∀ j : Fin s, 0 < qb j) ∧ (∑ j : Fin s, qb j = 1) ∧
      (∀ j : Fin s, thb j ∈ M.Θset \ singularBoundary M) ∧
      P0 = M.μ.withDensity (fun x : X => ENNReal.ofReal (mixDens M qb thb x)) := by
  /- @proof-region region.target-node.session.ad4fe9bbccc5f16f begin -/
  intros
  rename_i M s hs qseq thseq hq_pos hq_sum hth_inj hth_mem P0 hP0_prob hweak hliminf hcompact hcont
  obtain ⟨C, hC_compact, hC_mem, hC_sep⟩ := hcompact
  obtain ⟨ψ, qb, thb, hψ_mono, hqb_pos, hqb_sum, hthb_C, hqb_tend, hthb_tend⟩ :=
    statopia_math_node_908059601_53fbebb9 C s qseq thseq hC_compact
      (fun i j => le_of_lt (hq_pos i j)) hq_sum hliminf hC_mem
  have hthb_clos : ∀ j : Fin s, thb j ∈ closure M.Θset := by
    intro j
    by_contra hmem
    have hopen : IsOpen (closure M.Θset)ᶜ := isClosed_closure.isOpen_compl
    have hnhds : (closure M.Θset)ᶜ ∈ 𝓝 (thb j) := hopen.mem_nhds (by simpa using hmem)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ((hthb_tend j).eventually hnhds)
    exact hN N le_rfl (subset_closure (hth_mem (ψ N) j))
  have hthb_off : ∀ j : Fin s, thb j ∈ M.Θset \ singularBoundary M :=
    fun j => hC_sep ⟨hthb_C j, hthb_clos j⟩
  obtain ⟨hconv, hlim_meas⟩ :=
    statopia_math_node_2713798316_cec71e42 M s qb thb hthb_off
      (fun i j => qseq (ψ i) j) (fun i j => thseq (ψ i) j) hqb_tend hthb_tend hcont
  have hmix_meas : ∀ (n : ℕ) (q : Fin n → ℝ) (θ : Fin n → _),
      Measurable (fun x => mixDens M q θ x) := by
    intro n q θ
    have hk : ∀ j : Fin n, Measurable (fun x => M.kdens (θ j) x) :=
      fun j => M.hk_meas.comp (measurable_const.prodMk measurable_id)
    have h : Measurable (fun x => ∑ j : Fin n, q j * M.kdens (θ j) x) := by
      have hterm : ∀ j ∈ (Finset.univ : Finset (Fin n)),
          Measurable (fun x => q j * M.kdens (θ j) x) :=
        fun j _ => (hk j).const_mul (q j)
      simpa using Finset.measurable_sum (Finset.univ : Finset (Fin n)) hterm
    simpa [mixDens] using h
  have hnonneg : ∀ (n : ℕ) (q : Fin n → ℝ) (θ : Fin n → _), (∀ j, 0 < q j) →
      0 ≤ᵐ[M.μ] (fun x => mixDens M q θ x) := by
    intro n q θ hq
    refine Filter.Eventually.of_forall (fun x => ?_)
    have h : 0 ≤ ∑ j : Fin n, q j * M.kdens (θ j) x :=
      Finset.sum_nonneg fun j _ => mul_nonneg (le_of_lt (hq j)) (M.kdens_nonneg (θ j) x)
    simpa [mixDens] using h
  have hmix_eq : ∀ i : ℕ, mixtureMeasure M (fun j => qseq (ψ i) j) (fun j => thseq (ψ i) j)
      = M.μ.withDensity
          (fun x => ENNReal.ofReal (mixDens M (fun j => qseq (ψ i) j) (fun j => thseq (ψ i) j) x)) :=
    fun i => (statopia_math_node_2986921194_82fe1497 M s hs (fun j => qseq (ψ i) j)
      (fun j => thseq (ψ i) j) (fun j => hq_pos (ψ i) j) (hq_sum (ψ i))
      (fun j => M.kdens_prob (thseq (ψ i) j))).1
  have hmass : ∀ i : ℕ,
      ∫⁻ x, ENNReal.ofReal
        (mixDens M (fun j => qseq (ψ i) j) (fun j => thseq (ψ i) j) x) ∂M.μ = 1 := by
    intro i
    have hmain := statopia_math_node_2986921194_82fe1497 M s hs (fun j => qseq (ψ i) j)
      (fun j => thseq (ψ i) j) (fun j => hq_pos (ψ i) j) (hq_sum (ψ i))
      (fun j => M.kdens_prob (thseq (ψ i) j))
    have huniv : (M.μ.withDensity
        (fun x => ENNReal.ofReal
          (mixDens M (fun j => qseq (ψ i) j) (fun j => thseq (ψ i) j) x))) Set.univ = 1 := by
      rw [← hmain.1]
      exact hmain.2.1.measure_univ
    rw [← huniv, MeasureTheory.withDensity_apply _ MeasurableSet.univ]
    simp
  have hmass_lim : ∫⁻ x, ENNReal.ofReal (mixDens M qb thb x) ∂M.μ = 1 := by
    have hmain := statopia_math_node_2986921194_82fe1497 M s hs qb thb hqb_pos hqb_sum
      (fun j => M.kdens_prob (thb j))
    have huniv : (M.μ.withDensity (fun x => ENNReal.ofReal (mixDens M qb thb x))) Set.univ = 1 := by
      rw [← hmain.1]
      exact hmain.2.1.measure_univ
    rw [← huniv, MeasureTheory.withDensity_apply _ MeasurableSet.univ]
    simp
  have hfinal :=
    statopia_math_node_3732645458_2f14fac8 M.μ P0 hP0_prob
      (fun i x => mixDens M (fun j => qseq (ψ i) j) (fun j => thseq (ψ i) j) x)
      (fun x => mixDens M qb thb x)
      (fun i => (hmix_meas s (fun j => qseq (ψ i) j) (fun j => thseq (ψ i) j)).aemeasurable)
      (fun i => hnonneg s (fun j => qseq (ψ i) j) (fun j => thseq (ψ i) j) (fun j => hq_pos (ψ i) j))
      hlim_meas
      (hnonneg s qb thb (fun j => hqb_pos j))
      hmass hmass_lim hconv
      (fun φ hφc hφb => by
        have heqfun : (fun i : ℕ => ∫ x, φ x ∂(M.μ.withDensity
              (fun x => ENNReal.ofReal
                (mixDens M (fun j => qseq (ψ i) j) (fun j => thseq (ψ i) j) x))))
            = fun i : ℕ => ∫ x, φ x ∂(mixtureMeasure M (fun j => qseq (ψ i) j) (fun j => thseq (ψ i) j)) := by
          funext i
          rw [hmix_eq i]
        show Tendsto (fun i : ℕ => ∫ x, φ x ∂(M.μ.withDensity
          (fun x => ENNReal.ofReal
            (mixDens M (fun j => qseq (ψ i) j) (fun j => thseq (ψ i) j) x))))
          atTop (𝓝 (∫ x, φ x ∂P0))
        rw [heqfun]
        exact (hweak φ hφc hφb).comp hψ_mono.tendsto_atTop)
  exact ⟨qb, thb, hqb_pos, hqb_sum, hthb_off, hfinal⟩
  /- @proof-region region.target-node.session.ad4fe9bbccc5f16f end -/

end Statlib.Imported


end OfflineCorrectedDP


/- Genuine source ProverJobs.job_paper_80f79a059f3741e883a5b36dc8747f99.ProvedNodes.Node_2415940998_78aaa9b9_530a0a98; namespace isolation only; retained external axioms remain explicit. -/

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
theorem statopia_math_node_2415940998_78aaa9b9 : ∀ {X Θ : Type*} [MeasurableSpace X] [MeasurableSpace Θ]
    [MetricSpace X] [BorelSpace X] [MeasureSpace X]
    [TopologicalSpace.SeparableSpace X]
    [TopologicalSpace Θ] [StandardBorelSpace Θ]
    (M : DPMModel X Θ) (s : ℕ) (hs : 1 ≤ s)
    (P0 : Measure X) (hP0 : IsProbabilityMeasure P0)
    (hclos_s : (⟨P0, hP0⟩ : ProbabilityMeasure X) ∈
      closure {ν : ProbabilityMeasure X |
        ∃ (q : Fin s → ℝ) (θ : Fin s → Θ),
          (∀ j : Fin s, 0 < q j) ∧ (∑ j : Fin s, q j = 1) ∧
          Function.Injective θ ∧ (∀ j : Fin s, θ j ∈ M.Θset) ∧
          (ν : Measure X) = mixtureMeasure M q θ}),
    ∃ (s' : ℕ) (q : ℕ → Fin s' → ℝ) (θ : ℕ → Fin s' → Θ),
      1 ≤ s' ∧ s' ≤ s ∧
      (∀ i : ℕ,
        (∀ j : Fin s', 0 < q i j) ∧ (∑ j : Fin s', q i j = 1) ∧
        Function.Injective (θ i) ∧ (∀ j : Fin s', θ i j ∈ M.Θset) ∧
        IsProbabilityMeasure (mixtureMeasure M (q i) (θ i))) ∧
      (∀ j : Fin s', 0 < Filter.liminf (fun i : ℕ => q i j) atTop) ∧
      WeakTendsto (fun i : ℕ => mixtureMeasure M (q i) (θ i)) P0 := by
  /- @proof-region region.target-node.session.f4cfe9ea42253c87 begin -/
  intro X Θ _ _ _ _ _ _ _ _ M s hs P0 hP0 hclos_s
  classical
  haveI hmet : TopologicalSpace.MetrizableSpace (ProbabilityMeasure X) :=
    MeasureTheory.instMetrizableSpaceProbabilityMeasure X
  haveI hfc : FirstCountableTopology (ProbabilityMeasure X) := inferInstance
  have hclos : (⟨P0, hP0⟩ : ProbabilityMeasure X) ∈
      closure {ν : ProbabilityMeasure X |
        ∃ (q : Fin s → ℝ) (θ : Fin s → Θ),
          (∀ j : Fin s, 0 < q j) ∧ (∑ j : Fin s, q j = 1) ∧
            Function.Injective θ ∧ (∀ j : Fin s, θ j ∈ M.Θset) ∧
              (ν : Measure X) = mixtureMeasure M q θ} := hclos_s
  obtain ⟨u, huG, hutend⟩ :
      ∃ u : ℕ → ProbabilityMeasure X,
        (∀ i : ℕ, u i ∈ {ν : ProbabilityMeasure X |
          ∃ (q : Fin s → ℝ) (θ : Fin s → Θ),
            (∀ j : Fin s, 0 < q j) ∧ (∑ j : Fin s, q j = 1) ∧
              Function.Injective θ ∧ (∀ j : Fin s, θ j ∈ M.Θset) ∧
                (ν : Measure X) = mixtureMeasure M q θ}) ∧
          Tendsto u atTop (𝓝 ⟨P0, hP0⟩) := mem_closure_iff_seq_limit.mp hclos
  choose q θ hq using huG
  have hqpos : ∀ (i : ℕ) (j : Fin s), 0 < q i j := fun i => (hq i).1
  have hqsum : ∀ i : ℕ, ∑ j : Fin s, q i j = 1 := fun i => (hq i).2.1
  have hqinj : ∀ i : ℕ, Function.Injective (θ i) := fun i => (hq i).2.2.1
  have hqΘ : ∀ (i : ℕ) (j : Fin s), θ i j ∈ M.Θset := fun i => (hq i).2.2.2.1
  have hqeq : ∀ i : ℕ, (u i : Measure X) = mixtureMeasure M (q i) (θ i) :=
    fun i => (hq i).2.2.2.2
  have hweak : ∀ F : BoundedContinuousFunction X ℝ,
      Tendsto (fun i => ∫ x, F x ∂(mixtureMeasure M (q i) (θ i))) atTop (𝓝 (∫ x, F x ∂P0)) := by
    intro F
    have h := (MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hutend) F
    have heq : (fun i => ∫ x, F x ∂(mixtureMeasure M (q i) (θ i)))
        = fun i => ∫ x, F x ∂((u i : ProbabilityMeasure X) : Measure X) := by
      funext i
      rw [hqeq i]
    rw [heq]
    simpa using h
  have hsimplex : ∀ i : ℕ, q i ∈ stdSimplex ℝ (Fin s) :=
    fun i => ⟨fun j => (hqpos i j).le, hqsum i⟩
  obtain ⟨qstar, hqstar_mem, φ, hφmono, hqtend⟩ :=
    (isCompact_stdSimplex (Fin s)).tendsto_subseq hsimplex
  have hqstar_nonneg : ∀ j : Fin s, 0 ≤ qstar j := fun j => hqstar_mem.1 j
  have hqstar_sum : ∑ j : Fin s, qstar j = 1 := hqstar_mem.2
  have hqstar_tend : ∀ j : Fin s, Tendsto (fun k => q (φ k) j) atTop (𝓝 (qstar j)) := by
    intro j
    simpa using (tendsto_pi_nhds.mp hqtend) j
  let J : Finset (Fin s) := Finset.univ.filter (fun j => 0 < qstar j)
  have hJmem : ∀ j : Fin s, j ∈ J ↔ 0 < qstar j := by
    intro j
    simp [J]
  have hJsum : ∑ j ∈ J, qstar j = 1 := by
    rw [← hqstar_sum]
    refine Finset.sum_subset (Finset.subset_univ J) ?_
    intro j _ hj
    rw [hJmem] at hj
    exact le_antisymm (not_lt.mp hj) (hqstar_nonneg j)
  have hJne : J.Nonempty := by
    rcases Finset.eq_empty_or_nonempty J with h | h
    · rw [h, Finset.sum_empty] at hJsum
      exact absurd hJsum (by norm_num)
    · exact h
  let s' : ℕ := J.card
  have hs'1 : 1 ≤ s' := by
    simpa [s'] using Finset.card_pos.mpr hJne
  have hs'le : s' ≤ s := by
    simpa [s'] using Finset.card_le_univ J
  let e : Fin s' → Fin s := fun m => ((J.equivFin.symm m : ↥J) : Fin s)
  have he_mem : ∀ m : Fin s', e m ∈ J := fun m => (J.equivFin.symm m).2
  have he_inj : Function.Injective e := by
    intro m1 m2 h
    have h' : (J.equivFin.symm m1 : ↥J) = (J.equivFin.symm m2 : ↥J) := Subtype.ext h
    exact (J.equivFin.symm).injective h'
  have hsum_e : ∀ f : Fin s → ℝ, (∑ m : Fin s', f (e m)) = ∑ j ∈ J, f j := by
    intro f
    have h1 : (∑ m : Fin s', f (e m)) = ∑ x : ↥J, f (x : Fin s) := by
      simpa [e] using Equiv.sum_comp J.equivFin.symm (fun x : ↥J => f (x : Fin s))
    have h2 : (∑ x : ↥J, f (x : Fin s)) = ∑ j ∈ J, f j := by
      simpa [Finset.univ_eq_attach] using Finset.sum_attach J f
    rw [h1, h2]
  let S : ℕ → ℝ := fun k => ∑ m : Fin s', q (φ k) (e m)
  have hS_eq : ∀ k, S k = ∑ j ∈ J, q (φ k) j := fun k => hsum_e (q (φ k))
  have hStend : Tendsto S atTop (𝓝 1) := by
    have h2 : Tendsto (fun k => ∑ j ∈ J, q (φ k) j) atTop (𝓝 (∑ j ∈ J, qstar j)) :=
      tendsto_finset_sum J (fun j _ => hqstar_tend j)
    rw [hJsum] at h2
    exact (tendsto_congr hS_eq).mpr h2
  have hSpos : ∀ k, 0 < S k := by
    intro k
    rw [hS_eq k]
    exact Finset.sum_pos (fun j _ => hqpos (φ k) j) hJne
  let q' : ℕ → Fin s' → ℝ := fun k m => q (φ k) (e m) / S k
  let θ' : ℕ → Fin s' → Θ := fun k m => θ (φ k) (e m)
  have hq'pos : ∀ k m, 0 < q' k m :=
    fun k m => div_pos (hqpos (φ k) (e m)) (hSpos k)
  have hq'sum : ∀ k, ∑ m : Fin s', q' k m = 1 := by
    intro k
    have h1 : (∑ m : Fin s', q' k m) = (∑ m : Fin s', q (φ k) (e m)) / S k :=
      (Finset.sum_div ..).symm
    rw [h1]
    rw [show (∑ m : Fin s', q (φ k) (e m)) = S k from rfl]
    exact div_self (hSpos k).ne'
  have hθ'inj : ∀ k, Function.Injective (θ' k) := by
    intro k m1 m2 h
    exact he_inj (hqinj (φ k) h)
  have hθ'Θ : ∀ k m, θ' k m ∈ M.Θset := fun k m => hqΘ (φ k) (e m)
  have hprob : ∀ k, IsProbabilityMeasure (mixtureMeasure M (q' k) (θ' k)) := by
    intro k
    exact (statopia_math_node_2986921194_82fe1497 M s' hs'1 (q' k) (θ' k) (hq'pos k) (hq'sum k)
      (fun j => M.kdens_prob (θ' k j))).2.1
  have hliminf : ∀ m : Fin s', 0 < liminf (fun k => q' k m) atTop := by
    intro m
    have hnum : Tendsto (fun k => q (φ k) (e m)) atTop (𝓝 (qstar (e m))) := hqstar_tend (e m)
    have ht : Tendsto (fun k => q' k m) atTop (𝓝 (qstar (e m))) := by
      have h2 := hnum.div hStend one_ne_zero
      simpa [q', div_one] using h2
    rw [ht.liminf_eq]
    exact (hJmem (e m)).mp (he_mem m)
  have hsub : ∀ F : BoundedContinuousFunction X ℝ,
      Tendsto (fun k => ∫ x, F x ∂(mixtureMeasure M (q (φ k)) (θ (φ k)))) atTop (𝓝 (∫ x, F x ∂P0)) := by
    intro F
    exact (hweak F).comp hφmono.tendsto_atTop
  refine ⟨s', q', θ', hs'1, hs'le, fun i => ⟨hq'pos i, hq'sum i, hθ'inj i, hθ'Θ i, hprob i⟩,
    hliminf, ?_⟩
  intro ψ hψ hbdd
  obtain ⟨B, hB⟩ := hbdd
  set C : ℝ := |B| with hCdef
  have hCnonneg : 0 ≤ C := by rw [hCdef]; exact abs_nonneg B
  have hCbnd : ∀ x : X, |ψ x| ≤ C := fun x => by
    rw [hCdef]; exact le_trans (hB x) (le_abs_self B)
  have hkerprob : ∀ (k : ℕ) (j : Fin s), IsProbabilityMeasure (M.kernel (θ (φ k) j)) :=
    fun k j => M.kdens_prob (θ (φ k) j)
  have hIntK : ∀ (k : ℕ) (j : Fin s), |∫ x, ψ x ∂(M.kernel (θ (φ k) j))| ≤ C := by
    intro k j
    haveI := hkerprob k j
    have haesm : AEStronglyMeasurable ψ (M.kernel (θ (φ k) j)) := hψ.aestronglyMeasurable
    have hψint : Integrable ψ (M.kernel (θ (φ k) j)) :=
      MeasureTheory.Integrable.of_bound haesm C
        (Filter.Eventually.of_forall (fun x => by simpa [Real.norm_eq_abs] using hCbnd x))
    have h1 : |∫ x, ψ x ∂(M.kernel (θ (φ k) j))| ≤ ∫ x, ‖ψ x‖ ∂(M.kernel (θ (φ k) j)) := by
      simpa [Real.norm_eq_abs] using
        MeasureTheory.norm_integral_le_integral_norm (f := ψ) (μ := M.kernel (θ (φ k) j))
    have h2 : ∫ x, ‖ψ x‖ ∂(M.kernel (θ (φ k) j)) ≤ ∫ x, C ∂(M.kernel (θ (φ k) j)) :=
      MeasureTheory.integral_mono_ae hψint.norm (MeasureTheory.integrable_const C)
        (Filter.Eventually.of_forall (fun x => by simpa [Real.norm_eq_abs] using hCbnd x))
    have h3 : ∫ x, C ∂(M.kernel (θ (φ k) j)) = C := by
      rw [MeasureTheory.integral_const]
      simp [smul_eq_mul]
    linarith
  have hIntFull : ∀ k : ℕ, ∫ x, ψ x ∂(mixtureMeasure M (q (φ k)) (θ (φ k)))
      = ∑ j : Fin s, q (φ k) j * ∫ x, ψ x ∂(M.kernel (θ (φ k) j)) := by
    intro k
    rw [mixtureMeasure, MeasureTheory.integral_finset_sum_measure]
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [MeasureTheory.integral_smul_measure, ENNReal.toReal_ofReal (le_of_lt (hqpos (φ k) j)),
        smul_eq_mul]
    · intro j _
      haveI := hkerprob k j
      have hψint : Integrable ψ (M.kernel (θ (φ k) j)) :=
        MeasureTheory.Integrable.of_bound hψ.aestronglyMeasurable C
          (Filter.Eventually.of_forall (fun x => by simpa [Real.norm_eq_abs] using hCbnd x))
      exact hψint.smul_measure ENNReal.ofReal_ne_top
  have hIntRen : ∀ k : ℕ, ∫ x, ψ x ∂(mixtureMeasure M (q' k) (θ' k))
      = (∑ m : Fin s', q (φ k) (e m) * ∫ x, ψ x ∂(M.kernel (θ (φ k) (e m)))) / S k := by
    intro k
    rw [mixtureMeasure, MeasureTheory.integral_finset_sum_measure]
    · rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [MeasureTheory.integral_smul_measure, ENNReal.toReal_ofReal (le_of_lt (hq'pos k m)),
        smul_eq_mul]
      simp only [q', θ', div_mul_eq_mul_div]
    · intro m _
      haveI : IsProbabilityMeasure (M.kernel (θ' k m)) := M.kdens_prob (θ' k m)
      have hψint : Integrable ψ (M.kernel (θ' k m)) :=
        MeasureTheory.Integrable.of_bound hψ.aestronglyMeasurable C
          (Filter.Eventually.of_forall (fun x => by simpa [Real.norm_eq_abs] using hCbnd x))
      exact hψint.smul_measure ENNReal.ofReal_ne_top
  have hA : ∀ k : ℕ, (∑ m : Fin s', q (φ k) (e m) * ∫ x, ψ x ∂(M.kernel (θ (φ k) (e m))))
      = ∑ j ∈ J, q (φ k) j * ∫ x, ψ x ∂(M.kernel (θ (φ k) j)) :=
    fun k => hsum_e (fun j => q (φ k) j * ∫ x, ψ x ∂(M.kernel (θ (φ k) j)))
  have hcompl : ∀ k : ℕ, (∑ j : Fin s, q (φ k) j * ∫ x, ψ x ∂(M.kernel (θ (φ k) j)))
      = (∑ m : Fin s', q (φ k) (e m) * ∫ x, ψ x ∂(M.kernel (θ (φ k) (e m))))
        + ∑ j ∈ Finset.univ.filter (fun j : Fin s => ¬ 0 < qstar j),
            q (φ k) j * ∫ x, ψ x ∂(M.kernel (θ (φ k) j)) := by
    intro k
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin s))
      (fun j : Fin s => 0 < qstar j) (fun j => q (φ k) j * ∫ x, ψ x ∂(M.kernel (θ (φ k) j))),
      ← hA k]
  have hWsum : ∀ k : ℕ,
      (∑ j ∈ Finset.univ.filter (fun j : Fin s => ¬ 0 < qstar j), q (φ k) j) = 1 - S k := by
    intro k
    have h1 := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin s))
      (fun j : Fin s => 0 < qstar j) (fun j => q (φ k) j)
    have h2 : (∑ j ∈ Finset.univ.filter (fun j : Fin s => 0 < qstar j), q (φ k) j) = S k :=
      (hS_eq k).symm
    have h3 : (∑ j : Fin s, q (φ k) j) = 1 := hqsum (φ k)
    rw [h2, h3] at h1
    linarith
  have hSle : ∀ k : ℕ, S k ≤ 1 := by
    intro k
    rw [hS_eq k, ← hqsum (φ k)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J)
      (fun j _ _ => (hqpos (φ k) j).le)
  have hAbnd : ∀ k : ℕ,
      |∑ m : Fin s', q (φ k) (e m) * ∫ x, ψ x ∂(M.kernel (θ (φ k) (e m)))| ≤ C := by
    intro k
    have h1 : |∑ m : Fin s', q (φ k) (e m) * ∫ x, ψ x ∂(M.kernel (θ (φ k) (e m)))|
        ≤ ∑ m : Fin s', |q (φ k) (e m) * ∫ x, ψ x ∂(M.kernel (θ (φ k) (e m)))| :=
      Finset.abs_sum_le_sum_abs _ _
    have h2 : (∑ m : Fin s', |q (φ k) (e m) * ∫ x, ψ x ∂(M.kernel (θ (φ k) (e m)))|
        ) ≤ ∑ m : Fin s', q (φ k) (e m) * C := by
      refine Finset.sum_le_sum (fun m _ => ?_)
      rw [abs_mul, abs_of_pos (hqpos (φ k) (e m))]
      exact mul_le_mul_of_nonneg_left (hIntK k (e m)) (hqpos (φ k) (e m)).le
    have h3 : (∑ m : Fin s', q (φ k) (e m) * C) = S k * C := by
      simp only [Finset.sum_mul, S]
    have h4 : S k * C ≤ C := by
      have h5 := mul_le_mul_of_nonneg_right (hSle k) hCnonneg
      linarith
    calc |∑ m : Fin s', q (φ k) (e m) * ∫ x, ψ x ∂(M.kernel (θ (φ k) (e m)))|
        ≤ ∑ m : Fin s', |q (φ k) (e m) * ∫ x, ψ x ∂(M.kernel (θ (φ k) (e m)))| := h1
      _ ≤ ∑ m : Fin s', q (φ k) (e m) * C := h2
      _ = S k * C := h3
      _ ≤ C := h4
  have hWbnd : ∀ k : ℕ,
      |∑ j ∈ Finset.univ.filter (fun j : Fin s => ¬ 0 < qstar j),
        q (φ k) j * ∫ x, ψ x ∂(M.kernel (θ (φ k) j))| ≤ C * |1 - S k| := by
    intro k
    have h1 : |∑ j ∈ Finset.univ.filter (fun j : Fin s => ¬ 0 < qstar j),
        q (φ k) j * ∫ x, ψ x ∂(M.kernel (θ (φ k) j))|
        ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin s => ¬ 0 < qstar j),
          |q (φ k) j * ∫ x, ψ x ∂(M.kernel (θ (φ k) j))| :=
      Finset.abs_sum_le_sum_abs _ _
    have h2 : (∑ j ∈ Finset.univ.filter (fun j : Fin s => ¬ 0 < qstar j),
          |q (φ k) j * ∫ x, ψ x ∂(M.kernel (θ (φ k) j))|)
        ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin s => ¬ 0 < qstar j), q (φ k) j * C := by
      refine Finset.sum_le_sum (fun j _ => ?_)
      rw [abs_mul, abs_of_pos (hqpos (φ k) j)]
      exact mul_le_mul_of_nonneg_left (hIntK k j) (hqpos (φ k) j).le
    have h3 : (∑ j ∈ Finset.univ.filter (fun j : Fin s => ¬ 0 < qstar j), q (φ k) j * C)
        = (1 - S k) * C := by
      rw [← Finset.sum_mul, hWsum k]
    have h4 : (1 - S k) * C = C * |1 - S k| := by
      rw [abs_of_nonneg (by linarith [hSle k])]
      ring
    linarith
  have hpt : ∀ k : ℕ, |∫ x, ψ x ∂(mixtureMeasure M (q' k) (θ' k))
      - ∫ x, ψ x ∂(mixtureMeasure M (q (φ k)) (θ (φ k)))|
      ≤ C * |1 / S k - 1| + C * |1 - S k| := by
    intro k
    rw [hIntRen k, hIntFull k, hcompl k]
    set A : ℝ := ∑ m : Fin s', q (φ k) (e m) * ∫ x, ψ x ∂(M.kernel (θ (φ k) (e m)))
    set W : ℝ := ∑ j ∈ Finset.univ.filter (fun j : Fin s => ¬ 0 < qstar j),
      q (φ k) j * ∫ x, ψ x ∂(M.kernel (θ (φ k) j))
    have h1 : |A| ≤ C := hAbnd k
    have h2 : |W| ≤ C * |1 - S k| := hWbnd k
    have hAlg : A / S k - (A + W) = A * (1 / S k - 1) - W := by
      have h' : A * (1 / S k - 1) = A / S k - A := by rw [mul_sub, mul_one, mul_one_div]
      rw [h']
      ring
    have htri : |A * (1 / S k - 1) - W| ≤ |A * (1 / S k - 1)| + |W| := by
      have h5 := abs_add_le (A * (1 / S k - 1)) (-W)
      simpa using h5
    calc |A / S k - (A + W)| = |A * (1 / S k - 1) - W| := by rw [hAlg]
      _ ≤ |A * (1 / S k - 1)| + |W| := htri
      _ = |A| * |1 / S k - 1| + |W| := by rw [abs_mul]
      _ ≤ C * |1 / S k - 1| + C * |1 - S k| := by
          have h6 : |A| * |1 / S k - 1| ≤ C * |1 / S k - 1| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
          linarith
  have hu : Tendsto (fun k => C * |1 / S k - 1| + C * |1 - S k|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => 1 / S k - 1) atTop (𝓝 0) := by
      have h := hStend.inv₀ one_ne_zero
      have h' := h.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
      simpa [one_div] using h'
    have h2 : Tendsto (fun k => 1 - S k) atTop (𝓝 0) := by
      have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hStend
      simpa using h
    have h3 : Tendsto (fun k => |1 / S k - 1|) atTop (𝓝 0) := by
      simpa using h1.abs
    have h4 : Tendsto (fun k => |1 - S k|) atTop (𝓝 0) := by
      simpa using h2.abs
    have h5 : Tendsto (fun k => C * |1 / S k - 1| + C * |1 - S k|) atTop (𝓝 (C * 0 + C * 0)) :=
      (h3.const_mul C).add (h4.const_mul C)
    simpa using h5
  have hdiff : Tendsto (fun k => ∫ x, ψ x ∂(mixtureMeasure M (q' k) (θ' k))
      - ∫ x, ψ x ∂(mixtureMeasure M (q (φ k)) (θ (φ k)))) atTop (𝓝 0) := by
    have huneg : Tendsto (fun k => -(C * |1 / S k - 1| + C * |1 - S k|)) atTop (𝓝 0) := by
      simpa using hu.neg
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le huneg hu (fun k => ?_) (fun k => ?_)
    · have h := hpt k
      linarith [neg_abs_le (∫ x, ψ x ∂(mixtureMeasure M (q' k) (θ' k))
        - ∫ x, ψ x ∂(mixtureMeasure M (q (φ k)) (θ (φ k))))]
    · have h := hpt k
      linarith [le_abs_self (∫ x, ψ x ∂(mixtureMeasure M (q' k) (θ' k))
        - ∫ x, ψ x ∂(mixtureMeasure M (q (φ k)) (θ (φ k))))]
  set F : BoundedContinuousFunction X ℝ :=
    { toFun := ψ
      continuous_toFun := hψ
      map_bounded' := ⟨2 * C, fun x y => by
        rw [Real.dist_eq]
        have habs : |ψ x - ψ y| ≤ |ψ x| + |ψ y| := by
          have h5 := abs_add_le (ψ x) (-ψ y)
          simpa using h5
        linarith [hCbnd x, hCbnd y]⟩ }
  have hFval : ⇑F = ψ := rfl
  have ha : Tendsto (fun k => ∫ x, ψ x ∂(mixtureMeasure M (q (φ k)) (θ (φ k))))
      atTop (𝓝 (∫ x, ψ x ∂P0)) := by
    have h := hsub F
    simpa [hFval] using h
  have hfin := hdiff.add ha
  simpa [sub_add_cancel] using hfin
  /- @proof-region region.target-node.session.f4cfe9ea42253c87 end -/

end Statlib.Imported


end OfflineCorrectedDP


/- Genuine source ProverJobs.job_paper_80f79a059f3741e883a5b36dc8747f99.ExternalNodes.Node_c118597a8eac48c5b63c; namespace isolation only; retained external axioms remain explicit. -/

namespace OfflineCorrectedDP


end OfflineCorrectedDP


/- Genuine source ProverJobs.job_paper_80f79a059f3741e883a5b36dc8747f99.ExternalNodes.Node_6cf54d6285094eb0b147; namespace isolation only; retained external axioms remain explicit. -/

namespace OfflineCorrectedDP


end OfflineCorrectedDP


/- Genuine source ProverJobs.job_paper_80f79a059f3741e883a5b36dc8747f99.ProvedNodes.Node_282633141_fabe214b_555235e2; namespace isolation only; retained external axioms remain explicit. -/

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
theorem statopia_math_node_282633141_fabe214b : ∀ {X Θ : Type*} [MeasurableSpace X] [MeasurableSpace Θ]
    [MetricSpace X] [BorelSpace X] [MeasureSpace X]
    [TopologicalSpace.SeparableSpace X]
    [TopologicalSpace Θ] [StandardBorelSpace Θ]
    (M : DPMModel X Θ) (t : ℕ) (ht : 1 ≤ t)
    (P0 : Measure X) (hP0 : IsProbabilityMeasure P0)
    (hclos : (⟨P0, hP0⟩ : ProbabilityMeasure X) ∈
      closure (⋃ s ∈ {s : ℕ | 1 ≤ s ∧ s < t},
        {ν : ProbabilityMeasure X |
          ∃ (q : Fin s → ℝ) (theta : Fin s → Θ),
            (∀ j : Fin s, 0 < q j) ∧ (∑ j : Fin s, q j = 1) ∧
            Function.Injective theta ∧ (∀ j : Fin s, theta j ∈ M.Θset) ∧
            (ν : Measure X) = mixtureMeasure M q theta})),
    ∃ (s : ℕ) (q : ℕ → Fin s → ℝ) (theta : ℕ → Fin s → Θ),
      1 ≤ s ∧ s < t ∧
      (∀ i : ℕ,
        (∀ j : Fin s, 0 < q i j) ∧ (∑ j : Fin s, q i j = 1) ∧
        Function.Injective (theta i) ∧ (∀ j : Fin s, theta i j ∈ M.Θset)) ∧
      (∀ j : Fin s, 0 < Filter.liminf (fun i : ℕ => q i j) atTop) ∧
      WeakTendsto (fun i : ℕ => mixtureMeasure M (q i) (theta i)) P0 := by
  /- @proof-region region.target-node.session.35587922247982b6 begin -/
  intro X Θ hXm hΘm hMet hBor hMS hSep hΘtop hSB M t ht P0 hP0 hclos
  have hfin : ({s : ℕ | 1 ≤ s ∧ s < t} : Set ℕ).Finite :=
    Set.Finite.subset (Set.finite_Iio t) (fun s hs => hs.2)
  have hclosed : IsClosed (⋃ s ∈ ({s : ℕ | 1 ≤ s ∧ s < t} : Set ℕ),
      closure {ν : ProbabilityMeasure X |
        ∃ (q : Fin s → ℝ) (theta : Fin s → Θ),
          (∀ j : Fin s, 0 < q j) ∧ (∑ j : Fin s, q j = 1) ∧
            Function.Injective theta ∧ (∀ j : Fin s, theta j ∈ M.Θset) ∧
              (ν : Measure X) = mixtureMeasure M q theta}) :=
    hfin.isClosed_biUnion (fun s _ => isClosed_closure)
  have hsub : (⋃ s ∈ ({s : ℕ | 1 ≤ s ∧ s < t} : Set ℕ),
      {ν : ProbabilityMeasure X |
        ∃ (q : Fin s → ℝ) (theta : Fin s → Θ),
          (∀ j : Fin s, 0 < q j) ∧ (∑ j : Fin s, q j = 1) ∧
            Function.Injective theta ∧ (∀ j : Fin s, theta j ∈ M.Θset) ∧
              (ν : Measure X) = mixtureMeasure M q theta})
      ⊆ ⋃ s ∈ ({s : ℕ | 1 ≤ s ∧ s < t} : Set ℕ),
      closure {ν : ProbabilityMeasure X |
        ∃ (q : Fin s → ℝ) (theta : Fin s → Θ),
          (∀ j : Fin s, 0 < q j) ∧ (∑ j : Fin s, q j = 1) ∧
            Function.Injective theta ∧ (∀ j : Fin s, theta j ∈ M.Θset) ∧
              (ν : Measure X) = mixtureMeasure M q theta} := by
    intro x hx
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨s, hs, hxs⟩ := hx
    exact ⟨s, hs, subset_closure hxs⟩
  have hmem := closure_minimal hsub hclosed hclos
  obtain ⟨s, hs, hclos_s⟩ := by
    simpa only [Set.mem_iUnion] using hmem
  rw [Set.mem_setOf_eq] at hs
  obtain ⟨hs_ge, hs_lt⟩ := hs
  obtain ⟨s', q, θ, h1, h2, hmain, hlim, hweak⟩ :=
    statopia_math_node_2415940998_78aaa9b9 M s hs_ge P0 hP0 hclos_s
  exact ⟨s', q, θ, h1, lt_of_le_of_lt h2 hs_lt,
    fun i => ⟨(hmain i).1, (hmain i).2.1, (hmain i).2.2.1, (hmain i).2.2.2.1⟩,
    hlim, hweak⟩
  /- @proof-region region.target-node.session.35587922247982b6 end -/

end Statlib.Imported


end OfflineCorrectedDP


/- Genuine source ProverJobs.job_paper_80f79a059f3741e883a5b36dc8747f99.ProvedNodes.Node_4155964396_49859298_ad1a126e; namespace isolation only; retained external axioms remain explicit. -/

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
theorem statopia_math_node_4155964396_49859298 : ∀ {X Θ : Type*} [MeasurableSpace X] [MeasurableSpace Θ]
    [MetricSpace X] [BorelSpace X] [MeasureSpace X] [CompleteSpace X]
    [SecondCountableTopology X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
    [MetricSpace Θ] [BorelSpace Θ] [StandardBorelSpace Θ] [ProperSpace Θ]
    (M : DPMModel X Θ)
    (t : ℕ) (ht : 1 ≤ t)
    (p : Fin t → ℝ) (hp_pos : ∀ j : Fin t, 0 < p j) (hp_sum : ∑ j : Fin t, p j = 1)
    (thetaStar : Fin t → Θ)
    (P0 : Measure X) (hP0_prob : IsProbabilityMeasure P0)
    (hP0 : P0 = mixtureMeasure M p thetaStar)
    (s : ℕ) (hs : 1 ≤ s) (hst : s < t)
    (q : ℕ → Fin s → ℝ) (theta : ℕ → Fin s → Θ)
    (hq_pos : ∀ (i : ℕ) (j : Fin s), 0 < q i j)
    (hq_sum : ∀ i : ℕ, ∑ j : Fin s, q i j = 1)
    (htheta_inj : ∀ i : ℕ, Function.Injective (theta i))
    (htheta_mem : ∀ (i : ℕ) (j : Fin s), theta i j ∈ M.Θset)
    (hweak : WeakTendsto (fun i : ℕ => mixtureMeasure M (q i) (theta i)) P0)
    (hliminf : ∀ j : Fin s, 0 < Filter.liminf (fun i : ℕ => q i j) Filter.atTop)
    (hatom : (∀ x : X, M.μ {x} = 0) ∨ singularBoundary M = ∅)
    (hdirac : ∀ (thetaBar : Θ), thetaBar ∈ singularBoundary M → ∀ (thetaSeq : ℕ → Θ),
      Tendsto thetaSeq atTop (𝓝 thetaBar) →
        ∃ xstar : X, WeakTendsto (fun i : ℕ => M.kernel (thetaSeq i)) (Measure.dirac xstar)),
    ¬ ∃ (j : Fin s) (thetaBar : Θ) (phi : ℕ → ℕ),
      thetaBar ∈ singularBoundary M ∧ StrictMono phi ∧
        Tendsto (fun i : ℕ => theta (phi i) j) atTop (𝓝 thetaBar) := by
  /- @proof-region region.target-node.session.3dbd051f1f6dcec3 begin -/
  intro X Θ mX mΘ met bore meas cmp sct prop sep metΘ boreΘ sbΘ propΘ M t ht p hp hp_sum thetas P0
    hP0prob hP0mix s hs hst q theta hq_pos hq_sum htheta_inj htheta_mem hweak hliminf hatom hboundary
  rintro ⟨j, thetabar, phi, hbar, hphi, htend⟩
  rcases hatom with hμ | hB
  · obtain ⟨c, hcpos, hc⟩ : ∃ c : ℝ, 0 < c ∧ ∀ᶠ i : ℕ in atTop, c ≤ q i j := by
      by_contra hcon
      push_neg at hcon
      have hbd : ∀ᶠ i : ℕ in atTop, (fun x1 x2 : ℝ => x1 ≥ x2) (q i j) 0 :=
        Filter.Eventually.of_forall fun i => le_of_lt (hq_pos i j)
      have hle1 : ∀ i : ℕ, q i j ≤ 1 := fun i => by
        rw [← hq_sum i]
        exact Finset.single_le_sum (f := fun k : Fin s => q i k)
          (fun k _ => le_of_lt (hq_pos i k)) (Finset.mem_univ j)
      have h₂ : Filter.IsBoundedUnder (fun x1 x2 : ℝ => x1 ≥ x2) atTop (fun i : ℕ => q i j) :=
        ⟨0, hbd⟩
      have h₁ : Filter.IsCoboundedUnder (fun x1 x2 : ℝ => x1 ≥ x2) atTop (fun i : ℕ => q i j) := by
        refine ⟨1, fun a ha => ?_⟩
        have ha' : ∀ᶠ i : ℕ in atTop, (fun x1 x2 : ℝ => x1 ≥ x2) (q i j) a :=
          Filter.eventually_map.mp ha
        obtain ⟨i, hi⟩ := ha'.exists
        have hi1 : q i j ≤ 1 := hle1 i
        linarith
      have hle : Filter.liminf (fun i : ℕ => q i j) atTop ≤ 0 := by
        rw [Filter.liminf_le_iff (h₁ := h₁) (h₂ := h₂)]
        intro b hb
        exact hcon b hb
      linarith [hliminf j]
    obtain ⟨xstar, hD⟩ := hboundary thetabar hbar (fun i => theta (phi i) j) htend
    have hcsub : ∀ᶠ i : ℕ in atTop, c ≤ q (phi i) j := hphi.tendsto_atTop.eventually hc
    have hms : MeasurableSet ({xstar} : Set X) := measurableSet_singleton xstar
    have hres : M.μ.restrict ({xstar} : Set X) = 0 := by
      refine MeasureTheory.Measure.ext fun s hs => ?_
      rw [MeasureTheory.Measure.restrict_apply hs]
      show M.μ (s ∩ {xstar}) = 0
      exact MeasureTheory.measure_mono_null Set.inter_subset_right (hμ xstar)
    have hkSing : ∀ θ : Θ, M.kernel θ {xstar} = 0 := by
      intro θ
      show (M.μ.withDensity (fun x => ENNReal.ofReal (M.kdens θ x))) {xstar} = 0
      rw [MeasureTheory.withDensity_apply (fun x => ENNReal.ofReal (M.kdens θ x)) hms, hres]
      simp
    have hP0sing : P0 {xstar} = 0 := by
      rw [hP0mix]
      simp only [mixtureMeasure]
      rw [MeasureTheory.Measure.coe_finset_sum, Finset.sum_apply]
      exact Finset.sum_eq_zero fun k _ => by
        rw [MeasureTheory.Measure.smul_apply, hkSing (thetas k), smul_zero]
    set ψ : ℕ → X → ℝ := fun m x => max 0 (1 - (m : ℝ) * dist x xstar) with hψ
    have hψ_cont : ∀ m : ℕ, Continuous (ψ m) := by
      intro m
      have h1 : Continuous fun x : X => dist x xstar :=
        continuous_id.dist continuous_const
      have h2 : Continuous fun x : X => (m : ℝ) * dist x xstar :=
        continuous_const.mul h1
      have h3 : Continuous fun x : X => 1 - (m : ℝ) * dist x xstar :=
        (continuous_const : Continuous fun _ : X => (1 : ℝ)).sub h2
      have h4 : Continuous fun x : X => max 0 (1 - (m : ℝ) * dist x xstar) :=
        (continuous_const : Continuous fun _ : X => (0 : ℝ)).max h3
      simpa [hψ] using h4
    have hψ_bound : ∀ (m : ℕ) (x : X), |ψ m x| ≤ 1 := by
      intro m x
      have hval : ψ m x = max 0 (1 - (m : ℝ) * dist x xstar) := by simp [hψ]
      rw [hval, abs_of_nonneg (le_max_left 0 (1 - (m : ℝ) * dist x xstar))]
      refine max_le zero_le_one ?_
      have h : 0 ≤ (m : ℝ) * dist x xstar :=
        mul_nonneg (Nat.cast_nonneg m) dist_nonneg
      linarith
    have hψ_xstar : ∀ m : ℕ, ψ m xstar = 1 := fun m => by simp [hψ]
    have hLower : ∀ m : ℕ, c ≤ ∫ x, ψ m x ∂P0 := by
      intro m
      have hmix : ∀ i : ℕ,
          ∫ x, ψ m x ∂(mixtureMeasure M (q (phi i)) (theta (phi i)))
            = ∑ k : Fin s, q (phi i) k * ∫ x, ψ m x ∂(M.kernel (theta (phi i) k)) := by
        intro i
        have hInt : ∀ k : Fin s,
            Integrable (ψ m) (ENNReal.ofReal (q (phi i) k) • M.kernel (theta (phi i) k)) := by
          intro k
          haveI hk : IsProbabilityMeasure (M.kernel (theta (phi i) k)) :=
            M.kdens_prob (theta (phi i) k)
          haveI hfin :
              IsFiniteMeasure (ENNReal.ofReal (q (phi i) k) • M.kernel (theta (phi i) k)) := by
            refine ⟨?_⟩
            have hku : (M.kernel (theta (phi i) k)) Set.univ = 1 := measure_univ
            rw [MeasureTheory.Measure.smul_apply, hku, smul_eq_mul, mul_one]
            simp
          refine MeasureTheory.Integrable.of_bound ?_ 1 ?_
          · exact (hψ_cont m).aestronglyMeasurable
          · exact Filter.Eventually.of_forall fun x => by
              rw [Real.norm_eq_abs]
              exact hψ_bound m x
        simp only [mixtureMeasure]
        rw [MeasureTheory.integral_finset_sum_measure]
        · refine Finset.sum_congr rfl fun k _ => ?_
          rw [MeasureTheory.integral_smul_measure, smul_eq_mul,
            ENNReal.toReal_ofReal (le_of_lt (hq_pos (phi i) k))]
        · intro k _
          exact hInt k
      have hA : Tendsto (fun i : ℕ => ∫ x, ψ m x ∂(mixtureMeasure M (q (phi i)) (theta (phi i))))
          atTop (𝓝 (∫ x, ψ m x ∂P0)) :=
        (hweak (ψ m) (hψ_cont m) ⟨1, hψ_bound m⟩).comp hphi.tendsto_atTop
      have hB : Tendsto (fun i : ℕ => ∫ x, ψ m x ∂(M.kernel (theta (phi i) j))) atTop (𝓝 1) := by
        have h := hD (ψ m) (hψ_cont m) ⟨1, hψ_bound m⟩
        rw [MeasureTheory.integral_dirac (ψ m) xstar] at h
        simpa [hψ_xstar m] using h
      refine le_of_tendsto_of_tendsto
        (f := fun i : ℕ => c * ∫ x, ψ m x ∂(M.kernel (theta (phi i) j))) ?_ hA ?_
      · simpa using hB.const_mul c
      · filter_upwards [hcsub] with i hi
        have hnn : ∀ k : Fin s, 0 ≤ ∫ x, ψ m x ∂(M.kernel (theta (phi i) k)) := fun k =>
          MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => by
            simp only [hψ]
            exact le_max_left 0 _)
        have h2 : c * ∫ x, ψ m x ∂(M.kernel (theta (phi i) j))
            ≤ q (phi i) j * ∫ x, ψ m x ∂(M.kernel (theta (phi i) j)) :=
          mul_le_mul_of_nonneg_right hi (hnn j)
        have h3 : q (phi i) j * ∫ x, ψ m x ∂(M.kernel (theta (phi i) j))
            ≤ ∑ k : Fin s, q (phi i) k * ∫ x, ψ m x ∂(M.kernel (theta (phi i) k)) :=
          Finset.single_le_sum
            (f := fun k : Fin s => q (phi i) k * ∫ x, ψ m x ∂(M.kernel (theta (phi i) k)))
            (fun k _ => mul_nonneg (le_of_lt (hq_pos (phi i) k)) (hnn k)) (Finset.mem_univ j)
        rw [hmix i]
        linarith
    have hae : ∀ᵐ x ∂P0, x ≠ xstar := by
      rw [MeasureTheory.ae_iff]
      have hset : {x : X | ¬ x ≠ xstar} = ({xstar} : Set X) := by
        ext x
        simp
      rw [hset]
      exact hP0sing
    have hlim : ∀ᵐ x ∂P0, Tendsto (fun m : ℕ => ψ m x) atTop (𝓝 ((fun _ => (0 : ℝ)) x)) := by
      filter_upwards [hae] with x hx
      have hd : 0 < dist x xstar := dist_pos.mpr hx
      have hN : ∀ᶠ m : ℕ in atTop, ψ m x = 0 := by
        obtain ⟨N, hN⟩ := exists_nat_ge (1 / dist x xstar)
        filter_upwards [Filter.eventually_ge_atTop N] with m hm
        have hm' : (1 / dist x xstar) ≤ (m : ℝ) := le_trans hN (by exact_mod_cast hm)
        have h0 : (1 / dist x xstar) * dist x xstar = 1 := by
          field_simp [ne_of_gt hd]
        have h1 : (1 : ℝ) ≤ (m : ℝ) * dist x xstar := by
          calc (1 : ℝ) = (1 / dist x xstar) * dist x xstar := by rw [h0]
            _ ≤ (m : ℝ) * dist x xstar := mul_le_mul_of_nonneg_right hm' (le_of_lt hd)
        simp only [hψ]
        rw [max_eq_left (by linarith)]
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN'⟩ := Filter.eventually_atTop.mp hN
      refine ⟨N, fun n hn => ?_⟩
      rw [hN' n hn]
      simpa using hε
    have hupper : Tendsto (fun m : ℕ => ∫ x, ψ m x ∂P0) atTop (𝓝 0) := by
      have hbd : Integrable (fun _ : X => (1 : ℝ)) P0 :=
        MeasureTheory.Integrable.of_bound (continuous_const.aestronglyMeasurable) 1
          (Filter.Eventually.of_forall fun x => by simp)
      have hbnd : ∀ m : ℕ, ∀ᵐ x ∂P0, ‖ψ m x‖ ≤ (fun _ : X => (1 : ℝ)) x := fun m =>
        Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs]
          exact hψ_bound m x
      have h := MeasureTheory.tendsto_integral_of_dominated_convergence
        (μ := P0) (F := ψ) (f := fun _ => (0 : ℝ)) (bound := fun _ : X => (1 : ℝ))
        (fun m => (hψ_cont m).aestronglyMeasurable)
        hbd hbnd hlim
      simpa using h
    have hcle : c ≤ 0 := ge_of_tendsto hupper (Filter.Eventually.of_forall hLower)
    linarith
  · rw [hB] at hbar
    exact hbar
  /- @proof-region region.target-node.session.3dbd051f1f6dcec3 end -/

end Statlib.Imported


end OfflineCorrectedDP


/- Genuine source ProverJobs.job_paper_80f79a059f3741e883a5b36dc8747f99.ProvedNodes.Node_551590810_788b8fc0_ad558fe6; namespace isolation only; retained external axioms remain explicit. -/

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
theorem statopia_math_node_551590810_788b8fc0 : ∀ {Θ : Type*} [MetricSpace Θ]
    (B : Set Θ) (hB_closed : IsClosed B)
    (A : Set Θ) (hB_disj : Disjoint B A) (hclosure_subset : closure A ⊆ A ∪ B)
    (s : ℕ) (θ : ℕ → Fin s → Θ) (hθA : ∀ (i : ℕ) (j : Fin s), θ i j ∈ A)
    (C0 : Set Θ) (hC0_compact : IsCompact C0) (i0 : ℕ)
    (hC0_mem : ∀ (i : ℕ), i0 ≤ i → ∀ j : Fin s, θ i j ∈ C0)
    (hno_cluster : ∀ (j : Fin s) (x : Θ), x ∈ B →
      ¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun i : ℕ => θ (φ i) j) atTop (𝓝 x)),
    ∃ C : Set Θ, IsCompact C ∧ (∀ (i : ℕ) (j : Fin s), θ i j ∈ C) ∧
      C ∩ closure A ⊆ A \ B := by
  /- @proof-region region.target-node.session.c72378711ce1035b begin -/
  intro Θ _inst B hB_closed A hB_disj hclosure_subset s θ hθA C0 hC0 i0 hθC0 hnoescape
  classical
  have hLcompact : ∀ j : Fin s, IsCompact (closure (Set.range (fun i => θ i j))) := by
    intro j
    have hSsub : Set.range (fun i => θ i j) ⊆
        C0 ∪ ((Finset.range i0).image (fun i => θ i j) : Set Θ) := by
      rintro y ⟨i, rfl⟩
      by_cases hi : i < i0
      · exact Or.inr
          (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩))
      · exact Or.inl (hθC0 i (Nat.le_of_not_lt hi) j)
    have hclosed : IsClosed (C0 ∪ ((Finset.range i0).image (fun i => θ i j) : Set Θ)) :=
      hC0.isClosed.union (Finset.finite_toSet _).isClosed
    exact (hC0.union (Finset.finite_toSet _).isCompact).of_isClosed_subset isClosed_closure
      (closure_minimal hSsub hclosed)
  have hLdisj : ∀ (j : Fin s) (x : Θ), x ∈ B → x ∉ closure (Set.range (fun i => θ i j)) := by
    intro j x hxB hxclos
    have hxS : x ∉ Set.range (fun i => θ i j) := by
      rintro ⟨i, hi⟩
      have hxA : ((fun i => θ i j) i) ∈ A := hθA i j
      rw [hi] at hxA
      exact (Set.disjoint_left.mp hB_disj) hxB hxA
    have hfreq : ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop, θ n j ∈ Metric.ball x ε := by
      intro ε hε
      refine Filter.frequently_atTop'.mpr ?_
      intro a
      by_contra hcon
      have hout : ∀ b : ℕ, a < b → θ b j ∉ Metric.ball x ε := by
        intro b hb hp
        exact hcon ⟨b, hb, hp⟩
      have hFsub : ((Finset.range (a + 1)).image (fun b => θ b j) : Set Θ) ⊆
          Set.range (fun i => θ i j) := by
        intro y hy
        obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
        exact ⟨b, rfl⟩
      have hclosed : IsClosed (((Finset.range (a + 1)).image (fun b => θ b j) : Set Θ) ∪
          (Metric.ball x ε)ᶜ) :=
        (Finset.finite_toSet _).isClosed.union Metric.isOpen_ball.isClosed_compl
      have hsub : Set.range (fun i => θ i j) ⊆
          ((Finset.range (a + 1)).image (fun b => θ b j) : Set Θ) ∪ (Metric.ball x ε)ᶜ := by
        rintro y ⟨i, rfl⟩
        by_cases hi : i < a + 1
        · exact Or.inl
            (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩))
        · exact Or.inr (hout i (Nat.lt_of_succ_le (Nat.le_of_not_lt hi)))
      have hxnot : x ∉ ((Finset.range (a + 1)).image (fun b => θ b j) : Set Θ) ∪
          (Metric.ball x ε)ᶜ := by
        rintro (hx | hx)
        · exact hxS (hFsub hx)
        · exact hx (Metric.mem_ball_self hε)
      exact hxnot (closure_minimal hsub hclosed hxclos)
    choose φ hφ using fun n : ℕ =>
      Filter.frequently_atTop'.mp (hfreq (1 / ((n : ℝ) + 1)) (by positivity)) n
    have hφlt : ∀ n : ℕ, n < φ n := fun n => (hφ n).left
    have hφnear : ∀ n : ℕ, θ (φ n) j ∈ Metric.ball x (1 / ((n : ℝ) + 1)) := fun n => (hφ n).right
    have hφlim : Tendsto (fun n : ℕ => θ (φ n) j) atTop (𝓝 x) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
      refine ⟨N, fun n hn => ?_⟩
      have hle : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
        refine one_div_le_one_div_of_le (by positivity) ?_
        have hle' : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
        linarith
      exact lt_of_lt_of_le (Metric.mem_ball.mp (hφnear n)) (le_trans hle (le_of_lt hN))
    have hφtend : Tendsto φ atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro a
      exact ⟨a + 1, fun b hb => Nat.le_of_succ_le (Nat.le_trans hb (Nat.le_of_lt (hφlt b)))⟩
    obtain ⟨ψ, hψ, hψφ⟩ := Filter.strictMono_subseq_of_tendsto_atTop hφtend
    exact hnoescape j x hxB ⟨fun n => φ (ψ n), hψφ, hφlim.comp hψ.tendsto_atTop⟩
  refine ⟨⋃ j : Fin s, closure (Set.range (fun i => θ i j)), ?_, ?_, ?_⟩
  · exact isCompact_iUnion hLcompact
  · intro i j
    exact Set.mem_iUnion.mpr ⟨j, subset_closure ⟨i, rfl⟩⟩
  · rintro x ⟨hxC, hxA⟩
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxC
    have hxB : x ∉ B := fun hxB => hLdisj j x hxB hj
    rcases hclosure_subset hxA with hA | hB
    · exact ⟨hA, hxB⟩
    · exact absurd hB hxB
  /- @proof-region region.target-node.session.c72378711ce1035b end -/

end Statlib.Imported


end OfflineCorrectedDP


/- Genuine source ProverJobs.job_paper_80f79a059f3741e883a5b36dc8747f99.ProvedNodes.Node_2851582091_10c14bea_01ffbc6b; namespace isolation only; retained external axioms remain explicit. -/

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
theorem statopia_math_node_2851582091_10c14bea : ∀ {X Θ : Type*} [MeasurableSpace X] [MeasurableSpace Θ]
    [MetricSpace X] [BorelSpace X] [MeasureSpace X] [CompleteSpace X]
    [SecondCountableTopology X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
    [MetricSpace Θ] [BorelSpace Θ] [StandardBorelSpace Θ] [ProperSpace Θ]
    (M : DPMModel X Θ)
    (hmu_finite : ∀ K : Set X, IsCompact K → M.μ K < ∞)
    (hexhaustion : ∃ K : ℕ → Set Θ,
      (∀ m, IsCompact (K m)) ∧ Monotone K ∧ (⋃ m, K m) = Set.univ)
    (t : ℕ) (ht : 1 ≤ t)
    (p : Fin t → ℝ) (hp : ∀ j : Fin t, 0 < p j) (hp1 : ∑ j : Fin t, p j = 1)
    (θs : Fin t → Θ) (hθs_inj : Function.Injective θs)
    (P0 : Measure X) (hP0 : IsProbabilityMeasure P0)
    (hP0_eq : P0 = ∑ j : Fin t, ENNReal.ofReal (p j) • M.kernel (θs j))
    (hH1 : ∀ θbar ∈ M.Θset, θbar ∉ singularBoundary M →
      ∀ᵐ x ∂M.μ, ∃ A : Set Θ, A ∈ 𝓝 θbar ∧ A ⊆ M.Θset \ singularBoundary M ∧
        ContinuousOn (fun θ : Θ => M.kdens θ x) A)
    (hH2div : ∀ (theta : ℕ → Θ), Tendsto theta atTop (cocompact Θ) →
      ∀ K : Set X, IsCompact K →
        Tendsto (fun i : ℕ => M.kernel (theta i) K) atTop (𝓝 0))
    (hH2dirac : ∀ (θbar : Θ), θbar ∈ singularBoundary M → ∀ (theta : ℕ → Θ),
      Tendsto theta atTop (𝓝 θbar) →
        ∃ xstar : X, WeakTendsto (fun i : ℕ => M.kernel (theta i)) (Measure.dirac xstar))
    (hH3 : ∀ (s' : ℕ), 1 ≤ s' → s' < t →
      ∀ (q : Fin s' → ℝ) (theta : Fin s' → Θ),
        (∀ k : Fin s', 0 < q k) → (∑ k : Fin s', q k = 1) → Function.Injective theta →
          ¬ (∀ᵐ x ∂M.μ, mixDens M p θs x = mixDens M q theta x))
    (hatom : (∀ x : X, M.μ {x} = 0) ∨ singularBoundary M = ∅)
    (hB_closed : IsClosed (singularBoundary M))
    (hB_disj : Disjoint (singularBoundary M) M.Θset)
    (hclosure_subset : closure M.Θset ⊆ M.Θset ∪ singularBoundary M),
      ∃ U : Set (ProbabilityMeasure X),
        IsOpen U ∧ (⟨P0, hP0⟩ : ProbabilityMeasure X) ∈ U ∧
          (∀ s : ℕ, 1 ≤ s → s < t →
            U ∩ {ν : ProbabilityMeasure X |
              ∃ (q : Fin s → ℝ) (theta : Fin s → Θ),
                (∀ j : Fin s, 0 < q j) ∧ (∑ j : Fin s, q j = 1) ∧
                  Function.Injective theta ∧ (∀ j : Fin s, theta j ∈ M.Θset) ∧
                  (ν : Measure X) = mixtureMeasure M q theta} = ∅) ∧
          U = (closure (⋃ s ∈ {s : ℕ | 1 ≤ s ∧ s < t},
            {ν : ProbabilityMeasure X |
              ∃ (q : Fin s → ℝ) (theta : Fin s → Θ),
                (∀ j : Fin s, 0 < q j) ∧ (∑ j : Fin s, q j = 1) ∧
                  Function.Injective theta ∧ (∀ j : Fin s, theta j ∈ M.Θset) ∧
                  (ν : Measure X) = mixtureMeasure M q theta}))ᶜ := by
  /- @proof-region region.target-node.session.2542abc1c8c9a89d begin -/
  intro X Θ _ _ _ _ _ _ _ _ _ _ _ _ _ M hmu_finite hexhaustion t ht p hp hp1 θs hθs_inj P0
    hP0 hP0mix hH1_cont hH2_div hH2_dirac hH3 hatom hB_closed hB_disj hclosure_subset
  classical
  haveI hP0inst : IsProbabilityMeasure P0 := hP0
  have hnot : (⟨P0, hP0⟩ : ProbabilityMeasure X) ∉
      closure (⋃ s ∈ {s : ℕ | 1 ≤ s ∧ s < t},
        {ν : ProbabilityMeasure X |
          ∃ (q : Fin s → ℝ) (θ : Fin s → Θ),
            (∀ j : Fin s, 0 < q j) ∧ (∑ j : Fin s, q j = 1) ∧ Function.Injective θ ∧
              (∀ j : Fin s, θ j ∈ M.Θset) ∧ (ν : Measure X) = mixtureMeasure M q θ}) := by
    intro hclos
    obtain ⟨s, q, θ, hs1, hst, hmain, hliminf, hweak⟩ :=
      statopia_math_node_282633141_fabe214b M t ht P0 hP0 hclos
    have hqpos : ∀ (i : ℕ) (j : Fin s), 0 < q i j := fun i j => (hmain i).1 j
    have hqsum : ∀ i : ℕ, ∑ j : Fin s, q i j = 1 := fun i => (hmain i).2.1
    have hinj : ∀ i : ℕ, Function.Injective (θ i) := fun i => (hmain i).2.2.1
    have hmem : ∀ (i : ℕ) (j : Fin s), θ i j ∈ M.Θset := fun i j => (hmain i).2.2.2 j
    obtain ⟨hKj, hCex, hnoesc⟩ :=
      statopia_math_node_1004612324_aae1fc53 P0 M t s ht hs1 hst q hqpos hqsum θ hinj
        hmem hweak hliminf hH2_div
    haveI hPSX : PolishSpace X := inferInstance
    haveI hPSΘ : PolishSpace Θ := inferInstance
    obtain ⟨C0, hC0cpt, i0, hi0⟩ := hCex
    have hnoB : ∀ (j : Fin s) (x : Θ), x ∈ singularBoundary M →
        ¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun i : ℕ => θ (φ i) j) atTop (𝓝 x) := by
      have hb := statopia_math_node_4155964396_49859298 M t ht p hp hp1 θs P0 hP0 hP0mix
        s hs1 hst q θ hqpos hqsum hinj hmem hweak hliminf hatom hH2_dirac
      rintro j x hx ⟨φ, hφ, htend⟩
      exact hb ⟨j, x, φ, hx, hφ, htend⟩
    obtain ⟨C, hC, hall, hCsub⟩ :=
      statopia_math_node_551590810_788b8fc0 (singularBoundary M) hB_closed (M.Θset) hB_disj
        hclosure_subset s θ hmem C0 hC0cpt i0 hi0 hnoB
    have hcont : ∀ theta_bar ∈ M.Θset, theta_bar ∉ singularBoundary M →
        ∃ N : Set X, M.μ N = 0 ∧ ∀ x : X, x ∉ N → ∃ A : Set Θ,
          A ∈ 𝓝 theta_bar ∧ A ⊆ M.Θset \ singularBoundary M ∧
            ContinuousOn (fun th => M.kdens th x) A := by
      intro tb h1 h2
      refine ⟨{x | ¬ (∃ A : Set Θ, A ∈ 𝓝 tb ∧ A ⊆ M.Θset \ singularBoundary M ∧
        ContinuousOn (fun th => M.kdens th x) A)}, ?_, ?_⟩
      · exact MeasureTheory.ae_iff.mp (hH1_cont tb h1 h2)
      · intro x hx
        exact Classical.not_not.mp hx
    obtain ⟨qb, thb, hqb_pos, hqb_sum, hthb_mem, hP0qb⟩ :=
      statopia_math_node_1347167438_985a96d2 M s hs1 q θ hqpos hqsum hinj hmem P0 hP0 hweak
        hliminf ⟨C, hC, hall, hCsub⟩ hcont
    have hDens : ∀ᵐ x ∂M.μ, mixDens M p θs x = mixDens M qb thb x := by
      have hmeasK : ∀ θ : Θ, Measurable (fun x : X => M.kdens θ x) := by
        intro θ
        exact M.hk_meas.comp (measurable_const.prodMk measurable_id)
      have hmeasG : ∀ θ : Θ, Measurable (fun x : X => ENNReal.ofReal (M.kdens θ x)) :=
        fun θ => (hmeasK θ).ennreal_ofReal
      have hker : ∀ (j : Fin t) (A : Set X), MeasurableSet A →
          (M.kernel (θs j)) A = ∫⁻ x in A, ENNReal.ofReal (M.kdens (θs j) x) ∂M.μ :=
        fun j A hA => MeasureTheory.withDensity_apply
          (fun x : X => ENNReal.ofReal (M.kdens (θs j) x)) hA
      have eval_sum : ∀ (F : Finset (Fin t)) (nu : Fin t → Measure X) (A : Set X),
          (∑ j ∈ F, nu j) A = ∑ j ∈ F, nu j A := by
        intro F nu A
        induction F using Finset.induction_on with
        | empty => simp
        | insert a F ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha, MeasureTheory.Measure.coe_add]
          change ⇑(nu a) A + ⇑(∑ j ∈ F, nu j) A = ⇑(nu a) A + ∑ j ∈ F, nu j A
          rw [ih]
      have hfunP : (fun x : X => ENNReal.ofReal (mixDens M p θs x))
          = fun x : X =>
              ∑ j : Fin t, ENNReal.ofReal (p j) * ENNReal.ofReal (M.kdens (θs j) x) := by
        funext x
        show ENNReal.ofReal (∑ j : Fin t, p j * M.kdens (θs j) x) = _
        rw [ENNReal.ofReal_sum_of_nonneg
          (fun j _ => mul_nonneg (le_of_lt (hp j)) (M.kdens_nonneg (θs j) x))]
        exact Finset.sum_congr rfl (fun j _ => ENNReal.ofReal_mul (le_of_lt (hp j)))
      have hfunQ : (fun x : X => ENNReal.ofReal (mixDens M qb thb x))
          = fun x : X =>
              ∑ j : Fin s, ENNReal.ofReal (qb j) * ENNReal.ofReal (M.kdens (thb j) x) := by
        funext x
        show ENNReal.ofReal (∑ j : Fin s, qb j * M.kdens (thb j) x) = _
        rw [ENNReal.ofReal_sum_of_nonneg
          (fun j _ => mul_nonneg (le_of_lt (hqb_pos j)) (M.kdens_nonneg (thb j) x))]
        exact Finset.sum_congr rfl (fun j _ => ENNReal.ofReal_mul (le_of_lt (hqb_pos j)))
      have hP0A : ∀ A : Set X, MeasurableSet A → P0 A
          = ∑ j : Fin t, ENNReal.ofReal (p j) *
              ∫⁻ x in A, ENNReal.ofReal (M.kdens (θs j) x) ∂M.μ := by
        intro A hA
        rw [hP0mix,
          eval_sum Finset.univ (fun j => ENNReal.ofReal (p j) • M.kernel (θs j)) A]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [MeasureTheory.Measure.smul_apply, smul_eq_mul, hker j A hA]
      have hsum_apply : ∀ (F : Finset (Fin t)) (x : X),
          (∑ j ∈ F, fun y : X => ENNReal.ofReal (p j) * ENNReal.ofReal (M.kdens (θs j) y)) x
            = ∑ j ∈ F, ENNReal.ofReal (p j) * ENNReal.ofReal (M.kdens (θs j) x) := by
        intro F x
        induction F using Finset.induction_on with
        | empty => simp
        | insert a F ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha]
          change ENNReal.ofReal (p a) * ENNReal.ofReal (M.kdens (θs a) x)
              + (∑ j ∈ F, fun y : X =>
                  ENNReal.ofReal (p j) * ENNReal.ofReal (M.kdens (θs j) y)) x
            = ENNReal.ofReal (p a) * ENNReal.ofReal (M.kdens (θs a) x)
              + ∑ j ∈ F, ENNReal.ofReal (p j) * ENNReal.ofReal (M.kdens (θs j) x)
          rw [ih]
      have linfun : ∀ (F : Finset (Fin t)) (A : Set X),
          (∫⁻ x in A, (∑ j ∈ F, fun y : X =>
              ENNReal.ofReal (p j) * ENNReal.ofReal (M.kdens (θs j) y)) x ∂M.μ)
            = ∑ j ∈ F, ENNReal.ofReal (p j) *
                ∫⁻ x in A, ENNReal.ofReal (M.kdens (θs j) x) ∂M.μ := by
        intro F A
        induction F using Finset.induction_on with
        | empty => simp
        | insert a F ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha]
          change (∫⁻ x in A, (ENNReal.ofReal (p a) * ENNReal.ofReal (M.kdens (θs a) x)
              + (∑ j ∈ F, fun y : X =>
                  ENNReal.ofReal (p j) * ENNReal.ofReal (M.kdens (θs j) y)) x) ∂M.μ)
            = ENNReal.ofReal (p a) * ∫⁻ x in A, ENNReal.ofReal (M.kdens (θs a) x) ∂M.μ
              + ∑ j ∈ F, ENNReal.ofReal (p j) *
                  ∫⁻ x in A, ENNReal.ofReal (M.kdens (θs j) x) ∂M.μ
          rw [MeasureTheory.lintegral_add_left]
          · rw [MeasureTheory.lintegral_const_mul, ih]
            exact hmeasG (θs a)
          · exact measurable_const.mul (hmeasG (θs a))
      have lin : ∀ (F : Finset (Fin t)) (A : Set X),
          (∫⁻ x in A, ∑ j ∈ F,
              ENNReal.ofReal (p j) * ENNReal.ofReal (M.kdens (θs j) x) ∂M.μ)
            = ∑ j ∈ F, ENNReal.ofReal (p j) *
                ∫⁻ x in A, ENNReal.ofReal (M.kdens (θs j) x) ∂M.μ := by
        intro F A
        have hfun : (fun x : X => ∑ j ∈ F,
              ENNReal.ofReal (p j) * ENNReal.ofReal (M.kdens (θs j) x))
            = fun x : X => (∑ j ∈ F, fun y : X =>
                ENNReal.ofReal (p j) * ENNReal.ofReal (M.kdens (θs j) y)) x := by
          funext x
          exact (hsum_apply F x).symm
        rw [hfun]
        exact linfun F A
      have hIntP : ∀ A : Set X, MeasurableSet A →
          ∫⁻ x in A, ENNReal.ofReal (mixDens M p θs x) ∂M.μ = P0 A := by
        intro A hA
        rw [hP0A A hA, hfunP]
        exact lin Finset.univ A
      have hIntQ : ∀ A : Set X, MeasurableSet A →
          ∫⁻ x in A, ENNReal.ofReal (mixDens M qb thb x) ∂M.μ = P0 A := by
        intro A hA
        rw [hP0qb, MeasureTheory.withDensity_apply
          (fun x : X => ENNReal.ofReal (mixDens M qb thb x)) hA]
      have hmeasP : AEMeasurable (fun x : X => ENNReal.ofReal (mixDens M p θs x)) M.μ := by
        rw [hfunP]
        exact (Finset.measurable_sum Finset.univ
          (fun j _ => measurable_const.mul (hmeasG (θs j)))).aemeasurable
      have hmeasQ : AEMeasurable (fun x : X => ENNReal.ofReal (mixDens M qb thb x)) M.μ := by
        rw [hfunQ]
        exact (Finset.measurable_sum Finset.univ
          (fun j _ => measurable_const.mul (hmeasG (thb j)))).aemeasurable
      have htotP : ∫⁻ x, ENNReal.ofReal (mixDens M p θs x) ∂M.μ ≠ ⊤ := by
        have h : (∫⁻ x, ENNReal.ofReal (mixDens M p θs x) ∂M.μ) = 1 := by
          simpa using hIntP Set.univ MeasurableSet.univ
        rw [h]
        exact ENNReal.one_lt_top.ne
      have htotQ : ∫⁻ x, ENNReal.ofReal (mixDens M qb thb x) ∂M.μ ≠ ⊤ := by
        have h : (∫⁻ x, ENNReal.ofReal (mixDens M qb thb x) ∂M.μ) = 1 := by
          simpa using hIntQ Set.univ MeasurableSet.univ
        rw [h]
        exact ENNReal.one_lt_top.ne
      have hENNeq : (fun x : X => ENNReal.ofReal (mixDens M qb thb x))
          =ᶠ[ae M.μ] fun x : X => ENNReal.ofReal (mixDens M p θs x) :=
        hmeasQ.ae_eq_of_forall_setLIntegral_eq hmeasP htotQ htotP
          (fun A hA _ => by rw [hIntQ A hA, hIntP A hA])
      filter_upwards [hENNeq] with x hx
      have hnnP : 0 ≤ mixDens M p θs x :=
        Finset.sum_nonneg (fun j _ => mul_nonneg (le_of_lt (hp j)) (M.kdens_nonneg (θs j) x))
      have hnnQ : 0 ≤ mixDens M qb thb x :=
        Finset.sum_nonneg (fun j _ => mul_nonneg (le_of_lt (hqb_pos j)) (M.kdens_nonneg (thb j) x))
      have h2 := congrArg ENNReal.toReal hx
      rw [ENNReal.toReal_ofReal hnnQ, ENNReal.toReal_ofReal hnnP] at h2
      exact h2.symm
    let I : Finset Θ := Finset.univ.image thb
    let tht : Fin I.card → Θ := fun k => ((Finset.equivFin I).symm k : Θ)
    let qt : Fin I.card → ℝ :=
      fun k => ∑ j ∈ Finset.univ.filter (fun j => thb j = tht k), qb j
    have htht_inj : Function.Injective tht := by
      intro k l hkl
      refine (Finset.equivFin I).symm.injective (Subtype.ext ?_)
      exact hkl
    have hqt_pos : ∀ k : Fin I.card, 0 < qt k := by
      intro k
      have hmem : tht k ∈ I := ((Finset.equivFin I).symm k).2
      obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hmem
      exact Finset.sum_pos (fun i _ => hqb_pos i)
        ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
    have key : ∀ f : Fin s → ℝ,
        (∑ k : Fin I.card, ∑ j ∈ Finset.univ.filter (fun j => thb j = tht k), f j)
          = ∑ j : Fin s, f j := by
      intro f
      have h1 : ∀ k : Fin I.card,
          (∑ j ∈ Finset.univ.filter (fun j => thb j = tht k), f j)
            = ∑ j : Fin s, if thb j = tht k then f j else 0 := by
        intro k
        rw [Finset.sum_filter]
      rw [Finset.sum_congr rfl (fun k _ => h1 k), Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have hmem : thb j ∈ I := Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
      have hk0 : tht ((Finset.equivFin I) ⟨thb j, hmem⟩) = thb j := by
        simp only [tht, Equiv.symm_apply_apply]
      have hzero : ∀ a ∈ (Finset.univ : Finset (Fin I.card)),
          a ≠ (Finset.equivFin I) ⟨thb j, hmem⟩ →
            (if thb j = tht a then f j else 0) = 0 := by
        intro a _ ha
        have hne : tht a ≠ thb j := by
          intro h
          apply ha
          have hsub : (Finset.equivFin I).symm a = ⟨thb j, hmem⟩ := Subtype.ext h
          calc a = (Finset.equivFin I) ((Finset.equivFin I).symm a) :=
                (Equiv.apply_symm_apply _ _).symm
            _ = (Finset.equivFin I) ⟨thb j, hmem⟩ := by rw [hsub]
        rw [if_neg (Ne.symm hne)]
      have hnot : (Finset.equivFin I) ⟨thb j, hmem⟩ ∉ (Finset.univ : Finset (Fin I.card)) →
          (if thb j = tht ((Finset.equivFin I) ⟨thb j, hmem⟩) then f j else 0) = 0 :=
        fun h => absurd (Finset.mem_univ _) h
      rw [Finset.sum_eq_single _ hzero hnot, if_pos hk0.symm]
    have hqt_sum : ∑ k : Fin I.card, qt k = 1 := by
      have h := key (fun j => qb j)
      rw [hqb_sum] at h
      exact h
    have hmix : ∀ x : X, mixDens M qb thb x = mixDens M qt tht x := by
      intro x
      have hkey := key (fun j => qb j * M.kdens (thb j) x)
      have hstep : (∑ k : Fin I.card, qt k * M.kdens (tht k) x)
          = ∑ k : Fin I.card, ∑ j ∈ Finset.univ.filter (fun j => thb j = tht k),
              qb j * M.kdens (thb j) x := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun j hj => ?_)
        rw [(Finset.mem_filter.mp hj).2]
      show (∑ j : Fin s, qb j * M.kdens (thb j) x)
        = ∑ k : Fin I.card, qt k * M.kdens (tht k) x
      rw [hstep, hkey]
    have hcard_pos : 1 ≤ I.card := by
      have hne : I.Nonempty :=
        ⟨thb ⟨0, hs1⟩, Finset.mem_image.mpr ⟨⟨0, hs1⟩, Finset.mem_univ _, rfl⟩⟩
      exact Finset.card_pos.mpr hne
    have hcard_le : I.card ≤ s := by
      have h1 := Finset.card_image_le (s := (Finset.univ : Finset (Fin s))) (f := thb)
      simpa [I] using h1
    have hfin : ∀ᵐ x ∂M.μ, mixDens M p θs x = mixDens M qt tht x := by
      filter_upwards [hDens] with x hx
      exact hx.trans (hmix x)
    exact (hH3 I.card hcard_pos (lt_of_le_of_lt hcard_le hst) qt tht hqt_pos hqt_sum
      htht_inj) hfin
  have hflat : {ν : ProbabilityMeasure X |
        ∃ (s : ℕ) (q : Fin s → ℝ) (θ : Fin s → Θ),
          1 ≤ s ∧ s < t ∧
            (∀ j : Fin s, 0 < q j) ∧ (∑ j : Fin s, q j = 1) ∧
              Function.Injective θ ∧ (∀ j : Fin s, θ j ∈ M.Θset) ∧
                (ν : Measure X) = mixtureMeasure M q θ}
      = {ν : ProbabilityMeasure X |
        ∃ (s : ℕ), 1 ≤ s ∧ s < t ∧ ∃ (q : Fin s → ℝ) (θ : Fin s → Θ),
          (∀ j : Fin s, 0 < q j) ∧ (∑ j : Fin s, q j = 1) ∧ Function.Injective θ ∧
            (∀ j : Fin s, θ j ∈ M.Θset) ∧ (ν : Measure X) = mixtureMeasure M q θ} := by
    ext ν
    constructor
    · rintro ⟨s, q, θ, h1, h2, h3, h4, h5, h6, h7⟩
      exact ⟨s, h1, h2, q, θ, h3, h4, h5, h6, h7⟩
    · rintro ⟨s, h1, h2, q, θ, h3, h4, h5, h6, h7⟩
      exact ⟨s, q, θ, h1, h2, h3, h4, h5, h6, h7⟩
  have hGeq : {ν : ProbabilityMeasure X |
        ∃ (s : ℕ), 1 ≤ s ∧ s < t ∧ ∃ (q : Fin s → ℝ) (θ : Fin s → Θ),
          (∀ j : Fin s, 0 < q j) ∧ (∑ j : Fin s, q j = 1) ∧ Function.Injective θ ∧
            (∀ j : Fin s, θ j ∈ M.Θset) ∧ (ν : Measure X) = mixtureMeasure M q θ}
      = ⋃ k ∈ Set.Ico (1 : ℕ) t, (fun s : ℕ =>
          {ν : ProbabilityMeasure X |
            ∃ (q : Fin s → ℝ) (θ : Fin s → Θ),
              (∀ j : Fin s, 0 < q j) ∧ (∑ j : Fin s, q j = 1) ∧
                Function.Injective θ ∧ (∀ j : Fin s, θ j ∈ M.Θset) ∧
                  (ν : Measure X) = mixtureMeasure M q θ}) k := by
    ext ν
    constructor
    · rintro ⟨k, h1, h2, hν⟩
      exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨Set.mem_Ico.mpr ⟨h1, h2⟩, hν⟩⟩
    · intro hν
      rw [Set.mem_iUnion] at hν
      obtain ⟨k, hν⟩ := hν
      rw [Set.mem_iUnion] at hν
      obtain ⟨hk, hν⟩ := hν
      rw [Set.mem_Ico] at hk
      exact ⟨k, hk.1, hk.2, hν⟩
  refine ⟨(closure (⋃ s ∈ {s : ℕ | 1 ≤ s ∧ s < t},
      {ν : ProbabilityMeasure X |
        ∃ (q : Fin s → ℝ) (θ : Fin s → Θ),
          (∀ j : Fin s, 0 < q j) ∧ (∑ j : Fin s, q j = 1) ∧
            Function.Injective θ ∧ (∀ j : Fin s, θ j ∈ M.Θset) ∧
              (ν : Measure X) = mixtureMeasure M q θ}))ᶜ, ?_, ?_, ?_, ?_⟩
  · exact isClosed_closure.isOpen_compl
  · exact hnot
  · intro s hs1 hst
    ext x
    constructor
    · rintro ⟨hxU, hxG⟩
      obtain ⟨q, theta, hq, hsum, hinj, hmem, heq⟩ := hxG
      exact hxU (subset_closure (Set.mem_iUnion.mpr
        ⟨s, Set.mem_iUnion.mpr ⟨⟨hs1, hst⟩, ⟨q, theta, hq, hsum, hinj, hmem, heq⟩⟩⟩))
    · intro hx
      exact absurd hx (by simp)
  · rfl
  /- @proof-region region.target-node.session.2542abc1c8c9a89d end -/

end Statlib.Imported


end OfflineCorrectedDP
