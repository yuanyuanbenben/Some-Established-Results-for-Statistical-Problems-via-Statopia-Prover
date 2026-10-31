import Statlib.StatFoundation.BasicAnalysis.ENNRealBridge
import ProverJobs.manual_dp_weakcons_repair_20261031.BoxedWeakCons.CorrectedConsumerBundle
import ProverJobs.manual_dp_weakcons_repair_20261031.BoxedWeakCons.Bundle

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open OfflineCorrectedDP.Statlib.Imported
noncomputable section
namespace OfflineCorrectedDP.OfflineDPConsumer

/-- Mechanical conversion of the two genuine DP moment presentations. -/
lemma consumer_DP_to_boxed (Λ : Measure (ProbabilityMeasure ℝ)) (α : ℝ)
    (Q : Measure ℝ) (h : OfflineCorrectedDP.Statlib.Imported.IsDirichletProcessLaw α Q Λ) :
    OfflineWeakCons.Statlib.Imported.IsDirichletProcessLaw Λ α Q := by
  intro m n A k hm hA hd hsum
  have hmom := h m A k hA hd
  rw [hsum] at hmom
  calc
    (∫⁻ P : ProbabilityMeasure ℝ,
        ENNReal.ofReal (∏ i, ((P : Measure ℝ) (A i)).toReal ^ k i) ∂Λ) =
      ∫⁻ P : ProbabilityMeasure ℝ, ∏ i, ((P : Measure ℝ) (A i)) ^ k i ∂Λ := by
      apply lintegral_congr
      intro P
      rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => pow_nonneg ENNReal.toReal_nonneg _)]
      apply Finset.prod_congr rfl
      intro i hi
      rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (measure_ne_top (P : Measure ℝ) (A i))]
    _ = _ := by
      simpa only [OfflineCorrectedDP.Statlib.Imported.risingFac,
        OfflineWeakCons.Statlib.Imported.risingFactorial] using hmom

variable {X Θ : Type*} [MeasurableSpace X] [MeasurableSpace Θ]
variable [MetricSpace X] [BorelSpace X] [MeasureSpace X] [CompleteSpace X]
  [SecondCountableTopology X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
  [MetricSpace Θ] [BorelSpace Θ] [StandardBorelSpace Θ] [ProperSpace Θ]

/-- Actual BranchB data supply the fixed-atom KL producer, without a free KL input. -/
theorem branchB_location_KL_bound (M : DPMModel X Θ) (t : ℕ) (θs : Fin t → Θ)
    (hB : BranchB M t θs) (p : Fin t → ℝ) (ht : 1 ≤ t)
    (hp : ∀ j, 0 < p j) (hp1 : ∑ j, p j = 1)
    (hinj : Function.Injective θs) (hsupp : ∀ j, θs j ∈ M.Q0.support) :
    LocationKLAt M t θs hB p := by
  let Q : Measure ℝ := Measure.map (hB.eTheta : Θ → ℝ) M.Q0
  have hQ : Q = volume.withDensity (fun y => ENNReal.ofReal (hB.q0 y)) := by
    dsimp [Q]
    rw [hB.hQ0, Measure.map_map hB.eTheta.measurable hB.eTheta.symm.measurable]
    simpa only [Function.comp_def, hB.eTheta.apply_symm_apply] using
      (Measure.map_id (μ := volume.withDensity (fun y => ENNReal.ofReal (hB.q0 y))))
  haveI : IsProbabilityMeasure M.Q0 := M.Q0_prob
  have hQprob : IsProbabilityMeasure Q :=
    Measure.isProbabilityMeasure_map hB.eTheta.measurable.aemeasurable
  have hQmeas : AEMeasurable (fun y => ENNReal.ofReal (hB.q0 y)) volume :=
    hB.hq0_meas.ennreal_ofReal
  obtain ⟨m, M0, hm, hbdd⟩ := hB.T1
  have hM0 : 0 < M0 := by
    have h0 := hbdd 0 ⟨by linarith [hB.hc], hB.hc.le⟩
    linarith
  have hgpos : ∀ x ∈ Set.Icc (-hB.c) hB.c, 0 < hB.g x :=
    fun x hx => lt_of_lt_of_le hm (hbdd x hx).1
  have hderiv : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Set.Ioo (-hB.c) hB.c,
      |deriv hB.g x| ≤ C := by
    obtain ⟨R, hR⟩ := hB.T2_bound
    refine ⟨max R 0 * M0, mul_nonneg (le_max_right _ _) hM0.le, ?_⟩
    intro x hx
    have hx' : x ∈ Set.Icc (-hB.c) hB.c := ⟨hx.1.le, hx.2.le⟩
    have hgp := hgpos x hx'
    have hfactor : |deriv hB.g x| = |deriv hB.g x / hB.g x| * hB.g x := by
      rw [abs_div, abs_of_pos hgp, div_mul_cancel₀ _ hgp.ne']
    rw [hfactor]
    exact mul_le_mul ((hR x hx).trans (le_max_left _ _)) (hbdd x hx').2
      hgp.le (le_max_right _ _)
  have hθinj : Function.Injective (fun j : Fin t => hB.eTheta (θs j)) := by
    intro i j h
    exact hinj (hB.eTheta.injective h)
  have hθsupp : ∀ j : Fin t, hB.eTheta (θs j) ∈ Q.support := by
    intro j
    apply (Measure.mem_support_iff_forall _).mpr
    intro U hU
    have hpre := (Measure.mem_support_iff_forall _).mp (hsupp j)
      (hB.eTheta ⁻¹' U) (hB.hTheta_cont.continuousAt.preimage_mem_nhds hU)
    exact lt_of_lt_of_le hpre (Measure.le_map_apply hB.eTheta.measurable.aemeasurable U)
  have hpi_pos : hB.pi (Set.Ioi (0 : ℝ)) = 1 := by
    haveI : IsProbabilityMeasure hB.pi := hB.hpi_prob
    have hae : ∀ᵐ a ∂hB.pi, 0 < a := by
      rw [← hB.hpiAlpha]
      exact M.piAlpha_pos
    calc
      hB.pi (Set.Ioi (0 : ℝ)) = hB.pi Set.univ := by
        apply measure_congr
        filter_upwards [hae] with a ha
        apply propext
        change (0 < a ↔ True)
        simp [ha]
      _ = 1 := measure_univ
  have hprior : OfflineWeakCons.Statlib.Imported.DPMPriorLaw hB.prior hB.pi hB.Lambdafun Q
      (fun x θ => hB.g (x - θ)) := by
    refine ⟨fun α hα => consumer_DP_to_boxed _ _ _ (hB.hDPMPrior.1 α hα), ?_⟩
    exact hB.hDPMPrior.2
  intro eps heps
  exact OfflineWeakCons.Statlib.Imported.weakCons_H4_fixed_atoms_local
    hB.g (fun y => ENNReal.ofReal (hB.q0 y)) (-hB.c) hB.c Q hB.pi hB.Lambdafun hB.prior
    t p (fun j => hB.eTheta (θs j))
    (branchB_fixed_atom_lower_bounds M t θs hB) eps hB.hg_meas hB.hg_nonneg hB.hg_int
    hgpos hB.hB1_zero hB.T2_diff hderiv ⟨m, M0, hm, hbdd⟩ hQ hQmeas hQprob
    hB.hpi_prob hpi_pos hB.hLam_aemeas hprior ht hp hp1 hθinj hθsupp heps

/-- Original B-side assumptions now give BranchHAt with no extra premise. -/
theorem branchB_to_at_bound (M : DPMModel X Θ)
    (hmu_finite : ∀ K : Set X, IsCompact K → M.μ K < ∞)
    (t : ℕ) (θs : Fin t → Θ) (hB : BranchB M t θs) (p : Fin t → ℝ) (ht : 1 ≤ t)
    (hp : ∀ j, 0 < p j) (hp1 : ∑ j, p j = 1)
    (hinj : Function.Injective θs) (hsupp : ∀ j, θs j ∈ M.Q0.support) :
    BranchHAt M t θs p :=
  branchB_to_at M hmu_finite t θs hB p
    (branchB_location_KL_bound M t θs hB p ht hp hp1 hinj hsupp)

/-- Main's B-or-H input, discharged from genuine producer proofs. -/
theorem original_branch_to_at_bound (M : DPMModel X Θ)
    (hmu_finite : ∀ K : Set X, IsCompact K → M.μ K < ∞)
    (t : ℕ) (θs : Fin t → Θ) (p : Fin t → ℝ) (ht : 1 ≤ t)
    (hp : ∀ j, 0 < p j) (hp1 : ∑ j, p j = 1)
    (hinj : Function.Injective θs) (hsupp : ∀ j, θs j ∈ M.Q0.support)
    (hbranch : Nonempty (BranchB M t θs) ∨ BranchH M t θs) :
    BranchHAt M t θs p :=
  original_branch_to_at M hmu_finite t θs p ht hp hp1 hinj hsupp
    (fun hB => branchB_location_KL_bound M t θs hB p ht hp hp1 hinj hsupp) hbranch

end OfflineCorrectedDP.OfflineDPConsumer

namespace OfflineWeakCons.Statlib.Imported
theorem weakCons_parametric_KL_fixed_atoms_local : ∀ (g : ℝ → ℝ) (q0 : ℝ → ℝ≥0∞) (a b : ℝ)
    (Q0 π : Measure ℝ) (Λfun : ℝ → Measure (ProbabilityMeasure ℝ))
    (prior : Measure (ℝ → ℝ))
    (t : ℕ) (p thetaStar : Fin t → ℝ)
    (hT4_local : ∀ j : Fin t, ∃ L eta : ℝ, 0 < L ∧ 0 < eta ∧
      ∀ᵐ theta ∂volume, theta ∈ Set.Ioo (thetaStar j - eta) (thetaStar j + eta) →
        ENNReal.ofReal L ≤ q0 theta)
    (eps : ℝ)
    (hg_meas : Measurable g)
    (hg_nonneg : ∀ x : ℝ, 0 ≤ g x)
    (hg_int : ∫⁻ x : ℝ, ENNReal.ofReal (g x) ∂volume = 1)
    (hB1_pos : ∀ x ∈ Set.Icc a b, 0 < g x)
    (hB1_zero : ∀ x : ℝ, x ∉ Set.Icc a b → g x = 0)
    (hB2_diff : DifferentiableOn ℝ g (Set.Ioo a b))
    (hB2_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Set.Ioo a b, |deriv g x| ≤ C)
    (hT1 : ∃ m M : ℝ, 0 < m ∧ ∀ x ∈ Set.Icc a b, m ≤ g x ∧ g x ≤ M)
    (hB3 : Q0 = volume.withDensity q0)
    (hq0_meas : AEMeasurable q0 volume)
    (hQ0_prob : IsProbabilityMeasure Q0)
    (hpi_prob : IsProbabilityMeasure π)
    (hpi_pos : π (Set.Ioi (0 : ℝ)) = 1)
    (hLam_aemeas : AEMeasurable (fun α : ℝ => Λfun α) π)
    (hprior : DPMPriorLaw prior π Λfun Q0 (fun x θ => g (x - θ)))
    (ht : 1 ≤ t)
    (hp_pos : ∀ j : Fin t, 0 < p j)
    (hp_sum : ∑ j : Fin t, p j = 1)
    (hθ_inj : Function.Injective thetaStar)
    (hθ_supp : ∀ j : Fin t, thetaStar j ∈ Q0.support)
    (heps : 0 < eps),
    0 < (π.bind Λfun) {P : ProbabilityMeasure ℝ |
      InformationTheory.klDiv
        (volume.withDensity fun y => ENNReal.ofReal (∑ j, p j * g (y - thetaStar j)))
        (volume.withDensity fun y => ENNReal.ofReal (∫ θ, g (y - θ) ∂(P : Measure ℝ)))
          < ENNReal.ofReal eps} := by
  intro g q0 a b Q0 π Λfun prior t p θstar hT4_local ε hg_meas hg_nonneg hg_int
    hB1_pos hB1_zero hB2_diff hB2_bound hT1 hB3 hq0_meas hQ0_prob
    hpi_prob hpi_pos hLam_aemeas hprior ht hp_pos hp_sum hθ_inj hθ_supp hε
  obtain ⟨hDPLaw, hprior_eq⟩ := hprior
  obtain ⟨m, M, hm_pos, hmM⟩ := hT1
  have hab : a ≤ b := by
    by_contra hab
    have hz : ∀ x, g x = 0 := by
      intro x
      apply hB1_zero x
      intro hx
      exact hab (hx.1.trans hx.2)
    have : (0 : ℝ≥0∞) = 1 := by simpa [hz] using hg_int
    exact zero_ne_one this
  have hM_pos : 0 < M := lt_of_lt_of_le hm_pos
    ((hmM a ⟨le_rfl, hab⟩).1.trans (hmM a ⟨le_rfl, hab⟩).2)
  have hg_le_M : ∀ x, g x ≤ M := by
    intro x
    by_cases hx : x ∈ Set.Icc a b
    · exact (hmM x hx).2
    · rw [hB1_zero x hx]; exact hM_pos.le
  have hLam_prob : ∀ α : ℝ, 0 < α → IsProbabilityMeasure (Λfun α) := by
    intro α hα
    have hdisj : ∀ i j : Fin 1, i ≠ j → Disjoint (Set.univ : Set ℝ) (Set.univ : Set ℝ) :=
      fun i j hij => absurd (Subsingleton.elim i j) hij
    have hmom := hDPLaw α hα 1 0 (fun _ => (Set.univ : Set ℝ)) (fun _ => 0) le_rfl
      (fun _ => MeasurableSet.univ) hdisj (by simp)
    have h1 : ∫⁻ P, (1 : ℝ≥0∞) ∂(Λfun α) = 1 := by
      simpa [risingFactorial] using hmom
    have h2 : ∫⁻ P, (1 : ℝ≥0∞) ∂(Λfun α) = (Λfun α) Set.univ := by
      simpa using MeasureTheory.lintegral_const
    rw [h2] at h1
    exact ⟨h1⟩

  have hΦ_meas : Measurable (fun P : ProbabilityMeasure ℝ => fun x : ℝ => ∫ θ, g (x - θ) ∂(P : Measure ℝ)) := by
    rw [measurable_pi_iff]
    intro x
    have hF : Measurable fun θ : ℝ => ENNReal.ofReal (g (x - θ)) := by
      have h1 : Measurable fun θ : ℝ => x - θ :=
        (measurable_const : Measurable fun _ : ℝ => x).sub measurable_id
      exact ENNReal.measurable_ofReal.comp (hg_meas.comp h1)
    have hcoe : Measurable fun P : ProbabilityMeasure ℝ => (P : Measure ℝ) := measurable_subtype_coe
    have htr : Measurable fun a : ℝ≥0∞ => a.toReal := by fun_prop
    have h2 : Measurable fun P : ProbabilityMeasure ℝ =>
        (∫⁻ θ, ENNReal.ofReal (g (x - θ)) ∂(P : Measure ℝ)).toReal := by
      have h3 : Measurable fun P : ProbabilityMeasure ℝ =>
          ∫⁻ θ, ENNReal.ofReal (g (x - θ)) ∂(P : Measure ℝ) :=
        (MeasureTheory.Measure.measurable_lintegral hF).comp hcoe
      exact htr.comp h3
    have h5 : ∀ P : ProbabilityMeasure ℝ,
        (∫⁻ θ, ENNReal.ofReal (g (x - θ)) ∂(P : Measure ℝ)).toReal
          = ∫ θ, g (x - θ) ∂(P : Measure ℝ) := by
      intro P
      refine Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.lintegral_toReal_eq_integral_of_nonneg
        (Eventually.of_forall fun θ => hg_nonneg (x - θ)) ?_
      refine MeasureTheory.Integrable.of_bound ?_ M ?_
      · exact (hg_meas.comp
          ((measurable_const : Measurable fun _ : ℝ => x).sub measurable_id)).aestronglyMeasurable
      · filter_upwards with θ
        rw [Real.norm_eq_abs, abs_of_nonneg (hg_nonneg (x - θ))]
        exact hg_le_M (x - θ)
    have h5fun : (fun P : ProbabilityMeasure ℝ =>
          (∫⁻ θ, ENNReal.ofReal (g (x - θ)) ∂(P : Measure ℝ)).toReal)
        = fun P : ProbabilityMeasure ℝ => ∫ θ, g (x - θ) ∂(P : Measure ℝ) :=
      funext h5
    rw [h5fun] at h2
    exact h2


  have hf_meas : Measurable fun x : ℝ => ∑ j, p j * g (x - θstar j) := by
    exact Finset.measurable_sum Finset.univ (fun j _ =>
      measurable_const.mul (hg_meas.comp (measurable_id.sub measurable_const)))
  have hf_nonneg : ∀ x : ℝ, 0 ≤ ∑ j, p j * g (x - θstar j) := by
    intro x
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hp_pos j).le (hg_nonneg _)
  have hf_norm : ∫⁻ x, ENNReal.ofReal (∑ j, p j * g (x - θstar j)) ∂volume = 1 := by
    have hsum : ∀ x, ENNReal.ofReal (∑ j, p j * g (x - θstar j)) =
        ∑ j, ENNReal.ofReal (p j) * ENNReal.ofReal (g (x - θstar j)) := by
      intro x
      rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (hp_pos j).le (hg_nonneg _))]
      exact Finset.sum_congr rfl (fun j _ => ENNReal.ofReal_mul (hp_pos j).le)
    simp_rw [hsum]
    have hterms : ∀ j : Fin t, Measurable (fun x : ℝ =>
        ENNReal.ofReal (p j) * ENNReal.ofReal (g (x - θstar j))) := by
      intro j
      exact measurable_const.mul (ENNReal.measurable_ofReal.comp
        (hg_meas.comp (measurable_id.sub measurable_const)))
    rw [lintegral_finset_sum Finset.univ (fun j _ => hterms j)]
    have hintj : ∀ j : Fin t,
        (∫⁻ x, ENNReal.ofReal (p j) * ENNReal.ofReal (g (x - θstar j)) ∂volume) =
          ENNReal.ofReal (p j) := by
      intro j
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_sub_right_eq_self (fun x => ENNReal.ofReal (g x)) (θstar j),
        hg_int, mul_one]
    simp_rw [hintj]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => (hp_pos j).le), hp_sum]
    simp
  have hΦx_meas : ∀ P : ProbabilityMeasure ℝ,
      Measurable (fun x : ℝ => ∫ θ, g (x - θ) ∂(P : Measure ℝ)) := by
    intro P
    exact ((hg_meas.comp (measurable_fst.sub measurable_snd)).stronglyMeasurable.integral_prod_right').measurable
  obtain ⟨A, hA, hA_pos, hA_meas, hAsub⟩ := weakCons_hA_exists_local
    g q0 a b Q0 Λfun t p θstar hT4_local ε hg_meas hg_nonneg hg_int
    hB1_pos hB1_zero hB2_diff hB2_bound ⟨m,M,hm_pos,hmM⟩ hB3 hq0_meas
    hQ0_prob hDPLaw ht hp_pos hp_sum hθ_inj hθ_supp hε
  let Φ := fun P : ProbabilityMeasure ℝ => fun x : ℝ => ∫ θ, g (x - θ) ∂(P : Measure ℝ)
  have hmass : (π.bind Λfun) A = ∫⁻ α, Λfun α A ∂π := Measure.bind_apply hA hLam_aemeas
  set C : ℕ → Set (Set.Ioi (0 : ℝ)) :=
    fun n => {x | ENNReal.ofReal (1 / ((n : ℝ) + 1)) ≤ Λfun (x : ℝ) A} with hC
  set B : ℕ → Set ℝ := fun n => Subtype.val '' C n with hB
  have hC_meas : ∀ n, MeasurableSet (C n) := by
    intro n
    change MeasurableSet ((fun x : Set.Ioi (0 : ℝ) => Λfun (x : ℝ) A) ⁻¹'
      Set.Ici (ENNReal.ofReal (1 / ((n : ℝ) + 1))))
    exact measurableSet_Ici.preimage hA_meas
  have hB_meas : ∀ n, MeasurableSet (B n) := by
    intro n
    change MeasurableSet (Subtype.val '' C n)
    exact MeasurableSet.subtype_image measurableSet_Ioi (hC_meas n)
  have hex : ∀ α : ℝ, 0 < α → ∃ n : ℕ, ENNReal.ofReal (1 / ((n : ℝ) + 1)) ≤ Λfun α A := by
    intro α hα
    rcases eq_or_ne (Λfun α A) ⊤ with htop | htop
    · exact ⟨0, by rw [htop]; simp⟩
    · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (ε := (Λfun α A).toReal)
        (ENNReal.toReal_pos (hA_pos α hα).ne' htop)
      exact ⟨n, by rw [← ENNReal.ofReal_toReal htop]; exact ENNReal.ofReal_le_ofReal hn.le⟩
  have hcover : Set.Ioi (0 : ℝ) ⊆ ⋃ n, B n := by
    intro α hα
    obtain ⟨n, hn⟩ := hex α hα
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    simp only [hB, hC, Set.mem_image, Set.mem_setOf_eq]
    exact ⟨⟨α, hα⟩, hn, rfl⟩
  have hkey : (1 : ℝ≥0∞) ≤ ∑' n, π (B n) := by
    have h1 : π (Set.Ioi (0 : ℝ)) ≤ π (⋃ n, B n) := measure_mono hcover
    have h3 : π (⋃ n, B n) ≤ ∑' n, π (B n) := measure_iUnion_le _
    exact le_trans (le_of_eq hpi_pos.symm) (le_trans h1 h3)
  obtain ⟨n, hn⟩ : ∃ n, 0 < π (B n) := by
    by_contra h
    push_neg at h
    have hz : ∀ n, π (B n) = 0 := fun n => le_antisymm (h n) (zero_le _)
    have hcongr : (∑' n, π (B n)) = ∑' n, (0 : ℝ≥0∞) := tsum_congr hz
    have hzero : (∑' n, π (B n)) = 0 := by rw [hcongr]; simp
    rw [hzero] at hkey
    exact absurd hkey (not_le.mpr zero_lt_one)
  have hbdd : ENNReal.ofReal (1 / ((n : ℝ) + 1)) * π (B n) ≤ ∫⁻ α, Λfun α A ∂π := by
    have key : ∀ α : ℝ,
        (B n).indicator (fun _ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) α ≤ Λfun α A := by
      intro α
      by_cases hα : α ∈ B n
      · rw [Set.indicator_of_mem hα]
        obtain ⟨y, hy, hyα⟩ := by
          simpa only [hB, hC, Set.mem_image, Set.mem_setOf_eq] using hα
        rw [← hyα]
        exact hy
      · rw [Set.indicator_of_notMem hα]
        exact zero_le _
    calc ENNReal.ofReal (1 / ((n : ℝ) + 1)) * π (B n)
        = ∫⁻ α, (B n).indicator (fun _ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) α ∂π :=
          (lintegral_indicator_const (hB_meas n) _).symm
      _ ≤ ∫⁻ α, Λfun α A ∂π := lintegral_mono key
  have hpos : 0 < ∫⁻ α, Λfun α A ∂π := by
    have hc : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
      rw [ENNReal.ofReal_pos]; positivity
    exact lt_of_lt_of_le (by positivity) hbdd
  have hmA : 0 < (π.bind Λfun) A := by rw [hmass]; exact hpos
  exact lt_of_lt_of_le hmA (measure_mono (fun P hP =>
    local_InKL_klDiv ε hε _ _ hf_meas (hΦx_meas P) hf_nonneg hf_norm (hAsub P hP)))
end OfflineWeakCons.Statlib.Imported

namespace OfflineCorrectedDP.OfflineDPConsumer
variable {X Θ : Type*} [MeasurableSpace X] [MeasurableSpace Θ]
variable [MetricSpace X] [BorelSpace X] [MeasureSpace X] [CompleteSpace X]
  [SecondCountableTopology X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
  [MetricSpace Θ] [BorelSpace Θ] [StandardBorelSpace Θ] [ProperSpace Θ]
theorem branchB_parametric_R_KL_bound (M : DPMModel X Θ) (t : ℕ) (θs : Fin t → Θ)
    (hB : BranchB M t θs) (p : Fin t → ℝ) (ht : 1 ≤ t)
    (hp : ∀ j, 0 < p j) (hp1 : ∑ j, p j = 1)
    (hinj : Function.Injective θs) (hsupp : ∀ j, θs j ∈ M.Q0.support) :
    ∀ eps : ℝ, 0 < eps → 0 < (hB.pi.bind hB.Lambdafun)
      {P : ProbabilityMeasure ℝ | InformationTheory.klDiv
        (volume.withDensity fun y => ENNReal.ofReal (∑ j, p j * hB.g (y - hB.eTheta (θs j))))
        (volume.withDensity fun y => ENNReal.ofReal (∫ θ, hB.g (y - θ) ∂(P : Measure ℝ)))
          < ENNReal.ofReal eps} := by
  let Q : Measure ℝ := Measure.map (hB.eTheta : Θ → ℝ) M.Q0
  have hQ : Q = volume.withDensity (fun y => ENNReal.ofReal (hB.q0 y)) := by
    dsimp [Q]
    rw [hB.hQ0, Measure.map_map hB.eTheta.measurable hB.eTheta.symm.measurable]
    simpa only [Function.comp_def, hB.eTheta.apply_symm_apply] using
      (Measure.map_id (μ := volume.withDensity (fun y => ENNReal.ofReal (hB.q0 y))))
  haveI : IsProbabilityMeasure M.Q0 := M.Q0_prob
  have hQprob : IsProbabilityMeasure Q :=
    Measure.isProbabilityMeasure_map hB.eTheta.measurable.aemeasurable
  have hQmeas : AEMeasurable (fun y => ENNReal.ofReal (hB.q0 y)) volume :=
    hB.hq0_meas.ennreal_ofReal
  obtain ⟨m, M0, hm, hbdd⟩ := hB.T1
  have hM0 : 0 < M0 := by
    have h0 := hbdd 0 ⟨by linarith [hB.hc], hB.hc.le⟩
    linarith
  have hgpos : ∀ x ∈ Set.Icc (-hB.c) hB.c, 0 < hB.g x :=
    fun x hx => lt_of_lt_of_le hm (hbdd x hx).1
  have hderiv : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Set.Ioo (-hB.c) hB.c,
      |deriv hB.g x| ≤ C := by
    obtain ⟨R, hR⟩ := hB.T2_bound
    refine ⟨max R 0 * M0, mul_nonneg (le_max_right _ _) hM0.le, ?_⟩
    intro x hx
    have hx' : x ∈ Set.Icc (-hB.c) hB.c := ⟨hx.1.le, hx.2.le⟩
    have hgp := hgpos x hx'
    have hfactor : |deriv hB.g x| = |deriv hB.g x / hB.g x| * hB.g x := by
      rw [abs_div, abs_of_pos hgp, div_mul_cancel₀ _ hgp.ne']
    rw [hfactor]
    exact mul_le_mul ((hR x hx).trans (le_max_left _ _)) (hbdd x hx').2
      hgp.le (le_max_right _ _)
  have hθinj : Function.Injective (fun j : Fin t => hB.eTheta (θs j)) := by
    intro i j h
    exact hinj (hB.eTheta.injective h)
  have hθsupp : ∀ j : Fin t, hB.eTheta (θs j) ∈ Q.support := by
    intro j
    apply (Measure.mem_support_iff_forall _).mpr
    intro U hU
    have hpre := (Measure.mem_support_iff_forall _).mp (hsupp j)
      (hB.eTheta ⁻¹' U) (hB.hTheta_cont.continuousAt.preimage_mem_nhds hU)
    exact lt_of_lt_of_le hpre (Measure.le_map_apply hB.eTheta.measurable.aemeasurable U)
  have hpi_pos : hB.pi (Set.Ioi (0 : ℝ)) = 1 := by
    haveI : IsProbabilityMeasure hB.pi := hB.hpi_prob
    have hae : ∀ᵐ a ∂hB.pi, 0 < a := by
      rw [← hB.hpiAlpha]
      exact M.piAlpha_pos
    calc
      hB.pi (Set.Ioi (0 : ℝ)) = hB.pi Set.univ := by
        apply measure_congr
        filter_upwards [hae] with a ha
        apply propext
        change (0 < a ↔ True)
        simp [ha]
      _ = 1 := measure_univ
  have hprior : OfflineWeakCons.Statlib.Imported.DPMPriorLaw hB.prior hB.pi hB.Lambdafun Q
      (fun x θ => hB.g (x - θ)) := by
    refine ⟨fun α hα => consumer_DP_to_boxed _ _ _ (hB.hDPMPrior.1 α hα), ?_⟩
    exact hB.hDPMPrior.2
  intro eps heps
  exact OfflineWeakCons.Statlib.Imported.weakCons_parametric_KL_fixed_atoms_local
    hB.g (fun y => ENNReal.ofReal (hB.q0 y)) (-hB.c) hB.c Q hB.pi hB.Lambdafun hB.prior
    t p (fun j => hB.eTheta (θs j))
    (branchB_fixed_atom_lower_bounds M t θs hB) eps hB.hg_meas hB.hg_nonneg hB.hg_int
    hgpos hB.hB1_zero hB.T2_diff hderiv ⟨m, M0, hm, hbdd⟩ hQ hQmeas hQprob
    hB.hpi_prob hpi_pos hB.hLam_aemeas hprior ht hp hp1 hθinj hθsupp heps


end OfflineCorrectedDP.OfflineDPConsumer
