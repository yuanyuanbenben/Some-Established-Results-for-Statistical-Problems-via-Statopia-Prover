import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.ExternalNodes.Node_6515c10a3b2a6920f75d
import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.Vocabulary
import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.ProvedNodes
import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.Base

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace Statlib.Imported

theorem Theorem_2_2_thm_negative_both_parts_i_and_ii_using_v5_with_corrigendum
    (d : ℕ) (hd : 0 < d) (U : HMCState d → ℝ) (hU_nonneg : ∀ x, 0 ≤ U x)
    (hU_diff : Differentiable ℝ U)
    (ε : ℝ) (hε : 0 < ε) (𝔏 : Measure ℕ) [IsProbabilityMeasure 𝔏]
    (π : Measure (HMCState d)) [IsProbabilityMeasure π]
    (hπ : ∃ c : ℝ, 0 < c ∧
      π = volume.withDensity (fun x => ENNReal.ofReal (c * Real.exp (- U x)))) :
    ((Tendsto (fun x : HMCState d => ‖gradient U x‖ / ‖x‖)
          (Filter.cocompact (HMCState d)) Filter.atTop ∧
        (∃ C : ℝ, ∀ x y : HMCState d, ‖y‖ ≥ 2 * ‖x‖ → C ≤ 2 * ‖x‖ →
          ‖gradient U y‖ ≥ 3 * ‖gradient U x‖) ∧
        (∀ L : ℕ, 𝔏 {L} ≠ 0 → ∀ R : ℝ, ∃ K : ℝ, ∀ x y : HMCState d,
          K ≤ ‖x‖ → (2 : ℝ) ^ L * ‖x‖ ≤ ‖y‖ →
            U x - U y - (1 / 2) * ‖x‖ ^ 2 ≤ -R)) →
      ¬ IsGeometricallyErgodic (hmcKernel U ε 𝔏) π) ∧
    ((∃ M : ℝ, ∀ x : HMCState d, ‖gradient U x‖ ≤ M) ∧
        (∀ s : ℝ, 0 < s → ∫⁻ x, ENNReal.ofReal (Real.exp (s * ‖x‖)) ∂π = ⊤) →
      ¬ IsGeometricallyErgodic (hmcKernel U ε 𝔏) π)
:= by
  /- @proof-region region.root.df2c32308c60 begin -/
  obtain ⟨hkern, hprob, hmeas⟩ :=
    statopia_math_node_60244864_4d03ea71 d hd U hU_diff ε hε 𝔏
  constructor
  · rintro ⟨hT, hC, h3⟩ hge
    have h_atom : ∀ x : HMCState d, π {x} = 0 := by
      have hvol : ∀ x : HMCState d, (volume : Measure (HMCState d)) {x} = 0 := by
        intro x
        haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
        haveI hpino : NoAtoms (volume : Measure (Fin d → ℝ)) := by
          rw [MeasureTheory.volume_pi]
          exact MeasureTheory.Measure.pi_noAtoms' (μ := fun _ : Fin d => (volume : Measure ℝ))
        have hmp : MeasurePreserving (WithLp.toLp 2)
            (volume : Measure (Fin d → ℝ)) (volume : Measure (HMCState d)) :=
          PiLp.volume_preserving_toLp (Fin d)
        have hpre : (WithLp.toLp 2 : (Fin d → ℝ) → HMCState d) ⁻¹' {x}
            = {WithLp.ofLp x} := by
          ext a
          simp only [Set.mem_preimage, Set.mem_singleton_iff]
          constructor
          · intro h
            rw [← h, WithLp.ofLp_toLp]
          · intro h
            rw [h, WithLp.toLp_ofLp]
        rw [← hmp.map_eq, Measure.map_apply hmp.measurable (measurableSet_singleton x), hpre]
        exact (inferInstance : NoAtoms (volume : Measure (Fin d → ℝ))).measure_singleton _
      haveI : NoAtoms (volume : Measure (HMCState d)) := ⟨hvol⟩
      obtain ⟨c, hc, hπeq⟩ := hπ
      haveI : NoAtoms π := by
        rw [hπeq]
        exact MeasureTheory.noAtoms_withDensity _
      intro x
      exact (inferInstance : NoAtoms π).measure_singleton x
    have hzero : ∀ x : HMCState d,
        (((gaussianMomentum d).prod (volume.restrict (Set.Icc (0 : ℝ) 1))).map
          (fun w : HMCState d × ℝ => hmcStep U ε 0 x w.1 w.2)) {x} = 1 := by
      intro x
      have hconst : (fun w : HMCState d × ℝ => hmcStep U ε 0 x w.1 w.2) = fun _ => x := by
        funext w
        simp [hmcStep, leapfrogFlow]
      haveI hIcc : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
        refine ⟨?_⟩
        rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
        simp
      have hlinmeas : Measurable ⇑(EuclideanSpace.equiv (Fin d) ℝ).symm :=
        (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.measurable
      haveI hgauss : IsProbabilityMeasure (gaussianMomentum d) := by
        rw [gaussianMomentum]
        exact MeasureTheory.Measure.isProbabilityMeasure_map hlinmeas.aemeasurable
      have hpre : (fun _ : HMCState d × ℝ => x) ⁻¹' {x} = Set.univ := by
        ext w
        simp
      rw [hconst, Measure.map_apply measurable_const (measurableSet_singleton x), hpre,
        measure_univ]
    have hself : ∀ (L : ℕ), 1 ≤ L → ∀ x : HMCState d,
        ENNReal.ofReal (∫ p, (1 - acceptProb U ε L (x, p)) ∂(gaussianMomentum d))
          ≤ (((gaussianMomentum d).prod (volume.restrict (Set.Icc (0 : ℝ) 1))).map
              (fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2)) {x} := by
      have hgrad_meas : Measurable (fun x : HMCState d => gradient U x) := by
        have hfd : Measurable (fun x : HMCState d => fderiv ℝ U x) := measurable_fderiv ℝ U
        have htoD : Measurable ⇑(InnerProductSpace.toDual ℝ (HMCState d)).symm :=
          (InnerProductSpace.toDual ℝ (HMCState d)).symm.continuous.measurable
        exact htoD.comp hfd
      intro L hL x
      exact (statopia_math_node_1760066137_9d09a34f d hd U hU_diff hgrad_meas ε hε L).2.2.1 x
    have hgrad : ∀ N : ℝ, ∃ S : ℝ, ∀ z : HMCState d, S ≤ ‖z‖ → N * ‖z‖ ≤ ‖gradient U z‖ := by
      intro N
      obtain ⟨r, hr⟩ :=
        (Metric.mem_cocompact_iff_closedBall_compl_subset (0 : HMCState d)).mp
          (hT.eventually_ge_atTop N)
      refine ⟨max r 0 + 1, fun z hz => ?_⟩
      have hzK : z ∉ Metric.closedBall (0 : HMCState d) r := by
        intro hmem
        have h1 : ‖z‖ ≤ r := by
          simpa [Metric.mem_closedBall, dist_zero_right] using hmem
        have h2 : r ≤ max r 0 := le_max_left r 0
        linarith
      have hpos : 0 < ‖z‖ := by
        have h0 : (0 : ℝ) ≤ max r 0 := le_max_right r 0
        linarith
      exact (le_div_iff₀ hpos).mp (hr hzK)
    have hreject : ∀ (L : ℕ), 1 ≤ L → 𝔏 {L} ≠ 0 → ∀ δ : ℝ, 0 < δ → ∃ S : ℝ,
        ∀ x : HMCState d, S ≤ ‖x‖ →
          (1 - (∫ p, (1 - acceptProb U ε L (x, p)) ∂(gaussianMomentum d))) ≤ δ := by
      intro L hL hLne δ hδ
      obtain ⟨S, hSacc⟩ :=
        statopia_math_node_2631634989_f6938273 d hd U hU_diff ε hε L hL hgrad hC
          (h3 L hLne) δ hδ
      exact ⟨S, fun x hx => (hSacc x hx).2⟩
    have hmix :=
      statopia_math_node_3404074719_54f01d46 d hd U ε hε 𝔏 hzero hself hreject
    have hS : ∀ η : ℝ, 0 < η → η < 1 → ∀ N : Set (HMCState d), π N = 0 →
        ∃ x : HMCState d, ENNReal.ofReal (1 - η) ≤ hmcKernel U ε 𝔏 x {x} ∧ x ∉ N := by
      intro η hη hη1 N hN
      obtain ⟨S, hSmix⟩ := hmix η hη
      have hbig : ∃ x : HMCState d, S ≤ ‖x‖ ∧ x ∉ N :=
        statopia_math_node_1382433191_3c3c175b d hd U hU_diff.continuous.measurable π hπ S N hN
      obtain ⟨x, hxS, hxN⟩ := hbig
      refine ⟨x, ?_, hxN⟩
      rw [hkern x {x} (measurableSet_singleton x)]
      exact hSmix x hxS
    exact absurd hge (statopia_math_node_2473568002_d219e28a d hd (hmcKernel U ε 𝔏)
      hprob hmeas π h_atom hS)
  · rintro ⟨⟨M, hM⟩, hmom⟩ hge
    obtain ⟨G, hG, hG0⟩ : ∃ G : ℝ, 0 ≤ G ∧ ∀ x : HMCState d, ‖gradient U x‖ ≤ G :=
      ⟨max M 0, le_max_right _ _, fun x => le_trans (hM x) (le_max_left _ _)⟩
    have hloc_lin :=
      statopia_math_node_1514341555_35b36640 d hd U hU_diff ε hε 𝔏 G hG hG0
    have hlocal : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ x : HMCState d,
        hmcKernel U ε 𝔏 x (Metric.ball x δ) > ENNReal.ofReal (1 - η) := by
      intro η hη
      obtain ⟨δ, hδ, hδx⟩ := hloc_lin η hη
      refine ⟨δ, hδ, fun x => ?_⟩
      have hk := hkern x (Metric.ball x δ) measurableSet_ball
      have hset : (Metric.ball x δ : Set (HMCState d)) = {y : HMCState d | ‖y - x‖ < δ} := by
        ext y
        simp [Metric.mem_ball, dist_eq_norm]
      rw [hk, hset]
      exact hδx x
    obtain ⟨β, hβ, hβfin⟩ := ext_model_1 d (hmcKernel U ε 𝔏) π hlocal hge
    have htop : ∫⁻ x, ENNReal.ofReal (Real.exp (β * ‖x‖)) ∂π = ⊤ := hmom β hβ
    rw [htop] at hβfin
    exact absurd hβfin (lt_irrefl ⊤)
  /- @proof-region region.root.df2c32308c60 end -/

end Statlib.Imported

end

-- Paper root revision 3f35a4bb-5676-44d0-9cee-fd02177735a5
