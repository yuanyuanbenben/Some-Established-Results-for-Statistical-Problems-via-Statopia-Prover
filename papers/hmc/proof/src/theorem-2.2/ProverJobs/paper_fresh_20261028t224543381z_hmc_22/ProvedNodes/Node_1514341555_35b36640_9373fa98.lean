import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.Vocabulary
import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.Base
import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.ProvedNodes.Node_1760066137_9d09a34f_f99c9d1e
import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.ProvedNodes.Node_2434035012_bf892b59_840b5159

namespace PaperProofTasks.paper_fresh_20261028t224543381z_hmc_22


open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open _root_.PaperProofTasks.paper_fresh_20261028t224543381z_hmc_22.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace Statlib.Imported


set_option autoImplicit false in
theorem statopia_math_node_1514341555_35b36640 : ∀ (d : ℕ) (hd : 0 < d) (U : HMCState d → ℝ) (hU_diff : Differentiable ℝ U)
    (ε : ℝ) (hε : 0 < ε)
    (Ldist : Measure ℕ) [IsProbabilityMeasure Ldist]
    (G : ℝ) (hG_nonneg : 0 ≤ G) (hG_bound : ∀ x : HMCState d, ‖gradient U x‖ ≤ G),
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ x : HMCState d,
      ENNReal.ofReal (1 - η) <
        ∫⁻ L : ℕ,
          Measure.map (fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2)
            ((gaussianMomentum d).prod (volume.restrict (Set.Icc (0 : ℝ) 1)))
            {y : HMCState d | ‖y - x‖ < δ}
        ∂Ldist := by
  /- @proof-region region.target-node.session.e6cae497bdc87d23 begin -/
  intro d hd U hU_diff ε hε Ldist hLdist G hG_nonneg hG_bound η hη
  haveI : IsProbabilityMeasure Ldist := hLdist
  have hgrad_meas : Measurable (fun x : HMCState d => gradient U x) := by
    have h1 : Measurable fun x : HMCState d => fderiv ℝ U x := measurable_fderiv ℝ U
    have h2 : Measurable fun L : HMCState d →L[ℝ] ℝ =>
        (InnerProductSpace.toDual ℝ (HMCState d)).symm L :=
      (InnerProductSpace.toDual ℝ (HMCState d)).symm.continuous.measurable
    have h3 := h2.comp h1
    simpa only [Function.comp_apply, gradient] using h3
  have hflow_meas : ∀ (L : ℕ) (x : HMCState d),
      Measurable (fun p : HMCState d => (leapfrogFlow U ε L (x, p)).1) ∧
        Measurable (fun p : HMCState d => (leapfrogFlow U ε L (x, p)).2) := by
    intro L
    induction L with
    | zero =>
        intro x
        constructor
        · simpa [leapfrogFlow] using (measurable_const : Measurable fun _ : HMCState d => x)
        · simpa [leapfrogFlow] using (measurable_id : Measurable fun p : HMCState d => p)
    | succ n ih =>
        intro x
        obtain ⟨ih1, ih2⟩ := ih x
        have hiter : leapfrogFlow U ε (n + 1) = leapfrogStep U ε ∘ leapfrogFlow U ε n := by
          simp only [leapfrogFlow, Function.iterate_succ']
        have hstep1 : ∀ z : HMCState d × HMCState d, (leapfrogStep U ε z).1 =
            z.1 + ε • (z.2 - (ε / 2) • gradient U z.1) := fun z => rfl
        have hstep2 : ∀ z : HMCState d × HMCState d, (leapfrogStep U ε z).2 =
            (z.2 - (ε / 2) • gradient U z.1) -
              (ε / 2) • gradient U (z.1 + ε • (z.2 - (ε / 2) • gradient U z.1)) := fun z => rfl
        constructor
        · have e1 : (fun p : HMCState d => (leapfrogFlow U ε (n + 1) (x, p)).1)
              = fun p => (leapfrogFlow U ε n (x, p)).1 +
                  ε • ((leapfrogFlow U ε n (x, p)).2 - (ε / 2) • gradient U ((leapfrogFlow U ε n (x, p)).1)) := by
            funext p
            rw [hiter, Function.comp_apply]
            exact hstep1 _
          rw [e1]
          exact ih1.add (measurable_const.smul (ih2.sub (measurable_const.smul (hgrad_meas.comp ih1))))
        · have e2 : (fun p : HMCState d => (leapfrogFlow U ε (n + 1) (x, p)).2)
              = fun p => ((leapfrogFlow U ε n (x, p)).2 - (ε / 2) • gradient U ((leapfrogFlow U ε n (x, p)).1)) -
                  (ε / 2) • gradient U ((leapfrogFlow U ε n (x, p)).1 +
                    ε • ((leapfrogFlow U ε n (x, p)).2 - (ε / 2) • gradient U ((leapfrogFlow U ε n (x, p)).1))) := by
            funext p
            rw [hiter, Function.comp_apply]
            exact hstep2 _
          rw [e2]
          exact (ih2.sub (measurable_const.smul (hgrad_meas.comp ih1))).sub
            (measurable_const.smul (hgrad_meas.comp
              (ih1.add (measurable_const.smul (ih2.sub (measurable_const.smul (hgrad_meas.comp ih1)))))))
  have core : ∀ η₀ : ℝ, 0 < η₀ → η₀ < 1 → ∃ δ : ℝ, 0 < δ ∧ ∀ x : HMCState d,
      ENNReal.ofReal (1 - η₀) <
        ∫⁻ L : ℕ,
          Measure.map (fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2)
            ((gaussianMomentum d).prod (volume.restrict (Set.Icc (0 : ℝ) 1)))
            {y : HMCState d | ‖y - x‖ < δ}
        ∂Ldist := by
    intro η₀ hη₀ hη₁
    haveI hμG : IsProbabilityMeasure (gaussianMomentum d) := by
      first
        | exact inferInstance
        | rw [gaussianMomentum]
          exact MeasureTheory.Measure.isProbabilityMeasure_map
            ((EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.measurable.aemeasurable)
    have hdisp : ∀ (L : ℕ) (x p : HMCState d),
        ‖(leapfrogFlow U ε L (x, p)).1 - x‖ ≤
          2 * G * ε ^ 2 * (L : ℝ) ^ 2 + 2 * (L : ℝ) * ε * ‖p‖ := by
      intro L x p
      rcases Nat.eq_zero_or_pos L with h0 | hL
      · subst h0
        rw [(statopia_math_node_2434035012_bf892b59 d U hU_diff ε x p).2.2.2.2]
        simp
      · have hformula := (statopia_math_node_2434035012_bf892b59 d U hU_diff ε x p).2.2.2.1 L hL
        let S : HMCState d := ∑ i ∈ Finset.Icc 1 (L - 1),
          ((L : ℝ) - (i : ℝ)) • gradient U ((leapfrogFlow U ε i (x, p)).1)
        have hx : (leapfrogFlow U ε L (x, p)).1 - x
            = -(((L : ℝ) * ε ^ 2 / 2) • gradient U x)
              - ε ^ 2 • (∑ i ∈ Finset.Icc 1 (L - 1),
                  ((L : ℝ) - (i : ℝ)) • gradient U ((leapfrogFlow U ε i (x, p)).1))
              + ((L : ℝ) * ε) • p := by
          rw [hformula]
          abel
        have hSbound : ‖S‖ ≤ (L : ℝ) * ((L : ℝ) * G) := by
          change ‖(∑ i ∈ Finset.Icc 1 (L - 1),
            ((L : ℝ) - (i : ℝ)) • gradient U ((leapfrogFlow U ε i (x, p)).1))‖ ≤
              (L : ℝ) * ((L : ℝ) * G)
          calc ‖(∑ i ∈ Finset.Icc 1 (L - 1),
                ((L : ℝ) - (i : ℝ)) • gradient U ((leapfrogFlow U ε i (x, p)).1))‖
              ≤ ∑ i ∈ Finset.Icc 1 (L - 1),
                  ‖((L : ℝ) - (i : ℝ)) • gradient U ((leapfrogFlow U ε i (x, p)).1)‖ :=
                norm_sum_le _ _
            _ ≤ ∑ i ∈ Finset.Icc 1 (L - 1), (L : ℝ) * G := by
                apply Finset.sum_le_sum
                intro i hi
                have hi2 : i ≤ L - 1 := (Finset.mem_Icc.mp hi).2
                have hiL : (i : ℝ) ≤ (L : ℝ) := by
                  have h1 : i ≤ L := by omega
                  exact_mod_cast h1
                have hci : (0 : ℝ) ≤ (L : ℝ) - (i : ℝ) := by linarith
                calc ‖((L : ℝ) - (i : ℝ)) • gradient U ((leapfrogFlow U ε i (x, p)).1)‖
                    = ((L : ℝ) - (i : ℝ)) * ‖gradient U ((leapfrogFlow U ε i (x, p)).1)‖ := by
                      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hci]
                  _ ≤ ((L : ℝ) - (i : ℝ)) * G := mul_le_mul_of_nonneg_left (hG_bound _) hci
                  _ ≤ (L : ℝ) * G := by
                      have hle : (L : ℝ) - (i : ℝ) ≤ (L : ℝ) := by linarith
                      exact mul_le_mul_of_nonneg_right hle hG_nonneg
            _ = ((Finset.Icc 1 (L - 1)).card : ℝ) * ((L : ℝ) * G) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (L : ℝ) * ((L : ℝ) * G) := by
                have hcard : ((Finset.Icc 1 (L - 1)).card : ℝ) ≤ (L : ℝ) := by
                  have h1 : (Finset.Icc 1 (L - 1)).card ≤ L := by
                    have hsub : Finset.Icc 1 (L - 1) ⊆ Finset.range L := by
                      intro i hi
                      simp only [Finset.mem_range]
                      have hi2 : i ≤ L - 1 := (Finset.mem_Icc.mp hi).2
                      omega
                    calc (Finset.Icc 1 (L - 1)).card ≤ (Finset.range L).card :=
                          Finset.card_le_card hsub
                      _ = L := Finset.card_range L
                  exact_mod_cast h1
                exact mul_le_mul_of_nonneg_right hcard (mul_nonneg (Nat.cast_nonneg L) hG_nonneg)
        have hcoef : (0 : ℝ) ≤ (L : ℝ) * ε ^ 2 / 2 := by
          have h1 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
          have h2 : (0 : ℝ) ≤ ε ^ 2 := sq_nonneg ε
          nlinarith
        have hn1 : ‖((L : ℝ) * ε ^ 2 / 2) • gradient U x‖ ≤ (L : ℝ) * ε ^ 2 / 2 * G := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoef]
          exact mul_le_mul_of_nonneg_left (hG_bound x) hcoef
        have hn3 : ‖((L : ℝ) * ε) • p‖ = (L : ℝ) * ε * ‖p‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by
            have h1 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
            have h2 : (0 : ℝ) ≤ ε := le_of_lt hε
            exact mul_nonneg h1 h2)]
        have hB : ‖ε ^ 2 • S‖ = ε ^ 2 * ‖S‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ε)]
        calc ‖(leapfrogFlow U ε L (x, p)).1 - x‖
            = ‖-(((L : ℝ) * ε ^ 2 / 2) • gradient U x) - ε ^ 2 • S + ((L : ℝ) * ε) • p‖ := by
                rw [hx]
          _ ≤ ‖-(((L : ℝ) * ε ^ 2 / 2) • gradient U x) - ε ^ 2 • S‖ + ‖((L : ℝ) * ε) • p‖ :=
              norm_add_le _ _
          _ ≤ (‖((L : ℝ) * ε ^ 2 / 2) • gradient U x‖ + ‖ε ^ 2 • S‖) +
                ‖((L : ℝ) * ε) • p‖ := by
              have h := norm_sub_le (-(((L : ℝ) * ε ^ 2 / 2) • gradient U x)) (ε ^ 2 • S)
              rw [norm_neg] at h
              linarith
          _ ≤ ((L : ℝ) * ε ^ 2 / 2 * G + ε ^ 2 * ((L : ℝ) * ((L : ℝ) * G))) +
                (L : ℝ) * ε * ‖p‖ := by
              rw [hB, hn3]
              have h5 : ε ^ 2 * ‖S‖ ≤ ε ^ 2 * ((L : ℝ) * ((L : ℝ) * G)) :=
                mul_le_mul_of_nonneg_left hSbound (sq_nonneg ε)
              linarith [hn1, h5]
          _ ≤ 2 * G * ε ^ 2 * (L : ℝ) ^ 2 + 2 * (L : ℝ) * ε * ‖p‖ := by
              have hLc : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
              have hLnn : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
              have hε2 : (0 : ℝ) ≤ ε ^ 2 := sq_nonneg ε
              have hLsq : (L : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
              have hpnn : (0 : ℝ) ≤ ‖p‖ := norm_nonneg p
              have hA : (L : ℝ) * ε ^ 2 / 2 * G ≤ G * ε ^ 2 * (L : ℝ) ^ 2 := by
                have hnn : (0 : ℝ) ≤ G * ε ^ 2 := mul_nonneg hG_nonneg hε2
                have h1 : G * ε ^ 2 * (L : ℝ) ≤ G * ε ^ 2 * (L : ℝ) ^ 2 :=
                  mul_le_mul_of_nonneg_left hLsq hnn
                have h2 : (0 : ℝ) ≤ G * ε ^ 2 * (L : ℝ) := mul_nonneg hnn hLnn
                nlinarith [h1, h2]
              have hB2 : ε ^ 2 * ((L : ℝ) * ((L : ℝ) * G)) = G * ε ^ 2 * (L : ℝ) ^ 2 := by ring
              have hC : (0 : ℝ) ≤ (L : ℝ) * ε * ‖p‖ :=
                mul_nonneg (mul_nonneg hLnn (le_of_lt hε)) hpnn
              nlinarith [hA, hB2, hC, hLnn, hε2, hG_nonneg, hpnn]
    have hlt1 : ENNReal.ofReal (1 - η₀ / 2) < 1 := by
      rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)]
      linarith
    have key : ∀ (α : Type) [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
        (s : ℕ → Set α), Monotone s → (⋃ n, s n) = Set.univ →
        ∀ c : ENNReal, c < 1 → ∃ n, c < μ (s n) := by
      intro α _ μ hprob s hmono hunion c hc
      haveI := hprob
      by_contra hcon
      push_neg at hcon
      have hsup : (⨆ n, μ (s n)) = 1 := by
        rw [← Monotone.measure_iUnion hmono, hunion, measure_univ]
      have h1 : (⨆ n, μ (s n)) ≤ c := iSup_le hcon
      rw [hsup] at h1
      exact absurd h1 (not_le.mpr hc)
    obtain ⟨N, hN⟩ : ∃ N : ℕ,
        ENNReal.ofReal (1 - η₀ / 2) < Ldist ((Finset.range N : Finset ℕ) : Set ℕ) := by
      have hmono : Monotone fun n : ℕ => ((Finset.range n : Finset ℕ) : Set ℕ) := by
        intro a b hab p hp
        have hp' : p ∈ Finset.range a := hp
        have h2 : p ∈ Finset.range b := by
          simp only [Finset.mem_range] at hp' ⊢
          omega
        exact h2
      have hunion : (⋃ n : ℕ, ((Finset.range n : Finset ℕ) : Set ℕ)) = Set.univ := by
        ext m
        simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
        exact ⟨m + 1, by simp⟩
      exact key ℕ Ldist (fun n : ℕ => ((Finset.range n : Finset ℕ) : Set ℕ))
        hmono hunion (ENNReal.ofReal (1 - η₀ / 2)) hlt1
    obtain ⟨t, ht_nonneg, ht_lower⟩ : ∃ t : ℝ, 0 ≤ t ∧
        ENNReal.ofReal (1 - η₀ / 2) ≤ (gaussianMomentum d) {p : HMCState d | ‖p‖ ≤ t} := by
      have hmono : Monotone fun n : ℕ => {p : HMCState d | ‖p‖ ≤ (n : ℝ)} := by
        intro a b hab p hp
        simp only [Set.mem_setOf_eq] at hp ⊢
        exact le_trans hp (Nat.cast_le.mpr hab)
      have hunion : (⋃ n : ℕ, {p : HMCState d | ‖p‖ ≤ (n : ℝ)}) = Set.univ := by
        ext p
        simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact exists_nat_ge ‖p‖
      obtain ⟨n, hn⟩ := key (HMCState d) (gaussianMomentum d)
        (fun n : ℕ => {p : HMCState d | ‖p‖ ≤ (n : ℝ)}) hmono hunion
        (ENNReal.ofReal (1 - η₀ / 2)) hlt1
      exact ⟨(n : ℝ), Nat.cast_nonneg n, hn.le⟩
    set M : ℝ := ∑ L ∈ Finset.range N,
      (2 * G * ε ^ 2 * (L : ℝ) ^ 2 + 2 * (L : ℝ) * ε * t) with hMdef
    have hM_nonneg : 0 ≤ M := by
      rw [hMdef]
      refine Finset.sum_nonneg (fun L hL => ?_)
      have h1 : (0 : ℝ) ≤ 2 * G * ε ^ 2 * (L : ℝ) ^ 2 := by
        have a : (0 : ℝ) ≤ G * ε ^ 2 := mul_nonneg hG_nonneg (sq_nonneg ε)
        have b : (0 : ℝ) ≤ (L : ℝ) ^ 2 := sq_nonneg (L : ℝ)
        nlinarith [mul_nonneg a b]
      have h2 : (0 : ℝ) ≤ 2 * (L : ℝ) * ε * t := by
        have a : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
        have b : (0 : ℝ) ≤ ε := le_of_lt hε
        nlinarith [mul_nonneg (mul_nonneg a b) ht_nonneg]
      linarith
    refine ⟨1 + M, by linarith, ?_⟩
    intro x
    have hBmeas : MeasurableSet {y : HMCState d | ‖y - x‖ < 1 + M} := by
      have hcont : Continuous fun y : HMCState d => ‖y - x‖ :=
        (continuous_id.sub continuous_const).norm
      exact (isOpen_lt hcont continuous_const).measurableSet
    have hxB : x ∈ {y : HMCState d | ‖y - x‖ < 1 + M} := by
      simp only [Set.mem_setOf_eq, sub_self, norm_zero]
      linarith
    have hterm : ∀ L : ℕ, L ∈ ((Finset.range N : Finset ℕ) : Set ℕ) →
        ENNReal.ofReal (1 - η₀ / 2) ≤
          (Measure.map (fun p : HMCState d => (leapfrogFlow U ε L (x, p)).1) (gaussianMomentum d))
            {y : HMCState d | ‖y - x‖ < 1 + M} := by
      intro L hL
      have hflowpos : Measurable fun p : HMCState d => (leapfrogFlow U ε L (x, p)).1 :=
        (hflow_meas L x).1
      rw [MeasureTheory.Measure.map_apply hflowpos hBmeas]
      have hsub : {p : HMCState d | ‖p‖ ≤ t} ⊆
          (fun p : HMCState d => (leapfrogFlow U ε L (x, p)).1) ⁻¹'
            {y : HMCState d | ‖y - x‖ < 1 + M} := by
        intro p hp
        have hp' : ‖p‖ ≤ t := hp
        simp only [Set.mem_setOf_eq, Set.mem_preimage]
        have h1 := hdisp L x p
        have h3 : 2 * (L : ℝ) * ε * ‖p‖ ≤ 2 * (L : ℝ) * ε * t := by
          have hnn : (0 : ℝ) ≤ 2 * (L : ℝ) * ε := by
            have hLnn : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
            have hεnn : (0 : ℝ) ≤ ε := le_of_lt hε
            nlinarith
          exact mul_le_mul_of_nonneg_left hp' hnn
        have h4 : 2 * G * ε ^ 2 * (L : ℝ) ^ 2 + 2 * (L : ℝ) * ε * t ≤ M := by
          rw [hMdef]
          refine Finset.single_le_sum (f := fun i : ℕ =>
            2 * G * ε ^ 2 * (i : ℝ) ^ 2 + 2 * (i : ℝ) * ε * t) ?_ ?_
          · intro i hi
            have a : (0 : ℝ) ≤ G * ε ^ 2 := mul_nonneg hG_nonneg (sq_nonneg ε)
            have b : (0 : ℝ) ≤ (i : ℝ) ^ 2 := sq_nonneg (i : ℝ)
            have c : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
            have dd : (0 : ℝ) ≤ ε := le_of_lt hε
            nlinarith [mul_nonneg a b, mul_nonneg (mul_nonneg c dd) ht_nonneg]
          · exact hL
        linarith
      calc ENNReal.ofReal (1 - η₀ / 2)
          ≤ (gaussianMomentum d) {p : HMCState d | ‖p‖ ≤ t} := ht_lower
        _ ≤ (gaussianMomentum d) ((fun p : HMCState d => (leapfrogFlow U ε L (x, p)).1) ⁻¹'
              {y : HMCState d | ‖y - x‖ < 1 + M}) := MeasureTheory.measure_mono hsub
    have hPQ : ∀ L : ℕ,
        (Measure.map (fun p : HMCState d => (leapfrogFlow U ε L (x, p)).1) (gaussianMomentum d))
            {y : HMCState d | ‖y - x‖ < 1 + M} ≤
          (Measure.map (fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2)
            ((gaussianMomentum d).prod (volume.restrict (Set.Icc (0 : ℝ) 1))))
            {y : HMCState d | ‖y - x‖ < 1 + M} := by
      intro L
      exact (statopia_math_node_1760066137_9d09a34f d hd U hU_diff hgrad_meas ε hε L).2.2.2.1 x
        {y : HMCState d | ‖y - x‖ < 1 + M} hBmeas hxB
    have hInd : ∫⁻ L : ℕ,
        ((((Finset.range N : Finset ℕ) : Set ℕ)).indicator
          (fun _ : ℕ => ENNReal.ofReal (1 - η₀ / 2)) L) ∂Ldist
        = ENNReal.ofReal (1 - η₀ / 2) * Ldist (((Finset.range N : Finset ℕ) : Set ℕ)) := by
      exact MeasureTheory.lintegral_indicator_const
        (Set.Finite.measurableSet (Finset.finite_toSet (Finset.range N))) _
    have hcc : ENNReal.ofReal (1 - η₀ / 2) * ENNReal.ofReal (1 - η₀ / 2)
        = ENNReal.ofReal ((1 - η₀ / 2) * (1 - η₀ / 2)) := by
      rw [ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ 1 - η₀ / 2)]
    have hlt : ENNReal.ofReal (1 - η₀) <
        ENNReal.ofReal (1 - η₀ / 2) * ENNReal.ofReal (1 - η₀ / 2) := by
      rw [hcc, ENNReal.ofReal_lt_ofReal_iff (show (0 : ℝ) < (1 - η₀ / 2) * (1 - η₀ / 2) by
        have hpos : (0 : ℝ) < 1 - η₀ / 2 := by linarith
        exact mul_pos hpos hpos)]
      nlinarith
    calc ENNReal.ofReal (1 - η₀)
        < ENNReal.ofReal (1 - η₀ / 2) * ENNReal.ofReal (1 - η₀ / 2) := hlt
      _ ≤ ENNReal.ofReal (1 - η₀ / 2) * Ldist (((Finset.range N : Finset ℕ) : Set ℕ)) :=
          mul_le_mul_left' hN.le _
      _ = ∫⁻ L : ℕ,
            ((((Finset.range N : Finset ℕ) : Set ℕ)).indicator
              (fun _ : ℕ => ENNReal.ofReal (1 - η₀ / 2)) L) ∂Ldist := hInd.symm
      _ ≤ ∫⁻ L : ℕ,
            (Measure.map (fun p : HMCState d => (leapfrogFlow U ε L (x, p)).1)
              (gaussianMomentum d)) {y : HMCState d | ‖y - x‖ < 1 + M} ∂Ldist := by
          have hmono : ∀ L : ℕ,
              ((((Finset.range N : Finset ℕ) : Set ℕ)).indicator
                (fun _ : ℕ => ENNReal.ofReal (1 - η₀ / 2)) L) ≤
              (Measure.map (fun p : HMCState d => (leapfrogFlow U ε L (x, p)).1)
                (gaussianMomentum d)) {y : HMCState d | ‖y - x‖ < 1 + M} := by
            intro L
            by_cases hL : L ∈ ((Finset.range N : Finset ℕ) : Set ℕ)
            · rw [Set.indicator_of_mem hL]
              exact hterm L hL
            · rw [Set.indicator_of_notMem hL]
              exact zero_le _
          exact MeasureTheory.lintegral_mono hmono
      _ ≤ ∫⁻ L : ℕ,
            (Measure.map (fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2)
              ((gaussianMomentum d).prod (volume.restrict (Set.Icc (0 : ℝ) 1))))
              {y : HMCState d | ‖y - x‖ < 1 + M} ∂Ldist :=
          MeasureTheory.lintegral_mono hPQ
  obtain ⟨δ, hδpos, hδ⟩ := core (min (η / 2) (1 / 2))
    (lt_min (by linarith) (by norm_num))
    (by nlinarith [min_le_right (η / 2) (1 / 2), hη])
  refine ⟨δ, hδpos, fun x => lt_of_le_of_lt ?_ (hδ x)⟩
  exact ENNReal.ofReal_le_ofReal (by nlinarith [min_le_left (η / 2) (1 / 2), hη])
  /- @proof-region region.target-node.session.e6cae497bdc87d23 end -/

end Statlib.Imported

end

