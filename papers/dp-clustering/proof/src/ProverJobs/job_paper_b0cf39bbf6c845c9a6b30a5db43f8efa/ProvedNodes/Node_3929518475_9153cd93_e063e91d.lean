import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.Vocabulary
import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.Base
import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.ProvedNodes.Node_2862296761_3b0cbbcb_a48f58c1

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal MeasureTheory Topology BigOperators
open Statlib.Imported
open Statlib.Imported.DPMModel

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal MeasureTheory Topology BigOperators
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_3929518475_9153cd93 : ∀ {Θ X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Θ]
    (μ : Measure X)
    (k : Θ → X → ℝ) (hk_nonneg : ∀ (θ : Θ) (x : X), 0 ≤ k θ x)
    (hk_meas : Measurable (Function.uncurry k))
    (hk_int : ∀ (θ : Θ), ∫⁻ x : X, ENNReal.ofReal (k θ x) ∂μ = 1)
    (p0 : X → ℝ≥0∞) (hp0 : Measurable p0)
    (hp0_int : ∫⁻ x : X, p0 x ∂μ = 1)
    (P : ProbabilityMeasure X) (hP : P.toMeasure = μ.withDensity p0)
    (t : ℕ) (ht : 2 ≤ t)
    (n : ℕ) (hn : 0 < n)
    (r : ℕ) (hr : 1 ≤ r)
    (ψ : Fin r → X → ℝ) (hψ_cont : ∀ (j : Fin r), Continuous (ψ j))
    (M : ℝ) (hM_def : M = ⨆ j : Fin r, ⨆ x : X, |ψ j x|) (hM : 0 < M)
    (hψ_bound : ∀ (j : Fin r) (x : X), |ψ j x| ≤ M)
    (ε : ℝ) (hε : 0 < ε)
    (c : ℝ) (hc : c = ε ^ 2 / (8 * M ^ 2))
    (hsep : ∀ (s : ℕ), 1 ≤ s → s < t → ∀ Q : ProbabilityMeasure X,
      Q ∈ Gset μ k s →
        ¬ (∀ (j : Fin r),
          |∫ x : X, ψ j x ∂Q.toMeasure - ∫ x : X, ψ j x ∂P.toMeasure| < ε))
    (Lam : Measure (ProbabilityMeasure Θ × (ℕ → Θ))) [IsProbabilityMeasure Lam]
    (A : Set (ProbabilityMeasure Θ × (ℕ → Θ))) (hA : MeasurableSet A)
    (hA_few_clusters : ∀ᵐ ξ ∂Lam, ξ ∈ A → (Set.range (fun i : Fin n => ξ.2 (i : ℕ))).ncard < t),
    ∫⁻ x : Fin n → X,
        (if (⨆ j : Fin r,
              |(n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x' : X, ψ j x' ∂P.toMeasure|
                < ε / 2)
          then ∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
            A.indicator
              (fun ξ => ∏ i : Fin n,
                (ENNReal.ofReal (k (ξ.2 (i : ℕ)) (x i)) * (p0 (x i))⁻¹))
              ξ ∂Lam
          else 0)
        ∂(Measure.pi (fun _ : Fin n => P.toMeasure))
      ≤ ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * c)) * Lam A := by
  /- @proof-region region.target-node.session.6a7e9cb70e72f313 begin -/
  intro Θ X _ _ _ _ μ k hk_nonneg hk_meas hk_int p0 hp0_meas hp0_int P hP t ht n hn r hr
    psi hpsi_cont M hM_def hM hpsi_bd eps heps c hc hsep Lam hLam A hA hAcard
  classical
  haveI hLamI : IsProbabilityMeasure Lam := hLam
  haveI hPfin : IsFiniteMeasure P.toMeasure := by
    refine ⟨?_⟩
    rw [hP, MeasureTheory.withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hp0_int]
    simp
  have ind_mem : ∀ (f : ProbabilityMeasure Θ × (ℕ → Θ) → ℝ≥0∞)
      (ξ : ProbabilityMeasure Θ × (ℕ → Θ)), ξ ∈ A → A.indicator f ξ = f ξ := by
    intro f ξ h
    simp only [Set.indicator]
    rw [if_pos h]
  have ind_not : ∀ (f : ProbabilityMeasure Θ × (ℕ → Θ) → ℝ≥0∞)
      (ξ : ProbabilityMeasure Θ × (ℕ → Θ)), ξ ∉ A → A.indicator f ξ = 0 := by
    intro f ξ h
    simp only [Set.indicator]
    rw [if_neg h]
  set S : Set (Fin n → X) :=
    {x | (⨆ j : Fin r,
      |(n : ℝ)⁻¹ * (∑ i : Fin n, psi j (x i)) - ∫ y, psi j y ∂(P.toMeasure)| < eps / 2)} with hS
  set H : (Fin n → X) → (ProbabilityMeasure Θ × (ℕ → Θ)) → ℝ≥0∞ :=
    (fun x ξ => if x ∈ S then
      (if ξ ∈ A then ∏ i : Fin n, (ENNReal.ofReal (k (ξ.2 i) (x i)) * (p0 (x i))⁻¹) else 0)
      else 0) with hH
  have hHunfold : ∀ (x : Fin n → X) (ξ : ProbabilityMeasure Θ × (ℕ → Θ)),
      H x ξ = if x ∈ S then
        (if ξ ∈ A then ∏ i : Fin n, (ENNReal.ofReal (k (ξ.2 i) (x i)) * (p0 (x i))⁻¹) else 0)
        else 0 := fun x ξ => rfl
  have hSin : ∀ x : Fin n → X, (x ∈ S) ↔
      (⨆ j : Fin r,
        |(n : ℝ)⁻¹ * (∑ i : Fin n, psi j (x i)) - ∫ y, psi j y ∂(P.toMeasure)| < eps / 2) := by
    intro x
    rw [hS]
    simp
  have hmeas_j : ∀ j : Fin r, MeasurableSet {x : Fin n → X |
      |(n : ℝ)⁻¹ * (∑ i : Fin n, psi j (x i)) - ∫ y, psi j y ∂(P.toMeasure)| < eps / 2} := by
    intro j
    have hsum : Measurable (fun x : Fin n → X => ∑ i : Fin n, psi j (x i)) :=
      Finset.measurable_sum _ (fun i _ => (hpsi_cont j).measurable.comp (measurable_pi_apply i))
    have hmul : Measurable (fun x : Fin n → X => (n : ℝ)⁻¹ * (∑ i : Fin n, psi j (x i))) :=
      (measurable_const : Measurable fun _ : Fin n → X => (n : ℝ)⁻¹).mul hsum
    have hsub : Measurable (fun x : Fin n → X =>
        (n : ℝ)⁻¹ * (∑ i : Fin n, psi j (x i)) - ∫ y, psi j y ∂(P.toMeasure)) :=
      hmul.sub (measurable_const : Measurable fun _ : Fin n → X => (∫ y, psi j y ∂(P.toMeasure)))
    exact measurableSet_preimage hsub.abs measurableSet_Iio
  have hsup_iff : ∀ x : Fin n → X,
      ((⨆ j : Fin r,
          |(n : ℝ)⁻¹ * (∑ i : Fin n, psi j (x i)) - ∫ y, psi j y ∂(P.toMeasure)|) < eps / 2)
        ↔ (∀ j : Fin r,
          |(n : ℝ)⁻¹ * (∑ i : Fin n, psi j (x i)) - ∫ y, psi j y ∂(P.toMeasure)| < eps / 2) := by
    haveI : Nonempty (Fin r) := ⟨⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hr⟩⟩
    intro x
    constructor
    · intro h j
      exact lt_of_le_of_lt
        (le_ciSup (Finite.bddAbove_range (fun j : Fin r =>
          |(n : ℝ)⁻¹ * (∑ i : Fin n, psi j (x i)) - ∫ y, psi j y ∂(P.toMeasure)|)) j) h
    · intro h
      have hne : (Finset.univ : Finset (Fin r)).Nonempty :=
        ⟨⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hr⟩, Finset.mem_univ _⟩
      have hlt : (Finset.univ : Finset (Fin r)).sup' hne (fun j : Fin r =>
          |(n : ℝ)⁻¹ * (∑ i : Fin n, psi j (x i)) - ∫ y, psi j y ∂(P.toMeasure)|) < eps / 2 := by
        rw [Finset.sup'_lt_iff hne]
        intro i _
        exact h i
      have h0 : (0 : ℝ) ≤ (Finset.univ : Finset (Fin r)).sup' hne (fun j : Fin r =>
          |(n : ℝ)⁻¹ * (∑ i : Fin n, psi j (x i)) - ∫ y, psi j y ∂(P.toMeasure)|) := by
        rw [Finset.le_sup'_iff hne]
        exact ⟨⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hr⟩, Finset.mem_univ _, abs_nonneg _⟩
      exact lt_of_le_of_lt
        (Real.iSup_le (fun j => Finset.le_sup' (fun j : Fin r =>
          |(n : ℝ)⁻¹ * (∑ i : Fin n, psi j (x i)) - ∫ y, psi j y ∂(P.toMeasure)|)
          (Finset.mem_univ j)) h0) hlt
  have hφS : MeasurableSet S := by
    have hset : S = ⋂ j : Fin r, {x : Fin n → X |
        |(n : ℝ)⁻¹ * (∑ i : Fin n, psi j (x i)) - ∫ y, psi j y ∂(P.toMeasure)| < eps / 2} := by
      rw [hS]
      ext x
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      exact hsup_iff x
    rw [hset]
    exact MeasurableSet.iInter hmeas_j
  have hHmeas : Measurable (Function.uncurry H) := by
    show Measurable (fun p : (Fin n → X) × (ProbabilityMeasure Θ × (ℕ → Θ)) =>
      if p.1 ∈ S then
        (if p.2 ∈ A then ∏ i : Fin n, (ENNReal.ofReal (k (p.2.2 i) (p.1 i)) * (p0 (p.1 i))⁻¹) else 0)
        else 0)
    have hG : Measurable (fun p : (Fin n → X) × (ProbabilityMeasure Θ × (ℕ → Θ)) =>
        ∏ i : Fin n, (ENNReal.ofReal (k (p.2.2 i) (p.1 i)) * (p0 (p.1 i))⁻¹)) := by
      refine Finset.measurable_prod (Finset.univ : Finset (Fin n)) ?_
      intro i _
      have h1 : Measurable (fun f : ℕ → Θ => f (↑i)) :=
        measurable_pi_apply (δ := ℕ) (X := fun _ : ℕ => Θ) (a := (↑i))
      have h2 : Measurable (fun p : (Fin n → X) × (ProbabilityMeasure Θ × (ℕ → Θ)) => p.2.2) :=
        measurable_snd.comp measurable_snd
      have h4 : Measurable (fun f : Fin n → X => f i) := measurable_pi_apply i
      have h3 : Measurable (fun p : (Fin n → X) × (ProbabilityMeasure Θ × (ℕ → Θ)) => p.1 i) :=
        h4.comp measurable_fst
      have hpair : Measurable (fun p : (Fin n → X) × (ProbabilityMeasure Θ × (ℕ → Θ)) =>
          (p.2.2 (↑i), p.1 i)) :=
        (h1.comp h2).prodMk h3
      have hki : Measurable (fun p : (Fin n → X) × (ProbabilityMeasure Θ × (ℕ → Θ)) =>
          k (p.2.2 i) (p.1 i)) :=
        hk_meas.comp hpair
      have hp0i : Measurable (fun p : (Fin n → X) × (ProbabilityMeasure Θ × (ℕ → Θ)) =>
          (p0 (p.1 i))⁻¹) :=
        (hp0_meas.comp ((measurable_pi_apply i).comp measurable_fst)).inv
      exact (ENNReal.measurable_ofReal.comp hki).mul hp0i
    exact Measurable.ite (measurableSet_preimage measurable_fst hφS)
      (Measurable.ite (measurableSet_preimage measurable_snd hA) hG measurable_const) measurable_const
  have hstep1 :
      ∫⁻ x : Fin n → X,
        (if (⨆ j : Fin r,
              |(n : ℝ)⁻¹ * (∑ i : Fin n, psi j (x i)) - ∫ y, psi j y ∂(P.toMeasure)| < eps / 2)
          then ∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
             (Set.indicator A
                (fun y : ProbabilityMeasure Θ × (ℕ → Θ) =>
                  ∏ i : Fin n, (ENNReal.ofReal (k (y.2 i) (x i)) * (p0 (x i))⁻¹)) ξ) ∂Lam
          else 0)
        ∂(Measure.pi (fun _ : Fin n => P.toMeasure))
      = ∫⁻ x : Fin n → X,
          (∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ), H x ξ ∂Lam) ∂(Measure.pi (fun _ : Fin n => P.toMeasure)) := by
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ S
    · rw [if_pos ((hSin x).mp hx)]
      refine lintegral_congr fun ξ => ?_
      rw [hHunfold]
      by_cases hξA : ξ ∈ A
      · rw [ind_mem _ _ hξA, if_pos hx, if_pos hξA]
      · rw [ind_not _ _ hξA, if_pos hx, if_neg hξA]
    · rw [if_neg (fun h => hx ((hSin x).mpr h))]
      have hzero : (fun ξ : ProbabilityMeasure Θ × (ℕ → Θ) => H x ξ) = fun _ => 0 := by
        funext ξ
        rw [hHunfold, if_neg hx]
      have hz : ∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ), H x ξ ∂Lam = 0 := by
        rw [hzero]
        simp
      exact hz.symm
  have hstep2 :
      ∫⁻ x : Fin n → X,
          (∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ), H x ξ ∂Lam) ∂(Measure.pi (fun _ : Fin n => P.toMeasure))
      = ∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
          (∫⁻ x : Fin n → X, H x ξ ∂(Measure.pi (fun _ : Fin n => P.toMeasure))) ∂Lam := by
    exact MeasureTheory.lintegral_lintegral_swap hHmeas.aemeasurable
  have hstep3 :
      ∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
          (∫⁻ x : Fin n → X, H x ξ ∂(Measure.pi (fun _ : Fin n => P.toMeasure))) ∂Lam
      ≤ ∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
          Set.indicator A
            (fun _ => ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * c))) ξ ∂Lam := by
    refine lintegral_mono_ae ?_
    filter_upwards [hAcard] with ξ hξ
    by_cases hAξ : ξ ∈ A
    · rw [ind_mem _ _ hAξ]
      refine le_trans (le_of_eq ?_)
        (statopia_math_node_2862296761_3b0cbbcb μ k hk_nonneg hk_meas hk_int p0 hp0_meas hp0_int
          P hP t ht n hn r hr psi hpsi_cont M hM_def hM hpsi_bd eps heps c hc hsep
          (fun i : Fin n => ξ.2 i) (hξ hAξ))
      refine lintegral_congr fun x => ?_
      rw [hHunfold]
      by_cases hx : x ∈ S
      · have hx' : (⨆ j : Fin r,
            |(n : ℝ)⁻¹ * (∑ i : Fin n, psi j (x i)) - ∫ y, psi j y ∂(P.toMeasure)| < eps / 2) :=
          (hSin x).mp hx
        rw [if_pos hx, if_pos hAξ, if_pos hx']
      · have hx' : ¬ (⨆ j : Fin r,
            |(n : ℝ)⁻¹ * (∑ i : Fin n, psi j (x i)) - ∫ y, psi j y ∂(P.toMeasure)| < eps / 2) :=
          fun h => hx ((hSin x).mpr h)
        rw [if_neg hx, if_neg hx']
    · rw [ind_not _ _ hAξ]
      have hzero : (fun x : Fin n → X => H x ξ) = fun _ => 0 := by
        funext x
        rw [hHunfold]
        by_cases hx : x ∈ S
        · rw [if_pos hx, if_neg hAξ]
        · rw [if_neg hx]
      have hz : ∫⁻ x : Fin n → X, H x ξ ∂(Measure.pi (fun _ : Fin n => P.toMeasure)) = 0 := by
        rw [hzero]
        simp
      exact le_of_eq hz
  calc ∫⁻ x : Fin n → X,
        (if (⨆ j : Fin r,
              |(n : ℝ)⁻¹ * (∑ i : Fin n, psi j (x i)) - ∫ y, psi j y ∂(P.toMeasure)| < eps / 2)
          then ∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
             (Set.indicator A
                (fun y : ProbabilityMeasure Θ × (ℕ → Θ) =>
                  ∏ i : Fin n, (ENNReal.ofReal (k (y.2 i) (x i)) * (p0 (x i))⁻¹)) ξ) ∂Lam
          else 0)
        ∂(Measure.pi (fun _ : Fin n => P.toMeasure))
      = ∫⁻ x : Fin n → X,
          (∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ), H x ξ ∂Lam) ∂(Measure.pi (fun _ : Fin n => P.toMeasure)) := hstep1
    _ = ∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
          (∫⁻ x : Fin n → X, H x ξ ∂(Measure.pi (fun _ : Fin n => P.toMeasure))) ∂Lam := hstep2
    _ ≤ ∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
          Set.indicator A
            (fun _ => ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * c))) ξ ∂Lam := hstep3
    _ = ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * c)) * Lam A :=
        MeasureTheory.lintegral_indicator_const hA _
  /- @proof-region region.target-node.session.6a7e9cb70e72f313 end -/

end Statlib.Imported
