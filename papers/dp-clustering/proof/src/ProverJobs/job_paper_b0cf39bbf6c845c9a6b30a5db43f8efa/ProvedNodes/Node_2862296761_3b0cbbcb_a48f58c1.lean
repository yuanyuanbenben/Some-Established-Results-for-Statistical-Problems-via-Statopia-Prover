import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.Vocabulary
import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.Base
import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.ProvedNodes.Node_1034431849_4a9cb240_d2e5b5a7
import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.ProvedNodes.Node_2781295325_3f1c8bad_bf8659af
import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.ProvedNodes.Node_3257560511_130c2ed0_568820cd



open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal MeasureTheory Topology BigOperators
open Statlib.Imported
open Statlib.Imported.DPMModel

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal MeasureTheory Topology BigOperators
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_2862296761_3b0cbbcb : ∀ {Θ X : Type*}
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
    (θ : Fin n → Θ) (hθ : (Set.range θ).ncard < t),
    ∫⁻ x : Fin n → X,
        (if (⨆ j : Fin r,
              |(n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x' : X, ψ j x' ∂P.toMeasure|
                < ε / 2)
          then ∏ i : Fin n, (ENNReal.ofReal (k (θ i) (x i)) * (p0 (x i))⁻¹)
          else 0)
        ∂(Measure.pi (fun _ : Fin n => P.toMeasure))
      ≤ ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * c)) := by
  /- @proof-region region.target-node.session.6b74fec3d08b8daf begin -/
  classical
  intro Θ X iΘ iX iXm iXB μ k hk_nonneg hk_meas hk_int p0 hp0_meas hp0_int P hP t ht n
    hn r hr psi hpsi_cont M hM_def hM hpsi_bound eps heps c hc hsep theta htheta
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

  have hdens : ∀ x : X, dpMixDensity k q ϑ x = (n : ℝ)⁻¹ * (∑ i : Fin n, k (theta i) x) := by
    intro x
    have h₁ : (∑ j : Fin t'.card, q j * k (ϑ j) x)
        = (n : ℝ)⁻¹ * (∑ j : Fin t'.card, (m j : ℝ) * k (ϑ j) x) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [hqdef]
      ring
    have h₂ : (∑ j : Fin t'.card, (m j : ℝ) * k (ϑ j) x) = ∑ i : Fin n, k (theta i) x :=
      (hfiber x).symm
    simp only [dpMixDensity]
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
    set g : X → ℝ≥0∞ := fun x => ENNReal.ofReal (dpMixDensity k q ϑ x) with hgdef
    have hterm_meas : ∀ j : Fin t'.card,
        Measurable (fun x : X => ENNReal.ofReal (q j * k (ϑ j) x)) := by
      intro j
      exact ((hk_meas.comp (measurable_prodMk_left (x := ϑ j))).const_mul (q j)).ennreal_ofReal
    have hpoint : ∀ x : X, g x = ∑ j : Fin t'.card, ENNReal.ofReal (q j * k (ϑ j) x) := by
      intro x
      simp only [hgdef, dpMixDensity]
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
    have hQmem : Q ∈ Gset μ k t'.card := by
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
    have hdp_meas : Measurable (fun y : X => dpMixDensity k q ϑ y) := by
      simp only [dpMixDensity]
      exact Finset.measurable_sum Finset.univ
        (fun j' _ => (hk_meas.comp (measurable_prodMk_left (x := ϑ j'))).const_mul (q j'))
    have hdp_nn : ∀ y : X, 0 ≤ dpMixDensity k q ϑ y := by
      intro y
      simp only [dpMixDensity]
      exact Finset.sum_nonneg
        (fun j' _ => mul_nonneg (le_of_lt (hqpos j')) (hk_nonneg (ϑ j') y))
    have hQint : ∫ y, psi j y ∂(↑Q) = ∫ y, dpMixDensity k q ϑ y * psi j y ∂μ := by
      show ∫ y, psi j y ∂(μ.withDensity g) = ∫ y, dpMixDensity k q ϑ y * psi j y ∂μ
      rw [integral_withDensity_eq_integral_toReal_smul hdp_meas.ennreal_ofReal
        (Filter.Eventually.of_forall (fun x => by simp)) (psi j)]
      have hcongr : (fun y : X => ENNReal.toReal (g y) • psi j y)
          = fun y : X => dpMixDensity k q ϑ y * psi j y := by
        funext y
        simp only [hgdef]
        rw [ENNReal.toReal_ofReal (hdp_nn y)]
        simp
      rw [hcongr]
    have hkey : (∫ y, psi j y ∂(↑Q)) = (n : ℝ)⁻¹ * ∑ i : Fin n, ∫ y, psi j y ∂(ν i) := by
      rw [hQint]
      have hcongr : (fun y : X => dpMixDensity k q ϑ y * psi j y)
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
  have hPprob : IsProbabilityMeasure (↑P : Measure X) := by
    rw [hP]
    exact ⟨by
      rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      exact hp0_int⟩
  haveI := hPprob
  have hdep := (statopia_math_node_2781295325_3f1c8bad (↑P) r hr psi hpsi_cont M hM hM_def
    hpsi_bound eps heps).2 n hn ν hνprob ⟨j, hj⟩
  have hfmeas : ∀ i : Fin n, Measurable (fun x : X => ENNReal.ofReal (k (theta i) x)) := by
    intro i
    exact (hk_meas.comp (measurable_prodMk_left (x := theta i))).ennreal_ofReal
  have hT : MeasurableSet {x : Fin n → X |
      ∀ j : Fin r,
        |(n : ℝ)⁻¹ * (∑ i : Fin n, psi j (x i)) - ∫ y, psi j y ∂(P.toMeasure)| < eps / 2} := by
    rw [Set.setOf_forall]
    refine MeasurableSet.iInter (fun j => ?_)
    have hgj : Measurable (fun x : Fin n → X =>
        (n : ℝ)⁻¹ * (∑ i : Fin n, psi j (x i)) - ∫ y, psi j y ∂(P.toMeasure)) := by
      have h1 : Measurable (fun x : Fin n → X => ∑ i : Fin n, psi j (x i)) := by
        simpa using Finset.measurable_sum (Finset.univ)
          (fun i _ => (hpsi_cont j).measurable.comp (measurable_pi_apply i))
      exact (h1.const_mul ((n : ℝ)⁻¹)).sub measurable_const
    simpa only [Set.mem_Iio] using hgj.abs measurableSet_Iio
  have hTset : {x : Fin n → X |
      ⨆ j : Fin r,
        |(n : ℝ)⁻¹ * (∑ i : Fin n, psi j (x i)) - ∫ y, psi j y ∂(P.toMeasure)| < eps / 2}
      = {x : Fin n → X |
        ∀ j : Fin r,
          |(n : ℝ)⁻¹ * (∑ i : Fin n, psi j (x i)) - ∫ y, psi j y ∂(P.toMeasure)| < eps / 2} := by
    ext x
    have hne : (Finset.univ : Finset (Fin r)).Nonempty :=
      ⟨⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hr⟩, Finset.mem_univ _⟩
    haveI : Nonempty (Fin r) := ⟨⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hr⟩⟩
    simp only [Set.mem_setOf_eq]
    rw [← Finset.sup'_univ_eq_ciSup]
    exact (Finset.sup'_lt_iff hne).trans (by simp)
  have hT' : MeasurableSet {x : Fin n → X |
      ⨆ j : Fin r,
        |(n : ℝ)⁻¹ * (∑ i : Fin n, psi j (x i)) - ∫ y, psi j y ∂(P.toMeasure)| < eps / 2} := by
    rw [hTset]
    exact hT
  have hcmp : (∫⁻ x : Fin n → X,
      (if (⨆ j : Fin r,
          |(n : ℝ)⁻¹ * (∑ i : Fin n, psi j (x i)) - ∫ y, psi j y ∂(P.toMeasure)| < eps / 2)
        then ∏ i : Fin n, (ENNReal.ofReal (k (theta i) (x i)) * (p0 (x i))⁻¹)
        else 0)
      ∂(Measure.pi (fun _ : Fin n => P.toMeasure)))
      ≤ Measure.pi ν
        {x : Fin n → X |
          ⨆ j : Fin r,
            |(n : ℝ)⁻¹ * (∑ i : Fin n, psi j (x i)) - ∫ y, psi j y ∂(P.toMeasure)| < eps / 2} := by
    have hchild := statopia_math_node_1034431849_4a9cb240 μ p0 hp0_meas hp0_int n
      (fun i : Fin n => fun x : X => ENNReal.ofReal (k (theta i) x)) hfmeas
      (fun i => hk_int (theta i))
      {x : Fin n → X |
        ⨆ j : Fin r,
          |(n : ℝ)⁻¹ * (∑ i : Fin n, psi j (x i)) - ∫ y, psi j y ∂(P.toMeasure)| < eps / 2} hT'
    have hmeasP : Measure.pi (fun _ : Fin n => P.toMeasure)
        = Measure.pi (fun _ : Fin n => μ.withDensity p0) := by rw [hP]
    rw [hmeasP]
    refine le_trans (le_of_eq ?_) hchild
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  rw [hc]
  exact le_trans hcmp hdep
  /- @proof-region region.target-node.session.6b74fec3d08b8daf end -/

end Statlib.Imported
