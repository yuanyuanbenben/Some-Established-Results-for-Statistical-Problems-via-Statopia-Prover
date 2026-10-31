import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.Vocabulary
import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.Base
import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.ProvedNodes.Node_2407238401_b71e9352_a1e6b0d4
import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.ProvedNodes.Node_3155168291_3ca337d1_81920601
import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.ProvedNodes.Node_341907188_a9df01ea_9a8ad78f
import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.ProvedNodes.Node_3862551001_c5ec6ec7_577b3ee3



open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal MeasureTheory Topology BigOperators
open Statlib.Imported
open Statlib.Imported.DPMModel

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal MeasureTheory Topology BigOperators
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_905517917_ae3c2032 : ∀ {X H : Type*} [MeasurableSpace X] [MeasurableSpace H]
    (μ : Measure X) [SigmaFinite μ]
    (p0 : X → ℝ≥0∞) (hp0 : Measurable p0) (hp0_int : ∫⁻ x, p0 x ∂μ = 1)
    (PiPrior : Measure H) [IsProbabilityMeasure PiPrior]
    (dens : H → X → ℝ≥0∞) (hdens : Measurable (Function.uncurry dens))
    (hdens_lt_top : ∀ h : H, ∀ᵐ x ∂μ, dens h x ≠ ⊤)
    (hdens_norm : ∀ᵐ h ∂PiPrior, ∫⁻ x, dens h x ∂μ ≤ 1)
    (hKL_pos : ∀ delta : ℝ, 0 < delta →
      0 < PiPrior {h : H |
        InformationTheory.klDiv (μ.withDensity p0) (μ.withDensity (dens h))
          < ENNReal.ofReal delta}),
    ∀ delta : ℝ, 0 < delta →
      ∀ᵐ x ∂(Measure.infinitePi (fun _ : ℕ => μ.withDensity p0)),
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          ENNReal.ofReal (Real.exp (-(n : ℝ) * delta)) ≤
            ∫⁻ h, ∏ i ∈ Finset.range n, (dens h (x i) * (p0 (x i))⁻¹) ∂PiPrior := by
  /- @proof-region region.target-node.session.2d97536fa28e7d13 begin -/
  intro X H _ _ μ _ p0 hp0_meas hp0_int PiPrior _ dens hdens_meas hdens_lt_top hdens_norm hKL δ hδ
  haveI hPprob : IsProbabilityMeasure (μ.withDensity p0) :=
    ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hp0_int]⟩
  have hP_ne_zero : ∀ᵐ x ∂(μ.withDensity p0), p0 x ≠ 0 := by
    have hmeas : MeasurableSet {x : X | p0 x = 0} := hp0_meas (measurableSet_singleton 0)
    have hzero : (μ.withDensity p0) {x : X | p0 x = 0} = 0 := by
      rw [withDensity_apply _ hmeas]
      have hzero_ae : p0 =ᵐ[μ.restrict {x : X | p0 x = 0}] 0 := by
        filter_upwards [ae_restrict_mem hmeas] with x hx
        simpa using hx
      rw [lintegral_congr_ae hzero_ae]
      simp
    rw [ae_iff]
    simpa using hzero
  have hP_lt_top : ∀ᵐ x ∂(μ.withDensity p0), p0 x < ⊤ := by
    have hfin : ∀ᵐ x ∂μ, p0 x < ⊤ :=
      ae_lt_top hp0_meas (by rw [hp0_int]; exact ENNReal.one_ne_top)
    exact hfin.filter_mono
      (Measure.AbsolutelyContinuous.ae_le (withDensity_absolutelyContinuous μ p0))

  set δ₁ : ℝ := δ / 2 with hδ₁def
  have hδ₁pos : 0 < δ₁ := by
    rw [hδ₁def]; linarith
  have hδ₁lt : δ₁ < δ := by
    rw [hδ₁def]; linarith
  have hPuniv : (μ.withDensity p0).real Set.univ = 1 := by
    rw [Measure.real_def]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hp0_int]
    simp
  set δ₀ : ℝ := min (δ₁ ^ 2 / 64) (δ₁ / 4) with hδ₀def
  have hδ₀pos : 0 < δ₀ := by
    rw [hδ₀def]
    exact lt_min (div_pos (pow_pos hδ₁pos 2) (by norm_num)) (by linarith)
  have hδ₀_le : δ₀ ≤ δ₁ ^ 2 / 64 := by
    rw [hδ₀def]
    exact min_le_left _ _
  have hδ₀_le' : δ₀ ≤ δ₁ / 4 := by
    rw [hδ₀def]
    exact min_le_right _ _
  have hsqrt₀ : Real.sqrt δ₀ ≤ δ₁ / 8 := by
    have h8 : (0 : ℝ) ≤ δ₁ / 8 := by linarith
    have hsq : δ₀ ≤ (δ₁ / 8) ^ 2 := by
      have hEq : (δ₁ / 8) ^ 2 = δ₁ ^ 2 / 64 := by ring
      rw [hEq]
      exact hδ₀_le
    calc Real.sqrt δ₀ ≤ Real.sqrt ((δ₁ / 8) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = δ₁ / 8 := Real.sqrt_sq h8
  have hδ₀bound : δ₀ + 2 * Real.sqrt δ₀ ≤ δ₁ := by
    nlinarith [hδ₀_le', hsqrt₀, Real.sqrt_nonneg δ₀]
  set Kset : Set H :=
    {h : H | InformationTheory.klDiv (μ.withDensity p0) (μ.withDensity (dens h))
      < ENNReal.ofReal δ₀} with hKdef
  have hKpos : 0 < PiPrior Kset := by
    rw [hKdef]
    exact hKL δ₀ hδ₀pos
  set b : ℝ≥0∞ := PiPrior Kset with hbdef
  have hb_ne_zero : b ≠ 0 := by
    rw [hbdef]; exact ne_of_gt hKpos
  have hb_le_one : b ≤ 1 := by
    rw [hbdef]
    calc PiPrior Kset ≤ PiPrior Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hb_ne_top : b ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hb_le_one ENNReal.one_lt_top)
  set ν : Measure H := b⁻¹ • PiPrior.restrict Kset with hνdef
  haveI hνprob : IsProbabilityMeasure ν := by
    constructor
    rw [hνdef, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter, ← hbdef]
    exact ENNReal.inv_mul_cancel hb_ne_zero hb_ne_top
  have hν_ac : ν ≪ PiPrior := by
    rw [hνdef]
    have h1 : PiPrior.restrict Kset ≪ PiPrior :=
      Measure.absolutelyContinuous_of_le (Measure.restrict_le_self (μ := PiPrior) (s := Kset))
    have h2 : b⁻¹ • PiPrior ≪ PiPrior :=
      Measure.absolutelyContinuous_of_le_smul (le_refl (b⁻¹ • PiPrior))
    exact (h1.smul b⁻¹).trans h2
  have hK_meas : MeasurableSet Kset := by
    rw [hKdef]
    exact statopia_math_node_3155168291_3ca337d1 μ p0 hp0_meas hp0_int dens hdens_meas
      hdens_lt_top δ₀
  have hν_K : ∀ᵐ h ∂ν, h ∈ Kset := by
    rw [ae_iff]
    change ν Ksetᶜ = 0
    rw [hνdef, Measure.smul_apply, Measure.restrict_apply hK_meas.compl]
    have hempty : Ksetᶜ ∩ Kset = ∅ := by
      ext h; simp
    rw [hempty, measure_empty, smul_zero]
  have hν_norm : ∀ᵐ h ∂ν, ∫⁻ x, dens h x ∂μ ≤ 1 :=
    hdens_norm.filter_mono (Measure.AbsolutelyContinuous.ae_le hν_ac)
  set g : H → X → ℝ :=
    fun h x => Real.log (dens h x).toReal - Real.log (p0 x).toReal with hgdef
  have hpair_meas : ∀ h : H, Measurable fun x : X => (h, x) := fun h =>
    measurable_prodMk_left
  have hdens_h_meas : ∀ h : H, Measurable (dens h) := fun h =>
    hdens_meas.comp (hpair_meas h)
  have hg_meas : Measurable (Function.uncurry g) := by
    rw [hgdef]
    have h1 : Measurable fun p : H × X => Real.log (dens p.1 p.2).toReal :=
      hdens_meas.ennreal_toReal.log
    have h2 : Measurable fun p : H × X => Real.log (p0 p.2).toReal :=
      (hp0_meas.ennreal_toReal.log).comp measurable_snd
    exact h1.sub h2
  have hpert : ∀ h : H, h ∈ Kset → (∫⁻ x, dens h x ∂μ ≤ 1) →
      MeasureTheory.Integrable (g h) (μ.withDensity p0) ∧
      (-δ₁ ≤ ∫ x, g h x ∂(μ.withDensity p0)) ∧
      (∫ x, g h x ∂(μ.withDensity p0) ≤ 0) ∧
      (∫⁻ x, ENNReal.ofReal (max (g h x) 0) ∂(μ.withDensity p0) ≤ 1) ∧
      (∫⁻ x, ENNReal.ofReal (max (-(g h x)) 0) ∂(μ.withDensity p0)
        ≤ ENNReal.ofReal (δ₁ + 1)) := by
    intro h hK hnorm
    have hK' : InformationTheory.klDiv (μ.withDensity p0) (μ.withDensity (dens h))
        < ENNReal.ofReal δ₀ := by
      have h' := hK
      rw [hKdef] at h'
      exact h'
    have hkl_ne : InformationTheory.klDiv (μ.withDensity p0) (μ.withDensity (dens h)) ≠ ⊤ :=
      ne_of_lt (lt_of_lt_of_le hK' le_top)
    obtain ⟨hne, hlt, hInt, hlow, hpos, hneg⟩ :=
      statopia_math_node_3862551001_c5ec6ec7 μ p0 (dens h) hp0_meas
        (hdens_h_meas h) hp0_int hnorm hkl_ne
    have hKlt : (InformationTheory.klDiv (μ.withDensity p0) (μ.withDensity (dens h))).toReal
        < δ₀ := by
      have h2 := (ENNReal.toReal_lt_toReal hkl_ne ENNReal.ofReal_ne_top).mpr hK'
      rwa [ENNReal.toReal_ofReal (le_of_lt hδ₀pos)] at h2
    have hInt' : MeasureTheory.Integrable
        (fun x => Real.log (dens h x).toReal - Real.log (p0 x).toReal) (μ.withDensity p0) := hInt
    obtain ⟨hupper, hdef⟩ :=
      statopia_math_node_2407238401_b71e9352 μ p0 (dens h) hp0_meas
        (hdens_h_meas h) hp0_int hnorm hne hlt hInt' hlow
    have hlowg : -(InformationTheory.klDiv (μ.withDensity p0)
          (μ.withDensity (dens h))).toReal
        ≤ (∫ x, g h x ∂(μ.withDensity p0))
          + (1 - (μ.withDensity (dens h)).real Set.univ) := by
      rw [hPuniv] at hlow
      rw [hgdef]
      exact hlow
    refine ⟨hInt, ?_, ?_, ?_, ?_⟩
    · linarith [hlowg, hdef, hKlt, Real.sqrt_le_sqrt (le_of_lt hKlt), hδ₀bound,
        Real.sqrt_nonneg δ₀]
    · rw [hgdef]; exact hupper
    · rw [hgdef]; exact hpos
    · refine le_trans ?_ (ENNReal.ofReal_le_ofReal (by linarith :
        (InformationTheory.klDiv (μ.withDensity p0) (μ.withDensity (dens h))).toReal + 1
          ≤ δ₁ + 1))
      rw [hgdef]
      exact hneg
  have hInt_ae : ∀ᵐ h ∂ν, MeasureTheory.Integrable (g h) (μ.withDensity p0) := by
    filter_upwards [hν_K, hν_norm] with h hK hnorm
    exact (hpert h hK hnorm).1
  have hLower_ae : ∀ᵐ h ∂ν, -δ₁ ≤ ∫ x, g h x ∂(μ.withDensity p0) := by
    filter_upwards [hν_K, hν_norm] with h hK hnorm
    exact (hpert h hK hnorm).2.1
  have hUpper_ae : ∀ᵐ h ∂ν, ∫ x, g h x ∂(μ.withDensity p0) ≤ 0 := by
    filter_upwards [hν_K, hν_norm] with h hK hnorm
    exact (hpert h hK hnorm).2.2.1
  have hPos_ae : ∀ᵐ h ∂ν,
      ∫⁻ x, ENNReal.ofReal (max (g h x) 0) ∂(μ.withDensity p0) ≤ 1 := by
    filter_upwards [hν_K, hν_norm] with h hK hnorm
    exact (hpert h hK hnorm).2.2.2.1
  have hNeg_ae : ∀ᵐ h ∂ν,
      ∫⁻ x, ENNReal.ofReal (max (-(g h x)) 0) ∂(μ.withDensity p0)
        ≤ ENNReal.ofReal (δ₁ + 1) := by
    filter_upwards [hν_K, hν_norm] with h hK hnorm
    exact (hpert h hK hnorm).2.2.2.2
  have hFneg_meas :
      Measurable fun p : H × X => ENNReal.ofReal (max (-(Function.uncurry g p)) 0) :=
    (hg_meas.neg.max measurable_const).ennreal_ofReal
  have hFpos_meas :
      Measurable fun p : H × X => ENNReal.ofReal (max (Function.uncurry g p) 0) :=
    (hg_meas.max measurable_const).ennreal_ofReal
  have hNegFin : ∀ᵐ x ∂(μ.withDensity p0),
      ∫⁻ h, ENNReal.ofReal (max (-(g h x)) 0) ∂ν < ⊤ := by
    have hmeas : AEMeasurable
        (fun x : X => ∫⁻ h, ENNReal.ofReal (max (-(g h x)) 0) ∂ν) (μ.withDensity p0) :=
      AEMeasurable.lintegral_prod_left
        (f := fun h x => ENNReal.ofReal (max (-(g h x)) 0)) hFneg_meas.aemeasurable
    refine ae_lt_top' hmeas ?_
    have h1 : ∫⁻ x, (∫⁻ h, ENNReal.ofReal (max (-(g h x)) 0) ∂ν) ∂(μ.withDensity p0)
        = ∫⁻ p : H × X, ENNReal.ofReal (max (-(Function.uncurry g p)) 0)
            ∂(ν.prod (μ.withDensity p0)) :=
      (MeasureTheory.lintegral_prod_symm (μ := ν) (ν := μ.withDensity p0)
        (fun p : H × X => ENNReal.ofReal (max (-(Function.uncurry g p)) 0))
        hFneg_meas.aemeasurable).symm
    have h2 : ∫⁻ p : H × X, ENNReal.ofReal (max (-(Function.uncurry g p)) 0)
          ∂(ν.prod (μ.withDensity p0))
        = ∫⁻ h, (∫⁻ x, ENNReal.ofReal (max (-(g h x)) 0) ∂(μ.withDensity p0)) ∂ν :=
      MeasureTheory.lintegral_prod (μ := ν) (ν := μ.withDensity p0)
        (fun p : H × X => ENNReal.ofReal (max (-(Function.uncurry g p)) 0))
        hFneg_meas.aemeasurable
    rw [h1.trans h2]
    refine ne_of_lt (lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top (r := δ₁ + 1)))
    calc ∫⁻ h, (∫⁻ x, ENNReal.ofReal (max (-(g h x)) 0) ∂(μ.withDensity p0)) ∂ν
        ≤ ∫⁻ _, ENNReal.ofReal (δ₁ + 1) ∂ν := lintegral_mono_ae hNeg_ae
      _ = ENNReal.ofReal (δ₁ + 1) * ν Set.univ := lintegral_const _
      _ = ENNReal.ofReal (δ₁ + 1) := by rw [measure_univ, mul_one]
  have hPosFin : ∀ᵐ x ∂(μ.withDensity p0),
      ∫⁻ h, ENNReal.ofReal (max (g h x) 0) ∂ν < ⊤ := by
    have hmeas : AEMeasurable
        (fun x : X => ∫⁻ h, ENNReal.ofReal (max (g h x) 0) ∂ν) (μ.withDensity p0) :=
      AEMeasurable.lintegral_prod_left
        (f := fun h x => ENNReal.ofReal (max (g h x) 0)) hFpos_meas.aemeasurable
    refine ae_lt_top' hmeas ?_
    have h1 : ∫⁻ x, (∫⁻ h, ENNReal.ofReal (max (g h x) 0) ∂ν) ∂(μ.withDensity p0)
        = ∫⁻ p : H × X, ENNReal.ofReal (max (Function.uncurry g p) 0)
            ∂(ν.prod (μ.withDensity p0)) :=
      (MeasureTheory.lintegral_prod_symm (μ := ν) (ν := μ.withDensity p0)
        (fun p : H × X => ENNReal.ofReal (max (Function.uncurry g p) 0))
        hFpos_meas.aemeasurable).symm
    have h2 : ∫⁻ p : H × X, ENNReal.ofReal (max (Function.uncurry g p) 0)
          ∂(ν.prod (μ.withDensity p0))
        = ∫⁻ h, (∫⁻ x, ENNReal.ofReal (max (g h x) 0) ∂(μ.withDensity p0)) ∂ν :=
      MeasureTheory.lintegral_prod (μ := ν) (ν := μ.withDensity p0)
        (fun p : H × X => ENNReal.ofReal (max (Function.uncurry g p) 0))
        hFpos_meas.aemeasurable
    rw [h1.trans h2]
    refine ne_of_lt (lt_of_le_of_lt ?_ ENNReal.one_lt_top)
    calc ∫⁻ h, (∫⁻ x, ENNReal.ofReal (max (g h x) 0) ∂(μ.withDensity p0)) ∂ν
        ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂ν := lintegral_mono_ae hPos_ae
      _ = 1 * ν Set.univ := lintegral_const _
      _ = 1 := by rw [measure_univ, mul_one]
  set eps : ℝ := (δ - δ₁) / 2 with hepsdef
  have hepspos : 0 < eps := by
    rw [hepsdef]; linarith
  have hepslt : δ₁ + eps < δ := by
    rw [hepsdef, hδ₁def]; linarith
  have hcore := statopia_math_node_341907188_a9df01ea (μ.withDensity p0) ν g hg_meas
    δ₁ eps hepspos hInt_ae hUpper_ae hLower_ae hPos_ae hNeg_ae hNegFin hPosFin
  have hbν : b • ν = PiPrior.restrict Kset := by
    rw [hνdef, smul_smul, mul_comm, ENNReal.inv_mul_cancel hb_ne_zero hb_ne_top, one_smul]
  have hsmulInt : ∀ G : H → ℝ≥0∞, ∫⁻ h, G h ∂(b • ν) = b • ∫⁻ h, G h ∂ν := by
    intro G
    rw [MeasureTheory.lintegral_smul_measure]
  have hident : ∀ᵐ x ∂(Measure.infinitePi (fun _ : ℕ => μ.withDensity p0)), ∀ᵐ h ∂ν,
      ∀ n : ℕ, ∏ i ∈ Finset.range n, (dens h (x i) * (p0 (x i))⁻¹)
        = ENNReal.ofReal (Real.exp (∑ i ∈ Finset.range n, g h (x i))) := by
    have hcyl : ∀ (i : ℕ) (A : Set X), MeasurableSet A →
        (Measure.infinitePi (fun _ : ℕ => μ.withDensity p0)) {x : ℕ → X | x i ∈ A}
          = (μ.withDensity p0) A := by
      intro i A hA
      have h := Measure.infinitePi_pi (fun _ : ℕ => (μ.withDensity p0))
        (s := {i}) (t := fun _ : ℕ => A) (by intro j hj; exact hA)
      have hset : Set.pi (↑({i} : Finset ℕ)) (fun _ : ℕ => A) = {x : ℕ → X | x i ∈ A} := by
        ext x
        simp [Set.mem_pi, Finset.mem_singleton]
      rw [hset, Finset.prod_singleton] at h
      exact h
    have hsingle : ∀ (a c : ℝ≥0∞), a ≠ 0 → a ≠ ⊤ → c ≠ 0 → c ≠ ⊤ →
        a * c⁻¹ = ENNReal.ofReal (Real.exp (Real.log a.toReal - Real.log c.toReal)) := by
      intro a c ha0 hat hc0 hct
      have hctop : c⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hc0
      have hprod : a * c⁻¹ ≠ ⊤ := ENNReal.mul_ne_top hat hctop
      rw [← ENNReal.ofReal_toReal hprod]
      congr 1
      rw [ENNReal.toReal_mul, ENNReal.toReal_inv, Real.exp_sub,
        Real.exp_log (ENNReal.toReal_pos ha0 hat), Real.exp_log (ENNReal.toReal_pos hc0 hct),
        div_eq_mul_inv]
    have hdens_good_ae : ∀ᵐ h ∂ν, ∀ᵐ x ∂(μ.withDensity p0),
        dens h x ≠ 0 ∧ dens h x < ⊤ := by
      filter_upwards [hν_K, hν_norm] with h hK hnorm
      have hK' : InformationTheory.klDiv (μ.withDensity p0) (μ.withDensity (dens h))
          < ENNReal.ofReal δ₀ := by
        have h' := hK
        rw [hKdef] at h'
        exact h'
      have hkl_ne : InformationTheory.klDiv (μ.withDensity p0) (μ.withDensity (dens h)) ≠ ⊤ :=
        ne_of_lt (lt_of_lt_of_le hK' le_top)
      obtain ⟨hne, hlt, -⟩ :=
        statopia_math_node_3862551001_c5ec6ec7 μ p0 (dens h) hp0_meas
          (hdens_h_meas h) hp0_int hnorm hkl_ne
      filter_upwards [hne, hlt] with x h1 h2 using ⟨h1, h2⟩
    have hp0_good : ∀ᵐ x ∂(μ.withDensity p0), p0 x ≠ 0 ∧ p0 x < ⊤ := by
      filter_upwards [hP_ne_zero, hP_lt_top] with x h1 h2 using ⟨h1, h2⟩
    have hcoord : ∀ᵐ h ∂ν, ∀ᵐ x ∂(Measure.infinitePi (fun _ : ℕ => μ.withDensity p0)),
        ∀ i : ℕ, dens h (x i) ≠ 0 ∧ dens h (x i) < ⊤ ∧ p0 (x i) ≠ 0 ∧ p0 (x i) < ⊤ := by
      filter_upwards [hdens_good_ae] with h hgood
      have hcomb : ∀ᵐ x ∂(μ.withDensity p0),
          dens h x ≠ 0 ∧ dens h x < ⊤ ∧ p0 x ≠ 0 ∧ p0 x < ⊤ := by
        filter_upwards [hgood, hp0_good] with x h1 h2
        exact ⟨h1.1, h1.2, h2.1, h2.2⟩
      set Bad : Set X := {y : X | dens h y = 0} ∪ {y : X | dens h y = ⊤}
        ∪ {y : X | p0 y = 0} ∪ {y : X | p0 y = ⊤} with hBaddef
      have hBad_meas : MeasurableSet Bad := by
        rw [hBaddef]
        exact (((hdens_h_meas h (measurableSet_singleton 0)).union
          (hdens_h_meas h (measurableSet_singleton ⊤))).union
          (hp0_meas (measurableSet_singleton 0))).union (hp0_meas (measurableSet_singleton ⊤))
      have hBad0 : (μ.withDensity p0) Bad = 0 := by
        have hsets : {y : X | ¬ (dens h y ≠ 0 ∧ dens h y < ⊤ ∧ p0 y ≠ 0 ∧ p0 y < ⊤)} = Bad := by
          rw [hBaddef]
          ext y
          simp only [Set.mem_setOf_eq, Set.mem_union, lt_top_iff_ne_top]
          constructor
          · intro hn
            by_cases h0 : dens h y = 0
            · exact Or.inl (Or.inl (Or.inl h0))
            · by_cases h1 : dens h y = ⊤
              · exact Or.inl (Or.inl (Or.inr h1))
              · by_cases h2 : p0 y = 0
                · exact Or.inl (Or.inr h2)
                · exact Or.inr (by_contra fun h3 => hn ⟨h0, h1, h2, h3⟩)
          · intro hd hconj
            exact hd.elim
              (fun hl => hl.elim
                (fun hAB => hAB.elim (fun h0 => hconj.1 h0) (fun h1 => hconj.2.1 h1))
                (fun h2 => hconj.2.2.1 h2))
              (fun h3 => hconj.2.2.2 h3)
        rw [← hsets]
        exact MeasureTheory.ae_iff.mp hcomb
      have hcyl0 : ∀ i : ℕ, (Measure.infinitePi (fun _ : ℕ => μ.withDensity p0))
          {x : ℕ → X | x i ∈ Bad} = 0 := by
        intro i
        rw [hcyl i Bad hBad_meas, hBad0]
      have hmain : ∀ᵐ x ∂(Measure.infinitePi (fun _ : ℕ => μ.withDensity p0)),
          ∀ i : ℕ, x i ∉ Bad := by
        rw [ae_iff]
        have hsets : {x : ℕ → X | ¬ ∀ i : ℕ, x i ∉ Bad}
            = ⋃ i : ℕ, {x : ℕ → X | x i ∈ Bad} := by
          ext x
          simp only [Set.mem_setOf_eq, Set.mem_iUnion]
          simp only [not_forall, not_not]
        rw [hsets]
        exact measure_iUnion_null hcyl0
      filter_upwards [hmain] with x hx
      intro i
      have hx' := hx i
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro hzero; exact hx' (by simp [hBaddef, hzero])
      · rw [lt_top_iff_ne_top]; intro htop; exact hx' (by simp [hBaddef, htop])
      · intro hzero; exact hx' (by simp [hBaddef, hzero])
      · rw [lt_top_iff_ne_top]; intro htop; exact hx' (by simp [hBaddef, htop])
    have hident_pt : ∀ (h : H) (y : ℕ → X),
        (∀ i : ℕ, dens h (y i) ≠ 0 ∧ dens h (y i) < ⊤ ∧ p0 (y i) ≠ 0 ∧ p0 (y i) < ⊤) →
        ∀ n : ℕ, ∏ i ∈ Finset.range n, (dens h (y i) * (p0 (y i))⁻¹)
          = ENNReal.ofReal (Real.exp (∑ i ∈ Finset.range n, g h (y i))) := by
      have hofReal_prod : ∀ (s : Finset ℕ) (F : ℕ → ℝ),
          (∏ i ∈ s, ENNReal.ofReal (Real.exp (F i)))
            = ENNReal.ofReal (∏ i ∈ s, Real.exp (F i)) := by
        intro s F
        induction s using Finset.induction with
        | empty => simp
        | insert a s ha ih =>
            rw [Finset.prod_insert ha, Finset.prod_insert ha, ih,
              ← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos (F a)))]
      intro h y hy n
      have hstep1 : (∏ i ∈ Finset.range n, (dens h (y i) * (p0 (y i))⁻¹))
          = ∏ i ∈ Finset.range n, ENNReal.ofReal
              (Real.exp (Real.log (dens h (y i)).toReal - Real.log (p0 (y i)).toReal)) := by
        refine Finset.prod_congr rfl ?_
        intro i hi
        exact hsingle (dens h (y i)) (p0 (y i)) (hy i).1
          (ne_of_lt (hy i).2.1) (hy i).2.2.1 (ne_of_lt (hy i).2.2.2)
      rw [hstep1, hofReal_prod (Finset.range n)
        (fun i => Real.log (dens h (y i)).toReal - Real.log (p0 (y i)).toReal)]
      congr 1
      rw [Real.exp_sum]
    set A : Set (H × (ℕ → X)) := ⋃ i : ℕ,
      ({z : H × (ℕ → X) | dens z.1 (z.2 i) = 0} ∪ {z : H × (ℕ → X) | dens z.1 (z.2 i) = ⊤}
        ∪ {z : H × (ℕ → X) | p0 (z.2 i) = 0} ∪ {z : H × (ℕ → X) | p0 (z.2 i) = ⊤}) with hAdef
    have hA_meas : MeasurableSet A := by
      rw [hAdef]
      apply MeasurableSet.iUnion
      intro i
      have hd : Measurable fun z : H × (ℕ → X) => dens z.1 (z.2 i) :=
        hdens_meas.comp (Measurable.prodMk measurable_fst ((measurable_pi_apply i).comp measurable_snd))
      have hp : Measurable fun z : H × (ℕ → X) => p0 (z.2 i) :=
        hp0_meas.comp ((measurable_pi_apply i).comp measurable_snd)
      exact (((hd (measurableSet_singleton 0)).union (hd (measurableSet_singleton ⊤))).union
        (hp (measurableSet_singleton 0))).union (hp (measurableSet_singleton ⊤))
    have hmemA : ∀ (h : H) (x : ℕ → X),
        ((h, x) ∈ A ↔ ∃ i : ℕ,
          ((dens h (x i) = 0 ∨ dens h (x i) = ⊤) ∨ p0 (x i) = 0) ∨ p0 (x i) = ⊤) := by
      intro h x
      rw [hAdef]
      simp only [Set.mem_iUnion, Set.mem_union, Set.mem_setOf_eq]
    have hnotA : ∀ (h : H) (x : ℕ → X),
        (∀ i : ℕ, dens h (x i) ≠ 0 ∧ dens h (x i) < ⊤ ∧ p0 (x i) ≠ 0 ∧ p0 (x i) < ⊤) →
        (h, x) ∉ A := by
      intro h x hg hmem
      obtain ⟨i, hi⟩ := (hmemA h x).1 hmem
      have h1 : dens h (x i) ≠ 0 := (hg i).1
      have h2 : dens h (x i) ≠ ⊤ := ne_of_lt (hg i).2.1
      have h3 : p0 (x i) ≠ 0 := (hg i).2.2.1
      have h4 : p0 (x i) ≠ ⊤ := ne_of_lt (hg i).2.2.2
      have hni : ¬ (((dens h (x i) = 0 ∨ dens h (x i) = ⊤) ∨ p0 (x i) = 0) ∨ p0 (x i) = ⊤) :=
        fun hb =>
          Or.elim hb
            (fun hl => Or.elim hl
              (fun hAB => Or.elim hAB (fun h0 => h1 h0) (fun ht => h2 ht))
              (fun hz => h3 hz))
            (fun hz2 => h4 hz2)
      exact hni hi
    have hgood_of_notA : ∀ (h : H) (x : ℕ → X), (h, x) ∉ A →
        ∀ i : ℕ, dens h (x i) ≠ 0 ∧ dens h (x i) < ⊤ ∧ p0 (x i) ≠ 0 ∧ p0 (x i) < ⊤ := by
      intro h x hnot i
      have hni : ¬ (((dens h (x i) = 0 ∨ dens h (x i) = ⊤) ∨ p0 (x i) = 0) ∨ p0 (x i) = ⊤) := by
        intro hb
        exact hnot ((hmemA h x).2 ⟨i, hb⟩)
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro h0; exact hni (Or.inl (Or.inl (Or.inl h0)))
      · rw [lt_top_iff_ne_top]; intro ht; exact hni (Or.inl (Or.inl (Or.inr ht)))
      · intro h0; exact hni (Or.inl (Or.inr h0))
      · rw [lt_top_iff_ne_top]; intro ht; exact hni (Or.inr ht)
    have hF_meas : Measurable (A.indicator (fun _ => (1 : ℝ≥0∞))) :=
      measurable_const.indicator hA_meas
    have hmeasure_ind : ∫⁻ z, A.indicator (fun _ => (1 : ℝ≥0∞)) z
        ∂(ν.prod (Measure.infinitePi (fun _ : ℕ => μ.withDensity p0)))
        = (ν.prod (Measure.infinitePi (fun _ : ℕ => μ.withDensity p0))) A := by
      rw [lintegral_indicator hA_meas]
      rw [show ∫⁻ z in A, (1 : ℝ≥0∞)
            ∂(ν.prod (Measure.infinitePi (fun _ : ℕ => μ.withDensity p0)))
          = ∫⁻ z, (1 : ℝ≥0∞)
              ∂((ν.prod (Measure.infinitePi (fun _ : ℕ => μ.withDensity p0))).restrict A) from rfl]
      rw [lintegral_const, one_mul, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    have hA_null : (ν.prod (Measure.infinitePi (fun _ : ℕ => μ.withDensity p0))) A = 0 := by
      have hgood_prod :
          ∀ᵐ z ∂(ν.prod (Measure.infinitePi (fun _ : ℕ => μ.withDensity p0))), z ∉ A := by
        rw [MeasureTheory.Measure.ae_prod_iff_ae_ae (p := fun z : H × (ℕ → X) => z ∉ A)
          hA_meas.compl]
        exact hcoord.mono (fun h hh => hh.mono (fun x hx => hnotA h x hx))
      have := MeasureTheory.ae_iff.mp hgood_prod
      simpa using this
    have hzeroint : ∫⁻ x, (∫⁻ h, A.indicator (fun _ => (1 : ℝ≥0∞)) (h, x) ∂ν)
        ∂(Measure.infinitePi (fun _ : ℕ => μ.withDensity p0)) = 0 := by
      rw [← MeasureTheory.lintegral_prod_symm (μ := ν)
        (ν := Measure.infinitePi (fun _ : ℕ => μ.withDensity p0))
        (f := fun z : H × (ℕ → X) => A.indicator (fun _ => (1 : ℝ≥0∞)) z) hF_meas.aemeasurable]
      rw [hmeasure_ind, hA_null]
    have hae : ∀ᵐ x ∂(Measure.infinitePi (fun _ : ℕ => μ.withDensity p0)),
        ∀ᵐ h ∂ν, ∀ i : ℕ, dens h (x i) ≠ 0 ∧ dens h (x i) < ⊤ ∧ p0 (x i) ≠ 0 ∧ p0 (x i) < ⊤ := by
      have hmeas_int : AEMeasurable
          (fun x : ℕ → X => ∫⁻ h, A.indicator (fun _ => (1 : ℝ≥0∞)) (h, x) ∂ν)
          (Measure.infinitePi (fun _ : ℕ => μ.withDensity p0)) :=
        AEMeasurable.lintegral_prod_left
          (f := fun h x => A.indicator (fun _ => (1 : ℝ≥0∞)) (h, x)) hF_meas.aemeasurable
      have hzero_ae : ∀ᵐ x ∂(Measure.infinitePi (fun _ : ℕ => μ.withDensity p0)),
          ∫⁻ h, A.indicator (fun _ => (1 : ℝ≥0∞)) (h, x) ∂ν = 0 :=
        (MeasureTheory.lintegral_eq_zero_iff' hmeas_int).mp hzeroint
      filter_upwards [hzero_ae] with x hx
      have hsecA : MeasurableSet {h : H | (h, x) ∈ A} :=
        hA_meas.preimage (Measurable.prodMk measurable_id measurable_const)
      have hsec_int : ν {h : H | (h, x) ∈ A}
          = ∫⁻ h, ({h' : H | (h', x) ∈ A}).indicator (fun _ => (1 : ℝ≥0∞)) h ∂ν := by
        rw [lintegral_indicator hsecA]
        rw [show ∫⁻ h in {h' : H | (h', x) ∈ A}, (1 : ℝ≥0∞) ∂ν
            = ∫⁻ h, (1 : ℝ≥0∞) ∂(ν.restrict {h' : H | (h', x) ∈ A}) from rfl]
        rw [lintegral_const, one_mul, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      have hsec_zero : ν {h : H | (h, x) ∈ A} = 0 := by
        rw [hsec_int]
        have hxs : ∫⁻ h, ({h' : H | (h', x) ∈ A}).indicator (fun _ => (1 : ℝ≥0∞)) h ∂ν
            = ∫⁻ h, A.indicator (fun _ => (1 : ℝ≥0∞)) (h, x) ∂ν := rfl
        rw [hxs, hx]
      have hnotmem : ∀ᵐ h ∂ν, (h, x) ∉ A := by
        rw [ae_iff]
        simpa using hsec_zero
      filter_upwards [hnotmem] with h hh
      exact hgood_of_notA h x hh
    exact hae.mono (fun x hx => hx.mono (fun h hh => hident_pt h x hh))
  set η : ℝ := δ - (δ₁ + eps) with hηdef
  have hηpos : 0 < η := by
    rw [hηdef]; linarith
  have hb_toReal_pos : 0 < b.toReal := ENNReal.toReal_pos hb_ne_zero hb_ne_top
  have hev : ∀ᶠ n : ℕ in atTop, Real.exp (-(n : ℝ) * η) ≤ b.toReal := by
    obtain ⟨N₀, hN₀⟩ := exists_nat_ge (-(Real.log b.toReal) / η)
    refine eventually_atTop.2 ⟨N₀, fun n hn => ?_⟩
    have hn' : (-(Real.log b.toReal) / η) ≤ (n : ℝ) := le_trans hN₀ (by exact_mod_cast hn)
    have h1 : -(Real.log b.toReal) ≤ (n : ℝ) * η := by
      have h2 := mul_le_mul_of_nonneg_right hn' (le_of_lt hηpos)
      rwa [div_mul_cancel₀ _ (ne_of_gt hηpos)] at h2
    have h3 : Real.exp (-(n : ℝ) * η) ≤ Real.exp (Real.log b.toReal) := by
      apply Real.exp_le_exp.2
      have hrs : -(n : ℝ) * η = -((n : ℝ) * η) := by ring
      rw [hrs]
      linarith
    rwa [Real.exp_log hb_toReal_pos] at h3
  filter_upwards [hcore, hident] with x hxcore hxident
  obtain ⟨N₁, hN₁⟩ := hxcore
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 hev
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hn₁ : N₁ ≤ n := le_trans (le_max_left N₁ N₂) hn
  have hn₂ : N₂ ≤ n := le_trans (le_max_right N₁ N₂) hn
  have hstep : ENNReal.ofReal (Real.exp (-(n : ℝ) * δ))
      ≤ b * ENNReal.ofReal (Real.exp (-(n : ℝ) * (δ₁ + eps))) := by
    rw [← ENNReal.ofReal_toReal hb_ne_top, ← ENNReal.ofReal_mul (le_of_lt hb_toReal_pos)]
    apply ENNReal.ofReal_le_ofReal
    have hsplit : -(n : ℝ) * δ = -(n : ℝ) * (δ₁ + eps) + -(n : ℝ) * η := by
      rw [hηdef]; ring
    calc Real.exp (-(n : ℝ) * δ)
        = Real.exp (-(n : ℝ) * (δ₁ + eps)) * Real.exp (-(n : ℝ) * η) := by
          rw [hsplit, Real.exp_add]
      _ ≤ Real.exp (-(n : ℝ) * (δ₁ + eps)) * b.toReal :=
          mul_le_mul_of_nonneg_left (hN₂ n hn₂) (le_of_lt (Real.exp_pos _))
      _ = b.toReal * Real.exp (-(n : ℝ) * (δ₁ + eps)) := mul_comm _ _
  have hcongr : (∫⁻ h, ENNReal.ofReal (Real.exp (∑ i ∈ Finset.range n, g h (x i))) ∂ν)
      = ∫⁻ h, ∏ i ∈ Finset.range n, (dens h (x i) * (p0 (x i))⁻¹) ∂ν :=
    lintegral_congr_ae (hxident.mono fun h hh => (hh n).symm)
  calc ENNReal.ofReal (Real.exp (-(n : ℝ) * δ))
      ≤ b * ENNReal.ofReal (Real.exp (-(n : ℝ) * (δ₁ + eps))) := hstep
    _ ≤ b * (∫⁻ h, ENNReal.ofReal (Real.exp (∑ i ∈ Finset.range n, g h (x i))) ∂ν) :=
        mul_le_mul_left' (hN₁ n hn₁) b
    _ = b * (∫⁻ h, ∏ i ∈ Finset.range n, (dens h (x i) * (p0 (x i))⁻¹) ∂ν) := by
        rw [hcongr]
    _ = ∫⁻ h, ∏ i ∈ Finset.range n, (dens h (x i) * (p0 (x i))⁻¹) ∂(b • ν) :=
        (hsmulInt _).symm
    _ = ∫⁻ h, ∏ i ∈ Finset.range n, (dens h (x i) * (p0 (x i))⁻¹) ∂(PiPrior.restrict Kset) := by
        rw [hbν]
    _ = ∫⁻ h in Kset, ∏ i ∈ Finset.range n, (dens h (x i) * (p0 (x i))⁻¹) ∂PiPrior := rfl
    _ ≤ ∫⁻ h, ∏ i ∈ Finset.range n, (dens h (x i) * (p0 (x i))⁻¹) ∂PiPrior := by
        rw [← lintegral_indicator hK_meas]
        exact lintegral_mono (fun h => Set.indicator_le_self Kset _ h)
  /- @proof-region region.target-node.session.2d97536fa28e7d13 end -/

end Statlib.Imported
