import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.Vocabulary
import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.Base

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal MeasureTheory Topology BigOperators
open Statlib.Imported
open Statlib.Imported.DPMModel

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal MeasureTheory Topology BigOperators
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_3931880993_971defe3 : ∀ {X : Type*} [MeasurableSpace X] (μ : Measure X) (p0 f : X → ℝ≥0∞)
    (hp0_meas : Measurable p0) (hf_meas : Measurable f)
    (hp0_int : ∫⁻ x, p0 x ∂μ = 1)
    (hkl : InformationTheory.klDiv (μ.withDensity p0) (μ.withDensity f) ≠ ⊤)
    (hf_ne_zero : ∀ᵐ x ∂(μ.withDensity p0), f x ≠ 0)
    (hf_lt_top : ∀ᵐ x ∂(μ.withDensity p0), f x < ⊤),
    (∫⁻ x, ENNReal.ofReal (max (-(Real.log (f x).toReal - Real.log (p0 x).toReal)) 0)
      ∂(μ.withDensity p0)) ≠ ⊤ := by
  /- @proof-region region.target-node.session.a898ad74f86704d8 begin -/
  intro X _ μ p0 f hp0_meas hf_meas hp0_int hkl hf_ne_zero hf_lt_top
  have hmax : ∀ x, ENNReal.ofReal (max (-(Real.log (f x).toReal - Real.log (p0 x).toReal)) 0)
      = ENNReal.ofReal (-(Real.log (f x).toReal - Real.log (p0 x).toReal)) := by
    intro x
    rw [ENNReal.ofReal_max, ENNReal.ofReal_zero]
    simp
  rw [MeasureTheory.lintegral_congr hmax]
  rw [InformationTheory.klDiv_def] at hkl
  have hcond : (μ.withDensity p0) ≪ (μ.withDensity f) ∧
      Integrable (MeasureTheory.llr (μ.withDensity p0) (μ.withDensity f)) (μ.withDensity p0) := by
    by_contra h
    exact hkl (if_neg h)
  have hae1 : ∀ᵐ x ∂μ, p0 x ≠ 0 → f x ≠ 0 := (MeasureTheory.ae_withDensity_iff hp0_meas).mp hf_ne_zero
  have hae2 : ∀ᵐ x ∂μ, p0 x ≠ 0 → f x < ⊤ := (MeasureTheory.ae_withDensity_iff hp0_meas).mp hf_lt_top
  have hmul : ∀ᵐ x ∂μ, f x * (p0 x / f x) = p0 x := by
    filter_upwards [hae1, hae2] with x h1 h2
    by_cases hp : p0 x = 0
    · simp [hp]
    · rw [mul_comm, ENNReal.div_mul_cancel (h1 hp) (ne_of_lt (h2 hp))]
  have hQdens : (μ.withDensity f).withDensity (fun x => p0 x / f x) = μ.withDensity p0 := by
    rw [← MeasureTheory.withDensity_mul μ hf_meas (hp0_meas.div hf_meas)]
    exact MeasureTheory.withDensity_congr_ae hmul
  have hne_top_llr : (∫⁻ x, ENNReal.ofReal (max (MeasureTheory.llr (μ.withDensity p0) (μ.withDensity f) x) 0)
      ∂(μ.withDensity p0)) ≠ ⊤ :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hcond.2.pos_part.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => le_max_right _ _)).mpr hcond.2.pos_part
  have hfinal : (fun x => ENNReal.ofReal (-(Real.log (f x).toReal - Real.log (p0 x).toReal)))
      =ᵐ[μ.withDensity p0]
      (fun x => ENNReal.ofReal (max (MeasureTheory.llr (μ.withDensity p0) (μ.withDensity f) x) 0)) := by
    haveI hdec : (μ.withDensity p0).HaveLebesgueDecomposition (μ.withDensity f) :=
      ⟨(0, fun x => p0 x / f x), hp0_meas.div hf_meas,
        ⟨Set.univ, MeasurableSet.univ, by simp, by simp⟩, by rw [zero_add, ← hQdens]⟩
    have hρ : (μ.withDensity f).withDensity
        (MeasureTheory.Measure.rnDeriv (μ.withDensity p0) (μ.withDensity f)) = μ.withDensity p0 :=
      Measure.withDensity_rnDeriv_eq _ _ hcond.1
    have hPuniv : (μ.withDensity p0) Set.univ = 1 := by
      have h := MeasureTheory.withDensity_apply (μ := μ) (f := p0) MeasurableSet.univ
      rw [h]
      simp [hp0_int]
    have key : ∀ (g' ρ' : X → ℝ≥0∞), Measurable g' → Measurable ρ' →
        (μ.withDensity f).withDensity g' = μ.withDensity p0 →
        (μ.withDensity f).withDensity ρ' = μ.withDensity p0 →
        g' =ᵐ[μ.withDensity f] ρ' := by
      intro g' ρ' hg' hρ' h1 h2
      have hg_eq : ∫⁻ x, g' x ∂(μ.withDensity f) = 1 := by
        have h := MeasureTheory.withDensity_apply (μ := (μ.withDensity f)) (f := g') MeasurableSet.univ
        have h' : ∫⁻ x, g' x ∂(μ.withDensity f) = ((μ.withDensity f).withDensity g') Set.univ := by
          simpa using h.symm
        rw [h', h1, hPuniv]
      have hρ_eq : ∫⁻ x, ρ' x ∂(μ.withDensity f) = 1 := by
        have h := MeasureTheory.withDensity_apply (μ := (μ.withDensity f)) (f := ρ') MeasurableSet.univ
        have h' : ∫⁻ x, ρ' x ∂(μ.withDensity f) = ((μ.withDensity f).withDensity ρ') Set.univ := by
          simpa using h.symm
        rw [h', h2, hPuniv]
      have hg_top : ∀ᵐ x ∂(μ.withDensity f), g' x < ⊤ :=
        MeasureTheory.ae_lt_top hg' (by rw [hg_eq]; exact ENNReal.one_ne_top)
      have hρ_top : ∀ᵐ x ∂(μ.withDensity f), ρ' x < ⊤ :=
        MeasureTheory.ae_lt_top hρ' (by rw [hρ_eq]; exact ENNReal.one_ne_top)
      have hsum_meas : Measurable fun x => g' x + ρ' x := hg'.add hρ'
      haveI hηfin : IsFiniteMeasure ((μ.withDensity f).withDensity fun x => g' x + ρ' x) := by
        constructor
        have huniv : ((μ.withDensity f).withDensity fun x => g' x + ρ' x) Set.univ
            = ∫⁻ x, (g' x + ρ' x) ∂(μ.withDensity f) := by
          have h := MeasureTheory.withDensity_apply (μ := (μ.withDensity f))
            (fun x => g' x + ρ' x) MeasurableSet.univ
          simpa using h
        rw [huniv, MeasureTheory.lintegral_add_left hg' ρ', hg_eq, hρ_eq]
        exact ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, ENNReal.one_lt_top⟩
      have hptg : ∀ᵐ x ∂(μ.withDensity f),
          (g' x + ρ' x) * (g' x / (g' x + ρ' x)) = g' x := by
        filter_upwards [hg_top, hρ_top] with x h1' h2'
        by_cases h0 : g' x + ρ' x = 0
        · have hg0 : g' x = 0 := by
            have hle : g' x ≤ g' x + ρ' x := by
              calc g' x = g' x + 0 := (add_zero _).symm
                _ ≤ g' x + ρ' x := add_le_add_right (zero_le _) _
            simpa [h0] using hle
          rw [h0, hg0]
          simp
        · have htop : g' x + ρ' x < ⊤ := ENNReal.add_lt_top.mpr ⟨h1', h2'⟩
          rw [mul_comm, ENNReal.div_mul_cancel h0 (ne_of_lt htop)]
      have hptρ : ∀ᵐ x ∂(μ.withDensity f),
          (g' x + ρ' x) * (ρ' x / (g' x + ρ' x)) = ρ' x := by
        filter_upwards [hg_top, hρ_top] with x h1' h2'
        by_cases h0 : g' x + ρ' x = 0
        · have hρ0 : ρ' x = 0 := by
            have hle : ρ' x ≤ g' x + ρ' x := by
              calc ρ' x = 0 + ρ' x := (zero_add _).symm
                _ ≤ g' x + ρ' x := add_le_add_left (zero_le _) _
            simpa [h0] using hle
          rw [h0, hρ0]
          simp
        · have htop : g' x + ρ' x < ⊤ := ENNReal.add_lt_top.mpr ⟨h1', h2'⟩
          rw [mul_comm, ENNReal.div_mul_cancel h0 (ne_of_lt htop)]
      have hη1 : ((μ.withDensity f).withDensity fun x => g' x + ρ' x).withDensity
          (fun x => g' x / (g' x + ρ' x)) = μ.withDensity p0 := by
        rw [← MeasureTheory.withDensity_mul (μ.withDensity f) hsum_meas (hg'.div hsum_meas)]
        exact (MeasureTheory.withDensity_congr_ae hptg).trans h1
      have hη2 : ((μ.withDensity f).withDensity fun x => g' x + ρ' x).withDensity
          (fun x => ρ' x / (g' x + ρ' x)) = μ.withDensity p0 := by
        rw [← MeasureTheory.withDensity_mul (μ.withDensity f) hsum_meas (hρ'.div hsum_meas)]
        exact (MeasureTheory.withDensity_congr_ae hptρ).trans h2
      have hrn1 : MeasureTheory.Measure.rnDeriv (μ.withDensity p0)
          ((μ.withDensity f).withDensity fun x => g' x + ρ' x)
          =ᵐ[((μ.withDensity f).withDensity fun x => g' x + ρ' x)]
          (fun x => g' x / (g' x + ρ' x)) := by
        have h := MeasureTheory.Measure.rnDeriv_withDensity
          ((μ.withDensity f).withDensity fun x => g' x + ρ' x)
          (f := fun x => g' x / (g' x + ρ' x)) (hg'.div hsum_meas)
        rwa [hη1] at h
      have hrn2 : MeasureTheory.Measure.rnDeriv (μ.withDensity p0)
          ((μ.withDensity f).withDensity fun x => g' x + ρ' x)
          =ᵐ[((μ.withDensity f).withDensity fun x => g' x + ρ' x)]
          (fun x => ρ' x / (g' x + ρ' x)) := by
        have h := MeasureTheory.Measure.rnDeriv_withDensity
          ((μ.withDensity f).withDensity fun x => g' x + ρ' x)
          (f := fun x => ρ' x / (g' x + ρ' x)) (hρ'.div hsum_meas)
        rwa [hη2] at h
      have hquot : ∀ᵐ x ∂(μ.withDensity f), (g' x + ρ' x) ≠ 0 →
          g' x / (g' x + ρ' x) = ρ' x / (g' x + ρ' x) :=
        (MeasureTheory.ae_withDensity_iff hsum_meas).mp (hrn1.symm.trans hrn2)
      have hsum_top : ∀ᵐ x ∂(μ.withDensity f), g' x + ρ' x < ⊤ := by
        filter_upwards [hg_top, hρ_top] with x h1' h2'
        exact ENNReal.add_lt_top.mpr ⟨h1', h2'⟩
      filter_upwards [hquot, hsum_top] with x hq ht
      by_cases h0 : g' x + ρ' x = 0
      · have hg0 : g' x = 0 := by
          have hle : g' x ≤ g' x + ρ' x := by
            calc g' x = g' x + 0 := (add_zero _).symm
              _ ≤ g' x + ρ' x := add_le_add_right (zero_le _) _
          simpa [h0] using hle
        have hρ0 : ρ' x = 0 := by
          have hle : ρ' x ≤ g' x + ρ' x := by
            calc ρ' x = 0 + ρ' x := (zero_add _).symm
              _ ≤ g' x + ρ' x := add_le_add_left (zero_le _) _
          simpa [h0] using hle
        rw [hg0, hρ0]
      · have hmul : (g' x / (g' x + ρ' x)) * (g' x + ρ' x)
            = (ρ' x / (g' x + ρ' x)) * (g' x + ρ' x) :=
          congrArg (fun t => t * (g' x + ρ' x)) (hq h0)
        rw [ENNReal.div_mul_cancel h0 (ne_of_lt ht), ENNReal.div_mul_cancel h0 (ne_of_lt ht)] at hmul
        exact hmul
    have hρg : (fun x => p0 x / f x) =ᵐ[μ.withDensity f]
        (fun x => MeasureTheory.Measure.rnDeriv (μ.withDensity p0) (μ.withDensity f) x) :=
      key (fun x => p0 x / f x) (MeasureTheory.Measure.rnDeriv (μ.withDensity p0) (μ.withDensity f))
        (hp0_meas.div hf_meas) (MeasureTheory.Measure.measurable_rnDeriv _ _) hQdens hρ
    have hp0_ne : ∀ᵐ x ∂(μ.withDensity p0), p0 x ≠ 0 :=
      (MeasureTheory.ae_withDensity_iff hp0_meas).mpr (Filter.Eventually.of_forall fun _ h => h)
    have hp0_top : ∀ᵐ x ∂(μ.withDensity p0), p0 x < ⊤ := by
      refine (MeasureTheory.ae_withDensity_iff hp0_meas).mpr ?_
      filter_upwards [MeasureTheory.ae_lt_top hp0_meas (by rw [hp0_int]; exact ENNReal.one_ne_top)] with x hx
      exact fun _ => hx
    have hρgP : (fun x => MeasureTheory.Measure.rnDeriv (μ.withDensity p0) (μ.withDensity f) x)
        =ᵐ[μ.withDensity p0] (fun x => p0 x / f x) := by
      have hbase : ∀ᵐ x ∂(μ.withDensity f), p0 x / f x ≠ 0 →
          MeasureTheory.Measure.rnDeriv (μ.withDensity p0) (μ.withDensity f) x = p0 x / f x := by
        filter_upwards [hρg] with x hx _
        exact hx.symm
      have hQd : ∀ᵐ x ∂((μ.withDensity f).withDensity fun x => p0 x / f x),
          MeasureTheory.Measure.rnDeriv (μ.withDensity p0) (μ.withDensity f) x = p0 x / f x :=
        (MeasureTheory.ae_withDensity_iff (hp0_meas.div hf_meas)).mpr hbase
      simpa only [hQdens] using hQd
    have hllr : MeasureTheory.llr (μ.withDensity p0) (μ.withDensity f)
        =ᵐ[μ.withDensity p0] (fun x => -(Real.log (f x).toReal - Real.log (p0 x).toReal)) := by
      rw [MeasureTheory.llr_def]
      filter_upwards [hρgP, hp0_ne, hp0_top, hf_ne_zero, hf_lt_top] with x hx hp0n hp0t hfn hft
      rw [hx]
      have htoReal : (p0 x / f x).toReal = (p0 x).toReal / (f x).toReal := by
        rw [ENNReal.div_eq_inv_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, ← div_eq_inv_mul]
      rw [htoReal]
      have hp0ne : (p0 x).toReal ≠ 0 := ne_of_gt (ENNReal.toReal_pos hp0n (ne_of_lt hp0t))
      have hfne : (f x).toReal ≠ 0 := ne_of_gt (ENNReal.toReal_pos hfn (ne_of_lt hft))
      rw [Real.log_div hp0ne hfne]
      ring
    filter_upwards [hllr] with x hx
    rw [hx, hmax x]
  rw [MeasureTheory.lintegral_congr_ae hfinal]
  exact hne_top_llr
  /- @proof-region region.target-node.session.a898ad74f86704d8 end -/

end Statlib.Imported
