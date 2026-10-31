import ProverJobs.manual_dp_weakcons_repair_20261031.Contraction
import ProverJobs.manual_dp_weakcons_repair_20261031.BoxedWeakCons.CorrectedTesting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators
open OfflineCorrectedDP.Statlib.Imported
noncomputable section
namespace OfflineDPLatentPosterior

set_option autoImplicit false in
theorem statopia_math_node_1034431849_4a9cb240 : ∀ {X : Type*} [MeasurableSpace X]
    (μ : Measure X)
    (p0 : X → ℝ≥0∞) (hp0 : Measurable p0)
    (hp0_int : ∫⁻ x, p0 x ∂μ = 1)
    (n : ℕ) (f : Fin n → X → ℝ≥0∞) (hf : ∀ i : Fin n, Measurable (f i))
    (hf_int : ∀ i : Fin n, ∫⁻ x, f i x ∂μ = 1)
    (T : Set (Fin n → X)) (hT : MeasurableSet T),
    ∫⁻ x : Fin n → X,
        T.indicator (fun x => ∏ i : Fin n, (f i (x i) * (p0 (x i))⁻¹)) x
        ∂(Measure.pi (fun _ : Fin n => μ.withDensity p0))
      ≤ Measure.pi (fun i : Fin n => μ.withDensity (f i)) T := by
  /- @proof-region region.target-node.session.f3ecbc08da2204ee begin -/
  classical
  intro X _ mu p0 hp0 hp0_int n f hf hf_int T hT
  set σ : X → ℝ≥0∞ := fun x => p0 x + ∑ i : Fin n, f i x with hσ
  have hσmeas : Measurable σ := by
    rw [hσ]
    exact hp0.add (Finset.measurable_sum Finset.univ (fun i _ => hf i))
  have hσint : ∫⁻ x, σ x ∂mu = 1 + (n : ℝ≥0∞) := by
    rw [hσ]
    rw [lintegral_add_left hp0]
    rw [lintegral_finset_sum Finset.univ (fun i _ => hf i)]
    simp [hp0_int, hf_int]
  haveI hfin : IsFiniteMeasure (mu.withDensity σ) :=
    isFiniteMeasure_withDensity (by rw [hσint]; simp)
  haveI hsig : SigmaFinite (mu.withDensity σ) := inferInstance
  have key : ∀ (m : ℕ) (ρ : Measure X), SigmaFinite ρ →
      ∀ (g : Fin m → X → ℝ≥0∞), (∀ i, Measurable (g i)) →
      (∀ i, ∫⁻ x, g i x ∂ρ ≠ ⊤) →
      ∀ (G : (Fin m → X) → ℝ≥0∞), Measurable G →
      ∫⁻ x, G x ∂(Measure.pi (fun i : Fin m => ρ.withDensity (g i)))
        = ∫⁻ x, G x * ∏ i : Fin m, g i (x i) ∂(Measure.pi (fun _ : Fin m => ρ)) := by
    intro m
    induction m with
    | zero =>
      intro ρ hρ g hg hfin G hG
      have hfam : (fun i : Fin 0 => ρ.withDensity (g i)) = (fun _ : Fin 0 => ρ) := by
        funext i
        exact i.elim0
      rw [hfam]
      refine lintegral_congr_ae (Eventually.of_forall fun x => ?_)
      simp
    | succ m ih =>
      intro ρ hρ g hg hfin G hG
      haveI hρS : SigmaFinite ρ := hρ
      haveI hDfin : ∀ i : Fin (m + 1), IsFiniteMeasure (ρ.withDensity (g i)) :=
        fun i => isFiniteMeasure_withDensity (hfin i)
      set e : (Fin (m + 1) → X) ≃ᵐ (X × (Fin m → X)) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => X) 0 with he
      set P : Measure (Fin m → X) := Measure.pi (fun _ : Fin m => ρ) with hP
      set B : Measure (Fin m → X) :=
        Measure.pi (fun j : Fin m => ρ.withDensity (g ((0 : Fin (m + 1)).succAbove j))) with hB
      have happ : ∀ x : Fin (m + 1) → X,
          e x = (x 0, fun j : Fin m => x ((0 : Fin (m + 1)).succAbove j)) := by
        intro x
        rfl
      have hmap1 : Measure.map (⇑e) (Measure.pi (fun i : Fin (m + 1) => ρ.withDensity (g i)))
          = (ρ.withDensity (g 0)).prod B := by
        have h := (measurePreserving_piFinSuccAbove (fun i : Fin (m + 1) => ρ.withDensity (g i)) 0).map_eq
        simpa [he, hB] using h
      have hmap2 : Measure.map (⇑e) (Measure.pi (fun _ : Fin (m + 1) => ρ))
          = ρ.prod P := by
        have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => ρ) 0).map_eq
        simpa [he, hP] using h
      have hc0 : ∀ (a : X) (y : Fin m → X), (e.symm (a, y)) 0 = a := by
        intro a y
        have h := e.apply_symm_apply (a, y)
        rw [happ] at h
        exact congrArg Prod.fst h
      have hc : ∀ (a : X) (y : Fin m → X) (j : Fin m),
          (e.symm (a, y)) ((0 : Fin (m + 1)).succAbove j) = y j := by
        intro a y j
        have h := e.apply_symm_apply (a, y)
        rw [happ] at h
        exact congrFun (congrArg Prod.snd h) j
      have hinner : ∀ a : X, Measurable fun y : Fin m → X => G (e.symm (a, y)) := by
        intro a
        exact hG.comp (e.symm.measurable.comp
          (Measurable.prod (f := fun y : Fin m → X => (a, y)) measurable_const measurable_id))
      have hFmeas : Measurable fun x : Fin (m + 1) → X => G x * ∏ i : Fin (m + 1), g i (x i) :=
        hG.mul (Finset.measurable_prod Finset.univ (fun i _ => (hg i).comp (measurable_pi_apply i)))
      have hfin' : ∀ j : Fin m, ∫⁻ x, g ((0 : Fin (m + 1)).succAbove j) x ∂ρ ≠ ⊤ := fun j => hfin _
      have ih' : ∀ a : X, ∫⁻ y : Fin m → X, G (e.symm (a, y)) ∂B
          = ∫⁻ y : Fin m → X,
              G (e.symm (a, y)) * ∏ j : Fin m, g ((0 : Fin (m + 1)).succAbove j) (y j) ∂P := by
        intro a
        have h := ih ρ hρ (fun j => g ((0 : Fin (m + 1)).succAbove j)) (fun j => hg _) hfin'
          (fun y => G (e.symm (a, y))) (hinner a)
        simpa [hB, hP] using h
      have step1 : ∫⁻ x : Fin (m + 1) → X, G x ∂(Measure.pi (fun i : Fin (m + 1) => ρ.withDensity (g i)))
          = ∫⁻ z : X × (Fin m → X), G (e.symm z) ∂((ρ.withDensity (g 0)).prod B) := by
        have hlm : ∫⁻ z : X × (Fin m → X), G (e.symm z)
            ∂(Measure.map (⇑e) (Measure.pi (fun i : Fin (m + 1) => ρ.withDensity (g i))))
            = ∫⁻ x : Fin (m + 1) → X, G x ∂(Measure.pi (fun i : Fin (m + 1) => ρ.withDensity (g i))) := by
          rw [MeasureTheory.lintegral_map (g := ⇑e) (f := fun z : X × (Fin m → X) => G (e.symm z))
            (hG.comp e.symm.measurable) e.measurable]
          simp
        rw [← hmap1]
        exact hlm.symm
      have step2 : ∫⁻ z : X × (Fin m → X),
            (fun x : Fin (m + 1) → X => G x * ∏ i : Fin (m + 1), g i (x i)) (e.symm z) ∂(ρ.prod P)
          = ∫⁻ x : Fin (m + 1) → X, G x * ∏ i : Fin (m + 1), g i (x i)
              ∂(Measure.pi (fun _ : Fin (m + 1) => ρ)) := by
        have hlm : ∫⁻ z : X × (Fin m → X),
              (fun x : Fin (m + 1) → X => G x * ∏ i : Fin (m + 1), g i (x i)) (e.symm z)
            ∂(Measure.map (⇑e) (Measure.pi (fun _ : Fin (m + 1) => ρ)))
            = ∫⁻ x : Fin (m + 1) → X, G x * ∏ i : Fin (m + 1), g i (x i)
                ∂(Measure.pi (fun _ : Fin (m + 1) => ρ)) := by
          rw [MeasureTheory.lintegral_map (g := ⇑e)
            (f := fun z : X × (Fin m → X) =>
              (fun x : Fin (m + 1) → X => G x * ∏ i : Fin (m + 1), g i (x i)) (e.symm z))
            (hFmeas.comp e.symm.measurable) e.measurable]
          simp
        rw [← hmap2]
        exact hlm
      have hprod : ∀ (a : X) (y : Fin m → X),
          (fun x : Fin (m + 1) → X => G x * ∏ i : Fin (m + 1), g i (x i)) (e.symm (a, y))
            = G (e.symm (a, y)) *
                (g 0 a * ∏ j : Fin m, g ((0 : Fin (m + 1)).succAbove j) (y j)) := by
        intro a y
        have hp : ∏ i : Fin (m + 1), g i ((e.symm (a, y)) i)
            = g 0 a * ∏ j : Fin m, g ((0 : Fin (m + 1)).succAbove j) (y j) := by
          rw [Fin.prod_univ_succAbove (fun i => g i ((e.symm (a, y)) i)) 0, hc0 a y]
          congr 1
        simp only [hp]
      calc ∫⁻ x : Fin (m + 1) → X, G x ∂(Measure.pi (fun i : Fin (m + 1) => ρ.withDensity (g i)))
          = ∫⁻ z : X × (Fin m → X), G (e.symm z) ∂((ρ.withDensity (g 0)).prod B) := step1
        _ = ∫⁻ z : X × (Fin m → X), G (e.symm z) ∂((ρ.prod B).withDensity fun z => g 0 z.1) := by
              rw [MeasureTheory.prod_withDensity_left (hg 0)]
        _ = ∫⁻ z : X × (Fin m → X), (g 0 z.1) * G (e.symm z) ∂(ρ.prod B) := by
              exact MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀
                (μ := ρ.prod B) (f := fun z : X × (Fin m → X) => g 0 z.1)
                ((hg 0).comp measurable_fst).aemeasurable
                (hG.comp e.symm.measurable).aemeasurable
        _ = ∫⁻ a : X, ∫⁻ y : Fin m → X, (g 0 a) * G (e.symm (a, y)) ∂B ∂ρ := by
              rw [MeasureTheory.lintegral_prod
                (f := fun z : X × (Fin m → X) => (g 0 z.1) * G (e.symm z))
                (((hg 0).comp measurable_fst).mul (hG.comp e.symm.measurable)).aemeasurable]
        _ = ∫⁻ a : X, (g 0 a) * (∫⁻ y : Fin m → X, G (e.symm (a, y)) ∂B) ∂ρ := by
              refine lintegral_congr_ae (Eventually.of_forall fun a => ?_)
              exact MeasureTheory.lintegral_const_mul (g 0 a) (hinner a)
        _ = ∫⁻ a : X, (g 0 a) * (∫⁻ y : Fin m → X,
              G (e.symm (a, y)) * ∏ j : Fin m, g ((0 : Fin (m + 1)).succAbove j) (y j) ∂P) ∂ρ := by
              refine lintegral_congr_ae (Eventually.of_forall fun a => ?_)
              simp only [ih' a]
        _ = ∫⁻ a : X, ∫⁻ y : Fin m → X,
              (g 0 a) * (G (e.symm (a, y)) *
                ∏ j : Fin m, g ((0 : Fin (m + 1)).succAbove j) (y j)) ∂P ∂ρ := by
              refine lintegral_congr_ae (Eventually.of_forall fun a => ?_)
              exact (MeasureTheory.lintegral_const_mul (g 0 a)
                ((hinner a).mul (Finset.measurable_prod Finset.univ
                  (fun j _ => (hg _).comp (measurable_pi_apply j))))).symm
        _ = ∫⁻ a : X, ∫⁻ y : Fin m → X,
              G (e.symm (a, y)) *
                (g 0 a * ∏ j : Fin m, g ((0 : Fin (m + 1)).succAbove j) (y j)) ∂P ∂ρ := by
              refine lintegral_congr_ae (Eventually.of_forall fun a => ?_)
              refine lintegral_congr_ae (Eventually.of_forall fun y => ?_)
              exact mul_left_comm (g 0 a) (G (e.symm (a, y)))
                (∏ j : Fin m, g ((0 : Fin (m + 1)).succAbove j) (y j))
        _ = ∫⁻ a : X, ∫⁻ y : Fin m → X,
              (fun x : Fin (m + 1) → X => G x * ∏ i : Fin (m + 1), g i (x i)) (e.symm (a, y))
                ∂P ∂ρ := by
              refine lintegral_congr_ae (Eventually.of_forall fun a => ?_)
              refine lintegral_congr_ae (Eventually.of_forall fun y => ?_)
              exact (hprod a y).symm
        _ = ∫⁻ z : X × (Fin m → X),
              (fun x : Fin (m + 1) → X => G x * ∏ i : Fin (m + 1), g i (x i)) (e.symm z)
                ∂(ρ.prod P) := by
              rw [MeasureTheory.lintegral_prod
                (f := fun z : X × (Fin m → X) =>
                  (fun x : Fin (m + 1) → X => G x * ∏ i : Fin (m + 1), g i (x i)) (e.symm z))
                (hFmeas.comp e.symm.measurable).aemeasurable]
        _ = ∫⁻ x : Fin (m + 1) → X, G x * ∏ i : Fin (m + 1), g i (x i)
              ∂(Measure.pi (fun _ : Fin (m + 1) => ρ)) := step2
  set φp : X → ℝ≥0∞ := fun x => p0 x * (σ x)⁻¹ with hφp
  set φf : Fin n → X → ℝ≥0∞ := fun i x => f i x * (σ x)⁻¹ with hφf
  have hφp_meas : Measurable φp := by
    rw [hφp]
    exact hp0.mul hσmeas.inv
  have hφf_meas : ∀ i, Measurable (φf i) := by
    intro i
    rw [hφf]
    exact (hf i).mul hσmeas.inv
  have hinvle : ∀ a : ℝ≥0∞, a⁻¹ * a ≤ 1 := by
    intro a
    by_cases h0 : a = 0
    · simp [h0]
    by_cases ht : a = ⊤
    · simp [ht]
    · exact le_of_eq (ENNReal.inv_mul_cancel h0 ht)
  have hmul_le : ∀ (h : X → ℝ≥0∞) (x : X), σ x * (h x * (σ x)⁻¹) ≤ h x := by
    intro h x
    calc σ x * (h x * (σ x)⁻¹) = h x * ((σ x)⁻¹ * σ x) := by
          rw [mul_comm (σ x), mul_assoc]
      _ ≤ h x * 1 := mul_le_mul_left' (hinvle (σ x)) (h x)
      _ = h x := mul_one (h x)
  have hfinA : ∫⁻ x, φp x ∂(mu.withDensity σ) ≠ ⊤ := by
    have h1 : ∫⁻ x, φp x ∂(mu.withDensity σ) ≤ ∫⁻ x, (σ * φp) x ∂mu :=
      MeasureTheory.lintegral_withDensity_le_lintegral_mul mu hσmeas φp
    have h2 : ∫⁻ x, (σ * φp) x ∂mu ≤ ∫⁻ x, p0 x ∂mu := by
      refine lintegral_mono fun x => ?_
      exact hmul_le p0 x
    rw [hp0_int] at h2
    exact ne_top_of_le_ne_top (by simp) (le_trans h1 h2)
  have hfinB : ∀ i, ∫⁻ x, φf i x ∂(mu.withDensity σ) ≠ ⊤ := by
    intro i
    have h1 : ∫⁻ x, φf i x ∂(mu.withDensity σ) ≤ ∫⁻ x, (σ * φf i) x ∂mu :=
      MeasureTheory.lintegral_withDensity_le_lintegral_mul mu hσmeas (φf i)
    have h2 : ∫⁻ x, (σ * φf i) x ∂mu ≤ ∫⁻ x, f i x ∂mu := by
      refine lintegral_mono fun x => ?_
      exact hmul_le (f i) x
    rw [hf_int i] at h2
    exact ne_top_of_le_ne_top (by simp) (le_trans h1 h2)
  have hσne : ∫⁻ x, σ x ∂mu ≠ ⊤ := by
    rw [hσint]; simp
  have hσtop : ∀ᵐ x ∂mu, σ x < ⊤ := MeasureTheory.ae_lt_top hσmeas hσne
  have hle : ∀ x : X, p0 x ≤ σ x := by
    intro x
    rw [hσ]
    simpa using add_le_add_left (zero_le (∑ i : Fin n, f i x)) (p0 x)
  have hlef : ∀ (i : Fin n) (x : X), f i x ≤ σ x := by
    intro i x
    have h1 : f i x ≤ p0 x + ∑ j : Fin n, f j x := by
      refine le_trans (Finset.single_le_sum (fun j _ => zero_le (f j x)) (Finset.mem_univ i)) ?_
      have h3 := add_le_add_left (zero_le (p0 x)) (∑ j : Fin n, f j x)
      simpa [add_comm (∑ j : Fin n, f j x) (p0 x)] using h3
    rw [hσ]
    simpa using h1
  have hpt : ∀ x : X, σ x ≠ ⊤ → σ x * φp x = p0 x := by
    intro x ht
    by_cases h0 : σ x = 0
    · have hz : p0 x = 0 := le_antisymm (h0 ▸ hle x) (zero_le _)
      rw [hz, h0, zero_mul]
    · have hcancel : (σ x)⁻¹ * σ x = 1 := ENNReal.inv_mul_cancel h0 ht
      show σ x * (p0 x * (σ x)⁻¹) = p0 x
      rw [mul_comm (σ x) (p0 x * (σ x)⁻¹), mul_assoc, hcancel, mul_one]
  have hptf : ∀ (i : Fin n) (x : X), σ x ≠ ⊤ → σ x * φf i x = f i x := by
    intro i x ht
    by_cases h0 : σ x = 0
    · have hz : f i x = 0 := le_antisymm (h0 ▸ hlef i x) (zero_le _)
      rw [hz, h0, zero_mul]
    · have hcancel : (σ x)⁻¹ * σ x = 1 := ENNReal.inv_mul_cancel h0 ht
      show σ x * (f i x * (σ x)⁻¹) = f i x
      rw [mul_comm (σ x) (f i x * (σ x)⁻¹), mul_assoc, hcancel, mul_one]
  have hA : mu.withDensity p0 = (mu.withDensity σ).withDensity φp := by
    rw [← MeasureTheory.withDensity_mul mu hσmeas hφp_meas]
    refine MeasureTheory.withDensity_congr_ae ?_
    filter_upwards [hσtop] with x hx
    exact (hpt x hx.ne).symm
  have hB : ∀ i, mu.withDensity (f i) = (mu.withDensity σ).withDensity (φf i) := by
    intro i
    rw [← MeasureTheory.withDensity_mul mu hσmeas (hφf_meas i)]
    refine MeasureTheory.withDensity_congr_ae ?_
    filter_upwards [hσtop] with x hx
    exact (hptf i x hx.ne).symm
  set hfun : (Fin n → X) → ℝ≥0∞ := fun y => ∏ i : Fin n, (f i (y i) * (p0 (y i))⁻¹) with hhfun
  have hfun_meas : Measurable hfun := by
    rw [hhfun]
    exact Finset.measurable_prod Finset.univ
      (fun i _ => ((hf i).comp (measurable_pi_apply i)).mul
        (((hp0).comp (measurable_pi_apply i)).inv))
  have hind1 : Measurable (T.indicator hfun) := hfun_meas.indicator hT
  have hind2 : Measurable (T.indicator (1 : (Fin n → X) → ℝ≥0∞)) := measurable_const.indicator hT
  have hkey1 := key n (mu.withDensity σ) hsig (fun _ : Fin n => φp) (fun _ => hφp_meas)
    (fun _ => hfinA) (T.indicator hfun) hind1
  have hkey2 := key n (mu.withDensity σ) hsig φf hφf_meas hfinB (T.indicator 1) hind2
  rw [hA]
  simp only [hB]
  calc ∫⁻ x : Fin n → X,
        T.indicator hfun x ∂(Measure.pi (fun _ : Fin n => (mu.withDensity σ).withDensity φp))
      = ∫⁻ x : Fin n → X, T.indicator hfun x * ∏ i : Fin n, φp (x i)
          ∂(Measure.pi (fun _ : Fin n => mu.withDensity σ)) := hkey1
    _ ≤ ∫⁻ x : Fin n → X, T.indicator (fun y : Fin n → X => ∏ i : Fin n, φf i (y i)) x
          ∂(Measure.pi (fun _ : Fin n => mu.withDensity σ)) := by
          refine lintegral_mono fun x => ?_
          by_cases hx : x ∈ T
          · simp only [Set.indicator_of_mem hx]
            calc hfun x * ∏ i : Fin n, φp (x i)
                = (∏ i : Fin n, (f i (x i) * (p0 (x i))⁻¹)) *
                    ∏ i : Fin n, (p0 (x i) * (σ (x i))⁻¹) := rfl
              _ = ∏ i : Fin n,
                    ((f i (x i) * (p0 (x i))⁻¹) * (p0 (x i) * (σ (x i))⁻¹)) := by
                    rw [← Finset.prod_mul_distrib]
              _ ≤ ∏ i : Fin n, (f i (x i) * (σ (x i))⁻¹) := by
                    refine Finset.prod_le_prod (fun i _ => zero_le _) (fun i _ => ?_)
                    calc (f i (x i) * (p0 (x i))⁻¹) * (p0 (x i) * (σ (x i))⁻¹)
                        = (f i (x i) * (σ (x i))⁻¹) * ((p0 (x i))⁻¹ * p0 (x i)) := by ac_rfl
                      _ ≤ (f i (x i) * (σ (x i))⁻¹) * 1 :=
                          mul_le_mul_left' (hinvle (p0 (x i))) _
                      _ = f i (x i) * (σ (x i))⁻¹ := mul_one _
          · show (if x ∈ T then hfun x else 0) * (∏ i : Fin n, φp (x i))
              ≤ (if x ∈ T then (∏ i : Fin n, φf i (x i)) else 0)
            rw [if_neg hx]
            simp
    _ ≤ Measure.pi (fun i : Fin n => (mu.withDensity σ).withDensity (φf i)) T := by
          rw [← MeasureTheory.lintegral_indicator_one
            (μ := Measure.pi (fun i : Fin n => (mu.withDensity σ).withDensity (φf i))) hT, hkey2]
          refine lintegral_mono fun x => ?_
          by_cases hx : x ∈ T
          · simp only [Set.indicator_of_mem hx, Pi.one_apply, one_mul]
            exact le_rfl
          · show (if x ∈ T then (∏ i : Fin n, φf i (x i)) else 0)
              ≤ (if x ∈ T then (1 : ℝ≥0∞) else 0) * ∏ i : Fin n, φf i (x i)
            rw [if_neg hx]
            exact zero_le _
  /- @proof-region region.target-node.session.f3ecbc08da2204ee end -/


/-- Testing of each full latent vector controls the whole posterior numerator. -/
theorem integrated_test_bound {X Θ : Type*} [MeasurableSpace X] [MeasurableSpace Θ]
    (μ : Measure X) (k : Θ → X → ℝ)
    (hk : Measurable (Function.uncurry k))
    (hk_int : ∀ θ, ∫⁻ x, ENNReal.ofReal (k θ x) ∂μ = 1)
    (p0 : X → ℝ≥0∞) (hp0 : Measurable p0)
    (hp0_int : ∫⁻ x, p0 x ∂μ = 1) (hp0_finite : ∀ x, p0 x ≠ ∞)
    (n : ℕ) (π : Measure (Fin n → Θ)) [IsProbabilityMeasure π]
    (B : Set (Fin n → Θ)) (hB : MeasurableSet B)
    (T : Set (Fin n → X)) (hT : MeasurableSet T) (e : ℝ≥0∞)
    (htest : ∀ θ ∈ B,
      (Measure.pi (fun i : Fin n => μ.withDensity (fun x => ENNReal.ofReal (k (θ i) x))))
        Tᶜ ≤ e) :
    ∫⁻ xs in Tᶜ, (∫⁻ θ in B,
      (∏ i : Fin n, ENNReal.ofReal (k (θ i) (xs i))) /
        (∏ i : Fin n, p0 (xs i)) ∂π)
      ∂Measure.pi (fun _ : Fin n => μ.withDensity p0) ≤ e := by
  classical
  haveI : IsProbabilityMeasure (μ.withDensity p0) := ⟨by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hp0_int]⟩
  let ν := Measure.pi (fun _ : Fin n => μ.withDensity p0)
  let R : (Fin n → X) → (Fin n → Θ) → ℝ≥0∞ := fun xs θ =>
    (∏ i : Fin n, ENNReal.ofReal (k (θ i) (xs i))) / (∏ i : Fin n, p0 (xs i))
  have hR : Measurable (Function.uncurry R) := by
    apply Measurable.div
    · apply Finset.measurable_prod
      intro i _
      have hmtheta : Measurable (fun z : (Fin n → X) × (Fin n → Θ) => z.2 i) :=
        (measurable_pi_apply i).comp measurable_snd
      have hmx : Measurable (fun z : (Fin n → X) × (Fin n → Θ) => z.1 i) :=
        (measurable_pi_apply i).comp measurable_fst
      exact ENNReal.measurable_ofReal.comp (hk.comp (hmtheta.prodMk hmx))
    · apply Finset.measurable_prod
      intro i _
      exact hp0.comp ((measurable_pi_apply i).comp measurable_fst)
  have hrw : ∀ xs θ, R xs θ = ∏ i : Fin n,
      (ENNReal.ofReal (k (θ i) (xs i)) * (p0 (xs i))⁻¹) := by
    intro xs θ
    exact (ENNReal.prod_div_distrib_of_ne_top (fun i _ => hp0_finite (xs i))).symm
  change (∫⁻ xs in Tᶜ, ∫⁻ θ in B, R xs θ ∂π ∂ν) ≤ e
  rw [lintegral_lintegral_swap hR.aemeasurable]
  calc
    ∫⁻ θ in B, ∫⁻ xs in Tᶜ, R xs θ ∂ν ∂π ≤ ∫⁻ θ in B, e ∂π := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hB] with θ hθ
      apply le_trans _ (htest θ hθ)
      have h := statopia_math_node_1034431849_4a9cb240 μ p0 hp0 hp0_int n
        (fun i x => ENNReal.ofReal (k (θ i) x))
        (fun i => ENNReal.measurable_ofReal.comp
          (hk.comp (measurable_const.prodMk measurable_id)))
        (fun i => hk_int (θ i)) Tᶜ hT.compl
      rw [← lintegral_indicator hT.compl]
      simpa only [R, hrw] using h
    _ ≤ e := by
      simp only [lintegral_const, Measure.restrict_apply_univ]
      exact (mul_le_mul_left' (prob_le_one : π B ≤ 1) e).trans (by simp)

end OfflineDPLatentPosterior
