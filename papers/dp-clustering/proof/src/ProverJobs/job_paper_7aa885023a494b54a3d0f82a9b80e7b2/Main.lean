import ProverJobs.job_paper_7aa885023a494b54a3d0f82a9b80e7b2.Vocabulary
import ProverJobs.job_paper_7aa885023a494b54a3d0f82a9b80e7b2.ProvedNodes
import ProverJobs.job_paper_7aa885023a494b54a3d0f82a9b80e7b2.Base

open MeasureTheory
open scoped ENNReal BigOperators
namespace Statlib.Imported

theorem paper_7aa885023a494b54a3d0f82a9b80e7b2
    (t : ℕ) (p θstar : Fin t → ℝ) (g q0 : ℝ → ℝ) (c m M U : ℝ)
    (hp_pos : ∀ j : Fin t, 0 < p j)
    (hp_lt : ∀ j : Fin t, p j < 1)
    (hp_sum : ∑ j : Fin t, p j = 1)
    (hc : 0 < c)
    (hg_pos : ∀ x ∈ Set.Icc (-c) c, 0 < g x)
    (hg_zero : ∀ x, x ∉ Set.Icc (-c) c → g x = 0)
    (hg_meas : Measurable g)
    (hg_int : Integrable g volume)
    (hg_mass : ∫ x, g x ∂volume = 1)
    (hq0_nonneg : ∀ θ : ℝ, 0 ≤ q0 θ)
    (hq0_meas : Measurable q0)
    (hq0_int : Integrable q0 volume)
    (hm_pos : 0 < m)
    (hmM : m ≤ M)
    (hT1 : ∀ x ∈ Set.Icc (-c) c, m ≤ g x ∧ g x ≤ M)
    (hU_pos : 0 < U)
    (hT3 : ∀ (j : Fin t) (y : ℝ), y ∈ Set.Icc (0 : ℝ) (2 * c) →
      symmPriorAt q0 (θstar j) y ≤ U)
    (hsep : ∀ (j l : Fin t), l ≠ j →
      ∀ x ∈ Set.Icc (θstar j - c) (θstar j + c), g (x - θstar l) = 0) :
    ∀ (n : ℕ), 0 < n → ∀ (j : Fin t) (s : ℕ), 1 ≤ s →
      ∀ A : Fin s → Finset (Fin n),
        (∫ X in partitionEvent n c (θstar j) s A,
            (∏ h : Fin s, ∫ θ : ℝ,
              ((A h).prod (fun i => g (X i - θ) / g (X i - θstar j))) * q0 θ ∂volume)
          ∂(Measure.pi (fun _ : Fin n => mixtureLaw p θstar g)))
        ≤ (U / m) ^ s * ∏ h : Fin s, 1 / (((A h).card : ℝ) + 1)
:= by
  /- @proof-region region.root.f3acf0edd9e0 begin -/
  intro n hn j s hs A
  have hg_nonneg : ∀ x : ℝ, 0 ≤ g x := by
    intro x
    by_cases hx : x ∈ Set.Icc (-c) c
    · exact le_of_lt (hg_pos x hx)
    · rw [hg_zero x hx]
  have hRHS_nonneg : 0 ≤ (U / m) ^ s * ∏ h : Fin s, 1 / (((A h).card : ℝ) + 1) :=
    mul_nonneg (pow_nonneg (le_of_lt (div_pos hU_pos hm_pos)) s)
      (Finset.prod_nonneg (fun h _ => by positivity))
  rcases eq_or_ne (partitionEvent n c (θstar j) s A) ∅ with hE | hE
  · rw [hE, MeasureTheory.setIntegral_empty]
    exact hRHS_nonneg
  · obtain ⟨X, hX⟩ := Set.nonempty_iff_ne_empty.mpr hE
    have hne : ∀ h : Fin s, (A h).Nonempty := hX.2.1
    have hdisj : ∀ h h' : Fin s, h ≠ h' → Disjoint (A h) (A h') := hX.2.2.2.1
    have harith : (∏ h : Fin s, U / (m * (((A h).card : ℝ) + 1)))
        = (U / m) ^ s * ∏ h : Fin s, 1 / (((A h).card : ℝ) + 1) := by
      have hm : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
      calc ∏ h : Fin s, U / (m * (((A h).card : ℝ) + 1))
          = ∏ h : Fin s, (U / m) * (1 / (((A h).card : ℝ) + 1)) := by
            refine Finset.prod_congr rfl (fun h _ => ?_)
            have hb : ((A h).card : ℝ) + 1 ≠ 0 := by positivity
            field_simp
        _ = (U / m) ^ s * ∏ h : Fin s, 1 / (((A h).card : ℝ) + 1) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have htrans : ∀ a : ℝ, ∫⁻ x : ℝ, ENNReal.ofReal (g (x - a)) = ∫⁻ x : ℝ, ENNReal.ofReal (g x) := by
      intro a
      have hmp : MeasurePreserving (fun x : ℝ => x + (-a)) volume volume :=
        measurePreserving_add_right volume (-a)
      have h := hmp.lintegral_comp (f := fun x : ℝ => ENNReal.ofReal (g x)) hg_meas.ennreal_ofReal
      simpa [sub_eq_add_neg] using h
    have hg_lintegral : ∫⁻ x : ℝ, ENNReal.ofReal (g x) = 1 := by
      rw [← ofReal_integral_eq_lintegral_ofReal hg_int (Filter.Eventually.of_forall hg_nonneg),
        hg_mass]
      simp
    have hmass : ∫⁻ x : ℝ, ENNReal.ofReal (∑ l : Fin t, p l * g (x - θstar l)) = 1 := by
      have hcongr : ∀ x : ℝ, ENNReal.ofReal (∑ l : Fin t, p l * g (x - θstar l))
          = ∑ l : Fin t, ENNReal.ofReal (p l * g (x - θstar l)) := by
        intro x
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro l _
        exact mul_nonneg (le_of_lt (hp_pos l)) (hg_nonneg _)
      calc ∫⁻ x : ℝ, ENNReal.ofReal (∑ l : Fin t, p l * g (x - θstar l))
          = ∫⁻ x : ℝ, ∑ l : Fin t, ENNReal.ofReal (p l * g (x - θstar l)) := by
            simp only [hcongr]
        _ = ∑ l : Fin t, ∫⁻ x : ℝ, ENNReal.ofReal (p l * g (x - θstar l)) := by
            rw [lintegral_finset_sum]
            intro l _
            exact Measurable.ennreal_ofReal
              (Measurable.const_mul (hg_meas.comp (measurable_id.sub measurable_const)) (p l))
        _ = ∑ l : Fin t, ENNReal.ofReal (p l) * 1 := by
            refine Finset.sum_congr rfl (fun l _ => ?_)
            have h1 : ∫⁻ x : ℝ, ENNReal.ofReal (p l * g (x - θstar l))
                = ∫⁻ x : ℝ, ENNReal.ofReal (p l) * ENNReal.ofReal (g (x - θstar l)) := by
              refine lintegral_congr (fun x => ?_)
              exact ENNReal.ofReal_mul (le_of_lt (hp_pos l))
            rw [h1, lintegral_const_mul, htrans (θstar l), hg_lintegral]
            exact (hg_meas.comp (measurable_id.sub measurable_const)).ennreal_ofReal
        _ = 1 := by
            simp only [mul_one]
            rw [← ENNReal.ofReal_sum_of_nonneg (fun l _ => le_of_lt (hp_pos l)), hp_sum]
            simp
    haveI hPprob : IsProbabilityMeasure (mixtureLaw p θstar g) := by
      refine ⟨?_⟩
      simp only [mixtureLaw]
      rw [withDensity_apply _ MeasurableSet.univ]
      simpa using hmass
    set F : (Fin n → ℝ) → ℝ := fun X => ∏ h : Fin s, ∫ θ : ℝ,
      ((A h).prod (fun i => g (X i - θ) / g (X i - θstar j))) * q0 θ ∂volume with hFdef
    set B : ℝ := ∏ h : Fin s, U / (m * (((A h).card : ℝ) + 1)) with hBdef
    have hBpos : 0 ≤ B := by
      rw [hBdef]
      refine Finset.prod_nonneg (fun h _ => ?_)
      have hb : (0 : ℝ) < ((A h).card : ℝ) + 1 := by positivity
      exact le_of_lt (div_pos hU_pos (mul_pos hm_pos hb))
    have hmain : ENNReal.ofReal
        (∫ X in partitionEvent n c (θstar j) s A, F X
          ∂(Measure.pi (fun _ : Fin n => mixtureLaw p θstar g))) ≤ ENNReal.ofReal B := by
      set G : (h : Fin s) → ({i : Fin n // i ∈ A h} → ℝ) → ℝ≥0∞ := fun h y =>
        ∫⁻ θ : ℝ, (∏ i : {i : Fin n // i ∈ A h},
            ENNReal.ofReal (g (y i - θ) / g (y i - θstar j))) * ENNReal.ofReal (q0 θ) ∂volume
        with hGdef
      have hGmeas : ∀ h : Fin s, Measurable (G h) := by
        intro h
        rw [hGdef]
        have hfac : Measurable fun p : ({i : Fin n // i ∈ A h} → ℝ) × ℝ =>
            ∏ i : {i : Fin n // i ∈ A h},
              ENNReal.ofReal (g (p.1 i - p.2) / g (p.1 i - θstar j)) := by
          refine Finset.measurable_prod _ (fun i _ => ?_)
          refine Measurable.ennreal_ofReal ?_
          exact (hg_meas.comp (((measurable_pi_apply i).comp measurable_fst).sub measurable_snd)).div
            (hg_meas.comp (((measurable_pi_apply i).comp measurable_fst).sub measurable_const))
        have hq : Measurable fun p : ({i : Fin n // i ∈ A h} → ℝ) × ℝ =>
            ENNReal.ofReal (q0 p.2) :=
          (hq0_meas.comp measurable_snd).ennreal_ofReal
        exact Measurable.lintegral_prod_right'
          (f := fun p : ({i : Fin n // i ∈ A h} → ℝ) × ℝ =>
            (∏ i : {i : Fin n // i ∈ A h},
              ENNReal.ofReal (g (p.1 i - p.2) / g (p.1 i - θstar j))) * ENNReal.ofReal (q0 p.2))
          (hfac.mul hq)
      have hbox := statopia_math_node_2961478954_435cb595 n c (θstar j) s A hn hc hs hne hdisj
        (mixtureLaw p θstar g) G hGmeas
      have hstep1 : ENNReal.ofReal
          (∫ X in partitionEvent n c (θstar j) s A, F X
            ∂(Measure.pi (fun _ : Fin n => mixtureLaw p θstar g))) ≤
          ∫⁻ X in partitionEvent n c (θstar j) s A,
            (∏ h : Fin s, G h (fun i => X i.1))
            ∂(Measure.pi (fun _ : Fin n => mixtureLaw p θstar g)) := by
        have hpt : ∀ X : Fin n → ℝ,
            ENNReal.ofReal (F X) ≤ ∏ h : Fin s, G h (fun i => X i.1) := by
          have key : ∀ f : ℝ → ℝ, (∀ θ, 0 ≤ f θ) →
              ENNReal.ofReal (∫ θ : ℝ, f θ ∂volume)
                ≤ ∫⁻ θ : ℝ, ENNReal.ofReal (f θ) ∂volume := by
            intro f hf
            by_cases hint : Integrable f volume
            · rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hf)]
            · rw [MeasureTheory.integral_undef hint]
              simp
          intro X
          have hfac : ∀ h : Fin s, ENNReal.ofReal
              (∫ θ : ℝ,
                ((A h).prod (fun i => g (X i - θ) / g (X i - θstar j))) * q0 θ ∂volume)
              ≤ G h (fun i => X i.1) := by
            intro h
            have hnn : ∀ θ : ℝ,
                0 ≤ ((A h).prod (fun i => g (X i - θ) / g (X i - θstar j))) * q0 θ :=
              fun θ => mul_nonneg
                (Finset.prod_nonneg (fun i _ => div_nonneg (hg_nonneg _) (hg_nonneg _)))
                (hq0_nonneg θ)
            refine le_trans (key _ hnn) (le_of_eq ?_)
            rw [hGdef]
            refine lintegral_congr (fun θ => ?_)
            rw [ENNReal.ofReal_mul (Finset.prod_nonneg
              (fun i _ => div_nonneg (hg_nonneg _) (hg_nonneg _)))]
            congr 1
            rw [ENNReal.ofReal_prod_of_nonneg
              (fun i _ => div_nonneg (hg_nonneg _) (hg_nonneg _))]
            have hatt := Finset.prod_attach (s := A h)
              (f := fun i : Fin n => ENNReal.ofReal (g (X i - θ) / g (X i - θstar j)))
            rw [Finset.univ_eq_attach (A h)]
            exact hatt.symm
          simp only [hFdef]
          rw [ENNReal.ofReal_prod_of_nonneg (fun h _ => MeasureTheory.integral_nonneg (fun θ =>
            mul_nonneg
              (Finset.prod_nonneg (fun i _ => div_nonneg (hg_nonneg _) (hg_nonneg _)))
              (hq0_nonneg θ)))]
          exact Finset.prod_le_prod (fun h _ => zero_le _) (fun h _ => hfac h)
        have hin : ENNReal.ofReal
            (∫ X in partitionEvent n c (θstar j) s A, F X
              ∂(Measure.pi (fun _ : Fin n => mixtureLaw p θstar g)))
            ≤ ∫⁻ X in partitionEvent n c (θstar j) s A, ENNReal.ofReal (F X)
              ∂(Measure.pi (fun _ : Fin n => mixtureLaw p θstar g)) := by
          have hFnn : ∀ X : Fin n → ℝ, 0 ≤ F X := by
            intro X
            simp only [hFdef]
            exact Finset.prod_nonneg (fun h _ => MeasureTheory.integral_nonneg (fun θ =>
              mul_nonneg
                (Finset.prod_nonneg (fun i _ => div_nonneg (hg_nonneg _) (hg_nonneg _)))
                (hq0_nonneg θ)))
          by_cases hint : Integrable F
              ((Measure.pi (fun _ : Fin n => mixtureLaw p θstar g)).restrict
                (partitionEvent n c (θstar j) s A))
          · rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hFnn)]
          · rw [MeasureTheory.integral_undef hint]
            simp
        refine hin.trans ?_
        exact MeasureTheory.lintegral_mono (fun X => hpt X)
      have hρW : ∀ x ∈ Set.Icc (θstar j - c) (θstar j + c),
          (∑ l : Fin t, p l * g (x - θstar l)) = p j * g (x - θstar j) := by
        intro x hx
        refine Finset.sum_eq_single j (fun l _ hl => ?_) (fun hc' => absurd (Finset.mem_univ j) hc')
        rw [hsep j l hl x hx, mul_zero]
      have hρ_meas : Measurable fun x : ℝ => ∑ l : Fin t, p l * g (x - θstar l) :=
        Finset.measurable_sum _
          (fun l _ => (hg_meas.comp (measurable_id.sub measurable_const)).const_mul (p l))
      have hdens : ∀ θ : ℝ, (∫⁻ x in Set.Icc (θstar j - c) (θstar j + c),
            ENNReal.ofReal (g (x - θ) / g (x - θstar j)) ∂(mixtureLaw p θstar g))
          = ∫⁻ x in Set.Icc (θstar j - c) (θstar j + c),
              ENNReal.ofReal (p j * g (x - θ)) ∂volume := by
        intro θ
        have hstep := MeasureTheory.setLIntegral_withDensity_eq_setLIntegral_mul (μ := volume)
          (f := fun x : ℝ => ENNReal.ofReal (∑ l : Fin t, p l * g (x - θstar l)))
          (g := fun x : ℝ => ENNReal.ofReal (g (x - θ) / g (x - θstar j)))
          (s := Set.Icc (θstar j - c) (θstar j + c))
          hρ_meas.ennreal_ofReal
          (((hg_meas.comp (measurable_id.sub measurable_const)).div
            (hg_meas.comp (measurable_id.sub measurable_const))).ennreal_ofReal) measurableSet_Icc
        simp only [mixtureLaw]
        refine hstep.trans ?_
        simp only [Pi.mul_apply]
        have hpt : ∀ x ∈ Set.Icc (θstar j - c) (θstar j + c),
            ENNReal.ofReal (∑ l : Fin t, p l * g (x - θstar l))
              * ENNReal.ofReal (g (x - θ) / g (x - θstar j))
            = ENNReal.ofReal (p j * g (x - θ)) := by
          intro x hx
          have hden : 0 < g (x - θstar j) := by
            refine hg_pos (x - θstar j) ?_
            constructor <;> linarith [hx.1, hx.2]
          have hρnn : 0 ≤ ∑ l : Fin t, p l * g (x - θstar l) := by
            rw [hρW x hx]
            exact mul_nonneg (le_of_lt (hp_pos j)) (hg_nonneg _)
          rw [← ENNReal.ofReal_mul hρnn, hρW x hx]
          congr 1
          have hden' : g (x - θstar j) ≠ 0 := ne_of_gt hden
          field_simp
        refine le_antisymm ?_ ?_
        · refine MeasureTheory.setLIntegral_mono' measurableSet_Icc (fun x hx => ?_)
          exact le_of_eq (hpt x hx)
        · refine MeasureTheory.setLIntegral_mono' measurableSet_Icc (fun x hx => ?_)
          exact le_of_eq (hpt x hx).symm
      have hblk : ∀ h : Fin s,
          (∫⁻ y in Set.univ.pi (fun _ : {i : Fin n // i ∈ A h} =>
              Set.Icc (θstar j - c) (θstar j + c)), G h y
            ∂(Measure.pi (fun _ : {i : Fin n // i ∈ A h} => mixtureLaw p θstar g)))
          ≤ ENNReal.ofReal (U / (m * (((A h).card : ℝ) + 1))) := by
        intro h
        have ha : 1 ≤ Fintype.card {i : Fin n // i ∈ A h} := by
          rw [Fintype.card_coe]
          exact Finset.card_pos.mpr (hne h)
        have hset : Set.univ.pi (fun _ : {i : Fin n // i ∈ A h} =>
            Set.Icc (θstar j - c) (θstar j + c))
            = {y : {i : Fin n // i ∈ A h} → ℝ |
                ∀ i, y i ∈ Set.Icc (θstar j - c) (θstar j + c)} := by
          ext y
          show (∀ i ∈ (Set.univ : Set {i : Fin n // i ∈ A h}),
              y i ∈ Set.Icc (θstar j - c) (θstar j + c)) ↔
            (∀ i, y i ∈ Set.Icc (θstar j - c) (θstar j + c))
          exact ⟨fun h i => h i (Set.mem_univ i), fun h i _ => h i⟩
        have hton := statopia_math_node_3299224973_260511eb c (θstar j) hc
          (mixtureLaw p θstar g) g q0 hg_meas hq0_meas hg_nonneg hq0_nonneg hg_pos
          {i : Fin n // i ∈ A h} ha
        have hK : ∀ θ : ℝ, (∫⁻ x in Set.Icc (θstar j - c) (θstar j + c),
              ENNReal.ofReal (g (x - θ)) ∂volume)
            = ENNReal.ofReal (∫ x in (θstar j - c)..(θstar j + c), g (x - θ)) := by
          intro θ
          have hle : θstar j - c ≤ θstar j + c := by linarith
          have hae : (Set.Icc (θstar j - c) (θstar j + c) : Set ℝ)
              =ᶠ[ae (volume : Measure ℝ)] Set.Ioc (θstar j - c) (θstar j + c) := by
            filter_upwards [show ∀ᵐ x : ℝ ∂(volume : Measure ℝ), x ≠ θstar j - c from by
              rw [MeasureTheory.ae_iff]
              simp] with x hx
            refine propext ⟨fun h => ?_, fun h => ?_⟩
            · exact ⟨lt_of_le_of_ne h.1 (Ne.symm hx), h.2⟩
            · exact ⟨le_of_lt h.1, h.2⟩
          have hInt : IntegrableOn (fun x : ℝ => g (x - θ))
              (Set.Ioc (θstar j - c) (θstar j + c)) volume := by
            haveI : IsFiniteMeasure
                (volume.restrict (Set.Ioc (θstar j - c) (θstar j + c))) :=
              ⟨by
                rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc]
                simp⟩
            have hM : 0 ≤ M := le_trans (le_of_lt hm_pos) hmM
            refine MeasureTheory.Integrable.of_bound ?_ M (Filter.Eventually.of_forall ?_)
            · exact (hg_meas.comp (measurable_id.sub measurable_const)).aestronglyMeasurable
            · intro x
              by_cases hx : x - θ ∈ Set.Icc (-c) c
              · rw [Real.norm_eq_abs, abs_of_nonneg (hg_nonneg _)]
                exact (hT1 (x - θ) hx).2
              · rw [hg_zero (x - θ) hx, Real.norm_eq_abs, abs_zero]
                exact hM
          calc (∫⁻ x in Set.Icc (θstar j - c) (θstar j + c),
                ENNReal.ofReal (g (x - θ)) ∂volume)
              = ∫⁻ x in Set.Ioc (θstar j - c) (θstar j + c),
                  ENNReal.ofReal (g (x - θ)) ∂volume :=
                MeasureTheory.setLIntegral_congr hae
            _ = ENNReal.ofReal (∫ x in Set.Ioc (θstar j - c) (θstar j + c),
                  g (x - θ) ∂volume) :=
                (ofReal_integral_eq_lintegral_ofReal hInt
                  (Filter.Eventually.of_forall (fun x => hg_nonneg (x - θ)))).symm
            _ = ENNReal.ofReal (∫ x in (θstar j - c)..(θstar j + c), g (x - θ)) := by
                rw [intervalIntegral.integral_of_le hle]
  
        have hI : (∫⁻ θ : ℝ, ((∫⁻ x in Set.Icc (θstar j - c) (θstar j + c),
              ENNReal.ofReal (g (x - θ) / g (x - θstar j)) ∂(mixtureLaw p θstar g))
                ^ (Fintype.card {i : Fin n // i ∈ A h})) * ENNReal.ofReal (q0 θ) ∂volume)
            ≤ ENNReal.ofReal (U / (m * (((A h).card : ℝ) + 1))) := by
          have hcard' : Fintype.card {i : Fin n // i ∈ A h} = (A h).card := Fintype.card_coe _
          rw [hcard']
          have ha' : 1 ≤ (A h).card := by
            rw [← hcard']
            exact ha
          have hJ_nonneg : ∀ θ : ℝ, 0 ≤ ∫ x in (θstar j - c)..(θstar j + c), g (x - θ) := by
            intro θ
            exact intervalIntegral.integral_nonneg (by linarith) (fun x _ => hg_nonneg _)
          have hpow : ∀ (n : ℕ) (x : ℝ), 0 ≤ x →
              (ENNReal.ofReal x) ^ n = ENNReal.ofReal (x ^ n) := by
            intro n
            induction n with
            | zero =>
                intro x _
                simp
            | succ k ih =>
                intro x hx
                rw [pow_succ, ih x hx, ← ENNReal.ofReal_mul (pow_nonneg hx k), pow_succ]
          have hA : ∀ θ : ℝ, (∫⁻ x in Set.Icc (θstar j - c) (θstar j + c),
                ENNReal.ofReal (g (x - θ) / g (x - θstar j)) ∂(mixtureLaw p θstar g))
              ≤ ENNReal.ofReal (∫ x in (θstar j - c)..(θstar j + c), g (x - θ)) := by
            intro θ
            rw [hdens θ]
            refine le_trans (MeasureTheory.setLIntegral_mono' measurableSet_Icc (fun x _ => ?_))
              (le_of_eq (hK θ))
            refine ENNReal.ofReal_le_ofReal ?_
            calc p j * g (x - θ) ≤ 1 * g (x - θ) :=
                  mul_le_mul_of_nonneg_right (le_of_lt (hp_lt j)) (hg_nonneg _)
              _ = g (x - θ) := one_mul _
          have hIle : ∀ θ : ℝ, (∫⁻ x in Set.Icc (θstar j - c) (θstar j + c),
                ENNReal.ofReal (g (x - θ) / g (x - θstar j)) ∂(mixtureLaw p θstar g))
                ^ ((A h).card)
              ≤ ENNReal.ofReal
                  ((∫ x in (θstar j - c)..(θstar j + c), g (x - θ)) ^ ((A h).card)) := by
            intro θ
            refine le_trans (pow_le_pow_left' (hA θ) _) (le_of_eq ?_)
            exact hpow ((A h).card) _ (hJ_nonneg θ)
          have hlint : Integrable (fun θ : ℝ =>
              (∫ x in (θstar j - c)..(θstar j + c), g (x - θ)) ^ ((A h).card) * q0 θ)
              volume := by
            have hmeasJ : Measurable fun θ : ℝ =>
                ∫⁻ x in Set.Icc (θstar j - c) (θstar j + c),
                  ENNReal.ofReal (g (x - θ)) ∂volume :=
              Measurable.lintegral_prod_right'
                (f := fun p : ℝ × ℝ => ENNReal.ofReal (g (p.2 - p.1)))
                ((hg_meas.comp (measurable_snd.sub measurable_fst)).ennreal_ofReal)
            have hmeasJ' : Measurable fun θ : ℝ =>
                ∫ x in (θstar j - c)..(θstar j + c), g (x - θ) := by
              have heq : (fun θ : ℝ => ∫ x in (θstar j - c)..(θstar j + c), g (x - θ))
                  = fun θ => (∫⁻ x in Set.Icc (θstar j - c) (θstar j + c),
                      ENNReal.ofReal (g (x - θ)) ∂volume).toReal := by
                funext θ
                rw [hK θ, ENNReal.toReal_ofReal (hJ_nonneg θ)]
              rw [heq]
              exact hmeasJ.ennreal_toReal
            have hJle1 : ∀ θ : ℝ, ∫ x in (θstar j - c)..(θstar j + c), g (x - θ) ≤ 1 := by
              intro θ
              have h1 : ∫⁻ x in Set.Icc (θstar j - c) (θstar j + c),
                  ENNReal.ofReal (g (x - θ)) ∂volume ≤ 1 := by
                calc ∫⁻ x in Set.Icc (θstar j - c) (θstar j + c),
                      ENNReal.ofReal (g (x - θ)) ∂volume
                    ≤ ∫⁻ x : ℝ, ENNReal.ofReal (g (x - θ)) ∂volume :=
                      MeasureTheory.setLIntegral_le_lintegral _ _
                  _ = ∫⁻ x : ℝ, ENNReal.ofReal (g x) ∂volume := htrans θ
                  _ = 1 := hg_lintegral
              calc ∫ x in (θstar j - c)..(θstar j + c), g (x - θ)
                  = (∫⁻ x in Set.Icc (θstar j - c) (θstar j + c),
                      ENNReal.ofReal (g (x - θ)) ∂volume).toReal := by
                    rw [hK θ, ENNReal.toReal_ofReal (hJ_nonneg θ)]
                _ ≤ (1 : ℝ≥0∞).toReal := ENNReal.toReal_mono (by simp) h1
                _ = 1 := by simp
            have hmeasPow : ∀ k : ℕ, Measurable fun θ : ℝ =>
                (∫ x in (θstar j - c)..(θstar j + c), g (x - θ)) ^ k := by
              intro k
              induction k with
              | zero =>
                  simpa using (measurable_const : Measurable fun _ : ℝ => (1 : ℝ))
              | succ n ih =>
                  simpa [pow_succ] using ih.mul hmeasJ'
            have hbdd : ∀ θ : ℝ,
                ‖(∫ x in (θstar j - c)..(θstar j + c), g (x - θ)) ^ ((A h).card)‖ ≤ 1 := by
              intro θ
              rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hJ_nonneg θ) _)]
              exact pow_le_one₀ (hJ_nonneg θ) (hJle1 θ)
            exact hq0_int.bdd_mul ((hmeasPow ((A h).card)).aestronglyMeasurable)
              (Filter.Eventually.of_forall hbdd)
          have hFinal : (∫⁻ θ : ℝ, ENNReal.ofReal
                ((∫ x in (θstar j - c)..(θstar j + c), g (x - θ)) ^ ((A h).card))
                * ENNReal.ofReal (q0 θ) ∂volume)
              = ENNReal.ofReal (∫ θ : ℝ,
                  (∫ x in (θstar j - c)..(θstar j + c), g (x - θ)) ^ ((A h).card)
                    * q0 θ ∂volume) := by
            rw [ofReal_integral_eq_lintegral_ofReal hlint
              (Filter.Eventually.of_forall (fun θ =>
                mul_nonneg (pow_nonneg (hJ_nonneg θ) _) (hq0_nonneg θ)))]
            refine lintegral_congr (fun θ => ?_)
            rw [ENNReal.ofReal_mul (pow_nonneg (hJ_nonneg θ) _)]
          have hscal := statopia_math_node_1939138294_723e8d32 g q0 c m U (θstar j) ((A h).card)
            hc hm_pos hU_pos ha' hg_meas hq0_meas hq0_int hg_nonneg hg_zero hg_mass
            (fun x hx => (hT1 x hx).1) hq0_nonneg (fun y hy => hT3 j y hy) hlint
          calc (∫⁻ θ : ℝ, ((∫⁻ x in Set.Icc (θstar j - c) (θstar j + c),
                  ENNReal.ofReal (g (x - θ) / g (x - θstar j)) ∂(mixtureLaw p θstar g))
                    ^ ((A h).card)) * ENNReal.ofReal (q0 θ) ∂volume)
              ≤ ∫⁻ θ : ℝ, ENNReal.ofReal
                  ((∫ x in (θstar j - c)..(θstar j + c), g (x - θ)) ^ ((A h).card))
                  * ENNReal.ofReal (q0 θ) ∂volume := by
                refine MeasureTheory.lintegral_mono (fun θ => ?_)
                exact mul_le_mul_right' (hIle θ) _
            _ = ENNReal.ofReal (∫ θ : ℝ,
                  (∫ x in (θstar j - c)..(θstar j + c), g (x - θ)) ^ ((A h).card)
                    * q0 θ ∂volume) :=
                hFinal
            _ ≤ ENNReal.ofReal (U / (m * (((A h).card : ℝ) + 1))) :=
                ENNReal.ofReal_le_ofReal hscal
        have hcard : Fintype.card {i : Fin n // i ∈ A h} = (A h).card := Fintype.card_coe _
        rw [hcard] at hI hton
        rw [hset]
        simp only [hGdef]
        rw [hton]
        exact hI
      have hB : (∏ h : Fin s, ENNReal.ofReal (U / (m * (((A h).card : ℝ) + 1))))
          = ENNReal.ofReal B := by
        rw [hBdef]
        refine (ENNReal.ofReal_prod_of_nonneg ?_).symm
        intro h _
        have hb : (0 : ℝ) < ((A h).card : ℝ) + 1 := by positivity
        exact le_of_lt (div_pos hU_pos (mul_pos hm_pos hb))
      have hprod : (∏ h : Fin s,
            ∫⁻ y in Set.univ.pi (fun _ : {i : Fin n // i ∈ A h} =>
              Set.Icc (θstar j - c) (θstar j + c)), G h y
            ∂(Measure.pi (fun _ : {i : Fin n // i ∈ A h} => mixtureLaw p θstar g)))
          ≤ ∏ h : Fin s, ENNReal.ofReal (U / (m * (((A h).card : ℝ) + 1))) :=
        Finset.prod_le_prod (fun h _ => zero_le _) (fun h _ => hblk h)
      exact (hstep1.trans hbox).trans (hprod.trans (le_of_eq hB))
    have hreal : (∫ X in partitionEvent n c (θstar j) s A, F X
        ∂(Measure.pi (fun _ : Fin n => mixtureLaw p θstar g))) ≤ B :=
      (ENNReal.ofReal_le_ofReal_iff hBpos).mp hmain
    rw [harith] at hreal
    exact hreal
  /- @proof-region region.root.f3acf0edd9e0 end -/

end Statlib.Imported

-- Paper root revision 9dda842e-4d20-43b2-b6ad-387283ef74d5
