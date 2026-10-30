import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q12.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q12.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q12.ProvedNodes.Node_886141048_bc639600_8d1e83e5
open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_612610791_f42c035b : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X P)
    (B : ℝ) (hB : 0 ≤ B)
    (G : (Fin n → ℝ) → ℝ) (hG_meas : Measurable G)
    (hG_bound : ∀ u : Fin n → ℝ, |G u| ≤ B)
    (k : Fin n),
    let F : Fin (n + 1) → MeasurableSpace Ω :=
      fun j => ⨆ i : Fin n, ⨆ (_ : i.val < j.val), MeasurableSpace.comap (X i) inferInstance
    let Y : Ω → ℝ := fun ω => G (fun i => X i ω)
    let Z : Type := {i : Fin n // k.val < i.val}
    let νZ : Measure (Z → ℝ) := Measure.pi (fun i : Z => P.map (X (i : Fin n)))
    let Afun : Ω → ℝ → ℝ := fun ω y =>
      ∫ w : Z → ℝ,
        G (fun i : Fin n =>
          if h : k.val < i.val then w ⟨i, h⟩ else if i = k then y else X i ω) ∂νZ
    let μk : Measure ℝ := P.map (X k)
    MeasureTheory.condExp (F k.castSucc) P Y =ᵐ[P] fun ω => ∫ y : ℝ, Afun ω y ∂μk := by
  /- @proof-region region.target-node.session.dd095008f7fd813d begin -/
  classical
  intro Ω mΩ P hP n X hX_meas hX_indep B hB G hG_meas hG_bound k
  dsimp only
  let Pr : Type := {j : Fin n // j.val < k.val}
  let Zt : Type := {i : Fin n // k.val < i.val}
  let μ : Fin n → Measure ℝ := fun i => Measure.map (X i) P
  let μk : Measure ℝ := μ k
  let νZ : Measure (Zt → ℝ) := Measure.pi (fun i : Zt => μ ↑i)
  let u : Ω → (Pr → ℝ) := fun ω j => X ↑j ω
  let Y : Ω → ℝ := fun ω => G fun i => X i ω
  let g : Ω → ℝ := fun ω => ∫ y : ℝ, (∫ w : Zt → ℝ,
    G (fun i : Fin n => if h : k.val < i.val then w ⟨i, h⟩ else if i = k then y else X i ω)
    ∂νZ) ∂μk
  have hfull : Measure.map (fun ω i => X i ω) P = Measure.pi μ := by
    have h := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map (f := X) (μ := P)
      (fun i => (hX_meas i).aemeasurable)).mp hX_indep
    exact h
  obtain ⟨Fm, hFmdef⟩ : ∃ Fm : MeasurableSpace Ω,
      Fm = ⨆ i : Fin n, ⨆ (_ : i.val < k.castSucc.val),
        MeasurableSpace.comap (X i) inferInstance := ⟨_, rfl⟩
  rw [← hFmdef]
  have hmain : MeasureTheory.condExp Fm P Y =ᵐ[P] g := by
    letI hinstΩ : MeasurableSpace Ω := mΩ
    haveI hprob : ∀ i : Fin n, IsProbabilityMeasure (μ i) := fun i =>
      Measure.isProbabilityMeasure_map (hX_meas i).aemeasurable
    haveI hνZp : IsProbabilityMeasure νZ := Measure.pi.instIsProbabilityMeasure (fun i : Zt => μ ↑i)
    have hmle : Fm ≤ mΩ := by
      rw [hFmdef]
      refine iSup_le fun i => iSup_le fun _ => ?_
      exact (hX_meas i).comap_le
    have hFm_le : Fm ≤ MeasurableSpace.comap u inferInstance := by
      rw [hFmdef]
      refine iSup_le fun i => iSup_le fun hi => ?_
      have htt : Measurable[MeasurableSpace.comap u inferInstance] u :=
        Measurable.of_comap_le le_rfl
      have happ : Measurable (fun p : Pr → ℝ => p ⟨i, hi⟩) := measurable_pi_apply _
      have h2 : Measurable[MeasurableSpace.comap u inferInstance]
          ((fun p : Pr → ℝ => p ⟨i, hi⟩) ∘ u) := happ.comp htt
      rw [show ((fun p : Pr → ℝ => p ⟨i, hi⟩) ∘ u) = X i from funext fun x => rfl] at h2
      exact h2.comap_le
    let recon : (Pr → ℝ) → ℝ → (Zt → ℝ) → (Fin n → ℝ) := fun p y w i =>
      if h : k.val < i.val then w ⟨i, h⟩
      else if h₂ : i = k then y
      else p ⟨i, lt_of_le_of_ne (not_lt.mp h) (fun hk => h₂ (Fin.ext hk))⟩
    let Φ : (Pr → ℝ) → ℝ := fun p => ∫ y : ℝ, (∫ w : Zt → ℝ, G (recon p y w) ∂νZ) ∂μk
    have hfull_meas : Measurable (fun ω i => X i ω) := measurable_pi_iff.mpr fun i => hX_meas i
    have hu_amb : Measurable u := by
      refine measurable_pi_iff.mpr fun j => ?_
      rw [show (fun x => u x j) = X ↑j from funext fun x => rfl]
      exact hX_meas ↑j
    have hdite : ∀ (p : Prop) [Decidable p] (a b : ℝ),
        dite p (fun _ => a) (fun _ => b) = ite p a b := by
      intro p _ a b
      by_cases h : p <;> simp [h]
    have hg_eq : ∀ ω, g ω = Φ (u ω) := by
      intro ω
      simp only [g, Φ, recon, u, hdite]
    have hrecon_meas : Measurable (fun z : ((Pr → ℝ) × ℝ) × (Zt → ℝ) => recon z.1.1 z.1.2 z.2) := by
      refine measurable_pi_iff.mpr fun i => ?_
      by_cases hi : k.val < i.val
      · simp only [recon, dif_pos hi]
        exact (measurable_pi_apply (δ := Zt) (X := fun _ => ℝ) (⟨i, hi⟩ : Zt)).comp measurable_snd
      · by_cases hik : i = k
        · simp only [recon, dif_neg hi, dif_pos hik]
          exact measurable_snd.comp measurable_fst
        · simp only [recon, dif_neg hi, dif_neg hik]
          exact (measurable_pi_apply (δ := Pr) (X := fun _ => ℝ)
            (⟨i, lt_of_le_of_ne (not_lt.mp hi) (fun hk => hik (Fin.ext hk))⟩ : Pr)).comp
            (measurable_fst.comp measurable_fst)
    have hΦ_sm : StronglyMeasurable Φ := by
      have hm1 : Measurable (fun z : ((Pr → ℝ) × ℝ) × (Zt → ℝ) => G (recon z.1.1 z.1.2 z.2)) :=
        hG_meas.comp hrecon_meas
      have hs1 : StronglyMeasurable (fun z : ((Pr → ℝ) × ℝ) × (Zt → ℝ) => G (recon z.1.1 z.1.2 z.2)) :=
        hm1.stronglyMeasurable
      have h2 : StronglyMeasurable (fun z : (Pr → ℝ) × ℝ => ∫ w : Zt → ℝ, G (recon z.1 z.2 w) ∂νZ) :=
        MeasureTheory.StronglyMeasurable.integral_prod_right
          (f := fun (z : (Pr → ℝ) × ℝ) (w : Zt → ℝ) => G (recon z.1 z.2 w))
          (by simpa [Function.uncurry] using hs1)
      exact MeasureTheory.StronglyMeasurable.integral_prod_right
        (f := fun (p : Pr → ℝ) (y : ℝ) => ∫ w : Zt → ℝ, G (recon p y w) ∂νZ)
        (by simpa [Function.uncurry] using h2)
    have hinner : ∀ p : Pr → ℝ, ∀ y : ℝ, |∫ w : Zt → ℝ, G (recon p y w) ∂νZ| ≤ B := by
      intro p y
      have h := MeasureTheory.norm_integral_le_of_norm_le_const (μ := νZ)
        (f := fun w : Zt → ℝ => G (recon p y w)) (C := B) ?_
      · rw [show νZ.real Set.univ = 1 from by simp, mul_one] at h
        simpa [Real.norm_eq_abs] using h
      · filter_upwards with w
        simpa [Real.norm_eq_abs] using hG_bound (recon p y w)
    have hΦ_bd : ∀ p : Pr → ℝ, |Φ p| ≤ B := by
      intro p
      have h := MeasureTheory.norm_integral_le_of_norm_le_const (μ := μk)
        (f := fun y : ℝ => ∫ w : Zt → ℝ, G (recon p y w) ∂νZ) (C := B) ?_
      · rw [show μk.real Set.univ = 1 from by simp, mul_one] at h
        simpa [Φ, Real.norm_eq_abs] using h
      · filter_upwards with y
        simpa [Real.norm_eq_abs] using hinner p y
    have hYint : Integrable Y P := by
      refine MeasureTheory.Integrable.of_bound (hG_meas.comp hfull_meas).aestronglyMeasurable B ?_
      filter_upwards with ω
      simpa [Real.norm_eq_abs, Y] using hG_bound (fun i => X i ω)
    have hgint : Integrable g P := by
      have hgm : Measurable g := hΦ_sm.measurable.comp hu_amb
      refine MeasureTheory.Integrable.of_bound hgm.aestronglyMeasurable B ?_
      filter_upwards with ω
      rw [hg_eq ω]
      simpa [Real.norm_eq_abs] using hΦ_bd (u ω)
    have hgm : Measurable g := hΦ_sm.measurable.comp hu_amb
    have hkey : ∀ s : Set Ω, MeasurableSet[Fm] s → P s < ⊤ →
        ∫ ω in s, g ω ∂P = ∫ ω in s, Y ω ∂P := by
      intro s hs _
      let full : Ω → (Fin n → ℝ) := fun ω i => X i ω
      let perm : (Fin n → ℝ) → (Pr → ℝ) := fun x j => x ↑j
      have hs' : MeasurableSet[MeasurableSpace.comap u inferInstance] s :=
        MeasurableSpace.le_def.mp hFm_le s hs
      obtain ⟨S, hS, hSe⟩ :=
        (MeasurableSpace.measurableSet_comap (s := s) (f := u)
          (m := (inferInstance : MeasurableSpace (Pr → ℝ)))).mp hs'
      rw [← hSe]
      let T : Set (Fin n → ℝ) := perm ⁻¹' S
      have hperm_meas : Measurable perm := by
        refine measurable_pi_iff.mpr fun j => ?_
        rw [show (fun x : Fin n → ℝ => perm x j) = (fun x : Fin n → ℝ => x (↑j)) from
          funext fun x => rfl]
        exact measurable_pi_apply (δ := Fin n) (X := fun _ : Fin n => ℝ) (↑j : Fin n)
      have hT_meas : MeasurableSet T := hS.preimage hperm_meas
      have hside : ∀ (H : (Fin n → ℝ) → ℝ), Measurable H →
          ∫ ω in u ⁻¹' S, H (full ω) ∂P = ∫ x, T.indicator H x ∂(Measure.pi μ) := by
        intro H hH
        have h1 : ∫ ω in u ⁻¹' S, H (full ω) ∂P
            = ∫ x in T, H x ∂(Measure.map full P) := by
          rw [show u ⁻¹' S = full ⁻¹' T from rfl]
          rw [MeasureTheory.Measure.restrict_map hfull_meas hT_meas,
            MeasureTheory.integral_map hfull_meas.aemeasurable hH.aestronglyMeasurable]
        rw [h1, hfull, ← MeasureTheory.integral_indicator hT_meas]
      have hperm_recon : ∀ (p : Pr → ℝ) (y : ℝ) (w : Zt → ℝ), perm (recon p y w) = p := by
        intro p y w
        funext j
        have h1 : ¬ (k.val < (↑j : Fin n).val) := not_lt.mpr (le_of_lt j.2)
        have h2 : ¬ ((↑j : Fin n) = k) := fun h => ne_of_lt j.2 (congrArg Fin.val h)
        simp only [perm, recon, dif_neg h1, dif_neg h2]
        exact congrArg p (Subtype.ext rfl)
      have hF1_meas : Measurable (T.indicator G) := hG_meas.indicator hT_meas
      have hF2_meas : Measurable (T.indicator (fun x => Φ (perm x))) :=
        (hΦ_sm.measurable.comp hperm_meas).indicator hT_meas
      have hF1_bd : ∀ x : Fin n → ℝ, |(T.indicator G) x| ≤ B := by
        intro x
        have hx' : (T.indicator G) x = if x ∈ T then G x else 0 := rfl
        rw [hx']
        by_cases hx : x ∈ T
        · rw [if_pos hx]; exact hG_bound x
        · rw [if_neg hx]; simpa using hB
      have hF2_bd : ∀ x : Fin n → ℝ, |(T.indicator (fun x => Φ (perm x))) x| ≤ B := by
        intro x
        have hx' : (T.indicator (fun x => Φ (perm x))) x
            = if x ∈ T then Φ (perm x) else 0 := rfl
        rw [hx']
        by_cases hx : x ∈ T
        · rw [if_pos hx]; exact hΦ_bd (perm x)
        · rw [if_neg hx]; simpa using hB
      have hev1 : ∀ (p : Pr → ℝ) (y : ℝ) (w : Zt → ℝ),
          (T.indicator G) (recon p y w) = if p ∈ S then G (recon p y w) else 0 := by
        intro p y w
        have hiff : (recon p y w) ∈ T ↔ p ∈ S := by
          show perm (recon p y w) ∈ S ↔ p ∈ S
          rw [hperm_recon p y w]
        rw [show (T.indicator G) (recon p y w)
            = if (recon p y w) ∈ T then G (recon p y w) else 0 from rfl]
        by_cases hp : p ∈ S
        · rw [if_pos hp, if_pos (hiff.mpr hp)]
        · rw [if_neg hp, if_neg (fun hc => hp (hiff.mp hc))]
      have hev2 : ∀ (p : Pr → ℝ) (y : ℝ) (w : Zt → ℝ),
          (T.indicator (fun x => Φ (perm x))) (recon p y w) = if p ∈ S then Φ p else 0 := by
        intro p y w
        have hiff : (recon p y w) ∈ T ↔ p ∈ S := by
          show perm (recon p y w) ∈ S ↔ p ∈ S
          rw [hperm_recon p y w]
        rw [show (T.indicator (fun x => Φ (perm x))) (recon p y w)
            = if (recon p y w) ∈ T then Φ (perm (recon p y w)) else 0 from rfl]
        by_cases hp : p ∈ S
        · rw [if_pos hp, if_pos (hiff.mpr hp), hperm_recon p y w]
        · rw [if_neg hp, if_neg (fun hc => hp (hiff.mp hc))]
      have hc1 := statopia_math_node_886141048_bc639600 n k μ B (T.indicator G) hF1_meas hF1_bd
      have hc2 := statopia_math_node_886141048_bc639600 n k μ B
        (T.indicator (fun x => Φ (perm x))) hF2_meas hF2_bd
      have hg_eq2 : ∀ ω, g ω = Φ (perm (full ω)) := by
        intro ω
        rw [hg_eq ω]
      have hs1 : ∫ ω in u ⁻¹' S, Y ω ∂P
          = ∫ p, ∫ y, ∫ w, (if p ∈ S then G (recon p y w) else 0) ∂νZ ∂μk ∂
              (Measure.pi (fun j : Pr => μ ↑j)) := by
        rw [show (∫ ω in u ⁻¹' S, Y ω ∂P)
            = ∫ x, T.indicator G x ∂(Measure.pi μ) from hside G hG_meas]
        rw [hc1]
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p =>
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y =>
            MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => hev1 p y w)))
      have hs2 : ∫ ω in u ⁻¹' S, Φ (u ω) ∂P
          = ∫ p, ∫ y, ∫ w, (if p ∈ S then Φ p else 0) ∂νZ ∂μk ∂
              (Measure.pi (fun j : Pr => μ ↑j)) := by
        rw [show (∫ ω in u ⁻¹' S, Φ (u ω) ∂P)
            = ∫ x, T.indicator (fun x => Φ (perm x)) x ∂(Measure.pi μ) from
          hside (fun x => Φ (perm x)) (hΦ_sm.measurable.comp hperm_meas)]
        rw [hc2]
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p =>
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y =>
            MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => hev2 p y w)))
      have hmid : ∀ p : Pr → ℝ,
          (∫ y, ∫ w, (if p ∈ S then Φ p else 0) ∂νZ ∂μk)
            = ∫ y, ∫ w, (if p ∈ S then G (recon p y w) else 0) ∂νZ ∂μk := by
        intro p
        by_cases hp : p ∈ S
        · simp only [if_pos hp]
          have h1 : (∫ w : Zt → ℝ, Φ p ∂νZ) = Φ p := by
            rw [MeasureTheory.integral_const, show νZ.real Set.univ = 1 from by simp, one_smul]
          have h2 : (∫ y : ℝ, Φ p ∂μk) = Φ p := by
            rw [MeasureTheory.integral_const, show μk.real Set.univ = 1 from by simp, one_smul]
          rw [h1, h2]
        · simp only [if_neg hp]
      refine hs2.trans ?_
      rw [show (∫ p, ∫ y, ∫ w, (if p ∈ S then Φ p else 0) ∂νZ ∂μk ∂
              (Measure.pi (fun j : Pr => μ ↑j)))
          = ∫ p, ∫ y, ∫ w, (if p ∈ S then G (recon p y w) else 0) ∂νZ ∂μk ∂
              (Measure.pi (fun j : Pr => μ ↑j)) from
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hmid)]
      exact hs1.symm
    have hu_Fm : @Measurable Ω (Pr → ℝ) Fm _ u := by
      letI : MeasurableSpace Ω := Fm
      exact measurable_pi_iff.mpr fun j => by
        rw [show (fun ω => u ω j) = X ↑j from funext fun ω => rfl]
        refine Measurable.of_comap_le ?_
        rw [hFmdef]
        exact le_iSup_of_le ↑j (le_iSup_of_le j.2 le_rfl)
    have hg_aesm := Measurable.aestronglyMeasurable (m := Fm) (m₀ := mΩ) (μ := P)
      (f := fun ω => Φ (u ω)) (hΦ_sm.measurable.comp hu_Fm)
    have hgint2 : Integrable (fun ω => Φ (u ω)) P := by
      refine MeasureTheory.Integrable.of_bound (hΦ_sm.measurable.comp hu_amb).aestronglyMeasurable B ?_
      filter_upwards with ω
      simpa [Real.norm_eq_abs] using hΦ_bd (u ω)
    have hres : MeasureTheory.condExp Fm P Y =ᵐ[P] (fun ω => Φ (u ω)) := by
      refine (MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hmle hYint ?_ ?_ hg_aesm).symm
      · intro s hs hsf
        exact hgint2.integrableOn
      · intro s hs hsf
        exact hkey s hs hsf
    rw [show (fun ω => Φ (u ω)) = g from funext fun ω => (hg_eq ω).symm] at hres
    exact hres
  exact hmain
  /- @proof-region region.target-node.session.dd095008f7fd813d end -/
