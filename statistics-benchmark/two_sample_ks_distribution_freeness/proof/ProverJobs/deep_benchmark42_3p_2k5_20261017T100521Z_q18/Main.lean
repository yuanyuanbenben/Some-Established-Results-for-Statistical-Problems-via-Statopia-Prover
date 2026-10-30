import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q18.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q18.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q18.Base

open MeasureTheory ProbabilityTheory Filter

theorem two_sample_ks_distribution_freeness
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (F : StieltjesFunction ℝ)
    (hF_cont : Continuous F)
    (hF_strict : StrictMono F)
    (hF_bot : Tendsto F Filter.atBot (nhds 0))
    (hF_top : Tendsto F Filter.atTop (nhds 1))
    (X : Fin m → Ω → ℝ) (Y : Fin n → Ω → ℝ)
    (U : Fin m → Ω → ℝ) (V : Fin n → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hY_meas : ∀ j, Measurable (Y j))
    (hU_meas : ∀ i, Measurable (U i))
    (hV_meas : ∀ j, Measurable (V j))
    (hX_indep : iIndepFun X P)
    (hY_indep : iIndepFun Y P)
    (hU_indep : iIndepFun U P)
    (hV_indep : iIndepFun V P)
    (hXY_indep : IndepFun
      (fun ω ↦ fun i ↦ X i ω) (fun ω ↦ fun j ↦ Y j ω) P)
    (hUV_indep : IndepFun
      (fun ω ↦ fun i ↦ U i ω) (fun ω ↦ fun j ↦ V j ω) P)
    (hXY_UV_indep : IndepFun
      (fun ω ↦ (fun i ↦ X i ω, fun j ↦ Y j ω))
      (fun ω ↦ (fun i ↦ U i ω, fun j ↦ V j ω)) P)
    (hX_cdf : ∀ i t, (P {ω | X i ω ≤ t}).toReal = F t)
    (hY_cdf : ∀ j t, (P {ω | Y j ω ≤ t}).toReal = F t)
    (hU_uniform : ∀ i, MeasureTheory.pdf.IsUniform (U i) (Set.Ioo 0 1) P)
    (hV_uniform : ∀ j, MeasureTheory.pdf.IsUniform (V j) (Set.Ioo 0 1) P) :
    let FX : Ω → ℝ → ℝ := fun ω t ↦
      (m : ℝ)⁻¹ * ∑ i, if X i ω ≤ t then 1 else 0
    let FY : Ω → ℝ → ℝ := fun ω t ↦
      (n : ℝ)⁻¹ * ∑ j, if Y j ω ≤ t then 1 else 0
    let FU : Ω → ℝ → ℝ := fun ω u ↦
      (m : ℝ)⁻¹ * ∑ i, if U i ω ≤ u then 1 else 0
    let FV : Ω → ℝ → ℝ := fun ω u ↦
      (n : ℝ)⁻¹ * ∑ j, if V j ω ≤ u then 1 else 0
    let DXY : Ω → ℝ := fun ω ↦ ⨆ t : ℝ, |FX ω t - FY ω t|
    let DUV : Ω → ℝ := fun ω ↦
      ⨆ u : Set.Icc (0 : ℝ) 1, |FU ω u.1 - FV ω u.1|
    IdentDistrib DXY DUV P P
:= by
  /- @proof-region region.root.38e9a2dba3ad begin -/
  classical
  dsimp only
  change IdentDistrib
    (fun ω => ⨆ t : ℝ, |(m : ℝ)⁻¹ * ∑ i : Fin m, (if X i ω ≤ t then (1 : ℝ) else 0) - (n : ℝ)⁻¹ * ∑ j : Fin n, (if Y j ω ≤ t then (1 : ℝ) else 0)|)
    (fun ω => ⨆ u : Set.Icc (0 : ℝ) 1, |(m : ℝ)⁻¹ * ∑ i : Fin m, (if U i ω ≤ u.1 then (1 : ℝ) else 0) - (n : ℝ)⁻¹ * ∑ j : Fin n, (if V j ω ≤ u.1 then (1 : ℝ) else 0)|)
    P P
  set DXY : Ω → ℝ := fun ω => ⨆ t : ℝ, |(m : ℝ)⁻¹ * ∑ i : Fin m, (if X i ω ≤ t then (1 : ℝ) else 0) - (n : ℝ)⁻¹ * ∑ j : Fin n, (if Y j ω ≤ t then (1 : ℝ) else 0)| with hDXY
  set DUV : Ω → ℝ := fun ω => ⨆ u : Set.Icc (0 : ℝ) 1, |(m : ℝ)⁻¹ * ∑ i : Fin m, (if U i ω ≤ u.1 then (1 : ℝ) else 0) - (n : ℝ)⁻¹ * ∑ j : Fin n, (if V j ω ≤ u.1 then (1 : ℝ) else 0)| with hDUV
  set Lam : Measure ℝ := (volume (Set.Ioo (0 : ℝ) 1))⁻¹ • volume.restrict (Set.Ioo (0 : ℝ) 1) with hLam
  set Mfun : (Fin m → ℝ) × (Fin n → ℝ) → ℝ := fun p =>
    max 0 (max
      ((Finset.univ : Finset (Fin m)).sup'
        ⟨⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hm⟩, Finset.mem_univ _⟩
        (fun i : Fin m =>
          |(m : ℝ)⁻¹ * ∑ k : Fin m, (if p.1 k ≤ p.1 i then (1 : ℝ) else 0) -
           (n : ℝ)⁻¹ * ∑ k : Fin n, (if p.2 k ≤ p.1 i then (1 : ℝ) else 0)|))
      ((Finset.univ : Finset (Fin n)).sup'
        ⟨⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩, Finset.mem_univ _⟩
        (fun j : Fin n =>
          |(m : ℝ)⁻¹ * ∑ k : Fin m, (if p.1 k ≤ p.2 j then (1 : ℝ) else 0) -
           (n : ℝ)⁻¹ * ∑ k : Fin n, (if p.2 k ≤ p.2 j then (1 : ℝ) else 0)|))) with hMfun
  set WF : Ω → (Fin m → ℝ) × (Fin n → ℝ) :=
    fun ω => (fun i : Fin m => ⇑F (X i ω), fun j : Fin n => ⇑F (Y j ω)) with hWF
  set WU : Ω → (Fin m → ℝ) × (Fin n → ℝ) :=
    fun ω => (fun i : Fin m => U i ω, fun j : Fin n => V j ω) with hWU
  have hF_meas : Measurable ⇑F := hF_cont.measurable
  have hM_meas : Measurable Mfun := by
    rw [hMfun]
    exact statopia_math_node_3990029311_22268063 m n hm hn
  have hvol : (volume (Set.Ioo (0 : ℝ) 1)) = 1 := by
    rw [Real.volume_Ioo]
    simp
  have hLameq : Lam = volume.restrict (Set.Ioo (0 : ℝ) 1) := by
    rw [hLam, hvol]
    simp
  have hLamuniv : Lam Set.univ = 1 := by
    rw [hLameq, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, hvol]
  haveI : IsProbabilityMeasure Lam := ⟨hLamuniv⟩
  have hbridge : ∀ (d1 : Fin m → ℝ) (d2 : Fin n → ℝ)
      (p : (Finset.univ : Finset (Fin m)).Nonempty)
      (q : (Finset.univ : Finset (Fin n)).Nonempty),
      sSup (Set.insert (0 : ℝ) (Set.range d1 ∪ Set.range d2)) =
        max 0 (max ((Finset.univ : Finset (Fin m)).sup' p d1)
          ((Finset.univ : Finset (Fin n)).sup' q d2)) := by
    intro d1 d2 p q
    set T : Set ℝ := Set.insert (0 : ℝ) (Set.range d1 ∪ Set.range d2) with hT
    have hbd : BddAbove T := by
      rw [hT]
      exact (((Set.finite_range d1).union (Set.finite_range d2)).insert 0).bddAbove
    have h0 : (0 : ℝ) ∈ T := by
      rw [hT]
      exact Set.mem_insert_iff.2 (Or.inl rfl)
    have hm1 : ∀ i : Fin m, d1 i ∈ T := by
      intro i
      rw [hT]
      exact Set.mem_insert_iff.2 (Or.inr (Set.mem_union_left _ (Set.mem_range_self i)))
    have hm2 : ∀ j : Fin n, d2 j ∈ T := by
      intro j
      rw [hT]
      exact Set.mem_insert_iff.2 (Or.inr (Set.mem_union_right _ (Set.mem_range_self j)))
    have hgoal : sSup T = max 0 (max ((Finset.univ : Finset (Fin m)).sup' p d1)
        ((Finset.univ : Finset (Fin n)).sup' q d2)) := by
      refine le_antisymm ?_ ?_
      · refine csSup_le ⟨0, h0⟩ ?_
        intro x hx
        have hx' : x = 0 ∨ x ∈ Set.range d1 ∪ Set.range d2 := by
          simpa only [hT, Set.mem_insert_iff] using hx
        rcases hx' with rfl | hx'
        · exact le_max_left _ _
        · have hx'' : x ∈ Set.range d1 ∨ x ∈ Set.range d2 := by
            simpa only [Set.mem_union] using hx'
          rcases hx'' with hx'' | hx''
          · obtain ⟨i, rfl⟩ : ∃ i : Fin m, d1 i = x := by simpa using hx''
            exact le_trans ((Finset.le_sup'_iff p).2 ⟨i, Finset.mem_univ i, le_rfl⟩)
              (le_trans (le_max_left _ _) (le_max_right _ _))
          · obtain ⟨j, rfl⟩ : ∃ j : Fin n, d2 j = x := by simpa using hx''
            exact le_trans ((Finset.le_sup'_iff q).2 ⟨j, Finset.mem_univ j, le_rfl⟩)
              (le_trans (le_max_right _ _) (le_max_right _ _))
      · refine max_le (le_csSup hbd h0) (max_le ?_ ?_)
        · exact (Finset.sup'_le_iff p d1).2 (fun i _ => le_csSup hbd (hm1 i))
        · exact (Finset.sup'_le_iff q d2).2 (fun j _ => le_csSup hbd (hm2 j))
    rw [hT] at hgoal
    exact hgoal
  have keyXY : ∀ ω : Ω, DXY ω = Mfun (WF ω) := by
    intro ω
    have hD := (statopia_math_node_3702036791_3ce4dae5 m n hm hn (fun i => X i ω) (fun j => Y j ω)).1
    rw [hMfun, hWF]
    simp only [hF_strict.le_iff_le]
    rw [hDXY]
    exact hD.trans (hbridge
      (fun i : Fin m => |(m : ℝ)⁻¹ * ∑ k : Fin m, (if X k ω ≤ X i ω then (1 : ℝ) else 0) - (n : ℝ)⁻¹ * ∑ k : Fin n, (if Y k ω ≤ X i ω then (1 : ℝ) else 0)|)
      (fun j : Fin n => |(m : ℝ)⁻¹ * ∑ k : Fin m, (if X k ω ≤ Y j ω then (1 : ℝ) else 0) - (n : ℝ)⁻¹ * ∑ k : Fin n, (if Y k ω ≤ Y j ω then (1 : ℝ) else 0)|) _ _)
  have keyUV : ∀ ω : Ω, (∀ i : Fin m, U i ω ∈ Set.Ioo (0 : ℝ) 1) →
      (∀ j : Fin n, V j ω ∈ Set.Ioo (0 : ℝ) 1) → DUV ω = Mfun (WU ω) := by
    intro ω h1 h2
    have hD := (statopia_math_node_3702036791_3ce4dae5 m n hm hn (fun i => U i ω) (fun j => V j ω)).2 h1 h2
    rw [hMfun, hWU]
    simp only []
    rw [hDUV]
    exact hD.trans (hbridge
      (fun i : Fin m => |(m : ℝ)⁻¹ * ∑ k : Fin m, (if U k ω ≤ U i ω then (1 : ℝ) else 0) - (n : ℝ)⁻¹ * ∑ k : Fin n, (if V k ω ≤ U i ω then (1 : ℝ) else 0)|)
      (fun j : Fin n => |(m : ℝ)⁻¹ * ∑ k : Fin m, (if U k ω ≤ V j ω then (1 : ℝ) else 0) - (n : ℝ)⁻¹ * ∑ k : Fin n, (if V k ω ≤ V j ω then (1 : ℝ) else 0)|) _ _)
  have hWF_meas : Measurable WF := by
    have h1 : Measurable (fun ω => fun i : Fin m => ⇑F (X i ω)) :=
      measurable_pi_iff.2 (fun i => hF_meas.comp (hX_meas i))
    have h2 : Measurable (fun ω => fun j : Fin n => ⇑F (Y j ω)) :=
      measurable_pi_iff.2 (fun j => hF_meas.comp (hY_meas j))
    rw [hWF]
    first
      | exact h1.prod_mk h2
      | exact Measurable.prod_mk h1 h2
      | exact h1.prod h2
      | exact Measurable.prod h1 h2
      | measurability
  have hWU_meas : Measurable WU := by
    have h1 : Measurable (fun ω => fun i : Fin m => U i ω) :=
      measurable_pi_iff.2 (fun i => hU_meas i)
    have h2 : Measurable (fun ω => fun j : Fin n => V j ω) :=
      measurable_pi_iff.2 (fun j => hV_meas j)
    rw [hWU]
    first
      | exact h1.prod_mk h2
      | exact Measurable.prod_mk h1 h2
      | exact h1.prod h2
      | exact Measurable.prod h1 h2
      | measurability
  have hUlaw := statopia_math_node_1542068916_7a306912 P m U hU_meas hU_uniform
  have hVlaw := statopia_math_node_1542068916_7a306912 P n V hV_meas hV_uniform
  have hUmem : ∀ i : Fin m, ∀ᵐ ω ∂P, U i ω ∈ Set.Ioo (0 : ℝ) 1 := by
    intro i
    have hmeas : MeasurableSet {ω : Ω | U i ω ∈ Set.Ioo (0 : ℝ) 1} :=
      measurableSet_Ioo.preimage (hU_meas i)
    exact (MeasureTheory.mem_ae_iff_prob_eq_one hmeas).2 (hUlaw.2 i)
  have hVmem : ∀ j : Fin n, ∀ᵐ ω ∂P, V j ω ∈ Set.Ioo (0 : ℝ) 1 := by
    intro j
    have hmeas : MeasurableSet {ω : Ω | V j ω ∈ Set.Ioo (0 : ℝ) 1} :=
      measurableSet_Ioo.preimage (hV_meas j)
    exact (MeasureTheory.mem_ae_iff_prob_eq_one hmeas).2 (hVlaw.2 j)
  have hUall : ∀ᵐ ω ∂P, ∀ i : Fin m, U i ω ∈ Set.Ioo (0 : ℝ) 1 := Filter.eventually_all.2 hUmem
  have hVall : ∀ᵐ ω ∂P, ∀ j : Fin n, V j ω ∈ Set.Ioo (0 : ℝ) 1 := Filter.eventually_all.2 hVmem
  have hall : ∀ᵐ ω ∂P,
      (∀ i : Fin m, U i ω ∈ Set.Ioo (0 : ℝ) 1) ∧ (∀ j : Fin n, V j ω ∈ Set.Ioo (0 : ℝ) 1) := by
    filter_upwards [hUall, hVall] with ω h1 h2
    exact ⟨h1, h2⟩
  have hDUV_ae : (fun ω => Mfun (WU ω)) =ᵐ[P] DUV := by
    filter_upwards [hall] with ω hω
    exact (keyUV ω hω.1 hω.2).symm
  have hf_meas : ∀ i : Fin m, Measurable (fun ω => ⇑F (X i ω)) := fun i => hF_meas.comp (hX_meas i)
  have hg_meas : ∀ j : Fin n, Measurable (fun ω => ⇑F (Y j ω)) := fun j => hF_meas.comp (hY_meas j)
  have hf_indep : iIndepFun (fun i ω => ⇑F (X i ω)) P :=
    hX_indep.comp (fun i (x : ℝ) => ⇑F x) (fun i => hF_meas)
  have hg_indep : iIndepFun (fun j ω => ⇑F (Y j ω)) P :=
    hY_indep.comp (fun j (x : ℝ) => ⇑F x) (fun j => hF_meas)
  have hcomp_meas_m : Measurable (fun (a : Fin m → ℝ) => fun i : Fin m => ⇑F (a i)) :=
    measurable_pi_iff.2 (fun i => hF_meas.comp ((measurable_pi_iff.1 measurable_id) i))
  have hcomp_meas_n : Measurable (fun (b : Fin n → ℝ) => fun j : Fin n => ⇑F (b j)) :=
    measurable_pi_iff.2 (fun j => hF_meas.comp ((measurable_pi_iff.1 measurable_id) j))
  have hfg_indep : IndepFun (fun ω => fun i => ⇑F (X i ω)) (fun ω => fun j => ⇑F (Y j ω)) P :=
    hXY_indep.comp hcomp_meas_m hcomp_meas_n
  have hf_law : ∀ i : Fin m, Measure.map (fun ω => ⇑F (X i ω)) P = Lam := by
    intro i
    rw [hLam]
    exact statopia_math_node_947602353_69874ec6 P ⇑F hF_cont hF_strict hF_bot hF_top m X hX_meas hX_cdf i
  have hg_law : ∀ j : Fin n, Measure.map (fun ω => ⇑F (Y j ω)) P = Lam := by
    intro j
    rw [hLam]
    exact statopia_math_node_947602353_69874ec6 P ⇑F hF_cont hF_strict hF_bot hF_top n Y hY_meas hY_cdf j
  have hf'_law : ∀ i : Fin m, Measure.map (U i) P = Lam := by
    intro i
    rw [hLam]
    exact hUlaw.1 i
  have hg'_law : ∀ j : Fin n, Measure.map (V j) P = Lam := by
    intro j
    rw [hLam]
    exact hVlaw.1 j
  have hjoint : Measure.map WF P = Measure.map WU P := by
    rw [hWF, hWU]
    exact statopia_math_node_270293103_a393561b P Lam m n
      (fun i ω => ⇑F (X i ω)) U (fun j ω => ⇑F (Y j ω)) V
      hf_meas hU_meas hg_meas hV_meas
      hf_indep hU_indep hg_indep hV_indep
      hfg_indep hUV_indep hf_law hf'_law hg_law hg'_law
  have hDXY_eq : (fun ω => Mfun (WF ω)) = DXY := funext fun ω => (keyXY ω).symm
  have hDXY_meas : Measurable DXY := by
    rw [← hDXY_eq]
    exact hM_meas.comp hWF_meas
  have hDUV_aemeas : AEMeasurable DUV P := by
    have h1 : AEMeasurable (fun ω => Mfun (WU ω)) P := (hM_meas.comp hWU_meas).aemeasurable
    exact h1.congr hDUV_ae
  have hmap : Measure.map DXY P = Measure.map DUV P := by
    have h3 : Measure.map (fun ω => Mfun (WF ω)) P = Measure.map (fun ω => Mfun (WU ω)) P := by
      have h4 : Measure.map Mfun (Measure.map WF P) = Measure.map Mfun (Measure.map WU P) := by
        rw [hjoint]
      exact (Measure.map_map hM_meas hWF_meas).symm.trans (h4.trans (Measure.map_map hM_meas hWU_meas))
    calc Measure.map DXY P = Measure.map (fun ω => Mfun (WF ω)) P := by rw [hDXY_eq]
      _ = Measure.map (fun ω => Mfun (WU ω)) P := h3
      _ = Measure.map DUV P := Measure.map_congr hDUV_ae
  exact ⟨hDXY_meas.aemeasurable, hDUV_aemeas, hmap⟩
  /- @proof-region region.root.38e9a2dba3ad end -/
