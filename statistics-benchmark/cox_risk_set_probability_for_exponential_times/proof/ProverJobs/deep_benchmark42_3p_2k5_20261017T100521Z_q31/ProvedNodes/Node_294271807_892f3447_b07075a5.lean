import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q31.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q31.Base

open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_294271807_892f3447 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n)
    (T : Fin n → Ω → ℝ)
    (hTmeas : ∀ i, Measurable (T i))
    (hindep : iIndepFun T P),
    ∀ i : Fin n,
      MeasurableSet {ω | ∀ j : Fin n, j ≠ i → T i ω < T j ω} ∧
        (P {ω | ∀ j : Fin n, j ≠ i → T i ω < T j ω}
          = ∫⁻ x, P {y | ∀ j : Fin n, j ≠ i → T i x < T j y} ∂P) ∧
        (P {ω | ∀ j : Fin n, j ≠ i → T i ω < T j ω}
          = ∫⁻ x, ∫⁻ y,
              (∏ j ∈ Finset.univ.erase i,
                (if T i x < T j y then (1 : ENNReal) else 0)) ∂P ∂P) := by
  /- @proof-region region.target-node.session.d7451afc838d2130 begin -/
  intro Ω mΩ P hP n hn T hTmeas hindep i
  haveI hPprob : IsProbabilityMeasure P := hP
  classical
  have key : P {ω : Ω | ∀ j : Fin n, j ≠ i → T i ω < T j ω}
      = ∫⁻ x, P {y : Ω | ∀ j : Fin n, j ≠ i → T i x < T j y} ∂P := by
    haveI hprobmap : ∀ k : Fin n, IsProbabilityMeasure (Measure.map (T k) P) :=
      fun k => ⟨by rw [Measure.map_apply (hTmeas k) MeasurableSet.univ]; simp⟩
    let W : Ω → (Fin n → ℝ) := fun ω k => T k ω
    let G : Ω × Ω → (Fin n → ℝ) := fun z k => if k = i then T i z.1 else T k z.2
    let R : Set (Fin n → ℝ) := {s | ∀ j : Fin n, j ≠ i → s i < s j}
    have hcoord : ∀ k : Fin n, Measurable (fun s : Fin n → ℝ => s k) :=
      fun k => measurable_pi_apply k
    have hRmeas : MeasurableSet R := by
      have hIi : MeasurableSet (⋂ j ∈ Finset.univ.erase i,
          ((fun s : Fin n → ℝ => s j - s i) ⁻¹' Set.Ioi (0 : ℝ))) :=
        Finset.measurableSet_biInter (Finset.univ.erase i)
          (fun j _ => ((hcoord j).sub (hcoord i)) (measurableSet_Ioi (a := (0 : ℝ))))
      have hset : R = ⋂ j ∈ Finset.univ.erase i,
          ((fun s : Fin n → ℝ => s j - s i) ⁻¹' Set.Ioi (0 : ℝ)) := by
        ext s
        simp [R, Finset.mem_erase, Set.mem_Ioi, sub_pos]
      rw [hset]
      exact hIi
    have hWmeas : Measurable W := by
      refine measurable_pi_iff.mpr (fun k => ?_)
      exact hTmeas k
    have hGmeas : Measurable G := by
      refine measurable_pi_iff.mpr (fun k => ?_)
      by_cases hk : k = i
      · rw [show (fun z : Ω × Ω => G z k) = fun z : Ω × Ω => T i z.1 from by
          funext z
          simp only [G, if_pos hk]]
        exact (hTmeas i).comp measurable_fst
      · rw [show (fun z : Ω × Ω => G z k) = fun z : Ω × Ω => T k z.2 from by
          funext z
          simp only [G, if_neg hk]]
        exact (hTmeas k).comp measurable_snd
    have hWlaw : Measure.map W P = Measure.pi (fun k : Fin n => Measure.map (T k) P) := by
      have h := (iIndepFun_iff_map_fun_eq_pi_map (fun k => (hTmeas k).aemeasurable)).mp hindep
      simpa [W] using h
    have hleft : P {ω : Ω | ∀ j : Fin n, j ≠ i → T i ω < T j ω}
        = Measure.pi (fun k : Fin n => Measure.map (T k) P) R := by
      have hWA : W ⁻¹' R = {ω : Ω | ∀ j : Fin n, j ≠ i → T i ω < T j ω} := by
        ext ω
        show (∀ j : Fin n, j ≠ i → W ω i < W ω j) ↔ (∀ j : Fin n, j ≠ i → T i ω < T j ω)
        exact Iff.rfl
      have hmap : Measure.map W P R = P (W ⁻¹' R) := Measure.map_apply hWmeas hRmeas
      rw [← hWA, ← hmap, hWlaw]
    have hGlaw : Measure.map G (P.prod P) = Measure.pi (fun k : Fin n => Measure.map (T k) P) := by
      refine (Measure.pi_eq ?_).symm
      intro s hs
      have hbox : MeasurableSet (Set.univ.pi s) := by
        have hset : Set.univ.pi s = ⋂ k : Fin n, ((fun f : Fin n → ℝ => f k) ⁻¹' s k) := by
          ext f
          simp
        rw [hset]
        exact MeasurableSet.iInter (fun k => (hcoord k) (hs k))
      have hmapG : Measure.map G (P.prod P) (Set.univ.pi s) = (P.prod P) (G ⁻¹' Set.univ.pi s) :=
        Measure.map_apply hGmeas hbox
      rw [hmapG]
      have hpre : G ⁻¹' Set.univ.pi s
          = (T i ⁻¹' s i) ×ˢ (⋂ k ∈ Finset.univ.erase i, T k ⁻¹' s k) := by
        ext z
        simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod, Set.mem_iInter,
          Finset.mem_erase, Finset.mem_univ, and_true]
        constructor
        · intro h
          refine ⟨?_, fun k hk => ?_⟩
          · have h1 := h i
            rwa [show G z i = T i z.1 from by simp [G]] at h1
          · have h1 := h k
            rwa [show G z k = T k z.2 from by simp only [G]; exact if_neg hk] at h1
        · rintro ⟨h0, hrest⟩ k
          by_cases hk : k = i
          · rw [hk, show G z i = T i z.1 from by simp [G]]
            exact h0
          · rw [show G z k = T k z.2 from by simp only [G]; exact if_neg hk]
            exact hrest k hk
      rw [hpre]
      have hprod_eq : (P.prod P) ((T i ⁻¹' s i) ×ˢ (⋂ k ∈ Finset.univ.erase i, T k ⁻¹' s k))
          = P (T i ⁻¹' s i) * P (⋂ k ∈ Finset.univ.erase i, T k ⁻¹' s k) :=
        Measure.prod_prod _ _
      rw [hprod_eq]
      have hind : P (⋂ k ∈ Finset.univ.erase i, T k ⁻¹' s k)
          = ∏ k ∈ Finset.univ.erase i, P (T k ⁻¹' s k) :=
        (iIndepFun_iff_measure_inter_preimage_eq_mul (μ := P)).mp hindep (Finset.univ.erase i)
          (fun k _ => hs k)
      rw [hind]
      have hmg : ∀ k : Fin n, P (T k ⁻¹' s k) = Measure.map (T k) P (s k) :=
        fun k => (Measure.map_apply (hTmeas k) (hs k)).symm
      simp only [hmg]
      exact Finset.mul_prod_erase (Finset.univ) (fun k : Fin n => Measure.map (T k) P (s k))
        (Finset.mem_univ i)
    have hSmeas : MeasurableSet {z : Ω × Ω | ∀ j : Fin n, j ≠ i → T i z.1 < T j z.2} := by
      have hIi : MeasurableSet (⋂ j ∈ Finset.univ.erase i,
          ((fun z : Ω × Ω => T j z.2 - T i z.1) ⁻¹' Set.Ioi (0 : ℝ))) :=
        Finset.measurableSet_biInter (Finset.univ.erase i)
          (fun j _ => (((hTmeas j).comp measurable_snd).sub ((hTmeas i).comp measurable_fst))
            (measurableSet_Ioi (a := (0 : ℝ))))
      have hset : {z : Ω × Ω | ∀ j : Fin n, j ≠ i → T i z.1 < T j z.2}
          = ⋂ j ∈ Finset.univ.erase i,
              ((fun z : Ω × Ω => T j z.2 - T i z.1) ⁻¹' Set.Ioi (0 : ℝ)) := by
        ext z
        simp [Finset.mem_erase, Set.mem_Ioi, sub_pos]
      rw [hset]
      exact hIi
    have hGR : G ⁻¹' R = {z : Ω × Ω | ∀ j : Fin n, j ≠ i → T i z.1 < T j z.2} := by
      ext z
      show (∀ j : Fin n, j ≠ i → G z i < G z j) ↔ (∀ j : Fin n, j ≠ i → T i z.1 < T j z.2)
      constructor
      · intro h j hj
        have h1 := h j hj
        rwa [show G z i = T i z.1 from by simp [G],
             show G z j = T j z.2 from by simp only [G]; exact if_neg hj] at h1
      · intro h j hj
        rw [show G z i = T i z.1 from by simp [G],
            show G z j = T j z.2 from by simp only [G]; exact if_neg hj]
        exact h j hj
    have hright : Measure.pi (fun k : Fin n => Measure.map (T k) P) R
        = ∫⁻ x, P {y : Ω | ∀ j : Fin n, j ≠ i → T i x < T j y} ∂P := by
      have hmap : Measure.map G (P.prod P) R = (P.prod P) (G ⁻¹' R) :=
        Measure.map_apply hGmeas hRmeas
      rw [← hGlaw, hmap, hGR]
      exact Measure.prod_apply hSmeas
    exact hleft.trans hright
  refine ⟨?_, key, ?_⟩
  · have hInter : MeasurableSet
        (⋂ j ∈ Finset.univ.erase i, ((fun ω : Ω => T j ω - T i ω) ⁻¹' Set.Ioi (0 : ℝ))) :=
      Finset.measurableSet_biInter (Finset.univ.erase i)
        (fun j _ => ((hTmeas j).sub (hTmeas i)) (measurableSet_Ioi (a := (0 : ℝ))))
    have hset : {ω : Ω | ∀ j : Fin n, j ≠ i → T i ω < T j ω}
        = ⋂ j ∈ Finset.univ.erase i, ((fun ω : Ω => T j ω - T i ω) ⁻¹' Set.Ioi (0 : ℝ)) := by
      ext ω
      simp [Finset.mem_erase, Set.mem_Ioi, sub_pos]
    rw [hset]
    exact hInter
  · have hpt : (fun x : Ω => P {y : Ω | ∀ j : Fin n, j ≠ i → T i x < T j y})
        = (fun x : Ω => ∫⁻ y, (∏ j ∈ Finset.univ.erase i,
            (if T i x < T j y then (1 : ENNReal) else 0)) ∂P) := by
      funext x
      have hIi : MeasurableSet
          (⋂ j ∈ Finset.univ.erase i, ((fun y : Ω => T j y) ⁻¹' Set.Ioi (T i x))) :=
        Finset.measurableSet_biInter (Finset.univ.erase i)
          (fun j _ => (hTmeas j) (measurableSet_Ioi (a := T i x)))
      have hmeasx : MeasurableSet {y : Ω | ∀ j : Fin n, j ≠ i → T i x < T j y} := by
        have hset : {y : Ω | ∀ j : Fin n, j ≠ i → T i x < T j y}
            = ⋂ j ∈ Finset.univ.erase i, ((fun y : Ω => T j y) ⁻¹' Set.Ioi (T i x)) := by
          ext y
          simp [Finset.mem_erase, Set.mem_Ioi]
        rw [hset]
        exact hIi
      have hprod : ∀ y : Ω, (∏ j ∈ Finset.univ.erase i,
            (if T i x < T j y then (1 : ENNReal) else 0))
          = {y' : Ω | ∀ j : Fin n, j ≠ i → T i x < T j y'}.indicator (fun _ => 1) y := by
        intro y
        by_cases h : ∀ j : Fin n, j ≠ i → T i x < T j y
        · rw [Set.indicator_of_mem (show y ∈ {y' : Ω | ∀ j : Fin n, j ≠ i → T i x < T j y'}
            from h)]
          refine Finset.prod_eq_one (fun j hj => ?_)
          rw [Finset.mem_erase] at hj
          exact if_pos (h j hj.1)
        · rw [Set.indicator_of_notMem (show y ∉ {y' : Ω | ∀ j : Fin n, j ≠ i → T i x < T j y'}
            from h)]
          push_neg at h
          obtain ⟨j, hji, hle⟩ := h
          exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
            (if_neg (not_lt.mpr hle))
      have hlint : ∫⁻ y, {y' : Ω | ∀ j : Fin n, j ≠ i → T i x < T j y'}.indicator (fun _ => 1) y ∂P
          = P {y' : Ω | ∀ j : Fin n, j ≠ i → T i x < T j y'} := by
        rw [lintegral_indicator_const hmeasx (1 : ENNReal), one_mul]
      calc P {y : Ω | ∀ j : Fin n, j ≠ i → T i x < T j y}
          = ∫⁻ y, {y' : Ω | ∀ j : Fin n, j ≠ i → T i x < T j y'}.indicator (fun _ => 1) y ∂P :=
            hlint.symm
        _ = ∫⁻ y, (∏ j ∈ Finset.univ.erase i,
              (if T i x < T j y then (1 : ENNReal) else 0)) ∂P := by
            congr 1
            funext y
            exact (hprod y).symm
    rw [key, hpt]
  /- @proof-region region.target-node.session.d7451afc838d2130 end -/
