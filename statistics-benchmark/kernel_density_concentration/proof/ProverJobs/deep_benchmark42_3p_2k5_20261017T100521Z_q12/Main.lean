import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q12.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q12.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q12.Base

open MeasureTheory ProbabilityTheory

theorem kernel_density_concentration
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n)
    (X : Fin n → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (f : ℝ → ℝ) (hf_meas : Measurable f)
    (hf_nonneg : ∀ᵐ x ∂volume, 0 ≤ f x)
    (hX_law : ∀ i,
      HasLaw (X i) (volume.withDensity (fun x ↦ ENNReal.ofReal (f x))) P)
    (K : ℝ → ℝ) (hK_meas : Measurable K)
    (hK_nonneg : ∀ u, 0 ≤ K u)
    (hK_int : Integrable K)
    (hK_one : ∫ u, K u = 1)
    (h : ℝ) (hh : 0 < h) :
    let estimate : Ω → ℝ → ℝ := fun ω x ↦
      ((n : ℝ) * h)⁻¹ * ∑ i, K ((x - X i ω) / h)
    ∀ δ : ℝ, 0 ≤ δ →
      (P {ω |
        (∫ x, |estimate ω x - f x|) ≥
          (∫ z, ∫ x, |estimate z x - f x| ∂volume ∂P) + δ}).toReal ≤
        Real.exp (-(n : ℝ) * δ ^ 2 / 8)
:= by
  /- @proof-region region.root.1de322a40e97 begin -/
  intro estimate δ hδ
  rcases lt_or_eq_of_le hδ with hδpos | hδ0
  · set F : Ω → ℝ := fun ω => ∫ x : ℝ, |estimate ω x - f x| with hFdef
    set G : (Fin n → ℝ) → ℝ := fun a => ∫ x : ℝ, |((n : ℝ) * h)⁻¹ * ∑ i : Fin n, K ((x - a i) / h) - f x| with hGdef
    have hidx : Fin n := ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩
    haveI hprob : IsProbabilityMeasure
        (volume.withDensity (fun x => ENNReal.ofReal (f x))) :=
      (ProbabilityTheory.HasLaw.isProbabilityMeasure_iff (hX_law hidx)).mp inferInstance
    have hmass : (volume.withDensity (fun x => ENNReal.ofReal (f x))) Set.univ = 1 :=
      measure_univ
    have hlin : ∫⁻ x : ℝ, ENNReal.ofReal (f x) = 1 := by
      have h := MeasureTheory.lintegral_withDensity_eq_lintegral_mul (volume)
        (f := fun x : ℝ => ENNReal.ofReal (f x)) hf_meas.ennreal_ofReal
        (g := fun _ : ℝ => (1 : ENNReal)) measurable_const
      rw [MeasureTheory.lintegral_one, hmass] at h
      simpa only [Pi.mul_apply, mul_one] using h.symm
    have hf_int : Integrable f := by
      refine ⟨hf_meas.aestronglyMeasurable, ?_⟩
      rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
      have hcongr : ∫⁻ a : ℝ, ‖f a‖ₑ = ∫⁻ a : ℝ, ENNReal.ofReal (f a) := by
        refine MeasureTheory.lintegral_congr_ae ?_
        filter_upwards [hf_nonneg] with x hx
        exact Real.enorm_eq_ofReal hx
      rw [hcongr, hlin]
      simp
    have hf_one : ∫ x : ℝ, f x = 1 := by
      rw [Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.integral_eq_lintegral_toReal_of_nonneg
        hf_nonneg hf_int, hlin]
      simp
    have hf_l1 : ∫ x : ℝ, |f x| = 1 := by
      rw [MeasureTheory.integral_congr_ae (by
        filter_upwards [hf_nonneg] with x hx
        exact abs_of_nonneg hx)]
      exact hf_one
    have hstab : ∀ (k : Fin n) (u : Fin n → ℝ) (t : ℝ),
        |G u - G (Function.update u k t)| ≤ 2 / (n : ℝ) :=
      statopia_math_node_3608866754_ebb2fee6 n hn h hh K hK_meas hK_nonneg hK_int hK_one
        f hf_meas hf_int
    have hG_bound : ∀ u : Fin n → ℝ, |G u| ≤ |G 0| + 2 := by
      intro u
      set v : ℕ → Fin n → ℝ := fun j i => if (i.val : ℕ) < j then u i else 0 with hv
      have hvstep : ∀ (j : ℕ) (hj : j < n),
          Function.update (v j) ⟨j, hj⟩ (u ⟨j, hj⟩) = v (j + 1) := by
        intro j hj
        funext i
        simp only [hv, Function.update]
        by_cases hik : i = ⟨j, hj⟩
        · subst hik
          rw [dif_pos rfl, if_pos (Nat.lt_succ_self j)]
        · rw [dif_neg hik]
          by_cases hcase : i.val < j
          · rw [if_pos hcase, if_pos (Nat.lt_succ_of_lt hcase)]
          · have hne : ¬ (i.val < j + 1) := by
              intro hc
              have hval : i.val ≠ j := by
                intro hv'
                exact hik (Fin.ext hv')
              omega
            rw [if_neg hcase, if_neg hne]
      have hstep : ∀ (j : ℕ) (hj : j < n), |G (v (j + 1)) - G (v j)| ≤ 2 / (n : ℝ) := by
        intro j hj
        have hst := hstab ⟨j, hj⟩ (v j) (u ⟨j, hj⟩)
        rw [hvstep j hj, abs_sub_comm] at hst
        exact hst
      have hinduction : ∀ j : ℕ, j ≤ n → |G (v j) - G (v 0)| ≤ (j : ℝ) * (2 / (n : ℝ)) := by
        intro j
        induction j with
        | zero =>
          intro _
          simp
        | succ j ih =>
          intro hj
          have hprev := ih (Nat.le_of_succ_le hj)
          have hs := hstep j (Nat.lt_of_succ_le hj)
          calc |G (v (j + 1)) - G (v 0)|
              = |(G (v (j + 1)) - G (v j)) + (G (v j) - G (v 0))| := by
                rw [show G (v (j + 1)) - G (v 0) =
                  (G (v (j + 1)) - G (v j)) + (G (v j) - G (v 0)) from by ring]
            _ ≤ |G (v (j + 1)) - G (v j)| + |G (v j) - G (v 0)| := abs_add_le _ _
            _ ≤ 2 / (n : ℝ) + (j : ℝ) * (2 / (n : ℝ)) := by linarith
            _ = ((j + 1 : ℕ) : ℝ) * (2 / (n : ℝ)) := by push_cast; ring
      have hlast := hinduction n le_rfl
      have hv0 : v 0 = 0 := by
        funext i
        simp only [hv]
        rw [if_neg (Nat.not_lt_zero i.val)]
        rfl
      have hvn : v n = u := by
        funext i
        simp only [hv]
        rw [if_pos i.isLt]
      rw [hv0, hvn] at hlast
      have hsimp : (n : ℝ) * (2 / (n : ℝ)) = 2 := by
        have hnne : (n : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hn)
        field_simp
      rw [hsimp] at hlast
      have hfin : |G u| ≤ 2 + |G 0| := by
        calc |G u| = |(G u - G 0) + G 0| := by
              congr 1
              ring
          _ ≤ |G u - G 0| + |G 0| := abs_add_le _ _
          _ ≤ 2 + |G 0| := by linarith
      linarith
    have hB : (0 : ℝ) ≤ |G 0| + 2 := by positivity
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hc : (0 : ℝ) ≤ 2 / (n : ℝ) := by positivity
    have hN3 := statopia_math_node_2163822838_d5b91ca4 n hn X hX_meas f hf_meas K hK_meas h hh
    obtain ⟨he_meas, hG_meas, hFfac, hF_meas, hF_sigma⟩ := hN3
    have hmono : Monotone (fun j : Fin (n + 1) =>
        ⨆ i : Fin n, ⨆ (_ : i.val < j.val),
          MeasurableSpace.comap (X i) (inferInstance : MeasurableSpace ℝ)) := by
      intro j j' hjj
      refine iSup_le fun i => iSup_le fun hi => ?_
      exact (le_iSup (fun _ : (i.val < j'.val) =>
          MeasurableSpace.comap (X i) (inferInstance : MeasurableSpace ℝ))
          (lt_of_lt_of_le hi hjj)).trans
        (le_iSup (fun i : Fin n => ⨆ (_ : i.val < j'.val),
          MeasurableSpace.comap (X i) (inferInstance : MeasurableSpace ℝ)) i)
    have hle_top : ∀ j : Fin (n + 1),
        (⨆ i : Fin n, ⨆ (_ : i.val < j.val),
          MeasurableSpace.comap (X i) (inferInstance : MeasurableSpace ℝ)) ≤
          (inferInstance : MeasurableSpace Ω) := by
      intro j
      exact iSup_le fun i => iSup_le fun _ =>
        MeasurableSpace.comap_le_iff_le_map.mpr (hX_meas i)
    set seqF : Fin (n + 1) → MeasurableSpace Ω := fun j =>
      ⨆ i : Fin n, ⨆ (_ : i.val < j.val),
        MeasurableSpace.comap (X i) (inferInstance : MeasurableSpace ℝ) with hseqF
    set filt : Filtration (Fin (n + 1)) (inferInstance : MeasurableSpace Ω) :=
      ⟨seqF, hmono, hle_top⟩ with hfiltdef
    set ψ : Fin (n + 1) → Ω → ℝ := fun j => P[F | seqF j] with hψdef
    set d : Fin n → Ω → ℝ := fun k => ψ k.succ - ψ k.castSucc with hddef
    have hF_int : Integrable F P := by
      refine MeasureTheory.Integrable.of_bound hF_meas.aestronglyMeasurable (|G 0| + 2) ?_
      filter_upwards with ω
      rw [Real.norm_eq_abs]
      exact hG_bound (fun i => X i ω)
    have hd_sm : ∀ k : Fin n, StronglyMeasurable[seqF k.succ] (d k) := by
      intro k
      have h1 : StronglyMeasurable[seqF k.succ] (ψ k.succ) := by
        show StronglyMeasurable[seqF k.succ] (P[F | seqF k.succ])
        exact stronglyMeasurable_condExp
      have h2 : StronglyMeasurable[seqF k.succ] (ψ k.castSucc) := by
        show StronglyMeasurable[seqF k.succ] (P[F | seqF k.castSucc])
        exact stronglyMeasurable_condExp.mono (hmono (Fin.castSucc_le_succ k))
      show StronglyMeasurable[seqF k.succ] (ψ k.succ - ψ k.castSucc)
      exact h1.sub h2
    have hcenter : ∀ k : Fin n, P[d k | seqF k.castSucc] =ᵐ[P] 0 := by
      have hbdd_abs : ∀ j : Fin (n + 1), ∀ᵐ ω ∂P, |P[F | seqF j] ω| ≤ (|G 0| + 2) := by
        intro j
        have hlej : seqF j ≤ (inferInstance : MeasurableSpace Ω) := hle_top j
        have hconst : P[(fun _ : Ω => (|G 0| + 2)) | seqF j] = (fun _ : Ω => (|G 0| + 2)) :=
          condExp_const hlej (|G 0| + 2)
        have hFle : F ≤ᵐ[P] (fun _ : Ω => (|G 0| + 2)) := by
          filter_upwards with ω
          exact (abs_le.mp (hG_bound (fun i => X i ω))).2
        have hup : P[F | seqF j] ≤ᵐ[P] (fun _ : Ω => (|G 0| + 2)) := by
          have h := condExp_mono (m := seqF j) hF_int (integrable_const (|G 0| + 2)) hFle
          rwa [hconst] at h
        have hnFle : (-F) ≤ᵐ[P] (fun _ : Ω => (|G 0| + 2)) := by
          filter_upwards with ω
          have h := (abs_le.mp (hG_bound (fun i => X i ω))).1
          show -(F ω) ≤ |G 0| + 2
          linarith
        have hlow : P[-F | seqF j] ≤ᵐ[P] (fun _ : Ω => (|G 0| + 2)) := by
          have h := condExp_mono (m := seqF j) hF_int.neg (integrable_const (|G 0| + 2)) hnFle
          rwa [hconst] at h
        have hneg : P[-F | seqF j] =ᵐ[P] -P[F | seqF j] := condExp_neg F (seqF j)
        have hnegle : (-P[F | seqF j]) ≤ᵐ[P] (fun _ : Ω => (|G 0| + 2)) := by
          filter_upwards [hlow, hneg] with ω hω hω'
          rw [hω'] at hω
          simpa using hω
        filter_upwards [hup, hnegle] with ω hω1 hω4
        rw [abs_le]
        refine ⟨?_, hω1⟩
        have h5 : -P[F | seqF j] ω ≤ |G 0| + 2 := by
          simpa only [Pi.neg_apply] using hω4
        linarith
      intro k
      have hle1 : seqF k.castSucc ≤ seqF k.succ := hmono (Fin.castSucc_le_succ k)
      have hle2 : seqF k.succ ≤ (inferInstance : MeasurableSpace Ω) := hle_top k.succ
      have hle3 : seqF k.castSucc ≤ (inferInstance : MeasurableSpace Ω) := hle_top k.castSucc
      have hA : P[ψ k.succ | seqF k.castSucc] =ᵐ[P] P[F | seqF k.castSucc] :=
        condExp_condExp_of_le hle1 hle2
      have hB : P[ψ k.castSucc | seqF k.castSucc] =ᵐ[P] P[F | seqF k.castSucc] :=
        condExp_condExp_of_le le_rfl hle3
      have hi1 : Integrable (ψ k.succ) P := by
        refine MeasureTheory.Integrable.of_bound ?_ (|G 0| + 2) ?_
        · have hsm : StronglyMeasurable[seqF k.succ] (P[F | seqF k.succ]) :=
            stronglyMeasurable_condExp
          exact (hsm.mono (hle_top k.succ)).aestronglyMeasurable
        · filter_upwards [hbdd_abs k.succ] with ω hω
          simpa [Real.norm_eq_abs] using hω
      have hi2 : Integrable (ψ k.castSucc) P := by
        refine MeasureTheory.Integrable.of_bound ?_ (|G 0| + 2) ?_
        · have hsm : StronglyMeasurable[seqF k.castSucc] (P[F | seqF k.castSucc]) :=
            stronglyMeasurable_condExp
          exact (hsm.mono (hle_top k.castSucc)).aestronglyMeasurable
        · filter_upwards [hbdd_abs k.castSucc] with ω hω
          simpa [Real.norm_eq_abs] using hω
      have h1 : P[d k | seqF k.castSucc] =ᵐ[P]
          P[ψ k.succ | seqF k.castSucc] - P[ψ k.castSucc | seqF k.castSucc] :=
        condExp_sub hi1 hi2 (seqF k.castSucc)
      refine h1.trans ?_
      filter_upwards [hA, hB] with ω hω1 hω2
      simp only [Pi.sub_apply, Pi.zero_apply]
      rw [hω1, hω2, sub_self]
    have hbound : ∀ k : Fin n, ∀ᵐ ω ∂P, |d k ω| ≤ 2 / (n : ℝ) := by
      intro k
      simpa only [d, ψ, seqF] using
        statopia_math_node_3855570477_39b85b10 P n hn X hX_meas hX_indep
          ((2 : ℝ) / (n : ℝ)) (|G 0| + 2) hc hB G hG_meas hG_bound hstab k
    have hsumpos : 0 < ∑ k : Fin n, ((2 : ℝ) / (n : ℝ)) ^ 2 := by
      refine Finset.sum_pos (fun k _ => ?_)
        ⟨⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩, Finset.mem_univ _⟩
      exact pow_pos (div_pos (by norm_num) hn0) 2
    have hazuma :=
      Statlib.StatFoundation.Concentration.ExponentialType.azuma_sum_meas_ge_le_exp
        P n d (fun _ => (2 : ℝ) / (n : ℝ)) δ filt hd_sm hcenter hbound hδpos hsumpos
    have hexp : -δ ^ 2 / (2 * ∑ k : Fin n, ((2 : ℝ) / (n : ℝ)) ^ 2) =
        -(n : ℝ) * δ ^ 2 / 8 := by
      have hnne : (n : ℝ) ≠ 0 := ne_of_gt hn0
      have hsum4 : ∑ k : Fin n, ((2 : ℝ) / (n : ℝ)) ^ 2 = 4 / (n : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
        ring
      rw [hsum4]
      field_simp
      ring
    rw [hexp] at hazuma
    have hseqF_zero : seqF (0 : Fin (n + 1)) = ⊥ := by
      refine le_antisymm ?_ bot_le
      rw [hseqF]
      refine iSup_le fun i => iSup_le fun hi => ?_
      exact absurd hi (Nat.not_lt_zero i.val)
    have hψ0 : ψ 0 =ᵐ[P] (fun _ : Ω => ∫ z : Ω, F z ∂P) := by
      have hbot := condExp_bot_ae_eq (μ := P) F
      have hreal : (P.real Set.univ)⁻¹ = (1 : ℝ) := by
        have h1 : P.real Set.univ = 1 := by simp [Measure.real]
        rw [h1, inv_one]
      show P[F | seqF (0 : Fin (n + 1))] =ᵐ[P] (fun _ : Ω => ∫ z : Ω, F z ∂P)
      rw [hseqF_zero]
      filter_upwards [hbot] with ω hω
      rw [hω, hreal, one_smul]
    have hFm : AEStronglyMeasurable[seqF (Fin.last n)] F P := by
      have hsig : (⨆ i : Fin n,
            MeasurableSpace.comap (X i) (inferInstance : MeasurableSpace ℝ)) ≤
          seqF (Fin.last n) := by
        rw [hseqF]
        refine iSup_le fun i => ?_
        exact (le_iSup (fun _ : (i.val < (Fin.last n).val) =>
            MeasurableSpace.comap (X i) (inferInstance : MeasurableSpace ℝ)) i.isLt).trans
          (le_iSup (fun i : Fin n => ⨆ (_ : i.val < (Fin.last n).val),
            MeasurableSpace.comap (X i) (inferInstance : MeasurableSpace ℝ)) i)
      exact (hF_sigma.stronglyMeasurable.mono hsig).aestronglyMeasurable
    have hψn : ψ (Fin.last n) =ᵐ[P] F := by
      have hle : seqF (Fin.last n) ≤ (inferInstance : MeasurableSpace Ω) := hle_top _
      have hone : F =ᵐ[P] P[F | seqF (Fin.last n)] :=
        ae_eq_condExp_of_forall_setIntegral_eq hle hF_int
          (fun s _ _ => hF_int.integrableOn)
          (fun s _ _ => rfl)
          hFm
      show P[F | seqF (Fin.last n)] =ᵐ[P] F
      exact hone.symm
    have htel : ∑ k : Fin n, d k = ψ (Fin.last n) - ψ 0 := by
      funext ω
      simp only [Finset.sum_apply, Pi.sub_apply]
      set g : ℕ → ℝ := fun i => if hi : i ≤ n then ψ ⟨i, Nat.lt_succ_of_le hi⟩ ω else 0 with hg
      have hgn : g n = ψ (Fin.last n) ω := by
        simp only [hg]
        rw [dif_pos (le_refl n)]
        rfl
      have hg0 : g 0 = ψ (0 : Fin (n + 1)) ω := by
        simp only [hg]
        rw [dif_pos (Nat.zero_le n)]
        rfl
      have hstep : ∀ k : Fin n, d k ω = g (k.val + 1) - g k.val := by
        intro k
        have h1 : g (k.val + 1) = ψ k.succ ω := by
          simp only [hg]
          rw [dif_pos (Nat.succ_le_of_lt k.isLt)]
          rfl
        have h2 : g k.val = ψ k.castSucc ω := by
          simp only [hg]
          rw [dif_pos (Nat.le_of_lt k.isLt)]
          rfl
        simp only [d, Pi.sub_apply]
        rw [h1, h2]
      have hsum_eq : ∑ k : Fin n, d k ω =
          Finset.sum (Finset.range n) (fun i => g (i + 1) - g i) := by
        rw [← Fin.sum_univ_eq_sum_range (fun i => g (i + 1) - g i) n]
        exact Finset.sum_congr rfl (fun k _ => hstep k)
      rw [hsum_eq, Finset.sum_range_sub g n, hgn, hg0]
    have hPA : P {ω : Ω | F ω ≥ (∫ z : Ω, F z ∂P) + δ} ≤
        P {ω : Ω | δ ≤ ∑ k : Fin n, d k ω} := by
      have hN1 : P {ω : Ω | ψ (Fin.last n) ω ≠ F ω} = 0 := ae_iff.mp hψn
      have hN2 : P {ω : Ω | ψ 0 ω ≠ ∫ z : Ω, F z ∂P} = 0 := ae_iff.mp hψ0
      have hN : P ({ω : Ω | ψ (Fin.last n) ω ≠ F ω} ∪
          {ω : Ω | ψ 0 ω ≠ ∫ z : Ω, F z ∂P}) = 0 := measure_union_null hN1 hN2
      have hsub : {ω : Ω | F ω ≥ (∫ z : Ω, F z ∂P) + δ} ⊆
          {ω : Ω | δ ≤ ∑ k : Fin n, d k ω} ∪
            ({ω : Ω | ψ (Fin.last n) ω ≠ F ω} ∪
              {ω : Ω | ψ 0 ω ≠ ∫ z : Ω, F z ∂P}) := by
        intro ω hω
        by_cases hsum : δ ≤ ∑ k : Fin n, d k ω
        · exact Or.inl hsum
        · refine Or.inr ?_
          by_contra hcon
          simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
          obtain ⟨h1, h2⟩ := hcon
          have htelω : ∑ k : Fin n, d k ω = ψ (Fin.last n) ω - ψ 0 ω := by
            have hh := congrFun htel ω
            simpa only [Finset.sum_apply, Pi.sub_apply] using hh
          rw [htelω, h1, h2] at hsum
          simp only [Set.mem_setOf_eq] at hω
          linarith
      calc P {ω : Ω | F ω ≥ (∫ z : Ω, F z ∂P) + δ}
          ≤ P ({ω : Ω | δ ≤ ∑ k : Fin n, d k ω} ∪
              ({ω : Ω | ψ (Fin.last n) ω ≠ F ω} ∪
                {ω : Ω | ψ 0 ω ≠ ∫ z : Ω, F z ∂P})) := measure_mono hsub
        _ ≤ P {ω : Ω | δ ≤ ∑ k : Fin n, d k ω} +
              P ({ω : Ω | ψ (Fin.last n) ω ≠ F ω} ∪
                {ω : Ω | ψ 0 ω ≠ ∫ z : Ω, F z ∂P}) := measure_union_le _ _
        _ = P {ω : Ω | δ ≤ ∑ k : Fin n, d k ω} := by rw [hN, add_zero]
    refine ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le ?_
    exact le_trans hPA hazuma
  · obtain rfl : δ = 0 := hδ0.symm
    have hexp : Real.exp (-(n : ℝ) * (0 : ℝ) ^ 2 / 8) = 1 := by simp
    rw [hexp]
    refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    refine le_trans (measure_mono (Set.subset_univ _)) ?_
    simp
  /- @proof-region region.root.1de322a40e97 end -/
