import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.Vocabulary
import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.ProvedNodes
import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.Base

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal MeasureTheory Topology BigOperators
namespace Statlib.Imported

theorem paper_b0cf39bbf6c845c9a6b30a5db43f8efa
    {Θ X : Type*}
    [TopologicalSpace X] [MeasureSpace X] [BorelSpace X]
    
    
    
    [TopologicalSpace Θ] [MeasurableSpace Θ] [StandardBorelSpace Θ]
    
    
    (M : DPMModel Θ)
    
    
    (μ : Measure X) [SigmaFinite μ]
    (k : Θ → X → ℝ) (hk_nonneg : ∀ (θ : Θ) (x : X), 0 ≤ k θ x)
    (hk_meas : Measurable (Function.uncurry k))
    
    (hk_int : ∀ (θ : Θ), ∫⁻ x : X, ENNReal.ofReal (k θ x) ∂μ = 1)

    
    (hH4 : H4Condition M μ k)
    
    (t : ℕ) (ht : 1 ≤ t)
      (q : Fin t → ℝ) (θs : Fin t → Θ) (P : ProbabilityMeasure X)
      (hq : IsMixtureMeasure μ k q θs P.toMeasure)
      (hsupp : ∀ j : Fin t, θs j ∈ M.Q0.support)
      
      (U : Set (ProbabilityMeasure X)) (hU : U ∈ 𝓝 P)
      (hsep : ∀ s : ℕ, 1 ≤ s → s < t → U ∩ Gset μ k s = ∅) :
      
      
      ∀ ε : ℝ, 0 < ε →
        Tendsto
          (fun n : ℕ => (truthLaw P.toMeasure
            {x : ℕ → X |
              ε < (posteriorProb M k t n (fun i : Fin n => x (i : ℕ))).toReal} : ℝ≥0∞))
          atTop (𝓝 0)
:= by
  /- @proof-region region.root.25632fd897f7 begin -/
  intro ε hε
  rcases Nat.eq_or_lt_of_le ht with h1 | h2
  · rw [← h1]
    have hzero : ∀ (n : ℕ), 1 ≤ n → ∀ y : Fin n → X, posteriorProb M k 1 n y = 0 := by
      intro n hn y
      have hc : ∀ ξ : ProbabilityMeasure Θ × (ℕ → Θ), ¬ (clusterCount ξ.2 n < 1) := by
        intro ξ
        have hmem : (Set.range (fun i : Fin n => ξ.2 i)).Nonempty :=
          ⟨ξ.2 0, ⟨0, by omega⟩, rfl⟩
        have hfin : (Set.range (fun i : Fin n => ξ.2 i)).Finite := by
          have h := (Set.finite_univ (α := Fin n)).image (fun i : Fin n => ξ.2 i)
          simpa using h
        have hpos : 0 < (Set.range (fun i : Fin n => ξ.2 i)).ncard :=
          (Set.ncard_pos hfin).2 hmem
        show ¬ ((Set.range (fun i : Fin n => ξ.2 i)).ncard < 1)
        omega
      have hnum : (fun ξ : ProbabilityMeasure Θ × (ℕ → Θ) =>
          (if clusterCount ξ.2 n < 1 then
            ∏ i : Fin n, ENNReal.ofReal (k (ξ.2 i) (y i)) else 0)) = 0 := by
        funext ξ
        simp [hc ξ]
      simp only [posteriorProb]
      have hnum2 : (∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
          (if clusterCount ξ.2 n < 1 then
            ∏ i : Fin n, ENNReal.ofReal (k (ξ.2 i) (y i)) else 0) ∂M.latentLaw) = 0 := by
        rw [hnum]
        exact MeasureTheory.lintegral_zero
      rw [hnum2, ENNReal.zero_div]
    have hev : (fun n : ℕ => (truthLaw P.toMeasure
        {x : ℕ → X | ε < (posteriorProb M k 1 n (fun i : Fin n => x (i : ℕ))).toReal} : ℝ≥0∞))
        =ᶠ[atTop] (fun _ => 0) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hempty : {x : ℕ → X |
          ε < (posteriorProb M k 1 n (fun i : Fin n => x (i : ℕ))).toReal} = ∅ := by
        ext x
        show (ε < (posteriorProb M k 1 n (fun i : Fin n => x (i : ℕ))).toReal) ↔ False
        constructor
        · intro hx
          have h0 : posteriorProb M k 1 n (fun i : Fin n => x (i : ℕ)) = 0 := hzero n hn _
          simp [h0] at hx
          linarith
        · intro hx
          exact hx.elim
      rw [hempty, measure_empty]
    exact tendsto_const_nhds.congr' hev.symm
  · obtain ⟨r, ψ, ε₀, M₀, c, hr, hε₀, hM₀def, hM₀pos, hc_def, hc_pos, hVsub, hVsep⟩ :=
      statopia_math_node_3257560511_130c2ed0 (μ := μ) (k := k) hk_nonneg hk_meas hk_int
        P U hU t h2 (θs ⟨0, by omega⟩) hsep
    have hψ_cont : ∀ j : Fin r, Continuous (fun x : X => (ψ j : X → ℝ) x) :=
      fun j => (ψ j).continuous
    have hψ_bound : ∀ (j : Fin r) (x : X), |(ψ j : X → ℝ) x| ≤ M₀ := by
      intro j x
      rw [hM₀def]
      have hbdd1 : BddAbove (Set.range fun y : X => |(ψ j : X → ℝ) y|) := by
        refine ⟨‖ψ j‖, ?_⟩
        rintro _ ⟨y, rfl⟩
        simpa using BoundedContinuousFunction.norm_coe_le_norm (ψ j) y
      have hbdd2 : BddAbove (Set.range fun i : Fin r => ⨆ y : X, |(ψ i : X → ℝ) y|) := by
        have hf : (Set.range fun i : Fin r => ⨆ y : X, |(ψ i : X → ℝ) y|).Finite := by
          have h := (Set.finite_univ (α := Fin r)).image
            (fun i : Fin r => ⨆ y : X, |(ψ i : X → ℝ) y|)
          simpa using h
        exact hf.bddAbove
      calc |(ψ j : X → ℝ) x| ≤ ⨆ y : X, |(ψ j : X → ℝ) y| := le_ciSup hbdd1 x
        _ ≤ ⨆ i : Fin r, ⨆ y : X, |(ψ i : X → ℝ) y| := le_ciSup hbdd2 j
    set p0 : X → ℝ≥0∞ := fun x => ENNReal.ofReal (dpMixDensity k q θs x) with hp0_def
    have hP : P.toMeasure = μ.withDensity p0 := hq.2.2.2
    have hk_sec : ∀ θ : Θ, Measurable (fun x : X => k θ x) := fun θ =>
      hk_meas.comp (measurable_const.prodMk measurable_id)
    have hsum : Measurable (fun x : X => dpMixDensity k q θs x) := by
      unfold dpMixDensity
      exact Finset.measurable_sum _ (fun j _ => measurable_const.mul (hk_sec (θs j)))
    have hp0_meas : Measurable p0 := by
      rw [hp0_def]
      exact ENNReal.measurable_ofReal.comp hsum
    have hp0_int : ∫⁻ x, p0 x ∂μ = 1 := by
      have h1 : μ.withDensity p0 Set.univ = 1 := by
        rw [← hP]
        exact measure_univ
      rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
    have hε₀2 : 0 < ε₀ / 2 := by linarith
    have hDen_eq : ∀ (n : ℕ) (x : Fin n → X),
        (∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
            ∏ i : Fin n, ENNReal.ofReal (k (ξ.2 i) (x i)) ∂M.latentLaw)
          = ∫⁻ h : X → ℝ≥0∞, ∏ i : Fin n, h (x i) ∂
              (M.latentLaw.map (fun ξ : ProbabilityMeasure Θ × (ℕ → Θ) => dpmDensity k ξ.1)) :=
      fun n x => statopia_math_node_215231975_e5e8dd5e M μ k hk_nonneg hk_meas n x
    haveI hΛprob : IsProbabilityMeasure M.latentLaw := by
      haveI hπprob : IsProbabilityMeasure M.π := M.hπ
      obtain ⟨hGmeas, hGuniv⟩ := statopia_math_node_3905332965_3d9d9dd7 (Θ := Θ)
      have hFmeas : Measurable (fun a : ℝ => (M.dpLaw a).bind (fun P : ProbabilityMeasure Θ =>
          (Measure.dirac P).prod (Measure.infinitePi (fun _ : ℕ => P.toMeasure)))) :=
        (MeasureTheory.Measure.measurable_bind' hGmeas).comp M.dpLaw_meas
      refine ⟨?_⟩
      show Measure.bind M.π (fun a => Measure.bind (M.dpLaw a) (fun P : ProbabilityMeasure Θ =>
        (Measure.dirac P).prod (Measure.infinitePi (fun _ : ℕ => P.toMeasure)))) Set.univ = 1
      rw [Measure.bind_apply MeasurableSet.univ hFmeas.aemeasurable]
      have h1 : ∀ᵐ a ∂M.π, ((M.dpLaw a).bind (fun P : ProbabilityMeasure Θ =>
          (Measure.dirac P).prod (Measure.infinitePi (fun _ : ℕ => P.toMeasure)))) Set.univ = 1 := by
        filter_upwards [M.dpLaw_dirichlet] with a ha
        rw [Measure.bind_apply MeasurableSet.univ hGmeas.aemeasurable]
        simp only [hGuniv, lintegral_const]
        rw [one_mul]
        exact ha.1.measure_univ
      rw [lintegral_congr_ae h1, lintegral_const]
      rw [one_mul]
      exact measure_univ
    have hNum_bound : ∀ (n : ℕ), 0 < n →
        ∫⁻ x : Fin n → X,
            (if (⨆ j : Fin r, |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (x i))
                  - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure| < ε₀ / 2)
              then ∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
                Set.indicator {ξ : ProbabilityMeasure Θ × (ℕ → Θ) |
                    (Set.range (fun i : Fin n => ξ.2 (i : ℕ))).ncard < t}
                  (fun ξ => ∏ i : Fin n,
                    (ENNReal.ofReal (k (ξ.2 (i : ℕ)) (x i)) * (p0 (x i))⁻¹)) ξ ∂M.latentLaw
              else 0)
          ∂(Measure.pi (fun _ : Fin n => P.toMeasure))
          ≤ ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * c)) *
            M.latentLaw {ξ : ProbabilityMeasure Θ × (ℕ → Θ) |
              (Set.range (fun i : Fin n => ξ.2 (i : ℕ))).ncard < t} := by
      intro n hn
      exact statopia_math_node_3929518475_9153cd93 μ k hk_nonneg hk_meas hk_int p0 hp0_meas
        hp0_int P hP t h2 n hn r hr (fun j => (ψ j : X → ℝ)) hψ_cont M₀ hM₀def hM₀pos
        hψ_bound ε₀ hε₀ c hc_def hVsep M.latentLaw
        {ξ : ProbabilityMeasure Θ × (ℕ → Θ) | (Set.range (fun i : Fin n => ξ.2 (i : ℕ))).ncard < t}
        (statopia_math_node_4133567021_cdc336c6 n t)
        (Filter.Eventually.of_forall (fun ξ hξ => hξ))
    have hTypeI : ∀ (n : ℕ), 0 < n →
        Measure.pi (fun _ : Fin n => P.toMeasure)
            {y : Fin n → X |
              ε₀ / 2 ≤ ⨆ j : Fin r,
                |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (y i))
                  - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure|}
          ≤ ENNReal.ofReal (2 * (r : ℝ) * Real.exp (-(n : ℝ) * c)) := by
      intro n hn
      have h := (statopia_math_node_2781295325_3f1c8bad P.toMeasure r hr
        (fun j => (ψ j : X → ℝ)) hψ_cont M₀ hM₀pos hM₀def hψ_bound ε₀ hε₀).1 n hn
      rw [← hc_def] at h
      exact h
    have hP_p0_zero : P.toMeasure {x : X | p0 x = 0} = 0 := by
      have hs : MeasurableSet {x : X | p0 x = 0} := hp0_meas (measurableSet_singleton 0)
      rw [hP, withDensity_apply _ hs, ← lintegral_indicator hs]
      have hzero : ∀ x : X, {x : X | p0 x = 0}.indicator p0 x = 0 := by
        intro x
        by_cases hx : p0 x = 0
        · simp [hx]
        · simp [hx]
      simp [hzero]
    have hLam_le_one : ∀ A : Set (ProbabilityMeasure Θ × (ℕ → Θ)), M.latentLaw A ≤ 1 := by
      intro A
      calc M.latentLaw A ≤ M.latentLaw Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    have hsingle : ∀ i : ℕ, truthLaw P.toMeasure {x : ℕ → X | p0 (x i) = 0} = 0 := by
      intro i
      have hset : {x : ℕ → X | p0 (x i) = 0}
          = Set.pi ((({i} : Finset ℕ) : Set ℕ))
              (fun k => if k = i then {y : X | p0 y = 0} else Set.univ) := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_pi, Finset.mem_coe, Finset.mem_singleton]
        constructor
        · rintro hx k rfl
          simpa using hx
        · intro hx
          simpa using hx i rfl
      rw [hset]
      simp only [truthLaw]
      rw [Measure.infinitePi_pi]
      · simp [hP_p0_zero]
      · intro k _
        by_cases h : k = i
        · subst h
          simpa using hp0_meas.eq_const 0
        · simp [h]
    have hae_pos : ∀ (n : ℕ), ∀ᵐ x ∂(truthLaw P.toMeasure), ∀ i : Fin n, p0 (x (i : ℕ)) ≠ 0 := by
      intro n
      have hunion : truthLaw P.toMeasure
          (⋃ i : Fin n, {x : ℕ → X | p0 (x (i : ℕ)) = 0}) = 0 :=
        measure_iUnion_null (fun i => hsingle (i : ℕ))
      have hcompl : {x : ℕ → X | ¬ ∀ i : Fin n, p0 (x (i : ℕ)) ≠ 0}
          = ⋃ i : Fin n, {x : ℕ → X | p0 (x (i : ℕ)) = 0} := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_iUnion]
        constructor
        · intro h
          by_contra hc
          exact h fun i hi => hc ⟨i, hi⟩
        · rintro ⟨i, hi⟩ h
          exact h i hi
      rw [MeasureTheory.ae_iff, hcompl]
      exact hunion
    have hcyl_eq : ∀ (n : ℕ),
        Measure.pi (fun _ : Fin n => P.toMeasure)
          = Measure.map (fun x : ℕ → X => fun i : Fin n => x (i : ℕ)) (truthLaw P.toMeasure) := by
      intro n
      refine Measure.pi_eq (fun s hs => ?_)
      have hT : Measurable (fun x : ℕ → X => fun i : Fin n => x (i : ℕ)) := by
        rw [measurable_pi_iff]
        exact fun i => measurable_pi_apply (i : ℕ)
      have hS : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
      rw [Measure.map_apply hT hS]
      have hset : (fun x : ℕ → X => fun i : Fin n => x (i : ℕ)) ⁻¹' (Set.univ.pi s)
          = Set.pi (((Finset.range n : Finset ℕ)) : Set ℕ)
              (fun k => if h : k < n then s ⟨k, h⟩ else Set.univ) := by
        ext x
        simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Finset.mem_range]
        constructor
        · intro hx k hk
          rw [dif_pos hk]
          exact hx ⟨k, hk⟩ (Set.mem_univ _)
        · intro hx i _
          have h := hx (i : ℕ) i.isLt
          rw [dif_pos i.isLt] at h
          exact h
      rw [hset]
      simp only [truthLaw]
      rw [Measure.infinitePi_pi]
      · refine Finset.prod_bij
          (fun (k : ℕ) (hk : k ∈ Finset.range n) => (⟨k, Finset.mem_range.mp hk⟩ : Fin n))
          ?_ ?_ ?_ ?_
        · intro a _
          exact Finset.mem_univ _
        · intro a₁ _ a₂ _ h
          simpa using h
        · intro b _
          exact ⟨(b : ℕ), Finset.mem_range.mpr b.isLt, rfl⟩
        · intro a ha
          simp only [dif_pos (Finset.mem_range.mp ha)]
      · intro k _
        by_cases h : k < n
        · rw [dif_pos h]
          exact hs ⟨k, h⟩
        · rw [dif_neg h]
          exact MeasurableSet.univ
    have htransfer : ∀ (n : ℕ) (S : Set (Fin n → X)), MeasurableSet S →
        truthLaw P.toMeasure {x : ℕ → X | (fun i : Fin n => x (i : ℕ)) ∈ S}
          = (Measure.pi (fun _ : Fin n => P.toMeasure)) S := by
      intro n S hS
      have hT : Measurable (fun x : ℕ → X => fun i : Fin n => x (i : ℕ)) := by
        rw [measurable_pi_iff]
        exact fun i => measurable_pi_apply (i : ℕ)
      rw [hcyl_eq n, Measure.map_apply hT hS]
      rfl
    have htest_meas : ∀ (n : ℕ), MeasurableSet {y : Fin n → X |
        ε₀ / 2 ≤ ⨆ j : Fin r, |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (y i))
          - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure|} := by
      intro n
      have hF : ∀ j : Fin r, Measurable (fun y : Fin n → X =>
          (n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (y i))
            - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure) := by
        intro j
        have h1 : Measurable (fun y : Fin n → X => ∑ i : Fin n, (ψ j : X → ℝ) (y i)) :=
          Finset.measurable_sum _ (fun i _ => (hψ_cont j).measurable.comp (measurable_pi_apply i))
        exact (measurable_const.mul h1).sub measurable_const
      have hle_sup : ∀ (y : Fin n → X) (j : Fin r),
          |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (y i))
              - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure|
            ≤ ⨆ j : Fin r, |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (y i))
              - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure| := by
        intro y j
        have hbdd : BddAbove (Set.range fun j : Fin r =>
            |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (y i))
              - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure|) := by
          have hf : (Set.range fun j : Fin r =>
              |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (y i))
                - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure|).Finite := by
            have h := (Set.finite_univ (α := Fin r)).image (fun j : Fin r =>
              |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (y i))
                - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure|)
            simpa using h
          exact hf.bddAbove
        exact le_ciSup hbdd j
      have habs : ∀ (j : Fin r) (q : ℚ), MeasurableSet {y : Fin n → X |
          |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (y i))
            - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure| ≤ (q : ℝ)} := by
        intro j q
        have hu : {y : Fin n → X |
              |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (y i))
                - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure| ≤ (q : ℝ)}
            = {y : Fin n → X | -(q : ℝ) ≤ (n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (y i))
                - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure}
              ∩ {y : Fin n → X | (n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (y i))
                - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure ≤ (q : ℝ)} := by
          ext y
          simp only [Set.mem_setOf_eq, Set.mem_inter_iff, abs_le]
        rw [hu]
        exact MeasurableSet.inter (measurableSet_le measurable_const (hF j))
          (measurableSet_le (hF j) measurable_const)
      have hset : {y : Fin n → X | (⨆ j : Fin r,
            |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (y i))
              - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure|) < ε₀ / 2}
          = ⋃ (q : ℚ), ({y : Fin n → X | ∀ j : Fin r,
              |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (y i))
                - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure| ≤ (q : ℝ)}
            ∩ {y : Fin n → X | (q : ℝ) < ε₀ / 2}) := by
        ext y
        simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
        constructor
        · intro h
          obtain ⟨q, h1, h2⟩ := exists_rat_btwn h
          exact ⟨q, fun j => le_of_lt (lt_of_le_of_lt (hle_sup y j) h1), h2⟩
        · rintro ⟨q, hle, hq⟩
          have h1 : (⨆ j : Fin r, |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (y i))
              - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure|) ≤ max (q : ℝ) 0 :=
            Real.iSup_le (fun j => le_trans (hle j) (le_max_left _ _)) (le_max_right _ _)
          have h2 : max (q : ℝ) 0 < ε₀ / 2 := max_lt hq hε₀2
          linarith
      have hcompl : {y : Fin n → X | ε₀ / 2 ≤ ⨆ j : Fin r,
            |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (y i))
              - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure|}
          = {y : Fin n → X | (⨆ j : Fin r,
            |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (y i))
              - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure|) < ε₀ / 2}ᶜ := by
        ext y
        simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
      rw [hcompl, hset]
      refine MeasurableSet.compl ?_
      refine MeasurableSet.iUnion (fun q : ℚ => ?_)
      have hbase : MeasurableSet {y : Fin n → X | ∀ j : Fin r,
          |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (y i))
            - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure| ≤ (q : ℝ)} := by
        have he : {y : Fin n → X | ∀ j : Fin r,
              |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (y i))
                - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure| ≤ (q : ℝ)}
            = ⋂ j ∈ Finset.univ, {y : Fin n → X |
                |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (y i))
                  - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure| ≤ (q : ℝ)} := by
          ext y
          simp
        rw [he]
        exact Finset.measurableSet_biInter _ (fun j _ => habs j q)
      by_cases hq : (q : ℝ) < ε₀ / 2
      · have h1 : {y : Fin n → X | (q : ℝ) < ε₀ / 2} = Set.univ := by
          ext y
          simp [hq]
        rw [h1, Set.inter_univ]
        exact hbase
      · have h1 : {y : Fin n → X | (q : ℝ) < ε₀ / 2} = (∅ : Set (Fin n → X)) := by
          ext y
          simp [hq]
        rw [h1, Set.inter_empty]
        exact MeasurableSet.empty
    have hTypeI' : ∀ (n : ℕ), 0 < n →
        truthLaw P.toMeasure {x : ℕ → X | ε₀ / 2 ≤ ⨆ j : Fin r,
            |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (x (i : ℕ)))
              - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure|}
          ≤ ENNReal.ofReal (2 * (r : ℝ) * Real.exp (-(n : ℝ) * c)) := by
      intro n hn
      calc truthLaw P.toMeasure {x : ℕ → X | ε₀ / 2 ≤ ⨆ j : Fin r,
            |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (x (i : ℕ)))
              - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure|}
          = truthLaw P.toMeasure {x : ℕ → X | (fun i : Fin n => x (i : ℕ)) ∈
              {y : Fin n → X | ε₀ / 2 ≤ ⨆ j : Fin r,
                |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (y i))
                  - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure|}} := rfl
        _ = (Measure.pi (fun _ : Fin n => P.toMeasure))
              {y : Fin n → X | ε₀ / 2 ≤ ⨆ j : Fin r,
                |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (y i))
                  - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure|} :=
            htransfer n _ (htest_meas n)
        _ ≤ ENNReal.ofReal (2 * (r : ℝ) * Real.exp (-(n : ℝ) * c)) := hTypeI n hn
    have hNum_le : ∀ (n : ℕ), 0 < n →
        ∫⁻ x : Fin n → X,
            (if (⨆ j : Fin r, |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (x i))
                  - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure| < ε₀ / 2)
              then ∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
                Set.indicator {ξ : ProbabilityMeasure Θ × (ℕ → Θ) |
                    (Set.range (fun i : Fin n => ξ.2 (i : ℕ))).ncard < t}
                  (fun ξ => ∏ i : Fin n,
                    (ENNReal.ofReal (k (ξ.2 (i : ℕ)) (x i)) * (p0 (x i))⁻¹)) ξ ∂M.latentLaw
              else 0)
          ∂(Measure.pi (fun _ : Fin n => P.toMeasure))
          ≤ ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * c)) := by
      intro n hn
      refine le_trans (hNum_bound n hn) ?_
      calc ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * c)) *
            M.latentLaw {ξ : ProbabilityMeasure Θ × (ℕ → Θ) |
              (Set.range (fun i : Fin n => ξ.2 (i : ℕ))).ncard < t}
          ≤ ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * c)) * 1 := by
            gcongr
            exact hLam_le_one _
        _ = ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * c)) := mul_one _
    have htarget_subset : ∀ (n : ℕ),
        {x : ℕ → X | ε < (posteriorProb M k t n (fun i : Fin n => x (i : ℕ))).toReal}
          ⊆ {x : ℕ → X |
              ENNReal.ofReal ε < posteriorProb M k t n (fun i : Fin n => x (i : ℕ))} := by
      intro n x hx
      simp only [Set.mem_setOf_eq] at hx
      by_contra hcon
      have h1 : posteriorProb M k t n (fun i : Fin n => x (i : ℕ)) ≤ ENNReal.ofReal ε :=
        not_lt.1 hcon
      have h2 : (posteriorProb M k t n (fun i : Fin n => x (i : ℕ))).toReal ≤ ε := by
        have h3 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
        rwa [ENNReal.toReal_ofReal hε.le] at h3
      linarith
    have hNum'_eq : ∀ (n : ℕ) (x : Fin n → X),
        (∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
            Set.indicator {ξ : ProbabilityMeasure Θ × (ℕ → Θ) |
                (Set.range (fun i : Fin n => ξ.2 (i : ℕ))).ncard < t}
              (fun ξ => ∏ i : Fin n,
                (ENNReal.ofReal (k (ξ.2 (i : ℕ)) (x i)) * (p0 (x i))⁻¹)) ξ ∂M.latentLaw)
          = (∏ i : Fin n, (p0 (x i))⁻¹) *
            (∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
              Set.indicator {ξ : ProbabilityMeasure Θ × (ℕ → Θ) |
                  (Set.range (fun i : Fin n => ξ.2 (i : ℕ))).ncard < t}
                (fun ξ => ∏ i : Fin n,
                  ENNReal.ofReal (k (ξ.2 (i : ℕ)) (x i))) ξ ∂M.latentLaw) := by
      intro n x
      have hp : ∀ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
          (∏ i : Fin n, (ENNReal.ofReal (k (ξ.2 (i : ℕ)) (x i)) * (p0 (x i))⁻¹))
            = (∏ i : Fin n, (p0 (x i))⁻¹) *
              (∏ i : Fin n, ENNReal.ofReal (k (ξ.2 (i : ℕ)) (x i))) := by
        intro ξ
        rw [Finset.prod_mul_distrib]
        exact mul_comm _ _
      have hA : MeasurableSet {ξ : ProbabilityMeasure Θ × (ℕ → Θ) |
          (Set.range (fun i : Fin n => ξ.2 (i : ℕ))).ncard < t} :=
        statopia_math_node_4133567021_cdc336c6 n t
      have hprod : Measurable (fun ξ : ProbabilityMeasure Θ × (ℕ → Θ) =>
          ∏ i : Fin n, ENNReal.ofReal (k (ξ.2 (i : ℕ)) (x i))) := by
        refine Finset.measurable_prod _ (fun i _ => ?_)
        have h1 : Measurable (fun ξ : ProbabilityMeasure Θ × (ℕ → Θ) =>
            Function.uncurry k (ξ.2 (i : ℕ), x i)) :=
          hk_meas.comp (((measurable_pi_apply (i : ℕ)).comp measurable_snd).prodMk measurable_const)
        simpa [Function.uncurry] using ENNReal.measurable_ofReal.comp h1
      simp only [lintegral_indicator hA, hp]
      rw [lintegral_const_mul]
      exact hprod
    have hW_eq : ∀ (n : ℕ) (x : Fin n → X),
        (∫⁻ h : X → ℝ≥0∞, ∏ i : Fin n, (h (x i) * (p0 (x i))⁻¹) ∂
            (M.latentLaw.map (fun ξ : ProbabilityMeasure Θ × (ℕ → Θ) => dpmDensity k ξ.1)))
          = (∏ i : Fin n, (p0 (x i))⁻¹) *
            (∫⁻ h : X → ℝ≥0∞, ∏ i : Fin n, h (x i) ∂
              (M.latentLaw.map (fun ξ : ProbabilityMeasure Θ × (ℕ → Θ) => dpmDensity k ξ.1))) := by
      intro n x
      have hpt : ∀ h : X → ℝ≥0∞,
          (∏ i : Fin n, (h (x i) * (p0 (x i))⁻¹))
            = (∏ i : Fin n, (p0 (x i))⁻¹) * (∏ i : Fin n, h (x i)) := by
        intro h
        rw [Finset.prod_mul_distrib]
        exact mul_comm _ _
      have hprod : Measurable (fun h : X → ℝ≥0∞ => ∏ i : Fin n, h (x i)) :=
        Finset.measurable_prod _ (fun i _ => measurable_pi_apply (x i))
      simp only [hpt]
      rw [lintegral_const_mul]
      exact hprod
    have hlin_map : ∀ (n : ℕ) (f : (Fin n → X) → ℝ≥0∞), Measurable f →
        ∫⁻ y : Fin n → X, f y ∂(Measure.pi (fun _ : Fin n => P.toMeasure))
          = ∫⁻ x : ℕ → X, f (fun i : Fin n => x (i : ℕ)) ∂truthLaw P.toMeasure := by
      intro n f hf
      have hT : Measurable (fun x : ℕ → X => fun i : Fin n => x (i : ℕ)) := by
        rw [measurable_pi_iff]
        exact fun i => measurable_pi_apply (i : ℕ)
      rw [hcyl_eq n, lintegral_map hf hT]
    have hSqueeze : ∀ (f g : ℕ → ℝ≥0∞), (∀ n, f n ≤ g n) →
        Tendsto g atTop (𝓝 0) → Tendsto f atTop (𝓝 0) := by
      intro f g hle hg
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg
        (fun n => zero_le (f n)) hle
    have hExpLim : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ) * c)) atTop (𝓝 0) := by
      have hp : Tendsto (fun n : ℕ => Real.exp (-c) ^ n) atTop (𝓝 0) := by
        refine tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt (Real.exp_pos _)) ?_
        rw [Real.exp_lt_one_iff]
        linarith
      refine hp.congr (fun n => ?_)
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hTypeILim :
        Tendsto (fun n : ℕ => ENNReal.ofReal (2 * (r : ℝ) * Real.exp (-(n : ℝ) * c)))
          atTop (𝓝 0) := by
      have hmul : Tendsto (fun n : ℕ => 2 * (r : ℝ) * Real.exp (-(n : ℝ) * c))
          atTop (𝓝 0) := by
        simpa using hExpLim.const_mul (2 * (r : ℝ))
      have h := (ENNReal.continuous_ofReal.tendsto 0).comp hmul
      simpa only [Function.comp_apply, ENNReal.ofReal_zero] using h
    have hMarkov : ∀ (f : (ℕ → X) → ℝ≥0∞), Measurable f → ∀ a : ℝ≥0∞,
        a * truthLaw P.toMeasure {x | a ≤ f x} ≤ ∫⁻ x, f x ∂truthLaw P.toMeasure := by
      intro f hf a
      have hs : MeasurableSet {x : ℕ → X | a ≤ f x} := measurableSet_le measurable_const hf
      calc a * truthLaw P.toMeasure {x : ℕ → X | a ≤ f x}
          = ∫⁻ x : ℕ → X,
              Set.indicator {x : ℕ → X | a ≤ f x} (fun _ => a) x ∂truthLaw P.toMeasure := by
            rw [lintegral_indicator hs, lintegral_const]
            simp
        _ ≤ ∫⁻ x : ℕ → X, f x ∂truthLaw P.toMeasure := by
            refine lintegral_mono (fun x => ?_)
            by_cases hx : x ∈ {x : ℕ → X | a ≤ f x}
            · rw [Set.indicator_apply, if_pos hx]
              exact hx
            · simp [hx]
    have hp0_ne_top : ∀ x : X, p0 x ≠ ⊤ := fun x => ENNReal.ofReal_ne_top
    have hW_den : ∀ (n : ℕ) (x : Fin n → X),
        (∫⁻ h : X → ℝ≥0∞, ∏ i : Fin n, (h (x i) * (p0 (x i))⁻¹) ∂
            (M.latentLaw.map (fun ξ : ProbabilityMeasure Θ × (ℕ → Θ) => dpmDensity k ξ.1)))
          = (∏ i : Fin n, (p0 (x i))⁻¹) *
            (∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
              ∏ i : Fin n, ENNReal.ofReal (k (ξ.2 (i : ℕ)) (x i)) ∂M.latentLaw) := by
      intro n x
      rw [hW_eq n x, ← hDen_eq n x]
    have hdiv_cancel : ∀ (a b cd : ℝ≥0∞), cd ≠ 0 → cd ≠ ⊤ →
        a / b = (cd * a) / (cd * b) := by
      intro a b cd h0 hT
      have hb : cd⁻¹ * cd = 1 := ENNReal.inv_mul_cancel h0 hT
      rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
        ENNReal.mul_inv (Or.inl h0) (Or.inl hT)]
      calc b⁻¹ * a = (cd⁻¹ * cd) * (b⁻¹ * a) := by rw [hb, one_mul]
        _ = (cd⁻¹ * b⁻¹) * (cd * a) := mul_mul_mul_comm _ _ _ _
    have hc_facts : ∀ (n : ℕ) (x : Fin n → X), (∀ i : Fin n, p0 (x i) ≠ 0) →
        (∏ i : Fin n, (p0 (x i))⁻¹) ≠ 0 ∧ (∏ i : Fin n, (p0 (x i))⁻¹) ≠ ⊤ := by
      intro n x hpos
      constructor
      · refine Finset.prod_ne_zero_iff.2 (fun i _ => ?_)
        intro h
        exact hp0_ne_top _ (ENNReal.inv_eq_zero.mp h)
      · refine ENNReal.prod_ne_top (fun i _ => ?_)
        intro h
        exact hpos i (ENNReal.inv_eq_top.mp h)
    have hind : ∀ (n : ℕ) (g : (ProbabilityMeasure Θ × (ℕ → Θ)) → ℝ≥0∞),
        (∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
          Set.indicator {ξ : ProbabilityMeasure Θ × (ℕ → Θ) |
              (Set.range (fun i : Fin n => ξ.2 (i : ℕ))).ncard < t} g ξ ∂M.latentLaw)
          = ∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
              (if clusterCount ξ.2 n < t then g ξ else 0) ∂M.latentLaw := by
      intro n g
      refine lintegral_congr (fun ξ => ?_)
      by_cases h : clusterCount ξ.2 n < t
      · have hm : ξ ∈ {ζ : ProbabilityMeasure Θ × (ℕ → Θ) |
            (Set.range (fun i : Fin n => ζ.2 (i : ℕ))).ncard < t} := h
        rw [Set.indicator_apply, if_pos hm, if_pos h]
      · have hm : ξ ∉ {ζ : ProbabilityMeasure Θ × (ℕ → Θ) |
            (Set.range (fun i : Fin n => ζ.2 (i : ℕ))).ncard < t} := h
        rw [Set.indicator_apply, if_neg hm, if_neg h]
    have hNum'_eq_if : ∀ (n : ℕ) (y : Fin n → X),
        (∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
            (if clusterCount ξ.2 n < t then
              ∏ i : Fin n, (ENNReal.ofReal (k (ξ.2 (i : ℕ)) (y i)) * (p0 (y i))⁻¹)
              else 0) ∂M.latentLaw)
          = (∏ i : Fin n, (p0 (y i))⁻¹) *
            (∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
              (if clusterCount ξ.2 n < t then
                ∏ i : Fin n, ENNReal.ofReal (k (ξ.2 (i : ℕ)) (y i)) else 0) ∂M.latentLaw) := by
      intro n y
      rw [← hind n (fun ξ => ∏ i : Fin n,
            (ENNReal.ofReal (k (ξ.2 (i : ℕ)) (y i)) * (p0 (y i))⁻¹)),
          ← hind n (fun ξ => ∏ i : Fin n, ENNReal.ofReal (k (ξ.2 (i : ℕ)) (y i)))]
      exact hNum'_eq n y
    have hcancel : ∀ (n : ℕ), ∀ᵐ x ∂(truthLaw P.toMeasure),
        posteriorProb M k t n (fun i : Fin n => x (i : ℕ))
          = (∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
              (if clusterCount ξ.2 n < t then
                ∏ i : Fin n,
                  (ENNReal.ofReal (k (ξ.2 (i : ℕ)) (x (i : ℕ))) * (p0 (x (i : ℕ)))⁻¹)
                else 0) ∂M.latentLaw)
            / (∫⁻ h : X → ℝ≥0∞, ∏ i : Fin n, (h (x (i : ℕ)) * (p0 (x (i : ℕ)))⁻¹) ∂
                (M.latentLaw.map (fun ξ : ProbabilityMeasure Θ × (ℕ → Θ) => dpmDensity k ξ.1))) := by
      intro n
      filter_upwards [hae_pos n] with x hx
      have hcf := hc_facts n (fun i : Fin n => x (i : ℕ)) hx
      simp only [posteriorProb]
      rw [hNum'_eq_if n (fun i : Fin n => x (i : ℕ)),
        hW_den n (fun i : Fin n => x (i : ℕ))]
      exact hdiv_cancel _ _ _ hcf.1 hcf.2
    have htruth_univ : truthLaw P.toMeasure Set.univ = 1 := by
      simp only [truthLaw]
      have hpi : (((∅ : Finset ℕ)) : Set ℕ).pi (fun _ : ℕ => (Set.univ : Set X)) = Set.univ := by
        ext x
        simp
      rw [← hpi,
        Measure.infinitePi_pi (fun _ : ℕ => P.toMeasure) (t := fun _ : ℕ => (Set.univ : Set X))
          (s := ∅) (fun i _ => MeasurableSet.univ)]
      simp
    have htruth_le_one : ∀ s : Set (ℕ → X), truthLaw P.toMeasure s ≤ 1 := by
      intro s
      calc truthLaw P.toMeasure s ≤ truthLaw P.toMeasure Set.univ :=
            measure_mono (Set.subset_univ _)
        _ = 1 := htruth_univ
    have hTypeI_tendsto : Tendsto (fun n : ℕ => truthLaw P.toMeasure
        {x : ℕ → X | ε₀ / 2 ≤ ⨆ j : Fin r,
          |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (x (i : ℕ)))
            - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure|}) atTop (𝓝 0) := by
      refine hSqueeze _ (fun n : ℕ =>
        ENNReal.ofReal (2 * (r : ℝ) * Real.exp (-(n : ℝ) * c))) ?_ hTypeILim
      intro n
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        refine le_trans (htruth_le_one _) ?_
        have hreal : (1 : ℝ) ≤ 2 * (r : ℝ) * Real.exp (-(((0 : ℕ)) : ℝ) * c) := by
          have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
          simp only [Nat.cast_zero, neg_zero, zero_mul, Real.exp_zero, mul_one]
          linarith
        exact ENNReal.ofReal_one ▸ ENNReal.ofReal_le_ofReal hreal
      · exact hTypeI' n hn
    have hpost_le : ∀ (n : ℕ) (δ e : ℝ≥0∞), 0 < δ → 0 < e →
        ∀ᵐ x ∂(truthLaw P.toMeasure),
          e ≤ (∫⁻ h : X → ℝ≥0∞, ∏ i : Fin n,
              (h (x (i : ℕ)) * (p0 (x (i : ℕ)))⁻¹) ∂
                (M.latentLaw.map (fun ξ : ProbabilityMeasure Θ × (ℕ → Θ) => dpmDensity k ξ.1))) →
          (∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
              (if clusterCount ξ.2 n < t then
                ∏ i : Fin n,
                  (ENNReal.ofReal (k (ξ.2 (i : ℕ)) (x (i : ℕ))) * (p0 (x (i : ℕ)))⁻¹)
                else 0) ∂M.latentLaw)
            ≤ δ * (∫⁻ h : X → ℝ≥0∞, ∏ i : Fin n,
              (h (x (i : ℕ)) * (p0 (x (i : ℕ)))⁻¹) ∂
                (M.latentLaw.map (fun ξ : ProbabilityMeasure Θ × (ℕ → Θ) => dpmDensity k ξ.1))) →
          posteriorProb M k t n (fun i : Fin n => x (i : ℕ)) ≤ δ := by
      intro n δ e hδ he
      filter_upwards [hcancel n] with x hx hW hNum
      rw [hx]
      refine (ENNReal.div_le_iff_le_mul (Or.inl ?_) (Or.inr (ne_of_gt hδ))).2 hNum
      exact ne_of_gt (lt_of_lt_of_le he hW)
    have hinv_meas : Measurable (fun z : ℝ≥0∞ => z⁻¹) := by
      simpa using Measurable.inv measurable_id
    have hNum_meas : ∀ (n : ℕ), Measurable (fun y : Fin n → X =>
        ∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
          (if clusterCount ξ.2 n < t then
            ∏ i : Fin n, (ENNReal.ofReal (k (ξ.2 (i : ℕ)) (y i)) * (p0 (y i))⁻¹)
            else 0) ∂M.latentLaw) := by
      intro n
      have hA : MeasurableSet {ξ : ProbabilityMeasure Θ × (ℕ → Θ) |
          (Set.range (fun i : Fin n => ξ.2 (i : ℕ))).ncard < t} :=
        statopia_math_node_4133567021_cdc336c6 n t
      have hjoint : Measurable (Function.uncurry (fun (ξ : ProbabilityMeasure Θ × (ℕ → Θ))
          (y : Fin n → X) => ∏ i : Fin n,
            (ENNReal.ofReal (k (ξ.2 (i : ℕ)) (y i)) * (p0 (y i))⁻¹))) := by
        refine Finset.measurable_prod _ (fun i _ => ?_)
        have hk : Measurable (fun p : (ProbabilityMeasure Θ × (ℕ → Θ)) × (Fin n → X) =>
            Function.uncurry k (p.1.2 (i : ℕ), p.2 i)) :=
          hk_meas.comp
            (((measurable_pi_apply (i : ℕ)).comp (measurable_snd.comp measurable_fst)).prodMk
              ((measurable_pi_apply i).comp measurable_snd))
        have hp0i : Measurable (fun p : (ProbabilityMeasure Θ × (ℕ → Θ)) × (Fin n → X) =>
            p0 (p.2 i)) :=
          hp0_meas.comp ((measurable_pi_apply i).comp measurable_snd)
        have hinv : Measurable (fun p : (ProbabilityMeasure Θ × (ℕ → Θ)) × (Fin n → X) =>
            (p0 (p.2 i))⁻¹) := hp0i.inv
        simpa [Function.uncurry] using (ENNReal.measurable_ofReal.comp hk).mul hinv
      have hres : Measurable (fun y : Fin n → X =>
          ∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
            ∏ i : Fin n, (ENNReal.ofReal (k (ξ.2 (i : ℕ)) (y i)) * (p0 (y i))⁻¹)
            ∂(M.latentLaw.restrict {ξ : ProbabilityMeasure Θ × (ℕ → Θ) |
              (Set.range (fun i : Fin n => ξ.2 (i : ℕ))).ncard < t})) :=
        hjoint.lintegral_prod_left
      have hfun : (fun y : Fin n → X =>
          ∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
            (if clusterCount ξ.2 n < t then
              ∏ i : Fin n, (ENNReal.ofReal (k (ξ.2 (i : ℕ)) (y i)) * (p0 (y i))⁻¹)
              else 0) ∂M.latentLaw)
          = (fun y : Fin n → X =>
              ∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
                ∏ i : Fin n, (ENNReal.ofReal (k (ξ.2 (i : ℕ)) (y i)) * (p0 (y i))⁻¹)
                ∂(M.latentLaw.restrict {ξ : ProbabilityMeasure Θ × (ℕ → Θ) |
                  (Set.range (fun i : Fin n => ξ.2 (i : ℕ))).ncard < t})) := by
        funext y
        rw [← hind n (fun ξ => ∏ i : Fin n,
          (ENNReal.ofReal (k (ξ.2 (i : ℕ)) (y i)) * (p0 (y i))⁻¹)), lintegral_indicator hA]
      rw [hfun]
      exact hres
    have hnum_meas_full : ∀ (n : ℕ), Measurable (fun y : Fin n → X =>
        (if (⨆ j : Fin r, |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (y i))
              - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure| < ε₀ / 2)
          then ∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
            (if clusterCount ξ.2 n < t then
              ∏ i : Fin n, (ENNReal.ofReal (k (ξ.2 (i : ℕ)) (y i)) * (p0 (y i))⁻¹)
              else 0) ∂M.latentLaw
          else 0)) := by
      intro n
      have hs : MeasurableSet {y : Fin n → X |
          (⨆ j : Fin r, |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (y i))
            - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure|) < ε₀ / 2} := by
        have h := (htest_meas n).compl
        simpa only [Set.compl_setOf, not_le] using h
      have hmain := hNum_meas n
      have hfun : (fun y : Fin n → X =>
            (if (⨆ j : Fin r, |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (y i))
                  - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure| < ε₀ / 2)
              then ∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
                (if clusterCount ξ.2 n < t then
                  ∏ i : Fin n, (ENNReal.ofReal (k (ξ.2 (i : ℕ)) (y i)) * (p0 (y i))⁻¹)
                  else 0) ∂M.latentLaw
              else 0))
          = Set.indicator {y : Fin n → X |
              (⨆ j : Fin r, |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (y i))
                - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure|) < ε₀ / 2}
            (fun y : Fin n → X => ∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
              (if clusterCount ξ.2 n < t then
                ∏ i : Fin n, (ENNReal.ofReal (k (ξ.2 (i : ℕ)) (y i)) * (p0 (y i))⁻¹)
                else 0) ∂M.latentLaw) := by
        funext y
        by_cases h : (⨆ j : Fin r, |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (y i))
            - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure|) < ε₀ / 2
        · have hm : y ∈ {ζ : Fin n → X |
              (⨆ j : Fin r, |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (ζ i))
                - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure|) < ε₀ / 2} := h
          rw [if_pos h, Set.indicator_apply, if_pos hm]
        · have hm : y ∉ {ζ : Fin n → X |
              (⨆ j : Fin r, |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (ζ i))
                - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure|) < ε₀ / 2} := h
          rw [if_neg h, Set.indicator_apply, if_neg hm]
      rw [hfun]
      exact Measurable.indicator hmain hs
    have hNum_transfer : ∀ (n : ℕ), 0 < n →
        ∫⁻ x : ℕ → X, (fun y : Fin n → X =>
          (if (⨆ j : Fin r, |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (y i))
                - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure| < ε₀ / 2)
              then ∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
                (if clusterCount ξ.2 n < t then
                  ∏ i : Fin n, (ENNReal.ofReal (k (ξ.2 (i : ℕ)) (y i)) * (p0 (y i))⁻¹)
                  else 0) ∂M.latentLaw
              else 0)) (fun i : Fin n => x (i : ℕ)) ∂truthLaw P.toMeasure
          ≤ ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * c)) := by
      intro n hn
      have hkey : (∫⁻ y : Fin n → X, (fun y : Fin n → X =>
            (if (⨆ j : Fin r, |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (y i))
                  - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure| < ε₀ / 2)
                then ∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
                  (if clusterCount ξ.2 n < t then
                    ∏ i : Fin n, (ENNReal.ofReal (k (ξ.2 (i : ℕ)) (y i)) * (p0 (y i))⁻¹)
                    else 0) ∂M.latentLaw
                else 0)) y ∂(Measure.pi (fun _ : Fin n => P.toMeasure)))
          = ∫⁻ y : Fin n → X,
              (if (⨆ j : Fin r, |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (y i))
                    - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure| < ε₀ / 2)
                then ∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
                  Set.indicator {ξ : ProbabilityMeasure Θ × (ℕ → Θ) |
                      (Set.range (fun i : Fin n => ξ.2 (i : ℕ))).ncard < t}
                    (fun ξ => ∏ i : Fin n,
                      (ENNReal.ofReal (k (ξ.2 (i : ℕ)) (y i)) * (p0 (y i))⁻¹)) ξ ∂M.latentLaw
                else 0) ∂(Measure.pi (fun _ : Fin n => P.toMeasure)) := by
        refine lintegral_congr (fun y => ?_)
        by_cases h : (⨆ j : Fin r, |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (y i))
            - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure|) < ε₀ / 2
        · rw [if_pos h, if_pos h, ← hind n (fun ξ => ∏ i : Fin n,
              (ENNReal.ofReal (k (ξ.2 (i : ℕ)) (y i)) * (p0 (y i))⁻¹))]
        · rw [if_neg h, if_neg h]
      rw [← hlin_map n _ (hnum_meas_full n)]
      rw [hkey]
      exact hNum_le n hn
    have hNum_markov : ∀ (n : ℕ), 0 < n → ∀ a : ℝ≥0∞,
        a * truthLaw P.toMeasure {x : ℕ → X | a ≤ (fun y : Fin n → X =>
          (if (⨆ j : Fin r, |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (y i))
                - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure| < ε₀ / 2)
              then ∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
                (if clusterCount ξ.2 n < t then
                  ∏ i : Fin n, (ENNReal.ofReal (k (ξ.2 (i : ℕ)) (y i)) * (p0 (y i))⁻¹)
                  else 0) ∂M.latentLaw
              else 0)) (fun i : Fin n => x (i : ℕ))}
          ≤ ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * c)) := by
      intro n hn a
      have hT : Measurable (fun x : ℕ → X => fun i : Fin n => x (i : ℕ)) := by
        rw [measurable_pi_iff]
        exact fun i => measurable_pi_apply (i : ℕ)
      exact le_trans (hMarkov _ ((hnum_meas_full n).comp hT) a) (hNum_transfer n hn)
    have hunion_incl : ∀ (n : ℕ) (δ : ℝ≥0∞), 0 < δ →
        ∀ᵐ x ∂(truthLaw P.toMeasure),
          δ < posteriorProb M k t n (fun i : Fin n => x (i : ℕ)) →
            (ε₀ / 2 ≤ ⨆ j : Fin r,
                |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (x (i : ℕ)))
                  - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure|)
            ∨ (∫⁻ h : X → ℝ≥0∞, ∏ i : Fin n,
                  (h (x (i : ℕ)) * (p0 (x (i : ℕ)))⁻¹) ∂
                  (M.latentLaw.map (fun ξ : ProbabilityMeasure Θ × (ℕ → Θ) => dpmDensity k ξ.1)))
                < ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 4)))
            ∨ δ * ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 4)))
                < (if (⨆ j : Fin r,
                      |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (x (i : ℕ)))
                        - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure|) < ε₀ / 2
                    then ∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
                      (if clusterCount ξ.2 n < t then
                        ∏ i : Fin n,
                          (ENNReal.ofReal (k (ξ.2 (i : ℕ)) (x (i : ℕ))) * (p0 (x (i : ℕ)))⁻¹)
                        else 0) ∂M.latentLaw
                    else 0) := by
      intro n δ hδ
      have hEpos : 0 < ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 4))) :=
        ENNReal.ofReal_pos.mpr (Real.exp_pos _)
      filter_upwards [hpost_le n δ (ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 4))))
        hδ hEpos] with x hx hxlt
      by_cases h1 : ε₀ / 2 ≤ ⨆ j : Fin r,
          |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (x (i : ℕ)))
            - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure|
      · exact Or.inl h1
      · by_cases h2 : (∫⁻ h : X → ℝ≥0∞, ∏ i : Fin n,
            (h (x (i : ℕ)) * (p0 (x (i : ℕ)))⁻¹) ∂
            (M.latentLaw.map (fun ξ : ProbabilityMeasure Θ × (ℕ → Θ) => dpmDensity k ξ.1)))
            < ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 4)))
        · exact Or.inr (Or.inl h2)
        · by_cases h3 : δ * ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 4)))
              < (if (⨆ j : Fin r,
                    |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (x (i : ℕ)))
                      - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure|) < ε₀ / 2
                  then ∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
                    (if clusterCount ξ.2 n < t then
                      ∏ i : Fin n,
                        (ENNReal.ofReal (k (ξ.2 (i : ℕ)) (x (i : ℕ))) * (p0 (x (i : ℕ)))⁻¹)
                      else 0) ∂M.latentLaw
                  else 0)
          · exact Or.inr (Or.inr h3)
          · exfalso
            have hsup : (⨆ j : Fin r,
                |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (x (i : ℕ)))
                  - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure|) < ε₀ / 2 := not_le.mp h1
            have hF : (if (⨆ j : Fin r,
                  |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (x (i : ℕ)))
                    - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure|) < ε₀ / 2
                then ∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
                  (if clusterCount ξ.2 n < t then
                    ∏ i : Fin n,
                      (ENNReal.ofReal (k (ξ.2 (i : ℕ)) (x (i : ℕ))) * (p0 (x (i : ℕ)))⁻¹)
                    else 0) ∂M.latentLaw
                else 0)
                = ∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
                  (if clusterCount ξ.2 n < t then
                    ∏ i : Fin n,
                      (ENNReal.ofReal (k (ξ.2 (i : ℕ)) (x (i : ℕ))) * (p0 (x (i : ℕ)))⁻¹)
                    else 0) ∂M.latentLaw := if_pos hsup
            have hE_le_W : ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 4)))
                ≤ (∫⁻ h : X → ℝ≥0∞, ∏ i : Fin n,
                    (h (x (i : ℕ)) * (p0 (x (i : ℕ)))⁻¹) ∂
                    (M.latentLaw.map (fun ξ : ProbabilityMeasure Θ × (ℕ → Θ) => dpmDensity k ξ.1))) :=
              not_lt.mp h2
            have hNum_le_E : (∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
                  (if clusterCount ξ.2 n < t then
                    ∏ i : Fin n,
                      (ENNReal.ofReal (k (ξ.2 (i : ℕ)) (x (i : ℕ))) * (p0 (x (i : ℕ)))⁻¹)
                    else 0) ∂M.latentLaw)
                ≤ δ * ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 4))) := by
              have h := not_lt.mp h3
              rwa [hF] at h
            have hNum : (∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
                  (if clusterCount ξ.2 n < t then
                    ∏ i : Fin n,
                      (ENNReal.ofReal (k (ξ.2 (i : ℕ)) (x (i : ℕ))) * (p0 (x (i : ℕ)))⁻¹)
                    else 0) ∂M.latentLaw)
                ≤ δ * (∫⁻ h : X → ℝ≥0∞, ∏ i : Fin n,
                    (h (x (i : ℕ)) * (p0 (x (i : ℕ)))⁻¹) ∂
                    (M.latentLaw.map (fun ξ : ProbabilityMeasure Θ × (ℕ → Θ) => dpmDensity k ξ.1))) :=
              le_trans hNum_le_E (mul_le_mul_left' hE_le_W δ)
            exact absurd (hx hE_le_W hNum) (not_le.mpr hxlt)
    have hS3_markov : ∀ (n : ℕ), 0 < n → ∀ δ : ℝ≥0∞,
        (δ * ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 4))))
          * truthLaw P.toMeasure {x : ℕ → X |
              δ * ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 4)))
                < (if (⨆ j : Fin r,
                      |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (x (i : ℕ)))
                        - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure|) < ε₀ / 2
                    then ∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
                      (if clusterCount ξ.2 n < t then
                        ∏ i : Fin n,
                          (ENNReal.ofReal (k (ξ.2 (i : ℕ)) (x (i : ℕ))) * (p0 (x (i : ℕ)))⁻¹)
                        else 0) ∂M.latentLaw
                    else 0)}
          ≤ ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * c)) := by
      intro n hn δ
      have hmono : truthLaw P.toMeasure {x : ℕ → X |
            δ * ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 4)))
              < (if (⨆ j : Fin r,
                    |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (x (i : ℕ)))
                      - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure|) < ε₀ / 2
                  then ∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
                    (if clusterCount ξ.2 n < t then
                      ∏ i : Fin n,
                        (ENNReal.ofReal (k (ξ.2 (i : ℕ)) (x (i : ℕ))) * (p0 (x (i : ℕ)))⁻¹)
                      else 0) ∂M.latentLaw
                  else 0)}
          ≤ truthLaw P.toMeasure {x : ℕ → X |
              (δ * ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 4)))) ≤
                (fun y : Fin n → X =>
                  (if (⨆ j : Fin r, |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (y i))
                        - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure| < ε₀ / 2)
                    then ∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
                      (if clusterCount ξ.2 n < t then
                        ∏ i : Fin n, (ENNReal.ofReal (k (ξ.2 (i : ℕ)) (y i)) * (p0 (y i))⁻¹)
                        else 0) ∂M.latentLaw
                    else 0)) (fun i : Fin n => x (i : ℕ))} :=
        measure_mono (fun x hx => by
          simp only [Set.mem_setOf_eq] at hx ⊢
          exact le_of_lt hx)
      exact le_trans
        (mul_le_mul_left' hmono (δ * ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 4)))))
        (hNum_markov n hn (δ * ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 4)))))
    have hS3_prob : ∀ (n : ℕ), 0 < n → ∀ δ : ℝ≥0∞, 0 < δ → δ ≠ ⊤ →
        truthLaw P.toMeasure {x : ℕ → X |
            δ * ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 4)))
              < (if (⨆ j : Fin r,
                    |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (x (i : ℕ)))
                      - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure|) < ε₀ / 2
                  then ∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
                    (if clusterCount ξ.2 n < t then
                      ∏ i : Fin n,
                        (ENNReal.ofReal (k (ξ.2 (i : ℕ)) (x (i : ℕ))) * (p0 (x (i : ℕ)))⁻¹)
                      else 0) ∂M.latentLaw
                  else 0)}
          ≤ ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * c))
              / (δ * ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 4)))) := by
      intro n hn δ hδ hδT
      have hE0 : ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 4))) ≠ 0 :=
        ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
      refine (ENNReal.le_div_iff_mul_le (Or.inl (mul_ne_zero (ne_of_gt hδ) hE0))
        (Or.inr ENNReal.ofReal_ne_top)).2 ?_
      rw [mul_comm]
      exact hS3_markov n hn δ
    have hmeasure_ae_mono : ∀ (μ : Measure (ℕ → X)) (T U : Set (ℕ → X)),
        (∀ᵐ x ∂μ, x ∈ T → x ∈ U) → μ T ≤ μ U := by
      intro μ T U h
      have hN : μ {x : ℕ → X | ¬ (x ∈ T → x ∈ U)} = 0 := by
        have h' := h
        rwa [MeasureTheory.ae_iff] at h'
      calc μ T ≤ μ (U ∪ {x : ℕ → X | ¬ (x ∈ T → x ∈ U)}) := by
            refine measure_mono ?_
            intro x hx
            by_cases hxu : x ∈ U
            · exact Or.inl hxu
            · exact Or.inr (fun hxt => hxu (hxt hx))
        _ ≤ μ U + μ {x : ℕ → X | ¬ (x ∈ T → x ∈ U)} := measure_union_le _ _
        _ = μ U := by rw [hN, add_zero]
    have hunion_bound : ∀ (n : ℕ) (δ : ℝ≥0∞), 0 < δ →
        truthLaw P.toMeasure
            {x : ℕ → X | δ < posteriorProb M k t n (fun i : Fin n => x (i : ℕ))}
          ≤ (truthLaw P.toMeasure {x : ℕ → X | ε₀ / 2 ≤ ⨆ j : Fin r,
                |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (x (i : ℕ)))
                  - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure|}
              + truthLaw P.toMeasure {x : ℕ → X |
                  (∫⁻ h : X → ℝ≥0∞, ∏ i : Fin n,
                      (h (x (i : ℕ)) * (p0 (x (i : ℕ)))⁻¹) ∂
                      (M.latentLaw.map (fun ξ : ProbabilityMeasure Θ × (ℕ → Θ) => dpmDensity k ξ.1)))
                    < ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 4)))})
            + truthLaw P.toMeasure {x : ℕ → X |
                δ * ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 4)))
                  < (if (⨆ j : Fin r,
                        |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (x (i : ℕ)))
                          - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure|) < ε₀ / 2
                      then ∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
                        (if clusterCount ξ.2 n < t then
                          ∏ i : Fin n,
                            (ENNReal.ofReal (k (ξ.2 (i : ℕ)) (x (i : ℕ))) * (p0 (x (i : ℕ)))⁻¹)
                          else 0) ∂M.latentLaw
                      else 0)} := by
      intro n δ hδ
      have hU : ∀ᵐ x ∂(truthLaw P.toMeasure),
          x ∈ {x : ℕ → X | δ < posteriorProb M k t n (fun i : Fin n => x (i : ℕ))} →
            x ∈ (({x : ℕ → X | ε₀ / 2 ≤ ⨆ j : Fin r,
                    |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (x (i : ℕ)))
                      - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure|}
                  ∪ {x : ℕ → X |
                      (∫⁻ h : X → ℝ≥0∞, ∏ i : Fin n,
                          (h (x (i : ℕ)) * (p0 (x (i : ℕ)))⁻¹) ∂
                          (M.latentLaw.map
                            (fun ξ : ProbabilityMeasure Θ × (ℕ → Θ) => dpmDensity k ξ.1)))
                        < ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 4)))})
              ∪ {x : ℕ → X |
                  δ * ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 4)))
                    < (if (⨆ j : Fin r,
                          |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (x (i : ℕ)))
                            - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure|) < ε₀ / 2
                        then ∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
                          (if clusterCount ξ.2 n < t then
                            ∏ i : Fin n,
                              (ENNReal.ofReal (k (ξ.2 (i : ℕ)) (x (i : ℕ))) * (p0 (x (i : ℕ)))⁻¹)
                            else 0) ∂M.latentLaw
                        else 0)}) := by
        filter_upwards [hunion_incl n δ hδ] with x hx hxT
        simp only [Set.mem_setOf_eq, Set.mem_union] at hxT ⊢
        rcases hx hxT with h1 | h2 | h3
        · exact Or.inl (Or.inl h1)
        · exact Or.inl (Or.inr h2)
        · exact Or.inr h3
      have hunion3 : ∀ (ν : Measure (ℕ → X)) (s t u : Set (ℕ → X)),
          ν ((s ∪ t) ∪ u) ≤ (ν s + ν t) + ν u := by
        intro ν s t u
        calc ν ((s ∪ t) ∪ u) ≤ ν (s ∪ t) + ν u := measure_union_le _ _
          _ ≤ (ν s + ν t) + ν u := add_le_add (measure_union_le s t) le_rfl
      exact le_trans (hmeasure_ae_mono _ _ _ hU) (hunion3 _ _ _ _)
    have hc4_pos : 0 < c / 4 := by linarith
    have hexp3 : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ) * ((3 / 4) * c))) atTop (𝓝 0) := by
      have hp : Tendsto (fun n : ℕ => Real.exp (-((3 / 4) * c)) ^ n) atTop (𝓝 0) := by
        refine tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt (Real.exp_pos _)) ?_
        rw [Real.exp_lt_one_iff]
        linarith
      refine hp.congr (fun n => ?_)
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hexp3Lim : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (-(n : ℝ) * ((3 / 4) * c))))
        atTop (𝓝 0) := by
      have h := (ENNReal.continuous_ofReal.tendsto 0).comp hexp3
      simpa only [Function.comp_apply, ENNReal.ofReal_zero] using h
    have hexp3Lim2 : Tendsto (fun n : ℕ => ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * ((3 / 4) * c))))
        atTop (𝓝 0) := by
      have hmul : Tendsto (fun n : ℕ => 2 * Real.exp (-(n : ℝ) * ((3 / 4) * c)))
          atTop (𝓝 0) := by
        simpa using hexp3.const_mul 2
      have h := (ENNReal.continuous_ofReal.tendsto 0).comp hmul
      simpa only [Function.comp_apply, ENNReal.ofReal_zero] using h
    have hTwo_tendsto : Tendsto (fun n : ℕ =>
        truthLaw P.toMeasure {x : ℕ → X | ε₀ / 2 ≤ ⨆ j : Fin r,
            |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (x (i : ℕ)))
              - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure|}
        + ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * ((3 / 4) * c)))) atTop (𝓝 0) := by
      have h := hTypeI_tendsto.add hexp3Lim2
      simpa using h
    have hEn_pos : ∀ n : ℕ, 0 < ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 4))) :=
      fun n => ENNReal.ofReal_pos.mpr (Real.exp_pos _)
    have hEn_ne_zero : ∀ n : ℕ, ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 4))) ≠ 0 :=
      fun n => ne_of_gt (hEn_pos n)
    have hExpScaleLim : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 4))))
        atTop (𝓝 0) := by
      have hbase : Tendsto (fun n : ℕ => Real.exp (-(c / 4)) ^ n) atTop (𝓝 0) := by
        refine tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt (Real.exp_pos _)) ?_
        rw [Real.exp_lt_one_iff]
        linarith
      have hexp : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ) * (c / 4))) atTop (𝓝 0) := by
        refine hbase.congr (fun n => ?_)
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      have h := (ENNReal.continuous_ofReal.tendsto 0).comp hexp
      simpa only [Function.comp_apply, ENNReal.ofReal_zero] using h
    have hS3_ratio : ∀ (n : ℕ) (d : ℝ), 0 < d →
        (2 * Real.exp (-(n : ℝ) * c)) / (d * Real.exp (-(n : ℝ) * (c / 4)))
          = (2 / d) * Real.exp (-(n : ℝ) * ((3 / 4) * c)) := by
      intro n d hd
      have hsplit : Real.exp (-(n : ℝ) * c)
          = Real.exp (-(n : ℝ) * ((3 / 4) * c)) * Real.exp (-(n : ℝ) * (c / 4)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hsplit]
      have hB : Real.exp (-(n : ℝ) * (c / 4)) ≠ 0 := (Real.exp_pos _).ne'
      have hd0 : d ≠ 0 := hd.ne'
      have hdB : d * Real.exp (-(n : ℝ) * (c / 4)) ≠ 0 := mul_ne_zero hd0 hB
      field_simp
    have hS3_bound_lim : ∀ δ : ℝ≥0∞, 0 < δ → δ ≠ ⊤ →
        Tendsto (fun n : ℕ => ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * c))
            / (δ * ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 4))))) atTop (𝓝 0) := by
      intro δ hδ hδT
      have hδr : 0 < δ.toReal := by
        have h0 : (0:ℝ) ≤ δ.toReal := by
          have h := ENNReal.toReal_mono hδT hδ.le
          simpa using h
        exact lt_of_le_of_ne h0 (Ne.symm (ENNReal.toReal_ne_zero.mpr ⟨hδ.ne', hδT⟩))
      have hEq : (fun n : ℕ => ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * c))
            / (δ * ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 4)))))
          = fun n : ℕ => ENNReal.ofReal ((2 / δ.toReal)
              * Real.exp (-(n : ℝ) * ((3 / 4) * c))) := by
        funext n
        have hB : (0:ℝ) < Real.exp (-(n : ℝ) * (c / 4)) := Real.exp_pos _
        conv_lhs => rw [show δ = ENNReal.ofReal δ.toReal from
          (ENNReal.ofReal_toReal hδT).symm]
        rw [← ENNReal.ofReal_mul (le_of_lt hδr),
          ← ENNReal.ofReal_div_of_pos (mul_pos hδr hB), hS3_ratio n δ.toReal hδr]
      rw [hEq]
      have hreal : Tendsto (fun n : ℕ => (2 / δ.toReal)
          * Real.exp (-(n : ℝ) * ((3 / 4) * c))) atTop (𝓝 0) := by
        simpa using hexp3.const_mul (2 / δ.toReal)
      have h := (ENNReal.continuous_ofReal.tendsto 0).comp hreal
      simpa only [Function.comp_apply, ENNReal.ofReal_zero] using h
    have hS3_tendsto : Tendsto (fun n : ℕ => truthLaw P.toMeasure {x : ℕ → X |
        ENNReal.ofReal ε * ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 4)))
          < (if (⨆ j : Fin r,
                |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (x (i : ℕ)))
                  - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure|) < ε₀ / 2
              then ∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
                (if clusterCount ξ.2 n < t then
                  ∏ i : Fin n,
                    (ENNReal.ofReal (k (ξ.2 (i : ℕ)) (x (i : ℕ))) * (p0 (x (i : ℕ)))⁻¹)
                  else 0) ∂M.latentLaw
              else 0)}) atTop (𝓝 0) := by
      have hεT : (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
      have hεne : ENNReal.ofReal ε ≠ ⊤ := ENNReal.ofReal_ne_top
      refine hSqueeze _ (fun n : ℕ => if n = 0 then 1
          else ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * c))
            / (ENNReal.ofReal ε * ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 4))))) ?_ ?_
      · intro n
        rcases Nat.eq_zero_or_pos n with hn | hn
        · subst hn
          beta_reduce
          rw [if_pos rfl]
          exact htruth_le_one _
        · beta_reduce
          rw [if_neg (Nat.pos_iff_ne_zero.mp hn)]
          exact hS3_prob n hn (ENNReal.ofReal ε) hεT hεne
      · refine (hS3_bound_lim (ENNReal.ofReal ε) hεT hεne).congr' ?_
        filter_upwards [eventually_ge_atTop 1] with n hn
        beta_reduce
        rw [if_neg (by omega : ¬ (n = 0))]
    have hB_tendsto : Tendsto (fun n : ℕ => truthLaw P.toMeasure {x : ℕ → X |
        (∫⁻ h : X → ℝ≥0∞, ∏ i : Fin n,
            (h (x (i : ℕ)) * (p0 (x (i : ℕ)))⁻¹) ∂
            (M.latentLaw.map (fun ξ : ProbabilityMeasure Θ × (ℕ → Θ) => dpmDensity k ξ.1)))
          < ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 4)))}) atTop (𝓝 0) := by
      haveI hPiprob : IsProbabilityMeasure
          (M.latentLaw.map (fun ξ : ProbabilityMeasure Θ × (ℕ → Θ) => ξ.1)) :=
        ⟨by
          rw [Measure.map_apply measurable_fst MeasurableSet.univ]
          simp⟩
      have hton : ∀ P' : ProbabilityMeasure Θ, ∫⁻ x : X, dpmDensity k P' x ∂μ = 1 := by
        intro P'
        have hjoint : Measurable (Function.uncurry (fun (x : X) (θ : Θ) =>
            ENNReal.ofReal (k θ x))) :=
          (ENNReal.measurable_ofReal.comp hk_meas).comp
            (measurable_snd.prodMk measurable_fst)
        calc ∫⁻ x : X, dpmDensity k P' x ∂μ
            = ∫⁻ x : X, (∫⁻ θ : Θ, ENNReal.ofReal (k θ x) ∂P'.toMeasure) ∂μ := rfl
          _ = ∫⁻ θ : Θ, (∫⁻ x : X, ENNReal.ofReal (k θ x) ∂μ) ∂P'.toMeasure :=
              lintegral_lintegral_swap hjoint.aemeasurable
          _ = ∫⁻ θ : Θ, (1 : ℝ≥0∞) ∂P'.toMeasure :=
              lintegral_congr (fun θ => hk_int θ)
          _ = 1 := by
              simp
      have hdlt : ∀ P' : ProbabilityMeasure Θ, ∀ᵐ x ∂μ, dpmDensity k P' x ≠ ⊤ := by
        intro P'
        have hmeas : Measurable (fun x : X => dpmDensity k P' x) :=
          (statopia_math_node_9940328_8cef1cea k hk_meas).comp
            (measurable_const.prodMk measurable_id)
        have h1 : ∫⁻ x : X, dpmDensity k P' x ∂μ ≠ ⊤ := by
          rw [hton P']
          exact ENNReal.one_ne_top
        filter_upwards [MeasureTheory.ae_lt_top hmeas h1] with x hx
        exact hx.ne
      have hdnorm : ∀ᵐ P' ∂(M.latentLaw.map (fun ξ : ProbabilityMeasure Θ × (ℕ → Θ) => ξ.1)),
          ∫⁻ x : X, dpmDensity k P' x ∂μ ≤ 1 := by
        filter_upwards with P'
        rw [hton P']
      have hev : ∀ᵐ x ∂(truthLaw P.toMeasure), ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 4))) ≤
            ∫⁻ P' : ProbabilityMeasure Θ, ∏ i ∈ Finset.range n,
              (dpmDensity k P' (x i) * (p0 (x i))⁻¹) ∂
              (M.latentLaw.map (fun ξ : ProbabilityMeasure Θ × (ℕ → Θ) => ξ.1)) := by
        have h := statopia_math_node_905517917_ae3c2032
          (H := ProbabilityMeasure Θ) μ p0 hp0_meas hp0_int
          (M.latentLaw.map (fun ξ : ProbabilityMeasure Θ × (ℕ → Θ) => ξ.1))
          (fun (P' : ProbabilityMeasure Θ) (x : X) => dpmDensity k P' x)
          (statopia_math_node_9940328_8cef1cea k hk_meas) hdlt hdnorm
          (fun delta hdelta => by
            have hmix : mixtureDensity k q θs = p0 := by
              funext x
              rw [hp0_def]
              simp only [mixtureDensity, dpMixDensity]
              rw [ENNReal.ofReal_sum_of_nonneg (fun j _ =>
                mul_nonneg (le_of_lt (hq.1 j)) (hk_nonneg (θs j) x))]
              exact Finset.sum_congr rfl (fun j _ =>
                (ENNReal.ofReal_mul (le_of_lt (hq.1 j))).symm)
            have hpos := hH4 t ht q θs hq.1 hq.2.1 hq.2.2.1 hsupp delta hdelta
            rw [hmix] at hpos
            refine lt_of_lt_of_le hpos ?_
            exact MeasureTheory.Measure.le_map_apply
              (f := fun ξ : ProbabilityMeasure Θ × (ℕ → Θ) => ξ.1)
              measurable_fst.aemeasurable _) (c / 4) hc4_pos
        simpa only [truthLaw, hP] using h
      have hrepr : ∀ (n : ℕ) (x : ℕ → X),
          (∫⁻ P' : ProbabilityMeasure Θ, ∏ i ∈ Finset.range n,
              (dpmDensity k P' (x i) * (p0 (x i))⁻¹) ∂
              (M.latentLaw.map (fun ξ : ProbabilityMeasure Θ × (ℕ → Θ) => ξ.1)))
            = ∫⁻ h : X → ℝ≥0∞, ∏ i : Fin n,
                (h (x (i : ℕ)) * (p0 (x (i : ℕ)))⁻¹) ∂
                (M.latentLaw.map (fun ξ : ProbabilityMeasure Θ × (ℕ → Θ) => dpmDensity k ξ.1)) := by
        intro n x
        have hPm : Measurable (fun P' : ProbabilityMeasure Θ => ∏ i ∈ Finset.range n,
            (dpmDensity k P' (x i) * (p0 (x i))⁻¹)) := by
          refine Finset.measurable_prod _ (fun i _ => ?_)
          exact ((statopia_math_node_9940328_8cef1cea k hk_meas).comp
            (measurable_id.prodMk measurable_const)).mul measurable_const
        have hHm : Measurable (fun h : X → ℝ≥0∞ => ∏ i : Fin n,
            (h (x (i : ℕ)) * (p0 (x (i : ℕ)))⁻¹)) := by
          refine Finset.measurable_prod _ (fun i _ => ?_)
          exact (measurable_pi_apply (x (i : ℕ))).mul measurable_const
        have hgm : Measurable (fun ξ : ProbabilityMeasure Θ × (ℕ → Θ) =>
            dpmDensity k ξ.1) := by
          rw [measurable_pi_iff]
          intro y
          exact (statopia_math_node_9940328_8cef1cea k hk_meas).comp
            (measurable_fst.prodMk measurable_const)
        rw [lintegral_map hPm measurable_fst, lintegral_map hHm hgm]
        refine lintegral_congr (fun ξ => ?_)
        exact (Fin.prod_univ_eq_prod_range
          (fun i : ℕ => dpmDensity k ξ.1 (x i) * (p0 (x i))⁻¹) n).symm
      have hev' : ∀ᵐ x ∂(truthLaw P.toMeasure), ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 4))) ≤
            ∫⁻ h : X → ℝ≥0∞, ∏ i : Fin n,
              (h (x (i : ℕ)) * (p0 (x (i : ℕ)))⁻¹) ∂
              (M.latentLaw.map (fun ξ : ProbabilityMeasure Θ × (ℕ → Θ) => dpmDensity k ξ.1)) := by
        filter_upwards [hev] with x hx
        obtain ⟨N, hN⟩ := hx
        exact ⟨N, fun n hn => by rw [← hrepr n x]; exact hN n hn⟩
      set W : ℕ → (ℕ → X) → ℝ≥0∞ := fun n x =>
        ∫⁻ h : X → ℝ≥0∞, ∏ i : Fin n,
          (h (x (i : ℕ)) * (p0 (x (i : ℕ)))⁻¹) ∂
          (M.latentLaw.map (fun ξ : ProbabilityMeasure Θ × (ℕ → Θ) => dpmDensity k ξ.1))
        with hWdef
      have hAmeas : ∀ n : ℕ, MeasurableSet {x : ℕ → X |
          W n x < ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 4)))} := by
        intro n
        have hjointW : Measurable (Function.uncurry (fun (ξ : ProbabilityMeasure Θ × (ℕ → Θ))
            (x : ℕ → X) => ∏ i : Fin n, ENNReal.ofReal (k (ξ.2 (i : ℕ)) (x (i : ℕ))))) := by
          refine Finset.measurable_prod _ (fun i _ => ?_)
          have hk : Measurable (fun p : (ProbabilityMeasure Θ × (ℕ → Θ)) × (ℕ → X) =>
              Function.uncurry k (p.1.2 (i : ℕ), p.2 (i : ℕ))) :=
            hk_meas.comp
              (((measurable_pi_apply (i : ℕ)).comp (measurable_snd.comp measurable_fst)).prodMk
                ((measurable_pi_apply (i : ℕ)).comp measurable_snd))
          simpa [Function.uncurry] using ENNReal.measurable_ofReal.comp hk
        have hcore : Measurable (fun x : ℕ → X =>
            ∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
              ∏ i : Fin n, ENNReal.ofReal (k (ξ.2 (i : ℕ)) (x (i : ℕ))) ∂M.latentLaw) :=
          hjointW.lintegral_prod_left
        have hoen : Measurable (fun x : ℕ → X => ∏ i : Fin n, (p0 (x (i : ℕ)))⁻¹) := by
          refine Finset.measurable_prod _ (fun i _ => ?_)
          exact (hp0_meas.comp (measurable_pi_apply (i : ℕ))).inv
        have hpt : ∀ x : ℕ → X, W n x = (∏ i : Fin n, (p0 (x (i : ℕ)))⁻¹) *
              ∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
                ∏ i : Fin n, ENNReal.ofReal (k (ξ.2 (i : ℕ)) (x (i : ℕ))) ∂M.latentLaw := by
          intro x
          exact hW_den n (fun i : Fin n => x (i : ℕ))
        simp only [hpt]
        exact measurableSet_lt (hoen.mul hcore) measurable_const
      have hAnti : Antitone (fun n : ℕ => ⋃ k ∈ Set.Ici n,
          {x : ℕ → X | W k x < ENNReal.ofReal (Real.exp (-(k : ℝ) * (c / 4)))}) := by
        intro m n hmn x hx
        simp only [Set.mem_iUnion, Set.mem_Ici] at hx ⊢
        obtain ⟨k, hk, hkx⟩ := hx
        exact ⟨k, le_trans hmn hk, hkx⟩
      have hlim : truthLaw P.toMeasure (⋂ n, ⋃ k ∈ Set.Ici n,
          {x : ℕ → X | W k x < ENNReal.ofReal (Real.exp (-(k : ℝ) * (c / 4)))}) = 0 := by
        have hzero : truthLaw P.toMeasure {x : ℕ → X | ¬ (∃ N : ℕ, ∀ n : ℕ, N ≤ n →
            ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 4))) ≤ W n x)} = 0 := by
          rw [← MeasureTheory.ae_iff]
          exact hev'
        refine le_antisymm (le_trans (measure_mono ?_) (le_of_eq hzero)) (zero_le _)
        intro x hx
        simp only [Set.mem_iInter, Set.mem_iUnion, Set.mem_Ici, Set.mem_setOf_eq] at hx ⊢
        rintro ⟨N, hN⟩
        obtain ⟨k, hk, hkx⟩ := hx N
        exact absurd (hN k hk) (not_le.mpr hkx)
      have hC : Tendsto (fun n : ℕ => truthLaw P.toMeasure (⋃ k ∈ Set.Ici n,
          {x : ℕ → X | W k x < ENNReal.ofReal (Real.exp (-(k : ℝ) * (c / 4)))}))
          atTop (𝓝 0) := by
        have hcm : ∀ n : ℕ, NullMeasurableSet (⋃ k ∈ Set.Ici n,
            {x : ℕ → X | W k x < ENNReal.ofReal (Real.exp (-(k : ℝ) * (c / 4)))})
            (truthLaw P.toMeasure) := fun n =>
          (MeasurableSet.iUnion (fun k => MeasurableSet.iUnion
            (fun _ => hAmeas k))).nullMeasurableSet
        have h := MeasureTheory.tendsto_measure_iInter_atTop (μ := truthLaw P.toMeasure)
          (s := fun n : ℕ => ⋃ k ∈ Set.Ici n,
            {x : ℕ → X | W k x < ENNReal.ofReal (Real.exp (-(k : ℝ) * (c / 4)))}) hcm hAnti
          ⟨0, ne_top_of_le_ne_top ENNReal.one_ne_top (htruth_le_one _)⟩
        rwa [hlim] at h
      refine hSqueeze _ _ (fun n => ?_) hC
      exact measure_mono (fun x hx => by
        simp only [Set.mem_iUnion, Set.mem_Ici]
        exact ⟨n, le_refl n, hx⟩)
    let g : ℕ → ℝ≥0∞ := fun n =>
      (truthLaw P.toMeasure {x : ℕ → X | ε₀ / 2 ≤ ⨆ j : Fin r,
          |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (x (i : ℕ)))
            - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure|}
        + truthLaw P.toMeasure {x : ℕ → X |
            (∫⁻ h : X → ℝ≥0∞, ∏ i : Fin n,
                (h (x (i : ℕ)) * (p0 (x (i : ℕ)))⁻¹) ∂
                (M.latentLaw.map (fun ξ : ProbabilityMeasure Θ × (ℕ → Θ) => dpmDensity k ξ.1)))
              < ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 4)))})
        + truthLaw P.toMeasure {x : ℕ → X |
            ENNReal.ofReal ε * ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 4)))
              < (if (⨆ j : Fin r,
                    |(n : ℝ)⁻¹ * (∑ i : Fin n, (ψ j : X → ℝ) (x (i : ℕ)))
                      - ∫ x' : X, (ψ j : X → ℝ) x' ∂P.toMeasure|) < ε₀ / 2
                  then ∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
                    (if clusterCount ξ.2 n < t then
                      ∏ i : Fin n,
                        (ENNReal.ofReal (k (ξ.2 (i : ℕ)) (x (i : ℕ))) * (p0 (x (i : ℕ)))⁻¹)
                      else 0) ∂M.latentLaw
                  else 0)}
    have hThree : Tendsto g atTop (𝓝 0) := by
      have h := (hTypeI_tendsto.add hB_tendsto).add hS3_tendsto
      simpa only [g, add_zero, zero_add] using h
    refine hSqueeze _ g ?_ hThree
    intro n
    dsimp only [g]
    exact le_trans (measure_mono (htarget_subset n))
      (hunion_bound n (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε))
  /- @proof-region region.root.25632fd897f7 end -/

end Statlib.Imported

-- Paper root revision 27155baa-4ba6-4ac6-8e38-b913889ad446
