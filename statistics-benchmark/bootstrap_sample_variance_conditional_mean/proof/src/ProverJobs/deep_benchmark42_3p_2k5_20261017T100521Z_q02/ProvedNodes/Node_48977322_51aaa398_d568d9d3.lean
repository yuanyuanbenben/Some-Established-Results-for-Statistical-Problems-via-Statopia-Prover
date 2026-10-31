import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q02.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q02.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q02.ProvedNodes.Node_1444442084_ecdddf06_0899ce96
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q02.ProvedNodes.Node_2727953355_20110073_65e94148
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q02.ProvedNodes.Node_3259429663_3e1e7d56_9e566880
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q02.ProvedNodes.Node_3549106997_e1262180_9298e2b7
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q02.ProvedNodes.Node_488559670_a6d524b3_eb071a4e





open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_48977322_51aaa398 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n)
    (X : Fin n → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (I : Fin n → Ω → Fin n)
    (hI_meas : ∀ j, Measurable (I j))
    (hI_indep : iIndepFun I P)
    (hI_uniform : ∀ i j, P {ω | I j ω = i} = (n : ENNReal)⁻¹)
    (hIX_indep : IndepFun (fun ω j => I j ω) (fun ω i => X i ω) P),
    let mean : Ω → ℝ := fun ω => (n : ℝ)⁻¹ * ∑ i, X i ω
    let V : Ω → ℝ := fun ω => (n : ℝ)⁻¹ * ∑ i, (X i ω - mean ω) ^ 2
    let G : MeasurableSpace Ω :=
      MeasurableSpace.comap (fun ω i => X i ω)
        (inferInstance : MeasurableSpace (Fin n → ℝ))
    (∀ i k : Fin n, Integrable (fun ω => (X i ω - X k ω) ^ 2) P) →
      Measurable V →
      Integrable V P →
      ∀ j l : Fin n, j ≠ l →
        condExp G P (fun ω => (X (I j ω) ω - X (I l ω) ω) ^ 2) =ᵐ[P]
          (fun ω => 2 * V ω) := by
  /- @proof-region region.target-node.session.5f42ec19c3de2fbd begin -/
  classical
  intro Ω instΩ P hP n hn X hX_meas I hI_meas hI_indep hI_uniform hIX_indep mean V G h_int hV_meas hV_int j l hjl
  haveI : IsProbabilityMeasure P := hP
  letI : MeasurableSpace Ω := instΩ
  obtain ⟨hindep, hmass⟩ :=
    statopia_math_node_3549106997_e1262180 P n hn I hI_meas hI_indep hI_uniform X hIX_indep j l hjl
  let Φ : Ω → (Fin n × Fin n) := fun ω => (I j ω, I l ω)
  let g : Ω → (Fin n → ℝ) := fun ω i => X i ω
  let φ : (Fin n × Fin n) → Ω → ℝ := fun p ω =>
    (({p} : Set (Fin n × Fin n)).indicator (fun _ => (1 : ℝ))) (Φ ω) * (X p.1 ω - X p.2 ω) ^ 2
  have hΦ_meas : Measurable Φ := by
    show Measurable fun ω => (I j ω, I l ω)
    first
      | exact Measurable.prod_mk (hI_meas j) (hI_meas l)
      | exact Measurable.prod (hI_meas j) (hI_meas l)
      | exact measurable_prod_mk (hI_meas j) (hI_meas l)
      | exact measurable_prod (hI_meas j) (hI_meas l)
  have hg_meas : Measurable g := by
    show Measurable fun ω (i : Fin n) => X i ω
    exact measurable_pi_iff.mpr (fun i => hX_meas i)
  have hh_meas : ∀ p : Fin n × Fin n, Measurable (fun v : Fin n → ℝ => (v p.1 - v p.2) ^ 2) := by
    intro p
    have h1 : Measurable (fun v : Fin n → ℝ => v p.1) := measurable_pi_apply p.1
    have h2 : Measurable (fun v : Fin n → ℝ => v p.2) := measurable_pi_apply p.2
    simpa [pow_two] using (h1.sub h2).mul (h1.sub h2)
  have hset : ∀ p : Fin n × Fin n,
      Φ ⁻¹' ({p} : Set (Fin n × Fin n)) = {ω | I j ω = p.1 ∧ I l ω = p.2} := by
    rintro ⟨a, b⟩
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq, Φ]
    exact ⟨fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩, fun h => by rw [h.1, h.2]⟩
  have hmassp : ∀ p : Fin n × Fin n,
      (P (Φ ⁻¹' ({p} : Set (Fin n × Fin n)))).toReal = (n : ℝ)⁻¹ * (n : ℝ)⁻¹ := by
    intro p
    rw [hset p]
    exact hmass p.1 p.2
  have hterm : ∀ p : Fin n × Fin n,
      condExp G P (φ p) =ᵐ[P] fun ω => ((n : ℝ)⁻¹ * (n : ℝ)⁻¹) * (X p.1 ω - X p.2 ω) ^ 2 := by
    intro p
    have hmain := statopia_math_node_2727953355_20110073 P Φ g hΦ_meas hg_meas hindep
      ({p} : Set (Fin n × Fin n)) (measurableSet_singleton p)
      (fun v : Fin n → ℝ => (v p.1 - v p.2) ^ 2) (hh_meas p) (h_int p.1 p.2)
    rw [hmassp p] at hmain
    simpa [φ] using hmain
  have hφ_int : ∀ p : Fin n × Fin n, Integrable (φ p) P := by
    intro p
    have hEq : φ p = (Φ ⁻¹' ({p} : Set (Fin n × Fin n))).indicator
        (fun ω => (X p.1 ω - X p.2 ω) ^ 2) := by
      funext ω
      by_cases h : Φ ω ∈ ({p} : Set (Fin n × Fin n))
      · have h' : ω ∈ Φ ⁻¹' ({p} : Set (Fin n × Fin n)) := h
        simp only [φ, Set.indicator_of_mem h, Set.indicator_of_mem h', one_mul]
      · have h' : ω ∉ Φ ⁻¹' ({p} : Set (Fin n × Fin n)) := h
        simp only [φ, Set.indicator_of_notMem h, Set.indicator_of_notMem h', zero_mul]
    rw [hEq]
    exact (h_int p.1 p.2).indicator (hΦ_meas (measurableSet_singleton p))
  have hdecomp : (fun ω => (X (I j ω) ω - X (I l ω) ω) ^ 2) =
      fun ω => ∑ p : Fin n × Fin n, φ p ω := by
    funext ω
    symm
    have h0 : ∀ p ∈ (Finset.univ : Finset (Fin n × Fin n)), p ≠ Φ ω → φ p ω = 0 := by
      intro p _ hp
      have hmem : Φ ω ∉ ({p} : Set (Fin n × Fin n)) := by
        simp only [Set.mem_singleton_iff]
        exact fun h => hp h.symm
      simp only [φ, Set.indicator_of_notMem hmem, zero_mul]
    have h1 : Φ ω ∉ (Finset.univ : Finset (Fin n × Fin n)) → φ (Φ ω) ω = 0 :=
      fun h => absurd (Finset.mem_univ _) h
    rw [Finset.sum_eq_single (Φ ω) h0 h1]
    simp [φ, Set.indicator_of_mem, Φ]
  have hlin : condExp G P (fun ω => ∑ p : Fin n × Fin n, φ p ω) =ᵐ[P]
      fun ω => ∑ p : Fin n × Fin n, condExp G P (φ p) ω := by
    have h := MeasureTheory.condExp_finset_sum (μ := P)
      (s := (Finset.univ : Finset (Fin n × Fin n))) (f := φ) (fun p _ => hφ_int p) G
    have e1 : (fun ω => ∑ p : Fin n × Fin n, φ p ω) = (∑ p : Fin n × Fin n, φ p) := by
      funext ω
      simp
    have e2 : (∑ p : Fin n × Fin n, condExp G P (φ p)) =
        (fun ω => ∑ p : Fin n × Fin n, condExp G P (φ p) ω) := by
      funext ω
      simp
    rw [e2] at h
    rw [e1]
    exact h
  have hsum_congr : (fun ω => ∑ p : Fin n × Fin n, condExp G P (φ p) ω) =ᵐ[P]
      fun ω => ∑ p : Fin n × Fin n, ((n : ℝ)⁻¹ * (n : ℝ)⁻¹) * (X p.1 ω - X p.2 ω) ^ 2 := by
    have key : ∀ s : Finset (Fin n × Fin n),
        (fun ω => ∑ p ∈ s, condExp G P (φ p) ω) =ᵐ[P]
          (fun ω => ∑ p ∈ s, ((n : ℝ)⁻¹ * (n : ℝ)⁻¹) * (X p.1 ω - X p.2 ω) ^ 2) := by
      intro s
      induction s using Finset.induction with
      | empty =>
        simp only [Finset.sum_empty]
        exact Filter.EventuallyEq.rfl
      | insert a s ha ih =>
        have h1 : (fun ω => ∑ p ∈ insert a s, condExp G P (φ p) ω) =
            (fun ω => condExp G P (φ a) ω) + (fun ω => ∑ p ∈ s, condExp G P (φ p) ω) := by
          funext ω
          rw [Finset.sum_insert ha]
          rfl
        have h2 : (fun ω => ((n : ℝ)⁻¹ * (n : ℝ)⁻¹) * (X a.1 ω - X a.2 ω) ^ 2) +
              (fun ω => ∑ p ∈ s, ((n : ℝ)⁻¹ * (n : ℝ)⁻¹) * (X p.1 ω - X p.2 ω) ^ 2) =
            (fun ω => ∑ p ∈ insert a s, ((n : ℝ)⁻¹ * (n : ℝ)⁻¹) * (X p.1 ω - X p.2 ω) ^ 2) := by
          funext ω
          rw [Finset.sum_insert ha]
          rfl
        rw [h1, ← h2]
        exact (hterm a).add ih
    simpa using key Finset.univ

  have hfin : condExp G P (fun ω => (X (I j ω) ω - X (I l ω) ω) ^ 2) =ᵐ[P]
      fun ω => ∑ p : Fin n × Fin n, ((n : ℝ)⁻¹ * (n : ℝ)⁻¹) * (X p.1 ω - X p.2 ω) ^ 2 := by
    rw [hdecomp]
    exact hlin.trans hsum_congr
  have halg : (fun ω => ∑ p : Fin n × Fin n, ((n : ℝ)⁻¹ * (n : ℝ)⁻¹) * (X p.1 ω - X p.2 ω) ^ 2) =
      fun ω => 2 * V ω := by
    funext ω
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have h : (0 : ℕ) < n := Nat.zero_lt_one.trans_le hn
      exact_mod_cast h
    have hc : (2 * (n : ℝ) ^ 2) ≠ 0 := by
      have hpos : (0 : ℝ) < 2 * (n : ℝ) ^ 2 := by positivity
      exact ne_of_gt hpos
    have hvar := statopia_math_node_488559670_a6d524b3 n hn (fun i : Fin n => X i ω)
    have hVval : V ω = (2 * (n : ℝ) ^ 2)⁻¹ *
        (∑ i : Fin n, ∑ k : Fin n, (X i ω - X k ω) ^ 2) := by
      simpa using hvar.symm
    have hprod : (∑ p : Fin n × Fin n, (X p.1 ω - X p.2 ω) ^ 2) =
        ∑ i : Fin n, ∑ k : Fin n, (X i ω - X k ω) ^ 2 := by
      rw [Fintype.sum_prod_type]
    have hstep : (∑ p : Fin n × Fin n, ((n : ℝ)⁻¹ * (n : ℝ)⁻¹) * (X p.1 ω - X p.2 ω) ^ 2) =
        (n : ℝ)⁻¹ * (n : ℝ)⁻¹ * (∑ p : Fin n × Fin n, (X p.1 ω - X p.2 ω) ^ 2) := by
      rw [Finset.mul_sum]
    rw [hstep, hprod, hVval]
    field_simp
  rw [show (fun ω => 2 * V ω) =
      (fun ω => ∑ p : Fin n × Fin n, ((n : ℝ)⁻¹ * (n : ℝ)⁻¹) * (X p.1 ω - X p.2 ω) ^ 2)
      from halg.symm]
  exact hfin
  /- @proof-region region.target-node.session.5f42ec19c3de2fbd end -/
