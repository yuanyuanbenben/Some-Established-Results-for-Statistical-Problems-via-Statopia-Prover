import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q08.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q08.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q08.ProvedNodes.Node_4100084658_beb39d50_47d3a120
open MeasureTheory Matrix ProbabilityTheory

open MeasureTheory Matrix ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_11731219_b8d62fc9 : ∀ (n d : ℕ) (hn : 1 ≤ n) (hd : 2 ≤ d)
    (sigma : ℝ) (hsigma : 0 < sigma)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (X : Matrix (Fin n) (Fin d) ℝ)
    (thetaStar : Fin d → ℝ),
    let lambda : ℝ := 4 * sigma * Real.sqrt (Real.log (d : ℝ) / (n : ℝ))
    let c : ℝ := 6 * sigma / gamma * Real.sqrt (Real.log (d : ℝ) / (n : ℝ))
    let F : (Fin n → ℝ) → (Fin d → ℝ) → ℝ := fun z theta =>
      (∑ i, (X *ᵥ thetaStar + z - X *ᵥ theta) i ^ 2) / (2 * (n : ℝ)) +
        lambda * ∑ j, |theta j|
    MeasurableSet {z : Fin n → ℝ | ∀ theta : Fin d → ℝ,
      (∀ eta : Fin d → ℝ, F z theta ≤ F z eta) →
        (⨆ j, |(theta - thetaStar) j|) ≤ c} := by
  /- @proof-region region.target-node.session.932fcc0a5e5065e6 begin -/
  intro n d hn hd sigma hsigma gamma hgamma X thetaStar
  dsimp only
  let lam : ℝ := 4 * sigma * Real.sqrt (Real.log (d : ℝ) / (n : ℝ))
  let cc : ℝ := 6 * sigma / gamma * Real.sqrt (Real.log (d : ℝ) / (n : ℝ))
  let F : (Fin n → ℝ) → (Fin d → ℝ) → ℝ := fun z theta =>
    (∑ i, (X *ᵥ thetaStar + z - X *ᵥ theta) i ^ 2) / (2 * (n : ℝ)) + lam * ∑ j, |theta j|
  change MeasurableSet {z : Fin n → ℝ | ∀ theta : Fin d → ℝ,
    (∀ eta : Fin d → ℝ, F z theta ≤ F z eta) → (⨆ j, |(theta - thetaStar) j|) ≤ cc}
  have hd1 : (1 : ℝ) < (d : ℝ) := by
    have h : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have h : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hlog : 0 < Real.log (d : ℝ) := Real.log_pos hd1
  have hratio : 0 < Real.log (d : ℝ) / (n : ℝ) := div_pos hlog hn0
  have hsqrt_pos : 0 < Real.sqrt (Real.log (d : ℝ) / (n : ℝ)) := Real.sqrt_pos.mpr hratio
  have hsqrt_nonneg : 0 ≤ Real.sqrt (Real.log (d : ℝ) / (n : ℝ)) := Real.sqrt_nonneg _
  have hlam_pos : 0 < lam := by
    show 0 < 4 * sigma * Real.sqrt (Real.log (d : ℝ) / (n : ℝ))
    exact mul_pos (mul_pos (by norm_num) hsigma) hsqrt_pos
  have hcc_nonneg : 0 ≤ cc := by
    show 0 ≤ 6 * sigma / gamma * Real.sqrt (Real.log (d : ℝ) / (n : ℝ))
    exact mul_nonneg (le_of_lt (div_pos (by linarith [hsigma]) hgamma)) hsqrt_nonneg
  let φ : ℕ → (Fin d → ℝ) := TopologicalSpace.denseSeq (Fin d → ℝ)
  let hb : (Fin d → ℝ) → ℝ := fun theta => ⨆ j, |(theta - thetaStar) j|
  let M : (Fin n → ℝ) → ℝ := fun z => ⨅ m : ℕ, F z (φ m)
  let S : Set (Fin n → ℝ) := ⋃ (ε : ℚ), ⋂ k : ℕ, ⋃ m : ℕ,
    {z : Fin n → ℝ | (0 : ℝ) < (ε : ℝ) ∧ cc + (ε : ℝ) ≤ hb (φ m) ∧ F z (φ m) < M z + 1 / ((k : ℝ) + 1)}
  have hcont_z : ∀ θ : Fin d → ℝ, Continuous (fun z : Fin n → ℝ => F z θ) := by
    intro θ; fun_prop
  have hcont_θ : ∀ z : Fin n → ℝ, Continuous (fun θ : Fin d → ℝ => F z θ) := by
    intro z; fun_prop
  have hcoerc : ∀ (z : Fin n → ℝ) (θ : Fin d → ℝ), lam * (∑ j, |θ j|) ≤ F z θ := by
    intro z θ
    have hQ : 0 ≤ (∑ i, (X *ᵥ thetaStar + z - X *ᵥ θ) i ^ 2) / (2 * (n : ℝ)) := by positivity
    have hFF : F z θ = (∑ i, (X *ᵥ thetaStar + z - X *ᵥ θ) i ^ 2) / (2 * (n : ℝ)) + lam * ∑ j, |θ j| := rfl
    rw [hFF]; linarith
  classical
  have hBdd : ∀ z : Fin n → ℝ, BddBelow (Set.range (fun m : ℕ => F z (φ m))) := by
    intro z
    refine ⟨0, ?_⟩
    rintro _ ⟨m, rfl⟩
    have h1 : (0 : ℝ) ≤ lam * (∑ j, |(φ m) j|) :=
      mul_nonneg (le_of_lt hlam_pos) (Finset.sum_nonneg (fun j _ => abs_nonneg _))
    linarith [hcoerc z (φ m)]
  have hsub : ∀ s : ℝ, MeasurableSet {z : Fin n → ℝ | s < M z} := by
    intro s
    rw [show {z : Fin n → ℝ | s < M z}
        = ⋃ (t : ℚ), ({z : Fin n → ℝ | s < (t:ℝ)} ∩ {z : Fin n → ℝ | (t:ℝ) ≤ M z}) by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro h
        obtain ⟨t, ht1, ht2⟩ := exists_rat_btwn h
        exact ⟨t, ht1, le_of_lt ht2⟩
      · rintro ⟨t, ht1, ht2⟩
        exact lt_of_lt_of_le ht1 ht2]
    apply MeasurableSet.iUnion
    intro t
    by_cases ht : s < (t:ℝ)
    · rw [show ({z : Fin n → ℝ | s < (t:ℝ)} ∩ {z : Fin n → ℝ | (t:ℝ) ≤ M z}) = {z : Fin n → ℝ | (t:ℝ) ≤ M z} by
        ext z; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]; exact ⟨fun h => h.2, fun h => ⟨ht, h⟩⟩]
      rw [show {z : Fin n → ℝ | (t:ℝ) ≤ M z} = ⋂ m : ℕ, {z : Fin n → ℝ | (t:ℝ) ≤ F z (φ m)} by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_iInter]
        exact ⟨fun h m => le_trans h (ciInf_le (hBdd z) m), fun h => le_ciInf h⟩]
      apply MeasurableSet.iInter
      intro m
      exact (isClosed_Ici.preimage (hcont_z (φ m))).measurableSet
    · rw [show ({z : Fin n → ℝ | s < (t:ℝ)} ∩ {z : Fin n → ℝ | (t:ℝ) ≤ M z}) = ∅ by
        ext z; simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false]; exact ⟨fun h => absurd h.1 ht, fun h => h.elim⟩]
      exact MeasurableSet.empty
  have hB : ∀ (k m : ℕ), MeasurableSet {z : Fin n → ℝ | F z (φ m) < M z + 1 / ((k:ℝ) + 1)} := by
    intro k m
    rw [show {z : Fin n → ℝ | F z (φ m) < M z + 1 / ((k:ℝ) + 1)}
        = ⋃ (q : ℚ), ({z : Fin n → ℝ | F z (φ m) < (q:ℝ)} ∩ {z : Fin n → ℝ | (q:ℝ) - 1 / ((k:ℝ) + 1) < M z}) by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro h
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h
        exact ⟨q, hq1, by linarith⟩
      · rintro ⟨q, hq1, hq2⟩
        linarith]
    apply MeasurableSet.iUnion
    intro q
    apply MeasurableSet.inter
    · exact (isOpen_Iio.preimage (hcont_z (φ m))).measurableSet
    · exact hsub ((q:ℝ) - 1 / ((k:ℝ) + 1))
  have hA : ∀ (ε : ℚ) (k m : ℕ), MeasurableSet {z : Fin n → ℝ | (0:ℝ) < (ε:ℝ) ∧ cc + (ε:ℝ) ≤ hb (φ m) ∧ F z (φ m) < M z + 1 / ((k:ℝ) + 1)} := by
    intro ε k m
    by_cases hP : (0:ℝ) < (ε:ℝ) ∧ cc + (ε:ℝ) ≤ hb (φ m)
    · rw [show {z : Fin n → ℝ | (0:ℝ) < (ε:ℝ) ∧ cc + (ε:ℝ) ≤ hb (φ m) ∧ F z (φ m) < M z + 1 / ((k:ℝ) + 1)}
          = {z : Fin n → ℝ | F z (φ m) < M z + 1 / ((k:ℝ) + 1)} by
        ext z; simp only [Set.mem_setOf_eq]; exact ⟨fun h => h.2.2, fun h => ⟨hP.1, hP.2, h⟩⟩]
      exact hB k m
    · rw [show {z : Fin n → ℝ | (0:ℝ) < (ε:ℝ) ∧ cc + (ε:ℝ) ≤ hb (φ m) ∧ F z (φ m) < M z + 1 / ((k:ℝ) + 1)} = ∅ by
        ext z; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]; exact ⟨fun h => absurd ⟨h.1, h.2.1⟩ hP, fun h => h.elim⟩]
      exact MeasurableSet.empty
  have hS : MeasurableSet S := by
    show MeasurableSet (⋃ (ε : ℚ), ⋂ k : ℕ, ⋃ m : ℕ, {z : Fin n → ℝ | (0:ℝ) < (ε:ℝ) ∧ cc + (ε:ℝ) ≤ hb (φ m) ∧ F z (φ m) < M z + 1 / ((k:ℝ) + 1)})
    apply MeasurableSet.iUnion
    intro ε
    apply MeasurableSet.iInter
    intro k
    apply MeasurableSet.iUnion
    intro m
    exact hA ε k m
  have hZ : {z : Fin n → ℝ | ∀ theta : Fin d → ℝ,
      (∀ eta : Fin d → ℝ, F z theta ≤ F z eta) → (⨆ j, |(theta - thetaStar) j|) ≤ cc} = Sᶜ := by
    exact statopia_math_node_4100084658_beb39d50 n d hn hd sigma gamma hsigma hgamma X thetaStar
  rw [hZ]
  exact hS.compl

  /- @proof-region region.target-node.session.932fcc0a5e5065e6 end -/
