import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q13.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q13.Base

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

set_option autoImplicit false in
theorem statopia_math_node_3661166939_5226b67c : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : ℝ) (hθ : 0 < θ)
    (X : ℕ → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (hX_uniform : ∀ i, MeasureTheory.pdf.IsUniform (X i) (Set.Ioo 0 θ) P)
    (r : ℕ) (t : ℝ) (ht : t ≤ 0),
    (P.map (fun ω ↦
      ((r + 1 : ℕ) : ℝ) *
        (θ - (Finset.univ : Finset (Fin (r + 1))).sup'
          Finset.univ_nonempty (fun i ↦ X i.1 ω))))
      (Set.Iic t) = 0 := by
  /- @proof-region region.target-node.session.281e35d865b8a244 begin -/
  intro Ω _ P _ θ hθ X hX_meas hX_indep hX_uniform r t ht
  have hc : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := by
    have hpos : (0 : ℕ) < r + 1 := Nat.succ_pos r
    exact_mod_cast hpos
  have hvol : (volume : Measure ℝ) (Set.Ioo 0 θ) ≠ 0 := by
    rw [Real.volume_Ioo, sub_zero]
    exact (ENNReal.ofReal_pos.mpr hθ).ne'
  have hvol_top : (volume : Measure ℝ) (Set.Ioo 0 θ) ≠ ⊤ := by
    rw [Real.volume_Ioo, sub_zero]
    exact ENNReal.ofReal_ne_top
  have hcoord : ∀ i : ℕ, P {ω | θ ≤ X i ω} = 0 := by
    intro i
    have hmeas_i : MeasurableSet ((X i) ⁻¹' Set.Ioo (0 : ℝ) θ) :=
      hX_meas i measurableSet_Ioo
    have hpre : P ((X i) ⁻¹' Set.Ioo (0 : ℝ) θ) = 1 := by
      have h1 := MeasureTheory.pdf.IsUniform.measure_preimage hvol hvol_top
        (hX_uniform i) (A := Set.Ioo (0 : ℝ) θ) measurableSet_Ioo
      rwa [Set.inter_self, ENNReal.div_self hvol hvol_top] at h1
    have hcompl : P ((X i) ⁻¹' Set.Ioo (0 : ℝ) θ)ᶜ = 0 := by
      have htop : P ((X i) ⁻¹' Set.Ioo (0 : ℝ) θ) ≠ ⊤ := by
        rw [hpre]
        exact ENNReal.one_ne_top
      rw [measure_compl hmeas_i htop, hpre, measure_univ, tsub_self]
    refine measure_mono_null ?_ hcompl
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_Ioo]
    exact fun h => (not_lt.mpr hω) h.2
  have key : ∀ n : ℕ, Measurable (fun ω =>
      (Finset.univ : Finset (Fin (n + 1))).sup' Finset.univ_nonempty (fun i => X i.1 ω)) := by
    intro n
    induction n with
    | zero =>
      have hbase : (fun ω => (Finset.univ : Finset (Fin (0 + 1))).sup' Finset.univ_nonempty
          (fun i => X i.1 ω)) = fun ω => X 0 ω := by
        funext ω
        refine le_antisymm ?_ ?_
        · refine (Finset.sup'_le_iff Finset.univ_nonempty
            (fun i : Fin (0 + 1) => X i.1 ω)).mpr ?_
          intro i _
          have hi : i.1 = 0 := by
            have := i.isLt
            omega
          simp [hi]
        · simpa using Finset.le_sup'
            (fun i : Fin (0 + 1) => X i.1 ω) (Finset.mem_univ (0 : Fin (0 + 1)))
      rw [hbase]
      exact hX_meas 0
    | succ n ih =>
      have hstep : (fun ω => (Finset.univ : Finset (Fin (Nat.succ n + 1))).sup'
          Finset.univ_nonempty (fun i => X i.1 ω)) =
          fun ω => max ((Finset.univ : Finset (Fin (n + 1))).sup' Finset.univ_nonempty
            (fun i => X i.1 ω)) (X (n + 1) ω) := by
        funext ω
        refine le_antisymm ?_ (max_le_iff.mpr ⟨?_, ?_⟩)
        · refine (Finset.sup'_le_iff Finset.univ_nonempty
            (fun i : Fin (Nat.succ n + 1) => X i.1 ω)).mpr ?_
          intro i _
          by_cases hi : i.1 = n + 1
          · have hlast : i = ⟨n + 1, by omega⟩ := Fin.ext hi
            rw [hlast]
            exact le_max_right _ _
          · have hlt : i.1 < n + 1 := by
              have := i.isLt
              omega
            have hle := Finset.le_sup' (fun j : Fin (n + 1) => X j.1 ω)
              (Finset.mem_univ (⟨i.1, hlt⟩ : Fin (n + 1)))
            exact le_trans hle (le_max_left _ _)
        · refine (Finset.sup'_le_iff Finset.univ_nonempty
            (fun j : Fin (n + 1) => X j.1 ω)).mpr ?_
          intro j _
          exact Finset.le_sup' (fun i : Fin (Nat.succ n + 1) => X i.1 ω)
            (Finset.mem_univ (⟨j.1, by omega⟩ : Fin (Nat.succ n + 1)))
        · exact Finset.le_sup' (fun i : Fin (Nat.succ n + 1) => X i.1 ω)
            (Finset.mem_univ (⟨n + 1, by omega⟩ : Fin (Nat.succ n + 1)))
      rw [hstep]
      exact Measurable.max ih (hX_meas (n + 1))
  have hM_meas : Measurable (fun ω =>
      (Finset.univ : Finset (Fin (r + 1))).sup' Finset.univ_nonempty (fun i => X i.1 ω)) :=
    key r
  have hM_null : P {ω | θ ≤
      (Finset.univ : Finset (Fin (r + 1))).sup' Finset.univ_nonempty (fun i => X i.1 ω)} = 0 := by
    have hsubset : {ω | θ ≤
        (Finset.univ : Finset (Fin (r + 1))).sup' Finset.univ_nonempty (fun i => X i.1 ω)} ⊆
        ⋃ i : Fin (r + 1), {ω | θ ≤ X i.1 ω} := by
      intro ω hω
      by_contra hcon
      simp only [Set.mem_iUnion, not_exists, not_le, Set.mem_setOf_eq] at hcon
      have hlt : (Finset.univ : Finset (Fin (r + 1))).sup' Finset.univ_nonempty
          (fun i => X i.1 ω) < θ :=
        (Finset.sup'_lt_iff Finset.univ_nonempty).mpr (fun i _ => hcon i)
      exact absurd hω (not_le.mpr hlt)
    have hunion : P (⋃ i : Fin (r + 1), {ω | θ ≤ X i.1 ω}) = 0 := by
      rw [measure_iUnion_null_iff]
      intro i
      exact hcoord i.1
    exact measure_mono_null hsubset hunion
  have hV_meas : Measurable (fun ω =>
      ((r + 1 : ℕ) : ℝ) * (θ - (Finset.univ : Finset (Fin (r + 1))).sup'
        Finset.univ_nonempty (fun i => X i.1 ω))) :=
    measurable_const.mul (measurable_const.sub hM_meas)
  rw [MeasureTheory.Measure.map_apply hV_meas measurableSet_Iic]
  refine measure_mono_null ?_ hM_null
  intro ω hω
  simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq] at hω ⊢
  have hprod : ((r + 1 : ℕ) : ℝ) *
      (θ - (Finset.univ : Finset (Fin (r + 1))).sup' Finset.univ_nonempty
        (fun i => X i.1 ω)) ≤ 0 := le_trans hω ht
  by_contra hcon
  push_neg at hcon
  have hpos : 0 < ((r + 1 : ℕ) : ℝ) *
      (θ - (Finset.univ : Finset (Fin (r + 1))).sup' Finset.univ_nonempty
        (fun i => X i.1 ω)) := mul_pos hc (by linarith)
  linarith
  /- @proof-region region.target-node.session.281e35d865b8a244 end -/
