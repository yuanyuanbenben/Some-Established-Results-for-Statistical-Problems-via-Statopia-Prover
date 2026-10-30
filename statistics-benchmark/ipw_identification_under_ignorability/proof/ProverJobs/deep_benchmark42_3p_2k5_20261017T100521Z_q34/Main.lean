import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q34.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q34.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q34.Base

open MeasureTheory

theorem ipw_identification_under_ignorability
    {Ω 𝒵 : Type*}
    [MeasurableSpace Ω]
    [Fintype 𝒵]
    [MeasurableSpace 𝒵]
    [MeasurableSingletonClass 𝒵]
    (P : Measure Ω)
    [IsProbabilityMeasure P]
    (T : Ω → Bool)
    (Z : Ω → 𝒵)
    (Y Y0 Y1 : Ω → ℝ)
    (hTmeas : Measurable T)
    (hZmeas : Measurable Z)
    (hYmeas : Measurable Y)
    (hY0meas : Measurable Y0)
    (hY1meas : Measurable Y1)
    (hYint : Integrable Y P)
    (hY0int : Integrable Y0 P)
    (hY1int : Integrable Y1 P)
    (hZpos : ∀ z, 0 < P {ω | Z ω = z})
    (hObserved : Y =ᵐ[P] fun ω ↦ if T ω then Y1 ω else Y0 ω)
    (hIgnorable :
      ∀ (a : Bool) (B : Set ℝ), MeasurableSet B → ∀ t z,
        P {ω | (if a then Y1 ω else Y0 ω) ∈ B ∧ T ω = t ∧ Z ω = z} *
            P {ω | Z ω = z} =
          P {ω | (if a then Y1 ω else Y0 ω) ∈ B ∧ Z ω = z} *
            P {ω | T ω = t ∧ Z ω = z})
    (hPositive :
      ∀ a z, 0 <
        (P {ω | T ω = a ∧ Z ω = z}).toReal / (P {ω | Z ω = z}).toReal) :
    let e : Bool → 𝒵 → ℝ := fun a z ↦
      (P {ω | T ω = a ∧ Z ω = z}).toReal / (P {ω | Z ω = z}).toReal
    ∀ a : Bool,
      ∫ ω, (if a then Y1 ω else Y0 ω) ∂P =
        ∫ ω, (if T ω = a then (1 : ℝ) else 0) * Y ω / e a (Z ω) ∂P
:= by
  /- @proof-region region.root.8fcfb28efc33 begin -/
  classical
  intro e a
  have hTa_meas : MeasurableSet {ω : Ω | T ω = a} := hTmeas (measurableSet_singleton a)
  have hZat_meas : ∀ z : 𝒵, MeasurableSet {ω : Ω | Z ω = z} :=
    fun z => hZmeas (measurableSet_singleton z)
  have hInt : ∀ b : Bool, Integrable (fun ω => if b then Y1 ω else Y0 ω) P := by
    intro b
    cases b
    · simpa using hY0int
    · simpa using hY1int
  have hAa_int : Integrable (fun ω => if a then Y1 ω else Y0 ω) P := hInt a
  have hep : ∀ z : 𝒵, 0 < e a z := fun z => hPositive a z
  have hpt : ∀ ω : Ω,
      (if T ω = a then (1 : ℝ) else 0) * (if T ω then Y1 ω else Y0 ω) / e a (Z ω)
        = (if T ω = a then (1 : ℝ) else 0) * (if a then Y1 ω else Y0 ω) / e a (Z ω) := by
    intro ω
    by_cases h : T ω = a
    · rw [← h]
    · rw [if_neg h, zero_mul, zero_mul]
  have hstep1 :
      ∫ ω, (if T ω = a then (1 : ℝ) else 0) * Y ω / e a (Z ω) ∂P
        = ∫ ω, (if T ω = a then (1 : ℝ) else 0) * (if a then Y1 ω else Y0 ω) / e a (Z ω) ∂P := by
    have hmul : ∀ ω : Ω, Y ω = (if T ω then Y1 ω else Y0 ω) →
        (if T ω = a then (1 : ℝ) else 0) * Y ω / e a (Z ω)
          = (if T ω = a then (1 : ℝ) else 0) * (if T ω then Y1 ω else Y0 ω) / e a (Z ω) := by
      intro ω hω
      rw [hω]
    have h1 : (fun ω => (if T ω = a then (1 : ℝ) else 0) * Y ω / e a (Z ω))
        =ᵐ[P] (fun ω => (if T ω = a then (1 : ℝ) else 0) *
          (if T ω then Y1 ω else Y0 ω) / e a (Z ω)) := by
      filter_upwards [hObserved] with ω hω
      exact hmul ω hω
    calc ∫ ω, (if T ω = a then (1 : ℝ) else 0) * Y ω / e a (Z ω) ∂P
        = ∫ ω, (if T ω = a then (1 : ℝ) else 0) * (if T ω then Y1 ω else Y0 ω) / e a (Z ω) ∂P :=
          integral_congr_ae h1
      _ = ∫ ω, (if T ω = a then (1 : ℝ) else 0) * (if a then Y1 ω else Y0 ω) / e a (Z ω) ∂P := by
          rw [funext hpt]
  rw [hstep1]
  have hene : ∀ z : 𝒵, e a z ≠ 0 := fun z => (hep z).ne'
  have hPsum : P = ∑ z : 𝒵, P.restrict {ω : Ω | Z ω = z} := by
    ext s hs
    rw [Measure.finset_sum_apply]
    rw [Finset.sum_congr rfl (fun z _ => Measure.restrict_apply hs)]
    have hbi : P (⋃ b ∈ (Finset.univ : Finset 𝒵), (s ∩ {ω : Ω | Z ω = b}))
        = ∑ p ∈ (Finset.univ : Finset 𝒵), P (s ∩ {ω : Ω | Z ω = p}) := by
      refine measure_biUnion_finset ?_ ?_
      · intro z _ z' _ hne
        show Disjoint (s ∩ {ω : Ω | Z ω = z}) (s ∩ {ω : Ω | Z ω = z'})
        rw [Set.disjoint_left]
        intro x h1 h2
        rw [Set.mem_inter_iff] at h1 h2
        have h1' : Z x = z := h1.2
        have h2' : Z x = z' := h2.2
        exact hne (h1'.symm.trans h2')
      · intro b _
        exact hs.inter (hZat_meas b)
    have hUeq : (⋃ b ∈ (Finset.univ : Finset 𝒵), (s ∩ {ω : Ω | Z ω = b})) = s := by
      ext x
      constructor
      · intro hx
        rcases Set.mem_iUnion.1 hx with ⟨b, hx⟩
        rcases Set.mem_iUnion.1 hx with ⟨-, hx⟩
        rw [Set.mem_inter_iff] at hx
        exact hx.1
      · intro hx
        exact Set.mem_iUnion.2 ⟨Z x, Set.mem_iUnion.2 ⟨Finset.mem_univ _, by simp [hx]⟩⟩
    rw [hUeq] at hbi
    exact hbi
  have hpt_ind : ∀ ω : Ω,
      (if T ω = a then (1 : ℝ) else 0) * (if a then Y1 ω else Y0 ω)
        = {ω : Ω | T ω = a}.indicator (fun ω => if a then Y1 ω else Y0 ω) ω := by
    intro ω
    by_cases h : T ω = a
    · rw [if_pos h]
      rw [Set.indicator_of_mem (by simpa using h), one_mul]
    · rw [if_neg h, zero_mul]
      simp [h]
  have hpt_div : ∀ (z : 𝒵) (ω : Ω), Z ω = z →
      (if T ω = a then (1 : ℝ) else 0) * (if a then Y1 ω else Y0 ω) / e a (Z ω)
        = (e a z)⁻¹ * ({ω : Ω | T ω = a}.indicator (fun ω => if a then Y1 ω else Y0 ω) ω) := by
    intro z ω hZ
    rw [hZ, hpt_ind ω, div_eq_mul_inv, mul_comm]
  have hz_ae : ∀ z : 𝒵,
      (fun ω => (if T ω = a then (1 : ℝ) else 0) * (if a then Y1 ω else Y0 ω) / e a (Z ω))
        =ᵐ[P.restrict {ω : Ω | Z ω = z}]
        (fun ω => (e a z)⁻¹ * ({ω : Ω | T ω = a}.indicator (fun ω => if a then Y1 ω else Y0 ω) ω)) := by
    intro z
    filter_upwards [ae_restrict_mem (hZat_meas z)] with ω hω
    exact hpt_div z ω (by simpa using hω)
  have hz : ∀ z : 𝒵,
      ∫ ω in {ω : Ω | Z ω = z}, (if T ω = a then (1 : ℝ) else 0) * (if a then Y1 ω else Y0 ω) / e a (Z ω) ∂P
        = ∫ ω in {ω : Ω | Z ω = z}, (if a then Y1 ω else Y0 ω) ∂P := by
    intro z
    have hA : ∫ ω in {ω : Ω | Z ω = z}, (if T ω = a then (1 : ℝ) else 0) * (if a then Y1 ω else Y0 ω) / e a (Z ω) ∂P
        = (e a z)⁻¹ * ∫ ω in {ω : Ω | Z ω = z}, ({ω : Ω | T ω = a}.indicator (fun ω => if a then Y1 ω else Y0 ω) ω) ∂P := by
      rw [integral_congr_ae (hz_ae z), integral_const_mul]
    have hB : ∫ ω in {ω : Ω | Z ω = z}, ({ω : Ω | T ω = a}.indicator (fun ω => if a then Y1 ω else Y0 ω) ω) ∂P
        = ∫ ω in {ω : Ω | T ω = a} ∩ {ω : Ω | Z ω = z}, (if a then Y1 ω else Y0 ω) ∂P := by
      rw [integral_indicator hTa_meas, Measure.restrict_restrict hTa_meas]
    have hC : ∫ ω in {ω : Ω | T ω = a} ∩ {ω : Ω | Z ω = z}, (if a then Y1 ω else Y0 ω) ∂P
        = e a z * ∫ ω in {ω : Ω | Z ω = z}, (if a then Y1 ω else Y0 ω) ∂P :=
      statopia_math_node_2820037943_49881198 P T Z Y0 Y1 hTmeas hZmeas hY0meas hY1meas hZpos hPositive
        hIgnorable hInt a z
    have hD : (e a z)⁻¹ * (e a z * ∫ ω in {ω : Ω | Z ω = z}, (if a then Y1 ω else Y0 ω) ∂P)
        = ∫ ω in {ω : Ω | Z ω = z}, (if a then Y1 ω else Y0 ω) ∂P := by
      rw [← mul_assoc, inv_mul_cancel₀ (hene z), one_mul]
    rw [hA, hB, hC, hD]
  have hh_int : ∀ z ∈ (Finset.univ : Finset 𝒵),
      Integrable (fun ω => (if T ω = a then (1 : ℝ) else 0) * (if a then Y1 ω else Y0 ω) / e a (Z ω))
        (P.restrict {ω : Ω | Z ω = z}) := by
    intro z _
    have hbase : Integrable
        (fun ω => (e a z)⁻¹ * ({ω : Ω | T ω = a}.indicator (fun ω => if a then Y1 ω else Y0 ω) ω))
        (P.restrict {ω : Ω | Z ω = z}) :=
      ((Integrable.indicator hAa_int hTa_meas).const_mul (e a z)⁻¹).restrict
    exact hbase.congr (hz_ae z).symm
  have hAa_int' : ∀ z ∈ (Finset.univ : Finset 𝒵),
      Integrable (fun ω => (if a then Y1 ω else Y0 ω)) (P.restrict {ω : Ω | Z ω = z}) :=
    fun z _ => hAa_int.restrict
  have hPsum' : ∀ f : Ω → ℝ,
      ∫ ω, f ω ∂P = ∫ ω, f ω ∂(∑ z : 𝒵, P.restrict {ω : Ω | Z ω = z}) :=
    fun f => congrArg (fun ν => ∫ ω, f ω ∂ν) hPsum
  calc ∫ ω, (if a then Y1 ω else Y0 ω) ∂P
      = ∫ ω, (if a then Y1 ω else Y0 ω) ∂(∑ z : 𝒵, P.restrict {ω : Ω | Z ω = z}) :=
        hPsum' (fun ω => if a then Y1 ω else Y0 ω)
    _ = ∑ z : 𝒵, ∫ ω, (if a then Y1 ω else Y0 ω) ∂(P.restrict {ω : Ω | Z ω = z}) :=
        integral_finset_sum_measure hAa_int'
    _ = ∑ z : 𝒵, ∫ ω, (if T ω = a then (1 : ℝ) else 0) * (if a then Y1 ω else Y0 ω) / e a (Z ω)
          ∂(P.restrict {ω : Ω | Z ω = z}) := by
        refine Finset.sum_congr rfl (fun z _ => ?_)
        exact (hz z).symm
    _ = ∫ ω, (if T ω = a then (1 : ℝ) else 0) * (if a then Y1 ω else Y0 ω) / e a (Z ω)
          ∂(∑ z : 𝒵, P.restrict {ω : Ω | Z ω = z}) :=
        (integral_finset_sum_measure hh_int).symm
    _ = ∫ ω, (if T ω = a then (1 : ℝ) else 0) * (if a then Y1 ω else Y0 ω) / e a (Z ω) ∂P :=
        (hPsum' (fun ω => (if T ω = a then (1 : ℝ) else 0) * (if a then Y1 ω else Y0 ω)
          / e a (Z ω))).symm
  /- @proof-region region.root.8fcfb28efc33 end -/
