import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q17.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q17.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q17.ProvedNodes.Node_444070725_2ef7631b_919b314f
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q17.ProvedNodes.Node_482029874_f417c92e_c8c152fa


open MeasureTheory

open MeasureTheory

set_option autoImplicit false in
theorem statopia_math_node_2053934716_e66d820a : ∀ {Ω 𝒵 : Type*}
    [MeasurableSpace Ω]
    [Fintype 𝒵]
    [MeasurableSpace 𝒵]
    [MeasurableSingletonClass 𝒵]
    (P : Measure Ω)
    [IsProbabilityMeasure P]
    (R : Ω → Bool)
    (Z : Ω → 𝒵)
    (Y : Ω → ℝ)
    (hRmeas : Measurable R)
    (hZmeas : Measurable Z)
    (hYmeas : Measurable Y)
    (hYint : Integrable Y P)
    (hZpos : ∀ z, 0 < P {ω | Z ω = z})
    (hMAR :
      ∀ (B : Set ℝ), MeasurableSet B → ∀ r z,
        P {ω | Y ω ∈ B ∧ R ω = r ∧ Z ω = z} * P {ω | Z ω = z} =
          P {ω | Y ω ∈ B ∧ Z ω = z} * P {ω | R ω = r ∧ Z ω = z})
    (m : 𝒵 → ℝ)
    (π : 𝒵 → ℝ)
    (hπne : ∀ z, π z ≠ 0),
    let A : 𝒵 → ℝ := fun z ↦ (P {ω | Z ω = z}).toReal
    let m0 : 𝒵 → ℝ := fun z ↦ (∫ ω in {ω | Z ω = z}, Y ω ∂P) / A z
    let π0 : 𝒵 → ℝ := fun z ↦ (P {ω | R ω = true ∧ Z ω = z}).toReal / A z
    Integrable
        (fun ω ↦ m (Z ω) + (if R ω then (1 : ℝ) else 0) / π (Z ω) * (Y ω - m (Z ω))) P ∧
      ∫ ω, (m (Z ω) + (if R ω then (1 : ℝ) else 0) / π (Z ω) * (Y ω - m (Z ω))) ∂P
        = ∑ z, A z * (m z + (π0 z / π z) * (m0 z - m z)) := by
  /- @proof-region region.target-node.session.f0484915c9d70561 begin -/
  intro Omega Zt _ _ _ _ P _ R Z Y hRmeas hZmeas hYmeas hYint hZpos hMAR m π hpine
  classical
  dsimp only
  have hT : ∀ z : Zt, MeasurableSet ({ω | Z ω = z} : Set Omega) :=
    fun z => hZmeas (measurableSet_singleton z)
  have hRset : MeasurableSet ({ω | R ω = true} : Set Omega) :=
    hRmeas (measurableSet_singleton true)
  have hg_int : ∀ z : Zt,
      Integrable (fun ω => m z + (if R ω then (1 : ℝ) else 0) / π z * (Y ω - m z)) P := by
    intro z
    have hbase : Integrable (fun ω => (1 / π z) * (Y ω - m z)) P :=
      (hYint.sub (integrable_const (m z))).const_mul (1 / π z)
    have hind : Integrable (({ω | R ω = true} : Set Omega).indicator
        (fun ω => (1 / π z) * (Y ω - m z))) P := hbase.indicator hRset
    have hsum : Integrable (fun ω => m z + ({ω | R ω = true} : Set Omega).indicator
        (fun ω => (1 / π z) * (Y ω - m z)) ω) P :=
      (integrable_const (m z)).add hind
    have hpt : (fun ω => m z + ({ω | R ω = true} : Set Omega).indicator
        (fun ω => (1 / π z) * (Y ω - m z)) ω)
        = fun ω => m z + (if R ω then (1 : ℝ) else 0) / π z * (Y ω - m z) := by
      funext ω
      by_cases hR : R ω = true <;> simp [Set.indicator, hR]
    rw [hpt] at hsum
    exact hsum
  obtain ⟨hInt, hInteq⟩ :=
    statopia_math_node_482029874_f417c92e P (fun z : Zt => ({ω | Z ω = z} : Set Omega)) hT
      (fun z ω => m z + (if R ω then (1 : ℝ) else 0) / π z * (Y ω - m z)) hg_int
  have h_eq :
      (fun ω => ∑ z : Zt, ({ω | Z ω = z} : Set Omega).indicator
          (fun ω => m z + (if R ω then (1 : ℝ) else 0) / π z * (Y ω - m z)) ω) =
        fun ω => m (Z ω) + (if R ω then (1 : ℝ) else 0) / π (Z ω) * (Y ω - m (Z ω)) := by
    funext ω
    refine Eq.trans (Finset.sum_eq_single (s := Finset.univ) (a := Z ω) ?_ ?_) ?_
    · intro z _ hz
      have hmem : ω ∉ ({ω | Z ω = z} : Set Omega) := fun h => hz h.symm
      simp [Set.indicator, hmem]
    · intro h
      exact absurd (Finset.mem_univ (Z ω)) h
    · simp [Set.indicator]
  rw [← h_eq]
  refine ⟨hInt, ?_⟩
  rw [hInteq]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  set A : ℝ := (P {ω | Z ω = z}).toReal with hAdef
  set B : ℝ := (P {ω | R ω = true ∧ Z ω = z}).toReal with hBdef
  set I : ℝ := ∫ ω in {ω | Z ω = z}, Y ω ∂P with hIdef
  have hS : MeasurableSet ({ω | R ω = true ∧ Z ω = z} : Set Omega) := hRset.inter (hT z)
  have hreal : ∀ (μ : Measure Omega) (s : Set Omega), μ.real s = (μ s).toReal :=
    fun μ s => rfl
  have hsetconst : ∀ (s : Set Omega) (c : ℝ), ∫ ω in s, c ∂P = (P s).toReal * c := by
    intro s c
    rw [integral_const]
    simp [hreal, Measure.restrict_apply, smul_eq_mul]
  have hApos : 0 < A := by
    rw [hAdef]
    have hle : P {ω | Z ω = z} ≤ 1 := by
      have h1 : P {ω | Z ω = z} ≤ P Set.univ := measure_mono (Set.subset_univ _)
      simpa using h1
    exact ENNReal.toReal_pos (hZpos z).ne' (ne_top_of_le_ne_top ENNReal.one_ne_top hle)
  have e1 : ∫ ω in ({ω | Z ω = z} : Set Omega),
        (m z + (if R ω then (1 : ℝ) else 0) / π z * (Y ω - m z)) ∂P
      = ∫ ω, ({ω | Z ω = z} : Set Omega).indicator
          (fun ω => m z + (if R ω then (1 : ℝ) else 0) / π z * (Y ω - m z)) ω ∂P :=
    (integral_indicator (hT z)).symm
  have hconst : ∫ ω in ({ω | Z ω = z} : Set Omega), m z ∂P = A * m z := by
    rw [hsetconst, hAdef]
  have hAne : A ≠ 0 := hApos.ne'
  have hphi : Integrable (fun ω => (1 / π z) * ((if R ω then (1 : ℝ) else 0) * (Y ω - m z))) P := by
    have h1 : Integrable (fun ω => (1 / π z) * ({ω | R ω = true} : Set Omega).indicator
        (fun ω => Y ω - m z) ω) P :=
      (hYint.sub (integrable_const (m z))).indicator hRset |>.const_mul (1 / π z)
    have hfun : (fun ω => (1 / π z) * ({ω | R ω = true} : Set Omega).indicator
        (fun ω => Y ω - m z) ω)
        = fun ω => (1 / π z) * ((if R ω then (1 : ℝ) else 0) * (Y ω - m z)) := by
      funext ω
      by_cases hR : R ω = true <;> simp [Set.indicator, hR]
    rw [hfun] at h1
    exact h1
  have hSindY : Integrable (fun ω => ({ω | R ω = true ∧ Z ω = z} : Set Omega).indicator Y ω) P :=
    hYint.indicator hS
  have hSindm : Integrable (fun ω => ({ω | R ω = true ∧ Z ω = z} : Set Omega).indicator
      (fun _ => m z) ω) P := (integrable_const (m z)).indicator hS
  have hdec : ∀ ω, ({ω | Z ω = z} : Set Omega).indicator
      (fun ω => m z + (if R ω then (1 : ℝ) else 0) / π z * (Y ω - m z)) ω
      = ({ω | Z ω = z} : Set Omega).indicator (fun _ => m z) ω
        + ({ω | Z ω = z} : Set Omega).indicator
            (fun ω => (1 / π z) * ((if R ω then (1 : ℝ) else 0) * (Y ω - m z))) ω := by
    intro ω
    by_cases hmem : ω ∈ ({ω | Z ω = z} : Set Omega)
    · simp only [Set.indicator_of_mem hmem]
      ring
    · simp [Set.indicator, hmem]
  have estep : ∫ ω, ({ω | Z ω = z} : Set Omega).indicator
      (fun ω => m z + (if R ω then (1 : ℝ) else 0) / π z * (Y ω - m z)) ω ∂P
      = ∫ ω, ({ω | Z ω = z} : Set Omega).indicator (fun _ => m z) ω ∂P
        + ∫ ω, ({ω | Z ω = z} : Set Omega).indicator
            (fun ω => (1 / π z) * ((if R ω then (1 : ℝ) else 0) * (Y ω - m z))) ω ∂P := by
    rw [funext hdec]
    rw [integral_add ((integrable_const (m z)).indicator (hT z)) (hphi.indicator (hT z))]
  have ec1 : ∫ ω, ({ω | Z ω = z} : Set Omega).indicator (fun _ => m z) ω ∂P = m z * A := by
    rw [integral_indicator (hT z), hconst]
    ring
  have hK1 : ∀ ω, ({ω | Z ω = z} : Set Omega).indicator
      (fun ω => (if R ω then (1 : ℝ) else 0) * (Y ω - m z)) ω
      = ({ω | R ω = true ∧ Z ω = z} : Set Omega).indicator (fun ω => Y ω - m z) ω := by
    intro ω
    by_cases hZ : Z ω = z
    · by_cases hR : R ω = true <;> simp [Set.indicator, hZ, hR]
    · have hT' : ω ∉ ({ω | Z ω = z} : Set Omega) := hZ
      have hS' : ω ∉ ({ω | R ω = true ∧ Z ω = z} : Set Omega) := fun h => hZ h.2
      simp [Set.indicator, hT', hS']
  have hsplit : ∀ ω, ({ω | R ω = true ∧ Z ω = z} : Set Omega).indicator
      (fun ω => Y ω - m z) ω
      = ({ω | R ω = true ∧ Z ω = z} : Set Omega).indicator Y ω
        - ({ω | R ω = true ∧ Z ω = z} : Set Omega).indicator (fun _ => m z) ω := by
    intro ω
    by_cases hmem : ω ∈ ({ω | R ω = true ∧ Z ω = z} : Set Omega)
    · simp only [Set.indicator_of_mem hmem]
    · simp [Set.indicator, hmem]
  have eS1 : ∫ ω, ({ω | R ω = true ∧ Z ω = z} : Set Omega).indicator Y ω ∂P
      = ∫ ω in ({ω | R ω = true ∧ Z ω = z} : Set Omega), Y ω ∂P :=
    integral_indicator hS
  have eS2 : ∫ ω, ({ω | R ω = true ∧ Z ω = z} : Set Omega).indicator (fun _ => m z) ω ∂P
      = m z * B := by
    rw [integral_indicator hS, hsetconst, hBdef]
    ring
  have epull : ∫ ω, ({ω | Z ω = z} : Set Omega).indicator
      (fun ω => (1 / π z) * ((if R ω then (1 : ℝ) else 0) * (Y ω - m z))) ω ∂P
      = (1 / π z) * ∫ ω, ({ω | Z ω = z} : Set Omega).indicator
          (fun ω => (if R ω then (1 : ℝ) else 0) * (Y ω - m z)) ω ∂P := by
    have hfun : (fun ω => ({ω | Z ω = z} : Set Omega).indicator
        (fun ω => (1 / π z) * ((if R ω then (1 : ℝ) else 0) * (Y ω - m z))) ω)
        = fun ω => (1 / π z) * (({ω | Z ω = z} : Set Omega).indicator
            (fun ω => (if R ω then (1 : ℝ) else 0) * (Y ω - m z)) ω) := by
      funext ω
      by_cases hmem : ω ∈ ({ω | Z ω = z} : Set Omega)
      · simp only [Set.indicator_of_mem hmem]
      · simp [Set.indicator, hmem]
    rw [hfun, integral_const_mul]
  have eT : ∫ ω, ({ω | Z ω = z} : Set Omega).indicator
      (fun ω => (if R ω then (1 : ℝ) else 0) * (Y ω - m z)) ω ∂P
      = ∫ ω, ({ω | R ω = true ∧ Z ω = z} : Set Omega).indicator (fun ω => Y ω - m z) ω ∂P := by
    rw [funext hK1]
  have eS : ∫ ω, ({ω | R ω = true ∧ Z ω = z} : Set Omega).indicator (fun ω => Y ω - m z) ω ∂P
      = ∫ ω in ({ω | R ω = true ∧ Z ω = z} : Set Omega), Y ω ∂P - m z * B := by
    rw [funext hsplit]
    rw [integral_sub hSindY hSindm]
    rw [eS1, eS2]
  have hJ : ∫ ω in ({ω | R ω = true ∧ Z ω = z} : Set Omega), Y ω ∂P = (B / A) * I := by
    have h :=
      statopia_math_node_444070725_2ef7631b P R Z Y hRmeas hZmeas hYmeas hYint hZpos hMAR z
    simpa [hAdef, hBdef, hIdef] using h
  rw [e1, estep, ec1, epull, eT, eS, hJ]
  field_simp
  /- @proof-region region.target-node.session.f0484915c9d70561 end -/
