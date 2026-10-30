import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q15.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q15.Base

open Filter MeasureTheory ProbabilityTheory

open Filter MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_3660083059_ee3ca287 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (X : ℕ → Ω → Bool)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (hX_law : ∀ i,
      HasLaw (X i)
        (PMF.bernoulli ⟨θ, hθ0.le⟩ (by exact_mod_cast hθ1.le)).toMeasure P),
    (∀ i, Measurable (fun ω => if X i ω then (1 : ℝ) else 0))
    ∧ (∀ i, Measurable (fun ω => (if X i ω then (1 : ℝ) else 0) - θ))
    ∧ (∀ i, Measure.map (fun ω => if X i ω then (1 : ℝ) else 0) P
        = Measure.map (fun b : Bool => if b then (1 : ℝ) else 0)
            (PMF.bernoulli ⟨θ, hθ0.le⟩ (by exact_mod_cast hθ1.le)).toMeasure)
    ∧ iIndepFun (fun i ω => (if X i ω then (1 : ℝ) else 0) - θ) P
    ∧ (∀ i j, IdentDistrib (fun ω => (if X i ω then (1 : ℝ) else 0) - θ)
        (fun ω => (if X j ω then (1 : ℝ) else 0) - θ) P P) := by
  /- @proof-region region.target-node.session.774cff5255ea99e6 begin -/
  intro Ω _ P _ θ hθ0 hθ1 X hX_meas hX_indep hX_law
  have hg : Measurable (fun b : Bool => if b then (1 : ℝ) else 0) := measurable_of_finite _
  have hh : Measurable (fun b : Bool => (if b then (1 : ℝ) else 0) - θ) :=
    hg.sub measurable_const
  have hξ : ∀ i : ℕ, Measurable (fun ω => if X i ω then (1 : ℝ) else 0) := fun i =>
    hg.comp (hX_meas i)
  have hY : ∀ i : ℕ, Measurable (fun ω => (if X i ω then (1 : ℝ) else 0) - θ) := fun i =>
    (hξ i).sub measurable_const
  refine ⟨hξ, hY, ?_, ?_, ?_⟩
  · intro i
    have hi : Measure.map (X i) P
        = (PMF.bernoulli ⟨θ, hθ0.le⟩ (by exact_mod_cast hθ1.le)).toMeasure :=
      ((hX_law i).measurePreserving (hX_meas i)).map_eq
    calc Measure.map (fun ω => if X i ω then (1 : ℝ) else 0) P
        = Measure.map (fun b : Bool => if b then (1 : ℝ) else 0) (Measure.map (X i) P) :=
          (Measure.map_map hg (hX_meas i)).symm
      _ = Measure.map (fun b : Bool => if b then (1 : ℝ) else 0)
            (PMF.bernoulli ⟨θ, hθ0.le⟩ (by exact_mod_cast hθ1.le)).toMeasure := by rw [hi]
  · exact hX_indep.comp (fun (_ : ℕ) (b : Bool) => (if b then (1 : ℝ) else 0) - θ)
      (fun _ => hh)
  · intro i j
    have hi : Measure.map (X i) P
        = (PMF.bernoulli ⟨θ, hθ0.le⟩ (by exact_mod_cast hθ1.le)).toMeasure :=
      ((hX_law i).measurePreserving (hX_meas i)).map_eq
    have hj : Measure.map (X j) P
        = (PMF.bernoulli ⟨θ, hθ0.le⟩ (by exact_mod_cast hθ1.le)).toMeasure :=
      ((hX_law j).measurePreserving (hX_meas j)).map_eq
    refine ⟨(hY i).aemeasurable, (hY j).aemeasurable, ?_⟩
    calc Measure.map (fun ω => (if X i ω then (1 : ℝ) else 0) - θ) P
        = Measure.map (fun b : Bool => (if b then (1 : ℝ) else 0) - θ)
            (Measure.map (X i) P) := (Measure.map_map hh (hX_meas i)).symm
      _ = Measure.map (fun b : Bool => (if b then (1 : ℝ) else 0) - θ)
            (PMF.bernoulli ⟨θ, hθ0.le⟩ (by exact_mod_cast hθ1.le)).toMeasure := by rw [hi]
      _ = Measure.map (fun b : Bool => (if b then (1 : ℝ) else 0) - θ)
            (Measure.map (X j) P) := by rw [hj]
      _ = Measure.map (fun ω => (if X j ω then (1 : ℝ) else 0) - θ) P :=
          Measure.map_map hh (hX_meas j)
  /- @proof-region region.target-node.session.774cff5255ea99e6 end -/
