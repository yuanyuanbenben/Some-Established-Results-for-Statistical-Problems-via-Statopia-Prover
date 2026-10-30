import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q38.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q38.Base

open MeasureTheory ProbabilityTheory
open scoped BigOperators

open MeasureTheory ProbabilityTheory
open scoped BigOperators

set_option autoImplicit false in
theorem statopia_math_node_2382897187_683a51f9 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (mean : ℝ) (v : ℝ) (hv : 0 ≤ v)
    (X : Fin n → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (hX_law : ∀ i, P.map (X i) = gaussianReal mean ⟨v, hv⟩),
    let Z : Fin n → Ω → ℝ := fun i ω => X i ω - mean
    (∀ i, Measurable (Z i)) ∧ iIndepFun Z P ∧
      (∀ i, P.map (Z i) = gaussianReal 0 ⟨v, hv⟩) := by
  /- @proof-region region.target-node.session.6f84642582a7fc31 begin -/
  intro Ω _ P _ n mean v hv X hX_meas hX_indep hX_law
  dsimp only
  have hT : Measurable (fun x : ℝ => x - mean) := measurable_id.sub_const mean
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact hT.comp (hX_meas i)
  · exact hX_indep.comp (fun _ x => x - mean) (fun _ => hT)
  · intro i
    have hmap : Measure.map (fun ω => X i ω - mean) P
        = Measure.map (fun x : ℝ => x - mean) (Measure.map (X i) P) :=
      (Measure.map_map hT (hX_meas i)).symm
    calc Measure.map (fun ω => X i ω - mean) P
        = Measure.map (fun x : ℝ => x - mean) (Measure.map (X i) P) := hmap
      _ = Measure.map (fun x : ℝ => x - mean) (gaussianReal mean ⟨v, hv⟩) :=
          congrArg (Measure.map (fun x : ℝ => x - mean)) (hX_law i)
      _ = gaussianReal (mean - mean) ⟨v, hv⟩ := gaussianReal_map_sub_const mean
      _ = gaussianReal 0 ⟨v, hv⟩ :=
          congrArg (fun t : ℝ => gaussianReal t ⟨v, hv⟩) (sub_self mean)
  /- @proof-region region.target-node.session.6f84642582a7fc31 end -/
