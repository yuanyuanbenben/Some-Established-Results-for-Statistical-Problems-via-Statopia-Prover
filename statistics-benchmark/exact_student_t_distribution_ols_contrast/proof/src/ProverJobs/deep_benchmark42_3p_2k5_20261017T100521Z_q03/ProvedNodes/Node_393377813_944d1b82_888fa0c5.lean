import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.ProvedNodes.Node_4173097495_a654df71_78e5a325
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.ProvedNodes.Node_467221787_65608b8a_2c042b1a
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.ProvedNodes.Node_859487190_88621b65_8a0d7230


open MeasureTheory Matrix ProbabilityTheory

open MeasureTheory Matrix ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_393377813_944d1b82 : ∀ (n : ℕ) (hn : 1 ≤ n)
    (hind : (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).map
        (fun y : Fin n → ℝ => ∑ k : Fin n, (y k) ^ 2)
      = volume.withDensity
          (fun s : ℝ => ENNReal.ofReal (gammaConvDensity ((n : ℝ) / 2) s))),
    (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)).map
        (fun y : Fin (n + 1) → ℝ => ∑ k : Fin (n + 1), (y k) ^ 2)
      = volume.withDensity
          (fun s : ℝ => ENNReal.ofReal (gammaConvDensity (((n + 1 : ℕ) : ℝ) / 2) s)) := by
  /- @proof-region region.target-node.session.c35e8b3726dce9ec begin -/
  intro n hn hind
  have key :
      ((volume.withDensity (fun s : ℝ => ENNReal.ofReal (gammaConvDensity (1 / 2) s))).prod
        (volume.withDensity (fun s : ℝ => ENNReal.ofReal (gammaConvDensity ((n : ℝ) / 2) s)))).map
        (fun p : ℝ × ℝ => p.1 + p.2)
      = volume.withDensity
          (fun s : ℝ => ENNReal.ofReal (gammaConvDensity (((n + 1 : ℕ) : ℝ) / 2) s)) := by
    have h := statopia_math_node_4173097495_a654df71 (1 / 2) ((n : ℝ) / 2) (by norm_num) (by
      have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
      positivity)
    have harith : (1 / 2 : ℝ) + (n : ℝ) / 2 = (((n + 1 : ℕ) : ℝ) / 2) := by push_cast; ring
    simpa only [harith] using h
  have hbase1 : Measure.map (fun u : ℝ => u ^ 2) (gaussianReal 0 1)
      = volume.withDensity (fun s : ℝ => ENNReal.ofReal (gammaConvDensity ((1 / 2 : ℝ)) s)) := by
    have hb := statopia_math_node_467221787_65608b8a
    let φ := MeasurableEquiv.piUnique (fun _ : Fin 1 => ℝ)
    have hmp : MeasurePreserving (⇑φ) (Measure.pi (fun _ : Fin 1 => gaussianReal 0 1)) (gaussianReal 0 1) :=
      measurePreserving_piUnique (fun _ : Fin 1 => gaussianReal 0 1)
    have hfun : (fun u : ℝ => u ^ 2) ∘ ⇑φ = (fun y : Fin 1 → ℝ => ∑ k : Fin 1, (y k) ^ 2) := by
      funext y
      simp [φ, Function.comp_apply]
    have hm : (gaussianReal 0 1).map (fun u : ℝ => u ^ 2)
        = (Measure.pi (fun _ : Fin 1 => gaussianReal 0 1)).map
            (fun y : Fin 1 → ℝ => ∑ k : Fin 1, (y k) ^ 2) := by
      conv_lhs => rw [← hmp.map_eq]
      rw [Measure.map_map (by measurability) hmp.measurable, hfun]
    rw [hm, hb]
    simp only [show (((1 : ℕ) : ℝ) / 2) = (1 / 2 : ℝ) by norm_num]
  have hdec :
      (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)).map
          (fun y : Fin (n + 1) → ℝ => ∑ k : Fin (n + 1), (y k) ^ 2)
      = ((Measure.map (fun u : ℝ => u ^ 2) (gaussianReal 0 1)).prod
          (Measure.map (fun t : Fin n → ℝ => ∑ k : Fin n, (t k) ^ 2)
            (Measure.pi (fun _ : Fin n => gaussianReal 0 1)))).map
          (fun p : ℝ × ℝ => p.1 + p.2) := by
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (0 : Fin (n + 1))
    have hmp : MeasurePreserving (⇑e) (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1))
        ((gaussianReal 0 1).prod (Measure.pi (fun _ : Fin n => gaussianReal 0 1))) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gaussianReal 0 1) 0
    have hS : (fun y : Fin (n + 1) → ℝ => ∑ k : Fin (n + 1), (y k) ^ 2)
        = (fun q : ℝ × (Fin n → ℝ) => q.1 ^ 2 + ∑ k : Fin n, (q.2 k) ^ 2) ∘ ⇑e := by
      funext y
      simp [e, Fin.sum_univ_succ, Fin.tail]
    have hstep2 :
        ((gaussianReal 0 1).prod (Measure.pi (fun _ : Fin n => gaussianReal 0 1))).map
            (fun q : ℝ × (Fin n → ℝ) => q.1 ^ 2 + ∑ k : Fin n, (q.2 k) ^ 2)
        = ((Measure.map (fun u : ℝ => u ^ 2) (gaussianReal 0 1)).prod
            (Measure.map (fun t : Fin n → ℝ => ∑ k : Fin n, (t k) ^ 2)
              (Measure.pi (fun _ : Fin n => gaussianReal 0 1)))).map
            (fun p : ℝ × ℝ => p.1 + p.2) := by
      rw [Measure.map_prod_map (gaussianReal 0 1) (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
          (by measurability) (by measurability), Measure.map_map (by measurability) (by measurability)]
      congr 1
    calc (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)).map
            (fun y : Fin (n + 1) → ℝ => ∑ k : Fin (n + 1), (y k) ^ 2)
        = (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)).map
            ((fun q : ℝ × (Fin n → ℝ) => q.1 ^ 2 + ∑ k : Fin n, (q.2 k) ^ 2) ∘ ⇑e) := by
            rw [hS]
      _ = ((Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)).map ⇑e).map
            (fun q : ℝ × (Fin n → ℝ) => q.1 ^ 2 + ∑ k : Fin n, (q.2 k) ^ 2) := by
            rw [Measure.map_map (by measurability) hmp.measurable]
      _ = ((gaussianReal 0 1).prod (Measure.pi (fun _ : Fin n => gaussianReal 0 1))).map
            (fun q : ℝ × (Fin n → ℝ) => q.1 ^ 2 + ∑ k : Fin n, (q.2 k) ^ 2) := by
            rw [hmp.map_eq]
      _ = _ := hstep2
  rw [hdec, hbase1, hind]
  exact key
  /- @proof-region region.target-node.session.c35e8b3726dce9ec end -/
