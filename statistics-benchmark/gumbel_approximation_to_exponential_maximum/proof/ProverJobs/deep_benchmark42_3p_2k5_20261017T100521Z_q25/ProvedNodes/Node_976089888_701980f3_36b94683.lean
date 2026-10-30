import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q25.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q25.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q25.ProvedNodes.Node_401495820_d3a33ec9_12ddf63d

open MeasureTheory ProbabilityTheory
open scoped BigOperators

open MeasureTheory ProbabilityTheory
open scoped BigOperators

set_option autoImplicit false in
theorem statopia_math_node_976089888_701980f3 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n)
    (X : Fin n → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (hX_law : ∀ i, IdentDistrib (X i) id P (expMeasure 1))
    (x : ℝ),
    ENNReal.toReal
        (P {ω |
          (Finset.univ : Finset (Fin n)).sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩
              (fun i => X i ω) - Real.log (n : ℝ) ≤ x})
      = (max 0 (1 - Real.exp (-x) / (n : ℝ))) ^ n := by
  /- @proof-region region.target-node.session.3d49d77036716fbc begin -/
  intro Ω _ P _ n hn X hX_meas hX_indep hX_law x
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have h : (0 : ℕ) < n := lt_of_lt_of_le Nat.zero_lt_one hn
    exact_mod_cast h
  have hfac : ∀ i : Fin n,
      P (X i ⁻¹' Set.Iic (Real.log (n : ℝ) + x))
        = ENNReal.ofReal (1 - Real.exp (-x) / (n : ℝ)) := by
    intro i
    have h2 : P (X i ⁻¹' Set.Iic (Real.log (n : ℝ) + x))
        = (expMeasure 1) (Set.Iic (Real.log (n : ℝ) + x)) := by
      simpa using (hX_law i).measure_mem_eq (s := Set.Iic (Real.log (n : ℝ) + x)) measurableSet_Iic
    have hexp : Real.exp (-(Real.log (n : ℝ) + x)) = Real.exp (-x) / (n : ℝ) := by
      calc Real.exp (-(Real.log (n : ℝ) + x))
          = Real.exp (-(Real.log (n : ℝ))) * Real.exp (-x) := by rw [neg_add, Real.exp_add]
        _ = (Real.exp (Real.log (n : ℝ)))⁻¹ * Real.exp (-x) := by rw [Real.exp_neg]
        _ = (n : ℝ)⁻¹ * Real.exp (-x) := by rw [Real.exp_log hnpos]
        _ = Real.exp (-x) / (n : ℝ) := by rw [div_eq_inv_mul]
    rw [h2, statopia_math_node_401495820_d3a33ec9, hexp]
  have hset : {ω : Ω |
        (Finset.univ : Finset (Fin n)).sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩
            (fun i => X i ω) - Real.log (n : ℝ) ≤ x}
      = ⋂ i : Fin n, X i ⁻¹' Set.Iic (Real.log (n : ℝ) + x) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_Iic]
    show (Finset.univ : Finset (Fin n)).sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩
        (fun i => X i ω) - Real.log (n : ℝ) ≤ x
      ↔ ∀ i : Fin n, X i ω ≤ Real.log (n : ℝ) + x
    rw [sub_le_iff_le_add, add_comm x, Finset.sup'_le_iff ⟨⟨0, hn⟩, Finset.mem_univ _⟩]
    simp
  have hprod : P (⋂ i : Fin n, X i ⁻¹' Set.Iic (Real.log (n : ℝ) + x))
      = ∏ i : Fin n, P (X i ⁻¹' Set.Iic (Real.log (n : ℝ) + x)) := by
    have h := hX_indep.measure_inter_preimage_eq_mul (Finset.univ : Finset (Fin n))
      (sets := fun i => Set.Iic (Real.log (n : ℝ) + x)) (fun i _ => measurableSet_Iic)
    simpa using h
  have hprod' : ∏ i : Fin n, P (X i ⁻¹' Set.Iic (Real.log (n : ℝ) + x))
      = ENNReal.ofReal (1 - Real.exp (-x) / (n : ℝ)) ^ n := by
    simp only [hfac, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hset, hprod, hprod', ENNReal.toReal_pow, ENNReal.toReal_ofReal', max_comm]
  /- @proof-region region.target-node.session.3d49d77036716fbc end -/
