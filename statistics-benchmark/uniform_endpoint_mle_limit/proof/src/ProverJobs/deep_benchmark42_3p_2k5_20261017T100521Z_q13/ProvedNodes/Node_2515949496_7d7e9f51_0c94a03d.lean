import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q13.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q13.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q13.ProvedNodes.Node_394219309_051c530b_a4086216

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

set_option autoImplicit false in
theorem statopia_math_node_2515949496_7d7e9f51 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : ℝ) (hθ : 0 < θ)
    (X : ℕ → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (hX_uniform : ∀ i, MeasureTheory.pdf.IsUniform (X i) (Set.Ioo 0 θ) P)
    (t : ℝ) (ht : 0 < t),
    (∀ r : ℕ, t < (((r + 1 : ℕ) : ℝ) * θ) →
      (P.map (fun ω ↦ (((r + 1 : ℕ) : ℝ) *
          (θ - (Finset.univ : Finset (Fin (r + 1))).sup'
            Finset.univ_nonempty (fun i ↦ X i.1 ω))))) (Set.Iic t)
        = ENNReal.ofReal (1 - (1 - t / (((r + 1 : ℕ) : ℝ) * θ)) ^ (r + 1)))
    ∧ Tendsto
        (fun r : ℕ ↦
          ((P.map (fun ω ↦ (((r + 1 : ℕ) : ℝ) *
            (θ - (Finset.univ : Finset (Fin (r + 1))).sup'
              Finset.univ_nonempty (fun i ↦ X i.1 ω))))) (Set.Iic t)).toReal)
        atTop (nhds (1 - Real.exp (-t / θ))) := by
  /- @proof-region region.target-node.session.9a3fabc58e3be5f1 begin -/
  intro Ω _inst P _Pinst θ hθ X hX_meas hX_indep hX_uniform t ht
  have hA : ∀ r : ℕ, t < (((r + 1 : ℕ) : ℝ) * θ) →
      (P.map (fun ω ↦ (((r + 1 : ℕ) : ℝ) *
          (θ - (Finset.univ : Finset (Fin (r + 1))).sup'
            Finset.univ_nonempty (fun i ↦ X i.1 ω))))) (Set.Iic t)
        = ENNReal.ofReal (1 - (1 - t / (((r + 1 : ℕ) : ℝ) * θ)) ^ (r + 1)) := by
    intro r hr
    set n : ℝ := ((r + 1 : ℕ) : ℝ) with hn
    have hnpos : 0 < n := by
      rw [hn]; positivity
    let M : Ω → ℝ := fun ω => (Finset.univ : Finset (Fin (r + 1))).sup' Finset.univ_nonempty (fun i => X i.1 ω)
    have hMmeas : Measurable M := by
      have hlift : Measurable ((Finset.univ : Finset (Fin (r + 1))).sup' Finset.univ_nonempty (fun (i : Fin (r + 1)) => X i.1)) :=
        Finset.measurable_sup' (f := fun (i : Fin (r + 1)) => X i.1) Finset.univ_nonempty (fun i _ => hX_meas i.1)
      have heq : ((Finset.univ : Finset (Fin (r + 1))).sup' Finset.univ_nonempty (fun (i : Fin (r + 1)) => X i.1))
          = (fun ω => (Finset.univ : Finset (Fin (r + 1))).sup' Finset.univ_nonempty (fun i => X i.1 ω)) := by
        funext ω
        exact Finset.sup'_apply Finset.univ_nonempty (fun (i : Fin (r + 1)) => X i.1) ω
      show Measurable (fun ω => (Finset.univ : Finset (Fin (r + 1))).sup' Finset.univ_nonempty (fun i => X i.1 ω))
      rw [← heq]
      exact hlift
    have hVmeas : Measurable (fun ω => n * (θ - M ω)) :=
      (measurable_const : Measurable (fun _ : Ω => n)).mul ((measurable_const : Measurable (fun _ : Ω => θ)).sub hMmeas)
    have hset : (fun ω => n * (θ - M ω)) ⁻¹' (Set.Iic t) = {ω | M ω < θ - t / n}ᶜ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_compl_iff, Set.mem_setOf_eq]
      constructor
      · intro h hlt
        have h1 : t / n < θ - M ω := by linarith
        have h2 : n * (t / n) < n * (θ - M ω) := mul_lt_mul_of_pos_left h1 hnpos
        have h3 : n * (t / n) = t := by rw [mul_comm]; exact div_mul_cancel₀ t (ne_of_gt hnpos)
        linarith
      · intro hlt
        have h1 : θ - t / n ≤ M ω := by linarith
        have h2 : θ - M ω ≤ t / n := by linarith
        have h3 : n * (θ - M ω) ≤ n * (t / n) := mul_le_mul_of_nonneg_left h2 (le_of_lt hnpos)
        have h4 : n * (t / n) = t := by rw [mul_comm]; exact div_mul_cancel₀ t (ne_of_gt hnpos)
        linarith
    have hmeas_set : MeasurableSet {ω | M ω < θ - t / n} := hMmeas measurableSet_Iio
    have hapos : 0 < θ - t / n := by
      have h1 : t / n < θ := by
        rw [div_lt_iff₀ hnpos, mul_comm θ n]
        exact hr
      linarith
    have halt : θ - t / n < θ := by
      have h2 : 0 < t / n := div_pos ht hnpos
      linarith
    have hdep : P {ω | M ω < θ - t / n} = ENNReal.ofReal (((θ - t / n) / θ) ^ (r + 1)) := by
      have hd : (P {ω | (Finset.univ : Finset (Fin (r + 1))).sup' Finset.univ_nonempty (fun i => X i.1 ω) < θ - t / n}).toReal = ((θ - t / n) / θ) ^ (r + 1) :=
        statopia_math_node_394219309_051c530b P θ hθ X hX_meas hX_indep hX_uniform r (θ - t / n) hapos halt
      have hdt : (P {ω | M ω < θ - t / n}).toReal = ((θ - t / n) / θ) ^ (r + 1) := hd
      rw [← ENNReal.ofReal_toReal (measure_ne_top P {ω | M ω < θ - t / n}), hdt]
    have hprob : (P.map (fun ω => n * (θ - M ω))) (Set.Iic t) = 1 - ENNReal.ofReal (((θ - t / n) / θ) ^ (r + 1)) := by
      rw [Measure.map_apply hVmeas measurableSet_Iic, hset,
        measure_compl hmeas_set (measure_ne_top P {ω | M ω < θ - t / n}), measure_univ, hdep]
    have haratio : (θ - t / n) / θ = 1 - t / (n * θ) := by
      field_simp
    have hden : 0 < n * θ := mul_pos hnpos hθ
    have htθ1 : t / (n * θ) ≤ 1 := (div_le_one hden).2 (le_of_lt hr)
    have htθ0 : 0 ≤ t / (n * θ) := div_nonneg (le_of_lt ht) (le_of_lt hden)
    have hbase : 0 ≤ 1 - t / (n * θ) := by linarith
    have hbase1 : 1 - t / (n * θ) ≤ 1 := by linarith
    have hpowneg : 0 ≤ (1 - t / (n * θ)) ^ (r + 1) := pow_nonneg hbase _
    have hconv : 1 - ENNReal.ofReal ((1 - t / (n * θ)) ^ (r + 1)) = ENNReal.ofReal (1 - (1 - t / (n * θ)) ^ (r + 1)) := by
      rw [ENNReal.ofReal_sub 1 hpowneg, ENNReal.ofReal_one]
    have hpowle : ((θ - t / n) / θ) ^ (r + 1) = (1 - t / (n * θ)) ^ (r + 1) := by rw [haratio]
    rw [hprob, hpowle, hconv]
  constructor
  · exact hA
  · have hev_thresh : ∀ᶠ r : ℕ in atTop, t < (((r + 1 : ℕ) : ℝ) * θ) := by
      obtain ⟨N, hN⟩ := exists_nat_gt (t / θ)
      refine Filter.eventually_atTop.2 ⟨N, fun r hr => ?_⟩
      have hNr : (N : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      have hle : t / θ < (r : ℝ) := by linarith
      rw [div_lt_iff₀ hθ] at hle
      have hcast : (((r + 1 : ℕ) : ℝ)) = (r : ℝ) + 1 := by rw [Nat.cast_add, Nat.cast_one]
      rw [hcast]
      nlinarith [hle, hθ]
    have hev_eq : (fun r : ℕ => ((P.map (fun ω => (((r + 1 : ℕ) : ℝ) *
        (θ - (Finset.univ : Finset (Fin (r + 1))).sup'
          Finset.univ_nonempty (fun i => X i.1 ω))))) (Set.Iic t)).toReal)
        =ᶠ[atTop] (fun r : ℕ => 1 - (1 + (-t / θ) / (((r + 1 : ℕ) : ℝ))) ^ (r + 1)) := by
      filter_upwards [hev_thresh] with r hr
      have hpos_n : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := by positivity
      have hnd : 0 < (((r + 1 : ℕ) : ℝ) * θ) := mul_pos hpos_n hθ
      have hc : t / (((r + 1 : ℕ) : ℝ) * θ) ≤ 1 := by
        rw [div_le_one hnd]; exact le_of_lt hr
      have hc0 : 0 ≤ t / (((r + 1 : ℕ) : ℝ) * θ) := div_nonneg (le_of_lt ht) (le_of_lt hnd)
      have hb0 : 0 ≤ 1 - t / (((r + 1 : ℕ) : ℝ) * θ) := by linarith
      have hb1 : 1 - t / (((r + 1 : ℕ) : ℝ) * θ) ≤ 1 := by linarith
      have hpowle : (1 - t / (((r + 1 : ℕ) : ℝ) * θ)) ^ (r + 1) ≤ 1 := pow_le_one₀ hb0 hb1
      have hnonneg : 0 ≤ 1 - (1 - t / (((r + 1 : ℕ) : ℝ) * θ)) ^ (r + 1) := by linarith
      rw [hA r hr, ENNReal.toReal_ofReal hnonneg]
      have hbase_eq : 1 - t / (((r + 1 : ℕ) : ℝ) * θ) = 1 + (-t / θ) / (((r + 1 : ℕ) : ℝ)) := by
        have hAne : (((r + 1 : ℕ) : ℝ)) ≠ 0 := ne_of_gt hpos_n
        have hθne : θ ≠ 0 := ne_of_gt hθ
        field_simp
        ring
      rw [hbase_eq]
    have hlim_pow : Tendsto (fun r : ℕ => (1 + (-t / θ) / (((r + 1 : ℕ) : ℝ))) ^ (r + 1)) atTop (nhds (Real.exp (-t / θ))) :=
      (Real.tendsto_one_add_div_pow_exp (-t / θ)).comp (tendsto_add_atTop_nat 1)
    have hlim_final : Tendsto (fun r : ℕ => 1 - (1 + (-t / θ) / (((r + 1 : ℕ) : ℝ))) ^ (r + 1)) atTop (nhds (1 - Real.exp (-t / θ))) :=
      hlim_pow.const_sub 1
    exact Filter.Tendsto.congr' hev_eq.symm hlim_final
  /- @proof-region region.target-node.session.9a3fabc58e3be5f1 end -/
