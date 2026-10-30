import ProverJobs.paper_fresh_20261030t143835550708z_hulc.Vocabulary
import ProverJobs.paper_fresh_20261030t143835550708z_hulc.ProvedNodes
import ProverJobs.paper_fresh_20261030t143835550708z_hulc.Base

namespace Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section

theorem Theorem_1_thm_coverage_algorithm_known_Delta_HulC_finite_sample_coverage_and_exact_coverage_under_the_stated_additional
    (n : ℕ) (hn : 0 < n)
    (alpha : ℝ) (halpha_pos : 0 < alpha) (halpha_lt_one : alpha < 1)
    (Delta : ℝ) (hDelta_nonneg : 0 ≤ Delta) (hDelta_lt_half : Delta < 1 / 2)
    (theta0 : ℝ)
    (Balpha : ℕ) (hBalpha_ge_one : 1 ≤ Balpha)
    (hBalpha_spec : Pmis Delta Balpha ≤ alpha)
    (hBalpha_min : ∀ B : ℕ, 1 ≤ B → Pmis Delta B ≤ alpha → Balpha ≤ B)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {𝒳 : Type*} [MeasurableSpace 𝒳]
    (X : Fin n → Ω → 𝒳) (hX_meas : ∀ i, Measurable (X i)) (hX_indep : iIndepFun X P)
    (thetaHat : ℕ → Ω → ℝ) (hthetaHat_meas : ∀ j, Measurable (thetaHat j))
    (hthetaHat_indep : iIndepFun (fun j : Fin Balpha => thetaHat ((j : ℕ) + 1)) P)
    (hmedBias_le : ∀ j : Fin Balpha, medBias P theta0 (thetaHat ((j : ℕ) + 1)) ≤ Delta)
    (U : Ω → ℝ) (hU_meas : Measurable U)
    (hU_uniform : Measure.map U P = (volume : Measure ℝ).restrict (Set.Icc 0 1))
    (hU_indep_data : Indep (MeasurableSpace.comap U (inferInstance : MeasurableSpace ℝ))
      (⨆ i, MeasurableSpace.comap (X i) (inferInstance : MeasurableSpace 𝒳)) P)
    (hU_indep_est : Indep (MeasurableSpace.comap U (inferInstance : MeasurableSpace ℝ))
      (⨆ j : Fin Balpha, MeasurableSpace.comap (thetaHat ((j : ℕ) + 1))
        (inferInstance : MeasurableSpace ℝ)) P)
    (S : ℕ → Ω → Set (Fin n))
    (hU_indep_partition : Indep (MeasurableSpace.comap U (inferInstance : MeasurableSpace ℝ))
      (⨆ j : ℕ, MeasurableSpace.comap (S j)
        (inferInstance : MeasurableSpace (Set (Fin n)))) P)
    (hthetaHat_link : ∀ j : ℕ, MeasurableSpace.comap (thetaHat j)
        (inferInstance : MeasurableSpace ℝ) ≤
      (⨆ i, MeasurableSpace.comap (X i) (inferInstance : MeasurableSpace 𝒳)) ⊔
        MeasurableSpace.comap (S j) (inferInstance : MeasurableSpace (Set (Fin n))))

    (hS_pairwiseDisjoint : ∀ ω, Set.PairwiseDisjoint
      (↑(Finset.Icc 1 (Bstar U alpha Delta Balpha ω)) : Set ℕ) (fun j => S j ω))
    (hS_cover : ∀ ω, (⋃ j ∈ Finset.Icc 1 (Bstar U alpha Delta Balpha ω), S j ω) = Set.univ)
    (hn_ge : Balpha ≤ n) :
    (P {ω | inCI theta0 thetaHat (Bstar U alpha Delta Balpha) ω}).toReal ≥ 1 - alpha ∧
      ((∀ j : Fin Balpha, (P {ω | thetaHat ((j : ℕ) + 1) ω ≤ theta0}).toReal
          = (P {ω | thetaHat 1 ω ≤ theta0}).toReal) →
        (∀ j : Fin Balpha, P {ω | thetaHat ((j : ℕ) + 1) ω = theta0} = 0) →
        (∀ j : Fin Balpha, medBias P theta0 (thetaHat ((j : ℕ) + 1)) = Delta) →
        (P {ω | inCI theta0 thetaHat (Bstar U alpha Delta Balpha) ω}).toReal = 1 - alpha)
:= by
  /- @proof-region region.root.4c6ccf7dce70 begin -/
  have hPmis1 : Pmis Delta 1 = 1 := by
    unfold Pmis
    ring
  have hBalpha_ne_one : Balpha ≠ 1 := by
    rintro rfl
    rw [hPmis1] at hBalpha_spec
    linarith
  have hBalpha_ge_two : 2 ≤ Balpha := by omega
  have hBm1_ge_one : 1 ≤ Balpha - 1 := by omega
  have hBm1_le : Balpha - 1 ≤ Balpha := by omega
  have hhalf_minus : (0 : ℝ) < 1 / 2 - Delta := by linarith
  have hhalf_plus : (0 : ℝ) < 1 / 2 + Delta := by linarith
  have hPmis_pos : ∀ k : ℕ, 0 < Pmis Delta k := by
    intro k
    unfold Pmis
    have h1 : (0 : ℝ) < (1 / 2 - Delta) ^ k := pow_pos hhalf_minus k
    have h2 : (0 : ℝ) < (1 / 2 + Delta) ^ k := pow_pos hhalf_plus k
    linarith
  have hdiff : ∀ k : ℕ, Pmis Delta k - Pmis Delta (k + 1)
      = (1 / 2 - Delta) ^ k * (1 / 2 + Delta) + (1 / 2 + Delta) ^ k * (1 / 2 - Delta) := by
    intro k
    unfold Pmis
    rw [pow_succ, pow_succ]
    ring
  have hPmis_strict : ∀ k : ℕ, Pmis Delta (k + 1) < Pmis Delta k := by
    intro k
    have hp1 : (0 : ℝ) < (1 / 2 - Delta) ^ k := pow_pos hhalf_minus k
    have hp2 : (0 : ℝ) < (1 / 2 + Delta) ^ k := pow_pos hhalf_plus k
    have hA : (0 : ℝ) < (1 / 2 - Delta) ^ k * (1 / 2 + Delta) := mul_pos hp1 hhalf_plus
    have hB : (0 : ℝ) < (1 / 2 + Delta) ^ k * (1 / 2 - Delta) := mul_pos hp2 hhalf_minus
    linarith [hdiff k]
  have hPmis_Bm1_gt : alpha < Pmis Delta (Balpha - 1) := by
    by_contra hle
    push_neg at hle
    have h := hBalpha_min (Balpha - 1) hBm1_ge_one hle
    omega
  have hden_pos : 0 < Pmis Delta (Balpha - 1) - Pmis Delta Balpha := by
    have hs := hPmis_strict (Balpha - 1)
    have hsucc : Balpha - 1 + 1 = Balpha := Nat.sub_add_cancel hBalpha_ge_one
    rw [hsucc] at hs
    linarith
  have hnum_nonneg : 0 ≤ alpha - Pmis Delta Balpha := by linarith [hBalpha_spec]
  have htau_nonneg : 0 ≤ tauF alpha Delta Balpha := by
    unfold tauF
    exact div_nonneg hnum_nonneg (le_of_lt hden_pos)
  have htau_le_one : tauF alpha Delta Balpha ≤ 1 := by
    unfold tauF
    rw [div_le_one hden_pos]
    linarith [hPmis_Bm1_gt]
  have htau_mix : tauF alpha Delta Balpha * Pmis Delta (Balpha - 1)
      + (1 - tauF alpha Delta Balpha) * Pmis Delta Balpha = alpha := by
    have hden_ne : Pmis Delta (Balpha - 1) - Pmis Delta Balpha ≠ 0 := ne_of_gt hden_pos
    unfold tauF
    field_simp
    ring
  have htau_zero_iff : tauF alpha Delta Balpha = 0 ↔ alpha = Pmis Delta Balpha := by
    unfold tauF
    rw [div_eq_zero_iff]
    constructor
    · rintro (h | h)
      · linarith
      · exact absurd h (ne_of_gt hden_pos)
    · intro h
      exact Or.inl (by linarith)
  have hApos : 0 ≤ tauF alpha Delta Balpha * Pmis Delta (Balpha - 1) :=
    mul_nonneg htau_nonneg (le_of_lt (hPmis_pos (Balpha - 1)))
  have hBpos : 0 ≤ (1 - tauF alpha Delta Balpha) * Pmis Delta Balpha :=
    mul_nonneg (sub_nonneg.mpr htau_le_one) (le_of_lt (hPmis_pos Balpha))
  have hmeasS1 : MeasurableSet {ω : Ω | U ω ≤ tauF alpha Delta Balpha} :=
    hU_meas measurableSet_Iic
  have hmeasS2 : MeasurableSet {ω : Ω | tauF alpha Delta Balpha < U ω} :=
    hU_meas measurableSet_Ioi
  have hN1 := statopia_math_node_1460261823_45140d86 P theta0 thetaHat hthetaHat_meas U hU_meas Balpha hBalpha_ge_one hU_indep_est (Balpha - 1) hBm1_ge_one hBm1_le (tauF alpha Delta Balpha)
  have hN2 := statopia_math_node_1460261823_45140d86 P theta0 thetaHat hthetaHat_meas U hU_meas Balpha hBalpha_ge_one hU_indep_est Balpha hBalpha_ge_one (le_refl Balpha) (tauF alpha Delta Balpha)
  have hb1 := statopia_math_node_1727152864_9ef8801e P theta0 Delta hDelta_nonneg hDelta_lt_half Balpha hBalpha_ge_one thetaHat hthetaHat_meas hthetaHat_indep hmedBias_le (Balpha - 1) hBm1_ge_one hBm1_le
  have hb2 := statopia_math_node_1727152864_9ef8801e P theta0 Delta hDelta_nonneg hDelta_lt_half Balpha hBalpha_ge_one thetaHat hthetaHat_meas hthetaHat_indep hmedBias_le Balpha hBalpha_ge_one (le_refl Balpha)
  have ht := statopia_math_node_3519240212_d3830931 P U hU_meas hU_uniform (tauF alpha Delta Balpha) htau_nonneg htau_le_one
  have hdisj : Disjoint ({ω : Ω | U ω ≤ tauF alpha Delta Balpha} ∩ {ω : Ω | ¬ inCI theta0 thetaHat (fun _ => Balpha - 1) ω})
      ({ω : Ω | tauF alpha Delta Balpha < U ω} ∩ {ω : Ω | ¬ inCI theta0 thetaHat (fun _ => Balpha) ω}) := by
    rw [Set.disjoint_left]
    rintro ω ⟨hx, _⟩ ⟨hy, _⟩
    simp only [Set.mem_setOf_eq] at hx hy
    linarith
  have hAC_eq_union : ∀ (hτ0 : tauF alpha Delta Balpha ≠ 0),
      {ω : Ω | ¬ inCI theta0 thetaHat (Bstar U alpha Delta Balpha) ω}
        = ({ω : Ω | U ω ≤ tauF alpha Delta Balpha} ∩ {ω : Ω | ¬ inCI theta0 thetaHat (fun _ => Balpha - 1) ω})
          ∪ ({ω : Ω | tauF alpha Delta Balpha < U ω} ∩ {ω : Ω | ¬ inCI theta0 thetaHat (fun _ => Balpha) ω}) := by
    intro hτ0
    ext ω
    by_cases hω : U ω ≤ tauF alpha Delta Balpha
    · have hbv : Bstar U alpha Delta Balpha ω = Balpha - 1 := by
        unfold Bstar
        rw [if_neg hτ0, if_pos hω]
      have hlt : ¬ (tauF alpha Delta Balpha < U ω) := not_lt.mpr hω
      have e : ¬ inCI theta0 thetaHat (Bstar U alpha Delta Balpha) ω ↔ ¬ inCI theta0 thetaHat (fun _ => Balpha - 1) ω := by
        unfold inCI
        rw [hbv]
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff]
      rw [e]
      simp only [hω, hlt, true_and, false_and, or_false]
    · have hbv : Bstar U alpha Delta Balpha ω = Balpha := by
        unfold Bstar
        rw [if_neg hτ0, if_neg hω]
      have hgt : tauF alpha Delta Balpha < U ω := lt_of_not_ge hω
      have e : ¬ inCI theta0 thetaHat (Bstar U alpha Delta Balpha) ω ↔ ¬ inCI theta0 thetaHat (fun _ => Balpha) ω := by
        unfold inCI
        rw [hbv]
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff]
      rw [e]
      simp only [hω, hgt, true_and, false_and, false_or]
  have hAC_meas : MeasurableSet {ω : Ω | ¬ inCI theta0 thetaHat (Bstar U alpha Delta Balpha) ω} := by
    by_cases hτ0 : tauF alpha Delta Balpha = 0
    · have hc : Bstar U alpha Delta Balpha = fun _ => Balpha := by
        funext ω
        unfold Bstar
        rw [if_pos hτ0]
      rw [show {ω : Ω | ¬ inCI theta0 thetaHat (Bstar U alpha Delta Balpha) ω}
          = {ω : Ω | ¬ inCI theta0 thetaHat (fun _ => Balpha) ω} from by rw [hc]]
      exact hN2.1
    · rw [hAC_eq_union hτ0]
      exact (hmeasS1.inter hN1.1).union (hmeasS2.inter hN2.1)
  have hNCle_one : P {ω : Ω | ¬ inCI theta0 thetaHat (Bstar U alpha Delta Balpha) ω} ≤ 1 := by
    calc P {ω : Ω | ¬ inCI theta0 thetaHat (Bstar U alpha Delta Balpha) ω} ≤ P Set.univ :=
          measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hPA : P {ω : Ω | inCI theta0 thetaHat (Bstar U alpha Delta Balpha) ω}
      = 1 - P {ω : Ω | ¬ inCI theta0 thetaHat (Bstar U alpha Delta Balpha) ω} := by
    have hcompl : {ω : Ω | inCI theta0 thetaHat (Bstar U alpha Delta Balpha) ω}
        = {ω : Ω | ¬ inCI theta0 thetaHat (Bstar U alpha Delta Balpha) ω}ᶜ := by
      ext ω
      simp
    rw [hcompl, measure_compl hAC_meas (ne_top_of_le_ne_top (by simp) hNCle_one), measure_univ]
  have hPAt : (P {ω : Ω | inCI theta0 thetaHat (Bstar U alpha Delta Balpha) ω}).toReal
      = 1 - (P {ω : Ω | ¬ inCI theta0 thetaHat (Bstar U alpha Delta Balpha) ω}).toReal := by
    rw [hPA, ENNReal.toReal_sub_of_le hNCle_one (by simp), ENNReal.toReal_one]
  have hACle : P {ω : Ω | ¬ inCI theta0 thetaHat (Bstar U alpha Delta Balpha) ω} ≤ ENNReal.ofReal alpha := by
    by_cases hτ0 : tauF alpha Delta Balpha = 0
    · have hc : Bstar U alpha Delta Balpha = fun _ => Balpha := by
        funext ω
        unfold Bstar
        rw [if_pos hτ0]
      have hα : alpha = Pmis Delta Balpha := htau_zero_iff.mp hτ0
      rw [show {ω : Ω | ¬ inCI theta0 thetaHat (Bstar U alpha Delta Balpha) ω}
          = {ω : Ω | ¬ inCI theta0 thetaHat (fun _ => Balpha) ω} from by rw [hc], hα]
      exact hb2
    · have hfac1 : P ({ω : Ω | U ω ≤ tauF alpha Delta Balpha} ∩ {ω : Ω | ¬ inCI theta0 thetaHat (fun _ => Balpha - 1) ω})
          = P {ω : Ω | U ω ≤ tauF alpha Delta Balpha} * P {ω : Ω | ¬ inCI theta0 thetaHat (fun _ => Balpha - 1) ω} := hN1.2.2.1
      have hfac2 : P ({ω : Ω | tauF alpha Delta Balpha < U ω} ∩ {ω : Ω | ¬ inCI theta0 thetaHat (fun _ => Balpha) ω})
          = P {ω : Ω | tauF alpha Delta Balpha < U ω} * P {ω : Ω | ¬ inCI theta0 thetaHat (fun _ => Balpha) ω} := hN2.2.2.2
      calc P {ω : Ω | ¬ inCI theta0 thetaHat (Bstar U alpha Delta Balpha) ω}
          = P (({ω : Ω | U ω ≤ tauF alpha Delta Balpha} ∩ {ω : Ω | ¬ inCI theta0 thetaHat (fun _ => Balpha - 1) ω})
              ∪ ({ω : Ω | tauF alpha Delta Balpha < U ω} ∩ {ω : Ω | ¬ inCI theta0 thetaHat (fun _ => Balpha) ω})) := by
              rw [hAC_eq_union hτ0]
        _ = P ({ω : Ω | U ω ≤ tauF alpha Delta Balpha} ∩ {ω : Ω | ¬ inCI theta0 thetaHat (fun _ => Balpha - 1) ω})
              + P ({ω : Ω | tauF alpha Delta Balpha < U ω} ∩ {ω : Ω | ¬ inCI theta0 thetaHat (fun _ => Balpha) ω}) :=
              measure_union hdisj (hmeasS2.inter hN2.1)
        _ = P {ω : Ω | U ω ≤ tauF alpha Delta Balpha} * P {ω : Ω | ¬ inCI theta0 thetaHat (fun _ => Balpha - 1) ω}
              + P {ω : Ω | tauF alpha Delta Balpha < U ω} * P {ω : Ω | ¬ inCI theta0 thetaHat (fun _ => Balpha) ω} := by
              rw [hfac1, hfac2]
        _ = ENNReal.ofReal (tauF alpha Delta Balpha) * P {ω : Ω | ¬ inCI theta0 thetaHat (fun _ => Balpha - 1) ω}
              + ENNReal.ofReal (1 - tauF alpha Delta Balpha) * P {ω : Ω | ¬ inCI theta0 thetaHat (fun _ => Balpha) ω} := by
              rw [ht.1, ht.2]
        _ ≤ ENNReal.ofReal (tauF alpha Delta Balpha) * ENNReal.ofReal (Pmis Delta (Balpha - 1))
              + ENNReal.ofReal (1 - tauF alpha Delta Balpha) * ENNReal.ofReal (Pmis Delta Balpha) :=
              add_le_add (mul_le_mul_left' hb1 _) (mul_le_mul_left' hb2 _)
        _ = ENNReal.ofReal (tauF alpha Delta Balpha * Pmis Delta (Balpha - 1))
              + ENNReal.ofReal ((1 - tauF alpha Delta Balpha) * Pmis Delta Balpha) := by
              rw [ENNReal.ofReal_mul htau_nonneg, ENNReal.ofReal_mul (sub_nonneg.mpr htau_le_one)]
        _ = ENNReal.ofReal (tauF alpha Delta Balpha * Pmis Delta (Balpha - 1)
              + (1 - tauF alpha Delta Balpha) * Pmis Delta Balpha) := by
              rw [ENNReal.ofReal_add hApos hBpos]
        _ = ENNReal.ofReal alpha := by rw [htau_mix]
  have hACeq : (∀ j : Fin Balpha, (P {ω : Ω | thetaHat ((j : ℕ) + 1) ω ≤ theta0}).toReal
        = (P {ω : Ω | thetaHat 1 ω ≤ theta0}).toReal) →
      (∀ j : Fin Balpha, P {ω : Ω | thetaHat ((j : ℕ) + 1) ω = theta0} = 0) →
      (∀ j : Fin Balpha, medBias P theta0 (thetaHat ((j : ℕ) + 1)) = Delta) →
      P {ω : Ω | ¬ inCI theta0 thetaHat (Bstar U alpha Delta Balpha) ω} = ENNReal.ofReal alpha := by
    intro h1 h2 h3
    by_cases hτ0 : tauF alpha Delta Balpha = 0
    · have hc : Bstar U alpha Delta Balpha = fun _ => Balpha := by
        funext ω
        unfold Bstar
        rw [if_pos hτ0]
      have hα : alpha = Pmis Delta Balpha := htau_zero_iff.mp hτ0
      have hEq2 := statopia_math_node_411957280_656443f1 theta0 Delta hDelta_nonneg hDelta_lt_half Balpha hBalpha_ge_one P thetaHat hthetaHat_meas hthetaHat_indep h1 h2 h3 Balpha hBalpha_ge_one (le_refl Balpha)
      rw [show {ω : Ω | ¬ inCI theta0 thetaHat (Bstar U alpha Delta Balpha) ω}
          = {ω : Ω | ¬ inCI theta0 thetaHat (fun _ => Balpha) ω} from by rw [hc], hα]
      exact hEq2
    · have hEq1 := statopia_math_node_411957280_656443f1 theta0 Delta hDelta_nonneg hDelta_lt_half Balpha hBalpha_ge_one P thetaHat hthetaHat_meas hthetaHat_indep h1 h2 h3 (Balpha - 1) hBm1_ge_one hBm1_le
      have hEq2 := statopia_math_node_411957280_656443f1 theta0 Delta hDelta_nonneg hDelta_lt_half Balpha hBalpha_ge_one P thetaHat hthetaHat_meas hthetaHat_indep h1 h2 h3 Balpha hBalpha_ge_one (le_refl Balpha)
      have hfac1 : P ({ω : Ω | U ω ≤ tauF alpha Delta Balpha} ∩ {ω : Ω | ¬ inCI theta0 thetaHat (fun _ => Balpha - 1) ω})
          = P {ω : Ω | U ω ≤ tauF alpha Delta Balpha} * P {ω : Ω | ¬ inCI theta0 thetaHat (fun _ => Balpha - 1) ω} := hN1.2.2.1
      have hfac2 : P ({ω : Ω | tauF alpha Delta Balpha < U ω} ∩ {ω : Ω | ¬ inCI theta0 thetaHat (fun _ => Balpha) ω})
          = P {ω : Ω | tauF alpha Delta Balpha < U ω} * P {ω : Ω | ¬ inCI theta0 thetaHat (fun _ => Balpha) ω} := hN2.2.2.2
      calc P {ω : Ω | ¬ inCI theta0 thetaHat (Bstar U alpha Delta Balpha) ω}
          = P (({ω : Ω | U ω ≤ tauF alpha Delta Balpha} ∩ {ω : Ω | ¬ inCI theta0 thetaHat (fun _ => Balpha - 1) ω})
              ∪ ({ω : Ω | tauF alpha Delta Balpha < U ω} ∩ {ω : Ω | ¬ inCI theta0 thetaHat (fun _ => Balpha) ω})) := by
              rw [hAC_eq_union hτ0]
        _ = P ({ω : Ω | U ω ≤ tauF alpha Delta Balpha} ∩ {ω : Ω | ¬ inCI theta0 thetaHat (fun _ => Balpha - 1) ω})
              + P ({ω : Ω | tauF alpha Delta Balpha < U ω} ∩ {ω : Ω | ¬ inCI theta0 thetaHat (fun _ => Balpha) ω}) :=
              measure_union hdisj (hmeasS2.inter hN2.1)
        _ = P {ω : Ω | U ω ≤ tauF alpha Delta Balpha} * P {ω : Ω | ¬ inCI theta0 thetaHat (fun _ => Balpha - 1) ω}
              + P {ω : Ω | tauF alpha Delta Balpha < U ω} * P {ω : Ω | ¬ inCI theta0 thetaHat (fun _ => Balpha) ω} := by
              rw [hfac1, hfac2]
        _ = ENNReal.ofReal (tauF alpha Delta Balpha) * P {ω : Ω | ¬ inCI theta0 thetaHat (fun _ => Balpha - 1) ω}
              + ENNReal.ofReal (1 - tauF alpha Delta Balpha) * P {ω : Ω | ¬ inCI theta0 thetaHat (fun _ => Balpha) ω} := by
              rw [ht.1, ht.2]
        _ = ENNReal.ofReal (tauF alpha Delta Balpha) * ENNReal.ofReal (Pmis Delta (Balpha - 1))
              + ENNReal.ofReal (1 - tauF alpha Delta Balpha) * ENNReal.ofReal (Pmis Delta Balpha) := by
              rw [hEq1, hEq2]
        _ = ENNReal.ofReal (tauF alpha Delta Balpha * Pmis Delta (Balpha - 1))
              + ENNReal.ofReal ((1 - tauF alpha Delta Balpha) * Pmis Delta Balpha) := by
              rw [ENNReal.ofReal_mul htau_nonneg, ENNReal.ofReal_mul (sub_nonneg.mpr htau_le_one)]
        _ = ENNReal.ofReal (tauF alpha Delta Balpha * Pmis Delta (Balpha - 1)
              + (1 - tauF alpha Delta Balpha) * Pmis Delta Balpha) := by
              rw [ENNReal.ofReal_add hApos hBpos]
        _ = ENNReal.ofReal alpha := by rw [htau_mix]
  constructor
  · rw [hPAt]
    have hle : (P {ω : Ω | ¬ inCI theta0 thetaHat (Bstar U alpha Delta Balpha) ω}).toReal ≤ alpha := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hACle
      rwa [ENNReal.toReal_ofReal (le_of_lt halpha_pos)] at h
    linarith
  · intro h1 h2 h3
    rw [hPAt]
    have heq : (P {ω : Ω | ¬ inCI theta0 thetaHat (Bstar U alpha Delta Balpha) ω}).toReal = alpha := by
      rw [hACeq h1 h2 h3, ENNReal.toReal_ofReal (le_of_lt halpha_pos)]
    rw [heq]
  /- @proof-region region.root.4c6ccf7dce70 end -/

end

end Statlib.Imported
