import ProverJobs.paper_fresh_20261030t143835550708z_hulc.Vocabulary
import ProverJobs.paper_fresh_20261030t143835550708z_hulc.Base

namespace PaperProofTasks.paper_fresh_20261030t143835550708z_hulc

open _root_.PaperProofTasks.paper_fresh_20261030t143835550708z_hulc.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Statlib.Imported
open _root_.Statlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_1460261823_45140d86 : ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (theta0 : ℝ) (thetaHat : ℕ → Ω → ℝ) (hthetaHat_meas : ∀ j, Measurable (thetaHat j))
    (U : Ω → ℝ) (hU_meas : Measurable U)
    (Balpha : ℕ) (hBalpha_ge_one : 1 ≤ Balpha)
    (hU_indep_est : Indep (MeasurableSpace.comap U (inferInstance : MeasurableSpace ℝ))
      (⨆ j : Fin Balpha, MeasurableSpace.comap (thetaHat ((j : ℕ) + 1))
        (inferInstance : MeasurableSpace ℝ)) P)
    (k : ℕ) (hk_ge_one : 1 ≤ k) (hk_le_Balpha : k ≤ Balpha) (tau : ℝ),
    MeasurableSet {ω | ¬ inCI theta0 thetaHat (fun _ => k) ω} ∧
      MeasurableSet[⨆ j : Fin Balpha, MeasurableSpace.comap (thetaHat ((j : ℕ) + 1))
          (inferInstance : MeasurableSpace ℝ)] {ω | ¬ inCI theta0 thetaHat (fun _ => k) ω} ∧
      P ({ω | U ω ≤ tau} ∩ {ω | ¬ inCI theta0 thetaHat (fun _ => k) ω})
        = P {ω | U ω ≤ tau} * P {ω | ¬ inCI theta0 thetaHat (fun _ => k) ω} ∧
      P ({ω | tau < U ω} ∩ {ω | ¬ inCI theta0 thetaHat (fun _ => k) ω})
        = P {ω | tau < U ω} * P {ω | ¬ inCI theta0 thetaHat (fun _ => k) ω} := by
  /- @proof-region region.target-node.session.c0ff19744dfbe658 begin -/
  intro Ω mΩ P hPinst theta0 thetaHat hthetaHat_meas U hU_meas Balpha hBalpha_ge_one hU_indep_est k hk_ge_one hk_le_Balpha tau
  set Mg : MeasurableSpace Ω := ⨆ j : Fin Balpha, MeasurableSpace.comap (thetaHat ((j : ℕ) + 1)) (inferInstance : MeasurableSpace ℝ) with hMg_def
  have hMg_le : Mg ≤ mΩ := by
    rw [hMg_def]
    exact iSup_le (fun j => measurable_iff_comap_le.mp (hthetaHat_meas ((j : ℕ) + 1)))
  have hindep : Indep (MeasurableSpace.comap U (inferInstance : MeasurableSpace ℝ)) Mg P := by
    rw [hMg_def]
    exact hU_indep_est
  have hsingle_ub : ∀ n : ℕ, 1 ≤ n → n ≤ Balpha → MeasurableSet[Mg] {ω | thetaHat n ω ≤ theta0} := by
    intro n hn1 hnB
    have hlt : n - 1 < Balpha := by omega
    let i : Fin Balpha := ⟨n - 1, hlt⟩
    have hcast : (i : ℕ) + 1 = n := by
      show n - 1 + 1 = n
      omega
    have hle : MeasurableSpace.comap (thetaHat ((i : ℕ) + 1)) (inferInstance : MeasurableSpace ℝ) ≤ Mg := by
      rw [hMg_def]
      exact le_iSup (fun j : Fin Balpha => MeasurableSpace.comap (thetaHat ((j : ℕ) + 1)) (inferInstance : MeasurableSpace ℝ)) i
    have hbase : MeasurableSet[MeasurableSpace.comap (thetaHat ((i : ℕ) + 1)) (inferInstance : MeasurableSpace ℝ)] {ω | thetaHat ((i : ℕ) + 1) ω ≤ theta0} := by
      rw [MeasurableSpace.measurableSet_comap]
      exact ⟨Set.Iic theta0, measurableSet_Iic, by ext x; simp⟩
    have hres := MeasurableSpace.le_def.mp hle _ hbase
    rw [hcast] at hres
    exact hres
  have hsingle_lb : ∀ n : ℕ, 1 ≤ n → n ≤ Balpha → MeasurableSet[Mg] {ω | theta0 ≤ thetaHat n ω} := by
    intro n hn1 hnB
    have hlt : n - 1 < Balpha := by omega
    let i : Fin Balpha := ⟨n - 1, hlt⟩
    have hcast : (i : ℕ) + 1 = n := by
      show n - 1 + 1 = n
      omega
    have hle : MeasurableSpace.comap (thetaHat ((i : ℕ) + 1)) (inferInstance : MeasurableSpace ℝ) ≤ Mg := by
      rw [hMg_def]
      exact le_iSup (fun j : Fin Balpha => MeasurableSpace.comap (thetaHat ((j : ℕ) + 1)) (inferInstance : MeasurableSpace ℝ)) i
    have hbase : MeasurableSet[MeasurableSpace.comap (thetaHat ((i : ℕ) + 1)) (inferInstance : MeasurableSpace ℝ)] {ω | theta0 ≤ thetaHat ((i : ℕ) + 1) ω} := by
      rw [MeasurableSpace.measurableSet_comap]
      exact ⟨Set.Ici theta0, measurableSet_Ici, by ext x; simp⟩
    have hres := MeasurableSpace.le_def.mp hle _ hbase
    rw [hcast] at hres
    exact hres
  have hA : MeasurableSet[Mg] {ω | ∃ j ∈ Finset.Icc 1 k, thetaHat j ω ≤ theta0} := by
    have heq : {ω | ∃ j ∈ Finset.Icc 1 k, thetaHat j ω ≤ theta0}
        = ⋃ j : ℕ, if j ∈ Finset.Icc 1 k then {ω | thetaHat j ω ≤ theta0} else ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨j, hj, hle⟩
        exact ⟨j, by rw [if_pos hj]; exact hle⟩
      · rintro ⟨j, hj⟩
        by_cases h : j ∈ Finset.Icc 1 k
        · rw [if_pos h] at hj
          exact ⟨j, h, hj⟩
        · rw [if_neg h] at hj
          exact absurd hj (by simp)
    rw [heq]
    apply MeasurableSet.iUnion
    intro j
    by_cases hj : j ∈ Finset.Icc 1 k
    · rw [if_pos hj]
      exact hsingle_ub j (Finset.mem_Icc.mp hj).1 (le_trans (Finset.mem_Icc.mp hj).2 hk_le_Balpha)
    · rw [if_neg hj]
      exact MeasurableSet.empty
  have hB : MeasurableSet[Mg] {ω | ∃ j ∈ Finset.Icc 1 k, theta0 ≤ thetaHat j ω} := by
    have heq : {ω | ∃ j ∈ Finset.Icc 1 k, theta0 ≤ thetaHat j ω}
        = ⋃ j : ℕ, if j ∈ Finset.Icc 1 k then {ω | theta0 ≤ thetaHat j ω} else ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨j, hj, hle⟩
        exact ⟨j, by rw [if_pos hj]; exact hle⟩
      · rintro ⟨j, hj⟩
        by_cases h : j ∈ Finset.Icc 1 k
        · rw [if_pos h] at hj
          exact ⟨j, h, hj⟩
        · rw [if_neg h] at hj
          exact absurd hj (by simp)
    rw [heq]
    apply MeasurableSet.iUnion
    intro j
    by_cases hj : j ∈ Finset.Icc 1 k
    · rw [if_pos hj]
      exact hsingle_lb j (Finset.mem_Icc.mp hj).1 (le_trans (Finset.mem_Icc.mp hj).2 hk_le_Balpha)
    · rw [if_neg hj]
      exact MeasurableSet.empty
  have hNC : MeasurableSet[Mg] {ω | ¬ inCI theta0 thetaHat (fun _ => k) ω} := by
    have heq : {ω | ¬ inCI theta0 thetaHat (fun _ => k) ω}
        = ({ω | ∃ j ∈ Finset.Icc 1 k, thetaHat j ω ≤ theta0} ∩
           {ω | ∃ j ∈ Finset.Icc 1 k, theta0 ≤ thetaHat j ω})ᶜ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_inter_iff]
      exact Iff.rfl
    rw [heq]
    exact (hA.inter hB).compl
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact MeasurableSpace.le_def.mp hMg_le _ hNC
  · exact hNC
  · have hs : MeasurableSet[MeasurableSpace.comap U (inferInstance : MeasurableSpace ℝ)] {ω | U ω ≤ tau} := by
      rw [MeasurableSpace.measurableSet_comap]
      exact ⟨Set.Iic tau, measurableSet_Iic, by ext x; simp⟩
    have h1 := hindep {ω | U ω ≤ tau} {ω | ¬ inCI theta0 thetaHat (fun _ => k) ω} hs hNC
    simpa [Kernel.const_apply] using h1
  · have hs : MeasurableSet[MeasurableSpace.comap U (inferInstance : MeasurableSpace ℝ)] {ω | tau < U ω} := by
      rw [MeasurableSpace.measurableSet_comap]
      exact ⟨Set.Ioi tau, measurableSet_Ioi, by ext x; simp⟩
    have h2 := hindep {ω | tau < U ω} {ω | ¬ inCI theta0 thetaHat (fun _ => k) ω} hs hNC
    simpa [Kernel.const_apply] using h2
  /- @proof-region region.target-node.session.c0ff19744dfbe658 end -/

end

end Statlib.Imported

