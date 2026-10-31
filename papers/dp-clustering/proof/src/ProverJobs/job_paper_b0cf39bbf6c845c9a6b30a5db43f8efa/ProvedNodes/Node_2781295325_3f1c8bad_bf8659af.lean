import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.Vocabulary
import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.Base
import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.ProvedNodes.Node_2358127001_21193b79_db3ba381

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal MeasureTheory Topology BigOperators
open Statlib.Imported
open Statlib.Imported.DPMModel

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal MeasureTheory Topology BigOperators
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_2781295325_3f1c8bad : ∀ {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    (P : Measure X) [IsProbabilityMeasure P]
    (r : ℕ) (hr : 1 ≤ r)
    (ψ : Fin r → X → ℝ) (hψ_cont : ∀ j : Fin r, Continuous (ψ j))
    (M : ℝ) (hM : 0 < M)
    (hM_def : M = ⨆ j : Fin r, ⨆ x : X, |ψ j x|)
    (hψ_bound : ∀ (j : Fin r) (x : X), |ψ j x| ≤ M)
    (ε : ℝ) (hε : 0 < ε),
    (∀ (n : ℕ) (hn : 0 < n),
      Measure.pi (fun _ : Fin n => P)
        {x : Fin n → X |
          ε / 2 ≤ ⨆ j : Fin r,
            |(n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x' : X, ψ j x' ∂P|}
        ≤ ENNReal.ofReal (2 * (r : ℝ) * Real.exp (-(n : ℝ) * (ε ^ 2 / (8 * M ^ 2)))))
    ∧
    (∀ (n : ℕ) (hn : 0 < n) (ν : Fin n → Measure X)
        (hν : ∀ i : Fin n, IsProbabilityMeasure (ν i)),
      (∃ j : Fin r,
        ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, ∫ x' : X, ψ j x' ∂(ν i))
              - ∫ x' : X, ψ j x' ∂P|) →
      Measure.pi ν
        {x : Fin n → X |
          ⨆ j : Fin r,
            |(n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x' : X, ψ j x' ∂P| < ε / 2}
        ≤ ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * (ε ^ 2 / (8 * M ^ 2))))) := by
  /- @proof-region region.target-node.session.976874c3f5b5e3ff begin -/
  intro X _ _ _ P _ r hr ψ hψ M hM hM_def hψ_bound ε hε
  have hexp : ∀ n : ℕ, -(n : ℝ) * (ε / 2) ^ 2 / (2 * M ^ 2) = -(n : ℝ) * (ε ^ 2 / (8 * M ^ 2)) := by
    intro n
    have hkey : (ε / 2) ^ 2 / (2 * M ^ 2) = ε ^ 2 / (8 * M ^ 2) := by
      have h1 : (2 * M ^ 2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
      have h2 : (8 * M ^ 2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
      rw [div_eq_div_iff h1 h2]
      ring
    calc -(n : ℝ) * (ε / 2) ^ 2 / (2 * M ^ 2)
        = -(n : ℝ) * ((ε / 2) ^ 2 / (2 * M ^ 2)) := by rw [mul_div_assoc]
      _ = -(n : ℝ) * (ε ^ 2 / (8 * M ^ 2)) := by rw [hkey]
  have hmean : ∀ (n : ℕ) (_ : 0 < n) (j : Fin r),
      (n : ℝ)⁻¹ * (∑ i : Fin n, (∫ x, ψ j x ∂P)) = ∫ y, ψ j y ∂P := by
    intro n hn j
    have hn0 : (n : ℝ) ≠ 0 := by
      have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      exact ne_of_gt hpos
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hn0, one_mul]
  have ht : (0 : ℝ) < ε / 2 := by linarith
  constructor
  · intro n hn
    haveI : ∀ i : Fin n, IsProbabilityMeasure ((fun _ : Fin n => P) i) := fun i => inferInstance
    have hkey : ∀ j : Fin r, Measure.pi (fun _ : Fin n => P) {x : Fin n → X | ε / 2 ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x' : X, ψ j x' ∂P|} ≤ ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * (ε ^ 2 / (8 * M ^ 2)))) := by
      intro j
      have h := statopia_math_node_2358127001_21193b79 n hn M hM (fun _ : Fin n => X) (fun _ => P) (fun _ => ψ j) (fun i => (hψ j).measurable) (fun i ω => hψ_bound j ω) (ε / 2) ht
      rw [hmean n hn j, hexp n] at h
      exact h
    have hsub : {x : Fin n → X | ε / 2 ≤ ⨆ j : Fin r, |(n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x' : X, ψ j x' ∂P|} ⊆ ⋃ j : Fin r, {x : Fin n → X | ε / 2 ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x' : X, ψ j x' ∂P|} := by
      intro x hx
      simp only [Set.mem_setOf_eq] at hx
      haveI : Nonempty (Fin r) := ⟨⟨0, lt_of_lt_of_le Nat.zero_lt_one hr⟩⟩
      have hne : (Finset.univ : Finset (Fin r)).Nonempty := ⟨⟨0, lt_of_lt_of_le Nat.zero_lt_one hr⟩, Finset.mem_univ _⟩
      rw [← Finset.sup'_univ_eq_ciSup (fun j : Fin r => |(n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x' : X, ψ j x' ∂P|)] at hx
      obtain ⟨j, -, hj⟩ := (Finset.le_sup'_iff hne).mp hx
      simp only [Set.mem_iUnion]
      exact ⟨j, hj⟩
    have hunion : Measure.pi (fun _ : Fin n => P) (⋃ j : Fin r, {x : Fin n → X | ε / 2 ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x' : X, ψ j x' ∂P|}) ≤ ∑ j : Fin r, Measure.pi (fun _ : Fin n => P) {x : Fin n → X | ε / 2 ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x' : X, ψ j x' ∂P|} := by
      have hle := measure_biUnion_finset_le (μ := Measure.pi (fun _ : Fin n => P)) (Finset.univ : Finset (Fin r)) (fun j => {x : Fin n → X | ε / 2 ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x' : X, ψ j x' ∂P|})
      simpa using hle
    have hsum : (∑ j : Fin r, ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * (ε ^ 2 / (8 * M ^ 2))))) = ENNReal.ofReal (2 * (r : ℝ) * Real.exp (-(n : ℝ) * (ε ^ 2 / (8 * M ^ 2)))) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    calc Measure.pi (fun _ : Fin n => P) {x : Fin n → X | ε / 2 ≤ ⨆ j : Fin r, |(n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x' : X, ψ j x' ∂P|}
        ≤ Measure.pi (fun _ : Fin n => P) (⋃ j : Fin r, {x : Fin n → X | ε / 2 ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x' : X, ψ j x' ∂P|}) := measure_mono hsub
      _ ≤ ∑ j : Fin r, Measure.pi (fun _ : Fin n => P) {x : Fin n → X | ε / 2 ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x' : X, ψ j x' ∂P|} := hunion
      _ ≤ ∑ j : Fin r, ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * (ε ^ 2 / (8 * M ^ 2)))) := Finset.sum_le_sum (fun j _ => hkey j)
      _ = ENNReal.ofReal (2 * (r : ℝ) * Real.exp (-(n : ℝ) * (ε ^ 2 / (8 * M ^ 2)))) := hsum
  · intro n hn ν hν h
    haveI : ∀ i : Fin n, IsProbabilityMeasure (ν i) := hν
    rcases h with ⟨j, hj⟩
    have hhoef := statopia_math_node_2358127001_21193b79 n hn M hM (fun _ : Fin n => X)
      ν (fun _ => ψ j) (fun i => (hψ j).measurable) (fun i ω => hψ_bound j ω) (ε / 2) ht
    rw [hexp n] at hhoef
    refine le_trans (measure_mono ?_) hhoef
    intro x hx
    have hsup_lt : ⨆ j : Fin r, |(n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x' : X, ψ j x' ∂P| < ε / 2 := by
      simpa only [Set.mem_setOf_eq] using hx
    have hbdd : BddAbove (Set.range (fun j : Fin r => |(n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x' : X, ψ j x' ∂P|)) :=
      Finite.bddAbove_range _
    have hgj : |(n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x' : X, ψ j x' ∂P| < ε / 2 :=
      lt_of_le_of_lt (le_ciSup (f := fun j : Fin r => |(n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x' : X, ψ j x' ∂P|) hbdd j) hsup_lt
    have htri : |(n : ℝ)⁻¹ * (∑ i : Fin n, (∫ x', ψ j x' ∂(ν i))) - ∫ x', ψ j x' ∂P|
        ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, (∫ x', ψ j x' ∂(ν i))) - (n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i))|
          + |(n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x', ψ j x' ∂P| := by
      have h := abs_add_le
        ((n : ℝ)⁻¹ * (∑ i : Fin n, (∫ x', ψ j x' ∂(ν i))) - (n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)))
        ((n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x', ψ j x' ∂P)
      rwa [show
        ((n : ℝ)⁻¹ * (∑ i : Fin n, (∫ x', ψ j x' ∂(ν i))) - (n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)))
          + ((n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i)) - ∫ x', ψ j x' ∂P)
          = (n : ℝ)⁻¹ * (∑ i : Fin n, (∫ x', ψ j x' ∂(ν i))) - ∫ x', ψ j x' ∂P by ring] at h
    have hge : |(n : ℝ)⁻¹ * (∑ i : Fin n, (∫ x', ψ j x' ∂(ν i))) - (n : ℝ)⁻¹ * (∑ i : Fin n, ψ j (x i))| ≥ ε / 2 := by
      linarith [htri, hj, hgj]
    simp only [Set.mem_setOf_eq]
    rw [abs_sub_comm]
    exact hge
  /- @proof-region region.target-node.session.976874c3f5b5e3ff end -/

end Statlib.Imported
