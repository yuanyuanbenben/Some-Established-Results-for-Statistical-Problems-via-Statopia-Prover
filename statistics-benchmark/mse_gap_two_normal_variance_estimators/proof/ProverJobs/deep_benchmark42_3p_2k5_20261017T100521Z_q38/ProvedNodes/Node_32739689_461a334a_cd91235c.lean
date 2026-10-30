import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q38.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q38.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q38.ProvedNodes.Node_1250375089_9039a57c_25f5a737
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q38.ProvedNodes.Node_3292011310_9d98c3aa_7c2e0b1c
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q38.ProvedNodes.Node_449186465_eb0993fd_5afc276b


open MeasureTheory ProbabilityTheory
open scoped BigOperators

open MeasureTheory ProbabilityTheory
open scoped BigOperators

set_option autoImplicit false in
theorem statopia_math_node_32739689_461a334a : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (v : ℝ) (hv : 0 ≤ v)
    (Z : Fin n → Ω → ℝ)
    (hZ_meas : ∀ i, Measurable (Z i))
    (hZ_indep : iIndepFun Z P)
    (hZ_law : ∀ i, P.map (Z i) = gaussianReal 0 ⟨v, hv⟩)
    (A : Fin n → Fin n → ℝ)
    (hA_symm : ∀ i j, A i j = A j i),
    let Q : Ω → ℝ := fun ω => ∑ i : Fin n, ∑ j : Fin n, A i j * Z i ω * Z j ω
    Integrable (fun ω => Q ω ^ 2) P ∧
    Integrable Q P ∧
    (∫ ω, Q ω ∂P) = v * ∑ i : Fin n, A i i ∧
    (∫ ω, Q ω ^ 2 ∂P)
      = v ^ 2 * ((∑ i : Fin n, A i i) ^ 2 + 2 * ∑ i : Fin n, ∑ j : Fin n, A i j ^ 2) := by
  /- @proof-region region.target-node.session.80eaab8fe1002fab begin -/
  intro Ω _ P _ n v hv Z hZ_meas hZ_indep hZ_law A hA_symm Q
  have hMom : ∀ i : Fin n, Integrable (Z i) P ∧ Integrable (fun ω => Z i ω ^ 2) P ∧
      Integrable (fun ω => Z i ω ^ 3) P ∧ Integrable (fun ω => Z i ω ^ 4) P ∧
      (∫ ω, Z i ω ∂P) = 0 ∧ (∫ ω, Z i ω ^ 2 ∂P) = v ∧
      (∫ ω, Z i ω ^ 3 ∂P) = 0 ∧ (∫ ω, Z i ω ^ 4 ∂P) = 3 * v ^ 2 :=
    fun i => statopia_math_node_1250375089_9039a57c P v hv (Z i) (hZ_meas i) (hZ_law i)
  have h4 : ∀ p q r s : Fin n, Integrable (fun ω => Z p ω * Z q ω * Z r ω * Z s ω) P ∧
      (∫ ω, Z p ω * Z q ω * Z r ω * Z s ω ∂P)
        = v ^ 2 * ((if p = q then (1 : ℝ) else 0) * (if r = s then (1 : ℝ) else 0)
            + (if p = r then (1 : ℝ) else 0) * (if q = s then (1 : ℝ) else 0)
            + (if p = s then (1 : ℝ) else 0) * (if q = r then (1 : ℝ) else 0)) :=
    fun p q r s => statopia_math_node_449186465_eb0993fd P n v hv Z hZ_meas hZ_indep hZ_law p q r s
  have hZZ_int : ∀ i j : Fin n, Integrable (fun ω => Z i ω * Z j ω) P := by
    intro i j
    by_cases h : i = j
    · subst h
      have hsq : (fun ω => Z i ω * Z i ω) = fun ω => Z i ω ^ 2 := by funext ω; ring
      rw [hsq]
      exact (hMom i).2.1
    · exact (hZ_indep.indepFun h).integrable_mul (hMom i).1 (hMom j).1
  have hZZ_val : ∀ i j : Fin n, (∫ ω, Z i ω * Z j ω ∂P) = if i = j then v else 0 := by
    intro i j
    by_cases h : i = j
    · subst h
      rw [if_pos rfl]
      have hsq : (fun ω => Z i ω * Z i ω) = fun ω => Z i ω ^ 2 := by funext ω; ring
      rw [hsq]
      exact (hMom i).2.2.2.2.2.1
    · rw [if_neg h,
        (hZ_indep.indepFun h).integral_fun_mul_eq_mul_integral (hZ_meas i).aestronglyMeasurable (hZ_meas j).aestronglyMeasurable,
        (hMom i).2.2.2.2.1, (hMom j).2.2.2.2.1]
      ring
  have hQ_int : Integrable Q P := by
    show Integrable (fun ω => ∑ i : Fin n, ∑ j : Fin n, A i j * Z i ω * Z j ω) P
    apply integrable_finset_sum
    intro i _
    apply integrable_finset_sum
    intro j _
    have h1 : Integrable (fun ω => A i j * (Z i ω * Z j ω)) P := (hZZ_int i j).const_mul (A i j)
    have h2 : (fun ω => A i j * (Z i ω * Z j ω)) = fun ω => A i j * Z i ω * Z j ω := by
      funext ω; ring
    rwa [h2] at h1
  have hQ2_eq : (fun ω => Q ω ^ 2) = fun ω => ∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n, ∑ s : Fin n,
      A p q * A r s * (Z p ω * Z q ω * Z r ω * Z s ω) := by
    funext ω
    rw [pow_two]
    simp only [Q, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _
    apply Finset.sum_congr rfl; intro r _
    apply Finset.sum_congr rfl; intro s _
    ring
  refine ⟨?_, hQ_int, ?_, ?_⟩
  · rw [hQ2_eq]
    apply integrable_finset_sum
    intro p _
    apply integrable_finset_sum
    intro q _
    apply integrable_finset_sum
    intro r _
    apply integrable_finset_sum
    intro s _
    exact ((h4 p q r s).1).const_mul (A p q * A r s)
  · have hQ_eq : Q = fun ω => ∑ i : Fin n, ∑ j : Fin n, A i j * (Z i ω * Z j ω) := by
      funext ω
      simp only [Q]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      ring
    have hinner_int : ∀ i : Fin n, Integrable (fun ω => ∑ j : Fin n, A i j * (Z i ω * Z j ω)) P := by
      intro i
      apply integrable_finset_sum
      intro j _
      exact (hZZ_int i j).const_mul (A i j)
    rw [hQ_eq]
    have step1 : (∫ ω, (∑ i : Fin n, ∑ j : Fin n, A i j * (Z i ω * Z j ω)) ∂P)
        = ∑ i : Fin n, ∑ j : Fin n, A i j * (∫ ω, Z i ω * Z j ω ∂P) := by
      rw [integral_finset_sum Finset.univ (fun i _ => hinner_int i)]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finset_sum Finset.univ (fun j _ => (hZZ_int i j).const_mul (A i j))]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul]
    rw [step1]
    have hinner : ∀ i : Fin n, (∑ j : Fin n, A i j * (∫ ω, Z i ω * Z j ω ∂P)) = A i i * v := by
      intro i
      have hterm : ∀ j : Fin n, A i j * (∫ ω, Z i ω * Z j ω ∂P) = if i = j then A i i * v else 0 := by
        intro j
        rw [hZZ_val i j]
        by_cases h : i = j
        · subst h; simp
        · simp [h]
      calc (∑ j : Fin n, A i j * (∫ ω, Z i ω * Z j ω ∂P))
          = ∑ j : Fin n, (if i = j then A i i * v else 0) := Finset.sum_congr rfl (fun j _ => hterm j)
        _ = A i i * v := by
            rw [Finset.sum_eq_single i (fun b _ hb => by rw [if_neg (Ne.symm hb)]) (fun h => absurd (Finset.mem_univ i) h)]
            simp
    simp only [hinner]
    rw [← Finset.sum_mul]
    ring
  · rw [hQ2_eq]
    have hInt4 : ∀ p q r s : Fin n, Integrable (fun ω => A p q * A r s * (Z p ω * Z q ω * Z r ω * Z s ω)) P :=
      fun p q r s => ((h4 p q r s).1).const_mul (A p q * A r s)
    have hInt3 : ∀ p q r : Fin n, Integrable (fun ω => ∑ s : Fin n, A p q * A r s * (Z p ω * Z q ω * Z r ω * Z s ω)) P := by
      intro p q r
      apply integrable_finset_sum
      intro s _
      exact hInt4 p q r s
    have hInt2 : ∀ p q : Fin n, Integrable (fun ω => ∑ r : Fin n, ∑ s : Fin n, A p q * A r s * (Z p ω * Z q ω * Z r ω * Z s ω)) P := by
      intro p q
      apply integrable_finset_sum
      intro r _
      exact hInt3 p q r
    have hInt1 : ∀ p : Fin n, Integrable (fun ω => ∑ q : Fin n, ∑ r : Fin n, ∑ s : Fin n, A p q * A r s * (Z p ω * Z q ω * Z r ω * Z s ω)) P := by
      intro p
      apply integrable_finset_sum
      intro q _
      exact hInt2 p q
    have step_int : (∫ ω, (∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n, ∑ s : Fin n,
          A p q * A r s * (Z p ω * Z q ω * Z r ω * Z s ω)) ∂P)
        = ∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n, ∑ s : Fin n,
            A p q * A r s * (∫ ω, Z p ω * Z q ω * Z r ω * Z s ω ∂P) := by
      rw [integral_finset_sum Finset.univ (fun p _ => hInt1 p)]
      apply Finset.sum_congr rfl; intro p _
      rw [integral_finset_sum Finset.univ (fun q _ => hInt2 p q)]
      apply Finset.sum_congr rfl; intro q _
      rw [integral_finset_sum Finset.univ (fun r _ => hInt3 p q r)]
      apply Finset.sum_congr rfl; intro r _
      rw [integral_finset_sum Finset.univ (fun s _ => hInt4 p q r s)]
      apply Finset.sum_congr rfl; intro s _
      rw [integral_const_mul]
    have step_val : (∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n, ∑ s : Fin n,
          A p q * A r s * (∫ ω, Z p ω * Z q ω * Z r ω * Z s ω ∂P))
        = ∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n, ∑ s : Fin n,
            A p q * A r s * (v ^ 2 * ((if p = q then (1 : ℝ) else 0) * (if r = s then (1 : ℝ) else 0)
              + (if p = r then (1 : ℝ) else 0) * (if q = s then (1 : ℝ) else 0)
              + (if p = s then (1 : ℝ) else 0) * (if q = r then (1 : ℝ) else 0))) := by
      apply Finset.sum_congr rfl; intro p _
      apply Finset.sum_congr rfl; intro q _
      apply Finset.sum_congr rfl; intro r _
      apply Finset.sum_congr rfl; intro s _
      rw [(h4 p q r s).2]
    rw [step_int, step_val]
    exact statopia_math_node_3292011310_9d98c3aa n v A hA_symm
  /- @proof-region region.target-node.session.80eaab8fe1002fab end -/
