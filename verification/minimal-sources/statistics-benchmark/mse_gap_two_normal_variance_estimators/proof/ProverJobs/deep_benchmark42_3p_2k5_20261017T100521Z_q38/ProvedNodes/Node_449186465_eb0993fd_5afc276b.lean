import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q38.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q38.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q38.ProvedNodes.Node_1250375089_9039a57c_25f5a737

open MeasureTheory ProbabilityTheory
open scoped BigOperators

open MeasureTheory ProbabilityTheory
open scoped BigOperators

set_option autoImplicit false in
theorem statopia_math_node_449186465_eb0993fd : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (v : ℝ) (hv : 0 ≤ v)
    (Z : Fin n → Ω → ℝ)
    (hZ_meas : ∀ i, Measurable (Z i))
    (hZ_indep : iIndepFun Z P)
    (hZ_law : ∀ i, P.map (Z i) = gaussianReal 0 ⟨v, hv⟩)
    (p q r s : Fin n),
    Integrable (fun ω => Z p ω * Z q ω * Z r ω * Z s ω) P ∧
      (∫ ω, Z p ω * Z q ω * Z r ω * Z s ω ∂P)
        = v ^ 2 * ((if p = q then (1 : ℝ) else 0) * (if r = s then (1 : ℝ) else 0)
            + (if p = r then (1 : ℝ) else 0) * (if q = s then (1 : ℝ) else 0)
            + (if p = s then (1 : ℝ) else 0) * (if q = r then (1 : ℝ) else 0)) := by
  /- @proof-region region.target-node.session.c94127eb02c57017 begin -/
  intro Ω _ P _ n v hv Z hZ_meas hZ_indep hZ_law p q r s
  have hdep : ∀ i : Fin n, Integrable (Z i) P ∧ Integrable (fun ω => Z i ω ^ 2) P ∧
      Integrable (fun ω => Z i ω ^ 3) P ∧ Integrable (fun ω => Z i ω ^ 4) P ∧
      (∫ ω, Z i ω ∂P) = 0 ∧ (∫ ω, Z i ω ^ 2 ∂P) = v ∧
      (∫ ω, Z i ω ^ 3 ∂P) = 0 ∧ (∫ ω, Z i ω ^ 4 ∂P) = 3 * v ^ 2 :=
    fun i => statopia_math_node_1250375089_9039a57c P v hv (Z i) (hZ_meas i) (hZ_law i)
  have hmean : ∀ i : Fin n, (∫ ω, Z i ω ∂P) = 0 := fun i => (hdep i).2.2.2.2.1
  have hm : ∀ i : Fin n, AEStronglyMeasurable (Z i) P :=
    fun i => (hZ_meas i).aestronglyMeasurable
  have hmul : ∀ i j : Fin n, AEStronglyMeasurable (fun ω => Z i ω * Z j ω) P :=
    fun i j => ((hZ_meas i).mul (hZ_meas j)).aestronglyMeasurable
  have hpow_meas : ∀ a : ℕ, Measurable (fun x : ℝ => x ^ a) := by
    intro a
    induction a with
    | zero => simpa using (measurable_const : Measurable fun _ : ℝ => (1 : ℝ))
    | succ k ih => simpa [pow_succ] using ih.mul measurable_id
  have hpowAESM : ∀ (i : Fin n) (a : ℕ), AEStronglyMeasurable (fun ω => Z i ω ^ a) P :=
    fun i a => ((hpow_meas a).comp (hZ_meas i)).aestronglyMeasurable
  have hsq : ∀ i : Fin n, (∫ ω, Z i ω * Z i ω ∂P) = v := by
    intro i
    simpa [pow_two] using (hdep i).2.2.2.2.2.1
  have hpair0 : ∀ i j : Fin n, i ≠ j → (∫ ω, Z i ω * Z j ω ∂P) = 0 := by
    intro i j hij
    have h := IndepFun.integral_fun_mul_eq_mul_integral (hZ_indep.indepFun hij) (hm i) (hm j)
    rw [h, hmean i, hmean j, mul_zero]
  have hC : ∀ i j : Fin n, (∫ ω, Z i ω * Z j ω ∂P) = v * (if i = j then (1 : ℝ) else 0) := by
    intro i j
    by_cases h : i = j
    · subst h
      rw [if_pos rfl, mul_one]
      exact hsq i
    · rw [if_neg h, mul_zero]
      exact hpair0 i j h
  have hI2 : ∀ i j : Fin n, Integrable (fun ω => Z i ω * Z j ω) P := by
    intro i j
    by_cases h : i = j
    · subst h
      simpa [pow_two] using (hdep i).2.1
    · have h' := IndepFun.integrable_mul (hZ_indep.indepFun h) (hdep i).1 (hdep j).1
      simpa using h'
  have hIndPow : ∀ (i j : Fin n) (a b : ℕ), i ≠ j →
      (fun ω => Z i ω ^ a) ⟂ᵢ[P] (fun ω => Z j ω ^ b) := by
    intro i j a b hij
    have hgm : ∀ k : Fin n, Measurable (fun x : ℝ =>
        if k = i then x ^ a else if k = j then x ^ b else x) := by
      intro k
      by_cases hki : k = i
      · subst hki
        simpa using hpow_meas a
      · by_cases hkj : k = j
        · subst hkj
          simpa [hki] using hpow_meas b
        · simpa [hki, hkj] using measurable_id
    have hcomp := hZ_indep.comp
      (fun (k : Fin n) (x : ℝ) => if k = i then x ^ a else if k = j then x ^ b else x) hgm
    have hind := hcomp.indepFun hij
    simpa [hij, hij.symm] using hind
  have hF2 : ∀ i j k l : Fin n, i ≠ k → i ≠ l → j ≠ k → j ≠ l →
      Integrable (fun ω => Z i ω * Z j ω * Z k ω * Z l ω) P ∧
      (∫ ω, Z i ω * Z j ω * Z k ω * Z l ω ∂P) =
        v * (if i = j then (1 : ℝ) else 0) * (v * (if k = l then (1 : ℝ) else 0)) := by
    intro i j k l h1 h2 h3 h4
    have hind := hZ_indep.indepFun_mul_mul hZ_meas i j k l h1 h2 h3 h4
    have hreg : (fun ω => Z i ω * Z j ω * Z k ω * Z l ω)
        = (fun ω => Z i ω * Z j ω * (Z k ω * Z l ω)) := by
      funext ω; ring
    constructor
    · rw [hreg]
      exact IndepFun.integrable_mul hind (hI2 i j) (hI2 k l)
    · rw [hreg]
      have hfac : (∫ ω, Z i ω * Z j ω * (Z k ω * Z l ω) ∂P)
          = (∫ ω, Z i ω * Z j ω ∂P) * (∫ ω, Z k ω * Z l ω ∂P) :=
        IndepFun.integral_fun_mul_eq_mul_integral hind (hmul i j) (hmul k l)
      rw [hfac, hC i j, hC k l]
  have hF31 : ∀ i k : Fin n, i ≠ k →
      Integrable (fun ω => Z i ω * Z i ω * Z i ω * Z k ω) P ∧
      (∫ ω, Z i ω * Z i ω * Z i ω * Z k ω ∂P) = 0 := by
    intro i k hik
    have hind := hIndPow i k 3 1 hik
    have hreg : (fun ω => Z i ω * Z i ω * Z i ω * Z k ω)
        = (fun ω => Z i ω ^ 3 * Z k ω ^ 1) := by
      funext ω; ring
    have hint3 : Integrable (fun ω => Z i ω ^ 3) P := (hdep i).2.2.1
    have hint1 : Integrable (fun ω => Z k ω ^ 1) P := by
      simpa using (hdep k).1
    have hzero3 : (∫ ω, Z i ω ^ 3 ∂P) = 0 := (hdep i).2.2.2.2.2.2.1
    have hzero1 : (∫ ω, Z k ω ^ 1 ∂P) = 0 := by simpa using hmean k
    constructor
    · rw [hreg]
      exact IndepFun.integrable_mul hind hint3 hint1
    · rw [hreg]
      have hfac : (∫ ω, Z i ω ^ 3 * Z k ω ^ 1 ∂P)
          = (∫ ω, Z i ω ^ 3 ∂P) * (∫ ω, Z k ω ^ 1 ∂P) :=
        IndepFun.integral_fun_mul_eq_mul_integral hind (hpowAESM i 3) (hpowAESM k 1)
      rw [hfac, hzero3, hzero1, mul_zero]
  have hF4 : ∀ i : Fin n,
      Integrable (fun ω => Z i ω * Z i ω * Z i ω * Z i ω) P ∧
      (∫ ω, Z i ω * Z i ω * Z i ω * Z i ω ∂P) = 3 * v ^ 2 := by
    intro i
    have h4 : (fun ω => Z i ω ^ 4) = (fun ω => Z i ω * Z i ω * Z i ω * Z i ω) := by
      funext ω; ring
    constructor
    · rw [← h4]; exact (hdep i).2.2.2.1
    · rw [← h4]; exact (hdep i).2.2.2.2.2.2.2
  have ns : ∀ {i j : Fin n}, ¬(i = j) → ¬(j = i) := fun h k => h k.symm
  by_cases hqp : q = p
  · subst hqp
    by_cases hqr : q = r
    · subst hqr
      by_cases hqs : q = s
      · subst hqs
        refine ⟨?_, ?_⟩
        · exact (hF4 q).1
        · rw [(hF4 q).2]
          first | (simp; ring) | simp
      · refine ⟨?_, ?_⟩
        · exact (hF31 q s hqs).1
        · rw [(hF31 q s hqs).2]
          simp only [if_pos rfl, if_neg hqs]
          ring
    · by_cases hqs : q = s
      · subst hqs
        refine ⟨?_, ?_⟩
        · rw [show (fun ω => Z q ω * Z q ω * Z r ω * Z q ω)
              = (fun ω => Z q ω * Z q ω * Z q ω * Z r ω) from by funext ω; ring]
          exact (hF31 q r hqr).1
        · rw [show (fun ω => Z q ω * Z q ω * Z r ω * Z q ω)
              = (fun ω => Z q ω * Z q ω * Z q ω * Z r ω) from by funext ω; ring,
            (hF31 q r hqr).2]
          simp only [if_pos rfl, if_neg hqr, if_neg (ns hqr)]
          ring
      · by_cases hrs : r = s
        · subst hrs
          refine ⟨?_, ?_⟩
          · exact (hF2 q q r r hqr hqr hqr hqr).1
          · rw [(hF2 q q r r hqr hqr hqr hqr).2]
            simp only [if_pos rfl, if_neg hqr]
            ring
        · refine ⟨?_, ?_⟩
          · exact (hF2 q q r s hqr hqs hqr hqs).1
          · rw [(hF2 q q r s hqr hqs hqr hqs).2]
            simp only [if_pos rfl, if_neg hqr, if_neg hqs, if_neg hrs]
            ring
  · by_cases hrp : r = p
    · subst hrp
      by_cases hqs : q = s
      · subst hqs
        refine ⟨?_, ?_⟩
        · rw [show (fun ω => Z r ω * Z q ω * Z r ω * Z q ω)
              = (fun ω => Z r ω * Z r ω * Z q ω * Z q ω) from by funext ω; ring]
          exact (hF2 r r q q (ns hqp) (ns hqp) (ns hqp) (ns hqp)).1
        · rw [show (fun ω => Z r ω * Z q ω * Z r ω * Z q ω)
              = (fun ω => Z r ω * Z r ω * Z q ω * Z q ω) from by funext ω; ring,
            (hF2 r r q q (ns hqp) (ns hqp) (ns hqp) (ns hqp)).2]
          simp only [if_pos rfl, if_neg (ns hqp), if_neg hqp]
          ring
      · by_cases hrs : r = s
        · subst hrs
          refine ⟨?_, ?_⟩
          · rw [show (fun ω => Z r ω * Z q ω * Z r ω * Z r ω)
                = (fun ω => Z r ω * Z r ω * Z r ω * Z q ω) from by funext ω; ring]
            exact (hF31 r q (ns hqp)).1
          · rw [show (fun ω => Z r ω * Z q ω * Z r ω * Z r ω)
                = (fun ω => Z r ω * Z r ω * Z r ω * Z q ω) from by funext ω; ring,
              (hF31 r q (ns hqp)).2]
            simp only [if_pos rfl, if_neg (ns hqp), if_neg hqp]
            ring
        · refine ⟨?_, ?_⟩
          · rw [show (fun ω => Z r ω * Z q ω * Z r ω * Z s ω)
                = (fun ω => Z r ω * Z r ω * Z q ω * Z s ω) from by funext ω; ring]
            exact (hF2 r r q s (ns hqp) hrs (ns hqp) hrs).1
          · rw [show (fun ω => Z r ω * Z q ω * Z r ω * Z s ω)
                = (fun ω => Z r ω * Z r ω * Z q ω * Z s ω) from by funext ω; ring,
              (hF2 r r q s (ns hqp) hrs (ns hqp) hrs).2]
            simp only [if_pos rfl, if_neg (ns hqp), if_neg hrs, if_neg hqs, if_neg hqp]
            ring
    · by_cases hsp : s = p
      · subst hsp
        by_cases hqr : q = r
        · subst hqr
          refine ⟨?_, ?_⟩
          · rw [show (fun ω => Z s ω * Z q ω * Z q ω * Z s ω)
                = (fun ω => Z s ω * Z s ω * Z q ω * Z q ω) from by funext ω; ring]
            exact (hF2 s s q q (ns hqp) (ns hqp) (ns hqp) (ns hqp)).1
          · rw [show (fun ω => Z s ω * Z q ω * Z q ω * Z s ω)
                = (fun ω => Z s ω * Z s ω * Z q ω * Z q ω) from by funext ω; ring,
              (hF2 s s q q (ns hqp) (ns hqp) (ns hqp) (ns hqp)).2]
            simp only [if_pos rfl, if_neg (ns hqp), if_neg hqp]
            ring
        · refine ⟨?_, ?_⟩
          · rw [show (fun ω => Z s ω * Z q ω * Z r ω * Z s ω)
                = (fun ω => Z s ω * Z s ω * Z q ω * Z r ω) from by funext ω; ring]
            exact (hF2 s s q r (ns hqp) (ns hrp) (ns hqp) (ns hrp)).1
          · rw [show (fun ω => Z s ω * Z q ω * Z r ω * Z s ω)
                = (fun ω => Z s ω * Z s ω * Z q ω * Z r ω) from by funext ω; ring,
              (hF2 s s q r (ns hqp) (ns hrp) (ns hqp) (ns hrp)).2]
            simp only [if_pos rfl, if_neg (ns hqp), if_neg (ns hrp), if_neg hrp, if_neg hqp,
              if_neg hqr]
            ring
      · by_cases hqr : q = r
        · subst hqr
          by_cases hqs : q = s
          · subst hqs
            refine ⟨?_, ?_⟩
            · rw [show (fun ω => Z p ω * Z q ω * Z q ω * Z q ω)
                  = (fun ω => Z q ω * Z q ω * Z q ω * Z p ω) from by funext ω; ring]
              exact (hF31 q p hqp).1
            · rw [show (fun ω => Z p ω * Z q ω * Z q ω * Z q ω)
                  = (fun ω => Z q ω * Z q ω * Z q ω * Z p ω) from by funext ω; ring,
                (hF31 q p hqp).2]
              simp only [if_pos rfl, if_neg (ns hqp)]
              ring
          · refine ⟨?_, ?_⟩
            · rw [show (fun ω => Z p ω * Z q ω * Z q ω * Z s ω)
                  = (fun ω => Z q ω * Z q ω * Z p ω * Z s ω) from by funext ω; ring]
              exact (hF2 q q p s hqp hqs hqp hqs).1
            · rw [show (fun ω => Z p ω * Z q ω * Z q ω * Z s ω)
                  = (fun ω => Z q ω * Z q ω * Z p ω * Z s ω) from by funext ω; ring,
                (hF2 q q p s hqp hqs hqp hqs).2]
              simp only [if_pos rfl, if_neg (ns hqp), if_neg hqs, if_neg (ns hsp)]
              ring
        · by_cases hqs : q = s
          · subst hqs
            refine ⟨?_, ?_⟩
            · rw [show (fun ω => Z p ω * Z q ω * Z r ω * Z q ω)
                  = (fun ω => Z q ω * Z q ω * Z p ω * Z r ω) from by funext ω; ring]
              exact (hF2 q q p r hqp hqr hqp hqr).1
            · rw [show (fun ω => Z p ω * Z q ω * Z r ω * Z q ω)
                  = (fun ω => Z q ω * Z q ω * Z p ω * Z r ω) from by funext ω; ring,
                (hF2 q q p r hqp hqr hqp hqr).2]
              simp only [if_pos rfl, if_neg (ns hqp), if_neg hqr, if_neg hrp, if_neg (ns hrp)]
              ring
          · by_cases hrs : r = s
            · subst hrs
              refine ⟨?_, ?_⟩
              · exact (hF2 p q r r (ns hrp) (ns hsp) hqr hqs).1
              · rw [(hF2 p q r r (ns hrp) (ns hsp) hqr hqs).2]
                simp only [if_pos rfl, if_neg (ns hqp), if_neg (ns hrp), if_neg hqr]
                ring
            · refine ⟨?_, ?_⟩
              · exact (hF2 p q r s (ns hrp) (ns hsp) hqr hqs).1
              · rw [(hF2 p q r s (ns hrp) (ns hsp) hqr hqs).2]
                simp only [if_pos rfl, if_neg (ns hqp), if_neg hrs, if_neg (ns hrp),
                  if_neg hqs, if_neg (ns hsp), if_neg hqr]
                ring

  /- @proof-region region.target-node.session.c94127eb02c57017 end -/
