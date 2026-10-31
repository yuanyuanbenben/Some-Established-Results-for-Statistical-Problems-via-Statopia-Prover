import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q01.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q01.Base

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

set_option autoImplicit false in
theorem statopia_math_node_2950655660_fcc1ce66 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (d : ℕ) (X : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (hX_ident : ∀ i, P.map (X i) = P.map (X 0))
    (k : ℕ) (hk : 0 < k) (c : ℝ)
    (t : EuclideanSpace ℝ (Fin d)),
    charFun (P.map (fun ω => (c / (k : ℝ)) • ∑ i ∈ Finset.range k, X i ω)) t =
      (charFun (P.map (X 0)) ((c / (k : ℝ)) • t)) ^ k := by
  /- @proof-region region.target-node.session.62fca4d8296c2c84 begin -/
  intro Ω _ P _ d X hX_meas hX_indep hX_ident k hk c t
  have hmain : ∀ (n : ℕ), 0 < n → ∀ (r : ℝ) (s : EuclideanSpace ℝ (Fin d)),
      charFun (P.map (fun ω => r • ∑ i ∈ Finset.range n, X i ω)) s
        = (charFun (P.map (X 0)) (r • s)) ^ n := by
    intro n hn
    refine Nat.le_induction (m := 1) ?_ ?_ n hn
    · intro r s
      have h1 : (fun ω => r • ∑ i ∈ Finset.range 1, X i ω) = fun ω => r • X 0 ω := by
        funext ω
        simp
      have hmap : Measure.map (fun x : EuclideanSpace ℝ (Fin d) => r • x) (P.map (X 0))
          = Measure.map (fun ω => r • X 0 ω) P :=
        Measure.map_map (by fun_prop) (hX_meas 0)
      rw [h1, pow_one, ← hmap, MeasureTheory.charFun_map_smul]
    · intro m hm ih r s
      have hF_meas : Measurable (fun ω => r • ∑ i ∈ Finset.range m, X i ω) := by
        have h : Measurable (fun ω => ∑ i ∈ Finset.range m, X i ω) :=
          Finset.measurable_sum _ fun i _ => hX_meas i
        exact h.const_smul r
      have hG_meas : Measurable (fun ω => r • X m ω) := (hX_meas m).const_smul r
      have hFG : (fun ω => r • ∑ i ∈ Finset.range m, X i ω) ⟂ᵢ[P] (fun ω => r • X m ω) := by
        have hdisj : Disjoint (Finset.range m) ({m} : Finset ℕ) := by simp
        have hindep :=
          ProbabilityTheory.iIndepFun.indepFun_finset (f := X) (μ := P) (Finset.range m)
            ({m} : Finset ℕ) hdisj hX_indep hX_meas
        have hL : Measurable (fun y : ↥(Finset.range m) → EuclideanSpace ℝ (Fin d) =>
            r • ∑ i : ↥(Finset.range m), y i) := by
          have h : Measurable (fun y : ↥(Finset.range m) → EuclideanSpace ℝ (Fin d) =>
              ∑ i : ↥(Finset.range m), y i) :=
            Finset.measurable_sum _ fun i _ => measurable_pi_apply i
          exact h.const_smul r
        have hmem : m ∈ ({m} : Finset ℕ) := Finset.mem_singleton_self m
        have hR : Measurable (fun z : ↥({m} : Finset ℕ) → EuclideanSpace ℝ (Fin d) =>
            r • z ⟨m, hmem⟩) :=
          (measurable_pi_apply (X := fun _ : ↥({m} : Finset ℕ) =>
            EuclideanSpace ℝ (Fin d)) ⟨m, hmem⟩).const_smul r
        have hcoe : ∀ (g : ℕ → EuclideanSpace ℝ (Fin d)),
            (∑ i : ↥(Finset.range m), g ↑i) = ∑ i ∈ Finset.range m, g i := by
          intro g
          rw [Finset.sum_coe_sort]
        have hcomp := hindep.comp hL hR
        have hLfun : ((fun y : ↥(Finset.range m) → EuclideanSpace ℝ (Fin d) =>
              r • ∑ i : ↥(Finset.range m), y i) ∘ (fun a (i : ↥(Finset.range m)) => X ↑i a))
            = fun ω => r • ∑ i ∈ Finset.range m, X i ω := by
          funext ω
          simp only [Function.comp_apply]
          rw [hcoe (fun i => X i ω)]
        have hRfun : ((fun z : ↥({m} : Finset ℕ) → EuclideanSpace ℝ (Fin d) => r • z ⟨m, hmem⟩) ∘
              (fun a (i : ↥({m} : Finset ℕ)) => X ↑i a)) = fun ω => r • X m ω := by
          funext ω
          simp [Function.comp_apply]
        rw [← hLfun, ← hRfun]
        exact hcomp
      have hmul :=
        ProbabilityTheory.IndepFun.charFun_map_add_eq_mul hF_meas.aemeasurable hG_meas.aemeasurable hFG
      have hrewrite : (fun ω => r • ∑ i ∈ Finset.range (m + 1), X i ω)
          = (fun ω => r • ∑ i ∈ Finset.range m, X i ω) + (fun ω => r • X m ω) := by
        funext ω
        rw [Finset.sum_range_succ, smul_add]
        rfl
      have hsingle : charFun (Measure.map (fun ω => r • X m ω) P) s
          = charFun (P.map (X 0)) (r • s) := by
        have hmap : Measure.map (fun x : EuclideanSpace ℝ (Fin d) => r • x) (P.map (X m))
            = Measure.map (fun ω => r • X m ω) P :=
          Measure.map_map (by fun_prop) (hX_meas m)
        rw [← hmap, MeasureTheory.charFun_map_smul, hX_ident m]
      rw [hrewrite, hmul]
      change charFun (Measure.map (fun ω => r • ∑ i ∈ Finset.range m, X i ω) P) s
          * charFun (Measure.map (fun ω => r • X m ω) P) s
        = (charFun (P.map (X 0)) (r • s)) ^ (m + 1)
      rw [ih r s, hsingle, pow_succ]
  exact hmain k hk (c / (k : ℝ)) t
  /- @proof-region region.target-node.session.62fca4d8296c2c84 end -/
