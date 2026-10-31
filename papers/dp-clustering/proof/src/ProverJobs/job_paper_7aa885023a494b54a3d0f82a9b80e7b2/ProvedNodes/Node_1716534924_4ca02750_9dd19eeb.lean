import ProverJobs.job_paper_7aa885023a494b54a3d0f82a9b80e7b2.Vocabulary
import ProverJobs.job_paper_7aa885023a494b54a3d0f82a9b80e7b2.Base
import ProverJobs.job_paper_7aa885023a494b54a3d0f82a9b80e7b2.ProvedNodes.Node_1960594570_2408034e_38e7022d

open MeasureTheory
open scoped ENNReal BigOperators
open Statlib.Imported

open MeasureTheory
open scoped ENNReal BigOperators
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_1716534924_4ca02750 : ∀ (c thetaStar : ℝ) (hc : 0 < c)
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (g q0 : ℝ → ℝ)
    (hg_meas : Measurable g) (hq0_meas : Measurable q0)
    (hg_nonneg : ∀ x : ℝ, 0 ≤ g x) (hq0_nonneg : ∀ θ : ℝ, 0 ≤ q0 θ)
    (hg_pos : ∀ x ∈ Set.Icc (thetaStar - c) (thetaStar + c), 0 < g x)
    (A : Type) [Fintype A] (ha : 1 ≤ Fintype.card A),
    (∫⁻ y in {y : A → ℝ | ∀ i : A, y i ∈ Set.Icc (thetaStar - c) (thetaStar + c)},
        ∫⁻ θ, (∏ i : A, ENNReal.ofReal (g (y i - θ) / g (y i - thetaStar)))
            * ENNReal.ofReal (q0 θ) ∂volume
        ∂(Measure.pi (fun _ : A => P)))
      = ∫⁻ θ, (∫⁻ x in Set.Icc (thetaStar - c) (thetaStar + c),
            ENNReal.ofReal (g (x - θ) / g (x - thetaStar)) ∂P) ^ (Fintype.card A)
          * ENNReal.ofReal (q0 θ) ∂volume := by
  /- @proof-region region.target-node.session.cfac5665fe051511 begin -/
  intro c θstar hc P hP g q0 hg_meas hq0_meas hg_nonneg hq0_nonneg hg_pos A instA ha
  haveI := hP
  haveI := hP
  classical
  set W : Set ℝ := Set.Icc (θstar - c) (θstar + c) with hW
  have hWmeas : MeasurableSet W := measurableSet_Icc
  set S : Set (A → ℝ) := {y : A → ℝ | ∀ i : A, y i ∈ W} with hS
  have hSmeas : MeasurableSet S := by
    have hS' : S = Set.univ.pi (fun _ : A => W) := by
      ext y
      simp [hS]
    rw [hS']
    exact MeasurableSet.univ_pi (fun _ => hWmeas)
  have hφ_meas : ∀ θ : ℝ, Measurable fun x : ℝ =>
      ENNReal.ofReal (g (x - θ) / g (x - θstar)) := by
    intro θ
    fun_prop
  have hK_meas : AEMeasurable (Function.uncurry fun (y : A → ℝ) (θ : ℝ) =>
      (∏ i : A, ENNReal.ofReal (g (y i - θ) / g (y i - θstar))) * ENNReal.ofReal (q0 θ))
      (((Measure.pi (fun _ : A => P)).restrict S).prod (volume : Measure ℝ)) := by
    apply Measurable.aemeasurable
    show Measurable (fun p : (A → ℝ) × ℝ =>
      (∏ i : A, ENNReal.ofReal (g (p.1 i - p.2) / g (p.1 i - θstar))) *
        ENNReal.ofReal (q0 p.2))
    fun_prop
  have hswap := MeasureTheory.lintegral_lintegral_swap
    (μ := (Measure.pi (fun _ : A => P)).restrict S) (ν := (volume : Measure ℝ))
    (f := fun (y : A → ℝ) (θ : ℝ) =>
      (∏ i : A, ENNReal.ofReal (g (y i - θ) / g (y i - θstar))) * ENNReal.ofReal (q0 θ))
    hK_meas
  have hswap' : (∫⁻ (y : A → ℝ) in S,
        ∫⁻ (θ : ℝ),
          (∏ i : A, ENNReal.ofReal (g (y i - θ) / g (y i - θstar))) * ENNReal.ofReal (q0 θ)
          ∂(volume : Measure ℝ)
        ∂(Measure.pi (fun _ : A => P)))
      = ∫⁻ (θ : ℝ),
          (∫⁻ (y : A → ℝ) in S,
            (∏ i : A, ENNReal.ofReal (g (y i - θ) / g (y i - θstar))) * ENNReal.ofReal (q0 θ)
            ∂(Measure.pi (fun _ : A => P)))
          ∂(volume : Measure ℝ) := hswap
  refine Eq.trans hswap' ?_
  refine lintegral_congr fun θ => ?_
  have hbase_meas : Measurable fun y : A → ℝ =>
      ∏ i : A, ENNReal.ofReal (g (y i - θ) / g (y i - θstar)) := by
    fun_prop
  have h1 : ∫⁻ y, (∏ i : A, ENNReal.ofReal (g (y i - θ) / g (y i - θstar))) *
        ENNReal.ofReal (q0 θ) ∂((Measure.pi (fun _ : A => P)).restrict S)
      = (∫⁻ y, (∏ i : A, ENNReal.ofReal (g (y i - θ) / g (y i - θstar)))
          ∂((Measure.pi (fun _ : A => P)).restrict S)) * ENNReal.ofReal (q0 θ) := by
    rw [MeasureTheory.lintegral_mul_const]
    exact hbase_meas
  have h2 : ∫⁻ y, (∏ i : A, ENNReal.ofReal (g (y i - θ) / g (y i - θstar)))
        ∂((Measure.pi (fun _ : A => P)).restrict S)
      = ∫⁻ y, (∏ i : A,
          (W.indicator fun x : ℝ => ENNReal.ofReal (g (x - θ) / g (x - θstar))) (y i))
          ∂(Measure.pi (fun _ : A => P)) := by
    have hpt : (fun y : A → ℝ =>
          ∏ i : A, (W.indicator fun x : ℝ => ENNReal.ofReal (g (x - θ) / g (x - θstar))) (y i))
        = S.indicator (fun y : A → ℝ =>
          ∏ i : A, ENNReal.ofReal (g (y i - θ) / g (y i - θstar))) := by
      funext y
      by_cases hy : y ∈ S
      · have hyi : ∀ i : A, y i ∈ W := by simpa [hS] using hy
        rw [Set.indicator_of_mem hy]
        exact Finset.prod_congr rfl fun i _ =>
          Set.indicator_of_mem (hyi i)
            (fun x : ℝ => ENNReal.ofReal (g (x - θ) / g (x - θstar)))
      · rw [Set.indicator_of_notMem hy]
        have hy' : ∃ i : A, y i ∉ W := by
          by_contra h
          simp only [not_exists, not_not] at h
          exact hy (by simpa [hS] using h)
        obtain ⟨i, hi⟩ := hy'
        exact Finset.prod_eq_zero (Finset.mem_univ i)
          (Set.indicator_of_notMem hi
            (fun x : ℝ => ENNReal.ofReal (g (x - θ) / g (x - θstar))))
    rw [hpt]
    exact (MeasureTheory.lintegral_indicator hSmeas
      (fun y : A → ℝ => ∏ i : A, ENNReal.ofReal (g (y i - θ) / g (y i - θstar)))).symm
  have h3 : ∫⁻ y, (∏ i : A,
        (W.indicator fun x : ℝ => ENNReal.ofReal (g (x - θ) / g (x - θstar))) (y i))
        ∂(Measure.pi (fun _ : A => P))
      = ∏ i : A, ∫⁻ x,
          (W.indicator fun x : ℝ => ENNReal.ofReal (g (x - θ) / g (x - θstar))) x ∂P := by
    set f : ℝ → ENNReal :=
      W.indicator (fun x : ℝ => ENNReal.ofReal (g (x - θ) / g (x - θstar))) with hfdef
    have hf : Measurable f := by
      rw [hfdef]
      exact (hφ_meas θ).indicator hWmeas
    have key : ∀ (n : ℕ) (u : ℝ → ENNReal), Measurable u →
        ∫⁻ a : Fin n → ℝ, (∏ j : Fin n, u (a j)) ∂(Measure.pi (fun _ : Fin n => P))
          = ∏ j : Fin n, ∫⁻ x, u x ∂P := by
      intro n
      induction n with
      | zero =>
        intro u hu
        have hL : ∫⁻ a : Fin 0 → ℝ, (∏ j : Fin 0, u (a j))
            ∂(Measure.pi (fun _ : Fin 0 => P)) = 1 := by
          have hpt0 : (fun a : Fin 0 → ℝ => ∏ j : Fin 0, u (a j)) =
              fun _ => (1 : ENNReal) := by
            funext a
            simp
          rw [hpt0, MeasureTheory.lintegral_one, Measure.pi_univ]
          simp
        have hR : (∏ j : Fin 0, ∫⁻ x, u x ∂P) = 1 := by simp
        rw [hL, hR]
      | succ n ih =>
        intro u hu
        have hmp := MeasureTheory.measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 1) => (P : Measure ℝ)) (0 : Fin (n + 1))
        have hFmeas : Measurable fun p : ℝ × (Fin n → ℝ) =>
            u p.1 * ∏ j : Fin n, u (p.2 j) := by
          fun_prop
        have hpt : ∀ a : Fin (n + 1) → ℝ,
            (fun p : ℝ × (Fin n → ℝ) => u p.1 * ∏ j : Fin n, u (p.2 j))
              ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0) a)
            = ∏ j : Fin (n + 1), u (a j) := by
          intro a
          show u (((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0) a).1) *
              ∏ j : Fin n,
                u (((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0) a).2 j)
            = ∏ j : Fin (n + 1), u (a j)
          rw [Fin.prod_univ_succAbove (fun j : Fin (n + 1) => u (a j)) 0]
          have htail :
              ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0) a).2
                = fun j : Fin n => a j.succ := Fin.tail_def
          rw [htail]
          simp
        have hstep : ∫⁻ a : Fin (n + 1) → ℝ, (∏ j : Fin (n + 1), u (a j))
              ∂(Measure.pi (fun _ : Fin (n + 1) => P))
            = ∫⁻ p : ℝ × (Fin n → ℝ), u p.1 * ∏ j : Fin n, u (p.2 j)
              ∂(P.prod (Measure.pi (fun _ : Fin n => P))) := by
          calc ∫⁻ a : Fin (n + 1) → ℝ, (∏ j : Fin (n + 1), u (a j))
                ∂(Measure.pi (fun _ : Fin (n + 1) => P))
              = ∫⁻ a : Fin (n + 1) → ℝ,
                  (fun p : ℝ × (Fin n → ℝ) => u p.1 * ∏ j : Fin n, u (p.2 j))
                    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0) a)
                  ∂(Measure.pi (fun _ : Fin (n + 1) => P)) := by
                refine lintegral_congr fun a => (hpt a).symm
            _ = ∫⁻ p : ℝ × (Fin n → ℝ), u p.1 * ∏ j : Fin n, u (p.2 j)
                  ∂(P.prod (Measure.pi (fun _ : Fin n => P))) :=
                hmp.lintegral_comp
                  (f := fun p : ℝ × (Fin n → ℝ) => u p.1 * ∏ j : Fin n, u (p.2 j)) hFmeas
        have hg2 : Measurable fun z : Fin n → ℝ => ∏ j : Fin n, u (z j) := by
          fun_prop
        have hprod : ∫⁻ p : ℝ × (Fin n → ℝ), u p.1 * ∏ j : Fin n, u (p.2 j)
              ∂(P.prod (Measure.pi (fun _ : Fin n => P)))
            = (∫⁻ x, u x ∂P) * (∏ j : Fin n, ∫⁻ x, u x ∂P) := by
          rw [MeasureTheory.lintegral_prod_mul (f := u)
            (g := fun z : Fin n → ℝ => ∏ j : Fin n, u (z j))
            hu.aemeasurable hg2.aemeasurable]
          rw [ih u hu]
        rw [hstep, hprod, Fin.prod_univ_succ]
    let e : A ≃ Fin (Fintype.card A) := Fintype.equivFin A
    have hmp2 := MeasureTheory.measurePreserving_piCongrLeft
      (fun _ : A => (P : Measure ℝ)) e.symm
    have hFmeas2 : Measurable fun y : A → ℝ => ∏ i : A, f (y i) := by
      fun_prop
    have hcoe : ∀ (x : A → ℝ) (j : Fin (Fintype.card A)),
        (MeasurableEquiv.piCongrLeft (fun _ : A => ℝ) e.symm).symm x j = x (e.symm j) := by
      intro x j
      rfl
    have htrans : ∫⁻ y : A → ℝ, (∏ i : A, f (y i)) ∂(Measure.pi (fun _ : A => P))
        = ∫⁻ a : Fin (Fintype.card A) → ℝ, (∏ j : Fin (Fintype.card A), f (a j))
            ∂(Measure.pi (fun _ : Fin (Fintype.card A) => P)) := by
      rw [← hmp2.lintegral_comp (f := fun y : A → ℝ => ∏ i : A, f (y i)) hFmeas2]
      refine lintegral_congr fun a => ?_
      show (∏ i : A, f ((MeasurableEquiv.piCongrLeft (fun _ : A => ℝ) e.symm a) i))
        = ∏ j : Fin (Fintype.card A), f (a j)
      rw [← Equiv.prod_comp e.symm
        (fun i : A => f ((MeasurableEquiv.piCongrLeft (fun _ : A => ℝ) e.symm a) i))]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [← hcoe (MeasurableEquiv.piCongrLeft (fun _ : A => ℝ) e.symm a) j,
        MeasurableEquiv.symm_apply_apply]
    have hkey := key (Fintype.card A) f hf
    have hpow1 : (∏ j : Fin (Fintype.card A), ∫⁻ x, f x ∂P)
        = (∫⁻ x, f x ∂P) ^ Fintype.card A := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hpow2 : (∏ i : A, ∫⁻ x, f x ∂P) = (∫⁻ x, f x ∂P) ^ Fintype.card A := by
      rw [Finset.prod_const, Finset.card_univ]
    rw [htrans, hkey, hpow1, hpow2]
  have h4 : ∀ i : A, ∫⁻ x,
        (W.indicator fun x : ℝ => ENNReal.ofReal (g (x - θ) / g (x - θstar))) x ∂P
      = ∫⁻ x in W, ENNReal.ofReal (g (x - θ) / g (x - θstar)) ∂P := by
    intro i
    exact MeasureTheory.lintegral_indicator hWmeas
      (fun x : ℝ => ENNReal.ofReal (g (x - θ) / g (x - θstar)))
  have h5 : ∏ i : A, (∫⁻ x in W, ENNReal.ofReal (g (x - θ) / g (x - θstar)) ∂P)
      = (∫⁻ x in W, ENNReal.ofReal (g (x - θ) / g (x - θstar)) ∂P) ^ Fintype.card A := by
    rw [Finset.prod_const, Finset.card_univ]
  calc ∫⁻ y, (∏ i : A, ENNReal.ofReal (g (y i - θ) / g (y i - θstar))) *
        ENNReal.ofReal (q0 θ) ∂((Measure.pi (fun _ : A => P)).restrict S)
      = (∫⁻ y, (∏ i : A, ENNReal.ofReal (g (y i - θ) / g (y i - θstar)))
          ∂((Measure.pi (fun _ : A => P)).restrict S)) * ENNReal.ofReal (q0 θ) := h1
    _ = (∫⁻ y, (∏ i : A,
          (W.indicator fun x : ℝ => ENNReal.ofReal (g (x - θ) / g (x - θstar))) (y i))
          ∂(Measure.pi (fun _ : A => P))) * ENNReal.ofReal (q0 θ) := by rw [h2]
    _ = (∏ i : A, ∫⁻ x,
          (W.indicator fun x : ℝ => ENNReal.ofReal (g (x - θ) / g (x - θstar))) x ∂P) *
          ENNReal.ofReal (q0 θ) := by rw [h3]
    _ = (∏ i : A, ∫⁻ x in W, ENNReal.ofReal (g (x - θ) / g (x - θstar)) ∂P) *
          ENNReal.ofReal (q0 θ) := by
          rw [Finset.prod_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset A)) => h4 i)]
    _ = (∫⁻ x in W, ENNReal.ofReal (g (x - θ) / g (x - θstar)) ∂P) ^ (Fintype.card A) *
          ENNReal.ofReal (q0 θ) := by rw [h5]
  /- @proof-region region.target-node.session.cfac5665fe051511 end -/

end Statlib.Imported
