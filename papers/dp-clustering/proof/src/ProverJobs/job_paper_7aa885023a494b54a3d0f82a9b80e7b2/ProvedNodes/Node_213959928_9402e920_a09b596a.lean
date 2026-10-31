import ProverJobs.job_paper_7aa885023a494b54a3d0f82a9b80e7b2.Vocabulary
import ProverJobs.job_paper_7aa885023a494b54a3d0f82a9b80e7b2.Base

open MeasureTheory
open scoped ENNReal BigOperators
open Statlib.Imported

open MeasureTheory
open scoped ENNReal BigOperators
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_213959928_9402e920 : ∀ (A : Type*) [Fintype A]
    (ν : Measure ℝ) [SigmaFinite ν]
    (f : ℝ → ℝ≥0∞) (hf : Measurable f),
    ∫⁻ (y : A → ℝ), (∏ i : A, f (y i)) ∂(Measure.pi (fun _ : A => ν)) =
      (∫⁻ (x : ℝ), f x ∂ν) ^ (Fintype.card A) := by
  /- @proof-region region.target-node.session.711de4317949d31b begin -/
  intro A hA ν hν f hf
  have keyFin : ∀ (n : ℕ) (g : Fin n → ℝ → ℝ≥0∞), (∀ i, Measurable (g i)) →
      ∫⁻ (y : Fin n → ℝ), (∏ i : Fin n, g i (y i)) ∂(Measure.pi (fun _ : Fin n => ν)) =
        ∏ i : Fin n, ∫⁻ (x : ℝ), g i x ∂ν := by
    intro n
    induction n with
    | zero =>
      intro g hg
      simp
    | succ n ih =>
      intro g hg
      let φ : Fin (n + 1) ≃ Option (Fin n) :=
        ((Fintype.equivFin (Option (Fin n))).trans
          (finCongr (by simp : Fintype.card (Option (Fin n)) = n + 1))).symm
      have hT : Measurable (fun z : Option (Fin n) → ℝ => fun i : Fin (n + 1) => z (φ i)) := by
        measurability
      have hmap : Measure.map (fun z : Option (Fin n) → ℝ => fun i : Fin (n + 1) => z (φ i))
          (Measure.pi (fun _ : Option (Fin n) => ν)) = Measure.pi (fun _ : Fin (n + 1) => ν) := by
        refine Eq.symm (Measure.pi_eq (μ := fun _ : Fin (n + 1) => ν) ?_)
        intro s hs
        have hbox : MeasurableSet (Set.univ.pi s) := by
          have hset : Set.univ.pi s
              = ⋂ i : Fin (n + 1), (fun y : Fin (n + 1) → ℝ => y i) ⁻¹' (s i) := by
            ext y
            simp
          rw [hset]
          exact MeasurableSet.iInter (fun i => (hs i).preimage (measurable_pi_apply i))
        rw [Measure.map_apply hT hbox]
        have hpre : (fun z : Option (Fin n) → ℝ => fun i : Fin (n + 1) => z (φ i)) ⁻¹'
            (Set.univ.pi s) = Set.univ.pi (fun j : Option (Fin n) => s (φ.symm j)) := by
          ext z
          simp only [Set.mem_preimage, Set.mem_univ_pi]
          constructor
          · intro h j
            simpa using h (φ.symm j)
          · intro h i
            have h' := h (φ i)
            rw [Equiv.symm_apply_apply] at h'
            exact h'
        rw [hpre, Measure.pi_pi]
        exact Equiv.prod_comp φ.symm (fun i => ν (s i))
      have hstep1 : ∫⁻ (y : Fin (n + 1) → ℝ), (∏ i : Fin (n + 1), g i (y i))
            ∂(Measure.pi (fun _ : Fin (n + 1) => ν))
          = ∫⁻ (z : Option (Fin n) → ℝ), (∏ j : Option (Fin n), g (φ.symm j) (z j))
            ∂(Measure.pi (fun _ : Option (Fin n) => ν)) := by
        rw [← hmap, MeasureTheory.lintegral_map]
        · refine lintegral_congr (fun z => ?_)
          rw [← Equiv.prod_comp φ (fun j : Option (Fin n) => g (φ.symm j) (z j))]
          exact Finset.prod_congr rfl (fun i _ => by rw [Equiv.symm_apply_apply])
        · exact Finset.measurable_prod (s := Finset.univ)
            (f := fun i (y : Fin (n + 1) → ℝ) => g i (y i))
            (fun i _ => (hg i).comp (measurable_pi_apply i))
        · measurability
      have hmapOpt := Measure.pi_map_piOptionEquivProd
        (β := fun _ : Option (Fin n) => (ℝ : Type)) (μ := fun _ : Option (Fin n) => ν)
      have hm2 : Measurable (fun z1 : Fin n → ℝ =>
          ∏ i : Fin n, g (φ.symm (some i)) (z1 i)) :=
        Finset.measurable_prod (s := Finset.univ)
          (f := fun i (z1 : Fin n → ℝ) => g (φ.symm (some i)) (z1 i))
          (fun i _ => (hg (φ.symm (some i))).comp (measurable_pi_apply i))
      have hstep2 : ∫⁻ (z : Option (Fin n) → ℝ), (∏ j : Option (Fin n), g (φ.symm j) (z j))
            ∂(Measure.pi (fun _ : Option (Fin n) => ν))
          = ∫⁻ (w : (Fin n → ℝ) × ℝ),
              (∏ i : Fin n, g (φ.symm (some i)) (w.1 i)) * (g (φ.symm none) w.2)
            ∂((Measure.pi (fun _ : Fin n => ν)).prod ν) := by
        rw [← hmapOpt, MeasureTheory.lintegral_map]
        · refine lintegral_congr (fun w => ?_)
          have h1 : (MeasurableEquiv.piOptionEquivProd
              (fun _ : Option (Fin n) => (ℝ : Type))).symm w none = w.2 := rfl
          have h2 : ∀ i : Fin n, (MeasurableEquiv.piOptionEquivProd
              (fun _ : Option (Fin n) => (ℝ : Type))).symm w (some i) = w.1 i := fun i => rfl
          rw [Fintype.prod_option]
          simp [h1, h2, mul_comm]
        · exact Finset.measurable_prod (s := Finset.univ)
            (f := fun j (z : Option (Fin n) → ℝ) => g (φ.symm j) (z j))
            (fun j _ => (hg (φ.symm j)).comp (measurable_pi_apply j))
        · measurability
      have hfac : ∫⁻ (w : (Fin n → ℝ) × ℝ),
            (∏ i : Fin n, g (φ.symm (some i)) (w.1 i)) * (g (φ.symm none) w.2)
            ∂((Measure.pi (fun _ : Fin n => ν)).prod ν)
          = (∫⁻ (x : Fin n → ℝ), (∏ i : Fin n, g (φ.symm (some i)) (x i))
              ∂(Measure.pi (fun _ : Fin n => ν))) * ∫⁻ (x : ℝ), g (φ.symm none) x ∂ν :=
        MeasureTheory.lintegral_prod_mul hm2.aemeasurable (hg (φ.symm none)).aemeasurable
      rw [hstep1, hstep2, hfac,
        ih (fun i => g (φ.symm (some i))) (fun i => hg (φ.symm (some i)))]
      have hR : ∏ i : Fin (n + 1), ∫⁻ (x : ℝ), g i x ∂ν
          = (∏ i : Fin n, ∫⁻ (x : ℝ), g (φ.symm (some i)) x ∂ν) *
            ∫⁻ (x : ℝ), g (φ.symm none) x ∂ν := by
        rw [mul_comm,
          ← Fintype.prod_option (fun j : Option (Fin n) => ∫⁻ (x : ℝ), g (φ.symm j) x ∂ν),
          ← Equiv.prod_comp φ (fun j : Option (Fin n) => ∫⁻ (x : ℝ), g (φ.symm j) x ∂ν)]
        exact Finset.prod_congr rfl (fun i _ => by rw [Equiv.symm_apply_apply])
      exact hR.symm
  have htrans : ∫⁻ (y : A → ℝ), (∏ i : A, f (y i)) ∂(Measure.pi (fun _ : A => ν))
      = ∫⁻ (y : Fin (Fintype.card A) → ℝ), (∏ i : Fin (Fintype.card A), f (y i))
        ∂(Measure.pi (fun _ : Fin (Fintype.card A) => ν)) := by
    let e : Fin (Fintype.card A) ≃ A := (Fintype.equivFin A).symm
    have hT : Measurable (fun z : A → ℝ => fun i : Fin (Fintype.card A) => z (e i)) := by
      measurability
    have hmap : Measure.map (fun z : A → ℝ => fun i : Fin (Fintype.card A) => z (e i))
        (Measure.pi (fun _ : A => ν)) = Measure.pi (fun _ : Fin (Fintype.card A) => ν) := by
      refine Eq.symm (Measure.pi_eq (μ := fun _ : Fin (Fintype.card A) => ν) ?_)
      intro s hs
      have hbox : MeasurableSet (Set.univ.pi s) := by
        have hset : Set.univ.pi s
            = ⋂ i : Fin (Fintype.card A),
              (fun y : Fin (Fintype.card A) → ℝ => y i) ⁻¹' (s i) := by
          ext y
          simp
        rw [hset]
        exact MeasurableSet.iInter (fun i => (hs i).preimage (measurable_pi_apply i))
      rw [Measure.map_apply hT hbox]
      have hpre : (fun z : A → ℝ => fun i : Fin (Fintype.card A) => z (e i)) ⁻¹'
          (Set.univ.pi s) = Set.univ.pi (fun j : A => s (e.symm j)) := by
        ext z
        simp only [Set.mem_preimage, Set.mem_univ_pi]
        constructor
        · intro h j
          simpa using h (e.symm j)
        · intro h i
          have h' := h (e i)
          rw [Equiv.symm_apply_apply] at h'
          exact h'
      rw [hpre, Measure.pi_pi]
      exact Equiv.prod_comp e.symm (fun i => ν (s i))
    rw [← hmap, MeasureTheory.lintegral_map]
    · refine lintegral_congr (fun z => ?_)
      exact (Equiv.prod_comp e (fun j : A => f (z j))).symm
    · exact Finset.measurable_prod (s := Finset.univ)
        (f := fun i (y : Fin (Fintype.card A) → ℝ) => f (y i))
        (fun i _ => hf.comp (measurable_pi_apply i))
    · measurability
  rw [htrans, keyFin (Fintype.card A) (fun _ => f) (fun _ => hf)]
  simp [Finset.prod_const]
  /- @proof-region region.target-node.session.711de4317949d31b end -/

end Statlib.Imported
