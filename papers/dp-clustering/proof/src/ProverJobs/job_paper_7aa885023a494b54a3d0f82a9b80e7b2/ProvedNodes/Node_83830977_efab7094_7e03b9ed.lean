import ProverJobs.job_paper_7aa885023a494b54a3d0f82a9b80e7b2.Vocabulary
import ProverJobs.job_paper_7aa885023a494b54a3d0f82a9b80e7b2.Base

open MeasureTheory
open scoped ENNReal BigOperators
open Statlib.Imported

open MeasureTheory
open scoped ENNReal BigOperators
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_83830977_efab7094 : ∀ (n s : ℕ) (A : Fin s → Finset (Fin n))
    (hdisj : ∀ h h' : Fin s, h ≠ h' → Disjoint (A h) (A h'))
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (F : (h : Fin s) → ({i : Fin n // i ∈ A h} → ℝ) → ℝ≥0∞)
    (hF : ∀ h : Fin s, Measurable (F h)),
    ∫⁻ (X : Fin n → ℝ), (∏ h : Fin s, F h (fun i => X i.1))
        ∂(Measure.pi (fun _ : Fin n => P))
      = ∏ h : Fin s,
          ∫⁻ (y : {i : Fin n // i ∈ A h} → ℝ), F h y
            ∂(Measure.pi (fun _ : {i : Fin n // i ∈ A h} => P)) := by
  /- @proof-region region.target-node.session.856fb91f25575fef begin -/
  intro n s A hdisj P _ F hF
  have split : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (s : Finset ι)
      (f : ({i : ι // i ∈ s} → ℝ) → ℝ≥0∞) (g : ({i : ι // ¬ (i ∈ s)} → ℝ) → ℝ≥0∞),
      Measurable f → Measurable g →
      ∫⁻ (X : ι → ℝ), f (fun i => X i.1) * g (fun i => X i.1) ∂(Measure.pi (fun _ : ι => P))
        = (∫⁻ (u : {i : ι // i ∈ s} → ℝ), f u ∂(Measure.pi (fun _ : {i : ι // i ∈ s} => P)))
          * ∫⁻ (v : {i : ι // ¬ (i ∈ s)} → ℝ), g v
              ∂(Measure.pi (fun _ : {i : ι // ¬ (i ∈ s)} => P)) := by
    intro ι _ _ s f g hf hg
    let σ : Type := {i : ι // i ∈ s} ⊕ {i : ι // ¬ (i ∈ s)}
    let e : σ ≃ ι := Equiv.sumCompl (fun i => i ∈ s)
    let e2 : (σ → ℝ) ≃ᵐ (ι → ℝ) := MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e
    let e1 : (({i : ι // i ∈ s} → ℝ) × ({i : ι // ¬ (i ∈ s)} → ℝ)) ≃ᵐ (σ → ℝ) :=
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : σ => ℝ)).symm
    let F : (ι → ℝ) → ℝ≥0∞ := fun X => f (fun i => X i.1) * g (fun i => X i.1)
    have hstep1 : ∫⁻ (X : ι → ℝ), F X ∂(Measure.pi (fun _ : ι => P))
        = ∫⁻ (Y : σ → ℝ), F (e2 Y) ∂(Measure.pi (fun _ : σ => P)) :=
      MeasureTheory.MeasurePreserving.lintegral_map_equiv F e2
        (MeasureTheory.measurePreserving_piCongrLeft (fun _ : ι => P) e)
    have hstep2 : ∫⁻ (Y : σ → ℝ), F (e2 Y) ∂(Measure.pi (fun _ : σ => P))
        = ∫⁻ (z : ({i : ι // i ∈ s} → ℝ) × ({i : ι // ¬ (i ∈ s)} → ℝ)), F (e2 (e1 z))
            ∂((Measure.pi (fun _ : {i : ι // i ∈ s} => P)).prod
              (Measure.pi (fun _ : {i : ι // ¬ (i ∈ s)} => P))) :=
      MeasureTheory.MeasurePreserving.lintegral_map_equiv (fun Y : σ → ℝ => F (e2 Y)) e1
        (MeasureTheory.measurePreserving_sumPiEquivProdPi_symm (fun _ : σ => P))
    have hpt : ∀ z : ({i : ι // i ∈ s} → ℝ) × ({i : ι // ¬ (i ∈ s)} → ℝ),
        F (e2 (e1 z)) = f z.1 * g z.2 := by
      intro z
      have hA : (fun i : {i : ι // i ∈ s} => e2 (e1 z) i.1) = z.1 := by
        funext i
        rw [show (i.1 : ι) = e (Sum.inl i) from rfl]
        exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℝ) e (e1 z) (Sum.inl i)
      have hB : (fun i : {i : ι // ¬ (i ∈ s)} => e2 (e1 z) i.1) = z.2 := by
        funext i
        rw [show (i.1 : ι) = e (Sum.inr i) from rfl]
        exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℝ) e (e1 z) (Sum.inr i)
      show f (fun i : {i : ι // i ∈ s} => e2 (e1 z) i.1) * g (fun i : {i : ι // ¬ (i ∈ s)} => e2 (e1 z) i.1)
        = f z.1 * g z.2
      rw [hA, hB]
    have hstep3 : ∫⁻ (z : ({i : ι // i ∈ s} → ℝ) × ({i : ι // ¬ (i ∈ s)} → ℝ)), F (e2 (e1 z))
          ∂((Measure.pi (fun _ : {i : ι // i ∈ s} => P)).prod
            (Measure.pi (fun _ : {i : ι // ¬ (i ∈ s)} => P)))
        = (∫⁻ (u : {i : ι // i ∈ s} → ℝ), f u ∂(Measure.pi (fun _ : {i : ι // i ∈ s} => P)))
          * ∫⁻ (v : {i : ι // ¬ (i ∈ s)} → ℝ), g v
              ∂(Measure.pi (fun _ : {i : ι // ¬ (i ∈ s)} => P)) := by
      calc ∫⁻ (z : ({i : ι // i ∈ s} → ℝ) × ({i : ι // ¬ (i ∈ s)} → ℝ)), F (e2 (e1 z))
            ∂((Measure.pi (fun _ : {i : ι // i ∈ s} => P)).prod
              (Measure.pi (fun _ : {i : ι // ¬ (i ∈ s)} => P)))
          = ∫⁻ (z : ({i : ι // i ∈ s} → ℝ) × ({i : ι // ¬ (i ∈ s)} → ℝ)), f z.1 * g z.2
              ∂((Measure.pi (fun _ : {i : ι // i ∈ s} => P)).prod
                (Measure.pi (fun _ : {i : ι // ¬ (i ∈ s)} => P))) :=
            MeasureTheory.lintegral_congr hpt
        _ = (∫⁻ (u : {i : ι // i ∈ s} → ℝ), f u ∂(Measure.pi (fun _ : {i : ι // i ∈ s} => P)))
              * ∫⁻ (v : {i : ι // ¬ (i ∈ s)} → ℝ), g v
                  ∂(Measure.pi (fun _ : {i : ι // ¬ (i ∈ s)} => P)) :=
            MeasureTheory.lintegral_prod_mul (μ := Measure.pi (fun _ : {i : ι // i ∈ s} => P))
              (ν := Measure.pi (fun _ : {i : ι // ¬ (i ∈ s)} => P)) hf.aemeasurable hg.aemeasurable
    exact hstep1.trans (hstep2.trans hstep3)
  have main : ∀ (s : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (A : Fin s → Finset ι)
      (F : (h : Fin s) → ({i : ι // i ∈ A h} → ℝ) → ℝ≥0∞),
      (∀ h, Measurable (F h)) → (∀ h h', h ≠ h' → Disjoint (A h) (A h')) →
      ∫⁻ (X : ι → ℝ), ∏ h, F h (fun i => X i.1) ∂(Measure.pi (fun _ : ι => P))
        = ∏ h, ∫⁻ (y : {i : ι // i ∈ A h} → ℝ), F h y
            ∂(Measure.pi (fun _ : {i : ι // i ∈ A h} => P)) := by
    intro s
    induction s with
    | zero =>
      intro ι _ _ A F hF hdisj
      simp [MeasureTheory.Measure.pi_univ]
    | succ s ih =>
      intro ι _ _ A F hF hdisj
      have hsne : ∀ h : Fin s, (h.succ : Fin (s + 1)) ≠ 0 := by
        intro h hh
        have h1 : ((h.succ : Fin (s + 1)) : ℕ) = 0 := by rw [hh]; rfl
        exact Nat.succ_ne_zero h.val h1
      have hnot : ∀ (h : Fin s) (i : {i : ι // i ∈ A h.succ}), ¬ (i.1 ∈ A 0) :=
        fun h i hcon => (Finset.disjoint_left.mp (hdisj h.succ 0 (hsne h))) i.2 hcon
      let ι' : Type := {i : ι // ¬ (i ∈ A 0)}
      let A' : Fin s → Finset ι' := fun h => Finset.univ.filter (fun i' : ι' => i'.1 ∈ A h.succ)
      let e : ∀ h : Fin s, {i : ι // i ∈ A h.succ} ≃ {i' : ι' // i' ∈ A' h} := fun h =>
        { toFun := fun i =>
            ⟨⟨i.1, hnot h i⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.2⟩⟩
          invFun := fun i' => ⟨i'.1.1, (Finset.mem_filter.mp i'.2).2⟩
          left_inv := fun i => Subtype.ext rfl
          right_inv := fun i' => Subtype.ext (Subtype.ext rfl) }
      let F' : (h : Fin s) → ({i' : ι' // i' ∈ A' h} → ℝ) → ℝ≥0∞ :=
        fun h z => F h.succ (fun i => z (e h i))
      let g : ({i : ι // ¬ (i ∈ A 0)} → ℝ) → ℝ≥0∞ :=
        fun v => ∏ h : Fin s, F h.succ (fun i : {i : ι // i ∈ A h.succ} => v ⟨i.1, hnot h i⟩)
      have hF'meas : ∀ h : Fin s, Measurable (F' h) := by
        intro h
        refine (hF h.succ).comp ?_
        exact measurable_pi_iff.mpr (fun i => measurable_pi_apply (e h i))
      have hg_meas : Measurable g := by
        show Measurable (fun v : ({i : ι // ¬ (i ∈ A 0)} → ℝ) =>
          ∏ h : Fin s, F h.succ (fun i : {i : ι // i ∈ A h.succ} => v ⟨i.1, hnot h i⟩))
        exact Finset.measurable_prod Finset.univ (fun h _ =>
          (hF h.succ).comp (measurable_pi_iff.mpr (fun i => measurable_pi_apply (⟨i.1, hnot h i⟩ : {i : ι // ¬ (i ∈ A 0)}))))
      have hdisj' : ∀ h h' : Fin s, h ≠ h' → Disjoint (A' h) (A' h') := by
        intro h h' hne
        show Disjoint (Finset.univ.filter (fun i' : ι' => i'.1 ∈ A h.succ))
          (Finset.univ.filter (fun i' : ι' => i'.1 ∈ A h'.succ))
        refine Finset.disjoint_left.mpr (fun a ha hmem => ?_)
        rw [Finset.mem_filter] at ha hmem
        exact (Finset.disjoint_left.mp (hdisj h.succ h'.succ (by simpa using hne))) ha.2 hmem.2
      have hIH := ih ι' A' F' hF'meas hdisj'
      have hfac : ∀ h : Fin s,
          (∫⁻ (y : {x : ι' // x ∈ A' h} → ℝ), F' h y
              ∂(Measure.pi (fun _ : {x : ι' // x ∈ A' h} => P)))
            = ∫⁻ (y : {i : ι // i ∈ A h.succ} → ℝ), F h.succ y
                ∂(Measure.pi (fun _ : {i : ι // i ∈ A h.succ} => P)) := by
        intro h
        have hmp := MeasureTheory.measurePreserving_piCongrLeft
          (μ := fun _ : {x : ι' // x ∈ A' h} => P) (e h)
        have h1 := MeasureTheory.MeasurePreserving.lintegral_map_equiv (F' h)
          (MeasurableEquiv.piCongrLeft (fun _ : {x : ι' // x ∈ A' h} => ℝ) (e h)) hmp
        rw [h1]
        apply MeasureTheory.lintegral_congr
        intro x
        show F h.succ (fun i : {i : ι // i ∈ A h.succ} =>
            (MeasurableEquiv.piCongrLeft (fun _ : {x : ι' // x ∈ A' h} => ℝ) (e h)) x (e h i))
          = F h.succ x
        have hfun : (fun i : {i : ι // i ∈ A h.succ} =>
            (MeasurableEquiv.piCongrLeft (fun _ : {x : ι' // x ∈ A' h} => ℝ) (e h)) x (e h i)) = x := by
          funext i
          exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℝ) (e h) x i
        rw [hfun]
      have hg_eq : (∫⁻ (v : {i : ι // ¬ (i ∈ A 0)} → ℝ), g v
            ∂(Measure.pi (fun _ : {i : ι // ¬ (i ∈ A 0)} => P)))
          = ∏ h : Fin s, ∫⁻ (y : {i : ι // i ∈ A h.succ} → ℝ), F h.succ y
              ∂(Measure.pi (fun _ : {i : ι // i ∈ A h.succ} => P)) := by
        calc ∫⁻ (v : {i : ι // ¬ (i ∈ A 0)} → ℝ), g v
              ∂(Measure.pi (fun _ : {i : ι // ¬ (i ∈ A 0)} => P))
            = ∫⁻ (v : ι' → ℝ), (∏ h : Fin s, F' h (fun i => v i.1))
                ∂(Measure.pi (fun _ : ι' => P)) := by
              apply MeasureTheory.lintegral_congr
              intro v
              rfl
          _ = ∏ h : Fin s, ∫⁻ (y : {x : ι' // x ∈ A' h} → ℝ), F' h y
                ∂(Measure.pi (fun _ : {x : ι' // x ∈ A' h} => P)) := hIH
          _ = ∏ h : Fin s, ∫⁻ (y : {i : ι // i ∈ A h.succ} → ℝ), F h.succ y
                ∂(Measure.pi (fun _ : {i : ι // i ∈ A h.succ} => P)) := by
              simp only [hfac]
      have hprod : (∏ h : Fin (s + 1), ∫⁻ (y : {i : ι // i ∈ A h} → ℝ), F h y
            ∂(Measure.pi (fun _ : {i : ι // i ∈ A h} => P)))
          = (∫⁻ (u : {i : ι // i ∈ A 0} → ℝ), F 0 u
              ∂(Measure.pi (fun _ : {i : ι // i ∈ A 0} => P)))
            * ∏ h : Fin s, ∫⁻ (y : {i : ι // i ∈ A h.succ} → ℝ), F h.succ y
                ∂(Measure.pi (fun _ : {i : ι // i ∈ A h.succ} => P)) := by
        rw [Fin.prod_univ_succ]
      calc ∫⁻ (X : ι → ℝ), ∏ h : Fin (s + 1), F h (fun i => X i.1)
            ∂(Measure.pi (fun _ : ι => P))
          = ∫⁻ (X : ι → ℝ), F 0 (fun i => X i.1) * (∏ h : Fin s, F h.succ (fun i => X i.1))
              ∂(Measure.pi (fun _ : ι => P)) := by
            apply MeasureTheory.lintegral_congr
            intro X
            rw [Fin.prod_univ_succ]
        _ = ∫⁻ (X : ι → ℝ), F 0 (fun i => X i.1) * g (fun i : {i : ι // ¬ (i ∈ A 0)} => X i.1)
              ∂(Measure.pi (fun _ : ι => P)) := by
            apply MeasureTheory.lintegral_congr
            intro X
            rw [show g (fun i : {i : ι // ¬ (i ∈ A 0)} => X i.1)
                = ∏ h : Fin s, F h.succ (fun i => X i.1) from rfl]
        _ = (∫⁻ (u : {i : ι // i ∈ A 0} → ℝ), F 0 u
              ∂(Measure.pi (fun _ : {i : ι // i ∈ A 0} => P)))
            * ∫⁻ (v : {i : ι // ¬ (i ∈ A 0)} → ℝ), g v
                ∂(Measure.pi (fun _ : {i : ι // ¬ (i ∈ A 0)} => P)) :=
            split ι (A 0) (F 0) g (hF 0) hg_meas
        _ = (∫⁻ (u : {i : ι // i ∈ A 0} → ℝ), F 0 u
              ∂(Measure.pi (fun _ : {i : ι // i ∈ A 0} => P)))
            * ∏ h : Fin s, ∫⁻ (y : {i : ι // i ∈ A h.succ} → ℝ), F h.succ y
                ∂(Measure.pi (fun _ : {i : ι // i ∈ A h.succ} => P)) := by
            rw [hg_eq]
        _ = ∏ h : Fin (s + 1), ∫⁻ (y : {i : ι // i ∈ A h} → ℝ), F h y
              ∂(Measure.pi (fun _ : {i : ι // i ∈ A h} => P)) := by
            rw [hprod]
  exact main s (Fin n) A F hF hdisj
  /- @proof-region region.target-node.session.856fb91f25575fef end -/

end Statlib.Imported
