import ProverJobs.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Vocabulary
import ProverJobs.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Base

namespace PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed

open _root_.PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
universe u₀ u₁

set_option autoImplicit false in
theorem statopia_math_node_542235460_c14e1d61 : ∀ (p : ℕ) (W : Submodule ℝ (Fin p → ℝ)),
    ∃ Q : Matrix (Fin p) (Fin (Module.finrank ℝ W)) ℝ,
      Matrix.transpose Q * Q = 1 ∧
        Submodule.span ℝ
          (Set.range (fun j : Fin (Module.finrank ℝ W) => (fun m : Fin p => Q m j))) = W := by
  /- @proof-region region.target-node.session.ed8feda4e5c21796 begin -/
  intro p W
  classical
  let L : EuclideanSpace ℝ (Fin p) ≃ₗ[ℝ] (Fin p → ℝ) := WithLp.linearEquiv 2 ℝ (Fin p → ℝ)
  let W' : Submodule ℝ (EuclideanSpace ℝ (Fin p)) := W.comap L.toLinearMap
  have hmem : ∀ x : EuclideanSpace ℝ (Fin p), (x ∈ W' ↔ L x ∈ W) := by
    intro x
    simp [W', Submodule.mem_comap]
  have e : ↥W ≃ₗ[ℝ] ↥W' :=
    { toFun := fun x => ⟨L.symm x.1, by
        rw [hmem, LinearEquiv.apply_symm_apply]
        exact x.2⟩
      invFun := fun y => ⟨L y.1, (hmem y.1).mpr y.2⟩
      left_inv := by
        intro x
        apply Subtype.ext
        exact LinearEquiv.apply_symm_apply L x.1
      right_inv := by
        intro y
        apply Subtype.ext
        exact LinearEquiv.symm_apply_apply L y.1
      map_add' := by
        intro a b
        ext
        simp
      map_smul' := by
        intro a b
        ext
        simp }
  have hfin : Module.finrank ℝ W' = Module.finrank ℝ W := (LinearEquiv.finrank_eq e).symm
  have hfdall : ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin p)), FiniteDimensional ℝ ↥V :=
    fun V => inferInstance
  haveI hfd : FiniteDimensional ℝ ↥W' := hfdall W'
  let jj : Fin (Module.finrank ℝ W) ≃ Fin (Module.finrank ℝ W') := finCongr hfin.symm
  let bs : OrthonormalBasis (Fin (Module.finrank ℝ W')) ℝ ↥W' :=
    @stdOrthonormalBasis ℝ _ ↥W' _ _ hfd
  refine ⟨fun m j => (bs (jj j) : EuclideanSpace ℝ (Fin p)).ofLp m, ?_, ?_⟩
  · ext j j'
    show (∑ m, (bs (jj j) : EuclideanSpace ℝ (Fin p)).ofLp m *
        (bs (jj j') : EuclideanSpace ℝ (Fin p)).ofLp m) = if j = j' then 1 else 0
    have hinner : ∀ (x y : EuclideanSpace ℝ (Fin p)),
        inner ℝ x y = ∑ m, x.ofLp m * y.ofLp m := by
      intro x y
      rw [PiLp.inner_apply]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      simp [RCLike.inner_apply, mul_comm]
    have hint := (orthonormal_iff_ite.mp bs.orthonormal) (jj j) (jj j')
    have hcoe : inner ℝ ((bs (jj j) : EuclideanSpace ℝ (Fin p))) ((bs (jj j') : EuclideanSpace ℝ (Fin p))) =
        inner ℝ (bs (jj j)) (bs (jj j')) := (Submodule.coe_inner W' (bs (jj j)) (bs (jj j'))).symm
    have key : (∑ m, (bs (jj j) : EuclideanSpace ℝ (Fin p)).ofLp m *
          (bs (jj j') : EuclideanSpace ℝ (Fin p)).ofLp m) =
        inner ℝ (bs (jj j)) (bs (jj j')) := by
      rw [← hcoe, hinner]
    rw [key, hint]
    by_cases h : j = j'
    · subst h
      simp
    · have h2 : ¬ (jj j = jj j') := fun hh => h (jj.injective hh)
      simp [h, h2]
  · have hspan1 : Submodule.span ℝ
        (Set.range (fun i : Fin (Module.finrank ℝ W') => (bs i : EuclideanSpace ℝ (Fin p)))) = W' := by
      have h1 : Submodule.span ℝ (Set.range (fun i : Fin (Module.finrank ℝ W') => bs i)) = ⊤ := by
        have hb : Submodule.span ℝ
            (Set.range (fun i : Fin (Module.finrank ℝ W') => bs.toBasis i)) = ⊤ :=
          Module.Basis.span_eq bs.toBasis
        have hcoe : (fun i : Fin (Module.finrank ℝ W') => bs.toBasis i) = (fun i => bs i) :=
          funext fun i => congrFun (OrthonormalBasis.coe_toBasis bs) i
        rw [hcoe] at hb
        exact hb
      have h3 : Submodule.map (Submodule.subtype W') ⊤ = Submodule.span ℝ
          (Set.range (fun i : Fin (Module.finrank ℝ W') => (bs i : EuclideanSpace ℝ (Fin p)))) := by
        rw [← h1, Submodule.map_span]
        congr 1
        rw [← Set.range_comp]
        rfl
      rw [← h3, Submodule.map_top, Submodule.range_subtype]
    have hmap : Submodule.map L.toLinearMap (Submodule.span ℝ
        (Set.range (fun i : Fin (Module.finrank ℝ W') => (bs i : EuclideanSpace ℝ (Fin p))))) = W := by
      rw [hspan1]
      refine le_antisymm ?_ ?_
      · rintro y ⟨x, hx, rfl⟩
        exact (hmem x).mp hx
      · intro w hw
        refine ⟨L.symm w, ?_, ?_⟩
        · change L.symm w ∈ W'
          rw [hmem, LinearEquiv.apply_symm_apply]
          exact hw
        · exact LinearEquiv.apply_symm_apply L w
    have hLrange : Submodule.span ℝ
        (Set.range (fun i : Fin (Module.finrank ℝ W') =>
          (bs i : EuclideanSpace ℝ (Fin p)).ofLp)) = W := by
      have h1 : Submodule.map L.toLinearMap (Submodule.span ℝ
          (Set.range (fun i : Fin (Module.finrank ℝ W') =>
            (bs i : EuclideanSpace ℝ (Fin p))))) = Submodule.span ℝ
          (Set.range (fun i : Fin (Module.finrank ℝ W') =>
            (bs i : EuclideanSpace ℝ (Fin p)).ofLp)) := by
        rw [Submodule.map_span]
        congr 1
        rw [← Set.range_comp]
        rfl
      rw [← h1, hmap]
    have hrange_jj : Set.range (fun j : Fin (Module.finrank ℝ W) =>
          (bs (jj j) : EuclideanSpace ℝ (Fin p)).ofLp) =
        Set.range (fun i : Fin (Module.finrank ℝ W') =>
          (bs i : EuclideanSpace ℝ (Fin p)).ofLp) := by
      ext x
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨jj j, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨jj.symm i, by simp⟩
    rw [show (fun j : Fin (Module.finrank ℝ W) =>
        (fun m : Fin p => (bs (jj j) : EuclideanSpace ℝ (Fin p)).ofLp m)) =
        (fun j => (bs (jj j) : EuclideanSpace ℝ (Fin p)).ofLp) from rfl]
    rw [hrange_jj, hLrange]
  /- @proof-region region.target-node.session.ed8feda4e5c21796 end -/

end
end Statlib.Imported

