import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M000_Vocabulary
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M001_Base

/- Original module ProverJobs.job_paper_dc88427b52844263b5321fc99eb582d8.ProvedNodes.Node_2588147038_c72f539f_bf0a8a81; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported

open Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_2588147038_c72f539f : ∀ (n k : ℕ) (w : Finset (Fin n) → ℝ),
    (∑ f ∈ (Finset.univ : Finset (Fin k → Finset (Fin n))).filter (fun f =>
        (∀ i : Fin k, (f i).Nonempty) ∧
        (∀ i : Fin k, f i ⊆ (Finset.univ : Finset (Fin n))) ∧
        (∀ i : Fin k, ∀ i' : Fin k, i ≠ i' → Disjoint (f i) (f i')) ∧
        (∀ x ∈ (Finset.univ : Finset (Fin n)), ∃ i : Fin k, x ∈ f i)),
      ∏ i : Fin k, w (f i))
      = (k.factorial : ℝ) * (∑ A ∈ dpTau n k, ∏ B ∈ A, w B) := by
  /- @proof-region region.target-node.session.4473a9a92c549e86 begin -/
  intro n k w
  classical
  set P : (Fin k → Finset (Fin n)) → Prop := fun f =>
      (∀ i : Fin k, (f i).Nonempty) ∧
      (∀ i : Fin k, f i ⊆ (Finset.univ : Finset (Fin n))) ∧
      (∀ i : Fin k, ∀ i' : Fin k, i ≠ i' → Disjoint (f i) (f i')) ∧
      (∀ x ∈ (Finset.univ : Finset (Fin n)), ∃ i : Fin k, x ∈ f i) with hP
  set T : Finset (Fin k → Finset (Fin n)) :=
    (Finset.univ : Finset (Fin k → Finset (Fin n))).filter P with hT
  have hPT : ∀ f : Fin k → Finset (Fin n), f ∈ T ↔ P f := by
    intro f
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
  have hinj : ∀ f : Fin k → Finset (Fin n), P f → Function.Injective f := by
    intro f hf i i' hii
    by_contra hne
    obtain ⟨x, hx⟩ := hf.1 i
    exact (Finset.disjoint_left.mp (hf.2.2.1 i i' hne) hx) (hii ▸ hx)
  have himgcard : ∀ f : Fin k → Finset (Fin n), P f → (Finset.univ.image f).card = k := by
    intro f hf
    rw [Finset.card_image_of_injective (f := f) Finset.univ (hinj f hf)]
    simp
  have hmaps : ∀ f ∈ T, (Finset.univ.image f) ∈ dpTau n k := by
    intro f hfT
    have hf : P f := (hPT f).mp hfT
    simp only [dpTau, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨himgcard f hf, ?_, ?_, ?_⟩
    · intro B hB
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hB
      rw [← hi]
      exact hf.1 i
    · intro B hB B' hB' hne
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hB
      obtain ⟨i', -, hi'⟩ := Finset.mem_image.mp hB'
      rw [← hi, ← hi'] at hne ⊢
      exact hf.2.2.1 i i' (fun h => hne (by rw [h]))
    · intro x
      obtain ⟨i, hi⟩ := hf.2.2.2 x (Finset.mem_univ x)
      exact ⟨f i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, hi⟩
  have hfiber : ∀ A ∈ dpTau n k,
      (T.filter (fun f => Finset.univ.image f = A)).card = k.factorial := by
    intro A hA
    have hAparts : dpIsPartition A k := by
      simpa only [dpTau, Finset.mem_filter, Finset.mem_univ, true_and] using hA
    obtain ⟨hAcard, hAne, hAdisj, hAcov⟩ := hAparts
    let ψ : (Fin k ≃ ↥A) → (Fin k → Finset (Fin n)) := fun e i => (e i).val
    have hψinj : Function.Injective ψ := by
      intro e1 e2 he
      apply Equiv.ext
      intro i
      exact Subtype.ext (congrFun he i)
    have hψmem : ∀ e, ψ e ∈ T.filter (fun f => Finset.univ.image f = A) := by
      intro e
      rw [Finset.mem_filter]
      refine ⟨(hPT (ψ e)).mpr ⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · intro i
        exact hAne (e i).val (e i).2
      · intro i x _
        exact Finset.mem_univ x
      · intro i i' hii
        have hene : (e i).val ≠ (e i').val := by
          intro h
          exact hii (e.injective (Subtype.ext h))
        exact hAdisj (e i).val (e i).2 (e i').val (e i').2 hene
      · intro x _
        obtain ⟨B, hB, hxB⟩ := hAcov x
        refine ⟨e.symm ⟨B, hB⟩, ?_⟩
        have h1 : e (e.symm ⟨B, hB⟩) = ⟨B, hB⟩ := e.apply_symm_apply ⟨B, hB⟩
        show x ∈ (e (e.symm ⟨B, hB⟩)).val
        rw [h1]
        exact hxB
      · apply Finset.ext
        intro B
        simp only [Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨i, hi⟩
          exact hi ▸ (e i).2
        · intro hB
          refine ⟨e.symm ⟨B, hB⟩, ?_⟩
          have h1 : e (e.symm ⟨B, hB⟩) = ⟨B, hB⟩ := e.apply_symm_apply ⟨B, hB⟩
          show (e (e.symm ⟨B, hB⟩)).val = B
          rw [h1]
    have hψrange : Finset.univ.image ψ = T.filter (fun f => Finset.univ.image f = A) := by
      apply Finset.ext
      intro f
      constructor
      · intro hf
        obtain ⟨e, -, hfe⟩ := Finset.mem_image.mp hf
        rw [← hfe]
        exact hψmem e
      · intro hf
        rw [Finset.mem_filter] at hf
        obtain ⟨hfT, hfA⟩ := hf
        have hfP : P f := (hPT f).mp hfT
        rw [Finset.mem_image]
        have hmem : ∀ i : Fin k, f i ∈ A := by
          intro i
          rw [← hfA]
          exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
        refine ⟨Equiv.ofBijective (fun i : Fin k => (⟨f i, hmem i⟩ : ↥A)) ?_,
          Finset.mem_univ _, ?_⟩
        · constructor
          · intro i i' hii
            exact hinj f hfP (congrArg Subtype.val hii)
          · intro a
            have ha' : (a : Finset (Fin n)) ∈ Finset.image f Finset.univ := by
              rw [hfA]
              exact a.2
            rw [Finset.mem_image] at ha'
            obtain ⟨i, -, hi⟩ := ha'
            exact ⟨i, Subtype.ext hi⟩
        · funext i
          rfl
    have hcardψ : (Finset.univ.image ψ).card = k.factorial := by
      rw [Finset.card_image_of_injective (f := ψ) Finset.univ hψinj]
      rw [Finset.card_univ]
      rw [Fintype.card_equiv (Finset.equivFinOfCardEq hAcard).symm]
      rw [Fintype.card_fin]
    rw [← hψrange, hcardψ]
  have hprod : ∀ f : Fin k → Finset (Fin n), P f →
      (∏ i : Fin k, w (f i)) = ∏ B ∈ (Finset.univ.image f), w B := by
    intro f hf
    rw [Finset.prod_image (s := Finset.univ) (g := f) (f := w)
      (fun x _ y _ hxy => hinj f hf hxy)]
  have hstep1 : (∑ f ∈ T, ∏ i : Fin k, w (f i))
      = ∑ f ∈ T, ∏ B ∈ (Finset.univ.image f), w B := by
    apply Finset.sum_congr rfl
    intro f hf
    exact hprod f ((hPT f).mp hf)
  have hstep2 : (∑ f ∈ T, ∏ B ∈ (Finset.univ.image f), w B)
      = ∑ A ∈ dpTau n k,
          ∑ f ∈ T.filter (fun f => Finset.univ.image f = A), ∏ B ∈ A, w B := by
    have hfib := Finset.sum_fiberwise_of_maps_to (s := T) (t := dpTau n k)
      (g := fun f : Fin k → Finset (Fin n) => Finset.univ.image f) hmaps
      (fun f : Fin k → Finset (Fin n) => ∏ B ∈ (Finset.univ.image f), w B)
    rw [← hfib]
    apply Finset.sum_congr rfl
    intro A hA
    apply Finset.sum_congr rfl
    intro f hf
    rw [Finset.mem_filter] at hf
    rw [hf.2]
  have hstep3 : (∑ A ∈ dpTau n k,
        ∑ f ∈ T.filter (fun f => Finset.univ.image f = A), ∏ B ∈ A, w B)
      = ∑ A ∈ dpTau n k, (k.factorial : ℝ) * ∏ B ∈ A, w B := by
    apply Finset.sum_congr rfl
    intro A hA
    rw [Finset.sum_const, hfiber A hA, nsmul_eq_mul]
  have hstep4 : (∑ A ∈ dpTau n k, (k.factorial : ℝ) * ∏ B ∈ A, w B)
      = (k.factorial : ℝ) * ∑ A ∈ dpTau n k, ∏ B ∈ A, w B := by
    rw [Finset.mul_sum]
  rw [hstep1, hstep2, hstep3, hstep4]
  /- @proof-region region.target-node.session.4473a9a92c549e86 end -/

end

end Statlib.Imported
end DPCompletedProof
