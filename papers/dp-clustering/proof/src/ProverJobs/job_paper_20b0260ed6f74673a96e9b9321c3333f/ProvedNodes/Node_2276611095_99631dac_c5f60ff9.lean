import ProverJobs.job_paper_20b0260ed6f74673a96e9b9321c3333f.Vocabulary
import ProverJobs.job_paper_20b0260ed6f74673a96e9b9321c3333f.Base
import ProverJobs.job_paper_20b0260ed6f74673a96e9b9321c3333f.ProvedNodes.Node_2866290612_0c13d721_4eae36fe

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_2276611095_99631dac : ∀ (n s : ℕ) (a : Fin s → Fin (n + 1))
    (ha : a ∈ orderedCompositions n s) (f : Fin s → Finset (Fin n))
    (hne : ∀ j : Fin s, (f j).Nonempty)
    (hdisj : ∀ j k : Fin s, j ≠ k → Disjoint (f j) (f k))
    (hcover : ∀ i : Fin n, ∃ j : Fin s, i ∈ f j)
    (hcard : ∀ j : Fin s, (f j).card = (a j).val),
    ∃ σ : Equiv.Perm (Fin n), ∀ j : Fin s, f j = Finset.image σ (canonBlock n s a j) := by
  /- @proof-region region.target-node.session.58524cbb7652d447 begin -/
  intro n s a ha f hne hdisj hcov hcard
  obtain ⟨_, hCcard, hCdisj, hCcov, _⟩ :=
    statopia_math_node_2866290612_0c13d721 n s a ha
  let C : Fin s → Finset (Fin n) := fun j => canonBlock n s a j
  have hCcard' : ∀ j : Fin s, (C j).card = (a j).val := fun j => hCcard j
  have hcardC : ∀ j : Fin s, Fintype.card ↥(C j) = Fintype.card ↥(f j) := by
    intro j
    rw [Fintype.card_coe, Fintype.card_coe, hCcard' j, hcard j]
  let e : ∀ j : Fin s, ↥(C j) ≃ ↥(f j) := fun j => Fintype.equivOfCardEq (hcardC j)
  let φC : (Σ j : Fin s, ↥(C j)) → Fin n := fun p => p.2.val
  let φf : (Σ j : Fin s, ↥(f j)) → Fin n := fun p => p.2.val
  have hφC_inj : Function.Injective φC := by
    intro p q hpq
    obtain ⟨j, ⟨x, hx⟩⟩ := p
    obtain ⟨k, ⟨y, hy⟩⟩ := q
    change x = y at hpq
    have hy' : x ∈ C k := by rw [hpq]; exact hy
    have hjk : j = k := by
      by_contra hne'
      exact (Finset.disjoint_left.mp (hCdisj j k hne')) hx hy'
    subst hjk
    subst hpq
    rfl
  have hφC_surj : Function.Surjective φC := by
    intro i
    obtain ⟨j, hi⟩ := hCcov i
    exact ⟨⟨j, ⟨i, hi⟩⟩, rfl⟩
  have hφf_inj : Function.Injective φf := by
    intro p q hpq
    obtain ⟨j, ⟨x, hx⟩⟩ := p
    obtain ⟨k, ⟨y, hy⟩⟩ := q
    change x = y at hpq
    have hy' : x ∈ f k := by rw [hpq]; exact hy
    have hjk : j = k := by
      by_contra hne'
      exact (Finset.disjoint_left.mp (hdisj j k hne')) hx hy'
    subst hjk
    subst hpq
    rfl
  have hφf_surj : Function.Surjective φf := by
    intro i
    obtain ⟨j, hi⟩ := hcov i
    exact ⟨⟨j, ⟨i, hi⟩⟩, rfl⟩
  let ΦC : (Σ j : Fin s, ↥(C j)) ≃ Fin n := Equiv.ofBijective φC ⟨hφC_inj, hφC_surj⟩
  let Φf : (Σ j : Fin s, ↥(f j)) ≃ Fin n := Equiv.ofBijective φf ⟨hφf_inj, hφf_surj⟩
  let E : (Σ j : Fin s, ↥(C j)) ≃ (Σ j : Fin s, ↥(f j)) :=
    { toFun := fun p => ⟨p.1, e p.1 p.2⟩
      invFun := fun p => ⟨p.1, (e p.1).symm p.2⟩
      left_inv := by
        rintro ⟨j, x⟩
        simp only [Equiv.symm_apply_apply]
      right_inv := by
        rintro ⟨j, y⟩
        simp only [Equiv.apply_symm_apply] }
  let σ : Equiv.Perm (Fin n) := ΦC.symm.trans (E.trans Φf)
  have hσ_apply : ∀ (j : Fin s) (i : Fin n) (hi : i ∈ C j),
      σ i = ((e j) ⟨i, hi⟩).val := by
    intro j i hi
    have hpinv : ΦC.symm i = ⟨j, ⟨i, hi⟩⟩ := by
      apply ΦC.injective
      rw [Equiv.apply_symm_apply]
      rfl
    show Φf (E (ΦC.symm i)) = ((e j) ⟨i, hi⟩).val
    rw [hpinv]
    rfl
  refine ⟨σ, ?_⟩
  intro j
  have hFin : (C j).image σ = f j := by
    apply Finset.ext
    intro y
    constructor
    · intro hy
      rw [Finset.mem_image] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [hσ_apply j x hx]
      exact ((e j) ⟨x, hx⟩).property
    · intro hy
      refine Finset.mem_image.mpr
        ⟨((e j).symm ⟨y, hy⟩).val, ((e j).symm ⟨y, hy⟩).property, ?_⟩
      rw [hσ_apply j ((e j).symm ⟨y, hy⟩).val ((e j).symm ⟨y, hy⟩).property]
      have hw : (⟨((e j).symm ⟨y, hy⟩).val, ((e j).symm ⟨y, hy⟩).property⟩ : ↥(C j))
          = (e j).symm ⟨y, hy⟩ := Subtype.ext rfl
      rw [hw, Equiv.apply_symm_apply]
  rw [← hFin]
  all_goals rw [Finset.coe_image]
  /- @proof-region region.target-node.session.58524cbb7652d447 end -/

end Statlib.Imported
