import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.Vocabulary
import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.Base

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal MeasureTheory Topology BigOperators
open Statlib.Imported
open Statlib.Imported.DPMModel

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal MeasureTheory Topology BigOperators
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_4133567021_cdc336c6 : ∀ {Θ : Type*} [TopologicalSpace Θ] [MeasurableSpace Θ] [StandardBorelSpace Θ]
    (n t : ℕ),
    MeasurableSet {ξ : ProbabilityMeasure Θ × (ℕ → Θ) |
      (Set.range (fun i : Fin n => ξ.2 (i : ℕ))).ncard < t} := by
  /- @proof-region region.target-node.session.340b9d21528898d7 begin -/
  intro Θ _ _ _ n t
  classical
  haveI hcs : MeasurableSpace.CountablySeparated Θ := inferInstance
  have hdiag : MeasurableSet {p : Θ × Θ | p.1 = p.2} := by
    obtain ⟨f, hfm, hfi⟩ := MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated Θ
    have hEq : {p : Θ × Θ | p.1 = p.2} = {p : Θ × Θ | f p.1 = f p.2} := by
      ext p
      simp only [Set.mem_setOf_eq]
      exact ⟨fun h => congrArg f h, fun h => hfi h⟩
    rw [hEq]
    exact measurableSet_eq_fun (hfm.comp measurable_fst) (hfm.comp measurable_snd)
  haveI : MeasurableEq Θ := ⟨hdiag⟩
  have hproj : ∀ k : ℕ, Measurable fun θ : ℕ → Θ => θ k := fun k => measurable_pi_apply k
  suffices h : MeasurableSet {θ : ℕ → Θ | (Set.range (fun i : Fin n => θ i)).ncard < t} by
    simpa using h.preimage measurable_snd
  have hmeas : ∀ σ : Fin n → Fin (t - 1),
      MeasurableSet {θ : ℕ → Θ | ∀ i j : Fin n, σ i = σ j → θ i = θ j} := by
    intro σ
    have hEqset : {θ : ℕ → Θ | ∀ i j : Fin n, σ i = σ j → θ i = θ j}
        = ⋂ (p : Fin n × Fin n),
            (if σ p.1 = σ p.2 then {θ : ℕ → Θ | θ p.1 = θ p.2} else Set.univ) := by
      ext θ
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro hh p
        by_cases hp : σ p.1 = σ p.2
        · simpa [hp] using hh p.1 p.2 hp
        · simp [hp]
      · intro hh i j hij
        have := hh (i, j)
        simpa [hij] using this
    rw [hEqset]
    apply MeasurableSet.iInter
    intro p
    split_ifs with hp
    · exact measurableSet_eq_fun (hproj p.1) (hproj p.2)
    · exact MeasurableSet.univ
  rcases Nat.eq_zero_or_pos t with ht | ht
  · subst ht
    have h0 : {θ : ℕ → Θ | (Set.range (fun i : Fin n => θ i)).ncard < 0} = ∅ := by
      ext θ
      simp
    rw [h0]
    exact MeasurableSet.empty
  · have hset : {θ : ℕ → Θ | (Set.range (fun i : Fin n => θ i)).ncard < t}
        = ⋃ (σ : Fin n → Fin (t - 1)), {θ : ℕ → Θ | ∀ i j : Fin n, σ i = σ j → θ i = θ j} := by
      ext θ
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · intro h
        have hcoe : (↑(Finset.univ.image (fun i : Fin n => θ i)) : Set Θ)
            = Set.range (fun i : Fin n => θ i) := by
          ext x
          simp [Set.mem_range]
        have hcard : (Finset.univ.image (fun i : Fin n => θ i)).card
            = (Set.range (fun i : Fin n => θ i)).ncard := by
          rw [← Set.ncard_coe_finset (Finset.univ.image (fun i : Fin n => θ i)), hcoe]
        have hKu : (Finset.univ.image (fun i : Fin n => θ i)).card ≤ t - 1 := by omega
        have hmem : ∀ i : Fin n, θ i ∈ Finset.univ.image (fun i : Fin n => θ i) :=
          fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
        have hlt : ∀ x : ↥(Finset.univ.image (fun i : Fin n => θ i)),
            ((Finset.equivFin (Finset.univ.image (fun i : Fin n => θ i))) x).val < t - 1 := by
          intro x
          have hx := (Finset.equivFin (Finset.univ.image (fun i : Fin n => θ i)) x).isLt
          omega
        refine ⟨fun i => ⟨((Finset.equivFin (Finset.univ.image (fun i : Fin n => θ i)))
          ⟨θ i, hmem i⟩).val, hlt ⟨θ i, hmem i⟩⟩, ?_⟩
        intro i j hij
        have hv : ((Finset.equivFin (Finset.univ.image (fun i : Fin n => θ i)))
              ⟨θ i, hmem i⟩).val
            = ((Finset.equivFin (Finset.univ.image (fun i : Fin n => θ i)))
              ⟨θ j, hmem j⟩).val :=
          congrArg (fun x : Fin (t - 1) => x.val) hij
        have he : (Finset.equivFin (Finset.univ.image (fun i : Fin n => θ i))) ⟨θ i, hmem i⟩
            = (Finset.equivFin (Finset.univ.image (fun i : Fin n => θ i))) ⟨θ j, hmem j⟩ :=
          Fin.ext hv
        exact congrArg Subtype.val
          ((Finset.equivFin (Finset.univ.image (fun i : Fin n => θ i))).injective he)
      · rintro ⟨σ, hσ⟩
        rcases Nat.eq_zero_or_pos n with hn | hn
        · subst hn
          have h0 : (Set.range (fun i : Fin 0 => θ i)) = ∅ := by
            ext x
            constructor
            · rintro ⟨i, -⟩
              exact absurd i.isLt (by omega)
            · intro hx
              exact absurd hx (by simp)
          rw [h0, Set.ncard_empty]
          exact ht
        · let g : Fin (t - 1) → Θ := fun k =>
            if h : ∃ i : Fin n, σ i = k then θ ((Classical.choose h : Fin n) : ℕ)
            else θ ((⟨0, hn⟩ : Fin n) : ℕ)
          have hgi : ∀ i : Fin n, g (σ i) = θ i := by
            intro i
            have hne : ∃ i' : Fin n, σ i' = σ i := ⟨i, rfl⟩
            show (if h : ∃ i' : Fin n, σ i' = σ i then θ ((Classical.choose h : Fin n) : ℕ)
              else θ ((⟨0, hn⟩ : Fin n) : ℕ)) = θ i
            rw [dif_pos hne]
            exact hσ (Classical.choose hne) i (Classical.choose_spec hne)
          have hsub : Set.range (fun i : Fin n => θ i) ⊆ (↑(Finset.univ.image g) : Set Θ) := by
            rintro x ⟨i, rfl⟩
            show θ i ∈ (↑(Finset.univ.image g) : Set Θ)
            rw [← hgi i]
            exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨σ i, Finset.mem_univ _, rfl⟩)
          have h1 : (Set.range (fun i : Fin n => θ i)).ncard
              ≤ (↑(Finset.univ.image g) : Set Θ).ncard :=
            Set.ncard_le_ncard hsub (Finset.finite_toSet (Finset.univ.image g))
          have h2 : (↑(Finset.univ.image g) : Set Θ).ncard = (Finset.univ.image g).card :=
            Set.ncard_coe_finset (Finset.univ.image g)
          have h3 : (Finset.univ.image g).card ≤ t - 1 := by
            have h4 : (Finset.univ.image g).card ≤ (Finset.univ : Finset (Fin (t - 1))).card :=
              Finset.card_image_le
            rw [Finset.card_univ, Fintype.card_fin] at h4
            exact h4
          omega
    rw [hset]
    exact MeasurableSet.iUnion hmeas
  /- @proof-region region.target-node.session.340b9d21528898d7 end -/

end Statlib.Imported
