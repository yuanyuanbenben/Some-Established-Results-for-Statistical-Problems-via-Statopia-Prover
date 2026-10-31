import ProverJobs.job_paper_20b0260ed6f74673a96e9b9321c3333f.Vocabulary
import ProverJobs.job_paper_20b0260ed6f74673a96e9b9321c3333f.Base

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_642534324_01784987 : ∀ (n s : ℕ) (hs : 1 ≤ s) (c Psi : Finset (Fin n) → ℝ),
    (∑ P ∈ partitionsInto n s, (∏ B ∈ P, c B) * (∏ B ∈ P, Psi B))
      = (1 / ((Nat.factorial s : ℕ) : ℝ)) *
        (∑ f ∈ ((by
            classical
            exact Finset.univ.filter (fun f : Fin s → Finset (Fin n) =>
              (∀ j : Fin s, (f j).Nonempty) ∧
              (∀ j k : Fin s, j ≠ k → Disjoint (f j) (f k)) ∧
              Finset.univ.sup f = Finset.univ)) : Finset (Fin s → Finset (Fin n))),
          (∏ j : Fin s, c (f j)) * (∏ j : Fin s, Psi (f j))) := by
  /- @proof-region region.target-node.session.76d2b7238ca4fc9f begin -/
  intro n s hs c Psi
  classical
  dsimp only
  set O : Finset (Fin s → Finset (Fin n)) :=
    (Finset.univ : Finset (Fin s → Finset (Fin n))).filter
      (fun f => (∀ j : Fin s, (f j).Nonempty) ∧
        (∀ j k : Fin s, j ≠ k → Disjoint (f j) (f k)) ∧
        (∀ i : Fin n, ∃ j : Fin s, i ∈ f j)) with hO
  have hO_mem : ∀ f : Fin s → Finset (Fin n), f ∈ O ↔
      (∀ j : Fin s, (f j).Nonempty) ∧
        (∀ j k : Fin s, j ≠ k → Disjoint (f j) (f k)) ∧
        (∀ i : Fin n, ∃ j : Fin s, i ∈ f j) := by
    intro f
    rw [hO]
    simp
  have hP_mem : ∀ P : Finset (Finset (Fin n)), P ∈ partitionsInto n s ↔
      P.card = s ∧ (∀ B ∈ P, B.Nonempty) ∧ P.sup id = Finset.univ ∧
        (∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C) := by
    intro P
    simp [partitionsInto]
  have hinj : ∀ f : Fin s → Finset (Fin n), f ∈ O → Function.Injective f := by
    intro f hf j k hjk
    by_contra hne
    obtain ⟨hne', hdisj, _⟩ := (hO_mem f).mp hf
    obtain ⟨i, hi⟩ := hne' j
    exact (Finset.disjoint_left.mp (hdisj j k hne) hi) (hjk ▸ hi)
  have hcard_img : ∀ (f : Fin s → Finset (Fin n)), f ∈ O → (Finset.univ.image f).card = s := by
    intro f hf
    rw [Finset.card_image_of_injective (Finset.univ : Finset (Fin s)) (hinj f hf)]
    simp
  have hsup_img : ∀ (f : Fin s → Finset (Fin n)), f ∈ O → (Finset.univ.image f).sup id = Finset.univ := by
    intro f hf
    obtain ⟨-, -, hcov⟩ := (hO_mem f).mp hf
    rw [Finset.sup_image]
    ext i
    rw [Finset.mem_sup]
    constructor
    · intro _
      exact Finset.mem_univ i
    · intro _
      obtain ⟨j, hj⟩ := hcov i
      exact ⟨j, Finset.mem_univ j, hj⟩
  have himg_mem : ∀ (f : Fin s → Finset (Fin n)), f ∈ O → Finset.univ.image f ∈ partitionsInto n s := by
    intro f hf
    rw [hP_mem]
    refine ⟨hcard_img f hf, ?_, hsup_img f hf, ?_⟩
    · intro B hB
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hB
      exact ((hO_mem f).mp hf).1 j
    · intro B hB C hC hBC
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hB
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hC
      exact ((hO_mem f).mp hf).2.1 j k (fun h => hBC (by rw [h]))
  have hprod_c : ∀ (f : Fin s → Finset (Fin n)), f ∈ O →
      (∏ j : Fin s, c (f j)) = ∏ B ∈ Finset.univ.image f, c B := by
    intro f hf
    exact (Finset.prod_image (fun x _ y _ hxy => hinj f hf hxy)).symm
  have hprod_psi : ∀ (f : Fin s → Finset (Fin n)), f ∈ O →
      (∏ j : Fin s, Psi (f j)) = ∏ B ∈ Finset.univ.image f, Psi B := by
    intro f hf
    exact (Finset.prod_image (fun x _ y _ hxy => hinj f hf hxy)).symm
  have hfiber_card : ∀ P : Finset (Finset (Fin n)), P ∈ partitionsInto n s →
      (O.filter (fun f => Finset.univ.image f = P)).card = Nat.factorial s := by
    intro P hP
    obtain ⟨hPc, hPne, hPsup, hPdisj⟩ := (hP_mem P).mp hP
    let e0 : ↥P ≃ Fin s := Finset.equivFinOfCardEq hPc
    have hmem : ∀ (f : Fin s → Finset (Fin n)), Finset.univ.image f = P → ∀ j : Fin s, f j ∈ P := by
      intro f hf j
      rw [← hf]
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
    let toPerm : ↥(O.filter (fun f => Finset.univ.image f = P)) → Equiv.Perm (Fin s) := fun f =>
      Equiv.ofBijective
        (fun j : Fin s => e0 ⟨f.1 j, hmem f.1 (Finset.mem_filter.mp f.2).2 j⟩)
        (by
          constructor
          · intro j k hjk
            have h2 : (⟨f.1 j, hmem f.1 (Finset.mem_filter.mp f.2).2 j⟩ : ↥P)
                = ⟨f.1 k, hmem f.1 (Finset.mem_filter.mp f.2).2 k⟩ := e0.injective hjk
            exact hinj f.1 (Finset.mem_filter.mp f.2).1 (congrArg Subtype.val h2)
          · intro k
            have hk : (e0.symm k).val ∈ Finset.univ.image f.1 := by
              rw [(Finset.mem_filter.mp f.2).2]
              exact (e0.symm k).prop
            obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hk
            refine ⟨j, ?_⟩
            have h3 : (⟨f.1 j, hmem f.1 (Finset.mem_filter.mp f.2).2 j⟩ : ↥P) = e0.symm k :=
              Subtype.ext hj
            show e0 ⟨f.1 j, hmem f.1 (Finset.mem_filter.mp f.2).2 j⟩ = k
            rw [h3, Equiv.apply_symm_apply])
    have htoPerm_apply : ∀ (f : ↥(O.filter (fun f => Finset.univ.image f = P))) (j : Fin s),
        toPerm f j = e0 ⟨f.1 j, hmem f.1 (Finset.mem_filter.mp f.2).2 j⟩ := fun f j => rfl
    let fromPerm : Equiv.Perm (Fin s) → ↥(O.filter (fun f => Finset.univ.image f = P)) := fun σ =>
      ⟨fun j => (e0.symm (σ j)).val, by
        rw [Finset.mem_filter]
        refine ⟨(hO_mem _).mpr ⟨?_, ?_, ?_⟩, ?_⟩
        · intro j
          exact hPne _ (e0.symm (σ j)).prop
        · intro j k hne
          exact hPdisj _ (e0.symm (σ j)).prop _ (e0.symm (σ k)).prop
            (fun h => hne (σ.injective (e0.symm.injective (Subtype.ext h))))
        · intro i
          have hi : i ∈ P.sup id := by
            rw [hPsup]
            exact Finset.mem_univ i
          obtain ⟨B, hB, hiB⟩ := Finset.mem_sup.mp hi
          obtain ⟨j, hj⟩ := σ.surjective (e0 ⟨B, hB⟩)
          refine ⟨j, ?_⟩
          have h3 : e0.symm (σ j) = (⟨B, hB⟩ : ↥P) := by rw [hj, Equiv.symm_apply_apply]
          rw [h3]
          exact hiB
        · ext B
          constructor
          · intro hB
            obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hB
            exact (e0.symm (σ j)).prop
          · intro hB
            obtain ⟨j, hj⟩ := σ.surjective (e0 ⟨B, hB⟩)
            refine Finset.mem_image.mpr ⟨j, Finset.mem_univ j, ?_⟩
            rw [hj, Equiv.symm_apply_apply]⟩
    have htoPerm_inj : Function.Injective toPerm := by
      intro f f' h
      have h1 : f.1 = f'.1 := by
        funext j
        have h2 : toPerm f j = toPerm f' j := congrArg (fun e : Equiv.Perm (Fin s) => e j) h
        rw [htoPerm_apply, htoPerm_apply] at h2
        exact congrArg Subtype.val (e0.injective h2)
      exact Subtype.ext h1
    have hfromPerm_inj : Function.Injective fromPerm := by
      intro σ σ' h
      have h1 : (fun j => (e0.symm (σ j)).val) = (fun j => (e0.symm (σ' j)).val) :=
        congrArg Subtype.val h
      have h2 : ∀ j, σ j = σ' j := fun j => e0.symm.injective (Subtype.ext (congrFun h1 j))
      exact Equiv.ext h2
    have hle1 : Fintype.card ↥(O.filter (fun f => Finset.univ.image f = P)) ≤
        Fintype.card (Equiv.Perm (Fin s)) := Fintype.card_le_of_injective toPerm htoPerm_inj
    have hle2 : Fintype.card (Equiv.Perm (Fin s)) ≤
        Fintype.card ↥(O.filter (fun f => Finset.univ.image f = P)) :=
      Fintype.card_le_of_injective fromPerm hfromPerm_inj
    have hcard : Fintype.card ↥(O.filter (fun f => Finset.univ.image f = P)) = Nat.factorial s := by
      rw [le_antisymm hle1 hle2, Fintype.card_perm, Fintype.card_fin]
    rw [← Fintype.card_coe (O.filter (fun f => Finset.univ.image f = P)), hcard]
  have hfiber_sum : ∀ P : Finset (Finset (Fin n)), P ∈ partitionsInto n s →
      ∑ f ∈ O.filter (fun f => Finset.univ.image f = P),
          (∏ j : Fin s, c (f j)) * (∏ j : Fin s, Psi (f j))
        = ((Nat.factorial s : ℕ) : ℝ) * ((∏ B ∈ P, c B) * (∏ B ∈ P, Psi B)) := by
    intro P hP
    have hconst : ∀ f ∈ O.filter (fun f => Finset.univ.image f = P),
        (∏ j : Fin s, c (f j)) * (∏ j : Fin s, Psi (f j))
          = (∏ B ∈ P, c B) * (∏ B ∈ P, Psi B) := by
      intro f hf
      obtain ⟨hfO, hfP⟩ := Finset.mem_filter.mp hf
      rw [hprod_c f hfO, hprod_psi f hfO, hfP]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, hfiber_card P hP, nsmul_eq_mul]
  have hkey : (∑ f ∈ O, (∏ j : Fin s, c (f j)) * (∏ j : Fin s, Psi (f j)))
      = ((Nat.factorial s : ℕ) : ℝ) *
        (∑ P ∈ partitionsInto n s, (∏ B ∈ P, c B) * (∏ B ∈ P, Psi B)) := by
    have hfib := Finset.sum_fiberwise_of_maps_to himg_mem
      (fun f => (∏ j : Fin s, c (f j)) * (∏ j : Fin s, Psi (f j)))
    rw [← hfib]
    rw [Finset.sum_congr rfl (fun P hP => hfiber_sum P hP), Finset.mul_sum]
  have hsup_iff : ∀ f : Fin s → Finset (Fin n),
      (Finset.univ.sup f = Finset.univ ↔ ∀ i : Fin n, ∃ j : Fin s, i ∈ f j) := by
    intro f
    constructor
    · intro h i
      have hi : i ∈ (Finset.univ : Finset (Fin s)).sup f := by
        rw [h]
        exact Finset.mem_univ i
      obtain ⟨j, -, hj⟩ := Finset.mem_sup.mp hi
      exact ⟨j, hj⟩
    · intro h
      ext i
      rw [Finset.mem_sup]
      constructor
      · intro _
        exact Finset.mem_univ i
      · intro _
        obtain ⟨j, hj⟩ := h i
        exact ⟨j, Finset.mem_univ j, hj⟩
  have hfilter : (Finset.univ : Finset (Fin s → Finset (Fin n))).filter
      (fun f => (∀ j : Fin s, (f j).Nonempty) ∧
        (∀ j k : Fin s, j ≠ k → Disjoint (f j) (f k)) ∧
        Finset.univ.sup f = Finset.univ) = O := by
    rw [hO]
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hsup_iff f]
  rw [hfilter, hkey]
  have hfac : ((Nat.factorial s : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero s
  field_simp [hfac]
  /- @proof-region region.target-node.session.76d2b7238ca4fc9f end -/

end Statlib.Imported
