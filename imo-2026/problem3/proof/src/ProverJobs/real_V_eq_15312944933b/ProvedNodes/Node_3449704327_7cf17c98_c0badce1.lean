import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_2445022674_8afd0c25_fbcfa7f9
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_4221689064_d3ddf0ec_fbe161c8
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_689319304_41a3eefa_c0bba1a5
open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_3449704327_7cf17c98 : ∀ (q : ℕ) (hq : 1 ≤ q) (a : Fin q → ℝ) (ha_pos : ∀ i, 0 < a i) (b : ℕ → ℝ)
    (hb0 : b 0 = 0) (hbq : b q = 1)
    (hbmono : StrictMonoOn b (Set.Icc 0 q))
    (hbstep : ∀ k : Fin q, b ((k : ℕ) + 1) - b (k : ℕ) = a k)
    (I J : Finset (Fin q)) (hIJ : Disjoint I J) (hne : I ∪ J ≠ ∅) (C : Finset ℝ)
    (hC1 : ∀ c ∈ C, 0 < c ∧ c < 1)
    (hC2 : ∀ c ∈ C, ∀ k : Fin (q + 1), c ≠ b (k : ℕ))
    (hC3 : ∀ c ∈ C, ∃ k ∈ I ∪ J, b (k : ℕ) < c ∧ c < b ((k : ℕ) + 1))
    (hC4 : C.card ≤ I.card + J.card - 1),
    let A : Finset ℝ :=
      (Finset.univ.filter (fun k : Fin q => 1 ≤ (k : ℕ))).image (fun k : Fin q => b (k : ℕ))
    let M : Finset ℝ :=
      (Finset.univ.filter (fun k : Fin q => k ∉ I ∪ J)).image
        (fun k : Fin q => (b (k : ℕ) + b ((k : ℕ) + 1)) / 2)
    Multiset.ofList (pieceLengths (A ∪ (C ∪ M))) =
      (∑ k ∈ Finset.univ.filter (fun k : Fin q => k ∉ I ∪ J), ({a k / 2, a k / 2} : Multiset ℝ))
        + (∑ k ∈ I ∪ J, (let x : ℝ := b (k : ℕ); let y : ℝ := b ((k : ℕ) + 1)
            let D : List ℝ := (C.filter (fun c => x < c ∧ c < y)).sort (· ≤ ·)
            Multiset.ofList (List.zipWith (fun p r => r - p) (x :: D ++ [y]) (x :: D ++ [y]).tail))) := by
  /- @proof-region region.target-node.session.9866dd71e8768438 begin -/
  intro q hq a ha_pos b hb0 hbq hbmono hbstep I J hIJ hne C hC1 hC2 hC3 hC4
  dsimp only
  have hb_lt : ∀ i j : ℕ, i ≤ q → j ≤ q → i < j → b i < b j := by
    intro i j hi hj hij
    exact hbmono (⟨by omega, hi⟩ : i ∈ Set.Icc 0 q) (⟨by omega, hj⟩ : j ∈ Set.Icc 0 q) hij
  have hb_lt' : ∀ i j : ℕ, i < j → j ≤ q → b i < b j := by
    intro i j hij hj
    exact hb_lt i j (by omega) hj hij
  have hb_le : ∀ i j : ℕ, i ≤ q → j ≤ q → i ≤ j → b i ≤ b j := by
    intro i j hi hj hij
    rcases eq_or_lt_of_le hij with h | h
    · exact le_of_eq (by rw [h])
    · exact le_of_lt (hb_lt i j hi hj h)
  have hb_inj : ∀ i j : ℕ, i ≤ q → j ≤ q → b i = b j → i = j := by
    intro i j hi hj hij
    by_contra h
    rcases lt_or_gt_of_ne h with h' | h'
    · exact absurd hij (ne_of_lt (hb_lt i j hi hj h'))
    · exact absurd hij (ne_of_gt (hb_lt j i hj hi h'))
  have hb_lt_add : ∀ k : Fin q, b (k : ℕ) < b ((k : ℕ) + 1) := by
    intro k
    have hk : (k : ℕ) < q := k.isLt
    exact hb_lt (k : ℕ) ((k : ℕ) + 1) (by omega) (by omega) (by omega)
  have hC_unique : ∀ (c : ℝ) (hc : c ∈ C) (k j : Fin q),
      b (k : ℕ) < c → c < b ((k : ℕ) + 1) →
      b (j : ℕ) < c → c < b ((j : ℕ) + 1) → k = j := by
    intro c hc k j hk1 hk2 hj1 hj2
    have hk : (k : ℕ) < q := k.isLt
    have hj : (j : ℕ) < q := j.isLt
    rcases lt_trichotomy (k : ℕ) (j : ℕ) with h | h | h
    · have hle : b ((k : ℕ) + 1) ≤ b (j : ℕ) := by
        rcases eq_or_lt_of_le (show (k : ℕ) + 1 ≤ (j : ℕ) by omega) with he | hl
        · exact le_of_eq (congrArg b he)
        · exact le_of_lt (hb_lt ((k : ℕ) + 1) (j : ℕ) (by omega) (by omega) hl)
      linarith [lt_of_lt_of_le hk2 hle, hj1]
    · exact Fin.ext h
    · have hle : b ((j : ℕ) + 1) ≤ b (k : ℕ) := by
        rcases eq_or_lt_of_le (show (j : ℕ) + 1 ≤ (k : ℕ) by omega) with he | hl
        · exact le_of_eq (congrArg b he)
        · exact le_of_lt (hb_lt ((j : ℕ) + 1) (k : ℕ) (by omega) (by omega) hl)
      linarith [lt_of_lt_of_le hj2 hle, hk1]
  set A : Finset ℝ :=
    (Finset.univ.filter (fun k : Fin q => 1 ≤ (k : ℕ))).image (fun k : Fin q => b (k : ℕ)) with hAd
  set Mt : Finset ℝ :=
    (Finset.univ.filter (fun k : Fin q => k ∉ I ∪ J)).image
      (fun k : Fin q => (b (k : ℕ) + b ((k : ℕ) + 1)) / 2) with hMtd
  have hp_zero : (fun k : Fin (q + 1) => b (k : ℕ)) 0 = 0 := by
    show b 0 = 0
    exact hb0
  have hp_last : (fun k : Fin (q + 1) => b (k : ℕ)) (Fin.last q) = 1 := by
    show b q = 1
    exact hbq
  have hp : StrictMono (fun k : Fin (q + 1) => b (k : ℕ)) := by
    intro i j hij
    exact hb_lt (i : ℕ) (j : ℕ) (by omega) (by omega) hij
  have hMp : ∀ x ∈ C ∪ Mt,
      (fun k : Fin (q + 1) => b (k : ℕ)) 0 ≤ x ∧
        x ≤ (fun k : Fin (q + 1) => b (k : ℕ)) (Fin.last q) := by
    intro x hx
    rw [hp_zero, hp_last]
    rcases Finset.mem_union.mp hx with hxC | hxM
    · obtain ⟨h1, h2⟩ := hC1 x hxC
      exact ⟨le_of_lt h1, le_of_lt h2⟩
    · rw [hMtd] at hxM
      obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hxM
      rw [← hk]
      have hkq : (k : ℕ) ≤ q := by omega
      have h1 : 0 ≤ b (k : ℕ) := by
        have h := hb_le 0 (k : ℕ) (by omega) hkq (by omega)
        rwa [hb0] at h
      have h1b : 0 ≤ b ((k : ℕ) + 1) := by
        have h := hb_le 0 ((k : ℕ) + 1) (by omega) (by omega) (by omega)
        rwa [hb0] at h
      have h2 : b ((k : ℕ) + 1) ≤ 1 := by
        have h := hb_le ((k : ℕ) + 1) q (by omega) (by omega) (by omega)
        rwa [hbq] at h
      have h3 : b (k : ℕ) ≤ b ((k : ℕ) + 1) := le_of_lt (hb_lt_add k)
      constructor <;> linarith
  have hchild := statopia_math_node_689319304_41a3eefa q
    (fun k : Fin (q + 1) => b (k : ℕ)) (C ∪ Mt) hp hMp
  let W : Finset ℝ := Finset.image (fun k : Fin (q + 1) => b (k : ℕ)) Finset.univ ∪ (C ∪ Mt)
  have hchild' : (∑ k : Fin q, Multiset.ofList (List.zipWith (fun p r => r - p)
      (((b (k : ℕ) :: (((C ∪ Mt).filter (fun x => b (k : ℕ) < x ∧ x < b ((k : ℕ) + 1))).sort (· ≤ ·))) ++ [b ((k : ℕ) + 1)]))
      ((((b (k : ℕ) :: (((C ∪ Mt).filter (fun x => b (k : ℕ) < x ∧ x < b ((k : ℕ) + 1))).sort (· ≤ ·))) ++ [b ((k : ℕ) + 1)])).tail)))
      = Multiset.ofList (List.zipWith (fun p r => r - p) (W.sort (· ≤ ·)) (W.sort (· ≤ ·)).tail) := hchild
  have hW : W = insert (0 : ℝ) (insert 1 (A ∪ (C ∪ Mt))) := by
    ext x
    show x ∈ Finset.image (fun k : Fin (q + 1) => b (k : ℕ)) Finset.univ ∪ (C ∪ Mt) ↔
      x ∈ insert (0 : ℝ) (insert 1 (A ∪ (C ∪ Mt)))
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hx
        rw [← hk]
        have hklt : (k : ℕ) < q + 1 := k.isLt
        rcases lt_trichotomy (k : ℕ) q with h | h | h
        · rcases Nat.eq_zero_or_pos (k : ℕ) with h0 | h0
          · exact Finset.mem_insert.mpr (Or.inl (by rw [h0]; exact hb0))
          · have hk1 : 1 ≤ (k : ℕ) := by omega
            exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_union.mpr
              (Or.inl (Finset.mem_image.mpr ⟨⟨(k : ℕ), h⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk1⟩, rfl⟩))))))
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl (by rw [h]; exact hbq))))
        · exfalso; omega
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_union.mpr (Or.inr hx)))))
    · intro hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, hb0⟩))
      · rcases Finset.mem_insert.mp hx with rfl | hx
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨Fin.last q, Finset.mem_univ _, hbq⟩))
        · rcases Finset.mem_union.mp hx with hx | hx
          · rw [hAd] at hx
            obtain ⟨k, -, hk2⟩ := Finset.mem_image.mp hx
            rw [← hk2]
            exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨Fin.castSucc k, Finset.mem_univ _, rfl⟩))
          · exact Finset.mem_union.mpr (Or.inr hx)
  have hS01 : ∀ x ∈ A ∪ (C ∪ Mt), 0 < x ∧ x < 1 := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rw [hAd] at hx
      obtain ⟨k, hk, hk'⟩ := Finset.mem_image.mp hx
      rw [← hk']
      obtain ⟨-, hk1⟩ := Finset.mem_filter.mp hk
      have hkq : (k : ℕ) ≤ q := by omega
      have hkl : (k : ℕ) < q := k.isLt
      constructor
      · have h := hb_lt 0 (k : ℕ) (by omega) hkq (by omega)
        rwa [hb0] at h
      · have h := hb_lt (k : ℕ) q hkq (le_refl q) hkl
        rwa [hbq] at h
    · rcases Finset.mem_union.mp hx with hx | hx
      · exact hC1 x hx
      · rw [hMtd] at hx
        obtain ⟨k, hk, hk'⟩ := Finset.mem_image.mp hx
        rw [← hk']
        have hkq : (k : ℕ) ≤ q := by omega
        have h1 : 0 ≤ b (k : ℕ) := by
          have h := hb_le 0 (k : ℕ) (by omega) hkq (by omega)
          rwa [hb0] at h
        have h2 : b ((k : ℕ) + 1) ≤ 1 := by
          have h := hb_le ((k : ℕ) + 1) q (by omega) (by omega) (by omega)
          rwa [hbq] at h
        have h3 : b (k : ℕ) < b ((k : ℕ) + 1) := hb_lt_add k
        constructor <;> linarith
  have hsort : (insert (0 : ℝ) (insert 1 (A ∪ (C ∪ Mt)))).sort (· ≤ ·)
      = (0 : ℝ) :: (A ∪ (C ∪ Mt)).sort (· ≤ ·) ++ [1] := by
    have hsub : ∀ {x : ℝ}, x ∈ (A ∪ (C ∪ Mt)).sort (· ≤ ·) → x ∈ A ∪ (C ∪ Mt) := by
      intro x hx
      exact Finset.mem_toList.mp
        ((List.Perm.mem_iff (Finset.sort_perm_toList (A ∪ (C ∪ Mt)) (· ≤ ·))).mp hx)
    have hLtf : (((0 : ℝ) :: (A ∪ (C ∪ Mt)).sort (· ≤ ·)) ++ [1]).toFinset
        = insert (0 : ℝ) (insert 1 (A ∪ (C ∪ Mt))) := by
      rw [List.toFinset_append, List.toFinset_cons, Finset.sort_toFinset,
        List.toFinset_cons, List.toFinset_nil]
      rw [Finset.union_insert, Finset.union_empty, Finset.insert_comm]
    have hLnodup : ((((0 : ℝ) :: (A ∪ (C ∪ Mt)).sort (· ≤ ·)) ++ [1])).Nodup := by
      rw [List.nodup_append, List.nodup_cons, List.nodup_cons]
      refine ⟨⟨?_, Finset.sort_nodup _ _⟩, ⟨by simp, List.nodup_nil⟩, ?_⟩
      · intro h0
        have h1 : (0 : ℝ) < 0 := (hS01 0 (hsub h0)).1
        linarith
      · intro x hx y hy hxye
        rw [List.mem_singleton] at hy
        have h2 : x < 1 := by
          rcases List.mem_cons.mp hx with hx0 | hx
          · rw [hx0]; norm_num
          · exact (hS01 x (hsub hx)).2
        linarith
    have hLpair : List.Pairwise (· ≤ ·)
        ((((0 : ℝ) :: (A ∪ (C ∪ Mt)).sort (· ≤ ·)) ++ [1])) := by
      rw [List.pairwise_append, List.pairwise_cons]
      refine ⟨⟨?_, Finset.pairwise_sort _ _⟩,
        List.pairwise_cons.mpr ⟨by simp, List.Pairwise.nil⟩, ?_⟩
      · intro b hb
        exact le_of_lt (hS01 b (hsub hb)).1
      · intro a ha b hb
        rw [List.mem_singleton] at hb
        have h2 : a < 1 := by
          rcases List.mem_cons.mp ha with ha0 | ha
          · rw [ha0]; norm_num
          · exact (hS01 a (hsub ha)).2
        linarith
    rw [← hLtf]
    exact (List.toFinset_sort (· ≤ ·) hLnodup).mpr hLpair
  have hpiece : Multiset.ofList (pieceLengths (A ∪ (C ∪ Mt)))
      = Multiset.ofList (List.zipWith (fun p r => r - p) (W.sort (· ≤ ·)) (W.sort (· ≤ ·)).tail) := by
    show Multiset.ofList (List.zipWith (fun a b => b - a)
        ((0 : ℝ) :: (A ∪ (C ∪ Mt)).sort (· ≤ ·) ++ [1])
        ((0 : ℝ) :: (A ∪ (C ∪ Mt)).sort (· ≤ ·) ++ [1]).tail)
      = Multiset.ofList (List.zipWith (fun p r => r - p) (W.sort (· ≤ ·)) (W.sort (· ≤ ·)).tail)
    rw [← hsort, ← hW]
  have hfinal : (∑ k : Fin q, Multiset.ofList (List.zipWith (fun p r => r - p)
      (((b (k : ℕ) :: (((C ∪ Mt).filter (fun x => b (k : ℕ) < x ∧ x < b ((k : ℕ) + 1))).sort (· ≤ ·))) ++ [b ((k : ℕ) + 1)]))
      ((((b (k : ℕ) :: (((C ∪ Mt).filter (fun x => b (k : ℕ) < x ∧ x < b ((k : ℕ) + 1))).sort (· ≤ ·))) ++ [b ((k : ℕ) + 1)])).tail)))
      = (∑ k ∈ Finset.univ.filter (fun k : Fin q => k ∉ I ∪ J), ({a k / 2, a k / 2} : Multiset ℝ))
        + (∑ k ∈ I ∪ J, (let x : ℝ := b (k : ℕ); let y : ℝ := b ((k : ℕ) + 1)
            let D : List ℝ := (C.filter (fun c => x < c ∧ c < y)).sort (· ≤ ·)
            Multiset.ofList (List.zipWith (fun p r => r - p) (x :: D ++ [y]) (x :: D ++ [y]).tail))) := by
    have hfil : Finset.univ \ (I ∪ J) = Finset.univ.filter (fun k : Fin q => k ∉ I ∪ J) := by
      ext k
      simp
    have hsplit : ∀ (G H : Fin q → Multiset ℝ),
        (∑ k ∈ Finset.univ.filter (fun k : Fin q => k ∉ I ∪ J), G k) + (∑ k ∈ I ∪ J, H k)
          = (∑ k : Fin q, (if k ∈ I ∪ J then H k else G k)) := by
      intro G H
      have h2 : (∑ k ∈ I ∪ J, (if k ∈ I ∪ J then H k else G k)) = (∑ k ∈ I ∪ J, H k) := by
        refine Finset.sum_congr rfl (fun k hk => ?_)
        exact if_pos hk
      have h1 : (∑ k ∈ Finset.univ.filter (fun k : Fin q => k ∉ I ∪ J),
            (if k ∈ I ∪ J then H k else G k))
          = (∑ k ∈ Finset.univ.filter (fun k : Fin q => k ∉ I ∪ J), G k) := by
        refine Finset.sum_congr rfl (fun k hk => ?_)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        exact if_neg hk
      have hs : (∑ k ∈ Finset.univ \ (I ∪ J), (if k ∈ I ∪ J then H k else G k))
          + (∑ k ∈ I ∪ J, (if k ∈ I ∪ J then H k else G k))
          = (∑ k : Fin q, (if k ∈ I ∪ J then H k else G k)) :=
        Finset.sum_sdiff (s₁ := I ∪ J) (s₂ := Finset.univ) (by intro x _; exact Finset.mem_univ x)
      rw [hfil] at hs
      rw [h1, h2] at hs
      exact hs
    rw [hsplit (fun k : Fin q => ({a k / 2, a k / 2} : Multiset ℝ))
      (fun k : Fin q => (let x : ℝ := b (k : ℕ); let y : ℝ := b ((k : ℕ) + 1)
        let D : List ℝ := (C.filter (fun c => x < c ∧ c < y)).sort (· ≤ ·)
        Multiset.ofList (List.zipWith (fun p r => r - p) (x :: D ++ [y]) (x :: D ++ [y]).tail)))]
    exact Finset.sum_congr rfl (fun k _ =>
      statopia_math_node_2445022674_8afd0c25 q a b hbmono hbstep I J C hC3 k)
  exact hpiece.trans (hchild'.symm.trans hfinal)

  /- @proof-region region.target-node.session.9866dd71e8768438 end -/

end LiuBangXiangYu
