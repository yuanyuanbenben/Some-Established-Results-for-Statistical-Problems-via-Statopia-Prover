import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base

open scoped BigOperators
open LiuBangXiangYu
open Classical

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_428735515_34bc9020 : ∀ (q : ℕ) (a : Fin q → ℝ)
    (ha_pos : ∀ i : Fin q, 0 < a i) (I J : Finset (Fin q)) (hIJ : Disjoint I J)
    (i0 : Fin q) (hi0 : i0 ∈ I),
    let iHi : Fin q → ℝ := fun k => ∑ i ∈ I, if (i : ℕ) ≤ (k : ℕ) then a i else 0;
    let iLo : Fin q → ℝ := fun k => ∑ i ∈ I, if (i : ℕ) < (k : ℕ) then a i else 0;
    let jHi : Fin q → ℝ := fun k => ∑ j ∈ J, if (j : ℕ) ≤ (k : ℕ) then a j else 0;
    let jLo : Fin q → ℝ := fun k => ∑ j ∈ J, if (j : ℕ) < (k : ℕ) then a j else 0;
    let b : ℕ → ℝ := fun k => ∑ i : Fin q, if (i : ℕ) < k then a i else 0;
    let bdI : Finset ℝ := I.image iHi;
    let bdJ : Finset ℝ := J.image jHi;
    let C : Finset ℝ :=
      ((I ×ˢ bdJ).filter (fun ks => iLo ks.1 < ks.2 ∧ ks.2 < iHi ks.1)).image
          (fun ks => b (ks.1 : ℕ) + (ks.2 - iLo ks.1)) ∪
        ((J ×ˢ bdI).filter (fun ks => jLo ks.1 < ks.2 ∧ ks.2 < jHi ks.1)).image
          (fun ks => b (ks.1 : ℕ) + (ks.2 - jLo ks.1));
    let U : ℝ := ∑ i ∈ I, a i;
    (C.filter (fun c => b (i0 : ℕ) < c ∧ c < b ((i0 : ℕ) + 1))).sort (· ≤ ·)
      = List.map (fun s => s + (b (i0 : ℕ) - iLo i0))
          (((bdJ.filter (fun x => 0 < x ∧ x < U)).filter (fun x => iLo i0 < x ∧ x < iHi i0)).sort (· ≤ ·)) := by
  /- @proof-region region.target-node.session.b6e1559880742566 begin -/
  intro q a ha_pos I J hIJ i0 hi0
  intro iHi iLo jHi jLo b bdI bdJ C U
  have hfig : ∀ k : Fin q, (∑ i : Fin q, (if (i : ℕ) = (k : ℕ) then a i else 0)) = a k := by
    intro k
    have hs : (∑ i : Fin q, (if (i : ℕ) = (k : ℕ) then a i else 0))
        = (if (k : ℕ) = (k : ℕ) then a k else 0) :=
      Finset.sum_eq_single k
        (fun b' _ hb' => by
          rw [if_neg (show ¬ ((b' : ℕ) = (k : ℕ)) by intro h; exact hb' (Fin.ext h))])
        (fun hk => absurd (Finset.mem_univ k) hk)
    simpa using hs
  have hb_step : ∀ k : Fin q, b ((k : ℕ) + 1) = b (k : ℕ) + a k := by
    intro k
    have hpt : ∀ i : Fin q, (if (i : ℕ) < (k : ℕ) + 1 then a i else 0)
        = (if (i : ℕ) < (k : ℕ) then a i else 0)
          + (if (i : ℕ) = (k : ℕ) then a i else 0) := by
      intro i
      by_cases h1 : (i : ℕ) < (k : ℕ)
      · rw [if_pos (show (i : ℕ) < (k : ℕ) + 1 by omega), if_pos h1,
            if_neg (show ¬ ((i : ℕ) = (k : ℕ)) by omega), add_zero]
      · by_cases h2 : (i : ℕ) = (k : ℕ)
        · rw [if_pos (show (i : ℕ) < (k : ℕ) + 1 by omega), if_neg h1, if_pos h2, zero_add]
        · rw [if_neg (show ¬ ((i : ℕ) < (k : ℕ) + 1) by omega), if_neg h1, if_neg h2, add_zero]
    show (∑ i : Fin q, (if (i : ℕ) < (k : ℕ) + 1 then a i else 0))
        = (∑ i : Fin q, (if (i : ℕ) < (k : ℕ) then a i else 0)) + a k
    rw [show (∑ i : Fin q, (if (i : ℕ) < (k : ℕ) + 1 then a i else 0))
        = ∑ i : Fin q, ((if (i : ℕ) < (k : ℕ) then a i else 0)
            + (if (i : ℕ) = (k : ℕ) then a i else 0))
        from Finset.sum_congr rfl (fun i _ => hpt i)]
    rw [Finset.sum_add_distrib, hfig k]
  have hIeq : ∀ k : Fin q, (∑ i ∈ I, (if (i : ℕ) = (k : ℕ) then a i else 0))
      = (if k ∈ I then a k else 0) := by
    intro k
    by_cases hk : k ∈ I
    · rw [if_pos hk]
      have hs : (∑ i ∈ I, (if (i : ℕ) = (k : ℕ) then a i else 0))
          = (if (k : ℕ) = (k : ℕ) then a k else 0) :=
        Finset.sum_eq_single k
          (fun b' _ hb' => by
            rw [if_neg (show ¬ ((b' : ℕ) = (k : ℕ)) by intro h; exact hb' (Fin.ext h))])
          (fun hk' => absurd hk hk')
      simpa using hs
    · rw [if_neg hk]
      rw [show (∑ i ∈ I, (if (i : ℕ) = (k : ℕ) then a i else 0)) = ∑ i ∈ I, (0 : ℝ) from
        Finset.sum_congr rfl (fun i hi => by
          rw [if_neg (show ¬ ((i : ℕ) = (k : ℕ)) by
            intro h; exact hk ((Fin.ext h) ▸ hi))])]
      simp
  have hiHi_eq : ∀ k : Fin q, iHi k = iLo k + (if k ∈ I then a k else 0) := by
    intro k
    show (∑ i ∈ I, (if (i : ℕ) ≤ (k : ℕ) then a i else 0))
        = (∑ i ∈ I, (if (i : ℕ) < (k : ℕ) then a i else 0)) + (if k ∈ I then a k else 0)
    rw [show (∑ i ∈ I, (if (i : ℕ) ≤ (k : ℕ) then a i else 0))
        = ∑ i ∈ I, ((if (i : ℕ) < (k : ℕ) then a i else 0)
            + (if (i : ℕ) = (k : ℕ) then a i else 0))
        from Finset.sum_congr rfl (fun i _ => by
          by_cases h1 : (i : ℕ) < (k : ℕ)
          · rw [if_pos (show (i : ℕ) ≤ (k : ℕ) by omega), if_pos h1,
                if_neg (show ¬ ((i : ℕ) = (k : ℕ)) by omega), add_zero]
          · by_cases h2 : (i : ℕ) = (k : ℕ)
            · rw [if_pos (show (i : ℕ) ≤ (k : ℕ) by omega), if_neg h1, if_pos h2, zero_add]
            · rw [if_neg (show ¬ ((i : ℕ) ≤ (k : ℕ)) by omega), if_neg h1, if_neg h2, add_zero])]
    rw [Finset.sum_add_distrib, hIeq k]
  have hb_lt : ∀ k : Fin q, b (k : ℕ) < b ((k : ℕ) + 1) := by
    intro k
    have h1 := hb_step k
    have h2 := ha_pos k
    linarith
  have hb_mono : ∀ m k : ℕ, k < m → m ≤ q → b k < b m := by
    intro m
    induction m with
    | zero => intro k hk _; omega
    | succ m ih =>
      intro k hk hmq
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hlt | heq
      · have h1 : b k < b m := ih k hlt (by omega)
        have h2 : b m < b (m + 1) := by simpa using hb_lt (⟨m, by omega⟩ : Fin q)
        show b k < b (m + 1)
        linarith
      · rw [heq]
        show b m < b (m + 1)
        simpa using hb_lt (⟨m, by omega⟩ : Fin q)
  have hiHi_le_U : iHi i0 ≤ U := by
    show (∑ i ∈ I, (if (i : ℕ) ≤ (i0 : ℕ) then a i else 0)) ≤ (∑ i ∈ I, a i)
    apply Finset.sum_le_sum
    intro i _
    split_ifs with h
    · exact le_refl (a i)
    · exact le_of_lt (ha_pos i)
  have hiLo_nonneg : 0 ≤ iLo i0 := by
    show 0 ≤ ∑ i ∈ I, (if (i : ℕ) < (i0 : ℕ) then a i else 0)
    apply Finset.sum_nonneg
    intro i _
    split_ifs with h
    · exact le_of_lt (ha_pos i)
    · exact le_refl 0
  have ha_eq : ∀ k : Fin q, k ∈ I → a k = iHi k - iLo k := by
    intro k hk
    have h := hiHi_eq k
    rw [if_pos hk] at h
    linarith
  have hbleq : ∀ k : Fin q, k ∈ I → b ((k : ℕ) + 1) = b (k : ℕ) + (iHi k - iLo k) := by
    intro k hk
    rw [hb_step k, ha_eq k hk]
  have hjEeq : ∀ k : Fin q, (∑ j ∈ J, (if (j : ℕ) = (k : ℕ) then a j else 0))
      = (if k ∈ J then a k else 0) := by
    intro k
    by_cases hk : k ∈ J
    · rw [if_pos hk]
      have hs : (∑ j ∈ J, (if (j : ℕ) = (k : ℕ) then a j else 0))
          = (if (k : ℕ) = (k : ℕ) then a k else 0) :=
        Finset.sum_eq_single k
          (fun b' _ hb' => by
            rw [if_neg (show ¬ ((b' : ℕ) = (k : ℕ)) by intro h; exact hb' (Fin.ext h))])
          (fun hk' => absurd hk hk')
      simpa using hs
    · rw [if_neg hk]
      rw [show (∑ j ∈ J, (if (j : ℕ) = (k : ℕ) then a j else 0)) = ∑ j ∈ J, (0 : ℝ) from
        Finset.sum_congr rfl (fun j hj => by
          rw [if_neg (show ¬ ((j : ℕ) = (k : ℕ)) by
            intro h; exact hk ((Fin.ext h) ▸ hj))])]
      simp
  have hjHi_eq : ∀ k : Fin q, jHi k = jLo k + (if k ∈ J then a k else 0) := by
    intro k
    show (∑ j ∈ J, (if (j : ℕ) ≤ (k : ℕ) then a j else 0))
        = (∑ j ∈ J, (if (j : ℕ) < (k : ℕ) then a j else 0)) + (if k ∈ J then a k else 0)
    rw [show (∑ j ∈ J, (if (j : ℕ) ≤ (k : ℕ) then a j else 0))
        = ∑ j ∈ J, ((if (j : ℕ) < (k : ℕ) then a j else 0)
            + (if (j : ℕ) = (k : ℕ) then a j else 0))
        from Finset.sum_congr rfl (fun j _ => by
          by_cases h1 : (j : ℕ) < (k : ℕ)
          · rw [if_pos (show (j : ℕ) ≤ (k : ℕ) by omega), if_pos h1,
                if_neg (show ¬ ((j : ℕ) = (k : ℕ)) by omega), add_zero]
          · by_cases h2 : (j : ℕ) = (k : ℕ)
            · rw [if_pos (show (j : ℕ) ≤ (k : ℕ) by omega), if_neg h1, if_pos h2, zero_add]
            · rw [if_neg (show ¬ ((j : ℕ) ≤ (k : ℕ)) by omega), if_neg h1, if_neg h2, add_zero])]
    rw [Finset.sum_add_distrib, hjEeq k]
  have hja_eq : ∀ k : Fin q, k ∈ J → a k = jHi k - jLo k := by
    intro k hk
    have h := hjHi_eq k
    rw [if_pos hk] at h
    linarith
  have hbleqJ : ∀ k : Fin q, k ∈ J → b ((k : ℕ) + 1) = b (k : ℕ) + (jHi k - jLo k) := by
    intro k hk
    rw [hb_step k, hja_eq k hk]
  have hblksep : ∀ (i' i'' : Fin q) (c : ℝ), b (i' : ℕ) < c → c < b ((i' : ℕ) + 1) →
      b (i'' : ℕ) < c → c < b ((i'' : ℕ) + 1) → i' = i'' := by
    intro i' i'' c h1 h2 h3 h4
    by_contra hne
    have hne' : (i' : ℕ) ≠ (i'' : ℕ) := fun h => hne (Fin.ext h)
    rcases lt_or_gt_of_ne hne' with hlt | hgt
    · have hle : b ((i' : ℕ) + 1) ≤ b (i'' : ℕ) := by
        rcases lt_or_eq_of_le (show (i' : ℕ) + 1 ≤ (i'' : ℕ) by omega) with hlt2 | heq2
        · exact le_of_lt (hb_mono (i'' : ℕ) ((i' : ℕ) + 1) hlt2 (le_of_lt i''.isLt))
        · exact le_of_eq (by rw [heq2])
      linarith
    · have hle : b ((i'' : ℕ) + 1) ≤ b (i' : ℕ) := by
        rcases lt_or_eq_of_le (show (i'' : ℕ) + 1 ≤ (i' : ℕ) by omega) with hlt2 | heq2
        · exact le_of_lt (hb_mono (i' : ℕ) ((i'' : ℕ) + 1) hlt2 (le_of_lt i'.isLt))
        · exact le_of_eq (by rw [heq2])
      linarith
  set S' : Finset ℝ :=
    ((bdJ.filter (fun x => 0 < x ∧ x < U)).filter (fun x => iLo i0 < x ∧ x < iHi i0)) with hS'
  let f : ℝ ↪ ℝ := ⟨fun x => x + (b (i0 : ℕ) - iLo i0), fun x y h => by linarith⟩
  have hmem : ∀ x : ℝ,
      x ∈ C.filter (fun y => b (i0 : ℕ) < y ∧ y < b ((i0 : ℕ) + 1)) ↔ x ∈ Finset.map f S' := by
    intro x
    constructor
    · intro hx
      rw [Finset.mem_filter] at hx
      obtain ⟨hxC, hxa, hxb⟩ := hx
      have hxu : x ∈ (((I ×ˢ bdJ).filter (fun ks => iLo ks.1 < ks.2 ∧ ks.2 < iHi ks.1)).image
              (fun ks => b (ks.1 : ℕ) + (ks.2 - iLo ks.1)) ∪
            ((J ×ˢ bdI).filter (fun ks => jLo ks.1 < ks.2 ∧ ks.2 < jHi ks.1)).image
              (fun ks => b (ks.1 : ℕ) + (ks.2 - jLo ks.1))) := hxC
      rw [Finset.mem_union] at hxu
      rcases hxu with hxu | hxu
      · rw [Finset.mem_image] at hxu
        obtain ⟨ks, hks, hksx⟩ := hxu
        rw [Finset.mem_filter, Finset.mem_product] at hks
        obtain ⟨⟨hks1, hks2⟩, hks3, hks4⟩ := hks
        have hx_eq : x = b (ks.1 : ℕ) + (ks.2 - iLo ks.1) := by simpa using hksx.symm
        have hltA : b (ks.1 : ℕ) < x := by linarith
        have hltB : x < b ((ks.1 : ℕ) + 1) := by
          have hb := hbleq ks.1 hks1
          linarith
        have hieq : ks.1 = i0 := hblksep ks.1 i0 x hltA hltB hxa hxb
        rw [hieq] at hks3 hks4 hx_eq
        rw [Finset.mem_map]
        refine ⟨ks.2, ?_, ?_⟩
        · rw [hS']
          simp only [Finset.mem_filter]
          exact ⟨⟨hks2, by linarith [hks3, hiLo_nonneg], by linarith [hks4, hiHi_le_U]⟩,
            hks3, hks4⟩
        · show ks.2 + (b (i0 : ℕ) - iLo i0) = x
          linarith
      · exfalso
        rw [Finset.mem_image] at hxu
        obtain ⟨ks, hks, hksx⟩ := hxu
        rw [Finset.mem_filter, Finset.mem_product] at hks
        obtain ⟨⟨hks1, hks2⟩, hks3, hks4⟩ := hks
        have hx_eq : x = b (ks.1 : ℕ) + (ks.2 - jLo ks.1) := by simpa using hksx.symm
        have hltA : b (ks.1 : ℕ) < x := by linarith
        have hltB : x < b ((ks.1 : ℕ) + 1) := by
          have hb := hbleqJ ks.1 hks1
          linarith
        have hjeq : ks.1 = i0 := hblksep ks.1 i0 x hltA hltB hxa hxb
        exact (Finset.disjoint_left.mp hIJ hi0) (hjeq ▸ hks1)
    · intro hx
      rw [Finset.mem_map] at hx
      obtain ⟨s, hs, hfs⟩ := hx
      rw [hS'] at hs
      simp only [Finset.mem_filter] at hs
      obtain ⟨⟨hsJ, _, _⟩, hs3, hs4⟩ := hs
      have hx_eq : x = s + (b (i0 : ℕ) - iLo i0) := by simpa using hfs.symm
      have hxpart : x ∈ (((I ×ˢ bdJ).filter (fun ks => iLo ks.1 < ks.2 ∧ ks.2 < iHi ks.1)).image
          (fun ks => b (ks.1 : ℕ) + (ks.2 - iLo ks.1))) := by
        rw [Finset.mem_image]
        refine ⟨(i0, s), ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_product]
          exact ⟨⟨hi0, hsJ⟩, hs3, hs4⟩
        · show b (i0 : ℕ) + (s - iLo i0) = x
          linarith
      have hxC : x ∈ C := Finset.mem_union.mpr (Or.inl hxpart)
      have hxfin : x ∈ C.filter (fun y => b (i0 : ℕ) < y ∧ y < b ((i0 : ℕ) + 1)) := by
        rw [Finset.mem_filter]
        refine ⟨hxC, ?_, ?_⟩
        · linarith [hx_eq, hs3]
        · have hb := hbleq i0 hi0
          linarith [hx_eq, hs4, hb]
      exact hxfin
  have hset : C.filter (fun y => b (i0 : ℕ) < y ∧ y < b ((i0 : ℕ) + 1)) = Finset.map f S' :=
    Finset.ext (fun x => hmem x)
  have hmono : StrictMonoOn (⇑f) ↑S' := by
    intro x _ y _ hxy
    show x + (b (i0 : ℕ) - iLo i0) < y + (b (i0 : ℕ) - iLo i0)
    linarith
  rw [hset]
  exact (StrictMonoOn.map_finsetSort f S' hmono).symm
  /- @proof-region region.target-node.session.b6e1559880742566 end -/

end LiuBangXiangYu
