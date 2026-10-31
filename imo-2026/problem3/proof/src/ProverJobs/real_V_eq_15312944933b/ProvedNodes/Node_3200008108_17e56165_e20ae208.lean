import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_1713139905_c209ee41_4a5b99f3
open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_3200008108_17e56165 : ∀ (q : ℕ) (hq : 1 ≤ q) (a : Fin q → ℝ)
    (ha_pos : ∀ i, 0 < a i) (ha_sum : ∑ i, a i = 1)
    (I J : Finset (Fin q)) (hIJ : Disjoint I J) (hne : I ∪ J ≠ ∅)
    (hUW : ∑ j ∈ J, a j ≤ ∑ i ∈ I, a i),
    let b : ℕ → ℝ := fun k => ∑ i : Fin q, if (i : ℕ) < k then a i else 0
    let piecesOf : Finset ℝ → Multiset ℝ := fun C =>
      ∑ k ∈ I ∪ J,
        (let x : ℝ := b (k : ℕ)
         let y : ℝ := b ((k : ℕ) + 1)
         let D : List ℝ := (C.filter (fun c => x < c ∧ c < y)).sort (· ≤ ·)
         Multiset.ofList (List.zipWith (fun p r => r - p) (x :: D ++ [y]) (x :: D ++ [y]).tail))
    ∃ C : Finset ℝ,
      (∀ c ∈ C, (0 : ℝ) < c ∧ c < 1) ∧
      (∀ c ∈ C, ∀ k : Fin (q + 1), c ≠ b (k : ℕ)) ∧
      (∀ c ∈ C, ∃ k ∈ I ∪ J, b (k : ℕ) < c ∧ c < b ((k : ℕ) + 1)) ∧
      C.card ≤ I.card + J.card - 1 ∧
      (∃ Ps R : Multiset ℝ,
        Ps + Ps + R = piecesOf C ∧
        R.sum = (∑ i ∈ I, a i) - (∑ j ∈ J, a j)) := by
  /- @proof-region region.target-node.session.3b6d3b065c0e6232 begin -/
  intro q hq a ha_pos ha_sum I J hIJ hne hUW
  classical
  dsimp only
  set b : ℕ → ℝ := fun k => ∑ i : Fin q, if (i : ℕ) < k then a i else 0 with hb
  have hb_step : ∀ k : Fin q, b ((k : ℕ) + 1) = b (k : ℕ) + a k := by
    intro k
    simp only [hb]
    have hk_sum : (∑ i : Fin q, if i = k then a k else 0) = a k := by simp
    rw [← hk_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : (i : ℕ) < (k : ℕ)
    · have hne : i ≠ k := by rintro rfl; exact absurd hi (lt_irrefl _)
      simp [hi, hne, Nat.lt_succ_of_lt hi]
    · by_cases hik : i = k
      · subst hik; simp
      · have hge : ¬ (i : ℕ) < (k : ℕ) + 1 := by
          intro h
          exact hik (Fin.ext (by omega))
        simp [hi, hik, hge]
  have hb_zero : b 0 = 0 := by simp [hb]
  have hb_one : b q = 1 := by
    simp only [hb]
    rw [← ha_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [if_pos i.isLt]
  have hb_mono : Monotone b := by
    intro m n hmn
    simp only [hb]
    apply Finset.sum_le_sum
    intro i _
    by_cases h : (i : ℕ) < m
    · rw [if_pos h, if_pos (lt_of_lt_of_le h hmn)]
    · rw [if_neg h]
      by_cases h' : (i : ℕ) < n
      · rw [if_pos h']; exact le_of_lt (ha_pos i)
      · rw [if_neg h']
  have hb_lt : ∀ k : Fin q, b (k : ℕ) < b ((k : ℕ) + 1) := by
    intro k
    rw [hb_step k]; linarith [ha_pos k]
  have hb_nonneg : ∀ n : ℕ, 0 ≤ b n := by
    intro n; have := hb_mono (Nat.zero_le n); rwa [hb_zero] at this
  have hb_le_one : ∀ n : ℕ, n ≤ q → b n ≤ 1 := by
    intro n hn; have := hb_mono hn; rwa [hb_one] at this
  let iHi : Fin q → ℝ := fun k => ∑ i ∈ I, if (i : ℕ) ≤ (k : ℕ) then a i else 0
  let iLo : Fin q → ℝ := fun k => ∑ i ∈ I, if (i : ℕ) < (k : ℕ) then a i else 0
  let jHi : Fin q → ℝ := fun k => ∑ j ∈ J, if (j : ℕ) ≤ (k : ℕ) then a j else 0
  let jLo : Fin q → ℝ := fun k => ∑ j ∈ J, if (j : ℕ) < (k : ℕ) then a j else 0
  let bdI : Finset ℝ := I.image iHi
  let bdJ : Finset ℝ := J.image jHi
  let C : Finset ℝ :=
    ((I ×ˢ bdJ).filter (fun ks => iLo ks.1 < ks.2 ∧ ks.2 < iHi ks.1)).image
        (fun ks => b (ks.1 : ℕ) + (ks.2 - iLo ks.1))
    ∪ ((J ×ˢ bdI).filter (fun ks => jLo ks.1 < ks.2 ∧ ks.2 < jHi ks.1)).image
        (fun ks => b (ks.1 : ℕ) + (ks.2 - jLo ks.1))
  have hiLo_I : ∀ k ∈ I, iHi k - iLo k = a k := by
    intro k hk
    simp only [iHi, iLo]
    rw [← Finset.sum_sub_distrib]
    have h0 : ∀ i ∈ I, i ≠ k →
        (if (i : ℕ) ≤ (k : ℕ) then a i else 0) - (if (i : ℕ) < (k : ℕ) then a i else 0) = 0 := by
      intro i _ hik
      by_cases hlt : (i : ℕ) < (k : ℕ)
      · rw [if_pos (le_of_lt hlt), if_pos hlt]; ring
      · have hle : ¬ (i : ℕ) ≤ (k : ℕ) := fun h => hik (Fin.ext (by omega))
        rw [if_neg hle, if_neg hlt]; ring
    have h1 : k ∉ I →
        (if (k : ℕ) ≤ (k : ℕ) then a k else 0) - (if (k : ℕ) < (k : ℕ) then a k else 0) = 0 :=
      fun h => absurd hk h
    rw [Finset.sum_eq_single k h0 h1]
    simp
  have hjLo_J : ∀ k ∈ J, jHi k - jLo k = a k := by
    intro k hk
    simp only [jHi, jLo]
    rw [← Finset.sum_sub_distrib]
    have h0 : ∀ i ∈ J, i ≠ k →
        (if (i : ℕ) ≤ (k : ℕ) then a i else 0) - (if (i : ℕ) < (k : ℕ) then a i else 0) = 0 := by
      intro i _ hik
      by_cases hlt : (i : ℕ) < (k : ℕ)
      · rw [if_pos (le_of_lt hlt), if_pos hlt]; ring
      · have hle : ¬ (i : ℕ) ≤ (k : ℕ) := fun h => hik (Fin.ext (by omega))
        rw [if_neg hle, if_neg hlt]; ring
    have h1 : k ∉ J →
        (if (k : ℕ) ≤ (k : ℕ) then a k else 0) - (if (k : ℕ) < (k : ℕ) then a k else 0) = 0 :=
      fun h => absurd hk h
    rw [Finset.sum_eq_single k h0 h1]
    simp
  have hHi_le_Lo : ∀ i i' : Fin q, (i : ℕ) < (i' : ℕ) → iHi i ≤ iLo i' := by
    intro i i' hii
    simp only [iHi, iLo]
    apply Finset.sum_le_sum
    intro m _
    by_cases h : (m : ℕ) ≤ (i : ℕ)
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h]
      by_cases h2 : (m : ℕ) < (i' : ℕ)
      · rw [if_pos h2]; exact le_of_lt (ha_pos m)
      · simp [h2]
  have hHi_le_Lo_J : ∀ j j' : Fin q, (j : ℕ) < (j' : ℕ) → jHi j ≤ jLo j' := by
    intro j j' hjj
    simp only [jHi, jLo]
    apply Finset.sum_le_sum
    intro m _
    by_cases h : (m : ℕ) ≤ (j : ℕ)
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h]
      by_cases h2 : (m : ℕ) < (j' : ℕ)
      · rw [if_pos h2]; exact le_of_lt (ha_pos m)
      · simp [h2]

  have hC_int : ∀ c ∈ C, ∃ k ∈ I ∪ J, b (k : ℕ) < c ∧ c < b ((k : ℕ) + 1) := by
    intro c hc
    simp only [C, Finset.mem_union] at hc
    rcases hc with hc | hc
    · rw [Finset.mem_image] at hc
      rcases hc with ⟨ks, hks, rfl⟩
      rw [Finset.mem_filter, Finset.mem_product] at hks
      obtain ⟨⟨hkI, _⟩, hlt, hgt⟩ := hks
      refine ⟨ks.1, Finset.mem_union.mpr (Or.inl hkI), ?_, ?_⟩
      · linarith
      · rw [hb_step ks.1]; linarith [hiLo_I ks.1 hkI]
    · rw [Finset.mem_image] at hc
      rcases hc with ⟨ks, hks, rfl⟩
      rw [Finset.mem_filter, Finset.mem_product] at hks
      obtain ⟨⟨hkJ, _⟩, hlt, hgt⟩ := hks
      refine ⟨ks.1, Finset.mem_union.mpr (Or.inr hkJ), ?_, ?_⟩
      · linarith
      · rw [hb_step ks.1]; linarith [hjLo_J ks.1 hkJ]
  refine ⟨C, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨k, _, h1, h2⟩ := hC_int c hc
    exact ⟨lt_of_le_of_lt (hb_nonneg (k : ℕ)) h1,
      lt_of_lt_of_le h2 (hb_le_one ((k : ℕ) + 1) (by have h := k.isLt; omega))⟩
  · intro c hc k hcontra
    obtain ⟨k0, _, h1, h2⟩ := hC_int c hc
    by_cases hle : (k : ℕ) ≤ (k0 : ℕ)
    · have h := hb_mono hle; linarith
    · have hge : (k0 : ℕ) + 1 ≤ (k : ℕ) := by omega
      have h := hb_mono hge; linarith
  · exact hC_int
  · have hC1c : (((I ×ˢ bdJ).filter (fun ks => iLo ks.1 < ks.2 ∧ ks.2 < iHi ks.1)).image
          (fun ks => b (ks.1 : ℕ) + (ks.2 - iLo ks.1))).card ≤ J.card := by
      have hinj : Set.InjOn (fun ks : Fin q × ℝ => ks.2)
          ↑((I ×ˢ bdJ).filter (fun ks => iLo ks.1 < ks.2 ∧ ks.2 < iHi ks.1)) := by
        intro ks hks ks' hks' hEq
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hks hks'
        obtain ⟨⟨hI, _⟩, hl, hr⟩ := hks
        obtain ⟨⟨hI', _⟩, hl', hr'⟩ := hks'
        have hk : ks.1 = ks'.1 := by
          rcases lt_trichotomy ks.1 ks'.1 with hlt | heq | hgt
          · have h := hHi_le_Lo ks.1 ks'.1 hlt
            rw [show ks'.2 = ks.2 from hEq.symm] at hl'
            linarith
          · exact heq
          · have h := hHi_le_Lo ks'.1 ks.1 hgt
            rw [show ks.2 = ks'.2 from hEq] at hl
            linarith
        exact Prod.ext hk hEq
      calc (((I ×ˢ bdJ).filter (fun ks => iLo ks.1 < ks.2 ∧ ks.2 < iHi ks.1)).image
              (fun ks => b (ks.1 : ℕ) + (ks.2 - iLo ks.1))).card
          ≤ ((I ×ˢ bdJ).filter (fun ks => iLo ks.1 < ks.2 ∧ ks.2 < iHi ks.1)).card :=
            Finset.card_image_le
        _ ≤ (((I ×ˢ bdJ).filter (fun ks => iLo ks.1 < ks.2 ∧ ks.2 < iHi ks.1)).image
              (fun ks => ks.2)).card := by
            rw [Finset.card_image_of_injOn hinj]
        _ ≤ bdJ.card := by
            apply Finset.card_le_card
            intro x hx
            rw [Finset.mem_image] at hx
            obtain ⟨ks, hks, rfl⟩ := hx
            rw [Finset.mem_filter, Finset.mem_product] at hks
            exact hks.1.2
        _ ≤ J.card := by
            show (J.image jHi).card ≤ J.card
            exact Finset.card_image_le
    have hC2c : (((J ×ˢ bdI).filter (fun ks => jLo ks.1 < ks.2 ∧ ks.2 < jHi ks.1)).image
          (fun ks => b (ks.1 : ℕ) + (ks.2 - jLo ks.1))).card ≤ I.card - 1 := by
      by_cases hIe : I = ∅
      · have hbd : bdI = ∅ := by simp [bdI, hIe]
        rw [hbd, hIe]; simp
      · obtain ⟨t, htI, hmax⟩ := Finset.exists_max_image I (fun x : Fin q => (x : ℕ))
          (Finset.nonempty_iff_ne_empty.mpr hIe)
        have hUt : iHi t = ∑ i ∈ I, a i := by
          simp only [iHi]
          apply Finset.sum_congr rfl
          intro i hi
          rw [if_pos (hmax i hi)]
        have hUmem : (∑ i ∈ I, a i) ∈ bdI := by
          change (∑ i ∈ I, a i) ∈ I.image iHi
          exact Finset.mem_image.mpr ⟨t, htI, hUt⟩
        have hleW : ∀ k : Fin q, jHi k ≤ ∑ j ∈ J, a j := by
          intro k
          simp only [jHi]
          apply Finset.sum_le_sum
          intro m _
          by_cases hc : (m : ℕ) ≤ (k : ℕ)
          · rw [if_pos hc]
          · rw [if_neg hc]; exact le_of_lt (ha_pos m)
        have hsub : ((J ×ˢ bdI).filter (fun ks => jLo ks.1 < ks.2 ∧ ks.2 < jHi ks.1)).image
            (fun ks => ks.2) ⊆ bdI.erase (∑ i ∈ I, a i) := by
          intro x hx
          rw [Finset.mem_image] at hx
          obtain ⟨ks, hks, rfl⟩ := hx
          rw [Finset.mem_filter, Finset.mem_product] at hks
          obtain ⟨⟨hkJ, hxbd⟩, hlt, hgt⟩ := hks
          rw [Finset.mem_erase]
          refine ⟨?_, hxbd⟩
          intro hxe
          rw [hxe] at hgt
          linarith [hgt, hleW ks.1, hUW]
        have hcard2 : (((J ×ˢ bdI).filter (fun ks => jLo ks.1 < ks.2 ∧ ks.2 < jHi ks.1)).image
            (fun ks => ks.2)).card ≤ I.card - 1 := by
          calc _ ≤ (bdI.erase (∑ i ∈ I, a i)).card := Finset.card_le_card hsub
            _ = bdI.card - 1 := Finset.card_erase_of_mem hUmem
            _ ≤ I.card - 1 := by
                have hbc : bdI.card ≤ I.card := by
                  show (I.image iHi).card ≤ I.card
                  exact Finset.card_image_le
                omega
        have hinj2 : Set.InjOn (fun ks : Fin q × ℝ => ks.2)
            ↑((J ×ˢ bdI).filter (fun ks => jLo ks.1 < ks.2 ∧ ks.2 < jHi ks.1)) := by
          intro ks hks ks' hks' hEq
          rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hks hks'
          obtain ⟨⟨hJ, _⟩, hl, hr⟩ := hks
          obtain ⟨⟨hJ', _⟩, hl', hr'⟩ := hks'
          have hk : ks.1 = ks'.1 := by
            rcases lt_trichotomy ks.1 ks'.1 with hlt | heq | hgt
            · have h := hHi_le_Lo_J ks.1 ks'.1 hlt
              rw [show ks'.2 = ks.2 from hEq.symm] at hl'
              linarith
            · exact heq
            · have h := hHi_le_Lo_J ks'.1 ks.1 hgt
              rw [show ks.2 = ks'.2 from hEq] at hl
              linarith
          exact Prod.ext hk hEq
        calc (((J ×ˢ bdI).filter (fun ks => jLo ks.1 < ks.2 ∧ ks.2 < jHi ks.1)).image
                (fun ks => b (ks.1 : ℕ) + (ks.2 - jLo ks.1))).card
            ≤ ((J ×ˢ bdI).filter (fun ks => jLo ks.1 < ks.2 ∧ ks.2 < jHi ks.1)).card :=
              Finset.card_image_le
          _ ≤ (((J ×ˢ bdI).filter (fun ks => jLo ks.1 < ks.2 ∧ ks.2 < jHi ks.1)).image
                (fun ks => ks.2)).card := by
              rw [Finset.card_image_of_injOn hinj2]
          _ ≤ I.card - 1 := hcard2
    by_cases hIe : I = ∅
    · have hC1e : (((I ×ˢ bdJ).filter (fun ks => iLo ks.1 < ks.2 ∧ ks.2 < iHi ks.1)).image
          (fun ks => b (ks.1 : ℕ) + (ks.2 - iLo ks.1))) = ∅ := by
        rw [hIe]; simp
      have hJne : J ≠ ∅ := by
        intro hJ; exact hne (by rw [hJ, hIe]; simp)
      have hJpos : 1 ≤ J.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hJne)
      have hCu : C.card ≤ (((I ×ˢ bdJ).filter (fun ks => iLo ks.1 < ks.2 ∧ ks.2 < iHi ks.1)).image
            (fun ks => b (ks.1 : ℕ) + (ks.2 - iLo ks.1))).card +
            (((J ×ˢ bdI).filter (fun ks => jLo ks.1 < ks.2 ∧ ks.2 < jHi ks.1)).image
            (fun ks => b (ks.1 : ℕ) + (ks.2 - jLo ks.1))).card := by
        simp only [C]
        exact Finset.card_union_le _ _
      rw [hC1e] at hCu
      simp only [Finset.card_empty, zero_add] at hCu
      rw [hIe] at hC2c
      simp only [Finset.card_empty] at hC2c
      rw [hIe]
      simp only [Finset.card_empty, zero_add]
      omega
    · have hIpos : 1 ≤ I.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hIe)
      have hCu : C.card ≤ (((I ×ˢ bdJ).filter (fun ks => iLo ks.1 < ks.2 ∧ ks.2 < iHi ks.1)).image
            (fun ks => b (ks.1 : ℕ) + (ks.2 - iLo ks.1))).card +
            (((J ×ˢ bdI).filter (fun ks => jLo ks.1 < ks.2 ∧ ks.2 < jHi ks.1)).image
            (fun ks => b (ks.1 : ℕ) + (ks.2 - jLo ks.1))).card := by
        simp only [C]
        exact Finset.card_union_le _ _
      omega
  · exact statopia_math_node_1713139905_c209ee41 q hq a ha_pos I J hIJ hUW
  /- @proof-region region.target-node.session.3b6d3b065c0e6232 end -/

end LiuBangXiangYu
