import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_4221689064_d3ddf0ec_fbe161c8
open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_2471006781_90e3b0f3 : ∀ (A : Finset ℝ) (s : ℕ → ℝ)
    (hA : (A : Set ℝ) ⊆ Set.Ioo (0 : ℝ) 1)
    (hs0 : s 0 = 0) (hs1 : s (A.card + 1) = 1)
    (hs_mono : StrictMonoOn s (Set.Icc 0 (A.card + 1)))
    (hs_int : (A : Set ℝ) = s '' Set.Icc 1 A.card),
    pieceLengths (A ∪ (Finset.range (A.card + 1)).image (fun i => (s i + s (i + 1)) / 2))
      = ((pieceLengths A).map (fun a => a / 2)).flatMap (fun a => [a, a]) ∧
    (pieceLengths (A ∪ (Finset.range (A.card + 1)).image (fun i => (s i + s (i + 1)) / 2))).sum = 1 := by
  /- @proof-region region.target-node.session.31db2d32ef5be3a2 begin -/
  intro A s hA hs0 hs1 hs_mono hs_int
  obtain ⟨hA_lens, hA_len, hA_pos, hA_sum, -, -⟩ :=
    statopia_math_node_4221689064_d3ddf0ec A hA s hs0 hs1 hs_mono hs_int
  set B : Finset ℝ := (Finset.range (A.card + 1)).image (fun i => (s i + s (i + 1)) / 2) with hBdef
  set t : ℕ → ℝ := fun k => (s (k / 2) + s ((k + 1) / 2)) / 2 with htdef
  have ht_val : ∀ k, t k = (s (k / 2) + s ((k + 1) / 2)) / 2 := fun k => congrFun htdef k
  have hs_lt : ∀ i j, i < j → j ≤ A.card + 1 → s i < s j := by
    intro i j hij hj
    exact hs_mono (Set.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩)
      (Set.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩) hij
  have hs_le : ∀ i j, i ≤ j → j ≤ A.card + 1 → s i ≤ s j := by
    intro i j hij hj
    rcases eq_or_lt_of_le hij with h | h
    · subst h; exact le_refl _
    · exact le_of_lt (hs_lt i j h hj)
  have hs_mem_A : ∀ i, 1 ≤ i → i ≤ A.card → s i ∈ (A : Set ℝ) := by
    intro i hi hic
    rw [hs_int]
    exact ⟨i, Set.mem_Icc.mpr ⟨hi, hic⟩, rfl⟩
  have hs_pos : ∀ i, 1 ≤ i → i ≤ A.card → 0 < s i := fun i hi hic => (hA (hs_mem_A i hi hic)).1
  have hs_lt_one : ∀ i, 1 ≤ i → i ≤ A.card → s i < 1 := fun i hi hic => (hA (hs_mem_A i hi hic)).2
  have ht_zero : t 0 = 0 := by
    rw [ht_val, hs0]
    ring
  have ht_q : t (2 * (A.card + 1)) = 1 := by
    rw [ht_val]
    have h1 : (2 * (A.card + 1)) / 2 = A.card + 1 := by omega
    have h2 : (2 * (A.card + 1) + 1) / 2 = A.card + 1 := by omega
    rw [h1, h2, hs1]
    ring
  have ht_even : ∀ j, t (2 * j) = s j := by
    intro j
    rw [ht_val]
    have h1 : (2 * j) / 2 = j := by omega
    have h2 : (2 * j + 1) / 2 = j := by omega
    rw [h1, h2]
    ring
  have ht_odd : ∀ j, t (2 * j + 1) = (s j + s (j + 1)) / 2 := by
    intro j
    rw [ht_val]
    have h1 : (2 * j + 1) / 2 = j := by omega
    have h2 : (2 * j + 1 + 1) / 2 = j + 1 := by omega
    rw [h1, h2]
  have hinterior : ∀ i, 1 ≤ i → i < 2 * (A.card + 1) → t i ∈ Set.Ioo (0 : ℝ) 1 := by
    intro i hi1 hiQ
    have hmod : i % 2 = 0 ∨ i % 2 = 1 := by omega
    rcases hmod with hm | hm
    · have hi2 : i = 2 * (i / 2) := by omega
      rw [hi2, ht_even (i / 2)]
      exact ⟨hs_pos (i / 2) (by omega) (by omega), hs_lt_one (i / 2) (by omega) (by omega)⟩
    · have hi2 : i = 2 * (i / 2) + 1 := by omega
      rw [hi2, ht_odd (i / 2)]
      have hs1pos : 0 < s 1 := by
        rw [← hs0]; exact hs_lt 0 1 (by norm_num) (by omega)
      have hp : 0 < s (i / 2 + 1) := lt_of_lt_of_le hs1pos (hs_le 1 (i / 2 + 1) (by omega) (by omega))
      have hq : 0 ≤ s (i / 2) := by
        rw [← hs0]; exact hs_le 0 (i / 2) (Nat.zero_le _) (by omega)
      have hsj : s (i / 2) < 1 := by
        rcases Nat.eq_zero_or_pos (i / 2) with h | h
        · rw [h, hs0]; norm_num
        · exact hs_lt_one (i / 2) h (by omega)
      have hsj1 : s (i / 2 + 1) ≤ 1 := by
        rw [← hs1]; exact hs_le (i / 2 + 1) (A.card + 1) (by omega) (le_refl _)
      exact ⟨by linarith, by linarith⟩
  have ht_lt_upper : ∀ k, k < 2 * (A.card + 1) → t k < s (k / 2 + 1) := by
    intro k hk
    rw [ht_val]
    have hA : s (k / 2) < s (k / 2 + 1) := hs_lt (k / 2) (k / 2 + 1) (by omega) (by omega)
    have hB : s ((k + 1) / 2) ≤ s (k / 2 + 1) :=
      hs_le ((k + 1) / 2) (k / 2 + 1) (by omega) (by omega)
    linarith
  have ht_ge_lower : ∀ k, k ≤ 2 * (A.card + 1) → s (k / 2) ≤ t k := by
    intro k hk
    rw [ht_val]
    have hle : s (k / 2) ≤ s ((k + 1) / 2) :=
      hs_le (k / 2) ((k + 1) / 2) (by omega) (by omega)
    linarith
  have hmono : StrictMonoOn t (Set.Icc 0 (2 * (A.card + 1))) := by
    intro i hi j hj hij
    obtain ⟨-, hiQ⟩ := hi
    obtain ⟨-, hjQ⟩ := hj
    have hd : i / 2 < j / 2 ∨ i / 2 = j / 2 := by omega
    rcases hd with hab | hab
    · have h1 : t i < s (i / 2 + 1) := ht_lt_upper i (by omega)
      have h2 : s (i / 2 + 1) ≤ s (j / 2) := hs_le (i / 2 + 1) (j / 2) (by omega) (by omega)
      have h3 : s (j / 2) ≤ t j := ht_ge_lower j (by omega)
      exact lt_of_lt_of_le h1 (le_trans h2 h3)
    · have hi2 : i = 2 * (i / 2) := by omega
      have hj2 : j = 2 * (j / 2) + 1 := by omega
      rw [hi2, ht_even (i / 2), hj2, ht_odd (j / 2), hab]
      have hslt : s (j / 2) < s (j / 2 + 1) := hs_lt (j / 2) (j / 2 + 1) (by omega) (by omega)
      linarith
  have hAmem : ∀ x, x ∈ A ↔ ∃ k, 1 ≤ k ∧ k ≤ A.card ∧ s k = x := by
    intro x
    rw [← Finset.mem_coe, hs_int, Set.mem_image]
    constructor
    · rintro ⟨k, hk, hkx⟩
      exact ⟨k, (Set.mem_Icc.mp hk).1, (Set.mem_Icc.mp hk).2, hkx⟩
    · rintro ⟨k, hk1, hk2, hkx⟩
      exact ⟨k, Set.mem_Icc.mpr ⟨hk1, hk2⟩, hkx⟩
  have hBmem : ∀ x, x ∈ B ↔ ∃ i, i ≤ A.card ∧ (s i + s (i + 1)) / 2 = x := by
    intro x
    rw [hBdef, Finset.mem_image]
    simp only [Finset.mem_range]
    constructor
    · rintro ⟨i, hi, hix⟩; exact ⟨i, by omega, hix⟩
    · rintro ⟨i, hi, hix⟩; exact ⟨i, by omega, hix⟩
  have hSunion : (A ∪ B : Set ℝ) = t '' Set.Icc 1 (2 * (A.card + 1) - 1) := by
    ext x
    simp only [Set.mem_union, Finset.mem_coe, hAmem x, hBmem x, Set.mem_image]
    constructor
    · rintro (⟨k, hk1, hk2, hkx⟩ | ⟨i, hi, hix⟩)
      · refine ⟨2 * k, Set.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
        exact (ht_even k).trans hkx
      · refine ⟨2 * i + 1, Set.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
        exact (ht_odd i).trans hix
    · rintro ⟨j, hj, hjx⟩
      obtain ⟨hj1, hj2⟩ := Set.mem_Icc.mp hj
      have hmod : j % 2 = 0 ∨ j % 2 = 1 := by omega
      rcases hmod with hm | hm
      · left
        refine ⟨j / 2, by omega, by omega, ?_⟩
        have he : t j = s (j / 2) := by
          conv_lhs => rw [show j = 2 * (j / 2) by omega]
          exact ht_even (j / 2)
        exact he.symm.trans hjx
      · right
        refine ⟨j / 2, by omega, ?_⟩
        have he : t j = (s (j / 2) + s (j / 2 + 1)) / 2 := by
          conv_lhs => rw [show j = 2 * (j / 2) + 1 by omega]
          exact ht_odd (j / 2)
        exact he.symm.trans hjx
  have hmid_pos : ∀ i, i ≤ A.card → 0 < (s i + s (i + 1)) / 2 := by
    intro i hi
    have hsi : 0 ≤ s i := by rw [← hs0]; exact hs_le 0 i (Nat.zero_le _) (by omega)
    have hlt : s i < s (i + 1) := hs_lt i (i + 1) (by omega) (by omega)
    linarith
  have hmid_lt_one : ∀ i, i ≤ A.card → (s i + s (i + 1)) / 2 < 1 := by
    intro i hi
    have hlt : s i < s (i + 1) := hs_lt i (i + 1) (by omega) (by omega)
    have hle : s (i + 1) ≤ 1 := by
      rw [← hs1]; exact hs_le (i + 1) (A.card + 1) (by omega) (le_refl _)
    linarith
  have hSsub : ((A ∪ B : Finset ℝ) : Set ℝ) ⊆ Set.Ioo (0 : ℝ) 1 := by
    rw [Finset.coe_union]
    intro x hx
    rw [Set.mem_union] at hx
    rcases hx with hxA | hxB
    · exact hA hxA
    · rw [Finset.mem_coe, hBmem] at hxB
      obtain ⟨i, hi, hix⟩ := hxB
      rw [← hix]
      exact ⟨hmid_pos i hi, hmid_lt_one i hi⟩
  have hmid_inj : ∀ i j, i ≤ A.card → j ≤ A.card →
      (s i + s (i + 1)) / 2 = (s j + s (j + 1)) / 2 → i = j := by
    intro i j hi hj hij
    rcases lt_trichotomy i j with h | h | h
    · exfalso
      have a : s i < s (i + 1) := hs_lt i (i + 1) (by omega) (by omega)
      have b : s (i + 1) ≤ s j := hs_le (i + 1) j (by omega) (by omega)
      have c : s j < s (j + 1) := hs_lt j (j + 1) (by omega) (by omega)
      linarith
    · exact h
    · exfalso
      have a : s j < s (j + 1) := hs_lt j (j + 1) (by omega) (by omega)
      have b : s (j + 1) ≤ s i := hs_le (j + 1) i (by omega) (by omega)
      have c : s i < s (i + 1) := hs_lt i (i + 1) (by omega) (by omega)
      linarith
  have hdisj : Disjoint A B := by
    refine Finset.disjoint_left.mpr ?_
    intro a ha hb
    rw [hAmem] at ha
    rw [hBmem] at hb
    obtain ⟨k, hk1, hk2, hka⟩ := ha
    obtain ⟨i, hi, hib⟩ := hb
    have hki : s k = (s i + s (i + 1)) / 2 := hka.trans hib.symm
    by_cases hle : k ≤ i
    · have h1 : s k ≤ s i := hs_le k i hle (by omega)
      have h2 : s i < (s i + s (i + 1)) / 2 := by
        have a : s i < s (i + 1) := hs_lt i (i + 1) (by omega) (by omega); linarith
      linarith
    · have h1 : (s i + s (i + 1)) / 2 < s (i + 1) := by
        have a : s i < s (i + 1) := hs_lt i (i + 1) (by omega) (by omega); linarith
      have h2 : s (i + 1) ≤ s k := hs_le (i + 1) k (by omega) (by omega)
      linarith
  have hBcard : B.card = A.card + 1 := by
    rw [hBdef]
    have hinj : Set.InjOn (fun i => (s i + s (i + 1)) / 2) (↑(Finset.range (A.card + 1))) := by
      intro i hi j hj hij
      exact hmid_inj i j (by simp only [Finset.mem_coe, Finset.mem_range] at hi; omega)
        (by simp only [Finset.mem_coe, Finset.mem_range] at hj; omega) hij
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hcard : (A ∪ B).card + 1 = 2 * (A.card + 1) := by
    rw [Finset.card_union_of_disjoint hdisj, hBcard]
    omega
  have hcard' : (A ∪ B).card = 2 * (A.card + 1) - 1 := by omega
  have hs1' : t ((A ∪ B).card + 1) = 1 := by rw [hcard]; exact ht_q
  have hs_mono' : StrictMonoOn t (Set.Icc 0 ((A ∪ B).card + 1)) := by
    rw [hcard]; exact hmono
  have hs_int' : ((A ∪ B : Finset ℝ) : Set ℝ) = t '' Set.Icc 1 (A ∪ B).card := by
    rw [Finset.coe_union, hcard']; exact hSunion
  obtain ⟨-, -, -, hAB_sum, -, hclause⟩ :=
    statopia_math_node_4221689064_d3ddf0ec (A ∪ B) hSsub t ht_zero hs1' hs_mono' hs_int'
  have hpiece : pieceLengths (A ∪ B) =
      (List.range (2 * (A.card + 1))).map (fun i => t (i + 1) - t i) :=
    hclause (2 * (A.card + 1)) t (by omega) ht_zero ht_q hmono hinterior
      (by rw [Finset.coe_union]; exact hSunion)
  have hflat : pieceLengths (A ∪ B)
      = ((pieceLengths A).map (fun a => a / 2)).flatMap (fun a => [a, a]) := by
    have hg_even : ∀ i, t (2 * i + 1) - t (2 * i) = (s (i + 1) - s i) / 2 := by
      intro i
      rw [ht_odd i, ht_even i]
      ring
    have hg_odd : ∀ i, t (2 * i + 2) - t (2 * i + 1) = (s (i + 1) - s i) / 2 := by
      intro i
      have h2 : t (2 * i + 2) = s (i + 1) := by
        have he : 2 * i + 2 = 2 * (i + 1) := by omega
        rw [he, ht_even (i + 1)]
      rw [h2, ht_odd i]
      ring
    have hgen : ∀ {α : Type} (l : List α) (h : α → ℝ),
        l.flatMap (fun i => [h i, h i]) = (l.map h).flatMap (fun a => [a, a]) := by
      intro α l h
      induction l with
      | nil => simp
      | cons a t ih => simp [ih]
    have hpair : ∀ N, (List.range (2 * N)).map (fun i => t (i + 1) - t i)
        = (List.range N).flatMap (fun i =>
            [t (2 * i + 1) - t (2 * i), t (2 * i + 2) - t (2 * i + 1)]) := by
      intro N
      induction N with
      | zero => simp
      | succ k ih =>
        have hL : (List.range (2 * (k + 1))).map (fun i => t (i + 1) - t i)
            = (List.range (2 * k)).map (fun i => t (i + 1) - t i)
              ++ [t (2 * k + 1) - t (2 * k), t (2 * k + 2) - t (2 * k + 1)] := by
          rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega]
          rw [show List.range (2 * k + 1 + 1) = List.range (2 * k) ++ [2 * k, 2 * k + 1] from by
                simp [List.range_succ]]
          simp
        have hR : (List.range (k + 1)).flatMap (fun i =>
              [t (2 * i + 1) - t (2 * i), t (2 * i + 2) - t (2 * i + 1)])
            = (List.range k).flatMap (fun i =>
              [t (2 * i + 1) - t (2 * i), t (2 * i + 2) - t (2 * i + 1)])
              ++ [t (2 * k + 1) - t (2 * k), t (2 * k + 2) - t (2 * k + 1)] := by
          rw [show List.range (k + 1) = List.range k ++ [k] from by simp [List.range_succ]]
          simp [List.flatMap_append]
        rw [hL, hR, ih]
    have hRHS : (pieceLengths A).map (fun a => a / 2)
        = (List.range (A.card + 1)).map (fun i => (s (i + 1) - s i) / 2) := by
      rw [hA_lens, List.map_map]
      rw [show (fun a => a / 2) ∘ (fun i => s (i + 1) - s i)
            = (fun i => (s (i + 1) - s i) / 2) from by
          funext i
          simp [Function.comp_apply]]
    rw [hpiece, hpair (A.card + 1)]
    simp only [hg_even, hg_odd]
    have hstep : (List.range (A.card + 1)).flatMap
        (fun i => [(s (i + 1) - s i) / 2, (s (i + 1) - s i) / 2])
        = ((List.range (A.card + 1)).map (fun i => (s (i + 1) - s i) / 2)).flatMap
            (fun a => [a, a]) :=
      hgen (List.range (A.card + 1)) (fun i => (s (i + 1) - s i) / 2)
    rw [hstep, hRHS]
  exact ⟨hflat, hAB_sum⟩
  /- @proof-region region.target-node.session.31db2d32ef5be3a2 end -/

end LiuBangXiangYu
