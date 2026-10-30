import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_2583178723_e50b326f_abb8efa0
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_2999225285_90342243_ea48111e
open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_258886546_cb96d69f : ∀ (n : ℕ) (hn : 1 ≤ n) (d : ℝ) (hd : 0 < d)
    (L : List ℝ) (hLpos : ∀ x ∈ L, 0 < x)
    (blocks : List (List ℝ))
    (hflat : blocks.flatten = L)
    (hsums : blocks.map (fun b => b.sum) = (List.range (n + 1)).map (fun i => d * (2 : ℝ) ^ i))
    (hm_le : L.length ≤ 2 * n + 1),
    (∑ j ∈ Finset.range (((L.mergeSort (fun x1 x2 => decide (x1 ≥ x2))).length + 1) / 2),
        ((if h : 2 * j < (L.mergeSort (fun x1 x2 => decide (x1 ≥ x2))).length
            then (L.mergeSort (fun x1 x2 => decide (x1 ≥ x2))).get ⟨2 * j, h⟩ else 0)
          - (if h : 2 * j + 1 < (L.mergeSort (fun x1 x2 => decide (x1 ≥ x2))).length
            then (L.mergeSort (fun x1 x2 => decide (x1 ≥ x2))).get ⟨2 * j + 1, h⟩ else 0))) ≥ d := by
  /- @proof-region region.target-node.session.dd1ff47417f9d7ac begin -/
  intro n hn d hd L hLpos blocks hflat hsums hm_le
  set srt : List ℝ := L.mergeSort (fun x1 x2 => decide (x1 ≥ x2)) with hsrt
  have hperm : srt.Perm L := by rw [hsrt]; exact List.mergeSort_perm L _
  have hlen : srt.length = L.length := hperm.length_eq
  have hmle : srt.length ≤ 2 * n + 1 := by rw [hlen]; exact hm_le
  have hblen : blocks.length = n + 1 := by
    have h := congrArg List.length hsums
    simpa [List.length_map] using h
  obtain ⟨o₁, ho₁⟩ := statopia_math_node_2583178723_e50b326f L blocks hflat
  have hget : ∀ {α : Type} (l : List α) (i : ℕ) (h : i < l.length), l[i] = l.get ⟨i, h⟩ := by
    intro α l i h
    exact (List.get_eq_getElem (l := l) (i := ⟨i, h⟩)).symm
  have hentry : ∀ {α : Type} {l₁ l₂ : List α} (h : l₁ = l₂) (i : ℕ) (h₁ : i < l₁.length)
      (h₂ : i < l₂.length), l₁[i] = l₂[i] := by
    intro α l₁ l₂ h i h₁ h₂
    cases h
    rfl
  have hblk : ∀ k : Fin blocks.length, (blocks.get k).sum = d * 2 ^ (k : ℕ) := by
    intro k
    have hA : k.1 < (blocks.map (fun b => b.sum)).length := by rw [List.length_map]; exact k.2
    have hB : k.1 < ((List.range (n + 1)).map (fun i => d * 2 ^ i)).length := by
      rw [List.length_map, List.length_range, ← hblen]; exact k.2
    have h2 : (blocks.map (fun b => b.sum))[k.1]
        = ((List.range (n + 1)).map (fun i => d * 2 ^ i))[k.1] := hentry hsums k.1 hA hB
    simp only [List.getElem_map, List.getElem_range] at h2
    rwa [hget blocks k.1 k.2] at h2
  have key : ∀ (bs : List (List ℝ)) (b : List ℝ), b ∈ bs → b ≠ [] → 0 < bs.flatten.length := by
    intro bs
    induction bs with
    | nil => intro b hb _; simp at hb
    | cons c cs ih =>
      intro b hb hbne
      simp only [List.mem_cons] at hb
      rw [List.flatten_cons, List.length_append]
      rcases hb with hbc | hb'
      · have hc : c ≠ [] := by rw [← hbc]; exact hbne
        have hc0 : 0 < c.length := by
          cases c with
          | nil => exact absurd rfl hc
          | cons e es => simp
        omega
      · have := ih b hb' hbne
        omega
  have hm1 : 1 ≤ srt.length := by
    rw [hlen, ← hflat]
    have h0 : 0 < blocks.length := by omega
    have hks : (blocks.get ⟨0, h0⟩).sum = d * 2 ^ (0 : ℕ) := hblk ⟨0, h0⟩
    have hpos : 0 < (blocks.get ⟨0, h0⟩).sum := by
      rw [hks]; positivity
    have hne : blocks.get ⟨0, h0⟩ ≠ [] := by
      intro hh; rw [hh] at hpos; simp at hpos
    have := key blocks (blocks.get ⟨0, h0⟩) (List.get_mem blocks ⟨0, h0⟩) hne
    omega
  let x : Fin srt.length → ℝ := fun j => srt.get j / d
  have hdne : d ≠ 0 := ne_of_gt hd
  have hp_pos : ∀ j : Fin srt.length, 0 < x j := by
    intro j
    have hmem : srt.get j ∈ L := (hperm.mem_iff).mp (List.get_mem srt j)
    exact div_pos (hLpos _ hmem) hd
  have hsorted : List.Pairwise (fun a b : ℝ => decide (a ≥ b) = true) srt := by
    have h := List.sorted_mergeSort (le := fun x1 x2 : ℝ => decide (x1 ≥ x2))
      (by
        intro a b c hab hbc
        exact decide_eq_true (by
          have hab' : a ≥ b := of_decide_eq_true hab
          have hbc' : b ≥ c := of_decide_eq_true hbc
          linarith))
      (by
        intro a b
        by_cases h : a ≥ b
        · simp [h]
        · have h' : b ≥ a := le_of_lt (lt_of_not_ge h)
          simp [h, h'])
      L
    simpa [hsrt] using h
  have hx_sorted : ∀ j k : Fin srt.length, (j : ℕ) ≤ (k : ℕ) → x k ≤ x j := by
    intro j k hjk
    letI : Std.Refl (fun a b : ℝ => a ≥ b) := ⟨fun a => le_refl a⟩
    have hs : List.Pairwise (fun a b : ℝ => a ≥ b) srt :=
      List.Pairwise.imp (fun hab => of_decide_eq_true hab) hsorted
    have hle : srt.get k ≤ srt.get j := List.Pairwise.rel_get_of_le hs hjk
    exact div_le_div_of_nonneg_right hle (le_of_lt hd)
  let o : Fin srt.length → Fin (n + 1) := fun j => ⟨(o₁ j).1, by rw [← hblen]; exact (o₁ j).2⟩
  have hsum : ∀ i : Fin (n + 1),
      (∑ j ∈ Finset.univ.filter (fun j : Fin srt.length => o j = i), x j)
        = (2 : ℝ) ^ (i : ℕ) := by
    intro i
    let i' : Fin blocks.length := ⟨i.1, by omega⟩
    have hcond : ∀ j : Fin srt.length, (o j = i) ↔ (o₁ j = i') := by
      intro j
      constructor
      · intro h
        have h1 : (o j).val = i.val := congrArg Fin.val h
        exact Fin.ext h1
      · intro h
        have h1 : (o₁ j).val = (i').val := congrArg Fin.val h
        exact Fin.ext h1
    have h1 : (∑ j ∈ Finset.univ.filter (fun j : Fin srt.length => o j = i), x j)
        = ∑ j ∈ Finset.univ, (if o₁ j = i' then srt.get j / d else 0) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : o j = i
      · rw [if_pos h, if_pos ((hcond j).mp h)]
      · rw [if_neg h, if_neg (fun h2 => h ((hcond j).mpr h2))]
    have h2 : (∑ j ∈ Finset.univ, (if o₁ j = i' then srt.get j / d else 0))
        = (∑ j ∈ Finset.univ.filter (fun j : Fin srt.length => o₁ j = i'), srt.get j) / d := by
      rw [Finset.sum_div, Finset.sum_filter]
    rw [h1, h2, ho₁ i', hblk i']
    have hii : ((i' : ℕ)) = (i : ℕ) := rfl
    rw [hii]
    field_simp

  have hmain := statopia_math_node_2999225285_90342243 n hn srt.length hm1 x hp_pos o hsum hmle x
    hx_sorted ⟨Equiv.refl (Fin srt.length), fun j => rfl⟩
  have hsplit : (∑ j ∈ Finset.range ((srt.length + 1) / 2),
      ((if h : 2 * j < srt.length then x ⟨2 * j, h⟩ else 0)
        - (if h : 2 * j + 1 < srt.length then x ⟨2 * j + 1, h⟩ else 0)))
      = (∑ j ∈ Finset.range ((srt.length + 1) / 2),
      ((if h : 2 * j < srt.length then srt.get ⟨2 * j, h⟩ else 0)
        - (if h : 2 * j + 1 < srt.length then srt.get ⟨2 * j + 1, h⟩ else 0))) / d := by
    have hcongr : (∑ j ∈ Finset.range ((srt.length + 1) / 2),
        ((if h : 2 * j < srt.length then x ⟨2 * j, h⟩ else 0)
          - (if h : 2 * j + 1 < srt.length then x ⟨2 * j + 1, h⟩ else 0)))
        = ∑ j ∈ Finset.range ((srt.length + 1) / 2),
        ((if h : 2 * j < srt.length then srt.get ⟨2 * j, h⟩ else 0)
          - (if h : 2 * j + 1 < srt.length then srt.get ⟨2 * j + 1, h⟩ else 0)) / d := by
      apply Finset.sum_congr rfl
      intro j _
      have hAj : (if h : 2 * j < srt.length then x ⟨2 * j, h⟩ else 0)
          = (if h : 2 * j < srt.length then srt.get ⟨2 * j, h⟩ else 0) / d := by
        by_cases h : 2 * j < srt.length
        · rw [dif_pos h]
          rw [dif_pos h]
        · rw [dif_neg h]
          rw [dif_neg h, zero_div]
      have hBj : (if h : 2 * j + 1 < srt.length then x ⟨2 * j + 1, h⟩ else 0)
          = (if h : 2 * j + 1 < srt.length then srt.get ⟨2 * j + 1, h⟩ else 0) / d := by
        by_cases h : 2 * j + 1 < srt.length
        · rw [dif_pos h]
          rw [dif_pos h]
        · rw [dif_neg h]
          rw [dif_neg h, zero_div]
      rw [hAj, hBj, ← sub_div]
    rw [hcongr, ← Finset.sum_div]
  rw [hsplit] at hmain
  have h2 : (∑ j ∈ Finset.range ((srt.length + 1) / 2),
      ((if h : 2 * j < srt.length then srt.get ⟨2 * j, h⟩ else 0)
        - (if h : 2 * j + 1 < srt.length then srt.get ⟨2 * j + 1, h⟩ else 0))) / d * d
      = ∑ j ∈ Finset.range ((srt.length + 1) / 2),
      ((if h : 2 * j < srt.length then srt.get ⟨2 * j, h⟩ else 0)
        - (if h : 2 * j + 1 < srt.length then srt.get ⟨2 * j + 1, h⟩ else 0)) := by
    field_simp

  have h3 := mul_le_mul_of_nonneg_right hmain (le_of_lt hd)
  rw [h2] at h3
  simpa using h3

  /- @proof-region region.target-node.session.dd1ff47417f9d7ac end -/

end LiuBangXiangYu
