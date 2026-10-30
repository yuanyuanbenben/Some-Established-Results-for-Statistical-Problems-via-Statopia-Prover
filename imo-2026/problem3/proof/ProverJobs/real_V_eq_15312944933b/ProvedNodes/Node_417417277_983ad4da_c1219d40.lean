import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_4221689064_d3ddf0ec_fbe161c8
open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_417417277_983ad4da : ∀ (n : ℕ) (hn : 1 ≤ n) (d : ℝ) (hd : 0 < d) (T : Finset ℝ)
    (hT : (T : Set ℝ) ⊆ Set.Ioo (0 : ℝ) 1) (blocks : List (List ℝ))
    (hflat : blocks.flatten = pieceLengths T)
    (hsums : blocks.map (fun b => b.sum) = (List.range (n + 1)).map (fun i => d * (2 : ℝ) ^ i)),
    ∃ (p : Fin (pieceLengths T).length → ℝ)
      (o : Fin (pieceLengths T).length → Fin (n + 1)),
      (∀ j, 0 < p j) ∧
        (∀ i : Fin (n + 1),
          (∑ j ∈ Finset.univ.filter (fun j : Fin (pieceLengths T).length => o j = i), p j)
            = (2 : ℝ) ^ (i : ℕ)) := by
  /- @proof-region region.target-node.session.4bddf19eaa00e79f begin -/
  intro n hn d hd T hT blocks hflat hsums
  have hblocks_len : blocks.length = n + 1 := by
    have h := congrArg List.length hsums
    simpa using h
  have hblock_sum_pos : ∀ l ∈ blocks, 0 < l.sum := by
    intro l hl
    have hmem : l.sum ∈ blocks.map (fun b => b.sum) := List.mem_map.mpr ⟨l, hl, rfl⟩
    rw [hsums] at hmem
    simp only [List.mem_map, List.mem_range] at hmem
    obtain ⟨i, _hi, hgi⟩ := hmem
    rw [← hgi]
    positivity
  have hblock_ne : ∀ l ∈ blocks, 1 ≤ l.length := by
    intro l hl
    have hpos := hblock_sum_pos l hl
    cases l with
    | nil => exact absurd hpos (by simp)
    | cons a t => exact Nat.succ_le_succ (Nat.zero_le t.length)
  have hlen_sum : blocks.length ≤ (blocks.map List.length).sum := by
    have key : ∀ (bs : List (List ℝ)),
        (∀ l ∈ bs, 1 ≤ l.length) → bs.length ≤ (bs.map List.length).sum := by
      intro bs
      induction bs with
      | nil => intro _; simp
      | cons b bs ih =>
        intro hb
        have h1 : 1 ≤ b.length := hb b (by simp)
        have h2 : ∀ l ∈ bs, 1 ≤ l.length := fun l hl => hb l (by simp [hl])
        have h3 := ih h2
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        omega
    exact key blocks hblock_ne
  have hm_ge : n + 1 ≤ (pieceLengths T).length := by
    rw [← hflat, List.length_flatten, ← hblocks_len]
    exact hlen_sum
  let o : Fin (pieceLengths T).length → Fin (n + 1) :=
    fun j => ⟨min j.val n, Nat.lt_succ_of_le (Nat.min_le_right j.val n)⟩
  let c : Fin (n + 1) → ℕ :=
    fun i => (Finset.univ.filter (fun k : Fin (pieceLengths T).length => o k = i)).card
  have hfiber_pos : ∀ i : Fin (n + 1), 0 < c i := by
    intro i
    change 0 < (Finset.univ.filter (fun k : Fin (pieceLengths T).length => o k = i)).card
    apply Finset.card_pos.mpr
    refine ⟨⟨i.val, lt_of_lt_of_le i.isLt hm_ge⟩, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    apply Fin.ext
    show min i.val n = i.val
    exact Nat.min_eq_left (Nat.le_of_lt_succ i.isLt)
  let p : Fin (pieceLengths T).length → ℝ := fun j => (2:ℝ)^((o j).val) / (c (o j) : ℝ)
  refine ⟨p, o, ?_, ?_⟩
  · intro j
    change 0 < (2:ℝ)^((o j).val) / (c (o j) : ℝ)
    apply div_pos
    · positivity
    · exact_mod_cast hfiber_pos (o j)
  · intro i
    change (∑ j ∈ Finset.univ.filter (fun j : Fin (pieceLengths T).length => o j = i),
        (2:ℝ)^((o j).val) / (c (o j) : ℝ)) = (2:ℝ)^(i:ℕ)
    have hcongr : (∑ j ∈ Finset.univ.filter (fun j : Fin (pieceLengths T).length => o j = i),
        (2:ℝ)^((o j).val) / (c (o j) : ℝ))
        = ∑ j ∈ Finset.univ.filter (fun j : Fin (pieceLengths T).length => o j = i),
        (2:ℝ)^(i.val) / (c i : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      rw [hj]
    rw [hcongr, Finset.sum_const, nsmul_eq_mul]
    have hc : (c i : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (hfiber_pos i))
    rw [mul_comm, div_mul_cancel₀ _ hc]
  /- @proof-region region.target-node.session.4bddf19eaa00e79f end -/

end LiuBangXiangYu
