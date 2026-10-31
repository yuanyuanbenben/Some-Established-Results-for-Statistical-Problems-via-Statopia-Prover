import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base

open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_2798148667_8bcde5b0 : ∀ (q : ℕ) (hq : 1 ≤ q) (a : Fin q → ℝ)
    (ha_pos : ∀ i, 0 < a i) (ha_sum : ∑ i, a i = 1),
    ∃ I J : Finset (Fin q),
      Disjoint I J ∧ I ∪ J ≠ ∅ ∧
        |∑ i ∈ I, a i - ∑ j ∈ J, a j| ≤ 1 / ((2 : ℝ) ^ q - 1) := by
  /- @proof-region region.target-node.session.c970cae0e418c63c begin -/
  intro q hq a ha_pos ha_sum
  have hpow : 2 ≤ 2 ^ q := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hq
    rw [hk, pow_add, pow_one]
    have hk' : 0 < 2 ^ k := pow_pos (by norm_num) k
    omega
  have hpos_sum : ∀ S : Finset (Fin q), 0 ≤ ∑ i ∈ S, a i :=
    fun S => Finset.sum_nonneg (fun i _ => le_of_lt (ha_pos i))
  have hle_sum : ∀ S : Finset (Fin q), (∑ i ∈ S, a i) ≤ 1 := by
    intro S
    have h : (∑ i ∈ S, a i) ≤ ∑ i, a i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun i _ _ => le_of_lt (ha_pos i))
    rwa [ha_sum] at h
  set N : ℕ := 2 ^ q with hN
  set m : ℕ := N - 1 with hm
  have hm_pos : 0 < m := by rw [hm]; omega
  have hm_cast : (m : ℝ) = (2 : ℝ) ^ q - 1 := by
    rw [hm, hN, Nat.cast_sub (show (1 : ℕ) ≤ 2 ^ q by omega), Nat.cast_pow]
    norm_num
  have bounds : ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      ((min (Nat.floor (x * m)) (m - 1) : ℕ) : ℝ) ≤ x * m ∧
      x * m ≤ ((min (Nat.floor (x * m)) (m - 1) : ℕ) : ℝ) + 1 := by
    intro x hx0 hx1
    refine ⟨?_, ?_⟩
    · exact le_trans (Nat.cast_le.mpr (min_le_left _ _))
        (Nat.floor_le (mul_nonneg hx0 (Nat.cast_nonneg m)))
    · have hxm : x * m ≤ (m : ℝ) := by
        have h := mul_le_mul_of_nonneg_right hx1 (Nat.cast_nonneg m)
        simpa using h
      rcases le_total (Nat.floor (x * m)) (m - 1) with hfl | hfl
      · rw [min_eq_left hfl]
        have h := Nat.lt_floor_add_one (x * m)
        linarith
      · rw [min_eq_right hfl]
        have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
          rw [Nat.cast_sub (show (1 : ℕ) ≤ m by omega)]
          norm_num
        rw [hcast]
        linarith
  have floor_lem : ∀ x y : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 →
      min (Nat.floor (x * m)) (m - 1) = min (Nat.floor (y * m)) (m - 1) →
      |x - y| ≤ 1 / (m : ℝ) := by
    intro x y hx0 hx1 hy0 hy1 hk
    obtain ⟨hxlo, hxhi⟩ := bounds x hx0 hx1
    obtain ⟨hylo, hyhi⟩ := bounds y hy0 hy1
    have hc : ((min (Nat.floor (x * m)) (m - 1) : ℕ) : ℝ)
        = ((min (Nat.floor (y * m)) (m - 1) : ℕ) : ℝ) := by rw [hk]
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm_pos
    have hkey : |x * m - y * m| ≤ 1 := by
      rw [abs_sub_le_iff]
      constructor <;> linarith
    have h2 : |x * m - y * m| = |x - y| * m := by
      rw [← sub_mul, abs_mul, abs_of_nonneg (le_of_lt hmR)]
    rw [h2] at hkey
    exact (le_div_iff₀ hmR).mpr hkey
  let g : Finset (Fin q) → Fin m := fun S =>
    ⟨min (Nat.floor ((∑ i ∈ S, a i) * m)) (m - 1),
      Nat.lt_of_le_of_lt (min_le_right _ _) (by omega : m - 1 < m)⟩
  have hcard : (Finset.univ : Finset (Fin m)).card
      < (Finset.univ : Finset (Finset (Fin q))).card := by
    simp only [Finset.card_univ, Fintype.card_fin, Fintype.card_finset]
    rw [hm, hN]
    omega
  obtain ⟨S, _, T, _, hSne, hg⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard (f := g)
      (fun x _ => Finset.mem_univ (g x))
  have hk : min (Nat.floor ((∑ i ∈ S, a i) * m)) (m - 1)
      = min (Nat.floor ((∑ i ∈ T, a i) * m)) (m - 1) := by
    simpa only [g] using congrArg Fin.val hg
  have hb : |(∑ i ∈ S, a i) - (∑ i ∈ T, a i)| ≤ 1 / (m : ℝ) :=
    floor_lem _ _ (hpos_sum S) (hle_sum S) (hpos_sum T) (hle_sum T) hk
  have split : ∀ U V : Finset (Fin q),
      (∑ i ∈ U \ V, a i) + (∑ i ∈ U ∩ V, a i) = ∑ i ∈ U, a i := by
    intro U V
    have hdisj : Disjoint (U \ V) (U ∩ V) :=
      Finset.disjoint_left.mpr (fun x hx hy => by
        rw [Finset.mem_sdiff] at hx
        rw [Finset.mem_inter] at hy
        exact hx.2 hy.2)
    rw [← Finset.sum_union hdisj]
    apply Finset.sum_congr _ (fun x _ => rfl)
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hdiff : (∑ i ∈ S \ T, a i) - (∑ i ∈ T \ S, a i)
      = (∑ i ∈ S, a i) - (∑ i ∈ T, a i) := by
    have hS := split S T
    have hT := split T S
    rw [Finset.inter_comm T S] at hT
    linarith
  refine ⟨S \ T, T \ S, ?_, ?_, ?_⟩
  · exact Finset.disjoint_left.mpr (fun x hx hy => by
      rw [Finset.mem_sdiff] at hx hy
      exact hx.2 hy.1)
  · intro hunion
    have hST : S ⊆ T := by
      intro x hx
      by_contra hxT
      have hx' : x ∈ S \ T ∪ T \ S :=
        Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hx, hxT⟩))
      rw [hunion] at hx'
      simp at hx'
    have hTS : T ⊆ S := by
      intro x hx
      by_contra hxS
      have hx' : x ∈ S \ T ∪ T \ S :=
        Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hx, hxS⟩))
      rw [hunion] at hx'
      simp at hx'
    exact hSne (Finset.Subset.antisymm hST hTS)
  · have htarget : |(∑ i ∈ S \ T, a i) - (∑ i ∈ T \ S, a i)|
        ≤ 1 / ((2 : ℝ) ^ q - 1) := by
      rw [hdiff, ← hm_cast]
      exact hb
    exact htarget
  /- @proof-region region.target-node.session.c970cae0e418c63c end -/

end LiuBangXiangYu
