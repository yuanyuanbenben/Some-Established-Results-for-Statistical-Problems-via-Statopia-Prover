import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_247222274_f4a96af6_4b656963
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_2999225285_90342243_ea48111e
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_417417277_983ad4da_c1219d40
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_4221689064_d3ddf0ec_fbe161c8
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_781820246_3d08e56a_6bdd9b59
open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_3641882566_571fb3c0 : ∀ (n : ℕ) (hn : 0 < n),
    let d : ℝ := 1 / ((2 : ℝ) ^ (n + 1) - 1)
    let A0 : Finset ℝ := (Finset.Icc 1 n).image (fun j : ℕ => d * ((2 : ℝ) ^ j - 1))
    AdmissibleMark n A0 ∧
      (∀ B : Finset ℝ, AdmissibleMark n B → Disjoint A0 B → L A0 B ≥ (1 + d) / 2) := by
  /- @proof-region region.target-node.session.441252101edcea9c begin -/
  intro n hn
  intro d A0
  have hdval : d = 1 / ((2 : ℝ) ^ (n + 1) - 1) := rfl
  have hA0val : A0 = (Finset.Icc 1 n).image (fun j : ℕ => d * ((2 : ℝ) ^ j - 1)) := rfl
  have hpow1 : ∀ t : ℕ, (1 : ℝ) ≤ (2 : ℝ) ^ t := by
    intro t
    induction t with
    | zero => simp
    | succ s ih => rw [pow_succ]; nlinarith
  have hmono : ∀ a b : ℕ, a ≤ b → (2 : ℝ) ^ a ≤ (2 : ℝ) ^ b := by
    intro a b hab
    obtain ⟨c, hc⟩ := Nat.le.dest hab
    rw [← hc, pow_add]
    simpa using mul_le_mul_of_nonneg_left (hpow1 c) (le_of_lt (pow_pos (by norm_num : (0 : ℝ) < 2) a))
  have h2succ : (1 : ℝ) < (2 : ℝ) ^ (n + 1) := by
    have h : (2 : ℝ) ^ (n + 1) = (2 : ℝ) ^ n * 2 := by rw [pow_succ]
    have hn' : (1 : ℝ) ≤ (2 : ℝ) ^ n := hpow1 n
    nlinarith [h, hn']
  have hden_pos : 0 < (2 : ℝ) ^ (n + 1) - 1 := by linarith
  have hdpos : 0 < d := by rw [hdval]; exact div_pos one_pos hden_pos
  have hA0_sub : (A0 : Set ℝ) ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro x hx
    simp only [hA0val, Finset.mem_coe, Finset.mem_image, Finset.mem_Icc] at hx
    obtain ⟨j, ⟨hj1, hjn⟩, rfl⟩ := hx
    refine ⟨?_, ?_⟩
    · have h2j : (1 : ℝ) < (2 : ℝ) ^ j := by
        have hh := hmono 1 j hj1
        norm_num at hh
        linarith
      exact mul_pos hdpos (by linarith)
    · have h2j : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ n := hmono j n hjn
      have h2n_lt : (2 : ℝ) ^ n < (2 : ℝ) ^ (n + 1) := by
        rw [pow_succ]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) n]
      have hlt : (2 : ℝ) ^ j - 1 < (2 : ℝ) ^ (n + 1) - 1 := by
        have : (2 : ℝ) ^ j < (2 : ℝ) ^ (n + 1) := lt_of_le_of_lt h2j h2n_lt
        linarith
      calc d * ((2 : ℝ) ^ j - 1) = (1 / ((2 : ℝ) ^ (n + 1) - 1)) * ((2 : ℝ) ^ j - 1) := by rw [hdval]
        _ = ((2 : ℝ) ^ j - 1) / ((2 : ℝ) ^ (n + 1) - 1) := by ring
        _ < 1 := by rw [div_lt_one hden_pos]; exact hlt
  have hcard : (Finset.Icc 1 n).card ≤ n := by
    have h_eq : Finset.Icc 1 n = (Finset.range n).image (fun k => k + 1) := by
      ext m
      constructor
      · intro hm
        rw [Finset.mem_Icc] at hm
        obtain ⟨hm1, hmn⟩ := hm
        rw [Finset.mem_image]
        exact ⟨m - 1, by rw [Finset.mem_range]; omega, by omega⟩
      · intro hm
        rw [Finset.mem_image] at hm
        obtain ⟨k, hk, rfl⟩ := hm
        rw [Finset.mem_range] at hk
        rw [Finset.mem_Icc]
        omega
    rw [h_eq]
    calc ((Finset.range n).image (fun k => k + 1)).card
        ≤ (Finset.range n).card := Finset.card_image_le
      _ = n := Finset.card_range n
  have hA0_card : A0.card ≤ n := by
    rw [hA0val]
    exact le_trans (Finset.card_image_le (s := Finset.Icc 1 n) (f := fun j : ℕ => d * ((2 : ℝ) ^ j - 1))) hcard
  have h2lt : ∀ a b : ℕ, a < b → (2 : ℝ) ^ a < (2 : ℝ) ^ b := by
    intro a b hab
    have h1 : (2 : ℝ) ^ a < (2 : ℝ) ^ (a + 1) := by
      rw [pow_succ]
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) a]
    have h2 : (2 : ℝ) ^ (a + 1) ≤ (2 : ℝ) ^ b := hmono (a + 1) b (by omega)
    linarith
  have h2inj : ∀ a b : ℕ, (2 : ℝ) ^ a = (2 : ℝ) ^ b → a = b := by
    intro a b hab
    rcases lt_trichotomy a b with h | h | h
    · exact absurd hab (ne_of_lt (h2lt a b h))
    · exact h
    · exact absurd hab.symm (ne_of_lt (h2lt b a h))
  have hginj : ∀ a b : ℕ, d * ((2 : ℝ) ^ a - 1) = d * ((2 : ℝ) ^ b - 1) → a = b := by
    intro a b hab
    have hd0 : d ≠ 0 := ne_of_gt hdpos
    have h1 : (2 : ℝ) ^ a - 1 = (2 : ℝ) ^ b - 1 := mul_left_cancel₀ hd0 hab
    exact h2inj a b (by linarith)
  have hIcc_card : (Finset.Icc 1 n).card = n := by
    have hge : n ≤ (Finset.Icc 1 n).card := by
      by_contra h
      rw [not_le] at h
      obtain ⟨x, hx, y, hy, hne, hxy⟩ :=
        Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := Finset.range n)
          (t := Finset.Icc 1 n) (f := fun k : ℕ => k + 1)
          (by rw [Finset.card_range]; exact h) (by
            intro z hz
            simp only [Finset.mem_coe, Finset.mem_range] at hz
            simp only [Finset.mem_coe]
            exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      omega
    exact le_antisymm hcard hge
  have hle : (Finset.Icc 1 n).card ≤ A0.card := by
    by_contra h
    rw [not_le] at h
    obtain ⟨x, hx, y, hy, hne, hxy⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := Finset.Icc 1 n) (t := A0)
        (f := fun j : ℕ => d * ((2 : ℝ) ^ j - 1)) h (by
          intro z hz
          simp only [Finset.mem_coe] at hz
          simp only [hA0val, Finset.mem_coe]
          exact Finset.mem_image.mpr ⟨z, hz, rfl⟩)
    exact hne (hginj x y hxy)
  have hcard_eq : A0.card = n := le_antisymm hA0_card (by rw [← hIcc_card]; exact hle)
  refine ⟨⟨hA0_sub, hA0_card⟩, ?_⟩
  intro B hB hdisj
  obtain ⟨hBsub, hBcard⟩ := hB
  have hTsub : ((A0 ∪ B : Finset ℝ) : Set ℝ) ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro x hx
    simp only [Finset.mem_coe, Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact hA0_sub hx
    · exact hBsub hx
  have hTcard : (A0 ∪ B).card ≤ 2 * n := by
    calc (A0 ∪ B).card ≤ A0.card + B.card := Finset.card_union_le A0 B
      _ ≤ n + n := add_le_add hA0_card hBcard
      _ = 2 * n := by ring
  have hn1 : 1 ≤ n := by omega
  have hne : ((2 : ℝ) ^ (n + 1) - 1) ≠ 0 := ne_of_gt hden_pos
  have hdmul : d * ((2 : ℝ) ^ (n + 1) - 1) = 1 := by
    rw [hdval, one_div]
    rw [inv_mul_cancel₀ hne]
  have hpt : ∀ i : ℕ,
      d * ((2 : ℝ) ^ (i + 1) - 1) - d * ((2 : ℝ) ^ i - 1) = d * (2 : ℝ) ^ i := by
    intro i
    rw [pow_succ]
    ring
  have hs0 : (fun i : ℕ => d * ((2 : ℝ) ^ i - 1)) 0 = 0 := by simp
  have hs1 : (fun i : ℕ => d * ((2 : ℝ) ^ i - 1)) (A0.card + 1) = 1 := by
    rw [hcard_eq]
    exact hdmul
  have hs_mono : StrictMonoOn (fun i : ℕ => d * ((2 : ℝ) ^ i - 1)) (Set.Icc 0 (A0.card + 1)) := by
    intro a _ b _ hab
    have h1 : (2 : ℝ) ^ a - 1 < (2 : ℝ) ^ b - 1 := by linarith [h2lt a b hab]
    nlinarith [h1, hdpos]
  have hs_int : (A0 : Set ℝ) = (fun i : ℕ => d * ((2 : ℝ) ^ i - 1)) '' Set.Icc 1 A0.card := by
    rw [hcard_eq, hA0val, Finset.coe_image, Finset.coe_Icc]
  obtain ⟨hplA0raw, _, _, _, hrefine, _⟩ :=
    statopia_math_node_4221689064_d3ddf0ec A0 hA0_sub
      (fun i : ℕ => d * ((2 : ℝ) ^ i - 1)) hs0 hs1 hs_mono hs_int
  obtain ⟨blocks, hblocks_flat, hblocks_sums⟩ :=
    hrefine (A0 ∪ B) (Finset.subset_union_left) hTsub
  have hsums : blocks.map (fun b => b.sum) = (List.range (n + 1)).map (fun i => d * (2 : ℝ) ^ i) := by
    rw [hblocks_sums, hplA0raw, hcard_eq]
    simp only [hpt]
  have hfin := statopia_math_node_781820246_3d08e56a n hn1 d hdpos hdmul (A0 ∪ B) hTsub
    blocks hblocks_flat hsums hTcard
  simpa only [L] using hfin


  /- @proof-region region.target-node.session.441252101edcea9c end -/

end LiuBangXiangYu
