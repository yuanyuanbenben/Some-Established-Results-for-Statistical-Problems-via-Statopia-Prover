import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_2471006781_90e3b0f3_b4dd7482
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_247222274_f4a96af6_4b656963
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_2695346019_c5493af6_1c088893
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_2798148667_8bcde5b0_9857b7f6
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_3200008108_17e56165_e20ae208
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_3886798737_08bdef52_f40a7bbb
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_4221689064_d3ddf0ec_fbe161c8
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_951219948_a078b303_8e27ca79
open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_1763956908_225d779d : ∀ (n : ℕ) (hn : 1 ≤ n) (A : Finset ℝ)
    (hA : AdmissibleMark n A),
    ∃ B : Finset ℝ, AdmissibleMark n B ∧ Disjoint A B ∧
      L A B ≤ (1 + (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 1)) / 2 := by
  /- @proof-region region.target-node.session.1331e52066762eec begin -/
  intro n hn A hA
  obtain ⟨s, hs0, hs1, hs_mono, hs_int⟩ :=
    statopia_math_node_951219948_a078b303 A hA.1
  have hPL := statopia_math_node_4221689064_d3ddf0ec A hA.1 s hs0 hs1 hs_mono hs_int
  have hcard : A.card ≤ n := hA.2
  have hq_le : A.card + 1 ≤ n + 1 := by omega
  by_cases hcase : A.card + 1 ≤ n
  · let B : Finset ℝ := (Finset.range (A.card + 1)).image (fun i => (s i + s (i + 1)) / 2)
    obtain ⟨hB_eq, hB_sum⟩ :=
      statopia_math_node_2471006781_90e3b0f3 A s hA.1 hs0 hs1 hs_mono hs_int
    have hmono : ∀ a b : ℕ, a ≤ b → b ≤ A.card + 1 → s a ≤ s b := by
      intro a b hab hb
      rcases lt_or_eq_of_le hab with h | h
      · exact (hs_mono (by simp only [Set.mem_Icc]; omega)
            (by simp only [Set.mem_Icc]; omega) h).le
      · rw [h]
    refine ⟨B, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro x hx
        have hx' : x ∈ (Finset.range (A.card + 1)).image (fun i => (s i + s (i + 1)) / 2) := hx
        simp only [Finset.mem_image, Finset.mem_range] at hx'
        obtain ⟨i, hi, rfl⟩ := hx'
        have hi' : i + 1 ≤ A.card + 1 := by omega
        have hsi_nn : 0 ≤ s i := by
          rcases Nat.eq_zero_or_pos i with h | h
          · rw [h, hs0]
          · have hlt := hs_mono (by simp only [Set.mem_Icc]; omega)
                (by simp only [Set.mem_Icc]; omega) h
            rw [hs0] at hlt
            exact hlt.le
        have hsi1_pos : 0 < s (i + 1) := by
          have hlt := hs_mono (by simp only [Set.mem_Icc]; omega)
              (by simp only [Set.mem_Icc]; omega) (Nat.succ_pos i)
          rw [hs0] at hlt
          exact hlt
        have hsi_lt1 : s i < 1 := by
          have hlt := hs_mono (by simp only [Set.mem_Icc]; omega)
              (by simp only [Set.mem_Icc]; omega) hi
          rwa [hs1] at hlt
        have hsi1_le1 : s (i + 1) ≤ 1 := by
          rcases lt_or_eq_of_le hi' with h | h
          · have hlt := (hs_mono (by simp only [Set.mem_Icc]; omega)
                (by simp only [Set.mem_Icc]; omega) h).le
            rwa [hs1] at hlt
          · rw [h, hs1]
        exact ⟨by linarith, by linarith⟩
      · have hcimg : B.card ≤ (Finset.range (A.card + 1)).card :=
          Finset.card_image_le
        rw [Finset.card_range] at hcimg
        omega
    · rw [Finset.disjoint_left]
      intro x hx hxB
      change x ∈ (A : Set ℝ) at hx
      rw [hs_int] at hx
      obtain ⟨j, hj, hjeq⟩ := hx
      rw [← hjeq] at hxB
      have hxB' : s j ∈ (Finset.range (A.card + 1)).image (fun i => (s i + s (i + 1)) / 2) := hxB
      simp only [Finset.mem_image, Finset.mem_range] at hxB'
      obtain ⟨i, hi, heq⟩ := hxB'
      have hsi_lt : s i < s (i + 1) :=
        hs_mono (by simp only [Set.mem_Icc]; omega) (by simp only [Set.mem_Icc]; omega)
          (Nat.lt_succ_self i)
      by_cases hji : j ≤ i
      · have hle := hmono j i hji (by omega)
        linarith
      · have hji' : i < j := Nat.lt_of_not_le hji
        have hjc : j ≤ A.card := hj.2
        have hle := hmono (i + 1) j (by omega) (by omega)
        linarith
    · have hps_nn : ∀ a ∈ (pieceLengths A).map (fun a => a / 2), 0 ≤ a := by
        intro a ha
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
        have hbpos : 0 < b := hPL.2.2.1 b hb
        linarith
      have hB_eq' : pieceLengths (A ∪ B) =
          ((pieceLengths A).map (fun a => a / 2)).flatMap (fun a => [a, a]) := hB_eq
      have hB_sum' : (pieceLengths (A ∪ B)).sum = 1 := hB_sum
      have hL_nn : ∀ x ∈ pieceLengths (A ∪ B), 0 ≤ x := by
        rw [hB_eq']
        intro x hx
        obtain ⟨a, ha, hxa⟩ := List.mem_flatMap.mp hx
        have hxa' : x = a := by simpa using hxa
        rw [hxa']
        exact hps_nn a ha
      have hdx_zero : ([] : List ℝ).sum = 0 := by simp
      obtain ⟨-, hDx_le⟩ :=
        statopia_math_node_2695346019_c5493af6 ([] : List ℝ) (by intro z hz; simp at hz)
          ((pieceLengths A).map (fun a => a / 2)) hps_nn
      rw [hdx_zero] at hDx_le
      simp only [List.append_nil] at hDx_le
      rw [← hB_eq'] at hDx_le
      obtain ⟨-, -, -, hDnn, -, -, -, hlast⟩ :=
        statopia_math_node_247222274_f4a96af6 (pieceLengths (A ∪ B)) hL_nn
      have hperm : ((pieceLengths (A ∪ B)).mergeSort (· ≥ ·)).Perm (pieceLengths (A ∪ B)) :=
        List.mergeSort_perm _ _
      have hS : ((pieceLengths (A ∪ B)).mergeSort (· ≥ ·)).sum = 1 := by
        rw [List.Perm.sum_eq hperm, hB_sum']
      obtain ⟨hfp_eq, -, -⟩ := hlast hS
      change firstPlayerShare (pieceLengths (A ∪ B)) ≤
        (1 + (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 1)) / 2
      rw [hfp_eq]
      have hDzero := le_antisymm hDx_le hDnn
      rw [hDzero]
      have hd_nonneg : (0 : ℝ) ≤ 1 / ((2 : ℝ) ^ (n + 1) - 1) := by
        have hn1 : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
        have hsucc : (2 : ℝ) ^ (n + 1) = (2 : ℝ) ^ n * 2 := pow_succ 2 n
        apply div_nonneg zero_le_one
        linarith
      linarith
  · have hcardn : A.card = n := by omega
    exact statopia_math_node_3886798737_08bdef52 n hn A hA hcardn
  /- @proof-region region.target-node.session.1331e52066762eec end -/

end LiuBangXiangYu
