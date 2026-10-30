import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_3322926854_a1826859_e20c4f6c
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_3449704327_7cf17c98_c0badce1
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_4221689064_d3ddf0ec_fbe161c8
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_901974942_c7be0ac8_5f6106c2
open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_1937137240_45ae93aa : ∀ (q : ℕ) (hq : 1 ≤ q) (a : Fin q → ℝ)
    (ha_pos : ∀ i, 0 < a i) (ha_sum : ∑ i : Fin q, a i = 1)
    (b : ℕ → ℝ) (hb : ∀ k, b k = ∑ i : Fin q, (if (i : ℕ) < k then a i else 0))
    (I J : Finset (Fin q)) (hIJ : Disjoint I J) (hne : I ∪ J ≠ ∅)
    (C : Finset ℝ)
    (hC1 : ∀ c ∈ C, 0 < c ∧ c < 1)
    (hC2 : ∀ c ∈ C, ∀ k : Fin (q + 1), c ≠ b (k : ℕ))
    (hC3 : ∀ c ∈ C, ∃ k ∈ I ∪ J, b (k : ℕ) < c ∧ c < b ((k : ℕ) + 1))
    (hC4 : C.card ≤ I.card + J.card - 1),
    let A : Finset ℝ := (Finset.univ.filter (fun k : Fin q => 1 ≤ (k : ℕ))).image (fun k : Fin q => b (k : ℕ))
    let M : Finset ℝ := (Finset.univ.filter (fun k : Fin q => k ∉ I ∪ J)).image (fun k : Fin q => (b (k : ℕ) + b ((k : ℕ) + 1)) / 2)
    AdmissibleMark A.card (C ∪ M) ∧ Disjoint A (C ∪ M) ∧
      Multiset.ofList (pieceLengths (A ∪ (C ∪ M))) =
        (∑ k ∈ Finset.univ.filter (fun k : Fin q => k ∉ I ∪ J), ({a k / 2, a k / 2} : Multiset ℝ))
          + (∑ k ∈ I ∪ J, (let x : ℝ := b (k : ℕ); let y : ℝ := b ((k : ℕ) + 1)
              let D : List ℝ := (C.filter (fun c => x < c ∧ c < y)).sort (· ≤ ·)
              Multiset.ofList (List.zipWith (fun p r => r - p) (x :: D ++ [y]) (x :: D ++ [y]).tail))) := by
  /- @proof-region region.target-node.session.ade15205b755c7ef begin -/
  intro q hq a ha_pos ha_sum b hb I J hIJ hne C hC1 hC2 hC3 hC4
  obtain ⟨hb0, hbq, hbmono, hbstep⟩ :=
    statopia_math_node_901974942_c7be0ac8 q hq a ha_pos ha_sum b hb
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · exact (statopia_math_node_3322926854_a1826859 q hq b hb0 hbq hbmono I J hIJ hne C hC1 hC2 hC3 hC4).1
  · exact (statopia_math_node_3322926854_a1826859 q hq b hb0 hbq hbmono I J hIJ hne C hC1 hC2 hC3 hC4).2
  · exact statopia_math_node_3449704327_7cf17c98 q hq a ha_pos b hb0 hbq hbmono hbstep I J hIJ hne C hC1 hC2 hC3 hC4
  /- @proof-region region.target-node.session.ade15205b755c7ef end -/

end LiuBangXiangYu
