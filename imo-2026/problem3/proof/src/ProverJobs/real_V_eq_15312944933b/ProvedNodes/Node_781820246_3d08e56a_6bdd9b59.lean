import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_247222274_f4a96af6_4b656963
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_2999225285_90342243_ea48111e
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_64757959_89ee7b39_ade6efd3
open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_781820246_3d08e56a : ∀ (n : ℕ) (hn : 1 ≤ n) (d : ℝ) (hd : 0 < d)
    (hd1 : d * ((2 : ℝ) ^ (n + 1) - 1) = 1)
    (T : Finset ℝ) (hT : (T : Set ℝ) ⊆ Set.Ioo (0 : ℝ) 1)
    (blocks : List (List ℝ)) (hflat : blocks.flatten = pieceLengths T)
    (hsums : blocks.map (fun b => b.sum) = (List.range (n + 1)).map (fun i => d * (2 : ℝ) ^ i))
    (hcard : T.card ≤ 2 * n),
    (1 + d) / 2 ≤ firstPlayerShare (pieceLengths T) := by
  /- @proof-region region.target-node.session.31db7845463c85e9 begin -/
  intro n hn d hd hd1 T hT blocks hflat hsums hcard
  let xs : List ℝ := (pieceLengths T).mergeSort (· ≥ ·)
  let D : ℝ := ((xs.zipIdx.filter (fun p => p.2 % 2 = 0)).map (fun p => p.1 - xs.getD (p.2 + 1) 0)).sum
  obtain ⟨hL, hsumS, hDd⟩ :=
    statopia_math_node_64757959_89ee7b39 n hn d hd hd1 T hT blocks hflat hsums hcard
  have hDd' : d ≤ D := hDd
  have h247 := statopia_math_node_247222274_f4a96af6 (pieceLengths T) hL
  obtain ⟨-, -, -, -, -, -, -, hlast⟩ := h247
  have hfp : firstPlayerShare (pieceLengths T) = (1 + D) / 2 := (hlast hsumS).1
  linarith [hfp, hDd']
  /- @proof-region region.target-node.session.31db7845463c85e9 end -/

end LiuBangXiangYu
