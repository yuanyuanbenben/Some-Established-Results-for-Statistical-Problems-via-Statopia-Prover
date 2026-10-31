import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_158273889_304075e3_abf0ec42
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_247222274_f4a96af6_4b656963
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_255061405_785d7120_2a1785a2
open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_2695346019_c5493af6 : ∀ (y : List ℝ) (hy : ∀ z ∈ y, 0 ≤ z)
    (ps : List ℝ) (hps : ∀ a ∈ ps, 0 ≤ a),
    let x : List ℝ := ps.flatMap (fun a => [a, a]) ++ y
    let xs : List ℝ := x.mergeSort (· ≥ ·)
    let dx : ℝ :=
      ((xs.zipIdx.filter (fun p => p.2 % 2 = 0)).map
        (fun p => p.1 - xs.getD (p.2 + 1) 0)).sum
    let ys : List ℝ := y.mergeSort (· ≥ ·)
    let dy : ℝ :=
      ((ys.zipIdx.filter (fun p => p.2 % 2 = 0)).map
        (fun p => p.1 - ys.getD (p.2 + 1) 0)).sum
    dx = dy ∧ dx ≤ y.sum := by
  /- @proof-region region.target-node.session.97883586d75144ca begin -/
  intro y hy ps hps
  dsimp only
  let A : List ℝ → ℝ := fun m =>
    (((m.mergeSort (· ≥ ·)).zipIdx.filter (fun p => p.2 % 2 = 0)).map
      (fun p => p.1 - (m.mergeSort (· ≥ ·)).getD (p.2 + 1) 0)).sum
  have hstep : ∀ (l : List ℝ) (a : ℝ), A (a :: a :: l) = A l :=
    statopia_math_node_158273889_304075e3
  have key : ∀ (ps : List ℝ), A (ps.flatMap (fun a => [a, a]) ++ y) = A y := by
    intro ps
    induction ps with
    | nil => simp
    | cons a t ih =>
      have h1 : A ((a :: t).flatMap (fun a => [a, a]) ++ y)
          = A (t.flatMap (fun a => [a, a]) ++ y) := by
        show A (a :: a :: (t.flatMap (fun a => [a, a]) ++ y))
            = A (t.flatMap (fun a => [a, a]) ++ y)
        exact hstep (t.flatMap (fun a => [a, a]) ++ y) a
      rw [h1]
      exact ih
  refine ⟨?_, ?_⟩
  · show A (ps.flatMap (fun a => [a, a]) ++ y) = A y
    exact key ps
  · show A (ps.flatMap (fun a => [a, a]) ++ y) ≤ y.sum
    rw [key ps]
    exact statopia_math_node_255061405_785d7120 y hy
  /- @proof-region region.target-node.session.97883586d75144ca end -/

end LiuBangXiangYu
