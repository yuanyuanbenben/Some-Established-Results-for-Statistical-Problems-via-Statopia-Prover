import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_247222274_f4a96af6_4b656963
open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_255061405_785d7120 : ∀ (y : List ℝ) (hy : ∀ z ∈ y, 0 ≤ z),
    (let ys : List ℝ := y.mergeSort (· ≥ ·)
     let dy : ℝ :=
       ((ys.zipIdx.filter (fun p => p.2 % 2 = 0)).map
         (fun p => p.1 - ys.getD (p.2 + 1) 0)).sum
     dy ≤ y.sum) := by
  /- @proof-region region.target-node.session.56b828069c8b3314 begin -/
  intro y hy
  have hperm : (y.mergeSort (· ≥ ·)).Perm y := List.mergeSort_perm y _
  have hsum : (y.mergeSort (· ≥ ·)).sum = y.sum := hperm.sum_eq
  obtain ⟨-, hODE, -, -, -, hOES, -, -⟩ := statopia_math_node_247222274_f4a96af6 y hy
  have hEnn : 0 ≤ (((y.mergeSort (· ≥ ·)).zipIdx.filter (fun p => p.2 % 2 = 1)).map (fun p => p.1)).sum := by
    have key : ∀ (l : List ℝ), l.zipIdx.map Prod.fst = l := by
      intro l
      induction l with
      | nil => simp [List.zipIdx]
      | cons a t ih => simp [List.zipIdx, ih]
    apply List.sum_nonneg
    intro z hz
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz
    have hpz : p ∈ (y.mergeSort (· ≥ ·)).zipIdx := (List.mem_filter.mp hp).1
    have hp1 : p.1 ∈ (y.mergeSort (· ≥ ·)) := by
      have h1 : p.1 ∈ (y.mergeSort (· ≥ ·)).zipIdx.map Prod.fst := List.mem_map.mpr ⟨p, hpz, rfl⟩
      rwa [key] at h1
    exact hy p.1 (hperm.subset hp1)
  change (((y.mergeSort (· ≥ ·)).zipIdx.filter (fun p => p.2 % 2 = 0)).map (fun p => p.1 - (y.mergeSort (· ≥ ·)).getD (p.2 + 1) 0)).sum ≤ y.sum
  rw [← hODE, ← hsum, ← hOES]
  linarith [hEnn]
  /- @proof-region region.target-node.session.56b828069c8b3314 end -/

end LiuBangXiangYu
