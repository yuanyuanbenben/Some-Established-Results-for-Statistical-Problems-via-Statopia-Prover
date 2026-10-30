import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_247222274_f4a96af6_4b656963
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_2695346019_c5493af6_1c088893
open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_3723013110_f47aad67 : ∀ (l : List ℝ) (hL : ∀ z ∈ l, 0 ≤ z)
    (P R : Multiset ℝ) (hdec : Multiset.ofList l = P + P + R)
    (hsum : l.sum = 1) (d : ℝ) (hd : R.sum ≤ d),
    firstPlayerShare l ≤ (1 + d) / 2 := by
  /- @proof-region region.target-node.session.b8d9455bc155e6bb begin -/
  intro l hL P R hdec hsum d hd
  have hdec' : (l : Multiset ℝ) = P + P + R := hdec
  have hmem : ∀ z ∈ (P + P + R : Multiset ℝ), 0 ≤ z := by
    intro z hz
    refine hL z ?_
    have h1 : z ∈ (l : Multiset ℝ) := by rw [hdec']; exact hz
    simpa using h1
  have hP : ((P.toList : List ℝ) : Multiset ℝ) = P := Multiset.coe_toList P
  have hR : ((R.toList : List ℝ) : Multiset ℝ) = R := Multiset.coe_toList R
  have hps : ∀ a ∈ P.toList, 0 ≤ a := by
    intro a ha
    have haP : a ∈ P := by
      have h1 : a ∈ ((P.toList : List ℝ) : Multiset ℝ) := by simpa using ha
      rwa [hP] at h1
    exact hmem a (by rw [Multiset.mem_add, Multiset.mem_add]; exact Or.inl (Or.inl haP))
  have hy : ∀ a ∈ R.toList, 0 ≤ a := by
    intro a ha
    have haR : a ∈ R := by
      have h1 : a ∈ ((R.toList : List ℝ) : Multiset ℝ) := by simpa using ha
      rwa [hR] at h1
    exact hmem a (by rw [Multiset.mem_add]; exact Or.inr haR)
  have hflatp : ∀ t : List ℝ, (t.flatMap (fun a => [a, a])).Perm (t ++ t) := by
    intro t
    induction t with
    | nil => simp
    | cons a t ih =>
        have hpc : (t ++ a :: t).Perm (a :: (t ++ t)) := by
          simpa using (List.perm_append_comm t (a :: t))
        have hstep : ([a, a] ++ t.flatMap (fun a => [a, a])).Perm ([a, a] ++ (t ++ t)) :=
          List.Perm.append (List.Perm.refl [a, a]) ih
        have h2 : ([a, a] ++ (t ++ t)).Perm ((a :: t) ++ (a :: t)) := by
          have h3 : (a :: (a :: (t ++ t))).Perm (a :: (t ++ a :: t)) :=
            List.Perm.append (List.Perm.refl [a]) hpc.symm
          simpa using h3
        simpa [List.flatMap_cons] using hstep.trans h2
  have hflat : ∀ t : List ℝ, ((t.flatMap (fun a => [a, a]) : List ℝ) : Multiset ℝ) = (t : Multiset ℝ) + (t : Multiset ℝ) := by
    intro t
    have hA : ((t.flatMap (fun a => [a, a]) : List ℝ) : Multiset ℝ) = ((t ++ t : List ℝ) : Multiset ℝ) := by
      simpa using hflatp t
    rw [hA, show ((t ++ t : List ℝ) : Multiset ℝ) = (t : Multiset ℝ) + (t : Multiset ℝ) from by simp]
  have happ : ∀ (A B : List ℝ), ((A ++ B : List ℝ) : Multiset ℝ) = (A : Multiset ℝ) + (B : Multiset ℝ) := by
    intro A B
    induction A with
    | nil => simp
    | cons a A ih => simp
  have hxmult : (((P.toList.flatMap (fun a => [a, a]) ++ R.toList) : List ℝ) : Multiset ℝ) = P + P + R := by
    rw [happ, hflat P.toList, hP, hR]
  have hxE : (((P.toList.flatMap (fun a => [a, a]) ++ R.toList) : List ℝ) : Multiset ℝ) = ((l : List ℝ) : Multiset ℝ) := by
    rw [hxmult, hdec']
  have hxperm : (P.toList.flatMap (fun a => [a, a]) ++ R.toList).Perm l := by
    simpa using hxE
  have hxnn : ∀ z ∈ (P.toList.flatMap (fun a => [a, a]) ++ R.toList), 0 ≤ z := by
    intro z hz
    have h1 : z ∈ (((P.toList.flatMap (fun a => [a, a]) ++ R.toList) : List ℝ) : Multiset ℝ) := by
      simpa using hz
    exact hmem z (by rwa [hxmult] at h1)
  have hmse : (P.toList.flatMap (fun a => [a, a]) ++ R.toList).mergeSort (· ≥ ·) = l.mergeSort (· ≥ ·) := by
    rw [← Multiset.coe_sort (P.toList.flatMap (fun a => [a, a]) ++ R.toList) (· ≥ ·),
      ← Multiset.coe_sort l (· ≥ ·), hxE]
  have hfp_eq : firstPlayerShare l = firstPlayerShare (P.toList.flatMap (fun a => [a, a]) ++ R.toList) := by
    simp only [firstPlayerShare]
    rw [hmse]
  have hxsum : ((P.toList.flatMap (fun a => [a, a]) ++ R.toList).mergeSort (· ≥ ·)).sum = 1 := by
    rw [hmse, (List.mergeSort_perm l (fun x1 x2 : ℝ => decide (x1 ≥ x2))).sum_eq, hsum]
  obtain ⟨hfp, hOED, hpos, hDnn, hDabs, hOES, hDO, hS1⟩ :=
    statopia_math_node_247222274_f4a96af6 (P.toList.flatMap (fun a => [a, a]) ++ R.toList) hxnn
  obtain ⟨hfx1, _, _⟩ := hS1 hxsum
  have hpp := statopia_math_node_2695346019_c5493af6 R.toList hy P.toList hps
  have hyR : (R.toList : List ℝ).sum = R.sum := by
    rw [← hR]; simp
  have hDle : ((((P.toList.flatMap (fun a => [a, a]) ++ R.toList).mergeSort (· ≥ ·)).zipIdx.filter
      (fun p => p.2 % 2 = 0)).map (fun p => p.1 - ((P.toList.flatMap (fun a => [a, a]) ++ R.toList).mergeSort (· ≥ ·)).getD (p.2 + 1) 0)).sum ≤ d :=
    le_trans hpp.2 (hyR.symm ▸ hd)
  calc firstPlayerShare l = firstPlayerShare (P.toList.flatMap (fun a => [a, a]) ++ R.toList) := hfp_eq
    _ ≤ (1 + d) / 2 := by
        rw [hfx1]
        apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℝ) ≤ 2)
        linarith
  /- @proof-region region.target-node.session.b8d9455bc155e6bb end -/

end LiuBangXiangYu
