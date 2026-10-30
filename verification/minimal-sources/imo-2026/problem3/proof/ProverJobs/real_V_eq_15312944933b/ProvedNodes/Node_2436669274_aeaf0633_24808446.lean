import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_3426023923_ba29e974_d4c2d78c
open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_2436669274_aeaf0633 : ∀ (q : ℕ) (hq : 1 ≤ q) (a : Fin q → ℝ) (ha_pos : ∀ i, 0 < a i)
    (I J : Finset (Fin q)) (hIJ : Disjoint I J)
    (hUW : ∑ j ∈ J, a j ≤ ∑ i ∈ I, a i),
    let iHi : Fin q → ℝ := fun k => ∑ i ∈ I, if (i : ℕ) ≤ (k : ℕ) then a i else 0
    let jHi : Fin q → ℝ := fun k => ∑ j ∈ J, if (j : ℕ) ≤ (k : ℕ) then a j else 0
    let bdI : Finset ℝ := I.image iHi
    let bdJ : Finset ℝ := J.image jHi
    let U : ℝ := ∑ i ∈ I, a i
    let W : ℝ := ∑ j ∈ J, a j
    let SI : Finset ℝ := {0} ∪ bdI ∪ (bdJ.filter (fun x => 0 < x ∧ x < U))
    let SJ : Finset ℝ := {0} ∪ bdJ ∪ (bdI.filter (fun x => 0 < x ∧ x < W))
    let gI : Multiset ℝ := Multiset.ofList (List.zipWith (fun p r => r - p) (SI.sort (· ≤ ·)) (SI.sort (· ≤ ·)).tail)
    let gJ : Multiset ℝ := Multiset.ofList (List.zipWith (fun p r => r - p) (SJ.sort (· ≤ ·)) (SJ.sort (· ≤ ·)).tail)
    let E : List ℝ := (bdI.filter (fun x => W < x)).sort (· ≤ ·)
    let R : Multiset ℝ := Multiset.ofList (List.zipWith (fun p r => r - p) (W :: E) (W :: E).tail)
    gI = gJ + R ∧ R.sum = U - W := by
  /- @proof-region region.target-node.session.a2027acda7508500 begin -/
  intro q hq a ha_pos I J hIJ hUW
  classical
  dsimp only
  set iHi : Fin q → ℝ := fun k => ∑ i ∈ I, if (i : ℕ) ≤ (k : ℕ) then a i else 0 with hiHi
  set jHi : Fin q → ℝ := fun k => ∑ j ∈ J, if (j : ℕ) ≤ (k : ℕ) then a j else 0 with hjHi
  set bdI : Finset ℝ := I.image iHi with hbdI
  set bdJ : Finset ℝ := J.image jHi with hbdJ
  set U : ℝ := ∑ i ∈ I, a i with hU
  set W : ℝ := ∑ j ∈ J, a j with hW
  set SI : Finset ℝ := {0} ∪ bdI ∪ (bdJ.filter (fun x => 0 < x ∧ x < U)) with hSI
  set SJ : Finset ℝ := {0} ∪ bdJ ∪ (bdI.filter (fun x => 0 < x ∧ x < W)) with hSJ
  set gI : Multiset ℝ := Multiset.ofList (List.zipWith (fun p r => r - p) (SI.sort (· ≤ ·)) (SI.sort (· ≤ ·)).tail) with hgI
  set gJ : Multiset ℝ := Multiset.ofList (List.zipWith (fun p r => r - p) (SJ.sort (· ≤ ·)) (SJ.sort (· ≤ ·)).tail) with hgJ
  set E : List ℝ := (bdI.filter (fun x => W < x)).sort (· ≤ ·) with hE
  set R : Multiset ℝ := Multiset.ofList (List.zipWith (fun p r => r - p) (W :: E) (W :: E).tail) with hR
  refine ⟨?_, ?_⟩
  · exact (statopia_math_node_3426023923_ba29e974 q hq a ha_pos I J hIJ hUW).1
  · have hlast : (W :: E).getLastD 0 = U :=
      (statopia_math_node_3426023923_ba29e974 q hq a ha_pos I J hIJ hUW).2
    have htele : ∀ (M : List ℝ) (w : ℝ),
        (List.zipWith (fun p r => r - p) (w :: M) M).sum = (w :: M).getLastD 0 - w := by
      intro M
      induction M with
      | nil => intro w; simp
      | cons b M' ih =>
        intro w
        have hstep : (List.zipWith (fun p r => r - p) (w :: b :: M') (b :: M')).sum
            = (b - w) + (List.zipWith (fun p r => r - p) (b :: M') M').sum := rfl
        have hgl : (w :: b :: M').getLastD 0 = (b :: M').getLastD 0 := rfl
        rw [hstep, ih b, hgl]
        ring
    have hcoe : (Multiset.ofList (List.zipWith (fun p r => r - p) (W :: E) E)).sum
        = (List.zipWith (fun p r => r - p) (W :: E) E).sum := by simp
    have htail : (W :: E).tail = E := rfl
    rw [hR, htail, hcoe, htele E W, hlast]
  /- @proof-region region.target-node.session.a2027acda7508500 end -/

end LiuBangXiangYu
