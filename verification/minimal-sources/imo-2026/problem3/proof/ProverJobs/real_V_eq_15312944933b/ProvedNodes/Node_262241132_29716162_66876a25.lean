import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_3338307534_b988b604_80c841fd
open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_262241132_29716162 : ∀ (q : ℕ) (hq : 1 ≤ q) (a : Fin q → ℝ) (ha_pos : ∀ i, 0 < a i)
    (I J : Finset (Fin q)) (hIJ : Disjoint I J)
    (hUW : (∑ j ∈ J, a j) ≤ (∑ i ∈ I, a i)),
    let iHi : Fin q → ℝ := fun k => ∑ i ∈ I, if (i : ℕ) ≤ (k : ℕ) then a i else 0;
    let iLo : Fin q → ℝ := fun k => ∑ i ∈ I, if (i : ℕ) < (k : ℕ) then a i else 0;
    let jHi : Fin q → ℝ := fun k => ∑ j ∈ J, if (j : ℕ) ≤ (k : ℕ) then a j else 0;
    let jLo : Fin q → ℝ := fun k => ∑ j ∈ J, if (j : ℕ) < (k : ℕ) then a j else 0;
    let b : ℕ → ℝ := fun k => ∑ i : Fin q, if (i : ℕ) < k then a i else 0;
    let bdI : Finset ℝ := I.image iHi;
    let bdJ : Finset ℝ := J.image jHi;
    let C : Finset ℝ :=
      ((I ×ˢ bdJ).filter (fun ks => iLo ks.1 < ks.2 ∧ ks.2 < iHi ks.1)).image
          (fun ks => b (ks.1 : ℕ) + (ks.2 - iLo ks.1)) ∪
      ((J ×ˢ bdI).filter (fun ks => jLo ks.1 < ks.2 ∧ ks.2 < jHi ks.1)).image
          (fun ks => b (ks.1 : ℕ) + (ks.2 - jLo ks.1));
    let piecesOf : Finset ℝ → Multiset ℝ := fun C =>
      ∑ k ∈ I ∪ J,
        (let x : ℝ := b (k : ℕ);
         let y : ℝ := b ((k : ℕ) + 1);
         let D : List ℝ := (C.filter (fun c => x < c ∧ c < y)).sort (· ≤ ·);
         Multiset.ofList (List.zipWith (fun p r => r - p) (x :: D ++ [y]) (x :: D ++ [y]).tail));
    let U : ℝ := ∑ i ∈ I, a i;
    let W : ℝ := ∑ j ∈ J, a j;
    let SI : Finset ℝ := {0} ∪ bdI ∪ (bdJ.filter (fun x => 0 < x ∧ x < U));
    let SJ : Finset ℝ := {0} ∪ bdJ ∪ (bdI.filter (fun x => 0 < x ∧ x < W));
    piecesOf C
      = Multiset.ofList (List.zipWith (fun p r => r - p) (SI.sort (· ≤ ·)) (SI.sort (· ≤ ·)).tail)
        + Multiset.ofList (List.zipWith (fun p r => r - p) (SJ.sort (· ≤ ·)) (SJ.sort (· ≤ ·)).tail) := by
  /- @proof-region region.target-node.session.d20acef31328204b begin -/
  classical
  intro q hq a ha_pos I J hIJ hUW
  dsimp only
  set iHi : Fin q → ℝ := fun k => ∑ i ∈ I, if (i : ℕ) ≤ (k : ℕ) then a i else 0
  set iLo : Fin q → ℝ := fun k => ∑ i ∈ I, if (i : ℕ) < (k : ℕ) then a i else 0
  set jHi : Fin q → ℝ := fun k => ∑ j ∈ J, if (j : ℕ) ≤ (k : ℕ) then a j else 0
  set jLo : Fin q → ℝ := fun k => ∑ j ∈ J, if (j : ℕ) < (k : ℕ) then a j else 0
  set b : ℕ → ℝ := fun k => ∑ i : Fin q, if (i : ℕ) < k then a i else 0
  set bdI : Finset ℝ := I.image iHi
  set bdJ : Finset ℝ := J.image jHi
  set U : ℝ := ∑ i ∈ I, a i
  set W : ℝ := ∑ j ∈ J, a j
  set SI : Finset ℝ := {0} ∪ bdI ∪ (bdJ.filter (fun x => 0 < x ∧ x < U))
  set SJ : Finset ℝ := {0} ∪ bdJ ∪ (bdI.filter (fun x => 0 < x ∧ x < W))
  set C : Finset ℝ :=
    ((I ×ˢ bdJ).filter (fun ks => iLo ks.1 < ks.2 ∧ ks.2 < iHi ks.1)).image
        (fun ks => b (ks.1 : ℕ) + (ks.2 - iLo ks.1)) ∪
    ((J ×ˢ bdI).filter (fun ks => jLo ks.1 < ks.2 ∧ ks.2 < jHi ks.1)).image
        (fun ks => b (ks.1 : ℕ) + (ks.2 - jLo ks.1))
  rw [Finset.sum_union hIJ]
  obtain ⟨hI, hJ⟩ := statopia_math_node_3338307534_b988b604 q hq a ha_pos I J hIJ hUW
  rw [hI, hJ]
  /- @proof-region region.target-node.session.d20acef31328204b end -/

end LiuBangXiangYu
