import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_2436669274_aeaf0633_24808446
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_262241132_29716162_66876a25
open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_1713139905_c209ee41 : ∀ (q : ℕ) (hq : 1 ≤ q) (a : Fin q → ℝ) (ha_pos : ∀ i, 0 < a i)
    (I J : Finset (Fin q)) (hIJ : Disjoint I J)
    (hUW : ∑ j ∈ J, a j ≤ ∑ i ∈ I, a i),
    let iHi : Fin q → ℝ := fun k => ∑ i ∈ I, if (i : ℕ) ≤ (k : ℕ) then a i else 0
    let iLo : Fin q → ℝ := fun k => ∑ i ∈ I, if (i : ℕ) < (k : ℕ) then a i else 0
    let jHi : Fin q → ℝ := fun k => ∑ j ∈ J, if (j : ℕ) ≤ (k : ℕ) then a j else 0
    let jLo : Fin q → ℝ := fun k => ∑ j ∈ J, if (j : ℕ) < (k : ℕ) then a j else 0
    let b : ℕ → ℝ := fun k => ∑ i : Fin q, if (i : ℕ) < k then a i else 0
    let bdI : Finset ℝ := I.image iHi
    let bdJ : Finset ℝ := J.image jHi
    let C : Finset ℝ :=
      ((I ×ˢ bdJ).filter (fun ks => iLo ks.1 < ks.2 ∧ ks.2 < iHi ks.1)).image
          (fun ks => b (ks.1 : ℕ) + (ks.2 - iLo ks.1)) ∪
      ((J ×ˢ bdI).filter (fun ks => jLo ks.1 < ks.2 ∧ ks.2 < jHi ks.1)).image
          (fun ks => b (ks.1 : ℕ) + (ks.2 - jLo ks.1))
    let piecesOf : Finset ℝ → Multiset ℝ := fun C =>
      ∑ k ∈ I ∪ J,
        (let x : ℝ := b (k : ℕ)
         let y : ℝ := b ((k : ℕ) + 1)
         let D : List ℝ := (C.filter (fun c => x < c ∧ c < y)).sort (· ≤ ·)
         Multiset.ofList (List.zipWith (fun p r => r - p) (x :: D ++ [y]) (x :: D ++ [y]).tail))
    ∃ Ps R : Multiset ℝ,
      Ps + Ps + R = piecesOf C ∧ R.sum = (∑ i ∈ I, a i) - (∑ j ∈ J, a j) := by
  /- @proof-region region.target-node.session.e57ed2bbf53c30e4 begin -/
  classical
  intro q hq a ha_pos I J hIJ hUW
  let iHi : Fin q → ℝ := fun k => ∑ i ∈ I, if (i : ℕ) ≤ (k : ℕ) then a i else 0
  let iLo : Fin q → ℝ := fun k => ∑ i ∈ I, if (i : ℕ) < (k : ℕ) then a i else 0
  let jHi : Fin q → ℝ := fun k => ∑ j ∈ J, if (j : ℕ) ≤ (k : ℕ) then a j else 0
  let jLo : Fin q → ℝ := fun k => ∑ j ∈ J, if (j : ℕ) < (k : ℕ) then a j else 0
  let b : ℕ → ℝ := fun k => ∑ i : Fin q, if (i : ℕ) < k then a i else 0
  let bdI : Finset ℝ := I.image iHi
  let bdJ : Finset ℝ := J.image jHi
  let Cc : Finset ℝ :=
    ((I ×ˢ bdJ).filter (fun ks => iLo ks.1 < ks.2 ∧ ks.2 < iHi ks.1)).image
        (fun ks => b (ks.1 : ℕ) + (ks.2 - iLo ks.1)) ∪
    ((J ×ˢ bdI).filter (fun ks => jLo ks.1 < ks.2 ∧ ks.2 < jHi ks.1)).image
        (fun ks => b (ks.1 : ℕ) + (ks.2 - jLo ks.1))
  let po : Finset ℝ → Multiset ℝ := fun Cc =>
    ∑ k ∈ I ∪ J,
      (let x : ℝ := b (k : ℕ)
       let y : ℝ := b ((k : ℕ) + 1)
       let D : List ℝ := (Cc.filter (fun c => x < c ∧ c < y)).sort (· ≤ ·)
       Multiset.ofList (List.zipWith (fun p r => r - p) (x :: D ++ [y]) (x :: D ++ [y]).tail))
  change ∃ Ps R : Multiset ℝ, Ps + Ps + R = po Cc ∧ R.sum = (∑ i ∈ I, a i) - (∑ j ∈ J, a j)
  let G : List ℝ → List ℝ := fun l => List.zipWith (fun p r => r - p) l l.tail
  have hG_cons : ∀ (x : ℝ) (r : List ℝ), r ≠ [] → G (x :: r) = (r.headD 0 - x) :: G r := by
    intro x r hr
    rcases r with _ | ⟨h, t⟩
    · exact absurd rfl hr
    · simp [G]
  have hheadD_append : ∀ (l B : List ℝ), l ≠ [] → (l ++ B).headD 0 = l.headD 0 := by
    intro l B hl
    rcases l with _ | ⟨h, t⟩
    · exact absurd rfl hl
    · simp
  have hgap_snoc : ∀ (A : List ℝ) (W : ℝ) (B : List ℝ),
      G ((A ++ [W]) ++ B) = G (A ++ [W]) ++ G (W :: B) := by
    intro A
    induction A with
    | nil => intro W B; simp [G]
    | cons a A' ih =>
      intro W B
      have hne : A' ++ [W] ≠ [] := by simp
      have hne2 : (A' ++ [W]) ++ B ≠ [] := by simp
      simp only [List.cons_append]
      rw [hG_cons a ((A' ++ [W]) ++ B) hne2, hG_cons a (A' ++ [W]) hne]
      rw [ih W B, hheadD_append (A' ++ [W]) B hne]
      rfl
  have hsum_cons : ∀ (D : List ℝ) (x : ℝ) (y : ℝ), (G (x :: D ++ [y])).sum = y - x := by
    intro D
    induction D with
    | nil => intro x y; simp [G]
    | cons d D ih =>
      intro x y
      have h : G (x :: d :: D ++ [y]) = (d - x) :: G (d :: D ++ [y]) := by
        have h1 := hG_cons x (d :: D ++ [y]) (by simp)
        simpa using h1
      rw [h, List.sum_cons, ih d y]
      ring
  let U : ℝ := ∑ i ∈ I, a i
  let W : ℝ := ∑ j ∈ J, a j
  let SI : Finset ℝ := {0} ∪ bdI ∪ (bdJ.filter (fun x => 0 < x ∧ x < U))
  let SJ : Finset ℝ := {0} ∪ bdJ ∪ (bdI.filter (fun x => 0 < x ∧ x < W))
  let gI : Multiset ℝ := Multiset.ofList (G (SI.sort (· ≤ ·)))
  let gJ : Multiset ℝ := Multiset.ofList (G (SJ.sort (· ≤ ·)))
  let R : Multiset ℝ := Multiset.ofList (G (W :: (bdI.filter (fun x => W < x)).sort (· ≤ ·)))
  refine ⟨gJ, R, ?_, ?_⟩
  · have hA : po Cc = gI + gJ :=
      statopia_math_node_262241132_29716162 q hq a ha_pos I J hIJ hUW
    have hB1 : gI = gJ + R :=
      (statopia_math_node_2436669274_aeaf0633 q hq a ha_pos I J hIJ hUW).1
    rw [hA, hB1]
    abel
  · exact (statopia_math_node_2436669274_aeaf0633 q hq a ha_pos I J hIJ hUW).2
  /- @proof-region region.target-node.session.e57ed2bbf53c30e4 end -/

end LiuBangXiangYu
