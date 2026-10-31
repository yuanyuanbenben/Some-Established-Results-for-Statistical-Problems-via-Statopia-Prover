import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_2789815743_0d7f93cf_e8db38f5
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_428735515_34bc9020_214f2330
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_689319304_41a3eefa_c0bba1a5
open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_3338307534_b988b604 : ∀ (q : ℕ) (hq : 1 ≤ q) (a : Fin q → ℝ) (ha_pos : ∀ i, 0 < a i)
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
    let U : ℝ := ∑ i ∈ I, a i;
    let W : ℝ := ∑ j ∈ J, a j;
    let SI : Finset ℝ := {0} ∪ bdI ∪ (bdJ.filter (fun x => 0 < x ∧ x < U));
    let SJ : Finset ℝ := {0} ∪ bdJ ∪ (bdI.filter (fun x => 0 < x ∧ x < W));
    let blk : Fin q → Multiset ℝ := fun k =>
        (let x : ℝ := b (k : ℕ);
         let y : ℝ := b ((k : ℕ) + 1);
         let D : List ℝ := (C.filter (fun c => x < c ∧ c < y)).sort (· ≤ ·);
         Multiset.ofList (List.zipWith (fun p r => r - p) (x :: D ++ [y]) (x :: D ++ [y]).tail));
    (∑ i ∈ I, blk i)
        = Multiset.ofList (List.zipWith (fun p r => r - p) (SI.sort (· ≤ ·)) (SI.sort (· ≤ ·)).tail)
    ∧ (∑ j ∈ J, blk j)
        = Multiset.ofList (List.zipWith (fun p r => r - p) (SJ.sort (· ≤ ·)) (SJ.sort (· ≤ ·)).tail) := by
  /- @proof-region region.target-node.session.32cedbb93f9caee7 begin -/
  intro q hq a ha_pos I J hIJ hUW
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
  let U : ℝ := ∑ i ∈ I, a i
  let W : ℝ := ∑ j ∈ J, a j
  let SI : Finset ℝ := {0} ∪ bdI ∪ (bdJ.filter (fun x => 0 < x ∧ x < U))
  let SJ : Finset ℝ := {0} ∪ bdJ ∪ (bdI.filter (fun x => 0 < x ∧ x < W))
  let blk : Fin q → Multiset ℝ := fun k =>
      (let x : ℝ := b (k : ℕ);
       let y : ℝ := b ((k : ℕ) + 1);
       let D : List ℝ := (C.filter (fun c => x < c ∧ c < y)).sort (· ≤ ·);
       Multiset.ofList (List.zipWith (fun p r => r - p) (x :: D ++ [y]) (x :: D ++ [y]).tail))
  have hb_step : ∀ k : Fin q, b ((k : ℕ) + 1) = b (k : ℕ) + a k := by
    intro k
    show (∑ i : Fin q, (if (i : ℕ) < (k : ℕ) + 1 then a i else 0))
        = (∑ i : Fin q, (if (i : ℕ) < (k : ℕ) then a i else 0)) + a k
    have hc : ∀ i : Fin q, (if (i : ℕ) < (k : ℕ) + 1 then a i else 0)
        = (if (i : ℕ) < (k : ℕ) then a i else 0) + (if (i : ℕ) = (k : ℕ) then a i else 0) := by
      intro i
      by_cases hlt : (i : ℕ) < (k : ℕ)
      · have h1 : (i : ℕ) < (k : ℕ) + 1 := Nat.lt_succ_of_lt hlt
        have hne : ¬ ((i : ℕ) = (k : ℕ)) := by omega
        simp [hlt, h1, hne]
      · by_cases heq : (i : ℕ) = (k : ℕ)
        · have h3 : (i : ℕ) < (k : ℕ) + 1 := by omega
          simp [hlt, heq, h3]
        · have h3 : ¬ ((i : ℕ) < (k : ℕ) + 1) := by omega
          simp [hlt, heq, h3]
    rw [Finset.sum_congr rfl (fun i _ => hc i), Finset.sum_add_distrib]
    rw [Finset.sum_eq_single k (fun i _ hi => if_neg (fun h => hi (Fin.ext h)))
          (fun hk => absurd (Finset.mem_univ k) hk)]
    rw [if_pos rfl]
  have hIsum : ∀ k : Fin q, (∑ i ∈ I, (if (i : ℕ) = (k : ℕ) then a i else 0)) = (if k ∈ I then a k else 0) := by
    intro k
    by_cases hk : k ∈ I
    · rw [if_pos hk, Finset.sum_eq_single k (fun i _ hi => if_neg (fun h => hi (Fin.ext h)))
          (fun hk' => absurd hk hk'), if_pos rfl]
    · rw [if_neg hk, Finset.sum_congr rfl (fun i hi => if_neg (fun h => hk (by rw [← Fin.ext h]; exact hi)))]
      simp
  have hiHi_eq : ∀ k : Fin q, iHi k = iLo k + (if k ∈ I then a k else 0) := by
    intro k
    show (∑ i ∈ I, (if (i : ℕ) ≤ (k : ℕ) then a i else 0))
        = (∑ i ∈ I, (if (i : ℕ) < (k : ℕ) then a i else 0)) + (if k ∈ I then a k else 0)
    have hpt : ∀ i : Fin q, (if (i : ℕ) ≤ (k : ℕ) then a i else 0)
        = (if (i : ℕ) < (k : ℕ) then a i else 0) + (if (i : ℕ) = (k : ℕ) then a i else 0) := by
      intro i
      by_cases hlt : (i : ℕ) < (k : ℕ)
      · have h1 : (i : ℕ) ≤ (k : ℕ) := le_of_lt hlt
        have hne : ¬ ((i : ℕ) = (k : ℕ)) := by omega
        simp [hlt, h1, hne]
      · by_cases heq : (i : ℕ) = (k : ℕ)
        · have h1 : (i : ℕ) ≤ (k : ℕ) := by omega
          simp [hlt, heq, h1]
        · have h1 : ¬ ((i : ℕ) ≤ (k : ℕ)) := by omega
          simp [hlt, heq, h1]
    rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_add_distrib, hIsum k]
  have hJsum : ∀ k : Fin q, (∑ j ∈ J, (if (j : ℕ) = (k : ℕ) then a j else 0)) = (if k ∈ J then a k else 0) := by
    intro k
    by_cases hk : k ∈ J
    · rw [if_pos hk, Finset.sum_eq_single k (fun j _ hj => if_neg (fun h => hj (Fin.ext h)))
          (fun hk' => absurd hk hk'), if_pos rfl]
    · rw [if_neg hk, Finset.sum_congr rfl (fun j hj => if_neg (fun h => hk (by rw [← Fin.ext h]; exact hj)))]
      simp
  have hjHi_eq : ∀ k : Fin q, jHi k = jLo k + (if k ∈ J then a k else 0) := by
    intro k
    show (∑ j ∈ J, (if (j : ℕ) ≤ (k : ℕ) then a j else 0))
        = (∑ j ∈ J, (if (j : ℕ) < (k : ℕ) then a j else 0)) + (if k ∈ J then a k else 0)
    have hpt : ∀ j : Fin q, (if (j : ℕ) ≤ (k : ℕ) then a j else 0)
        = (if (j : ℕ) < (k : ℕ) then a j else 0) + (if (j : ℕ) = (k : ℕ) then a j else 0) := by
      intro j
      by_cases hlt : (j : ℕ) < (k : ℕ)
      · have h1 : (j : ℕ) ≤ (k : ℕ) := le_of_lt hlt
        have hne : ¬ ((j : ℕ) = (k : ℕ)) := by omega
        simp [hlt, h1, hne]
      · by_cases heq : (j : ℕ) = (k : ℕ)
        · have h1 : (j : ℕ) ≤ (k : ℕ) := by omega
          simp [hlt, heq, h1]
        · have h1 : ¬ ((j : ℕ) ≤ (k : ℕ)) := by omega
          simp [hlt, heq, h1]
    rw [Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_add_distrib, hJsum k]
  have hiLo_lt_iHi : ∀ i ∈ I, iLo i < iHi i := by
    intro i hi
    have h := hiHi_eq i
    rw [if_pos hi] at h
    have hp := ha_pos i
    linarith
  have hb_lt : ∀ k : Fin q, b (k : ℕ) < b ((k : ℕ) + 1) := by
    intro k
    have h := hb_step k
    have hp := ha_pos k
    linarith
  have hreindexI : (∑ i ∈ I, blk i) = ∑ k : Fin I.card, blk (I.orderEmbOfFin rfl k) := by
    conv_lhs => rw [← Finset.map_orderEmbOfFin_univ I rfl]
    rw [Finset.sum_map]
    rfl
  have hreindexJ : (∑ j ∈ J, blk j) = ∑ k : Fin J.card, blk (J.orderEmbOfFin rfl k) := by
    conv_lhs => rw [← Finset.map_orderEmbOfFin_univ J rfl]
    rw [Finset.sum_map]
    rfl
  have htrans : ∀ (c : ℝ) (l₁ l₂ : List ℝ),
      List.zipWith (fun p r => r - p) (l₁.map (fun s => s + c)) (l₂.map (fun s => s + c))
        = List.zipWith (fun p r => r - p) l₁ l₂ := by
    intro c l₁
    induction l₁ with
    | nil => intro l₂; cases l₂ <;> simp [List.zipWith]
    | cons a as ih =>
      intro l₂
      cases l₂ with
      | nil => simp [List.zipWith]
      | cons b bs =>
        have h : (b + c) - (a + c) = b - a := by ring
        simp [List.zipWith, ih bs, h]
  have hmap_tail : ∀ (c : ℝ) (l : List ℝ),
      List.zipWith (fun p r => r - p) (l.map (fun s => s + c)) ((l.map (fun s => s + c)).tail)
        = List.zipWith (fun p r => r - p) l l.tail := by
    intro c l
    have hmt : (l.map (fun s : ℝ => s + c)).tail = l.tail.map (fun s : ℝ => s + c) := by
      cases l <;> rfl
    rw [hmt, htrans c l l.tail]





  change (∑ i ∈ I, blk i) = Multiset.ofList (List.zipWith (fun p r => r - p) (SI.sort (· ≤ ·)) (SI.sort (· ≤ ·)).tail)
       ∧ (∑ j ∈ J, blk j) = Multiset.ofList (List.zipWith (fun p r => r - p) (SJ.sort (· ≤ ·)) (SJ.sort (· ≤ ·)).tail)
  refine ⟨?_, ?_⟩
  · rw [hreindexI]
    obtain ⟨p, hp, hpc, hps, himg, hp0, hplast⟩ := statopia_math_node_2789815743_0d7f93cf q a ha_pos I
    have hM : ∀ x ∈ bdJ.filter (fun x => 0 < x ∧ x < U), p 0 ≤ x ∧ x ≤ p (Fin.last I.card) := by
      intro x hx
      rw [Finset.mem_filter] at hx
      exact ⟨by rw [hp0]; exact le_of_lt hx.2.1, le_of_lt (by rw [hplast]; exact hx.2.2)⟩
    have htileI : ∀ k : Fin I.card, blk (I.orderEmbOfFin rfl k) =
        Multiset.ofList (List.zipWith (fun p r => r - p)
          (p (Fin.castSucc k) :: ((bdJ.filter (fun x => 0 < x ∧ x < U)).filter (fun x => p (Fin.castSucc k) < x ∧ x < p (Fin.succ k))).sort (· ≤ ·) ++ [p (Fin.succ k)])
          (p (Fin.castSucc k) :: ((bdJ.filter (fun x => 0 < x ∧ x < U)).filter (fun x => p (Fin.castSucc k) < x ∧ x < p (Fin.succ k))).sort (· ≤ ·) ++ [p (Fin.succ k)]).tail) := by
      intro k
      let i : Fin q := ↑(I.orderEmbOfFin rfl k)
      let c : ℝ := b (i : ℕ) - iLo i
      have hmem : i ∈ I := by
        rw [← Finset.image_orderEmbOfFin_univ I rfl]
        exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩
      have hpc' : p (Fin.castSucc k) = iLo i := hpc k
      have hps' : p (Fin.succ k) = iHi i := hps k
      rw [hpc', hps']
      have hiso := statopia_math_node_428735515_34bc9020 q a ha_pos I J hIJ i hmem
      have hb1 : b (i : ℕ) = iLo i + c := by
        show b (i : ℕ) = iLo i + (b (i : ℕ) - iLo i)
        ring
      have hb2 : b ((i : ℕ) + 1) = iHi i + c := by
        show b ((i : ℕ) + 1) = iHi i + (b (i : ℕ) - iLo i)
        rw [hb_step i, hiHi_eq i, if_pos hmem]
        ring
      have hiso' : ((C.filter (fun d => b (i : ℕ) < d ∧ d < b ((i : ℕ) + 1))).sort (· ≤ ·))
          = List.map (fun s : ℝ => s + c)
              (((bdJ.filter (fun x => 0 < x ∧ x < U)).filter (fun x => iLo i < x ∧ x < iHi i)).sort (· ≤ ·)) := by
        rw [hiso]
      have hlist : (b (i : ℕ) :: ((C.filter (fun d => b (i : ℕ) < d ∧ d < b ((i : ℕ) + 1))).sort (· ≤ ·)) ++ [b ((i : ℕ) + 1)])
          = List.map (fun s : ℝ => s + c)
              ((iLo i :: ((bdJ.filter (fun x => 0 < x ∧ x < U)).filter (fun x => iLo i < x ∧ x < iHi i)).sort (· ≤ ·)) ++ [iHi i]) := by
        rw [hiso']
        simp only [List.map_append, List.map_cons, List.map_nil]
        rw [hb1, hb2]
      have hblk : blk (↑(I.orderEmbOfFin rfl k)) = Multiset.ofList (List.zipWith (fun p r => r - p)
          (b (i : ℕ) :: ((C.filter (fun d => b (i : ℕ) < d ∧ d < b ((i : ℕ) + 1))).sort (· ≤ ·)) ++ [b ((i : ℕ) + 1)])
          ((b (i : ℕ) :: ((C.filter (fun d => b (i : ℕ) < d ∧ d < b ((i : ℕ) + 1))).sort (· ≤ ·)) ++ [b ((i : ℕ) + 1)]).tail)) := rfl
      rw [hblk, hlist, hmap_tail c
        (iLo i :: ((bdJ.filter (fun x => 0 < x ∧ x < U)).filter (fun x => iLo i < x ∧ x < iHi i)).sort (· ≤ ·) ++ [iHi i])]
    rw [Finset.sum_congr rfl (fun k _ => htileI k),
      statopia_math_node_689319304_41a3eefa I.card p (bdJ.filter (fun x => 0 < x ∧ x < U)) hp hM, himg]
  · rw [hreindexJ]
    obtain ⟨p, hp, hpc, hps, himg, hp0, hplast⟩ := statopia_math_node_2789815743_0d7f93cf q a ha_pos J
    have hM : ∀ x ∈ bdI.filter (fun x => 0 < x ∧ x < W), p 0 ≤ x ∧ x ≤ p (Fin.last J.card) := by
      intro x hx
      rw [Finset.mem_filter] at hx
      exact ⟨by rw [hp0]; exact le_of_lt hx.2.1, le_of_lt (by rw [hplast]; exact hx.2.2)⟩
    have hCeq : (C : Finset ℝ) =
        ((J ×ˢ bdI).filter (fun ks => jLo ks.1 < ks.2 ∧ ks.2 < jHi ks.1)).image
            (fun ks => b (ks.1 : ℕ) + (ks.2 - jLo ks.1)) ∪
          ((I ×ˢ bdJ).filter (fun ks => iLo ks.1 < ks.2 ∧ ks.2 < iHi ks.1)).image
            (fun ks => b (ks.1 : ℕ) + (ks.2 - iLo ks.1)) := by
      show (((I ×ˢ bdJ).filter (fun ks => iLo ks.1 < ks.2 ∧ ks.2 < iHi ks.1)).image
            (fun ks => b (ks.1 : ℕ) + (ks.2 - iLo ks.1)) ∪
          ((J ×ˢ bdI).filter (fun ks => jLo ks.1 < ks.2 ∧ ks.2 < jHi ks.1)).image
            (fun ks => b (ks.1 : ℕ) + (ks.2 - jLo ks.1)))
        = ((J ×ˢ bdI).filter (fun ks => jLo ks.1 < ks.2 ∧ ks.2 < jHi ks.1)).image
            (fun ks => b (ks.1 : ℕ) + (ks.2 - jLo ks.1)) ∪
          ((I ×ˢ bdJ).filter (fun ks => iLo ks.1 < ks.2 ∧ ks.2 < iHi ks.1)).image
            (fun ks => b (ks.1 : ℕ) + (ks.2 - iLo ks.1))
      ext x
      simp only [Finset.mem_union]
      tauto
    have htileJ : ∀ k : Fin J.card, blk (J.orderEmbOfFin rfl k) =
        Multiset.ofList (List.zipWith (fun p r => r - p)
          (p (Fin.castSucc k) :: ((bdI.filter (fun x => 0 < x ∧ x < W)).filter (fun x => p (Fin.castSucc k) < x ∧ x < p (Fin.succ k))).sort (· ≤ ·) ++ [p (Fin.succ k)])
          (p (Fin.castSucc k) :: ((bdI.filter (fun x => 0 < x ∧ x < W)).filter (fun x => p (Fin.castSucc k) < x ∧ x < p (Fin.succ k))).sort (· ≤ ·) ++ [p (Fin.succ k)]).tail) := by
      intro k
      let j : Fin q := ↑(J.orderEmbOfFin rfl k)
      let c : ℝ := b (j : ℕ) - jLo j
      have hmem : j ∈ J := by
        rw [← Finset.image_orderEmbOfFin_univ J rfl]
        exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩
      have hpc' : p (Fin.castSucc k) = jLo j := hpc k
      have hps' : p (Fin.succ k) = jHi j := hps k
      rw [hpc', hps']
      have hiso := statopia_math_node_428735515_34bc9020 q a ha_pos J I hIJ.symm j hmem
      have hb1 : b (j : ℕ) = jLo j + c := by
        show b (j : ℕ) = jLo j + (b (j : ℕ) - jLo j)
        ring
      have hb2 : b ((j : ℕ) + 1) = jHi j + c := by
        show b ((j : ℕ) + 1) = jHi j + (b (j : ℕ) - jLo j)
        rw [hb_step j, hjHi_eq j, if_pos hmem]
        ring
      have hiso' : ((C.filter (fun d => b (j : ℕ) < d ∧ d < b ((j : ℕ) + 1))).sort (· ≤ ·))
          = List.map (fun s : ℝ => s + c)
              (((bdI.filter (fun x => 0 < x ∧ x < W)).filter (fun x => jLo j < x ∧ x < jHi j)).sort (· ≤ ·)) := by
        simpa only [hCeq] using hiso
      have hlist : (b (j : ℕ) :: ((C.filter (fun d => b (j : ℕ) < d ∧ d < b ((j : ℕ) + 1))).sort (· ≤ ·)) ++ [b ((j : ℕ) + 1)])
          = List.map (fun s : ℝ => s + c)
              ((jLo j :: ((bdI.filter (fun x => 0 < x ∧ x < W)).filter (fun x => jLo j < x ∧ x < jHi j)).sort (· ≤ ·)) ++ [jHi j]) := by
        rw [hiso']
        simp only [List.map_append, List.map_cons, List.map_nil]
        rw [hb1, hb2]
      have hblk : blk (↑(J.orderEmbOfFin rfl k)) = Multiset.ofList (List.zipWith (fun p r => r - p)
          (b (j : ℕ) :: ((C.filter (fun d => b (j : ℕ) < d ∧ d < b ((j : ℕ) + 1))).sort (· ≤ ·)) ++ [b ((j : ℕ) + 1)])
          ((b (j : ℕ) :: ((C.filter (fun d => b (j : ℕ) < d ∧ d < b ((j : ℕ) + 1))).sort (· ≤ ·)) ++ [b ((j : ℕ) + 1)]).tail)) := rfl
      rw [hblk, hlist, hmap_tail c
        (jLo j :: ((bdI.filter (fun x => 0 < x ∧ x < W)).filter (fun x => jLo j < x ∧ x < jHi j)).sort (· ≤ ·) ++ [jHi j])]
    rw [Finset.sum_congr rfl (fun k _ => htileJ k),
      statopia_math_node_689319304_41a3eefa J.card p (bdI.filter (fun x => 0 < x ∧ x < W)) hp hM, himg]
  /- @proof-region region.target-node.session.32cedbb93f9caee7 end -/

end LiuBangXiangYu
