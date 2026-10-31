import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base

open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_3426023923_ba29e974 : ∀ (q : ℕ) (hq : 1 ≤ q) (a : Fin q → ℝ) (ha_pos : ∀ i, 0 < a i)
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
    let gI : Multiset ℝ :=
      Multiset.ofList (List.zipWith (fun p r => r - p) (SI.sort (· ≤ ·)) (SI.sort (· ≤ ·)).tail)
    let gJ : Multiset ℝ :=
      Multiset.ofList (List.zipWith (fun p r => r - p) (SJ.sort (· ≤ ·)) (SJ.sort (· ≤ ·)).tail)
    let E : List ℝ := (bdI.filter (fun x => W < x)).sort (· ≤ ·)
    let R : Multiset ℝ :=
      Multiset.ofList (List.zipWith (fun p r => r - p) (W :: E) (W :: E).tail)
    gI = gJ + R ∧ (W :: E).getLastD 0 = U := by
  /- @proof-region region.target-node.session.f8a340afc4798832 begin -/
  intro q hq a ha_pos I J hIJ hUW
  dsimp only
  set iHi : Fin q → ℝ := fun k => ∑ i ∈ I, if (i : ℕ) ≤ (k : ℕ) then a i else 0 with hiHi
  set jHi : Fin q → ℝ := fun k => ∑ j ∈ J, if (j : ℕ) ≤ (k : ℕ) then a j else 0 with hjHi
  set bdI : Finset ℝ := I.image iHi with hbdI
  set bdJ : Finset ℝ := J.image jHi with hbdJ
  set U : ℝ := ∑ i ∈ I, a i with hU
  set W : ℝ := ∑ j ∈ J, a j with hW
  set F : Finset ℝ := bdI.filter (fun x => W < x) with hF
  set SI : Finset ℝ := {0} ∪ bdI ∪ (bdJ.filter (fun x => 0 < x ∧ x < U)) with hSI
  set SJ : Finset ℝ := {0} ∪ bdJ ∪ (bdI.filter (fun x => 0 < x ∧ x < W)) with hSJ
  set gI : Multiset ℝ := Multiset.ofList (List.zipWith (fun p r => r - p) (SI.sort (· ≤ ·)) (SI.sort (· ≤ ·)).tail) with hgI
  set gJ : Multiset ℝ := Multiset.ofList (List.zipWith (fun p r => r - p) (SJ.sort (· ≤ ·)) (SJ.sort (· ≤ ·)).tail) with hgJ
  set E : List ℝ := F.sort (· ≤ ·) with hE
  set R : Multiset ℝ := Multiset.ofList (List.zipWith (fun p r => r - p) (W :: E) (W :: E).tail) with hR
  have hIpos : ∀ x ∈ bdI, 0 < x := by
    intro x hx
    rw [hbdI, Finset.mem_image] at hx
    obtain ⟨i, hiI, rfl⟩ := hx
    change 0 < ∑ i' ∈ I, (if (i' : ℕ) ≤ (i : ℕ) then a i' else 0)
    have hle : a i ≤ ∑ i' ∈ I, (if (i' : ℕ) ≤ (i : ℕ) then a i' else 0) := by
      have h := Finset.single_le_sum (s := I) (a := i)
        (f := fun k : Fin q => if (k : ℕ) ≤ (i : ℕ) then a k else 0)
        (fun k _ => by
          show 0 ≤ (if (k : ℕ) ≤ (i : ℕ) then a k else 0)
          by_cases hk : (k : ℕ) ≤ (i : ℕ)
          · rw [if_pos hk]; exact le_of_lt (ha_pos k)
          · rw [if_neg hk] <;> exact le_refl 0) hiI
      simpa using h
    exact lt_of_lt_of_le (ha_pos i) hle
  have hJpos : ∀ x ∈ bdJ, 0 < x := by
    intro x hx
    rw [hbdJ, Finset.mem_image] at hx
    obtain ⟨j, hjJ, rfl⟩ := hx
    change 0 < ∑ j' ∈ J, (if (j' : ℕ) ≤ (j : ℕ) then a j' else 0)
    have hle : a j ≤ ∑ j' ∈ J, (if (j' : ℕ) ≤ (j : ℕ) then a j' else 0) := by
      have h := Finset.single_le_sum (s := J) (a := j)
        (f := fun k : Fin q => if (k : ℕ) ≤ (j : ℕ) then a k else 0)
        (fun k _ => by
          show 0 ≤ (if (k : ℕ) ≤ (j : ℕ) then a k else 0)
          by_cases hk : (k : ℕ) ≤ (j : ℕ)
          · rw [if_pos hk]; exact le_of_lt (ha_pos k)
          · rw [if_neg hk] <;> exact le_refl 0) hjJ
      simpa using h
    exact lt_of_lt_of_le (ha_pos j) hle
  have hIleU : ∀ x ∈ bdI, x ≤ U := by
    intro x hx
    rw [hbdI, Finset.mem_image] at hx
    obtain ⟨i, hiI, rfl⟩ := hx
    rw [hU]
    change (∑ i' ∈ I, (if (i' : ℕ) ≤ (i : ℕ) then a i' else 0)) ≤ ∑ i' ∈ I, a i'
    apply Finset.sum_le_sum
    intro i' hi'I
    by_cases hk : (i' : ℕ) ≤ (i : ℕ)
    · rw [if_pos hk]
    · rw [if_neg hk]; exact le_of_lt (ha_pos i')
  have hJleW : ∀ x ∈ bdJ, x ≤ W := by
    intro x hx
    rw [hbdJ, Finset.mem_image] at hx
    obtain ⟨j, hjJ, rfl⟩ := hx
    rw [hW]
    change (∑ j' ∈ J, (if (j' : ℕ) ≤ (j : ℕ) then a j' else 0)) ≤ ∑ j' ∈ J, a j'
    apply Finset.sum_le_sum
    intro j' hj'J
    by_cases hk : (j' : ℕ) ≤ (j : ℕ)
    · rw [if_pos hk]
    · rw [if_neg hk]; exact le_of_lt (ha_pos j')
  have hIne_U : I.Nonempty → U ∈ bdI := by
    intro hne
    obtain ⟨im, himI, hmax⟩ := Finset.exists_max_image I (fun i => (i : ℕ)) hne
    rw [hbdI, Finset.mem_image]
    refine ⟨im, himI, ?_⟩
    rw [hU]
    change (∑ i' ∈ I, (if (i' : ℕ) ≤ (im : ℕ) then a i' else 0)) = ∑ i' ∈ I, a i'
    apply Finset.sum_congr rfl
    intro i' hi'I
    rw [if_pos (hmax i' hi'I)]
  have hJne_W : J.Nonempty → W ∈ bdJ := by
    intro hne
    obtain ⟨jm, hjmJ, hmax⟩ := Finset.exists_max_image J (fun j => (j : ℕ)) hne
    rw [hbdJ, Finset.mem_image]
    refine ⟨jm, hjmJ, ?_⟩
    rw [hW]
    change (∑ j' ∈ J, (if (j' : ℕ) ≤ (jm : ℕ) then a j' else 0)) = ∑ j' ∈ J, a j'
    apply Finset.sum_congr rfl
    intro j' hj'J
    rw [if_pos (hmax j' hj'J)]
  have hU0 : I = ∅ → U = 0 := by intro hI; rw [hU, hI]; simp
  have hW0 : J = ∅ → W = 0 := by intro hJ; rw [hW, hJ]; simp
  have hWnn : 0 ≤ W := by rw [hW]; exact Finset.sum_nonneg (fun j _ => le_of_lt (ha_pos j))
  have hIne_of_Upos : 0 < U → I.Nonempty := by
    intro hUp
    rcases Finset.eq_empty_or_nonempty I with h | h
    · rw [hU0 h] at hUp; exact absurd hUp (lt_irrefl 0)
    · exact h
  have hJne_of_Wpos : 0 < W → J.Nonempty := by
    intro hWp
    rcases Finset.eq_empty_or_nonempty J with h | h
    · rw [hW0 h] at hWp; exact absurd hWp (lt_irrefl 0)
    · exact h
  have h0SI : (0 : ℝ) ∈ SI := by simp [hSI]
  have h0SJ : (0 : ℝ) ∈ SJ := by simp [hSJ]
  have hbdI_SI : bdI ⊆ SI := by
    intro x hx
    rw [hSI]
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hx)))
  have hbdJ_SJ : bdJ ⊆ SJ := by
    intro x hx
    rw [hSJ]
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hx)))
  have hbdI_filter_SJ : bdI.filter (fun x => 0 < x ∧ x < W) ⊆ SJ := by
    intro x hx
    rw [hSJ]
    exact Finset.mem_union.mpr (Or.inr hx)
  have hF_SI : F ⊆ SI := by
    intro x hx
    rw [hF] at hx
    exact hbdI_SI (Finset.mem_filter.mp hx).1
  have hW_SJ : W ∈ SJ := by
    rcases lt_or_eq_of_le hWnn with h | h
    · exact hbdJ_SJ (hJne_W (hJne_of_Wpos h))
    · rw [← h]; exact h0SJ
  have hbdJ_SI : bdJ ⊆ SI := by
    intro x hx
    have hx0 : 0 < x := hJpos x hx
    have hxU : x ≤ U := le_trans (hJleW x hx) hUW
    rcases lt_or_eq_of_le hxU with hxlt | hxeq
    · rw [hSI]
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hx, hx0, hxlt⟩))
    · have hxU0 : 0 < U := hxeq ▸ hx0
      exact hbdI_SI (hxeq.symm ▸ (hIne_U (hIne_of_Upos hxU0)))
  have hsub1 : SJ ∪ F ⊆ SI := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rw [hSJ] at hx
      rcases Finset.mem_union.mp hx with hx | hx
      · rcases Finset.mem_union.mp hx with hx | hx
        · rw [Finset.mem_singleton] at hx
          rw [hx]; exact h0SI
        · exact hbdJ_SI hx
      · exact hbdI_SI (Finset.mem_filter.mp hx).1
    · exact hF_SI hx
  have hsub2 : SI ⊆ SJ ∪ F := by
    intro x hx
    rw [hSI] at hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_union.mp hx with hx | hx
      · rw [Finset.mem_singleton] at hx
        rw [hx]
        exact Finset.mem_union.mpr (Or.inl h0SJ)
      · by_cases hWx : W < x
        · exact Finset.mem_union.mpr (Or.inr (by rw [hF]; exact Finset.mem_filter.mpr ⟨hx, hWx⟩))
        · push_neg at hWx
          rcases lt_or_eq_of_le hWx with hxlt | hxeq
          · exact Finset.mem_union.mpr (Or.inl (hbdI_filter_SJ (Finset.mem_filter.mpr ⟨hx, hIpos x hx, hxlt⟩)))
          · rw [hxeq]
            exact Finset.mem_union.mpr (Or.inl hW_SJ)
    · exact Finset.mem_union.mpr (Or.inl (hbdJ_SJ (Finset.mem_filter.mp hx).1))
  have hSI_eq : SI = SJ ∪ F := Finset.Subset.antisymm hsub2 hsub1
  have pair_append : ∀ (l₁ l₂ : List ℝ), l₁.Pairwise (· ≤ ·) → l₂.Pairwise (· ≤ ·) →
      (∀ a ∈ l₁, ∀ b ∈ l₂, a ≤ b) → (l₁ ++ l₂).Pairwise (· ≤ ·) := by
    intro l₁
    induction l₁ with
    | nil => intro l₂ _ h₂ _; simpa using h₂
    | cons x xs ih =>
      intro l₂ h₁ h₂ hc
      cases h₁ with
      | cons hhead htail =>
        show (x :: (xs ++ l₂)).Pairwise (· ≤ ·)
        refine List.Pairwise.cons ?_ ?_
        · intro b hb
          rcases List.mem_append.mp hb with hb | hb
          · exact hhead b hb
          · exact hc x (by simp) b hb
        · exact ih l₂ htail h₂ (fun a ha b hb => hc a (by simp [ha]) b hb)
  have nodup_append : ∀ (l₁ l₂ : List ℝ), l₁.Nodup → l₂.Nodup →
      (∀ a ∈ l₁, a ∉ l₂) → (l₁ ++ l₂).Nodup := by
    intro l₁
    induction l₁ with
    | nil => intro l₂ _ h₂ _; simpa using h₂
    | cons x xs ih =>
      intro l₂ h₁ h₂ hc
      rw [List.nodup_cons] at h₁
      obtain ⟨hx, hxs⟩ := h₁
      show (x :: (xs ++ l₂)).Nodup
      rw [List.nodup_cons]
      refine ⟨?_, ?_⟩
      · intro hb
        rcases List.mem_append.mp hb with hb | hb
        · exact hx hb
        · exact hc x (by simp) hb
      · exact ih l₂ hxs h₂ (fun a ha => hc a (by simp [ha]))
  have hSJ_le_W : ∀ x ∈ SJ, x ≤ W := by
    intro x hx
    rw [hSJ] at hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_union.mp hx with hx | hx
      · rw [Finset.mem_singleton] at hx
        rw [hx]; exact hWnn
      · exact hJleW x hx
    · exact le_of_lt (Finset.mem_filter.mp hx).2.2
  have hF_gt_W : ∀ x ∈ F, W < x := by
    intro x hx
    rw [hF] at hx
    exact (Finset.mem_filter.mp hx).2
  have hcross : ∀ a ∈ SJ.sort (· ≤ ·), ∀ b ∈ E, a ≤ b := by
    intro a ha b hb
    have ha' : a ∈ SJ := (Finset.mem_sort (· ≤ ·)).mp ha
    have hb' : b ∈ F := by rw [hE] at hb; exact (Finset.mem_sort (· ≤ ·)).mp hb
    have h1 : a ≤ W := hSJ_le_W a ha'
    have h2 : W < b := hF_gt_W b hb'
    linarith
  have hdisj : ∀ a ∈ SJ.sort (· ≤ ·), a ∉ E := by
    intro a ha hb
    have ha' : a ∈ SJ := (Finset.mem_sort (· ≤ ·)).mp ha
    have hb' : a ∈ F := by rw [hE] at hb; exact (Finset.mem_sort (· ≤ ·)).mp hb
    have h1 : a ≤ W := hSJ_le_W a ha'
    have h2 : W < a := hF_gt_W a hb'
    linarith
  have hE_nodup : E.Nodup := by rw [hE]; exact Finset.sort_nodup F (· ≤ ·)
  have hE_pair : E.Pairwise (· ≤ ·) := by rw [hE]; exact Finset.pairwise_sort F (· ≤ ·)
  have hpair : (SJ.sort (· ≤ ·) ++ E).Pairwise (· ≤ ·) :=
    pair_append _ _ (Finset.pairwise_sort SJ (· ≤ ·)) hE_pair hcross
  have hnd : (SJ.sort (· ≤ ·) ++ E).Nodup :=
    nodup_append _ _ (Finset.sort_nodup SJ (· ≤ ·)) hE_nodup hdisj
  have htoFinset : (SJ.sort (· ≤ ·) ++ E).toFinset = SI := by
    rw [List.toFinset_append]
    have h1 : (SJ.sort (· ≤ ·)).toFinset = SJ := Finset.sort_toFinset SJ (· ≤ ·)
    have h2 : E.toFinset = F := by rw [hE]; exact Finset.sort_toFinset F (· ≤ ·)
    rw [h1, h2, hSI_eq]
  have hSI_sort : SI.sort (· ≤ ·) = SJ.sort (· ≤ ·) ++ E := by
    have h := (List.toFinset_sort (· ≤ ·) hnd).mpr hpair
    rw [htoFinset] at h
    exact h
  have getLastD_mem : ∀ (l : List ℝ), l ≠ [] → l.getLastD 0 ∈ l := by
    intro l
    induction l with
    | nil => intro h; exact absurd rfl h
    | cons x t ih =>
      intro _
      cases t with
      | nil => simp
      | cons y t' =>
        have h := ih (by simp)
        show (y :: t').getLastD 0 ∈ x :: y :: t'
        rw [List.mem_cons]
        exact Or.inr h
  have getLastD_eq_max : ∀ (l : List ℝ) (u : ℝ), l.Pairwise (· ≤ ·) → u ∈ l →
      (∀ z ∈ l, z ≤ u) → l.getLastD 0 = u := by
    intro l
    induction l with
    | nil => intro u _ hu _; simp at hu
    | cons x t ih =>
      intro u hpair hu hle
      cases hpair with
      | cons hhead htail =>
        cases t with
        | nil =>
          simp at hu
          rw [hu]
          simp
        | cons y t' =>
          by_cases hut : u ∈ (y :: t')
          · have hres := ih u htail hut (fun z hz => hle z (by rw [List.mem_cons]; exact Or.inr hz))
            show (x :: y :: t').getLastD 0 = u
            exact hres
          · rw [List.mem_cons] at hu
            rcases hu with hu | hu
            · rw [hu] at hle ⊢
              have hmem : (y :: t').getLastD 0 ∈ (y :: t') := getLastD_mem _ (by simp)
              have h1 : x ≤ (y :: t').getLastD 0 := hhead _ hmem
              have h2 : (y :: t').getLastD 0 ≤ x := hle _ (by rw [List.mem_cons]; exact Or.inr hmem)
              exact le_antisymm h2 h1
            · exact absurd hu hut
  have getLastD_singleton : ∀ (w : ℝ), (w :: ([] : List ℝ)).getLastD 0 = w := by
    intro w; simp
  have getLastD_cons_ne : ∀ (w : ℝ) (L : List ℝ), L ≠ [] → (w :: L).getLastD 0 = L.getLastD 0 := by
    intro w L hL
    cases L with
    | nil => exact absurd rfl hL
    | cons y t => simp
  have exists_mem_ne_nil : ∀ (l : List ℝ), l ≠ [] → ∃ x, x ∈ l := by
    intro l
    cases l with
    | nil => intro h; exact absurd rfl h
    | cons y t => intro _; exact ⟨y, by simp⟩
  have hSJ_ne : SJ.sort (· ≤ ·) ≠ [] := by
    intro h
    have hmem : (0 : ℝ) ∈ SJ.sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).mpr h0SJ
    rw [h] at hmem
    simp at hmem
  have hSJ_last : (SJ.sort (· ≤ ·)).getLastD 0 = W :=
    getLastD_eq_max _ _ (Finset.pairwise_sort SJ (· ≤ ·))
      ((Finset.mem_sort (· ≤ ·)).mpr hW_SJ)
      (fun z hz => hSJ_le_W z ((Finset.mem_sort (· ≤ ·)).mp hz))
  have zipWith_cons : ∀ (a b : ℝ) (as bs : List ℝ),
      List.zipWith (fun p r => r - p) (a :: as) (b :: bs)
        = (b - a) :: List.zipWith (fun p r => r - p) as bs := by
    intro a b as bs
    rfl
  have gap_append : ∀ (A E : List ℝ), A ≠ [] → A.getLastD 0 = W →
      List.zipWith (fun p r => r - p) (A ++ E) (A ++ E).tail
        = List.zipWith (fun p r => r - p) A A.tail
          ++ List.zipWith (fun p r => r - p) (W :: E) (W :: E).tail := by
    intro A
    induction A with
    | nil => intro E h _; exact absurd rfl h
    | cons x t ih =>
      intro E _ hx
      cases t with
      | nil =>
        have hxw : x = W := hx
        rw [hxw]
        rfl
      | cons y t' =>
        have hstep : List.zipWith (fun p r => r - p) (y :: (t' ++ E)) (t' ++ E)
            = List.zipWith (fun p r => r - p) (y :: t') t'
              ++ List.zipWith (fun p r => r - p) (W :: E) (W :: E).tail := ih E (by simp) hx
        show List.zipWith (fun p r => r - p) (x :: y :: (t' ++ E)) (y :: (t' ++ E))
            = List.zipWith (fun p r => r - p) (x :: y :: t') (y :: t')
              ++ List.zipWith (fun p r => r - p) (W :: E) (W :: E).tail
        rw [zipWith_cons x y (y :: t') t', zipWith_cons x y (y :: (t' ++ E)) (t' ++ E), hstep] <;> rfl
  have hG : List.zipWith (fun p r => r - p) (SI.sort (· ≤ ·)) (SI.sort (· ≤ ·)).tail
      = List.zipWith (fun p r => r - p) (SJ.sort (· ≤ ·)) (SJ.sort (· ≤ ·)).tail
        ++ List.zipWith (fun p r => r - p) (W :: E) (W :: E).tail := by
    rw [hSI_sort]
    exact gap_append (SJ.sort (· ≤ ·)) E hSJ_ne hSJ_last
  constructor
  · rw [hgI, hgJ, hR, hG]
    exact Multiset.coe_add _ _
  · by_cases hE0 : E = []
    · have hEF : E.toFinset = F := by rw [hE]; exact Finset.sort_toFinset F (· ≤ ·)
      have hFnil : F = ∅ := by
        rw [hE0] at hEF
        simpa using hEF.symm
      have hUleW : U ≤ W := by
        rcases Finset.eq_empty_or_nonempty I with hI0 | hIne
        · rw [hU0 hI0]; exact hWnn
        · have hUnF : U ∉ F := by rw [hFnil]; simp
          refine le_of_not_gt (fun hWU => hUnF ?_)
          rw [hF]
          exact Finset.mem_filter.mpr ⟨hIne_U hIne, hWU⟩
      have hWU : W = U := le_antisymm hUW hUleW
      rw [hE0, getLastD_singleton W, hWU]
    · obtain ⟨x, hxE⟩ := exists_mem_ne_nil E hE0
      have hxF : x ∈ F := by rw [hE] at hxE; exact (Finset.mem_sort (· ≤ ·)).mp hxE
      have hxF' : x ∈ bdI.filter (fun y => W < y) := by rw [← hF]; exact hxF
      have hxb : x ∈ bdI := (Finset.mem_filter.mp hxF').1
      have hxW : W < x := hF_gt_W x hxF
      have hxU : x ≤ U := hIleU x hxb
      have hWltU : W < U := by linarith
      have hUpos : (0 : ℝ) < U := by linarith
      have hUinF : U ∈ F := by
        rw [hF]
        exact Finset.mem_filter.mpr ⟨hIne_U (hIne_of_Upos hUpos), hWltU⟩
      have hUinE : U ∈ E := by
        rw [hE]
        exact (Finset.mem_sort (· ≤ ·)).mpr hUinF
      have hleE : ∀ z ∈ E, z ≤ U := by
        intro z hz
        have hzF : z ∈ F := by rw [hE] at hz; exact (Finset.mem_sort (· ≤ ·)).mp hz
        exact hIleU z (Finset.mem_filter.mp (by rw [hF] at hzF; exact hzF)).1
      have hElast : E.getLastD 0 = U := getLastD_eq_max E U hE_pair hUinE hleE
      rw [getLastD_cons_ne W E hE0, hElast]
  /- @proof-region region.target-node.session.f8a340afc4798832 end -/

end LiuBangXiangYu
