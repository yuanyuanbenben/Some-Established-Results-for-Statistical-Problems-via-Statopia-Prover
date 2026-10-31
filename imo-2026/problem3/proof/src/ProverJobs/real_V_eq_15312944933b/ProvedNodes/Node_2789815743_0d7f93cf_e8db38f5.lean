import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base

open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_2789815743_0d7f93cf : ∀ (q : ℕ) (a : Fin q → ℝ)
    (ha : ∀ i : Fin q, 0 < a i) (K : Finset (Fin q)),
    let Hi : Fin q → ℝ := fun k => ∑ i ∈ K, if (i : ℕ) ≤ (k : ℕ) then a i else 0
    let Lo : Fin q → ℝ := fun k => ∑ i ∈ K, if (i : ℕ) < (k : ℕ) then a i else 0
    let S : ℝ := ∑ i ∈ K, a i
    ∃ p : Fin (K.card + 1) → ℝ,
      StrictMono p ∧
      (∀ k : Fin K.card, p (Fin.castSucc k) = Lo (K.orderEmbOfFin rfl k)) ∧
      (∀ k : Fin K.card, p (Fin.succ k) = Hi (K.orderEmbOfFin rfl k)) ∧
      (Finset.image p Finset.univ = {0} ∪ K.image Hi) ∧
      p 0 = 0 ∧
      p (Fin.last K.card) = S := by
  /- @proof-region region.target-node.session.fe9a031f46d197b9 begin -/
  classical
  intro q a ha K
  intro Hi Lo S
  let e : Fin K.card ↪o Fin q := K.orderEmbOfFin rfl
  let p : Fin (K.card + 1) → ℝ := fun j => if h : (j : ℕ) < K.card then Lo (e ⟨j, h⟩) else S
  have hplast : p (Fin.last K.card) = S := by
    have hlt : ¬ (((Fin.last K.card : Fin (K.card + 1)) : ℕ) < K.card) :=
      fun h => absurd h (lt_irrefl K.card)
    dsimp only [p]
    rw [dif_neg hlt]
  have hpcast : ∀ k : Fin K.card, p (Fin.castSucc k) = Lo (e k) := by
    intro k
    have hk : ((Fin.castSucc k : Fin (K.card + 1)) : ℕ) < K.card := k.isLt
    have hidx : (⟨Fin.castSucc k, hk⟩ : Fin K.card) = k := by ext; rfl
    dsimp only [p]
    rw [dif_pos hk, hidx]
  have hbridge : ∀ m : Fin K.card, ((K.orderIsoOfFin rfl m : ↥K) : Fin q) = e m :=
    fun m => rfl
  have he_lt : ∀ m k : Fin K.card, e m < e k ↔ m < k := by
    intro m k
    rw [← hbridge m, ← hbridge k]
    exact OrderIso.lt_iff_lt (K.orderIsoOfFin rfl)
  have he_le : ∀ m k : Fin K.card, e m ≤ e k ↔ m ≤ k := by
    intro m k
    constructor
    · intro hle
      by_contra hk
      exact absurd hle (not_le.mpr ((he_lt k m).mpr (lt_of_not_ge hk)))
    · intro hle
      rcases eq_or_lt_of_le hle with h' | h'
      · rw [← h']
      · exact le_of_lt ((he_lt m k).mpr h')
  have hee : Finset.image (⇑e) Finset.univ = K := Finset.image_orderEmbOfFin_univ K rfl
  have hemem : ∀ k : Fin K.card, e k ∈ K := by
    intro k
    have h2 : e k ∈ Finset.image (⇑e) Finset.univ :=
      Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩
    rwa [hee] at h2
  have hex : ∀ x ∈ K, ∃ m : Fin K.card, e m = x := by
    intro x hx
    rw [← hee] at hx
    obtain ⟨m, -, hm⟩ := Finset.mem_image.mp hx
    exact ⟨m, hm⟩
  have hmin : ∀ (h0 : 0 < K.card), Lo (e (⟨0, h0⟩ : Fin K.card)) = 0 := by
    intro h0
    have hzero : ∀ i ∈ K, (if (i : ℕ) < (e (⟨0, h0⟩ : Fin K.card) : ℕ) then a i else 0) = 0 := by
      intro i hi
      rw [← hee] at hi
      obtain ⟨m, -, hm⟩ := Finset.mem_image.mp hi
      rw [← hm]
      exact if_neg (not_lt.mpr ((he_le (⟨0, h0⟩ : Fin K.card) m).mpr (Nat.zero_le _)))
    calc Lo (e (⟨0, h0⟩ : Fin K.card))
        = ∑ i ∈ K, (if (i : ℕ) < (e (⟨0, h0⟩ : Fin K.card) : ℕ) then a i else 0) := rfl
      _ = ∑ i ∈ K, (0 : ℝ) := Finset.sum_congr rfl hzero
      _ = 0 := by simp
  have hmax : ∀ k : Fin K.card, (k : ℕ) + 1 = K.card → Hi (e k) = S := by
    intro k hk
    have hpt : ∀ x ∈ K, (if (x : ℕ) ≤ ((e k : Fin q) : ℕ) then a x else 0) = a x := by
      intro x hx
      obtain ⟨m, hm⟩ := hex x hx
      rw [← hm]
      refine if_pos ?_
      have hmk : (m : ℕ) ≤ (k : ℕ) := by
        have h1 : (m : ℕ) < K.card := m.isLt
        omega
      exact (he_le m k).mpr hmk
    calc Hi (e k) = ∑ x ∈ K, (if (x : ℕ) ≤ ((e k : Fin q) : ℕ) then a x else 0) := rfl
      _ = ∑ x ∈ K, a x := Finset.sum_congr rfl hpt
      _ = S := rfl
  have hsucc : ∀ (k : Fin K.card) (hk : (k : ℕ) + 1 < K.card),
      Lo (e ⟨(k : ℕ) + 1, hk⟩) = Hi (e k) := by
    intro k hk
    have hkey : ∀ x ∈ K,
        ((x : ℕ) < (((e ⟨(k : ℕ) + 1, hk⟩ : Fin q)) : ℕ)) ↔
          ((x : ℕ) ≤ ((e k : Fin q) : ℕ)) := by
      intro x hx
      obtain ⟨m, hm⟩ := hex x hx
      rw [← hm]
      change e m < e ⟨(k : ℕ) + 1, hk⟩ ↔ e m ≤ e k
      constructor
      · intro hlt
        have h1 : m < ⟨(k : ℕ) + 1, hk⟩ := (he_lt m _).mp hlt
        have h2 : (m : ℕ) ≤ (k : ℕ) := by
          have h1' : (m : ℕ) < (k : ℕ) + 1 := h1
          omega
        exact (he_le m k).mpr h2
      · intro hle
        have h1 : m ≤ k := (he_le m k).mp hle
        have h2 : m < ⟨(k : ℕ) + 1, hk⟩ := by
          have h1' : (m : ℕ) < (k : ℕ) + 1 := by
            have h1'' : (m : ℕ) ≤ (k : ℕ) := h1
            omega
          exact h1'
        exact (he_lt m _).mpr h2
    calc Lo (e ⟨(k : ℕ) + 1, hk⟩)
        = ∑ x ∈ K, (if (x : ℕ) < (((e ⟨(k : ℕ) + 1, hk⟩ : Fin q)) : ℕ) then a x else 0) := rfl
      _ = ∑ x ∈ K, (if (x : ℕ) ≤ ((e k : Fin q) : ℕ) then a x else 0) := by
            refine Finset.sum_congr rfl (fun x hx => ?_)
            by_cases hc : ((x : ℕ) < (((e ⟨(k : ℕ) + 1, hk⟩ : Fin q)) : ℕ))
            · rw [if_pos hc, if_pos ((hkey x hx).mp hc)]
            · rw [if_neg hc, if_neg (fun h => hc ((hkey x hx).mpr h))]
      _ = Hi (e k) := rfl
  have hpsucc : ∀ k : Fin K.card, p (Fin.succ k) = Hi (e k) := by
    intro k
    by_cases hk : (k : ℕ) + 1 < K.card
    · have hlt : (((Fin.succ k : Fin (K.card + 1)) : ℕ)) < K.card := hk
      have hidx : (⟨((Fin.succ k : Fin (K.card + 1)) : ℕ), hlt⟩ : Fin K.card) = ⟨(k : ℕ) + 1, hk⟩ := by
        ext; rfl
      dsimp only [p]
      rw [dif_pos hlt, hidx]
      exact hsucc k hk
    · have hk' : (k : ℕ) + 1 = K.card := by
        have h1 : (k : ℕ) < K.card := k.isLt
        omega
      have hlt : ¬ (((Fin.succ k : Fin (K.card + 1)) : ℕ) < K.card) := by
        rw [show ((Fin.succ k : Fin (K.card + 1)) : ℕ) = (k : ℕ) + 1 from rfl, hk']
        exact Nat.lt_irrefl K.card
      dsimp only [p]
      rw [dif_neg hlt]
      exact (hmax k hk').symm
  have hp0 : p 0 = 0 := by
    rcases Nat.eq_zero_or_pos K.card with hc | hc
    · have hK : K = ∅ := Finset.card_eq_zero.mp hc
      have hS : S = 0 := by
        show (∑ i ∈ K, a i) = 0
        rw [hK]
        simp
      have hlt : ¬ (((0 : Fin (K.card + 1)) : ℕ) < K.card) := by
        rw [hc]
        exact Nat.lt_irrefl 0
      dsimp only [p]
      rw [dif_neg hlt]
      exact hS
    · have hlt : (((0 : Fin (K.card + 1)) : ℕ)) < K.card := hc
      have hidx : (⟨((0 : Fin (K.card + 1)) : ℕ), hlt⟩ : Fin K.card) = ⟨0, hc⟩ := by
        ext; rfl
      dsimp only [p]
      rw [dif_pos hlt, hidx]
      exact hmin hc
  have hHiLo : ∀ k : Fin K.card, Hi (e k) = Lo (e k) + a (e k) := by
    intro k
    have hLo : (∑ x ∈ K, (if (x : ℕ) < ((e k : Fin q) : ℕ) then a x else 0)) = Lo (e k) := rfl
    have hsingle0 :
        (∑ x ∈ K, (if x = e k then a x else 0)) = (if e k ∈ K then a (e k) else 0) := by
      simp
    have hsingle : (∑ x ∈ K, (if x = e k then a x else 0)) = a (e k) := by
      rw [hsingle0, if_pos (hemem k)]
    have hpt : ∀ x ∈ K,
        (if (x : ℕ) ≤ ((e k : Fin q) : ℕ) then a x else 0)
          = (if (x : ℕ) < ((e k : Fin q) : ℕ) then a x else 0)
            + (if x = e k then a x else 0) := by
      intro x hx
      obtain ⟨m, hm⟩ := hex x hx
      rw [← hm]
      change (if e m ≤ e k then a (e m) else 0)
          = (if e m < e k then a (e m) else 0) + (if e m = e k then a (e m) else 0)
      rcases lt_trichotomy m k with h | h | h
      · rw [if_pos ((he_le m k).mpr (le_of_lt h)), if_pos ((he_lt m k).mpr h),
          if_neg (ne_of_lt ((he_lt m k).mpr h))]
        ring
      · rw [h, if_pos le_rfl, if_neg (lt_irrefl (e k)), if_pos rfl]
        ring
      · have hle : ¬ (e m ≤ e k) := not_le.mpr ((he_lt k m).mpr h)
        have hge : ¬ (e m < e k) := not_lt.mpr (le_of_lt ((he_lt k m).mpr h))
        rw [if_neg hle, if_neg hge, if_neg (ne_of_gt ((he_lt k m).mpr h))]
        ring
    calc Hi (e k)
        = ∑ x ∈ K, (if (x : ℕ) ≤ ((e k : Fin q) : ℕ) then a x else 0) := rfl
      _ = ∑ x ∈ K, ((if (x : ℕ) < ((e k : Fin q) : ℕ) then a x else 0)
            + (if x = e k then a x else 0)) := Finset.sum_congr rfl hpt
      _ = (∑ x ∈ K, (if (x : ℕ) < ((e k : Fin q) : ℕ) then a x else 0))
            + ∑ x ∈ K, (if x = e k then a x else 0) := Finset.sum_add_distrib
      _ = Lo (e k) + a (e k) := by rw [hLo, hsingle]
  have hmono : StrictMono p := by
    let P : ℕ → ℝ := fun j => if h : j < K.card then Lo (e ⟨j, h⟩) else S
    have hpP : ∀ j : Fin (K.card + 1), p j = P (j : ℕ) := fun j => rfl
    have hstep : ∀ j : ℕ, j + 1 ≤ K.card → P j < P (j + 1) := by
      intro j hj
      have hj' : j < K.card := by omega
      have hPj : P j = Lo (e ⟨j, hj'⟩) := by
        dsimp only [P]
        rw [dif_pos hj']
      have hH : Hi (e ⟨j, hj'⟩) = Lo (e ⟨j, hj'⟩) + a (e ⟨j, hj'⟩) := hHiLo ⟨j, hj'⟩
      have hpos : 0 < a (e ⟨j, hj'⟩) := ha _
      rw [hPj]
      by_cases hcase : j + 1 < K.card
      · have hPj1 : P (j + 1) = Lo (e ⟨j + 1, hcase⟩) := by
          dsimp only [P]
          rw [dif_pos hcase]
        have hbr : Lo (e ⟨j + 1, hcase⟩) = Hi (e ⟨j, hj'⟩) := hsucc ⟨j, hj'⟩ hcase
        rw [hPj1, hbr, hH]
        linarith
      · have hcast : j + 1 = K.card := by omega
        have hcast' : (⟨j, hj'⟩ : Fin K.card).val + 1 = K.card := hcast
        have hPj1 : P (j + 1) = S := by
          dsimp only [P]
          rw [dif_neg (show ¬ (j + 1 < K.card) by omega)]
        have hbr : Hi (e ⟨j, hj'⟩) = S := hmax ⟨j, hj'⟩ hcast'
        rw [hPj1, ← hbr, hH]
        linarith
    have hmonoP : ∀ m n : ℕ, n ≤ K.card → m < n → P m < P n := by
      intro m n
      induction n with
      | zero =>
        intro hn hmn
        exfalso
        omega
      | succ n ih =>
        intro hn hmn
        rcases eq_or_lt_of_le (show m ≤ n by omega) with h | h
        · rw [h]
          exact hstep n hn
        · exact lt_trans (ih (by omega) h) (hstep n hn)
    intro u v huv
    rw [hpP u, hpP v]
    exact hmonoP (u : ℕ) (v : ℕ) (by have := v.isLt; omega) huv
  have himg : Finset.image p Finset.univ = {0} ∪ K.image Hi := by
    have hmemHi : ∀ m : Fin K.card, Hi (e m) ∈ Finset.image p Finset.univ := by
      intro m
      by_cases hmc : (m : ℕ) + 1 < K.card
      · let j : Fin (K.card + 1) := ⟨(m : ℕ) + 1, by omega⟩
        have hjval : (j : ℕ) = (m : ℕ) + 1 := rfl
        have hj : (j : ℕ) < K.card := by rw [hjval]; exact hmc
        have hidx : (⟨(j : ℕ), hj⟩ : Fin K.card) = ⟨(m : ℕ) + 1, hmc⟩ :=
          Fin.ext (by rw [hjval])
        have hpe : p j = Lo (e ⟨(j : ℕ), hj⟩) := by
          dsimp only [p]
          rw [dif_pos hj]
        refine Finset.mem_image.mpr ⟨j, Finset.mem_univ j, ?_⟩
        rw [hpe, hidx]
        exact hsucc m hmc
      · have hmeq : (m : ℕ) + 1 = K.card := by have := m.isLt; omega
        refine Finset.mem_image.mpr ⟨Fin.last K.card, Finset.mem_univ _, ?_⟩
        rw [hmax m hmeq]
        exact hplast
    ext y
    constructor
    · intro hy
      obtain ⟨j, -, hjy⟩ := Finset.mem_image.mp hy
      rw [← hjy]
      by_cases hj : (j : ℕ) < K.card
      · have hpe : p j = Lo (e ⟨(j : ℕ), hj⟩) := by
          dsimp only [p]
          rw [dif_pos hj]
        rw [hpe]
        by_cases hj0 : (j : ℕ) = 0
        · have h0 : 0 < K.card := by omega
          have hidx : (⟨(j : ℕ), hj⟩ : Fin K.card) = ⟨0, h0⟩ := Fin.ext (by rw [hj0])
          rw [hidx, hmin h0]
          simp
        · have hpos : 0 < (j : ℕ) := by omega
          let m : Fin K.card := ⟨(j : ℕ) - 1, by omega⟩
          have hmc : (m : ℕ) + 1 < K.card := by dsimp only [m]; omega
          have hidx : (⟨(j : ℕ), hj⟩ : Fin K.card) = ⟨(m : ℕ) + 1, hmc⟩ :=
            Fin.ext (by dsimp only [m]; omega)
          rw [hidx]
          have hLo_eq : Lo (e ⟨(m : ℕ) + 1, hmc⟩) = Hi (e m) := hsucc m hmc
          rw [hLo_eq]
          exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨e m, hemem m, rfl⟩))
      · have hpe : p j = S := by
          dsimp only [p]
          rw [dif_neg hj]
        rw [hpe]
        rcases Nat.eq_zero_or_pos K.card with hc | hc
        · have hK : K = ∅ := Finset.card_eq_zero.mp hc
          have hS : S = 0 := by
            show (∑ i ∈ K, a i) = 0
            rw [hK]
            simp
          rw [hS]
          simp
        · let m : Fin K.card := ⟨K.card - 1, by omega⟩
          have hmeq : (m : ℕ) + 1 = K.card := by dsimp only [m]; omega
          rw [← hmax m hmeq]
          exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨e m, hemem m, rfl⟩))
    · intro hy
      rcases Finset.mem_union.mp hy with h0 | hKi
      · have hy0 : y = 0 := by simpa using h0
        rw [hy0]
        exact Finset.mem_image.mpr ⟨0, Finset.mem_univ 0, hp0⟩
      · obtain ⟨x, hxK, hxHi⟩ := Finset.mem_image.mp hKi
        rw [← hxHi]
        obtain ⟨m, hm⟩ := hex x hxK
        rw [← hm]
        exact hmemHi m
  exact ⟨p, hmono, hpcast, hpsucc, himg, hp0, hplast⟩
  /- @proof-region region.target-node.session.fe9a031f46d197b9 end -/

end LiuBangXiangYu
