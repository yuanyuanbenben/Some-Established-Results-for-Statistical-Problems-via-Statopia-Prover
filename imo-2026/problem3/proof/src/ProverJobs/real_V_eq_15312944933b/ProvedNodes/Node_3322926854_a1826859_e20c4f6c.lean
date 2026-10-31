import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base

open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_3322926854_a1826859 : ∀ (q : ℕ) (hq : 1 ≤ q) (b : ℕ → ℝ)
    (hb0 : b 0 = 0) (hbq : b q = 1)
    (hbmono : StrictMonoOn b (Set.Icc 0 q))
    (I J : Finset (Fin q)) (hIJ : Disjoint I J) (hne : I ∪ J ≠ ∅) (C : Finset ℝ)
    (hC1 : ∀ c ∈ C, 0 < c ∧ c < 1)
    (hC2 : ∀ c ∈ C, ∀ k : Fin (q + 1), c ≠ b (k : ℕ))
    (hC3 : ∀ c ∈ C, ∃ k ∈ I ∪ J, b (k : ℕ) < c ∧ c < b ((k : ℕ) + 1))
    (hC4 : C.card ≤ I.card + J.card - 1),
    let A : Finset ℝ := (Finset.univ.filter (fun k : Fin q => 1 ≤ (k : ℕ))).image (fun k : Fin q => b (k : ℕ))
    let M : Finset ℝ := (Finset.univ.filter (fun k : Fin q => k ∉ I ∪ J)).image (fun k : Fin q => (b (k : ℕ) + b ((k : ℕ) + 1)) / 2)
    AdmissibleMark A.card (C ∪ M) ∧ Disjoint A (C ∪ M) := by
  /- @proof-region region.target-node.session.c35b23a63853f56c begin -/
  intro q hq b hb0 hbq hbmono I J hIJ hne C hC1 hC2 hC3 hC4
  dsimp only
  set A : Finset ℝ := (Finset.univ.filter (fun k : Fin q => 1 ≤ (k : ℕ))).image (fun k : Fin q => b (k : ℕ)) with hAdef
  set M : Finset ℝ := (Finset.univ.filter (fun k : Fin q => k ∉ I ∪ J)).image (fun k : Fin q => (b (k : ℕ) + b ((k : ℕ) + 1)) / 2) with hMdef
  have hb_mono_le : ∀ {i j : ℕ}, i ≤ j → j ≤ q → b i ≤ b j := by
    intro i j hij hj
    exact hbmono.monotoneOn ⟨Nat.zero_le i, le_trans hij hj⟩ ⟨Nat.zero_le j, hj⟩ hij
  have hb_mono_lt : ∀ {i j : ℕ}, i < j → j ≤ q → b i < b j := by
    intro i j hij hj
    exact hbmono ⟨Nat.zero_le i, le_trans (le_of_lt hij) hj⟩ ⟨Nat.zero_le j, hj⟩ hij
  have hb_lo : ∀ k : Fin q, 0 ≤ b (k : ℕ) := by
    intro k
    have h := hb_mono_le (Nat.zero_le (k : ℕ)) (le_of_lt k.isLt)
    rwa [hb0] at h
  have hb_hi : ∀ k : Fin q, b ((k : ℕ) + 1) ≤ 1 := by
    intro k
    have h := hb_mono_le (Nat.succ_le_of_lt k.isLt) (le_refl q)
    rwa [hbq] at h
  have hb_st : ∀ k : Fin q, b (k : ℕ) < b ((k : ℕ) + 1) := by
    intro k
    exact hb_mono_lt (Nat.lt_succ_self _) (Nat.succ_le_of_lt k.isLt)
  have hb_mid_lo : ∀ k : Fin q, b (k : ℕ) < (b (k : ℕ) + b ((k : ℕ) + 1)) / 2 :=
    fun k => by linarith [hb_st k]
  have hb_mid_hi : ∀ k : Fin q, (b (k : ℕ) + b ((k : ℕ) + 1)) / 2 < b ((k : ℕ) + 1) :=
    fun k => by linarith [hb_st k]
  have hb_inj : Function.Injective (fun k : Fin q => b (k : ℕ)) := by
    intro i j hij
    have hij' : b (i : ℕ) = b (j : ℕ) := hij
    rcases lt_trichotomy (i : ℕ) (j : ℕ) with hlt | heq | hlt
    · exfalso
      have h := hb_mono_lt hlt (le_of_lt j.isLt)
      rw [hij'] at h
      exact lt_irrefl _ h
    · exact Fin.ext heq
    · exfalso
      have h := hb_mono_lt hlt (le_of_lt i.isLt)
      rw [hij'] at h
      exact lt_irrefl _ h
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro x hx
    rw [Finset.mem_coe] at hx
    rw [Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact hC1 x hx
    · rw [hMdef] at hx
      rw [Finset.mem_image] at hx
      obtain ⟨k, _, rfl⟩ := hx
      exact ⟨lt_of_le_of_lt (hb_lo k) (hb_mid_lo k), lt_of_lt_of_le (hb_mid_hi k) (hb_hi k)⟩
  · have hIUs : (I ∪ J).card = I.card + J.card := Finset.card_union_of_disjoint hIJ
    have hle : I.card + J.card ≤ q := by
      rw [← hIUs]
      calc (I ∪ J).card ≤ Fintype.card (Fin q) := Finset.card_le_univ (I ∪ J)
        _ = q := Fintype.card_fin q
    have hge : 1 ≤ I.card + J.card := by
      rw [← hIUs]
      exact Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
    have hAcard : A.card = q - 1 := by
      rw [hAdef]
      rw [Finset.card_image_of_injective _ hb_inj]
      have hq_pos : 0 < q := hq
      have hsing : (Finset.univ.filter (fun k : Fin q => ¬ (1 ≤ (k : ℕ)))) = {⟨0, hq_pos⟩} := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro h
          apply Fin.ext
          show (k : ℕ) = 0
          omega
        · intro h
          rw [h]
          simp
      have hh := Finset.filter_card_add_filter_neg_card_eq_card (s := (Finset.univ : Finset (Fin q))) (p := fun k : Fin q => 1 ≤ (k : ℕ))
      rw [Finset.card_univ, Fintype.card_fin, hsing, Finset.card_singleton] at hh
      omega
    have hMcard : M.card ≤ q - (I ∪ J).card := by
      rw [hMdef]
      calc ((Finset.univ.filter (fun k : Fin q => k ∉ I ∪ J)).image (fun k : Fin q => (b (k : ℕ) + b ((k : ℕ) + 1)) / 2)).card
          ≤ (Finset.univ.filter (fun k : Fin q => k ∉ I ∪ J)).card := Finset.card_image_le
        _ = q - (I ∪ J).card := by
            have hh := Finset.filter_card_add_filter_neg_card_eq_card (s := (Finset.univ : Finset (Fin q))) (p := fun k : Fin q => k ∉ I ∪ J)
            rw [Finset.card_univ, Fintype.card_fin] at hh
            have h2 : (Finset.univ.filter (fun k : Fin q => ¬ (k ∉ I ∪ J))) = I ∪ J := by
              ext k
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              constructor
              · intro h
                by_contra hc
                exact h hc
              · intro h hc
                exact hc h
            rw [h2] at hh
            omega
    have h1 : (C ∪ M).card ≤ C.card + M.card := Finset.card_union_le C M
    have h2 : C.card + M.card ≤ (I.card + J.card - 1) + (q - (I ∪ J).card) := by omega
    have h3 : (I.card + J.card - 1) + (q - (I ∪ J).card) = q - 1 := by
      rw [hIUs]
      omega
    calc (C ∪ M).card ≤ C.card + M.card := h1
      _ ≤ (I.card + J.card - 1) + (q - (I ∪ J).card) := h2
      _ = q - 1 := h3
      _ = A.card := hAcard.symm
  · rw [Finset.disjoint_left]
    intro x hx
    rw [hAdef] at hx
    rw [Finset.mem_image] at hx
    obtain ⟨k, _, rfl⟩ := hx
    rw [Finset.mem_union]
    rw [not_or]
    constructor
    · intro hc
      exact hC2 (b (k : ℕ)) hc ⟨(k : ℕ), Nat.lt_succ_of_lt k.isLt⟩ rfl
    · intro hm
      rw [hMdef] at hm
      rw [Finset.mem_image] at hm
      obtain ⟨j, _, hjx⟩ := hm
      rcases lt_trichotomy (j : ℕ) (k : ℕ) with hlt | heq | hgt
      · have h1 : (b (j : ℕ) + b ((j : ℕ) + 1)) / 2 < b ((j : ℕ) + 1) := hb_mid_hi j
        have h2 : b ((j : ℕ) + 1) ≤ b (k : ℕ) := hb_mono_le (Nat.succ_le_of_lt hlt) (le_of_lt k.isLt)
        have h3 : (b (j : ℕ) + b ((j : ℕ) + 1)) / 2 < b (k : ℕ) := lt_of_lt_of_le h1 h2
        rw [hjx] at h3
        exact lt_irrefl _ h3
      · have hjk : j = k := Fin.ext heq
        rw [hjk] at hjx
        have h := hb_mid_lo k
        rw [hjx] at h
        exact lt_irrefl _ h
      · have h1 : b (k : ℕ) < b ((k : ℕ) + 1) := hb_st k
        have h2 : b ((k : ℕ) + 1) ≤ b (j : ℕ) := hb_mono_le (Nat.succ_le_of_lt hgt) (le_of_lt j.isLt)
        have h3 : b (j : ℕ) ≤ (b (j : ℕ) + b ((j : ℕ) + 1)) / 2 := le_of_lt (hb_mid_lo j)
        have h4 : b (k : ℕ) < (b (j : ℕ) + b ((j : ℕ) + 1)) / 2 := lt_of_lt_of_le h1 (le_trans h2 h3)
        rw [hjx] at h4
        exact lt_irrefl _ h4
  /- @proof-region region.target-node.session.c35b23a63853f56c end -/

end LiuBangXiangYu
