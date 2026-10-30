import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_1733068511_28bb1d76_7e68b264
open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_2999225285_90342243 : ∀ (n : ℕ) (hn : 1 ≤ n)
    (m : ℕ) (hm : 1 ≤ m)
    (p : Fin m → ℝ) (hp_pos : ∀ j, 0 < p j)
    (o : Fin m → Fin (n + 1))
      (hsum : ∀ i : Fin (n + 1),
        (∑ j ∈ Finset.univ.filter (fun j : Fin m => o j = i), p j) = (2 : ℝ) ^ (i : ℕ))
      (hm_le : m ≤ 2 * n + 1)
      (x : Fin m → ℝ)
      (hx_sorted : ∀ j k : Fin m, (j : ℕ) ≤ (k : ℕ) → x k ≤ x j)
      (hx_perm : ∃ σ : Equiv.Perm (Fin m), ∀ j, x j = p (σ j)),
      (∑ j ∈ Finset.range ((m + 1) / 2),
          ((if h : 2 * j < m then x ⟨2 * j, h⟩ else 0)
            - (if h : 2 * j + 1 < m then x ⟨2 * j + 1, h⟩ else 0))) ≥ 1 := by
  /- @proof-region region.target-node.session.9cf409370b290ddb begin -/
  intro n hn m hm p hp_pos o hsum hm_le x hx_sorted hx_perm
  classical
  obtain ⟨σ, hσ⟩ := hx_perm
  let oo : Fin m → Fin (n + 2) := fun j => ⟨(o j : ℕ), by have h := (o j).isLt; omega⟩
  let d : Fin (n + 2) := ⟨n + 1, by omega⟩
  let K : ℕ := m / 2 + 1
  let A : Fin K → Fin (n + 2) := fun e =>
    if h : 2 * (e : ℕ) + 1 < m then oo (σ ⟨2 * (e : ℕ) + 1, h⟩) else d
  let B : Fin K → Fin (n + 2) := fun e =>
    if h : 2 * (e : ℕ) < m then oo (σ ⟨2 * (e : ℕ), h⟩) else d
  let FL : Fin K → ℝ := fun e =>
    if h : 2 * (e : ℕ) + 1 < m then x ⟨2 * (e : ℕ) + 1, h⟩ else 0
  let FR : Fin K → ℝ := fun e =>
    if h : 2 * (e : ℕ) < m then x ⟨2 * (e : ℕ), h⟩ else 0
  let W : Fin (n + 2) → ℝ := fun u => if (u : ℕ) < n + 1 then (2 : ℝ) ^ (u : ℕ) else 0
  let lab : Fin (n + 2) → ℕ := fun u => (u : ℕ)
  have hreal : ∃ u : Fin (n + 2), W u ≠ 0 := by
    refine ⟨⟨0, by omega⟩, ?_⟩
    show (if (0 : ℕ) < n + 1 then (2 : ℝ) ^ (0 : ℕ) else 0) ≠ 0
    rw [if_pos (by omega)]
    norm_num
  have hpow : ∀ u : Fin (n + 2), W u ≠ 0 → W u = (2 : ℝ) ^ (lab u) := by
    intro u hu
    show (if (u : ℕ) < n + 1 then (2 : ℝ) ^ (u : ℕ) else 0) = (2 : ℝ) ^ (u : ℕ)
    by_cases h : (u : ℕ) < n + 1
    · exact if_pos h
    · have hWu : W u = 0 := if_neg h
      rw [hWu] at hu
      exact absurd rfl hu
  have hlab : ∀ u v : Fin (n + 2), W u ≠ 0 → W v ≠ 0 → lab u = lab v → u = v := by
    intro u v _ _ huv
    exact Fin.ext huv
  have hzero : (Finset.univ.filter (fun u : Fin (n + 2) => W u = 0)).card ≤ 1 := by
    have hsub : Finset.univ.filter (fun u : Fin (n + 2) => W u = 0) ⊆ {d} := by
      intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      simp only [Finset.mem_singleton]
      have hval : (u : ℕ) = n + 1 := by
        by_cases h : (u : ℕ) < n + 1
        · have hWu : W u = (2 : ℝ) ^ (u : ℕ) := if_pos h
          rw [hWu] at hu
          have hpos : (0 : ℝ) < (2 : ℝ) ^ (u : ℕ) := by positivity
          exact absurd hu hpos.ne'
        · have hlt := u.isLt
          omega
      exact Fin.ext hval
    calc (Finset.univ.filter (fun u : Fin (n + 2) => W u = 0)).card
        ≤ ({d} : Finset (Fin (n + 2))).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton d
  have hsize : K ≤ Fintype.card (Fin (n + 2)) - 1 := by
    show m / 2 + 1 ≤ Fintype.card (Fin (n + 2)) - 1
    rw [Fintype.card_fin]
    omega
  have hdeg : ∀ u : Fin (n + 2), ∃ e : Fin K, A e = u ∨ B e = u := by
    intro u
    by_cases hu : (u : ℕ) < n + 1
    · have hi : ∃ j : Fin m, oo j = u := by
        have hex : ∃ j : Fin m, o j = ⟨(u : ℕ), hu⟩ := by
          by_contra hc
          push_neg at hc
          have h0 : (∑ j ∈ Finset.univ.filter (fun j : Fin m => o j = ⟨(u : ℕ), hu⟩), p j) = 0 := by
            apply Finset.sum_eq_zero
            intro j hj
            rw [Finset.mem_filter] at hj
            exact absurd hj.2 (hc j)
          have h2 := hsum ⟨(u : ℕ), hu⟩
          rw [h0] at h2
          have hpos : (0 : ℝ) < (2 : ℝ) ^ (u : ℕ) := by positivity
          have h2' : (2 : ℝ) ^ (u : ℕ) = 0 := h2.symm
          exact absurd h2' hpos.ne'
        obtain ⟨j, hj⟩ := hex
        refine ⟨j, ?_⟩
        apply Fin.ext
        show (o j : ℕ) = (u : ℕ)
        rw [hj]
      obtain ⟨j, hj⟩ := hi
      let e : Fin K := ⟨(σ.symm j : ℕ) / 2, by
        have h := (σ.symm j).isLt
        show (σ.symm j : ℕ) / 2 < m / 2 + 1
        omega⟩
      refine ⟨e, ?_⟩
      by_cases hpar : 2 * ((σ.symm j : ℕ) / 2) = (σ.symm j : ℕ)
      · refine Or.inr ?_
        have hlt : 2 * (e : ℕ) < m := by
          have h := (σ.symm j).isLt
          show 2 * ((σ.symm j : ℕ) / 2) < m
          omega
        have hB : B e = oo (σ ⟨2 * (e : ℕ), hlt⟩) := dif_pos hlt
        rw [hB]
        have hsub : σ ⟨2 * (e : ℕ), hlt⟩ = j := by
          have hfin : (⟨2 * (e : ℕ), hlt⟩ : Fin m) = σ.symm j := by
            apply Fin.ext
            show 2 * ((σ.symm j : ℕ) / 2) = (σ.symm j : ℕ)
            exact hpar
          rw [hfin]
          exact Equiv.apply_symm_apply σ j
        rw [hsub]
        exact hj
      · refine Or.inl ?_
        have hodd : 2 * ((σ.symm j : ℕ) / 2) + 1 = (σ.symm j : ℕ) := by omega
        have hlt : 2 * (e : ℕ) + 1 < m := by
          have h := (σ.symm j).isLt
          show 2 * ((σ.symm j : ℕ) / 2) + 1 < m
          omega
        have hA : A e = oo (σ ⟨2 * (e : ℕ) + 1, hlt⟩) := dif_pos hlt
        rw [hA]
        have hsub : σ ⟨2 * (e : ℕ) + 1, hlt⟩ = j := by
          have hfin : (⟨2 * (e : ℕ) + 1, hlt⟩ : Fin m) = σ.symm j := by
            apply Fin.ext
            show 2 * ((σ.symm j : ℕ) / 2) + 1 = (σ.symm j : ℕ)
            exact hodd
          rw [hfin]
          exact Equiv.apply_symm_apply σ j
        rw [hsub]
        exact hj
    · let e : Fin K := ⟨m / 2, by show m / 2 < m / 2 + 1; omega⟩
      refine ⟨e, ?_⟩
      refine Or.inl ?_
      have hge : ¬ (2 * (m / 2) + 1 < m) := by omega
      have hA : A e = d := dif_neg hge
      rw [hA]
      apply Fin.ext
      show n + 1 = (u : ℕ)
      have h := u.isLt
      omega
  have hfrag : ∀ u : Fin (n + 2), (∑ e ∈ Finset.univ.filter (fun e : Fin K => A e = u), FL e)
      + (∑ e ∈ Finset.univ.filter (fun e : Fin K => B e = u), FR e) = W u := by
    intro u
    let Gm : Fin m → ℝ := fun j => if oo (σ j) = u then x j else 0
    let Fodd : Fin K → ℝ := fun e =>
      if h : 2 * (e : ℕ) + 1 < m then
        (if oo (σ ⟨2 * (e : ℕ) + 1, h⟩) = u then x ⟨2 * (e : ℕ) + 1, h⟩ else 0) else 0
    have hfilt : ∀ {α : Type} [Fintype α] (G : α → ℝ) (Pp : α → Prop) [DecidablePred Pp],
        (∑ e ∈ Finset.univ.filter Pp, G e) = ∑ e : α, (if Pp e then G e else 0) := by
      intro α _ G Pp _
      have h1 : (∑ e ∈ Finset.univ.filter Pp, G e)
          = ∑ e ∈ Finset.univ.filter Pp, (if Pp e then G e else 0) := by
        apply Finset.sum_congr rfl
        intro e he
        exact (if_pos (Finset.mem_filter.mp he).2).symm
      rw [h1]
      refine Finset.sum_subset (fun e _ => Finset.mem_univ e) (fun e _ he => ?_)
      have hne : ¬ Pp e := fun hP => he (Finset.mem_filter.mpr ⟨Finset.mem_univ e, hP⟩)
      rw [if_neg hne]
    have hperm : (∑ j : Fin m, (if oo (σ j) = u then x j else 0))
        = ∑ k : Fin m, (if oo k = u then p k else 0) := by
      exact Finset.sum_bij (fun j (_ : j ∈ Finset.univ) => σ j) (fun j _ => Finset.mem_univ _)
        (fun a _ b _ hh => Equiv.injective σ hh)
        (fun b _ => ⟨σ.symm b, Finset.mem_univ _, by simp⟩)
        (fun j _ => by rw [hσ j])
    have hodd : (∑ e ∈ Finset.univ.filter (fun e : Fin K => A e = u), FL e)
        = ∑ j ∈ Finset.univ.filter (fun j : Fin m => 2 * ((j : ℕ) / 2) + 1 = (j : ℕ)), Gm j := by
      have hA1 : (∑ e ∈ Finset.univ.filter (fun e : Fin K => A e = u), FL e)
          = ∑ e : Fin K, Fodd e := by
        rw [hfilt FL (fun e : Fin K => A e = u)]
        apply Finset.sum_congr rfl
        intro e _
        by_cases h : 2 * (e : ℕ) + 1 < m
        · have hAe : A e = oo (σ ⟨2 * (e : ℕ) + 1, h⟩) := dif_pos h
          have hFLe : FL e = x ⟨2 * (e : ℕ) + 1, h⟩ := dif_pos h
          have hFe : Fodd e
              = (if oo (σ ⟨2 * (e : ℕ) + 1, h⟩) = u then x ⟨2 * (e : ℕ) + 1, h⟩ else 0) :=
            dif_pos h
          rw [hAe, hFLe, hFe]
        · have hAe : A e = d := dif_neg h
          have hFLe : FL e = 0 := dif_neg h
          have hFe : Fodd e = 0 := dif_neg h
          rw [hAe, hFLe, hFe]
          by_cases hdu : d = u <;> simp [hdu]
      have hA2 : (∑ e : Fin K, Fodd e)
          = ∑ j ∈ Finset.univ.filter (fun j : Fin m => 2 * ((j : ℕ) / 2) + 1 = (j : ℕ)), Gm j := by
        have hind : (∑ e : Fin K, Fodd e)
            = ∑ e : Fin K, (if 2 * (e : ℕ) + 1 < m then Fodd e else 0) := by
          apply Finset.sum_congr rfl
          intro e _
          by_cases h : 2 * (e : ℕ) + 1 < m
          · rw [if_pos h]
          · have he : Fodd e = 0 := dif_neg h
            rw [he, if_neg h]
        rw [hind, ← hfilt Fodd (fun e : Fin K => 2 * (e : ℕ) + 1 < m)]
        exact Finset.sum_bij
          (fun e he => (⟨2 * (e : ℕ) + 1, (Finset.mem_filter.mp he).2⟩ : Fin m))
          (fun e _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
            show 2 * ((2 * (e : ℕ) + 1) / 2) + 1 = 2 * (e : ℕ) + 1
            omega⟩)
          (fun e₁ _ e₂ _ hh => by
            have h1 : 2 * (e₁ : ℕ) + 1 = 2 * (e₂ : ℕ) + 1 := by
              have h2 := congrArg (fun w : Fin m => (w : ℕ)) hh
              simpa using h2
            apply Fin.ext
            omega)
          (fun j hj => ⟨⟨(j : ℕ) / 2, by
              have hlt := j.isLt
              show (j : ℕ) / 2 < m / 2 + 1
              omega⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
              show 2 * ((j : ℕ) / 2) + 1 < m
              have h := (Finset.mem_filter.mp hj).2
              have hlt := j.isLt
              omega⟩,
            by
              have h := (Finset.mem_filter.mp hj).2
              apply Fin.ext
              simp [h]⟩)
          (fun e he => by
            have hb : 2 * (e : ℕ) + 1 < m := (Finset.mem_filter.mp he).2
            have hFe : Fodd e
                = (if oo (σ (⟨2 * (e : ℕ) + 1, hb⟩ : Fin m)) = u then
                    x (⟨2 * (e : ℕ) + 1, hb⟩ : Fin m) else 0) := dif_pos hb
            exact hFe)
      exact hA1.trans hA2
    have heven : (∑ e ∈ Finset.univ.filter (fun e : Fin K => B e = u), FR e)
        = ∑ j ∈ Finset.univ.filter (fun j : Fin m => 2 * ((j : ℕ) / 2) = (j : ℕ)), Gm j := by
      let Feven : Fin K → ℝ := fun e =>
        if h : 2 * (e : ℕ) < m then
          (if oo (σ ⟨2 * (e : ℕ), h⟩) = u then x ⟨2 * (e : ℕ), h⟩ else 0) else 0
      have he1 : (∑ e ∈ Finset.univ.filter (fun e : Fin K => B e = u), FR e)
          = ∑ e : Fin K, Feven e := by
        rw [hfilt FR (fun e : Fin K => B e = u)]
        apply Finset.sum_congr rfl
        intro e _
        by_cases h : 2 * (e : ℕ) < m
        · have hBe : B e = oo (σ ⟨2 * (e : ℕ), h⟩) := dif_pos h
          have hFRe : FR e = x ⟨2 * (e : ℕ), h⟩ := dif_pos h
          have hFe : Feven e
              = (if oo (σ ⟨2 * (e : ℕ), h⟩) = u then x ⟨2 * (e : ℕ), h⟩ else 0) := dif_pos h
          rw [hBe, hFRe, hFe]
        · have hBe : B e = d := dif_neg h
          have hFRe : FR e = 0 := dif_neg h
          have hFe : Feven e = 0 := dif_neg h
          rw [hBe, hFRe, hFe]
          by_cases hdu : d = u <;> simp [hdu]
      have he2 : (∑ e : Fin K, Feven e)
          = ∑ j ∈ Finset.univ.filter (fun j : Fin m => 2 * ((j : ℕ) / 2) = (j : ℕ)), Gm j := by
        have hind : (∑ e : Fin K, Feven e)
            = ∑ e : Fin K, (if 2 * (e : ℕ) < m then Feven e else 0) := by
          apply Finset.sum_congr rfl
          intro e _
          by_cases h : 2 * (e : ℕ) < m
          · rw [if_pos h]
          · have he : Feven e = 0 := dif_neg h
            rw [he, if_neg h]
        rw [hind, ← hfilt Feven (fun e : Fin K => 2 * (e : ℕ) < m)]
        exact Finset.sum_bij
          (fun e he => (⟨2 * (e : ℕ), (Finset.mem_filter.mp he).2⟩ : Fin m))
          (fun e _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
            show 2 * ((2 * (e : ℕ)) / 2) = 2 * (e : ℕ)
            omega⟩)
          (fun e₁ _ e₂ _ hh => by
            have h1 : 2 * (e₁ : ℕ) = 2 * (e₂ : ℕ) := by
              have h2 := congrArg (fun w : Fin m => (w : ℕ)) hh
              simpa using h2
            apply Fin.ext
            omega)
          (fun j hj => ⟨⟨(j : ℕ) / 2, by
              have hlt := j.isLt
              show (j : ℕ) / 2 < m / 2 + 1
              omega⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
              show 2 * ((j : ℕ) / 2) < m
              have h := (Finset.mem_filter.mp hj).2
              have hlt := j.isLt
              omega⟩,
            by
              have h := (Finset.mem_filter.mp hj).2
              apply Fin.ext
              simp [h]⟩)
          (fun e he => by
            have hb : 2 * (e : ℕ) < m := (Finset.mem_filter.mp he).2
            have hFe : Feven e
                = (if oo (σ (⟨2 * (e : ℕ), hb⟩ : Fin m)) = u then
                    x (⟨2 * (e : ℕ), hb⟩ : Fin m) else 0) := dif_pos hb
            exact hFe)
      exact he1.trans he2
    have hsplit : (∑ j ∈ Finset.univ.filter (fun j : Fin m => 2 * ((j : ℕ) / 2) + 1 = (j : ℕ)), Gm j)
        + (∑ j ∈ Finset.univ.filter (fun j : Fin m => 2 * ((j : ℕ) / 2) = (j : ℕ)), Gm j)
        = ∑ j : Fin m, Gm j := by
      rw [hfilt Gm (fun j : Fin m => 2 * ((j : ℕ) / 2) + 1 = (j : ℕ)),
        hfilt Gm (fun j : Fin m => 2 * ((j : ℕ) / 2) = (j : ℕ)),
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h1 : 2 * ((j : ℕ) / 2) + 1 = (j : ℕ)
      · by_cases h2 : 2 * ((j : ℕ) / 2) = (j : ℕ)
        · exact absurd (h1.trans h2.symm) (by omega)
        · rw [if_pos h1, if_neg h2]
          ring
      · by_cases h2 : 2 * ((j : ℕ) / 2) = (j : ℕ)
        · rw [if_neg h1, if_pos h2]
          ring
        · exfalso
          omega
    have hval : (∑ k : Fin m, (if oo k = u then p k else 0)) = W u := by
      by_cases hu : (u : ℕ) < n + 1
      · have hWu : W u = (2 : ℝ) ^ (u : ℕ) := if_pos hu
        rw [hWu, ← hfilt (fun k : Fin m => p k) (fun k : Fin m => oo k = u)]
        have hset : Finset.univ.filter (fun k : Fin m => oo k = u)
            = Finset.univ.filter (fun k : Fin m => o k = ⟨(u : ℕ), hu⟩) := by
          apply Finset.ext
          intro k
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro hk
            exact Fin.ext (by
              have h2 := congrArg (fun v : Fin (n + 2) => (v : ℕ)) hk
              simpa using h2)
          · intro hk
            apply Fin.ext
            show (o k : ℕ) = (u : ℕ)
            rw [hk]
        rw [hset]
        exact hsum ⟨(u : ℕ), hu⟩
      · have hWu : W u = 0 := if_neg hu
        rw [hWu]
        apply Finset.sum_eq_zero
        intro k _
        have hne : ¬ (oo k = u) := by
          intro hk
          have h1 : (oo k : ℕ) = (u : ℕ) := by
            have h2 := congrArg (fun v : Fin (n + 2) => (v : ℕ)) hk
            simpa using h2
          have h5 : (oo k : ℕ) = (o k : ℕ) := rfl
          have h3 : (u : ℕ) = n + 1 := by
            have h := u.isLt
            omega
          have h4 : (o k : ℕ) < n + 1 := (o k).isLt
          omega
        rw [if_neg hne]
    rw [hodd, heven]
    exact hsplit.trans (hperm.trans hval)
  have hbound : (∑ e : Fin K, |FL e - FR e|) ≤
      (∑ j ∈ Finset.range ((m + 1) / 2),
        ((if h : 2 * j < m then x ⟨2 * j, h⟩ else 0)
          - (if h : 2 * j + 1 < m then x ⟨2 * j + 1, h⟩ else 0))) := by
    let T : ℕ → ℝ := fun j =>
      (if h : 2 * j < m then x ⟨2 * j, h⟩ else 0)
        - (if h : 2 * j + 1 < m then x ⟨2 * j + 1, h⟩ else 0)
    show (∑ e : Fin K, |FL e - FR e|) ≤ ∑ j ∈ Finset.range ((m + 1) / 2), T j
    have hmono : ∀ a b : ℕ, a ≤ b → ∀ (ha : a < m) (hb : b < m), x ⟨b, hb⟩ ≤ x ⟨a, ha⟩ := by
      intro a b hab ha hb
      exact hx_sorted ⟨a, ha⟩ ⟨b, hb⟩ hab
    have hT : ∀ e : Fin K, |FL e - FR e| = T (e : ℕ) := by
      intro e
      have hle : FL e - FR e ≤ 0 := by
        by_cases h2 : 2 * (e : ℕ) < m
        · by_cases h1 : 2 * (e : ℕ) + 1 < m
          · have hFL : FL e = x ⟨2 * (e : ℕ) + 1, h1⟩ := dif_pos h1
            have hFR : FR e = x ⟨2 * (e : ℕ), h2⟩ := dif_pos h2
            rw [hFL, hFR]
            have hs := hmono (2 * (e : ℕ)) (2 * (e : ℕ) + 1) (by omega) h2 h1
            linarith
          · have hFL : FL e = 0 := dif_neg h1
            have hFR : FR e = x ⟨2 * (e : ℕ), h2⟩ := dif_pos h2
            rw [hFL, hFR]
            have hpos : 0 < x ⟨2 * (e : ℕ), h2⟩ := by
              rw [hσ]
              exact hp_pos _
            linarith
        · have hFL : FL e = 0 := dif_neg (by omega)
          have hFR : FR e = 0 := dif_neg h2
          rw [hFL, hFR]
          simp
      rw [abs_of_nonpos hle, show -((FL e) - (FR e)) = FR e - FL e by ring]
    have key : (∑ e : Fin K, |FL e - FR e|) = ∑ j ∈ Finset.range ((m + 1) / 2), T j := by
      calc (∑ e : Fin K, |FL e - FR e|)
          = ∑ e : Fin K, T (e : ℕ) := Finset.sum_congr rfl (fun e _ => hT e)
        _ = ∑ j ∈ Finset.range K, T j := Fin.sum_univ_eq_sum_range T K
        _ = ∑ j ∈ Finset.range ((m + 1) / 2), T j := by
            refine (Finset.sum_subset ?_ ?_).symm
            · intro y hy
              simp only [Finset.mem_range] at hy ⊢
              show y < m / 2 + 1
              omega
            · intro y _ hynot
              simp only [Finset.mem_range] at hynot
              dsimp only [T]
              rw [dif_neg (show ¬ (2 * y < m) by omega),
                dif_neg (show ¬ (2 * y + 1 < m) by omega)]
              ring
    exact le_of_eq key
  exact statopia_math_node_1733068511_28bb1d76 (Fin (n + 2)) K A B FL FR W lab _
    hreal hfrag hpow hlab hdeg hzero hsize hbound
  /- @proof-region region.target-node.session.9cf409370b290ddb end -/

end LiuBangXiangYu
