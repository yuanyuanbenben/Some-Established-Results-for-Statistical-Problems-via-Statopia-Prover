import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q28.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q28.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q28.Base

open Matrix

theorem axial_extrinsic_mean_leading_eigenvector
    (d n : ℕ) (hd : 2 ≤ d) (hn : 1 ≤ n)
    (x : Fin n → Fin d → ℝ)
    (hx : ∀ i, dotProduct (x i) (x i) = 1)
    (v : Fin d → ℝ) (hv : dotProduct v v = 1)
    (lambda : ℝ) :
    let A : Matrix (Fin d) (Fin d) ℝ :=
      (n : ℝ)⁻¹ • ∑ i, vecMulVec (x i) (x i)
    A *ᵥ v = lambda • v →
    (∀ u, dotProduct u u = 1 →
      dotProduct u (A *ᵥ u) ≤ lambda) →
    (∀ u, A *ᵥ u = lambda • u →
      ∃ c : ℝ, u = c • v) →
      let objective : (Fin d → ℝ) → ℝ := fun u ↦
        (n : ℝ)⁻¹ *
          ∑ i, ∑ j, ∑ k,
            (u j * u k - x i j * x i k) ^ 2
      {u : Fin d → ℝ |
        dotProduct u u = 1 ∧
          ∀ w, dotProduct w w = 1 → objective u ≤ objective w} =
        {v, -v}
:= by
  /- @proof-region region.root.8a7eb6fabaf2 begin -/
  dsimp only
  intro hAv hRay hUniq
  set A : Matrix (Fin d) (Fin d) ℝ := (n : ℝ)⁻¹ • ∑ i, vecMulVec (x i) (x i) with hA
  let O : (Fin d → ℝ) → ℝ :=
    fun u => (n : ℝ)⁻¹ * ∑ i, ∑ j, ∑ k, (u j * u k - x i j * x i k) ^ 2
  change {u : Fin d → ℝ | dotProduct u u = 1 ∧
    ∀ w, dotProduct w w = 1 → O u ≤ O w} = {v, -v}
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hAjk : ∀ j k : Fin d, A j k = (n : ℝ)⁻¹ * ∑ i, x i j * x i k := by
    intro j k
    rw [hA]
    simp [Matrix.smul_apply, Matrix.sum_apply, Matrix.vecMulVec]
  have hAsym : ∀ j k : Fin d, A j k = A k j := by
    intro j k
    simp only [hAjk]
    exact congrArg (fun s => (n : ℝ)⁻¹ * s)
      (Finset.sum_congr rfl (fun i _ => mul_comm (x i j) (x i k)))
  have hquad : ∀ u : Fin d → ℝ,
      dotProduct u (A *ᵥ u) = (n : ℝ)⁻¹ * ∑ i, (dotProduct u (x i)) ^ 2 := by
    intro u
    have e1 : dotProduct u (A *ᵥ u) = ∑ j, ∑ k, u j * u k * A j k := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro k _
      ring
    have e2a : (∑ j, ∑ k, u j * u k * A j k)
        = (n : ℝ)⁻¹ * ∑ j, ∑ k, ∑ i, (u j * x i j) * (u k * x i k) := by
      simp only [hAjk, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro k _
      apply Finset.sum_congr rfl; intro i _
      ring
    have e2b : (∑ j, ∑ k, ∑ i, (u j * x i j) * (u k * x i k))
        = ∑ i, (∑ j, u j * x i j) * (∑ k, u k * x i k) := by
      have hii : ∀ i : Fin n, (∑ j, u j * x i j) * (∑ k, u k * x i k)
          = ∑ j, ∑ k, (u j * x i j) * (u k * x i k) := by
        intro i
        exact Fintype.sum_mul_sum (fun j => u j * x i j) (fun k => u k * x i k)
      have hsum : (∑ i, (∑ j, u j * x i j) * (∑ k, u k * x i k))
          = ∑ i, ∑ j, ∑ k, (u j * x i j) * (u k * x i k) :=
        Finset.sum_congr rfl (fun i _ => hii i)
      have h1 : (∑ i, ∑ j, ∑ k, (u j * x i j) * (u k * x i k))
          = ∑ j, ∑ i, ∑ k, (u j * x i j) * (u k * x i k) := Finset.sum_comm
      have h2 : (∑ j, ∑ i, ∑ k, (u j * x i j) * (u k * x i k))
          = ∑ j, ∑ k, ∑ i, (u j * x i j) * (u k * x i k) := by
        apply Finset.sum_congr rfl; intro j _; exact Finset.sum_comm
      exact (h1.trans h2).symm.trans hsum.symm
    have e3 : ∀ i : Fin n,
        (∑ j, u j * x i j) * (∑ k, u k * x i k) = (dotProduct u (x i)) ^ 2 := by
      intro i
      simp [dotProduct, pow_two]
    rw [e1, e2a, e2b]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => e3 i)
  have hinner_gen : ∀ a b : Fin d → ℝ,
      (∑ j, ∑ k, (a j * a k - b j * b k) ^ 2)
        = (dotProduct a a) ^ 2 + (dotProduct b b) ^ 2 - 2 * (dotProduct a b) ^ 2 := by
    intro a b
    have h1 : ∀ j k : Fin d, (a j * a k - b j * b k) ^ 2
        = (a j * a j) * (a k * a k) + (b j * b j) * (b k * b k)
          - 2 * ((a j * b j) * (a k * b k)) := by
      intro j k; ring
    have ea : (∑ j, ∑ k, (a j * a j) * (a k * a k)) = (dotProduct a a) ^ 2 := by
      rw [← Fintype.sum_mul_sum]
      simp [dotProduct, pow_two]
    have eb : (∑ j, ∑ k, (b j * b j) * (b k * b k)) = (dotProduct b b) ^ 2 := by
      rw [← Fintype.sum_mul_sum]
      simp [dotProduct, pow_two]
    have eab : (∑ j, ∑ k, (a j * b j) * (a k * b k)) = (dotProduct a b) ^ 2 := by
      rw [← Fintype.sum_mul_sum]
      simp [dotProduct, pow_two]
    have hmain : (∑ j, ∑ k, (a j * a k - b j * b k) ^ 2)
        = (∑ j, ∑ k, ((a j * a j) * (a k * a k) + (b j * b j) * (b k * b k)
            - 2 * ((a j * b j) * (a k * b k)))) :=
      Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => h1 j k))
    have e2 : (∑ j, ∑ k, ((a j * a j) * (a k * a k) + (b j * b j) * (b k * b k)
          - 2 * ((a j * b j) * (a k * b k))))
        = (∑ j, ∑ k, (a j * a j) * (a k * a k)) + (∑ j, ∑ k, (b j * b j) * (b k * b k))
          - 2 * (∑ j, ∑ k, (a j * b j) * (a k * b k)) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    rw [hmain, e2, ea, eb, eab]
  have hO_unit : ∀ u : Fin d → ℝ, dotProduct u u = 1 →
      O u = 2 * (1 - dotProduct u (A *ᵥ u)) := by
    intro u hu
    change (n : ℝ)⁻¹ * ∑ i, ∑ j, ∑ k, (u j * u k - x i j * x i k) ^ 2
      = 2 * (1 - dotProduct u (A *ᵥ u))
    have hinner : ∀ i : Fin n, (∑ j, ∑ k, (u j * u k - x i j * x i k) ^ 2)
        = 2 * (1 - (dotProduct u (x i)) ^ 2) := by
      intro i
      rw [hinner_gen u (x i), hu, hx i]
      ring
    have hSum : (∑ i : Fin n, (∑ j, ∑ k, (u j * u k - x i j * x i k) ^ 2))
        = 2 * ((n : ℝ) - ∑ i : Fin n, (dotProduct u (x i)) ^ 2) := by
      rw [Finset.sum_congr rfl (fun i _ => hinner i)]
      rw [← Finset.mul_sum, Finset.sum_sub_distrib]
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hSum, hquad u]
    have hkey : (n : ℝ)⁻¹ * ((n : ℝ) - ∑ i : Fin n, (dotProduct u (x i)) ^ 2)
        = 1 - (n : ℝ)⁻¹ * ∑ i : Fin n, (dotProduct u (x i)) ^ 2 := by
      rw [mul_sub, inv_mul_cancel₀ hn0]
    rw [← hkey]
    ring
  have hdot_self_nonneg : ∀ y : Fin d → ℝ, 0 ≤ dotProduct y y := by
    intro y
    have h : dotProduct y y = ∑ j, y j * y j := by simp [dotProduct]
    rw [h]
    exact Finset.sum_nonneg (fun j _ => mul_self_nonneg (y j))
  have hdot_smul : ∀ (t : ℝ) (y z : Fin d → ℝ),
      dotProduct (t • y) z = t * dotProduct y z := by
    intro t y z
    rw [dotProduct_comm (t • y) z, dotProduct_smul, dotProduct_comm z y, smul_eq_mul]
  have hnorm_hom : ∀ (t : ℝ) (y : Fin d → ℝ),
      dotProduct (t • y) (t • y) = t ^ 2 * dotProduct y y := by
    intro t y
    rw [hdot_smul t y (t • y), dotProduct_smul, smul_eq_mul]
    ring
  have hq_hom : ∀ (t : ℝ) (y : Fin d → ℝ),
      dotProduct (t • y) (A *ᵥ (t • y)) = t ^ 2 * dotProduct y (A *ᵥ y) := by
    intro t y
    rw [Matrix.mulVec_smul, hdot_smul t y (t • (A *ᵥ y)), dotProduct_smul, smul_eq_mul]
    ring
  have hglobal : ∀ y : Fin d → ℝ,
      dotProduct y (A *ᵥ y) ≤ lambda * dotProduct y y := by
    intro y
    by_cases hy : y = 0
    · rw [hy]
      simp [dotProduct]
    · have hyy : 0 < dotProduct y y := by
        refine lt_of_le_of_ne (hdot_self_nonneg y) ?_
        intro h
        exact hy (dotProduct_self_eq_zero.mp h.symm)
      set s : ℝ := Real.sqrt (dotProduct y y) with hs
      have hs2 : s ^ 2 = dotProduct y y := by
        rw [hs]; exact Real.sq_sqrt (le_of_lt hyy)
      have hsne : s ≠ 0 := by
        intro h
        have h1 : s ^ 2 = 0 := by rw [h]; ring
        rw [hs2] at h1
        linarith
      set z : Fin d → ℝ := s⁻¹ • y with hz
      have hzz : dotProduct z z = 1 := by
        rw [hz, hnorm_hom, inv_pow, hs2, inv_mul_cancel₀ (ne_of_gt hyy)]
      have hqle : dotProduct z (A *ᵥ z) ≤ lambda := hRay z hzz
      have hys : y = s • z := by
        rw [hz, smul_smul, mul_inv_cancel₀ hsne, one_smul]
      have hyform : dotProduct y (A *ᵥ y) = (dotProduct y y) * dotProduct z (A *ᵥ z) := by
        conv_lhs => rw [hys]
        rw [hq_hom, hs2]
      rw [hyform]
      calc (dotProduct y y) * dotProduct z (A *ᵥ z)
          ≤ (dotProduct y y) * lambda := mul_le_mul_of_nonneg_left hqle (le_of_lt hyy)
        _ = lambda * dotProduct y y := by ring
  have hdep2 := statopia_math_node_1531792026_97dcbda1 d n hn x hx v hv lambda hAv hRay
  dsimp only at hdep2
  obtain ⟨hvq, hlb, hnegv, hOv, hOnegv, hminv, hminneg⟩ := hdep2
  have hOvO : O v = 2 * (1 - lambda) := hOv
  have hminvO : ∀ w : Fin d → ℝ, dotProduct w w = 1 → O v ≤ O w := hminv
  have hminnegO : ∀ w : Fin d → ℝ, dotProduct w w = 1 → O (-v) ≤ O w := hminneg
  ext u
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hu, hmin⟩
    have hle : O u ≤ O v := hmin v hv
    have h1 : 2 * (1 - dotProduct u (A *ᵥ u)) ≤ 2 * (1 - lambda) := by
      calc 2 * (1 - dotProduct u (A *ᵥ u)) = O u := (hO_unit u hu).symm
        _ ≤ O v := hle
        _ = 2 * (1 - lambda) := hOvO
    have hge : lambda ≤ dotProduct u (A *ᵥ u) := by linarith
    have hqu : dotProduct u (A *ᵥ u) = lambda := le_antisymm (hRay u hu) hge
    have hAu : A *ᵥ u = lambda • u :=
      statopia_math_node_3205143652_e97c7860 d A hAsym lambda hglobal u hu hqu
    obtain ⟨c, hc⟩ := hUniq u hAu
    have hc2 : c ^ 2 = 1 := by
      have h : dotProduct u u = dotProduct (c • v) (c • v) := by rw [hc]
      rw [hu, hnorm_hom, hv] at h
      linarith
    have h2 : (c - 1) * (c + 1) = 0 := by nlinarith [hc2]
    rcases mul_eq_zero.mp h2 with h | h
    · left
      rw [hc, show c = 1 by linarith, one_smul]
    · right
      rw [hc, show c = -1 by linarith, neg_one_smul]
  · rintro (rfl | rfl)
    · exact ⟨hv, hminvO⟩
    · exact ⟨hnegv, hminnegO⟩
  /- @proof-region region.root.8a7eb6fabaf2 end -/
