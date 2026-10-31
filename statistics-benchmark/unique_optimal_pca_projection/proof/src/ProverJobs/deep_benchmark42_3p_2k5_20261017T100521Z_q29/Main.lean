import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q29.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q29.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q29.Base

open Matrix

theorem unique_optimal_pca_projection
    (n d r : ℕ) (hn : 1 ≤ n) (hd : 2 ≤ d)
    (hr₀ : 1 ≤ r) (hrd : r < d)
    (x : Fin n → Fin d → ℝ)
    (hcenter : ∑ i, x i = 0)
    (v : Fin d → Fin d → ℝ)
    (lambda : Fin d → ℝ)
    (horth : ∀ j k, dotProduct (v j) (v k) = if j = k then 1 else 0)
    (hspan : Submodule.span ℝ (Set.range v) = ⊤) :
    let S : Matrix (Fin d) (Fin d) ℝ :=
      (n : ℝ)⁻¹ • ∑ i, vecMulVec (x i) (x i)
    let Pᵣ : Matrix (Fin d) (Fin d) ℝ :=
      ∑ j with j.val < r, vecMulVec (v j) (v j)
    (∀ j, S *ᵥ v j = lambda j • v j) →
    Antitone lambda →
    (∀ i j, i.val < r → r ≤ j.val → lambda i > lambda j) →
      let projections : Set (Matrix (Fin d) (Fin d) ℝ) :=
        {P | P.transpose = P ∧ P * P = P ∧ P.trace = (r : ℝ)}
      let objective : Matrix (Fin d) (Fin d) ℝ → ℝ := fun P ↦
        (n : ℝ)⁻¹ *
          ∑ i, dotProduct (x i - P *ᵥ x i) (x i - P *ᵥ x i)
      {P | P ∈ projections ∧
        ∀ Q ∈ projections, objective P ≤ objective Q} = {Pᵣ}
:= by
  /- @proof-region region.root.7467cf85669b begin -/
  intro S Pr hS hmono hsep
  have hPrdef : Pr = ∑ j with j.val < r, vecMulVec (v j) (v j) := rfl
  have hcard : (Finset.univ.filter (fun j : Fin d => j.val < r)).card = r := by
    have hfil : Finset.univ.filter (fun j : Fin d => j.val < r) = Finset.Iio ⟨r, hrd⟩ := by
      ext j
      simp [Fin.lt_def]
    rw [hfil, Fin.card_Iio]
  have hvmv : ∀ (a b u : Fin d → ℝ), vecMulVec a b *ᵥ u = (b ⬝ᵥ u) • a := by
    intro a b u
    ext i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Matrix.vecMulVec,
      Matrix.of_apply]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have hvmvm : ∀ (a b c e : Fin d → ℝ),
      vecMulVec a b * vecMulVec c e = (b ⬝ᵥ c) • vecMulVec a e := by
    intro a b c e
    ext i l
    simp only [Matrix.mul_apply, Matrix.vecMulVec, Matrix.of_apply, dotProduct, Matrix.smul_apply,
      smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have hsum_mulVec : ∀ (s : Finset (Fin d)) (A : Fin d → Matrix (Fin d) (Fin d) ℝ) (u : Fin d → ℝ),
      (∑ k ∈ s, A k) *ᵥ u = ∑ k ∈ s, A k *ᵥ u := by
    intro s A u
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, Finset.sum_mul, Finset.sum_apply]
    rw [Finset.sum_comm]
  have hPr_symm : Prᵀ = Pr := by
    rw [hPrdef]
    ext i l
    simp only [Matrix.transpose_apply, Matrix.sum_apply]
    exact Finset.sum_congr rfl (fun j _ => by simp [Matrix.vecMulVec, mul_comm])
  have hPr_idem : Pr * Pr = Pr := by
    rw [hPrdef, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    refine (Finset.sum_eq_single j ?_ ?_).trans ?_
    · intro k _ hkj
      rw [hvmvm, horth j k, if_neg (fun h : j = k => hkj h.symm), zero_smul]
    · intro h
      exact absurd (by simpa using hj) h
    · rw [hvmvm, horth j j, if_pos rfl, one_smul]
  have hPr_trace : Pr.trace = (r : ℝ) := by
    rw [hPrdef, Matrix.trace_sum]
    have h1 : ∀ j ∈ Finset.univ.filter (fun j : Fin d => j.val < r),
        (vecMulVec (v j) (v j)).trace = (1 : ℝ) := by
      intro j _
      rw [Matrix.trace_vecMulVec, horth j j, if_pos rfl]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, hcard, nsmul_eq_mul, mul_one]
  have hPr_mulVec : ∀ u : Fin d → ℝ,
      Pr *ᵥ u = ∑ k with k.val < r, (v k ⬝ᵥ u) • v k := by
    intro u
    rw [hPrdef, hsum_mulVec]
    exact Finset.sum_congr rfl (fun k _ => hvmv (v k) (v k) u)
  have hPr_v : ∀ j : Fin d, Pr *ᵥ v j = if j.val < r then v j else 0 := by
    intro j
    by_cases hj : j.val < r
    · have hPrj : Pr *ᵥ v j = v j := by
        rw [hPr_mulVec (v j)]
        refine (Finset.sum_eq_single j ?_ ?_).trans ?_
        · intro k _ hkj
          rw [horth k j, if_neg hkj, zero_smul]
        · intro h
          exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩) h
        · rw [horth j j, if_pos rfl, one_smul]
      rw [hPrj, if_pos hj]
    · have hPrj : Pr *ᵥ v j = 0 := by
        rw [hPr_mulVec (v j)]
        refine Finset.sum_eq_zero (fun k hk => ?_)
        obtain ⟨-, hk⟩ := Finset.mem_filter.mp hk
        have hkj : k ≠ j := by
          intro h
          rw [h] at hk
          exact hj hk
        rw [horth k j, if_neg hkj, zero_smul]
      rw [hPrj, if_neg hj]
  have hPr_w : ∀ j : Fin d, v j ⬝ᵥ (Pr *ᵥ v j) = if j.val < r then 1 else 0 := by
    intro j
    by_cases hj : j.val < r
    · have h1 : Pr *ᵥ v j = v j := by rw [hPr_v j, if_pos hj]
      rw [h1, horth j j, if_pos rfl, if_pos hj]
    · have h0 : Pr *ᵥ v j = 0 := by rw [hPr_v j, if_neg hj]
      rw [h0, if_neg hj]
      simp [dotProduct]
  have hPrS : (Pr * S).trace = ∑ j with j.val < r, lambda j := by
    obtain ⟨-, -, -, h4⟩ :=
      statopia_math_node_3038386786_a9667efa d v lambda S r Pr horth hspan hS hPr_symm hPr_idem hPr_trace
    rw [h4, Finset.sum_filter]
    exact Finset.sum_congr rfl (fun j _ => by
      by_cases hj : j.val < r <;> simp [hj, hPr_w j])
  have hobj : ∀ (P : Matrix (Fin d) (Fin d) ℝ), Pᵀ = P → P * P = P →
      (n : ℝ)⁻¹ * ∑ i, (x i - P *ᵥ x i) ⬝ᵥ (x i - P *ᵥ x i) = S.trace - (P * S).trace := by
    intro P h1 h2
    exact statopia_math_node_405419422_e48aae78 n d x P h1 h2
  have hPrmem : Prᵀ = Pr ∧ Pr * Pr = Pr ∧ Pr.trace = (r : ℝ) := ⟨hPr_symm, hPr_idem, hPr_trace⟩
  ext P
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hPmem, hmin⟩
    obtain ⟨hP1, hP2, hP3⟩ := hPmem
    set w : Fin d → ℝ := fun j => v j ⬝ᵥ (P *ᵥ v j) with hw
    set T : ℝ := ∑ j with j.val < r, lambda j with hT
    obtain ⟨hw_nn, hw_le, hw_sum, hw_tr⟩ :=
      statopia_math_node_3038386786_a9667efa d v lambda S r P horth hspan hS hP1 hP2 hP3
    have hb := statopia_math_node_3808411263_c3a7b8bc d r hr₀ hrd lambda w hmono hsep hw_nn hw_le hw_sum
    have hb1 : ∑ j, lambda j * w j ≤ T := hb.1
    have hPle : (n : ℝ)⁻¹ * ∑ i, (x i - P *ᵥ x i) ⬝ᵥ (x i - P *ᵥ x i) ≤
        (n : ℝ)⁻¹ * ∑ i, (x i - Pr *ᵥ x i) ⬝ᵥ (x i - Pr *ᵥ x i) := hmin Pr hPrmem
    rw [hobj P hP1 hP2, hobj Pr hPr_symm hPr_idem, hPrS, hT] at hPle
    have hge : T ≤ (P * S).trace := by linarith
    have hle : (P * S).trace ≤ T := by
      rw [hw_tr]
      exact hb1
    have heq : (P * S).trace = T := le_antisymm hle hge
    have hw_tr' : (P * S).trace = ∑ j, lambda j * w j := hw_tr
    have hpat := hb.2 (by rw [← hw_tr', heq, hT])
    exact statopia_math_node_4070169760_207a1beb d r hr₀ hrd v horth hspan S lambda hS P hP1 hP2
      hpat.1 hpat.2
  · rintro rfl
    refine ⟨hPrmem, ?_⟩
    intro Q hQ
    obtain ⟨hQ1, hQ2, hQ3⟩ := hQ
    obtain ⟨hQ_nn, hQ_le, hQ_sum, hQ_tr⟩ :=
      statopia_math_node_3038386786_a9667efa d v lambda S r Q horth hspan hS hQ1 hQ2 hQ3
    have hb := statopia_math_node_3808411263_c3a7b8bc d r hr₀ hrd lambda
      (fun j => v j ⬝ᵥ (Q *ᵥ v j)) hmono hsep hQ_nn hQ_le hQ_sum
    rw [hobj Pr hPr_symm hPr_idem, hobj Q hQ1 hQ2, hPrS]
    linarith [hb.1, hQ_tr]
  /- @proof-region region.root.7467cf85669b end -/
