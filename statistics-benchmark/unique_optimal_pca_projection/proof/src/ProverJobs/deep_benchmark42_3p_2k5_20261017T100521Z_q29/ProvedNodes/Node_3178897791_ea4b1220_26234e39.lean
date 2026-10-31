import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q29.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q29.Base

open Matrix

open Matrix

set_option autoImplicit false in
theorem statopia_math_node_3178897791_ea4b1220 : ∀ (d r : ℕ) (hr0 : 1 ≤ r) (hrd : r < d)
    (v : Fin d → Fin d → ℝ)
    (lambda : Fin d → ℝ)
    (horth : ∀ j k, dotProduct (v j) (v k) = if j = k then 1 else 0)
    (S : Matrix (Fin d) (Fin d) ℝ)
    (hS : ∀ j, S *ᵥ v j = lambda j • v j),
    let P : Matrix (Fin d) (Fin d) ℝ := ∑ j with j.val < r, vecMulVec (v j) (v j)
    P.transpose = P ∧ P * P = P ∧ P.trace = (r : ℝ) ∧
      (∀ j : Fin d, j.val < r → P *ᵥ v j = v j) ∧
      (∀ j : Fin d, r ≤ j.val → P *ᵥ v j = 0) ∧
      (P * S).trace = ∑ j with j.val < r, lambda j := by
  /- @proof-region region.target-node.session.4b84fff1f3de1a5d begin -/
  intro d r hr0 hrd v lambda horth S hS
  dsimp only
  set A : Finset (Fin d) := Finset.univ.filter (fun j : Fin d => j.val < r) with hAdef
  have hAmem : ∀ j : Fin d, j ∈ A ↔ j.val < r := by
    intro j
    simp [hAdef]
  have hvecapp : ∀ (a b : Fin d → ℝ) (i t : Fin d), vecMulVec a b i t = a i * b t :=
    fun a b i t => rfl
  have hmulapp : ∀ (M N : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d),
      (M * N) i j = ∑ t, M i t * N t j := fun M N i j => rfl
  have hmvapp : ∀ (M : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) (i : Fin d),
      (M *ᵥ x) i = ∑ t, M i t * x t := fun M x i => rfl
  have htrapp : ∀ M : Matrix (Fin d) (Fin d) ℝ, M.trace = ∑ i, M i i := fun M => rfl
  have htrTapp : ∀ (M : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d), Mᵀ i j = M j i :=
    fun M i j => rfl
  have hdotapp : ∀ a b : Fin d → ℝ, a ⬝ᵥ b = ∑ t, a t * b t := fun a b => rfl
  have hsumapp : ∀ (F : Finset (Fin d)) (M : Fin d → Matrix (Fin d) (Fin d) ℝ) (i j : Fin d),
      (∑ k ∈ F, M k) i j = ∑ k ∈ F, M k i j := by
    intro F
    induction F using Finset.induction with
    | empty =>
        intro M i j
        simp
    | insert a s ha ih =>
        intro M i j
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        simp [ih]
  have hdot : ∀ k l : Fin d, (∑ t : Fin d, v k t * v l t) = if k = l then (1 : ℝ) else 0 := by
    intro k l
    exact (hdotapp (v k) (v l)).symm.trans (horth k l)
  have htrace_sum : ∀ (F : Finset (Fin d)) (M : Fin d → Matrix (Fin d) (Fin d) ℝ),
      (∑ k ∈ F, M k).trace = ∑ k ∈ F, (M k).trace := by
    intro F M
    have h1 : (∑ k ∈ F, M k).trace = ∑ i, ∑ k ∈ F, M k i i := by
      rw [htrapp]
      exact Finset.sum_congr rfl (fun i _ => hsumapp F M i i)
    have h2 : (∑ k ∈ F, (M k).trace) = ∑ k ∈ F, ∑ i, M k i i :=
      Finset.sum_congr rfl (fun k _ => htrapp (M k))
    rw [h1, h2]
    exact Finset.sum_comm
  have hboole' : ∀ (f : Fin d → ℝ) (j : Fin d),
      (∑ k ∈ A, f k * (if k = j then (1 : ℝ) else 0)) = if j ∈ A then f j else 0 := by
    intro f j
    rw [← Finset.sum_mul_boole A f j]
    exact Finset.sum_congr rfl (fun k _ => by
      by_cases hk : k = j
      · rw [if_pos hk, if_pos hk.symm]
      · rw [if_neg hk, if_neg (Ne.symm hk)])
  have hcard : A.card = r := by
    have h := Finset.card_bij (s := A) (t := Finset.range r)
      (fun (j : Fin d) (_ : j ∈ A) => j.val)
      (fun (j : Fin d) (hj : j ∈ A) => Finset.mem_range.2 ((hAmem j).1 hj))
      (fun (j₁ : Fin d) (_ : j₁ ∈ A) (j₂ : Fin d) (_ : j₂ ∈ A) (he : j₁.val = j₂.val) =>
        Fin.ext he)
      (fun (b : ℕ) (hb : b ∈ Finset.range r) =>
        ⟨⟨b, lt_trans (Finset.mem_range.1 hb) hrd⟩, (hAmem _).2 (Finset.mem_range.1 hb), rfl⟩)
    rw [Finset.card_range] at h
    exact h
  have htrans : (∑ j ∈ A, vecMulVec (v j) (v j))ᵀ = ∑ j ∈ A, vecMulVec (v j) (v j) := by
    ext a b
    rw [htrTapp, hsumapp, hsumapp]
    exact Finset.sum_congr rfl (fun k _ => by rw [hvecapp, hvecapp, mul_comm])
  have hmul : (∑ k ∈ A, vecMulVec (v k) (v k)) * (∑ l ∈ A, vecMulVec (v l) (v l))
      = ∑ k ∈ A, vecMulVec (v k) (v k) := by
    ext a b
    rw [hmulapp]
    have h1 : ∀ t : Fin d, (∑ k ∈ A, vecMulVec (v k) (v k)) a t
          * (∑ l ∈ A, vecMulVec (v l) (v l)) t b
        = ∑ k ∈ A, ∑ l ∈ A, (v k a * v k t) * (v l t * v l b) := by
      intro t
      rw [hsumapp, hsumapp, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl (fun k _ =>
        Finset.sum_congr rfl (fun l _ => by rw [hvecapp, hvecapp]))
    rw [Finset.sum_congr rfl (fun t _ => h1 t), Finset.sum_comm, hsumapp]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [Finset.sum_comm, hvecapp]
    have h2 : ∀ l ∈ A, (∑ t : Fin d, (v k a * v k t) * (v l t * v l b))
        = (v k a * v l b) * (if k = l then (1 : ℝ) else 0) := by
      intro l _
      have h3 : (∑ t : Fin d, (v k a * v k t) * (v l t * v l b))
          = (v k a * v l b) * (∑ t : Fin d, v k t * v l t) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun t _ => by ring)
      rw [h3, hdot k l]
    rw [Finset.sum_congr rfl h2, Finset.sum_mul_boole A (fun x => v k a * v x b) k]
    simp [if_pos hk]
  have htrace_one : ∀ k ∈ A, (vecMulVec (v k) (v k)).trace = (1 : ℝ) := by
    intro k _
    have h1 : (vecMulVec (v k) (v k)).trace = v k ⬝ᵥ v k := by
      rw [htrapp, hdotapp]
      exact Finset.sum_congr rfl (fun i _ => rfl)
    rw [h1, horth k k, if_pos rfl]
  have htraceP : (∑ k ∈ A, vecMulVec (v k) (v k)).trace = (r : ℝ) := by
    rw [htrace_sum]
    rw [show (∑ k ∈ A, (vecMulVec (v k) (v k)).trace) = ∑ k ∈ A, (1 : ℝ) from
      Finset.sum_congr rfl htrace_one]
    rw [Finset.sum_const, hcard, nsmul_eq_mul, mul_one]
  have hPmulVec : ∀ (x : Fin d → ℝ) (i : Fin d),
      ((∑ k ∈ A, vecMulVec (v k) (v k)) *ᵥ x) i = ∑ k ∈ A, v k i * (v k ⬝ᵥ x) := by
    intro x i
    rw [hmvapp]
    have h1 : ∀ t : Fin d, (∑ k ∈ A, vecMulVec (v k) (v k)) i t * x t
        = ∑ k ∈ A, (v k i * v k t) * x t := by
      intro t
      rw [hsumapp, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun k _ => by rw [hvecapp])
    rw [Finset.sum_congr rfl (fun t _ => h1 t), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have h2 : (∑ t : Fin d, (v k i * v k t) * x t) = v k i * (∑ t : Fin d, v k t * x t) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun t _ => by ring)
    rw [h2, ← hdotapp (v k) x]
  have hmulVec_lt : ∀ j : Fin d, j.val < r →
      (∑ k ∈ A, vecMulVec (v k) (v k)) *ᵥ v j = v j := by
    intro j hj
    funext i
    rw [hPmulVec]
    have h1 : ∀ k ∈ A, v k i * (v k ⬝ᵥ v j) = v k i * (if k = j then (1 : ℝ) else 0) := by
      intro k _
      rw [horth k j]
    rw [Finset.sum_congr rfl h1, hboole' (fun k => v k i) j, if_pos ((hAmem j).2 hj)]
  have hmulVec_ge : ∀ j : Fin d, r ≤ j.val →
      (∑ k ∈ A, vecMulVec (v k) (v k)) *ᵥ v j = 0 := by
    intro j hj
    funext i
    rw [hPmulVec]
    have h1 : ∀ k ∈ A, v k i * (v k ⬝ᵥ v j) = v k i * (if k = j then (1 : ℝ) else 0) := by
      intro k _
      rw [horth k j]
    have hnot : ¬ j ∈ A := fun h => Nat.not_lt.mpr hj ((hAmem j).1 h)
    rw [Finset.sum_congr rfl h1, hboole' (fun k => v k i) j, if_neg hnot]
    simp
  have hsum_mul_S : (∑ j ∈ A, vecMulVec (v j) (v j)) * S
      = ∑ j ∈ A, vecMulVec (v j) (v j) * S := by
    ext a b
    rw [hmulapp]
    have h1 : ∀ t : Fin d, (∑ j ∈ A, vecMulVec (v j) (v j)) a t * S t b
        = ∑ j ∈ A, (v j a * v j t) * S t b := by
      intro t
      rw [hsumapp, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun j _ => by rw [hvecapp])
    rw [Finset.sum_congr rfl (fun t _ => h1 t), Finset.sum_comm, hsumapp]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hmulapp]
    exact Finset.sum_congr rfl (fun t _ => by rw [hvecapp])
  have htrace_vmS : ∀ a b : Fin d → ℝ, (vecMulVec a b * S).trace = b ⬝ᵥ (S *ᵥ a) := by
    intro a b
    rw [htrapp]
    have h1 : ∀ i : Fin d, (vecMulVec a b * S) i i = ∑ t, (a i * b t) * S t i := by
      intro i
      rw [hmulapp]
      exact Finset.sum_congr rfl (fun t _ => by rw [hvecapp])
    rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_comm, hdotapp]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [hmvapp, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hstep : ∀ j ∈ A, (vecMulVec (v j) (v j) * S).trace = lambda j := by
    intro j _
    rw [htrace_vmS, hS j, dotProduct_smul, smul_eq_mul, horth j j, if_pos rfl, mul_one]
  have htrace_PS : ((∑ j ∈ A, vecMulVec (v j) (v j)) * S).trace = ∑ j ∈ A, lambda j := by
    rw [hsum_mul_S, htrace_sum]
    exact Finset.sum_congr rfl hstep
  exact ⟨htrans, hmul, htraceP, hmulVec_lt, hmulVec_ge, htrace_PS⟩
  /- @proof-region region.target-node.session.4b84fff1f3de1a5d end -/
