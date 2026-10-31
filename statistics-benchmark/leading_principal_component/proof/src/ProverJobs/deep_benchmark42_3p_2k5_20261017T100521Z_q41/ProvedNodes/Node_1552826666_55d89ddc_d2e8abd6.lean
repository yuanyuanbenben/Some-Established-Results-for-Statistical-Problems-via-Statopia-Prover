import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q41.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q41.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q41.ProvedNodes.Node_2870924675_739d774f_df01e636
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q41.ProvedNodes.Node_3287348555_0ab2c998_b668baa5
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q41.ProvedNodes.Node_3782112706_5d79a883_ea50a37e



open Matrix

open Matrix

set_option autoImplicit false in
theorem statopia_math_node_1552826666_55d89ddc : ∀ (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (x : Fin n → Fin d → ℝ)
    (v : Fin d → Fin d → ℝ)
    (lambda : Fin d → ℝ)
    (first : Fin d) (hfirst : (first : ℕ) = 0)
    (horth : ∀ j k : Fin d, dotProduct (v j) (v k) = if j = k then (1 : ℝ) else 0)
    (hspan : Submodule.span ℝ (Set.range v) = ⊤)
    (S : Matrix (Fin d) (Fin d) ℝ)
    (hS : S = (n : ℝ)⁻¹ • ∑ i, vecMulVec (x i) (x i))
    (heig : ∀ j : Fin d, S *ᵥ v j = lambda j • v j)
    (hne : ∀ j : Fin d, j ≠ first → lambda first > lambda j)
    (u : Fin d → ℝ),
    let objective : (Fin d → ℝ) → ℝ :=
      fun z => (n : ℝ)⁻¹ * (∑ i : Fin n, (dotProduct z (x i)) ^ 2)
    (dotProduct u u = 1 ∧
        ∀ w : Fin d → ℝ, dotProduct w w = 1 → objective w ≤ objective u) ↔
      (u = v first ∨ u = (-(v first))) := by
  /- @proof-region region.target-node.session.1ccb0b679dcd6dd3 begin -/
  intro n d hn hd x v lambda first hfirst horth hspan S hS heig hne u
  dsimp only
  constructor
  · rintro ⟨hu1, humax⟩
    have hvv : dotProduct (v first) (v first) = 1 := by
      rw [horth first first, if_pos rfl]
    have hdiag_v := statopia_math_node_3287348555_0ab2c998 n d hn hd x v lambda first hfirst horth hspan S hS heig (v first)
    have hsingle : (∑ j : Fin d, lambda j * (dotProduct (v first) (v j)) ^ 2)
        = lambda first * (dotProduct (v first) (v first)) ^ 2 :=
      Finset.sum_eq_single first
        (fun j _ hj => by rw [horth first j, if_neg (Ne.symm hj)]; ring)
        (fun hmem => absurd (Finset.mem_univ first) hmem)
    have hA_vfirst : (n : ℝ)⁻¹ * (∑ i : Fin n, (dotProduct (v first) (x i)) ^ 2) = lambda first := by
      rw [hdiag_v.1, hsingle, hvv]
      ring
    have hmax : (n : ℝ)⁻¹ * (∑ i : Fin n, (dotProduct (v first) (x i)) ^ 2)
        ≤ (n : ℝ)⁻¹ * (∑ i : Fin n, (dotProduct u (x i)) ^ 2) := humax (v first) hvv
    have hupper := statopia_math_node_3782112706_5d79a883 n d hn hd x v lambda first hfirst horth hspan S hS heig hne u
    have hle2 : (n : ℝ)⁻¹ * (∑ i : Fin n, (dotProduct u (x i)) ^ 2) ≤ lambda first := by
      have hle := hupper.1
      rw [hu1, mul_one] at hle
      exact hle
    have hle1 : lambda first ≤ (n : ℝ)⁻¹ * (∑ i : Fin n, (dotProduct u (x i)) ^ 2) := by
      rw [← hA_vfirst]; exact hmax
    have hA_u : (n : ℝ)⁻¹ * (∑ i : Fin n, (dotProduct u (x i)) ^ 2) = lambda first :=
      le_antisymm hle2 hle1
    have heq : (n : ℝ)⁻¹ * (∑ i : Fin n, (dotProduct u (x i)) ^ 2) = lambda first * dotProduct u u := by
      rw [hA_u, hu1, mul_one]
    have hcoeff : ∀ j : Fin d, j ≠ first → dotProduct u (v j) = 0 := hupper.2.mp heq
    have h_expand : u = ∑ j : Fin d, (dotProduct u (v j)) • v j :=
      (statopia_math_node_2870924675_739d774f d hd v horth hspan).1 u
    have hcollapse : (∑ j : Fin d, (dotProduct u (v j)) • v j) = (dotProduct u (v first)) • v first :=
      Finset.sum_eq_single first
        (fun j _ hj => by rw [hcoeff j hj]; simp)
        (fun hmem => absurd (Finset.mem_univ first) hmem)
    have hu_eq : u = (dotProduct u (v first)) • v first := h_expand.trans hcollapse
    have hnorm : dotProduct u u = (dotProduct u (v first)) ^ 2 := by
      nth_rewrite 2 [hu_eq]
      rw [dotProduct_smul, smul_eq_mul]
      ring
    have hc_sq : (dotProduct u (v first)) ^ 2 = 1 := by
      rw [← hnorm]; exact hu1
    have hc : dotProduct u (v first) = 1 ∨ dotProduct u (v first) = -1 := by
      have h1 : (dotProduct u (v first) - 1) * (dotProduct u (v first) + 1) = 0 := by nlinarith [hc_sq]
      rcases mul_eq_zero.mp h1 with hh | hh
      · left; linarith
      · right; linarith
    rcases hc with hc1 | hcneg
    · left
      rw [hu_eq, hc1, one_smul]
    · right
      rw [hu_eq, hcneg]
      funext i
      simp
  · intro h
    have hvv : dotProduct (v first) (v first) = 1 := by
      rw [horth first first, if_pos rfl]
    have hdiag_v := statopia_math_node_3287348555_0ab2c998 n d hn hd x v lambda first hfirst horth hspan S hS heig (v first)
    have hsingle : (∑ j : Fin d, lambda j * (dotProduct (v first) (v j)) ^ 2)
        = lambda first * (dotProduct (v first) (v first)) ^ 2 :=
      Finset.sum_eq_single first
        (fun j _ hj => by rw [horth first j, if_neg (Ne.symm hj)]; ring)
        (fun hmem => absurd (Finset.mem_univ first) hmem)
    have hA_vfirst : (n : ℝ)⁻¹ * (∑ i : Fin n, (dotProduct (v first) (x i)) ^ 2) = lambda first := by
      rw [hdiag_v.1, hsingle, hvv]
      ring
    rcases h with hu | hu
    · rw [hu]
      refine ⟨hvv, ?_⟩
      intro w hw
      rw [hA_vfirst]
      have hb := (statopia_math_node_3782112706_5d79a883 n d hn hd x v lambda first hfirst horth hspan S hS heig hne w).1
      rw [hw, mul_one] at hb
      exact hb
    · rw [hu]
      have hneg_one : -(v first) = (-1 : ℝ) • v first := by
        funext i
        simp
      rw [hneg_one]
      have hdiag_neg := statopia_math_node_3287348555_0ab2c998 n d hn hd x v lambda first hfirst horth hspan S hS heig ((-1 : ℝ) • v first)
      have hterm : ∀ j : Fin d, (dotProduct ((-1 : ℝ) • v first) (v j)) ^ 2 = (dotProduct (v first) (v j)) ^ 2 := by
        intro j
        have hdj : dotProduct ((-1 : ℝ) • v first) (v j) = -(dotProduct (v first) (v j)) := by
          rw [dotProduct_comm ((-1 : ℝ) • v first) (v j), dotProduct_smul, dotProduct_comm (v j) (v first), smul_eq_mul]
          ring
        rw [hdj]; ring
      have hA_neg : (n : ℝ)⁻¹ * (∑ i : Fin n, (dotProduct ((-1 : ℝ) • v first) (x i)) ^ 2) = lambda first := by
        rw [hdiag_neg.1]
        have hsum_eq : (∑ j : Fin d, lambda j * (dotProduct ((-1 : ℝ) • v first) (v j)) ^ 2)
            = (∑ j : Fin d, lambda j * (dotProduct (v first) (v j)) ^ 2) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [hterm j]
        rw [hsum_eq, hsingle, hvv]
        ring
      refine ⟨?_, ?_⟩
      · rw [dotProduct_smul, dotProduct_comm ((-1 : ℝ) • v first) (v first), dotProduct_smul, hvv, smul_eq_mul]
        norm_num
      · intro w hw
        rw [hA_neg]
        have hb := (statopia_math_node_3782112706_5d79a883 n d hn hd x v lambda first hfirst horth hspan S hS heig hne w).1
        rw [hw, mul_one] at hb
        exact hb
  /- @proof-region region.target-node.session.1ccb0b679dcd6dd3 end -/
