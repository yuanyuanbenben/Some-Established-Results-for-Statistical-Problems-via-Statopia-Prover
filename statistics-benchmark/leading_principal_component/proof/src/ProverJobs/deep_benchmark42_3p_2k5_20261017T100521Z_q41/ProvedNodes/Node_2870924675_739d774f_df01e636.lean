import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q41.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q41.Base

open Matrix

open Matrix

set_option autoImplicit false in
theorem statopia_math_node_2870924675_739d774f : ∀ (d : ℕ) (hd : 1 ≤ d)
    (v : Fin d → Fin d → ℝ)
    (horth : ∀ j k : Fin d, dotProduct (v j) (v k) = if j = k then (1 : ℝ) else 0)
    (hspan : Submodule.span ℝ (Set.range v) = ⊤),
    (∀ u : Fin d → ℝ, u = ∑ j : Fin d, (dotProduct u (v j)) • v j) ∧
      (∀ (u : Fin d → ℝ) (b : Fin d → ℝ),
        u = ∑ j : Fin d, b j • v j → b = fun j : Fin d => dotProduct u (v j)) := by
  /- @proof-region region.target-node.session.2c812eccec575e40 begin -/
  intro d hd v horth hspan
  have hkey : ∀ (c : Fin d → ℝ) (k : Fin d),
      dotProduct (∑ j, c j • v j) (v k) = c k := by
    intro c k
    have hlin : dotProduct (∑ j, c j • v j) (v k)
        = ∑ j : Fin d, c j * dotProduct (v j) (v k) := by
      simp only [dotProduct]
      simp [Finset.sum_mul, Finset.mul_sum]
      conv_lhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
      ring
    rw [hlin]
    have h1 : ∑ j : Fin d, c j * dotProduct (v j) (v k)
        = ∑ j : Fin d, c j * (if j = k then (1 : ℝ) else 0) :=
      Finset.sum_congr rfl (fun j _ => by rw [horth j k])
    rw [h1]
    have h2 : ∑ j : Fin d, c j * (if j = k then (1 : ℝ) else 0) = c k := by
      have hs := Finset.sum_eq_single (s := Finset.univ)
        (f := fun j : Fin d => c j * (if j = k then (1 : ℝ) else 0)) k
        (fun j _ hjk => by simp [hjk])
        (fun hk => absurd (Finset.mem_univ k) hk)
      rw [hs]
      simp
    exact h2
  constructor
  · intro u
    set S : Fin d → ℝ := ∑ j : Fin d, (dotProduct u (v j)) • v j with hS
    have hkeyS : ∀ k : Fin d, dotProduct S (v k) = dotProduct u (v k) := by
      intro k
      rw [hS]
      exact hkey (fun j : Fin d => dotProduct u (v j)) k
    have hsub : ∀ k : Fin d, dotProduct (u - S) (v k) = 0 := by
      intro k
      have hsplit : dotProduct (u - S) (v k)
          = dotProduct u (v k) - dotProduct S (v k) := by
        simp [dotProduct, sub_mul, Finset.sum_sub_distrib]
      rw [hsplit, hkeyS k]
      simp
    have hz : ∀ z : Fin d → ℝ, dotProduct (u - S) z = 0 := by
      have hle : Submodule.span ℝ (Set.range v) ≤
          ({ carrier := {z : Fin d → ℝ | dotProduct (u - S) z = 0},
             zero_mem' := by simp [dotProduct],
             add_mem' := by
               intro x y hx hy
               simp only [Set.mem_setOf_eq] at hx hy ⊢
               rw [dotProduct_add, hx, hy, add_zero]
             smul_mem' := by
               intro c x hx
               simp only [Set.mem_setOf_eq] at hx ⊢
               rw [dotProduct_smul, hx, smul_zero] } : Submodule ℝ (Fin d → ℝ)) := by
        rw [Submodule.span_le]
        rintro z ⟨j, rfl⟩
        exact hsub j
      intro z
      have hzspan : z ∈ Submodule.span ℝ (Set.range v) := by
        rw [hspan]
        exact Submodule.mem_top
      simpa using hle hzspan
    have hww : dotProduct (u - S) (u - S) = 0 := hz (u - S)
    have hzero : u - S = 0 := by
      funext k
      have hsq : ∑ i : Fin d, (u - S) i * (u - S) i = 0 := by
        simpa [dotProduct] using hww
      have := (Finset.sum_mul_self_eq_zero_iff Finset.univ
        (fun i : Fin d => (u - S) i)).mp hsq k (Finset.mem_univ k)
      simpa using this
    exact sub_eq_zero.mp hzero
  · intro u b hb
    funext k
    calc b k = dotProduct (∑ j : Fin d, b j • v j) (v k) := (hkey b k).symm
      _ = dotProduct u (v k) := by rw [hb]
  /- @proof-region region.target-node.session.2c812eccec575e40 end -/
