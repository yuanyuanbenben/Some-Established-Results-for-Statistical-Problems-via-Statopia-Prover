import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q40.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q40.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q40.ProvedNodes.Node_2474807198_d38bf418_b2bd71be
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q40.ProvedNodes.Node_3652586393_a25bccab_59257ec6
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q40.ProvedNodes.Node_3852170914_d7d89bd9_21230dd8



open Matrix

open Matrix

set_option autoImplicit false in
theorem statopia_math_node_646129307_86263361 : ∀ (d n : ℕ) (hn : 1 ≤ n)
    (x : Fin n → Fin d → ℝ)
    (hx : ∀ i : Fin n, dotProduct (x i) (x i) = 1)
    (ha : (n : ℝ)⁻¹ • (∑ i : Fin n, x i) ≠ 0)
    (p : Fin d → ℝ)
    (hp : dotProduct p p = 1)
    (hmin : ∀ q : Fin d → ℝ, dotProduct q q = 1 →
      (n : ℝ)⁻¹ * (∑ i : Fin n, dotProduct (x i - p) (x i - p)) ≤
        (n : ℝ)⁻¹ * (∑ i : Fin n, dotProduct (x i - q) (x i - q))),
    p = (Real.sqrt
          (dotProduct ((n : ℝ)⁻¹ • (∑ i : Fin n, x i))
            ((n : ℝ)⁻¹ • (∑ i : Fin n, x i))))⁻¹ •
        ((n : ℝ)⁻¹ • (∑ i : Fin n, x i)) := by
  /- @proof-region region.target-node.session.8951035c90e31888 begin -/
  intro d n hn x hx ha p hp hmin
  set a : Fin d → ℝ := (n : ℝ)⁻¹ • ∑ i : Fin n, x i with ha_eq
  set t : ℝ := Real.sqrt (dotProduct a a) with ht_eq
  set v : Fin d → ℝ := t⁻¹ • a with hv_eq
  obtain ⟨hspos, hvunit, hav⟩ := statopia_math_node_3852170914_d7d89bd9 d a ha
  rw [← ht_eq] at hvunit hav
  have hvunit' : dotProduct v v = 1 := by
    rw [hv_eq]; exact hvunit
  have hav' : dotProduct a v = t := by
    rw [hv_eq]; exact hav
  have hobj : ∀ r : Fin d → ℝ,
      (n : ℝ)⁻¹ * (∑ i : Fin n, dotProduct (x i - r) (x i - r))
        = 1 + dotProduct r r - 2 * dotProduct a r := by
    intro r
    have h := statopia_math_node_3652586393_a25bccab d n hn x hx r
    rwa [← ha_eq] at h
  have hmin' := hmin v hvunit'
  rw [hobj p, hobj v, hp, hvunit', hav'] at hmin'
  have hap_ge : t ≤ dotProduct a p := by linarith
  have hap_le : dotProduct a p ≤ t := by
    have h := statopia_math_node_2474807198_d38bf418 d a p hp
    rwa [← ht_eq] at h
  have hap : dotProduct a p = t := le_antisymm hap_le hap_ge
  have ht_sq : t ^ 2 = dotProduct a a := by
    rw [ht_eq]
    exact Real.sq_sqrt hspos.le
  have ht_ne : t ≠ 0 := by
    intro h
    have h0 : dotProduct a a = 0 := by
      rw [← ht_sq, h]
      ring
    linarith
  have hzero : dotProduct (a - t • p) (a - t • p) = 0 := by
    have hsum : dotProduct (a - t • p) (a - t • p)
        = ∑ i : Fin d, (a i * a i - 2 * t * (a i * p i) + t ^ 2 * (p i * p i)) := by
      rw [show dotProduct (a - t • p) (a - t • p)
            = ∑ i : Fin d, (a - t • p) i * (a - t • p) i from rfl]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hsum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [show (∑ i : Fin d, 2 * t * (a i * p i)) = 2 * t * (∑ i : Fin d, a i * p i) from by
      rw [Finset.mul_sum]]
    rw [show (∑ i : Fin d, t ^ 2 * (p i * p i)) = t ^ 2 * (∑ i : Fin d, p i * p i) from by
      rw [Finset.mul_sum]]
    rw [show (∑ i : Fin d, a i * a i) = dotProduct a a from rfl,
      show (∑ i : Fin d, a i * p i) = dotProduct a p from rfl,
      show (∑ i : Fin d, p i * p i) = dotProduct p p from rfl]
    rw [hp, hap, ← ht_sq]
    ring
  have hsub : a - t • p = 0 := (dotProduct_self_eq_zero (v := a - t • p)).mp hzero
  rw [sub_eq_zero] at hsub
  have hp_eq : p = t⁻¹ • a := by
    rw [hsub]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ ht_ne, one_mul]
  rw [hv_eq]
  exact hp_eq
  /- @proof-region region.target-node.session.8951035c90e31888 end -/
