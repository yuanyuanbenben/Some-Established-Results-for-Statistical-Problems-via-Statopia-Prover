import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q01.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q01.Base

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

set_option autoImplicit false in
theorem statopia_math_node_3980798612_87c1b9de : ∀ (u : ℂ) (hu : ‖u‖ ≤ 1),
    ‖Complex.exp u - 1 - u - u ^ 2 / 2‖ ≤ ‖u‖ ^ 3 := by
  /- @proof-region region.target-node.session.bb4dd1bf2da52fbd begin -/
  intro u hu
  have hderiv : ∀ z : ℂ,
      HasDerivAt (fun w : ℂ => Complex.exp w - 1 - w - w ^ 2 / 2) (Complex.exp z - 1 - z) z := by
    intro z
    have hexp : HasDerivAt Complex.exp (Complex.exp z) z := Complex.hasDerivAt_exp z
    have hc : HasDerivAt (fun _ : ℂ => (1 : ℂ)) 0 z := hasDerivAt_const (x := z) (c := (1 : ℂ))
    have hid : HasDerivAt (fun w : ℂ => w) 1 z := hasDerivAt_id z
    have hsq : HasDerivAt (fun w : ℂ => w ^ 2 / 2) z z := by
      have hp : HasDerivAt (fun w : ℂ => w ^ 2) (2 * z) z := by
        simpa using (hasDerivAt_id z).pow 2
      have hd : HasDerivAt (fun w : ℂ => w ^ 2 / 2) (2 * z / 2) z := hp.div_const 2
      have he : 2 * z / 2 = z := by ring
      rw [he] at hd
      exact hd
    have h2 : HasDerivAt (fun w : ℂ => Complex.exp w - 1 - w - w ^ 2 / 2)
        (Complex.exp z - 0 - 1 - z) z := ((hexp.sub hc).sub hid).sub hsq
    have he2 : Complex.exp z - 0 - 1 - z = Complex.exp z - 1 - z := by ring
    rw [he2] at h2
    exact h2
  have hconv : Convex ℝ {z : ℂ | ‖z‖ ≤ ‖u‖} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    calc ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = a * ‖x‖ + b * ‖y‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ a * ‖u‖ + b * ‖u‖ :=
          add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
      _ = ‖u‖ := by rw [← add_mul, hab, one_mul]
  have hbound : ∀ z ∈ {z : ℂ | ‖z‖ ≤ ‖u‖}, ‖Complex.exp z - 1 - z‖ ≤ ‖u‖ ^ 2 := by
    intro z hz
    have hzu : ‖z‖ ≤ ‖u‖ := hz
    have hz1 : ‖z‖ ≤ 1 := le_trans hzu hu
    have h2 : ‖Complex.exp z - 1 - z‖ ≤ ‖z‖ ^ 2 := by
      simpa using Complex.exp_bound_sq 0 z hz1
    have h3 : ‖z‖ ^ 2 ≤ ‖u‖ ^ 2 := by nlinarith [norm_nonneg z, norm_nonneg u]
    linarith
  have hmain : ‖(fun z : ℂ => Complex.exp z - 1 - z - z ^ 2 / 2) u -
      (fun z : ℂ => Complex.exp z - 1 - z - z ^ 2 / 2) 0‖ ≤ ‖u‖ ^ 2 * ‖u - 0‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      (s := {z : ℂ | ‖z‖ ≤ ‖u‖}) (f := fun z : ℂ => Complex.exp z - 1 - z - z ^ 2 / 2)
      (x := 0) (y := u) (C := ‖u‖ ^ 2)
      (fun z _ => (hderiv z).differentiableAt)
      (fun z hz => by
        rw [(hderiv z).deriv]
        exact hbound z hz)
      hconv (by simp) (by simp)
  have hfin : ‖Complex.exp u - 1 - u - u ^ 2 / 2‖ ≤ ‖u‖ ^ 2 * ‖u‖ := by
    simpa using hmain
  calc ‖Complex.exp u - 1 - u - u ^ 2 / 2‖ ≤ ‖u‖ ^ 2 * ‖u‖ := hfin
    _ = ‖u‖ ^ 3 := by ring
  /- @proof-region region.target-node.session.bb4dd1bf2da52fbd end -/
