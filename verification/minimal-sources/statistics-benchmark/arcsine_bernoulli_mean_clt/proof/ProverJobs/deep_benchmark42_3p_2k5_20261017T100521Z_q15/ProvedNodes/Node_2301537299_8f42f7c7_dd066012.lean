import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q15.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q15.Base

open Filter MeasureTheory ProbabilityTheory
open Topology

open Filter MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_2301537299_8f42f7c7 : ∀ (theta L : ℝ) (f : ℝ → ℝ) (hf : Measurable f) (hderiv : HasDerivAt f L theta),
    let q : ℝ → ℝ := fun x => if x = theta then L else (f x - f theta) / (x - theta)
    q theta = L ∧ Measurable q ∧ Tendsto q (𝓝 theta) (𝓝 L) := by
  /- @proof-region region.target-node.session.133cd561950812ed begin -/
  intro theta L f hf hderiv
  dsimp only
  refine ⟨by simp, ?_, ?_⟩
  · have hdiv : Measurable fun x : ℝ => (f x - f theta) / (x - theta) :=
      (hf.sub measurable_const).div (measurable_id.sub measurable_const)
    have hpiece : Measurable (({theta} : Set ℝ).piecewise (fun _ => L)
        (fun x : ℝ => (f x - f theta) / (x - theta))) :=
      Measurable.piecewise (measurableSet_singleton theta) measurable_const hdiv
    simpa [Set.piecewise] using hpiece
  · have hslope : Tendsto (slope f theta) (𝓝[≠] theta) (𝓝 L) :=
      hasDerivAt_iff_tendsto_slope.1 hderiv
    have h1 : Tendsto (fun x : ℝ => if x = theta then L else (f x - f theta) / (x - theta))
        (𝓝[≠] theta) (𝓝 L) := by
      refine hslope.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hx' : x ≠ theta := by simpa using hx
      rw [if_neg hx']
      unfold slope
      simp [smul_eq_mul, div_eq_mul_inv, mul_comm]
    have h2 : Tendsto (fun x : ℝ => if x = theta then L else (f x - f theta) / (x - theta))
        (𝓝[({theta} : Set ℝ)] theta) (𝓝 L) := by
      refine (tendsto_const_nhds (x := L)).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [Set.mem_singleton_iff] at hx
      simp [hx]
    have hsplit : 𝓝 theta = 𝓝[≠] theta ⊔ 𝓝[({theta} : Set ℝ)] theta := by
      rw [← nhdsWithin_union]
      simp
    rw [hsplit]
    exact Filter.tendsto_sup.2 ⟨h1, h2⟩
  /- @proof-region region.target-node.session.133cd561950812ed end -/
