import Statlib.StatFoundation.Convergence.AnalysisTools.ConvergenceModes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q07.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q07.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q07.ProvedNodes.Node_4173812781_fb083835_9423f68b

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

set_option autoImplicit false in
theorem statopia_math_node_3098910026_8cbaa9f6 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (mean varianceSq : ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (hX_ident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hfourth_integrable : Integrable (fun ω => |X 0 ω| ^ 4) P)
    (hmean : ∫ ω, X 0 ω ∂P = mean)
    (hvariance : ∫ ω, (X 0 ω - mean) ^ 2 ∂P = varianceSq),
    let D : ℕ → Ω → ℝ :=
      fun n ω => (n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, X i ω) - mean
    (∀ n : ℕ, 1 ≤ n → ∫ ω, (D n ω) ^ 2 ∂P = varianceSq / (n : ℝ)) ∧
    (∀ n : ℕ, 1 ≤ n →
      ∫ ω, Real.sqrt (n : ℝ) * (D n ω) ^ 2 ∂P
        = varianceSq / Real.sqrt (n : ℝ)) ∧
    Tendsto (fun n : ℕ => varianceSq / Real.sqrt (n : ℝ)) atTop (𝓝 0) ∧
    TendstoInMeasure P
      (fun (n : ℕ) (ω : Ω) => -(Real.sqrt (n : ℝ) * (D n ω) ^ 2)) atTop (fun _ => 0) := by
  /- @proof-region region.target-node.session.10de82be59052e72 begin -/
  intro Ω instΩ P instP X mean varianceSq hX_meas hX_indep hX_ident hfourth_integrable hmean hvariance
  dsimp only
  obtain ⟨hvar_nonneg, hZ⟩ :=
    statopia_math_node_4173812781_fb083835 P X mean varianceSq hX_meas hX_indep hX_ident
      hfourth_integrable hmean hvariance
  set Z : ℕ → Ω → ℝ := fun i ω => X i ω - mean with hZdef
  have hZmeas : ∀ i, Measurable (Z i) := fun i => (hZ i).1
  have hZmemLp : ∀ i, MemLp (Z i) 2 P := fun i => (hZ i).2.1
  have hZint : ∀ i, ∫ ω, Z i ω ∂P = 0 := fun i => (hZ i).2.2.1
  have hZsq : ∀ i, ∫ ω, (Z i ω) ^ 2 ∂P = varianceSq := fun i => (hZ i).2.2.2.1
  have hZpair : ∀ a b : ℕ, a ≠ b → IndepFun (Z a) (Z b) P :=
    fun a b hab => (hZ a).2.2.2.2.2 a b hab
  have hmul_int : ∀ i j : ℕ, Integrable (fun ω : Ω => Z i ω * Z j ω) P := by
    intro i j
    have h1 : MemLp (fun ω : Ω => Z i ω + Z j ω) 2 P := (hZmemLp i).add (hZmemLp j)
    have h2 : MemLp (fun ω : Ω => Z i ω - Z j ω) 2 P := (hZmemLp i).sub (hZmemLp j)
    have hi1 : Integrable (fun ω : Ω => (Z i ω + Z j ω) ^ 2) P :=
      (MeasureTheory.memLp_two_iff_integrable_sq h1.aestronglyMeasurable).1 h1
    have hi2 : Integrable (fun ω : Ω => (Z i ω - Z j ω) ^ 2) P :=
      (MeasureTheory.memLp_two_iff_integrable_sq h2.aestronglyMeasurable).1 h2
    have hfun : (fun ω : Ω => Z i ω * Z j ω)
        = fun ω : Ω => (4 : ℝ)⁻¹ * ((Z i ω + Z j ω) ^ 2 - (Z i ω - Z j ω) ^ 2) := by
      funext ω
      ring
    rw [hfun]
    simpa only [smul_eq_mul] using (hi1.sub hi2).const_mul ((4 : ℝ)⁻¹)
  have int_sum : ∀ (s : Finset ℕ) (f : ℕ → Ω → ℝ), (∀ i ∈ s, Integrable (f i) P) →
      Integrable (fun ω : Ω => ∑ i ∈ s, f i ω) P := by
    intro s
    induction s using Finset.induction with
    | empty =>
      intro f _
      simp
    | insert a s ha ih =>
      intro f hf
      have h1 : Integrable (f a) P := hf a (Finset.mem_insert_self a s)
      have h2 : Integrable (fun ω : Ω => ∑ i ∈ s, f i ω) P :=
        ih f (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      simpa only [Finset.sum_insert ha] using h1.add h2
  have hS2int : ∀ n : ℕ, Integrable (fun ω : Ω => (∑ i ∈ Finset.range n, Z i ω) ^ 2) P := by
    intro n
    have hfun : (fun ω : Ω => (∑ i ∈ Finset.range n, Z i ω) ^ 2)
        = fun ω : Ω => ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, Z i ω * Z j ω := by
      funext ω
      rw [pow_two, Finset.sum_mul_sum]
    rw [hfun]
    exact int_sum (Finset.range n) (fun i ω => ∑ j ∈ Finset.range n, Z i ω * Z j ω)
      (fun i _ => int_sum (Finset.range n) (fun j ω => Z i ω * Z j ω) (fun j _ => hmul_int i j))
  have hSsq : ∀ n : ℕ, ∫ ω : Ω, (∑ i ∈ Finset.range n, Z i ω) ^ 2 ∂P = (n : ℝ) * varianceSq := by
    intro n
    have hfun : (fun ω : Ω => (∑ i ∈ Finset.range n, Z i ω) ^ 2)
        = fun ω : Ω => ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, Z i ω * Z j ω := by
      funext ω
      rw [pow_two, Finset.sum_mul_sum]
    rw [hfun]
    rw [MeasureTheory.integral_finset_sum (Finset.range n)
      (fun i _ => int_sum (Finset.range n) (fun j ω => Z i ω * Z j ω) (fun j _ => hmul_int i j))]
    have hinner : ∀ i ∈ Finset.range n,
        ∫ ω : Ω, ∑ j ∈ Finset.range n, Z i ω * Z j ω ∂P = varianceSq := by
      intro i hi
      rw [MeasureTheory.integral_finset_sum (Finset.range n) (fun j _ => hmul_int i j)]
      rw [Finset.sum_eq_single i
        (fun j hj hji => by
          have hfac := (hZpair i j (Ne.symm hji)).integral_fun_mul_eq_mul_integral
            (hZmeas i).aestronglyMeasurable (hZmeas j).aestronglyMeasurable
          rw [hfac, hZint i]
          simp)
        (fun hmem => by exact absurd hi hmem)]
      rw [show (fun ω : Ω => Z i ω * Z i ω) = fun ω : Ω => (Z i ω) ^ 2 from by funext ω; ring]
      exact hZsq i
    rw [Finset.sum_congr rfl hinner]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hDpt : ∀ (n : ℕ), 1 ≤ n → ∀ ω : Ω,
      (n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, X i ω) - mean
        = (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, Z i ω := by
    intro n hn ω
    have hn0 : (n : ℝ) ≠ 0 := by
      have h : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    simp only [hZdef]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_sub,
      ← mul_assoc, inv_mul_cancel₀ hn0, one_mul]
  have hfirst : ∀ n : ℕ, 1 ≤ n →
      ∫ ω : Ω, ((n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, X i ω) - mean) ^ 2 ∂P = varianceSq / (n : ℝ) := by
    intro n hn
    have hpt : (fun ω : Ω => ((n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, X i ω) - mean) ^ 2)
        = fun ω : Ω => ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, Z i ω) ^ 2 := by
      funext ω
      rw [hDpt n hn ω]
    rw [hpt]
    have hsq : (fun ω : Ω => ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, Z i ω) ^ 2)
        = fun ω : Ω => ((n : ℝ)⁻¹) ^ 2 * (∑ i ∈ Finset.range n, Z i ω) ^ 2 := by
      funext ω
      ring
    rw [hsq, MeasureTheory.integral_const_mul, hSsq n]
    have hn0 : (n : ℝ) ≠ 0 := by
      have h : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    field_simp
  have hsecond : ∀ n : ℕ, 1 ≤ n →
      ∫ ω : Ω, Real.sqrt (n : ℝ) * ((n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, X i ω) - mean) ^ 2 ∂P
        = varianceSq / Real.sqrt (n : ℝ) := by
    intro n hn
    have hpt : (fun ω : Ω => Real.sqrt (n : ℝ) * ((n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, X i ω) - mean) ^ 2)
        = fun ω : Ω => Real.sqrt (n : ℝ) * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, Z i ω) ^ 2 := by
      funext ω
      rw [hDpt n hn ω]
    rw [hpt]
    have hfac : (fun ω : Ω => Real.sqrt (n : ℝ) * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, Z i ω) ^ 2)
        = fun ω : Ω => (Real.sqrt (n : ℝ) * ((n : ℝ)⁻¹) ^ 2) * (∑ i ∈ Finset.range n, Z i ω) ^ 2 := by
      funext ω
      ring
    rw [hfac, MeasureTheory.integral_const_mul, hSsq n]
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have h : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    set s : ℝ := Real.sqrt (n : ℝ) with hsdef
    have hsne : s ≠ 0 := by
      rw [hsdef]
      exact ne_of_gt (Real.sqrt_pos.mpr hnpos)
    have hs2ne : s * s ≠ 0 := mul_ne_zero hsne hsne
    have hss : s * s = (n : ℝ) := by
      rw [hsdef]
      exact Real.mul_self_sqrt hnpos.le
    rw [← hss]
    field_simp
  have hRint : ∀ n : ℕ, 1 ≤ n → Integrable (fun ω : Ω =>
      Real.sqrt (n : ℝ) * ((n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, X i ω) - mean) ^ 2) P := by
    intro n hn
    have hpt : (fun ω : Ω => Real.sqrt (n : ℝ) * ((n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, X i ω) - mean) ^ 2)
        = fun ω : Ω => Real.sqrt (n : ℝ) * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, Z i ω) ^ 2 := by
      funext ω
      rw [hDpt n hn ω]
    rw [hpt]
    have hfac : (fun ω : Ω => Real.sqrt (n : ℝ) * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, Z i ω) ^ 2)
        = fun ω : Ω => (Real.sqrt (n : ℝ) * ((n : ℝ)⁻¹) ^ 2) * (∑ i ∈ Finset.range n, Z i ω) ^ 2 := by
      funext ω
      ring
    rw [hfac]
    simpa only [smul_eq_mul] using
      (hS2int n).const_mul (Real.sqrt (n : ℝ) * ((n : ℝ)⁻¹) ^ 2)
  have hthird : Tendsto (fun n : ℕ => varianceSq / Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
    have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    have hinv : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hsqrt
    simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul varianceSq
  refine ⟨hfirst, hsecond, hthird, ?_⟩
  have hR_tim : TendstoInMeasure P
      (fun (n : ℕ) (ω : Ω) => Real.sqrt (n : ℝ) * ((n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, X i ω) - mean) ^ 2)
      atTop (fun _ => 0) := by
    rw [Statlib.StatFoundation.Convergence.tendstoInMeasure_iff_measureReal_dist]
    intro ε hε
    have hupper : Tendsto (fun n : ℕ => ε⁻¹ * (varianceSq / Real.sqrt (n : ℝ))) atTop (𝓝 0) := by
      have hc := hthird.const_mul ε⁻¹
      simpa using hc
    refine squeeze_zero' ?_ ?_ hupper
    · exact Filter.Eventually.of_forall (fun n => MeasureTheory.measureReal_nonneg)
    · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      have hset : {ω : Ω | ε ≤ dist (Real.sqrt (n : ℝ) * ((n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, X i ω) - mean) ^ 2) 0}
          = {ω : Ω | ε ≤ Real.sqrt (n : ℝ) * ((n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, X i ω) - mean) ^ 2} := by
        ext ω
        have hnn : (0 : ℝ) ≤ Real.sqrt (n : ℝ) * ((n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, X i ω) - mean) ^ 2 := by
          positivity
        simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero, abs_of_nonneg hnn]
      rw [hset]
      have hmark := MeasureTheory.mul_meas_ge_le_integral_of_nonneg
        (f := fun ω : Ω => Real.sqrt (n : ℝ) * ((n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, X i ω) - mean) ^ 2)
        (Filter.Eventually.of_forall (fun ω => by positivity)) (hRint n hn) ε
      rw [hsecond n hn] at hmark
      have h2 := mul_le_mul_of_nonneg_left hmark (le_of_lt (by positivity : (0 : ℝ) < ε⁻¹))
      simpa only [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hε), one_mul] using h2
  have hneg := Statlib.StatFoundation.Convergence.tendstoInMeasure_neg hR_tim
  simpa using hneg
  /- @proof-region region.target-node.session.10de82be59052e72 end -/
