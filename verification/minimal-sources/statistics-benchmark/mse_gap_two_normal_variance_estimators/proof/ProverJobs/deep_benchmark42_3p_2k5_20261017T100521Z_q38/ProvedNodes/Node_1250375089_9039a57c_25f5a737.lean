import Statlib.StatFoundation.RandomVariable.Gaussian.Standard
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q38.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q38.Base

open MeasureTheory ProbabilityTheory
open scoped BigOperators

open MeasureTheory ProbabilityTheory
open scoped BigOperators

set_option autoImplicit false in
theorem statopia_math_node_1250375089_9039a57c : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (v : ℝ) (hv : 0 ≤ v)
    (Z : Ω → ℝ)
    (hZ_meas : Measurable Z)
    (hZ_law : P.map Z = gaussianReal 0 ⟨v, hv⟩),
    Integrable Z P ∧
    Integrable (fun ω => Z ω ^ 2) P ∧
    Integrable (fun ω => Z ω ^ 3) P ∧
    Integrable (fun ω => Z ω ^ 4) P ∧
    (∫ ω, Z ω ∂P) = 0 ∧
    (∫ ω, Z ω ^ 2 ∂P) = v ∧
    (∫ ω, Z ω ^ 3 ∂P) = 0 ∧
    (∫ ω, Z ω ^ 4 ∂P) = 3 * v ^ 2 := by
  /- @proof-region region.target-node.session.0c2e85c9766a5cd5 begin -/
  intro Ω _ P _ v hv Z hZ_meas hZ_law
  have hmap1 : ∫ ω, Z ω ∂P = ∫ x, x ∂gaussianReal 0 ⟨v, hv⟩ := by
    have h := MeasureTheory.integral_map (μ := P) (φ := Z) hZ_meas.aemeasurable
      (f := fun x : ℝ => x) (by measurability)
    rw [hZ_law] at h
    exact h.symm
  have hmap2 : ∫ ω, Z ω ^ 2 ∂P = ∫ x, x ^ 2 ∂gaussianReal 0 ⟨v, hv⟩ := by
    have h := MeasureTheory.integral_map (μ := P) (φ := Z) hZ_meas.aemeasurable
      (f := fun x : ℝ => x ^ 2) (by measurability)
    rw [hZ_law] at h
    exact h.symm
  have hmap3 : ∫ ω, Z ω ^ 3 ∂P = ∫ x, x ^ 3 ∂gaussianReal 0 ⟨v, hv⟩ := by
    have h := MeasureTheory.integral_map (μ := P) (φ := Z) hZ_meas.aemeasurable
      (f := fun x : ℝ => x ^ 3) (by measurability)
    rw [hZ_law] at h
    exact h.symm
  have hmap4 : ∫ ω, Z ω ^ 4 ∂P = ∫ x, x ^ 4 ∂gaussianReal 0 ⟨v, hv⟩ := by
    have h := MeasureTheory.integral_map (μ := P) (φ := Z) hZ_meas.aemeasurable
      (f := fun x : ℝ => x ^ 4) (by measurability)
    rw [hZ_law] at h
    exact h.symm
  have hIntPow : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) (gaussianReal 0 ⟨v, hv⟩) := by
    intro n
    have h := Statlib.StatFoundation.RandomVariable.Gaussian.memLp_pow_id_gaussianReal
      (μ₀ := (0 : ℝ)) (v := ⟨v, hv⟩) n 1 ENNReal.one_ne_top
    simpa [MeasureTheory.MemLp, MeasureTheory.Integrable, MeasureTheory.HasFiniteIntegral,
      MeasureTheory.eLpNorm_one_eq_lintegral_enorm] using h
  have hIntZ : ∀ n : ℕ, Integrable (fun ω => Z ω ^ n) P := by
    intro n
    have hν : Integrable (fun x : ℝ => x ^ n) (Measure.map Z P) := by
      rw [hZ_law]
      exact hIntPow n
    have h := MeasureTheory.Integrable.comp_measurable (μ := P) (f := Z)
      (g := fun x : ℝ => x ^ n) hν hZ_meas
    simpa using h
  have hmom : ∀ n : ℕ, iteratedDeriv n (mgf (fun x : ℝ => x) (gaussianReal 0 ⟨v, hv⟩)) 0
      = ∫ x, x ^ n ∂gaussianReal 0 ⟨v, hv⟩ := by
    intro n
    have h0 : (0 : ℝ) ∈ interior (integrableExpSet (fun x : ℝ => x) (gaussianReal 0 ⟨v, hv⟩)) := by
      rw [ProbabilityTheory.integrableExpSet_fun_id_gaussianReal]
      simp
    have h := ProbabilityTheory.iteratedDeriv_mgf_zero h0 n
    simpa using h
  have hmgf : mgf (fun x : ℝ => x) (gaussianReal 0 ⟨v, hv⟩)
      = fun s : ℝ => Real.exp (s ^ 2 * v / 2) := by
    funext t
    have h := Statlib.StatFoundation.Statistics.Asymptotic.gaussianReal_integral_exp t v hv
    simpa [ProbabilityTheory.mgf] using h
  have H1 : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Real.exp (s ^ 2 * v / 2))
      (v * t * Real.exp (t ^ 2 * v / 2)) t := by
    intro t
    have hinner : HasDerivAt (fun s : ℝ => s ^ 2 * v / 2) (t * v) t := by
      have h1 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
        simpa using (hasDerivAt_id (x := t)).fun_pow 2
      have h2 : HasDerivAt (fun s : ℝ => s ^ 2 * v) (2 * t * v) t := h1.mul_const v
      have h3 : HasDerivAt (fun s : ℝ => s ^ 2 * v / 2) (2 * t * v / 2) t := h2.div_const 2
      have hv' : 2 * t * v / 2 = t * v := by ring
      rw [hv'] at h3
      exact h3
    have hval : Real.exp (t ^ 2 * v / 2) * (t * v) = v * t * Real.exp (t ^ 2 * v / 2) := by ring
    simpa [hval] using hinner.exp
  have H2 : ∀ t : ℝ, HasDerivAt (fun s : ℝ => v * s * Real.exp (s ^ 2 * v / 2))
      ((v + v ^ 2 * t ^ 2) * Real.exp (t ^ 2 * v / 2)) t := by
    intro t
    have hp : HasDerivAt (fun s : ℝ => v * s) v t := by
      simpa using (hasDerivAt_id (x := t)).const_mul v
    have h := hp.mul (H1 t)
    have hval : v * Real.exp (t ^ 2 * v / 2) + v * t * (v * t * Real.exp (t ^ 2 * v / 2))
        = (v + v ^ 2 * t ^ 2) * Real.exp (t ^ 2 * v / 2) := by ring
    simpa [hval] using h
  have H3 : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (v + v ^ 2 * s ^ 2) * Real.exp (s ^ 2 * v / 2))
      ((3 * v ^ 2 * t + v ^ 3 * t ^ 3) * Real.exp (t ^ 2 * v / 2)) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
      simpa using (hasDerivAt_id (x := t)).fun_pow 2
    have hp1 : HasDerivAt (fun s : ℝ => v ^ 2 * s ^ 2) (v ^ 2 * (2 * t)) t :=
      h1.const_mul (v ^ 2)
    have hp : HasDerivAt (fun s : ℝ => v + v ^ 2 * s ^ 2) (2 * v ^ 2 * t) t := by
      have h := (hasDerivAt_const t v).add hp1
      have hval : 0 + v ^ 2 * (2 * t) = 2 * v ^ 2 * t := by ring
      rw [hval] at h
      exact h
    have h' := hp.mul (H1 t)
    have hval : 2 * v ^ 2 * t * Real.exp (t ^ 2 * v / 2)
        + (v + v ^ 2 * t ^ 2) * (v * t * Real.exp (t ^ 2 * v / 2))
        = (3 * v ^ 2 * t + v ^ 3 * t ^ 3) * Real.exp (t ^ 2 * v / 2) := by ring
    simpa [hval] using h'
  have H4 : ∀ t : ℝ, HasDerivAt
      (fun s : ℝ => (3 * v ^ 2 * s + v ^ 3 * s ^ 3) * Real.exp (s ^ 2 * v / 2))
      ((3 * v ^ 2 + 6 * v ^ 3 * t ^ 2 + v ^ 4 * t ^ 4) * Real.exp (t ^ 2 * v / 2)) t := by
    intro t
    have ha : HasDerivAt (fun s : ℝ => 3 * v ^ 2 * s) (3 * v ^ 2) t := by
      simpa using (hasDerivAt_id (x := t)).const_mul (3 * v ^ 2)
    have hb1 : HasDerivAt (fun s : ℝ => s ^ 3) (3 * t ^ 2) t := by
      simpa using (hasDerivAt_id (x := t)).fun_pow 3
    have hb : HasDerivAt (fun s : ℝ => v ^ 3 * s ^ 3) (v ^ 3 * (3 * t ^ 2)) t :=
      hb1.const_mul (v ^ 3)
    have hp : HasDerivAt (fun s : ℝ => 3 * v ^ 2 * s + v ^ 3 * s ^ 3)
        (3 * v ^ 2 + v ^ 3 * (3 * t ^ 2)) t := ha.add hb
    have h' := hp.mul (H1 t)
    have hval : (3 * v ^ 2 + v ^ 3 * (3 * t ^ 2)) * Real.exp (t ^ 2 * v / 2)
        + (3 * v ^ 2 * t + v ^ 3 * t ^ 3) * (v * t * Real.exp (t ^ 2 * v / 2))
        = (3 * v ^ 2 + 6 * v ^ 3 * t ^ 2 + v ^ 4 * t ^ 4) * Real.exp (t ^ 2 * v / 2) := by ring
    simpa [hval] using h'
  have hstep1 : iteratedDeriv 1 (fun s : ℝ => Real.exp (s ^ 2 * v / 2))
      = deriv (fun s : ℝ => Real.exp (s ^ 2 * v / 2)) := by
    have h := iteratedDeriv_succ (n := 0) (f := fun s : ℝ => Real.exp (s ^ 2 * v / 2))
    rw [iteratedDeriv_zero] at h
    exact h
  have hd1 : iteratedDeriv 1 (fun s : ℝ => Real.exp (s ^ 2 * v / 2))
      = fun t : ℝ => v * t * Real.exp (t ^ 2 * v / 2) := by
    rw [hstep1]
    funext t
    exact (H1 t).deriv
  have hstep2 : iteratedDeriv 2 (fun s : ℝ => Real.exp (s ^ 2 * v / 2))
      = deriv (iteratedDeriv 1 (fun s : ℝ => Real.exp (s ^ 2 * v / 2))) :=
    iteratedDeriv_succ (n := 1) (f := fun s : ℝ => Real.exp (s ^ 2 * v / 2))
  have hd2 : iteratedDeriv 2 (fun s : ℝ => Real.exp (s ^ 2 * v / 2))
      = fun t : ℝ => (v + v ^ 2 * t ^ 2) * Real.exp (t ^ 2 * v / 2) := by
    rw [hstep2, hd1]
    funext t
    exact (H2 t).deriv
  have hstep3 : iteratedDeriv 3 (fun s : ℝ => Real.exp (s ^ 2 * v / 2))
      = deriv (iteratedDeriv 2 (fun s : ℝ => Real.exp (s ^ 2 * v / 2))) :=
    iteratedDeriv_succ (n := 2) (f := fun s : ℝ => Real.exp (s ^ 2 * v / 2))
  have hd3 : iteratedDeriv 3 (fun s : ℝ => Real.exp (s ^ 2 * v / 2))
      = fun t : ℝ => (3 * v ^ 2 * t + v ^ 3 * t ^ 3) * Real.exp (t ^ 2 * v / 2) := by
    rw [hstep3, hd2]
    funext t
    exact (H3 t).deriv
  have hstep4 : iteratedDeriv 4 (fun s : ℝ => Real.exp (s ^ 2 * v / 2))
      = deriv (iteratedDeriv 3 (fun s : ℝ => Real.exp (s ^ 2 * v / 2))) :=
    iteratedDeriv_succ (n := 3) (f := fun s : ℝ => Real.exp (s ^ 2 * v / 2))
  have hd4 : iteratedDeriv 4 (fun s : ℝ => Real.exp (s ^ 2 * v / 2))
      = fun t : ℝ => (3 * v ^ 2 + 6 * v ^ 3 * t ^ 2 + v ^ 4 * t ^ 4) * Real.exp (t ^ 2 * v / 2) := by
    rw [hstep4, hd3]
    funext t
    exact (H4 t).deriv
  have E2 : iteratedDeriv 2 (fun s : ℝ => Real.exp (s ^ 2 * v / 2)) 0 = v := by
    simp [hd2]
  have E3 : iteratedDeriv 3 (fun s : ℝ => Real.exp (s ^ 2 * v / 2)) 0 = 0 := by
    simp [hd3]
  have E4 : iteratedDeriv 4 (fun s : ℝ => Real.exp (s ^ 2 * v / 2)) 0 = 3 * v ^ 2 := by
    simp [hd4]
  have hm2 : ∫ x, x ^ 2 ∂gaussianReal 0 ⟨v, hv⟩ = v := by
    have h := hmom 2
    rw [hmgf, E2] at h
    exact h.symm
  have hm3 : ∫ x, x ^ 3 ∂gaussianReal 0 ⟨v, hv⟩ = 0 := by
    have h := hmom 3
    rw [hmgf, E3] at h
    exact h.symm
  have hm4 : ∫ x, x ^ 4 ∂gaussianReal 0 ⟨v, hv⟩ = 3 * v ^ 2 := by
    have h := hmom 4
    rw [hmgf, E4] at h
    exact h.symm
  refine ⟨?_, hIntZ 2, hIntZ 3, hIntZ 4, ?_, ?_, ?_, ?_⟩
  · simpa using hIntZ 1
  · rw [hmap1, integral_id_gaussianReal]
  · rw [hmap2, hm2]
  · rw [hmap3, hm3]
  · rw [hmap4, hm4]
  /- @proof-region region.target-node.session.0c2e85c9766a5cd5 end -/
