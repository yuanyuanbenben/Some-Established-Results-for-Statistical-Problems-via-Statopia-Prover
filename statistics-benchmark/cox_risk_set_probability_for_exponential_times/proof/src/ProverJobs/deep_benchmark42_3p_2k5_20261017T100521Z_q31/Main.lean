import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q31.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q31.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q31.Base

open MeasureTheory ProbabilityTheory

theorem cox_risk_set_probability_for_exponential_times
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n)
    (lambda₀ beta : ℝ) (hlambda : 0 < lambda₀)
    (z : Fin n → ℝ)
    (T : Fin n → Ω → ℝ)
    (hTmeas : ∀ i, Measurable (T i))
    (hTnonneg : ∀ i ω, 0 ≤ T i ω)
    (hindep : iIndepFun T P)
    (hsurvival : ∀ i t, 0 ≤ t →
      P {ω | t < T i ω} =
        ENNReal.ofReal (Real.exp (-lambda₀ * Real.exp (beta * z i) * t))) :
    ∀ i,
      P {ω | ∀ j, j ≠ i → T i ω < T j ω} =
        ENNReal.ofReal
          (Real.exp (beta * z i) /
            ∑ j, Real.exp (beta * z j))
:= by
  /- @proof-region region.root.32d3997ec897 begin -/
  intro i
  have hpos : 0 < lambda₀ * Real.exp (beta * z i) := mul_pos hlambda (Real.exp_pos _)
  have hc : 0 ≤ ∑ j ∈ Finset.univ.erase i, lambda₀ * Real.exp (beta * z j) :=
    Finset.sum_nonneg fun j _ => le_of_lt (mul_pos hlambda (Real.exp_pos _))
  have hs : ∀ t : ℝ, 0 ≤ t → P {ω | t < T i ω} =
      ENNReal.ofReal (Real.exp (-(lambda₀ * Real.exp (beta * z i)) * t)) := by
    intro t ht
    rw [hsurvival i t ht,
      show -lambda₀ * Real.exp (beta * z i) * t
        = -(lambda₀ * Real.exp (beta * z i)) * t from by ring]
  have hrisk := statopia_math_node_3031005534_a772eef4 P n hn lambda₀ beta hlambda z T
    hTmeas hTnonneg hindep hsurvival i
  have hsingle := statopia_math_node_4101882941_149a37f4 P (T i) (hTmeas i) (hTnonneg i)
    (lambda₀ * Real.exp (beta * z i)) hpos hs
    (∑ j ∈ Finset.univ.erase i, lambda₀ * Real.exp (beta * z j)) hc
  have hsplit : lambda₀ * Real.exp (beta * z i)
      + ∑ j ∈ Finset.univ.erase i, lambda₀ * Real.exp (beta * z j)
      = ∑ j, lambda₀ * Real.exp (beta * z j) :=
    Finset.add_sum_erase (Finset.univ : Finset (Fin n))
      (fun j => lambda₀ * Real.exp (beta * z j)) (Finset.mem_univ i)
  have hden : lambda₀ * Real.exp (beta * z i)
      + ∑ j ∈ Finset.univ.erase i, lambda₀ * Real.exp (beta * z j)
      = lambda₀ * ∑ j, Real.exp (beta * z j) := by
    rw [hsplit, Finset.mul_sum]
  have hSpos : 0 < ∑ j, Real.exp (beta * z j) :=
    Finset.sum_pos (fun j _ => Real.exp_pos _)
      ⟨⟨0, Nat.zero_lt_one.trans_le hn⟩, Finset.mem_univ _⟩
  have hSne : (∑ j, Real.exp (beta * z j)) ≠ 0 := ne_of_gt hSpos
  have harg : (lambda₀ * Real.exp (beta * z i))
        / (lambda₀ * Real.exp (beta * z i)
          + ∑ j ∈ Finset.univ.erase i, lambda₀ * Real.exp (beta * z j))
      = Real.exp (beta * z i) / ∑ j, Real.exp (beta * z j) := by
    rw [hden]
    rw [div_eq_div_iff (mul_ne_zero (ne_of_gt hlambda) hSne) hSne]
    ring
  calc P {ω | ∀ j, j ≠ i → T i ω < T j ω}
      = ∫⁻ ω, ENNReal.ofReal
          (Real.exp (-(∑ j ∈ Finset.univ.erase i, lambda₀ * Real.exp (beta * z j))
            * T i ω)) ∂P := hrisk
    _ = ENNReal.ofReal ((lambda₀ * Real.exp (beta * z i))
          / (lambda₀ * Real.exp (beta * z i)
            + ∑ j ∈ Finset.univ.erase i, lambda₀ * Real.exp (beta * z j))) := hsingle.1
    _ = ENNReal.ofReal (Real.exp (beta * z i) / ∑ j, Real.exp (beta * z j)) := by
        rw [harg]
  /- @proof-region region.root.32d3997ec897 end -/
