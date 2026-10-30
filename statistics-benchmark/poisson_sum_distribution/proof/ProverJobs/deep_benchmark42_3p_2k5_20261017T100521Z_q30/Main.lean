import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q30.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q30.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q30.Base

open MeasureTheory ProbabilityTheory
namespace Msc62GroundTruth

theorem poisson_sum_distribution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n)
    (lambda : Fin n → ℝ) (hlambda : ∀ i, 0 < lambda i)
    (X : Fin n → Ω → ℕ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (hX_pmf : ∀ i m,
      (P {ω | X i ω = m}).toReal =
        Real.exp (-(lambda i)) * (lambda i) ^ m / (Nat.factorial m : ℝ))
    (k : ℕ) :
    let S : Ω → ℕ := fun ω => ∑ i : Fin n, X i ω
    let Lambda : ℝ := ∑ i : Fin n, lambda i
    (P {ω | S ω = k}).toReal =
      Real.exp (-Lambda) * Lambda ^ k / (Nat.factorial k : ℝ)
:= by
  /- @proof-region region.root.63e40df6ac60 begin -/
  classical
  dsimp only
  set L : ℝ := ∑ i : Fin n, lambda i with hL
  obtain ⟨-, -, hpart⟩ := statopia_math_node_2879488259_e798087e P n X hX_meas k
  have hprod : ∀ m ∈ (Finset.univ : Finset (Fin n)).piAntidiag k,
      (P {ω : Ω | ∀ i : Fin n, X i ω = m i}).toReal
        = ∏ i : Fin n, (P {ω : Ω | X i ω = m i}).toReal := by
    intro m _
    have hset : {ω : Ω | ∀ i : Fin n, X i ω = m i}
        = ⋂ i : Fin n, {ω : Ω | X i ω = m i} := by
      ext ω
      simp
    rw [hset]
    exact (statopia_math_node_3983978749_db5aa105 P n X hX_meas hX_indep m).2
  have hpois : ∀ m : Fin n → ℕ,
      (∏ i : Fin n, (P {ω : Ω | X i ω = m i}).toReal)
        = Real.exp (-L) * ∏ i : Fin n, ((lambda i) ^ (m i) / (Nat.factorial (m i) : ℝ)) := by
    intro m
    have h1 : (∏ i : Fin n, (P {ω : Ω | X i ω = m i}).toReal)
        = ∏ i : Fin n,
            (Real.exp (-(lambda i)) * (lambda i) ^ (m i) / (Nat.factorial (m i) : ℝ)) :=
      Finset.prod_congr rfl fun i _ => hX_pmf i (m i)
    rw [h1]
    have he : (∏ i : Fin n, Real.exp (-(lambda i))) = Real.exp (-L) := by
      rw [← Real.exp_sum, Finset.sum_neg_distrib, ← hL]
    calc (∏ i : Fin n,
            (Real.exp (-(lambda i)) * (lambda i) ^ (m i) / (Nat.factorial (m i) : ℝ)))
        = (∏ i : Fin n, Real.exp (-(lambda i))) * (∏ i : Fin n, (lambda i) ^ (m i))
            / (∏ i : Fin n, (Nat.factorial (m i) : ℝ)) := by
          rw [Finset.prod_div_distrib, Finset.prod_mul_distrib]
      _ = Real.exp (-L) * (∏ i : Fin n, (lambda i) ^ (m i))
            / (∏ i : Fin n, (Nat.factorial (m i) : ℝ)) := by
          rw [he]
      _ = Real.exp (-L) * ((∏ i : Fin n, (lambda i) ^ (m i))
            / (∏ i : Fin n, (Nat.factorial (m i) : ℝ))) := by
          rw [mul_div_assoc]
      _ = Real.exp (-L) * ∏ i : Fin n, ((lambda i) ^ (m i) / (Nat.factorial (m i) : ℝ)) := by
          rw [Finset.prod_div_distrib]
  have hterm : ∀ m ∈ (Finset.univ : Finset (Fin n)).piAntidiag k,
      (Nat.multinomial (Finset.univ : Finset (Fin n)) m : ℝ) * ∏ i : Fin n, (lambda i) ^ (m i)
        = (Nat.factorial k : ℝ)
            * ∏ i : Fin n, ((lambda i) ^ (m i) / (Nat.factorial (m i) : ℝ)) := by
    intro m hm
    have hm' : m ∈ (Finset.univ : Finset (Fin n)).piAntidiag k := hm
    have hsum : (∑ i : Fin n, m i) = k := (Finset.mem_piAntidiag.mp hm').1
    have hfac : Nat.multinomial (Finset.univ : Finset (Fin n)) m * (∏ i : Fin n, Nat.factorial (m i))
        = Nat.factorial k := by
      rw [statopia_math_node_1039099906_8ca3f57f, hsum]
    have hfacR : (Nat.multinomial (Finset.univ : Finset (Fin n)) m : ℝ)
          * (∏ i : Fin n, (Nat.factorial (m i) : ℝ)) = (Nat.factorial k : ℝ) := by
      have h := congrArg (fun x : ℕ => (x : ℝ)) hfac
      push_cast at h
      simpa using h
    have hPm : (∏ i : Fin n, (Nat.factorial (m i) : ℝ)) ≠ 0 := by
      have hpos : 0 < ∏ i : Fin n, (Nat.factorial (m i) : ℝ) := by
        apply Finset.prod_pos
        intro i _
        exact_mod_cast Nat.factorial_pos (m i)
      exact ne_of_gt hpos
    rw [Finset.prod_div_distrib, ← mul_div_assoc, eq_div_iff hPm, ← hfacR]
    ring
  have hmulti : (∑ m ∈ (Finset.univ : Finset (Fin n)).piAntidiag k,
        ∏ i : Fin n, ((lambda i) ^ (m i) / (Nat.factorial (m i) : ℝ)))
      = L ^ k / (Nat.factorial k : ℝ) := by
    have hE11 : L ^ k = ∑ m ∈ (Finset.univ : Finset (Fin n)).piAntidiag k,
        (Nat.multinomial (Finset.univ : Finset (Fin n)) m : ℝ) * ∏ i : Fin n, (lambda i) ^ (m i) := by
      have h := Finset.sum_pow_eq_sum_piAntidiag (Finset.univ : Finset (Fin n)) lambda k
      rw [← hL] at h
      simpa using h
    have hsplit : (∑ m ∈ (Finset.univ : Finset (Fin n)).piAntidiag k,
          (Nat.multinomial (Finset.univ : Finset (Fin n)) m : ℝ) * ∏ i : Fin n, (lambda i) ^ (m i))
        = (Nat.factorial k : ℝ) * ∑ m ∈ (Finset.univ : Finset (Fin n)).piAntidiag k,
            ∏ i : Fin n, ((lambda i) ^ (m i) / (Nat.factorial (m i) : ℝ)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m hm => hterm m hm
    rw [hsplit] at hE11
    have hK : (Nat.factorial k : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    rw [eq_div_iff hK, hE11]
    ring
  calc (P {ω : Ω | (∑ i : Fin n, X i ω) = k}).toReal
      = ∑ m ∈ (Finset.univ : Finset (Fin n)).piAntidiag k,
          (P {ω : Ω | ∀ i : Fin n, X i ω = m i}).toReal := hpart
    _ = ∑ m ∈ (Finset.univ : Finset (Fin n)).piAntidiag k,
          Real.exp (-L) * ∏ i : Fin n, ((lambda i) ^ (m i) / (Nat.factorial (m i) : ℝ)) := by
        exact Finset.sum_congr rfl fun m hm => by rw [hprod m hm, hpois m]
    _ = Real.exp (-L) * ∑ m ∈ (Finset.univ : Finset (Fin n)).piAntidiag k,
          ∏ i : Fin n, ((lambda i) ^ (m i) / (Nat.factorial (m i) : ℝ)) := by
        rw [Finset.mul_sum]
    _ = Real.exp (-L) * (L ^ k / (Nat.factorial k : ℝ)) := by rw [hmulti]
    _ = Real.exp (-L) * L ^ k / (Nat.factorial k : ℝ) := by rw [mul_div_assoc]
  /- @proof-region region.root.63e40df6ac60 end -/

end Msc62GroundTruth
