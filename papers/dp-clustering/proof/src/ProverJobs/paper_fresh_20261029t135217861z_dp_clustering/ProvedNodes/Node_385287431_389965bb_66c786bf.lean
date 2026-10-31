import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.Vocabulary
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.Base

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal
open Statlib.Imported

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_385287431_389965bb : ∀ (g q0 : ℝ → ℝ) (c M : ℝ)
    (hc : 0 < c) (hM : 0 < M)
    (hg_meas : Measurable g) (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_support : ∀ x : ℝ, x ∉ Set.Icc (-c) c → g x = 0)
    (hg_bound : ∀ x ∈ Set.Icc (-c) c, g x ≤ M)
    (hq0_meas : Measurable q0) (hq0_nonneg : ∀ x, 0 ≤ q0 x)
    (hq0_density : ∫⁻ x, ENNReal.ofReal (q0 x) ∂volume = 1),
    (∀ (n : ℕ), 1 ≤ n → ∀ (π : Measure ℝ), IsProbabilityMeasure π →
        (∀ᵐ α ∂π, 0 < α) →
        ∀ (r : ℕ), 1 ≤ r → r ≤ n → ∀ x : Fin n → ℝ,
          jointMass g q0 π n r x =
            (∫ α, α ^ r / ascFact α n ∂π) *
              (∑ A ∈ tau n r,
                Finset.prod A (fun B => ((B.card - 1).factorial : ℝ)) *
                  Finset.prod A (fun B => margLik g q0 B x))) ∧
    (∀ (n : ℕ), 1 ≤ n → ∀ (π : Measure ℝ), IsProbabilityMeasure π →
        (∀ᵐ α ∂π, 0 < α) →
        ∀ (s t : ℕ) (x : Fin n → ℝ), 1 ≤ s → s ≤ n → 1 ≤ t → t ≤ n →
          (∑ r ∈ Finset.Icc 1 n, jointMass g q0 π n r x) ≠ 0 →
          (∫ α, α ^ t / ascFact α n ∂π) ≠ 0 →
          (∑ A ∈ tau n t,
              Finset.prod A (fun B => ((B.card - 1).factorial : ℝ)) *
                Finset.prod A (fun B => margLik g q0 B x)) ≠ 0 →
          postProb g q0 π n s x / postProb g q0 π n t x =
            ((∫ α, α ^ s / ascFact α n ∂π) / (∫ α, α ^ t / ascFact α n ∂π)) *
              ((∑ A ∈ tau n s,
                  Finset.prod A (fun B => ((B.card - 1).factorial : ℝ)) *
                    Finset.prod A (fun B => margLik g q0 B x)) /
                (∑ A ∈ tau n t,
                  Finset.prod A (fun B => ((B.card - 1).factorial : ℝ)) *
                    Finset.prod A (fun B => margLik g q0 B x)))) ∧
    (∀ (αstar : ℝ), 0 < αstar → ∀ (n : ℕ), 1 ≤ n →
        (∀ (r : ℕ), 1 ≤ r → r ≤ n →
          (∫ α, α ^ r / ascFact α n ∂(Measure.dirac αstar)) =
              αstar ^ r / ascFact αstar n ∧
            0 < (∫ α, α ^ r / ascFact α n ∂(Measure.dirac αstar))) ∧
        (∀ (t : ℕ) (x : Fin n → ℝ), 1 ≤ t → t < n →
          (∑ r ∈ Finset.Icc 1 n, jointMass g q0 (Measure.dirac αstar) n r x) ≠ 0 →
          (∑ A ∈ tau n t,
              Finset.prod A (fun B => ((B.card - 1).factorial : ℝ)) *
                Finset.prod A (fun B => margLik g q0 B x)) ≠ 0 →
          postProb g q0 (Measure.dirac αstar) n (t + 1) x /
              postProb g q0 (Measure.dirac αstar) n t x =
            αstar *
              ((∑ A ∈ tau n (t + 1),
                  Finset.prod A (fun B => ((B.card - 1).factorial : ℝ)) *
                    Finset.prod A (fun B => margLik g q0 B x)) /
                (∑ A ∈ tau n t,
                  Finset.prod A (fun B => ((B.card - 1).factorial : ℝ)) *
                    Finset.prod A (fun B => margLik g q0 B x))))) := by
  /- @proof-region region.target-node.session.c0562d2198c1754d begin -/
  intro g q0 c M hc hM hg_meas hg_nonneg hg_support hg_bound hq0_meas hq0_nonneg hq0_density
  have hcard : ∀ (n r : ℕ) (A : Finset (Finset (Fin n))), A ∈ tau n r → A.card = r := by
    intro n r A hA
    simp only [tau, Finset.mem_filter] at hA
    exact hA.2.1
  have hprA : ∀ (n r : ℕ) (π : Measure ℝ) (A : Finset (Finset (Fin n))), A ∈ tau n r →
      prA π n A = (∏ B ∈ A, ((B.card - 1).factorial : ℝ)) *
        (∫ α, α ^ r / ascFact α n ∂π) := by
    intro n r π A hA
    have hcA : A.card = r := hcard n r A hA
    simp only [prA, eppf]
    have hfun : (fun α : ℝ => α ^ A.card / ascFact α n *
          (∏ B ∈ A, ((B.card - 1).factorial : ℝ))) =
        (fun α : ℝ => (∏ B ∈ A, ((B.card - 1).factorial : ℝ)) *
          (α ^ r / ascFact α n)) := by
      funext α
      rw [hcA]
      ring
    rw [hfun, MeasureTheory.integral_const_mul]
  have hmain : ∀ (n : ℕ), 1 ≤ n → ∀ (π : Measure ℝ), IsProbabilityMeasure π →
      ∀ (r : ℕ), 1 ≤ r → r ≤ n → ∀ x : Fin n → ℝ,
        jointMass g q0 π n r x = (∫ α, α ^ r / ascFact α n ∂π) *
          (∑ A ∈ tau n r,
            (∏ B ∈ A, ((B.card - 1).factorial : ℝ)) *
              ∏ B ∈ A, margLik g q0 B x) := by
    intro n hn π hπ r hr hrn x
    simp only [jointMass]
    have hstep : ∀ A ∈ tau n r, prA π n A * ∏ B ∈ A, margLik g q0 B x =
        (∫ α, α ^ r / ascFact α n ∂π) *
          ((∏ B ∈ A, ((B.card - 1).factorial : ℝ)) *
            ∏ B ∈ A, margLik g q0 B x) := by
      intro A hA
      rw [hprA n r π A hA]
      ring
    rw [Finset.sum_congr rfl hstep, Finset.mul_sum]
  have hratio : ∀ (n : ℕ), 1 ≤ n → ∀ (π : Measure ℝ), IsProbabilityMeasure π →
      ∀ (s t : ℕ) (x : Fin n → ℝ), 1 ≤ s → s ≤ n → 1 ≤ t → t ≤ n →
        (∑ r ∈ Finset.Icc 1 n, jointMass g q0 π n r x) ≠ 0 →
        (∫ α, α ^ t / ascFact α n ∂π) ≠ 0 →
        (∑ A ∈ tau n t,
            (∏ B ∈ A, ((B.card - 1).factorial : ℝ)) *
              ∏ B ∈ A, margLik g q0 B x) ≠ 0 →
        postProb g q0 π n s x / postProb g q0 π n t x =
          ((∫ α, α ^ s / ascFact α n ∂π) / (∫ α, α ^ t / ascFact α n ∂π)) *
            ((∑ A ∈ tau n s,
                (∏ B ∈ A, ((B.card - 1).factorial : ℝ)) *
                  ∏ B ∈ A, margLik g q0 B x) /
              (∑ A ∈ tau n t,
                (∏ B ∈ A, ((B.card - 1).factorial : ℝ)) *
                  ∏ B ∈ A, margLik g q0 B x)) := by
    intro n hn π hπ s t x hs hsn ht htn hT hPt hNt
    have hJ : postProb g q0 π n s x / postProb g q0 π n t x =
        jointMass g q0 π n s x / jointMass g q0 π n t x := by
      simp only [postProb]
      by_cases hJt : jointMass g q0 π n t x = 0
      · simp [hJt]
      · field_simp
    rw [hJ, hmain n hn π hπ s hs hsn x, hmain n hn π hπ t ht htn x]
    field_simp
  refine ⟨?_, ?_, ?_⟩
  · intro n hn π hπ hpos r hr hrn x
    exact hmain n hn π hπ r hr hrn x
  · intro n hn π hπ hpos s t x hs hsn ht htn hT hPt hNt
    exact hratio n hn π hπ s t x hs hsn ht htn hT hPt hNt
  · intro αstar hα n hn
    have hasc : 0 < ascFact αstar n := by
      simp only [ascFact]
      refine Finset.prod_pos ?_
      intro k hk
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hPval : ∀ r, 1 ≤ r → r ≤ n →
        (∫ α, α ^ r / ascFact α n ∂(Measure.dirac αstar)) =
          αstar ^ r / ascFact αstar n := by
      intro r hr hrn
      rw [MeasureTheory.integral_dirac]
    have hPpos : ∀ r, 1 ≤ r → r ≤ n →
        0 < (∫ α, α ^ r / ascFact α n ∂(Measure.dirac αstar)) := by
      intro r hr hrn
      rw [hPval r hr hrn]
      exact div_pos (pow_pos hα r) hasc
    refine ⟨?_, ?_⟩
    · intro r hr hrn
      exact ⟨hPval r hr hrn, hPpos r hr hrn⟩
    · intro t x ht htn hT hNt
      have htn' : t ≤ n := le_of_lt htn
      have hrat := hratio n hn (Measure.dirac αstar) inferInstance (t + 1) t x
        (by omega) (by omega) ht htn' hT (hPpos t ht htn').ne' hNt
      have hPrat : (∫ α, α ^ (t + 1) / ascFact α n ∂(Measure.dirac αstar)) /
          (∫ α, α ^ t / ascFact α n ∂(Measure.dirac αstar)) = αstar := by
        rw [hPval (t + 1) (by omega) (by omega), hPval t ht htn', pow_succ]
        have hA : ascFact αstar n ≠ 0 := hasc.ne'
        have hp : αstar ^ t ≠ 0 := (pow_pos hα t).ne'
        field_simp
      rw [hrat, hPrat]
  /- @proof-region region.target-node.session.c0562d2198c1754d end -/

end Statlib.Imported
