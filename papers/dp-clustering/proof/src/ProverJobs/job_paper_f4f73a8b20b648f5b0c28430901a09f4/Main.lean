import ProverJobs.job_paper_f4f73a8b20b648f5b0c28430901a09f4.Vocabulary
import ProverJobs.job_paper_f4f73a8b20b648f5b0c28430901a09f4.ProvedNodes
import ProverJobs.job_paper_f4f73a8b20b648f5b0c28430901a09f4.Base

open MeasureTheory
open scoped BigOperators
open Classical
noncomputable section
namespace Statlib.Imported

theorem paper_f4f73a8b20b648f5b0c28430901a09f4
    (t : ℕ) (p : Fin t → ℝ) (Rm : Fin t → Measure ℝ)
    (hRm_prob : ∀ j : Fin t, IsProbabilityMeasure (Rm j))
    (hRm_distinct : ∀ j k : Fin t, j ≠ k → Rm j ≠ Rm k)
    (hp_pos : ∀ j : Fin t, 0 < p j)
    (hp_lt : ∀ j : Fin t, p j < 1)
    (hp_sum : ∑ j : Fin t, p j = 1)
    (g q0 : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hg_nonneg : ∀ x : ℝ, 0 ≤ g x)
    (θstar : Fin t → ℝ)
    (hsep : ∀ j k : Fin t, j ≠ k → 2 * c < |θstar j - θstar k|)
    (m M : ℝ) (hm : 0 < m)
    (hT1_lo : ∀ x ∈ Set.Icc (-c) c, m ≤ g x)
    (hT1_hi : ∀ x ∈ Set.Icc (-c) c, g x ≤ M)
    (hT2_diff : DifferentiableOn ℝ g (Set.Ioo (-c) c))
    (Rc : ℝ) (hT2_log : ∀ x ∈ Set.Ioo (-c) c, |deriv g x / g x| ≤ Rc)
    (U : ℝ) (hU : 0 < U)
    (hT3 : ∀ y ∈ Set.Icc (0 : ℝ) (2 * c), q0 y + q0 (-y) ≤ U)
    (L : ℝ) (hL : 0 < L)
    (hT4 : ∀ j : Fin t, ∃ ε : ℝ, 0 < ε ∧ ∀ θ : ℝ, |θ - θstar j| < ε → L ≤ q0 θ)
    (s : ℕ) (hs : t < s)
      (K : ℝ) (hK : 0 < K) (N : Fin t → ℕ) (hN : ∀ j : Fin t, 1 ≤ N j)
      (X : ℕ → ℝ)
      (hden : ∀ (n : ℕ) (j : Fin t),
        N j ≤ paperNcard (paperSeq X n) (θstar j) c →
        K ^ ((1 : ℝ) / (t : ℝ)) * paperY t (paperSeq X n) (θstar j) c ≤
          (paperNcard (paperSeq X n) (θstar j) c : ℝ) *
            (Real.log (n : ℝ)) ^ ((1 : ℝ) / (2 * (t : ℝ))) *
            paperBlockIntegralT g q0 (paperSeq X n) (θstar j)
              (paperCblock (paperSeq X n) (θstar j) c)) :
      ∀ n : ℕ, 0 < n →
        paperInd (paperOmega N (paperSeq X n) θstar c) *
            paperSigmaCore g q0 p θstar c s (paperSeq X n) ≤
          ((2 : ℝ) ^ t * Real.sqrt (Real.log (n : ℝ)) / K) *
            paperTcore g q0 θstar c s (paperSeq X n) *
            paperInd (paperOmega N (paperSeq X n) θstar c)
:= by
  /- @proof-region region.root.07bcb8cc63f8 begin -/
  intro n hn
  have ht_ne : t ≠ 0 := by
    intro h
    subst h
    simp at hp_sum
  by_cases hΩ : paperOmega N (paperSeq X n) θstar c
  · have hΩ' : ∀ j : Fin t,
        N j ≤ paperNcard (paperSeq X n) (θstar j) c ∧
          paperY t (paperSeq X n) (θstar j) c ∈ Set.Icc (1 / 2 : ℝ) 1 := hΩ
    have hind : paperInd (paperOmega N (paperSeq X n) θstar c) = 1 := by
      simp only [paperInd]
      exact if_pos hΩ
    rw [hind, one_mul, mul_one]
    simp only [paperSigmaCore, paperTcore]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun sv _ => ?_)
    refine statopia_math_node_2993697126_ef5aa026 t n ht_ne hn K hK _ _ ?_ ?_
    · intro j
      exact (statopia_math_node_402565943_af0b7f17 t n hn (paperSeq X n) g q0 hg_nonneg
        p θstar c K hK N hN j (sv j) (ne_of_gt (hp_pos j)) (hΩ' j).1 (hΩ' j).2
        (hden n j (hΩ' j).1)).1
    · intro j
      exact (statopia_math_node_402565943_af0b7f17 t n hn (paperSeq X n) g q0 hg_nonneg
        p θstar c K hK N hN j (sv j) (ne_of_gt (hp_pos j)) (hΩ' j).1 (hΩ' j).2
        (hden n j (hΩ' j).1)).2
  · have hind : paperInd (paperOmega N (paperSeq X n) θstar c) = 0 := by
      simp only [paperInd]
      exact if_neg hΩ
    rw [hind, zero_mul, mul_zero]
  /- @proof-region region.root.07bcb8cc63f8 end -/

end Statlib.Imported

-- Paper root revision 46b92d09-0df3-4f95-b417-63c508ae06fe
