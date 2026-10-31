import ProverJobs.job_paper_f4f73a8b20b648f5b0c28430901a09f4.Vocabulary
import ProverJobs.job_paper_f4f73a8b20b648f5b0c28430901a09f4.Base
import ProverJobs.job_paper_f4f73a8b20b648f5b0c28430901a09f4.ProvedNodes.Node_1172546344_62d35ca0_2626b73b
import ProverJobs.job_paper_f4f73a8b20b648f5b0c28430901a09f4.ProvedNodes.Node_2508078247_c99def20_3f1caded


open MeasureTheory
open scoped BigOperators
open Classical
open Statlib.Imported

open MeasureTheory
open scoped BigOperators
open Classical
noncomputable section
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_402565943_af0b7f17 : ∀ (t n : ℕ) (hn : 0 < n) (X : Fin n → ℝ) (g q0 : ℝ → ℝ)
    (hg_nonneg : ∀ x : ℝ, 0 ≤ g x)
    (p θstar : Fin t → ℝ) (c K : ℝ) (hK : 0 < K)
    (N : Fin t → ℕ) (hN : ∀ j : Fin t, 1 ≤ N j)
    (j : Fin t) (sj : ℕ)
    (hpj : p j ≠ 0)
    (hNj : N j ≤ paperNcard X (θstar j) c)
    (hY : paperY t X (θstar j) c ∈ Set.Icc (1 / 2 : ℝ) 1)
    (hden :
      K ^ ((1 : ℝ) / (t : ℝ)) * paperY t X (θstar j) c ≤
        (paperNcard X (θstar j) c : ℝ) *
          (Real.log (n : ℝ)) ^ ((1 : ℝ) / (2 * (t : ℝ))) *
          paperBlockIntegralT g q0 X (θstar j) (paperCblock X (θstar j) c)),
    0 ≤ paperGroupSigma g q0 X p θstar c j sj ∧
      paperGroupSigma g q0 X p θstar c j sj ≤
        (2 * (Real.log (n : ℝ)) ^ ((1 : ℝ) / (2 * (t : ℝ))) /
            K ^ ((1 : ℝ) / (t : ℝ))) *
          paperGroupT g q0 X θstar c j sj := by
  /- @proof-region region.target-node.session.c4b9563c7fe57bc8 begin -/
  intro t n hn X g q0 hg_nonneg p θstar c K hK N hN j sj hpj hNj hY hden
  have hrecip :=
    statopia_math_node_2508078247_c99def20 t n hn X g q0 (θstar j) c K hK (N j) (hN j) hNj hY
      hden
  obtain ⟨hJpos, hJinv⟩ := hrecip
  have hTnn : ∀ A : Finset (Fin n), 0 ≤ paperBlockIntegralT g q0 X (θstar j) A := by
    intro A
    unfold paperBlockIntegralT paperTIntegrand
    exact integral_nonneg
      (fun θ => Finset.prod_nonneg (fun i _ => div_nonneg (hg_nonneg _) (hg_nonneg _)))
  have hWnn : ∀ P : Finset (Finset (Fin n)),
      0 ≤ paperPartWeight (paperNcard X (θstar j) c) P := by
    intro P
    unfold paperPartWeight
    exact div_nonneg (Finset.prod_nonneg (fun A _ => by positivity)) (by positivity)
  have hNP : ∀ P ∈ paperTau (paperCblock X (θstar j) c) sj,
      0 ≤ paperPartWeight (paperNcard X (θstar j) c) P *
        (∏ A ∈ P, paperBlockIntegralT g q0 X (θstar j) A) :=
    fun P _ => mul_nonneg (hWnn P) (Finset.prod_nonneg (fun A _ => hTnn A))
  have hsig :
      paperGroupSigma g q0 X p θstar c j sj
        = ∑ P ∈ paperTau (paperCblock X (θstar j) c) sj,
            (paperPartWeight (paperNcard X (θstar j) c) P *
              (∏ A ∈ P, paperBlockIntegralT g q0 X (θstar j) A)) *
            (paperBlockIntegralT g q0 X (θstar j) (paperCblock X (θstar j) c))⁻¹ := by
    unfold paperGroupSigma
    exact Finset.sum_congr rfl (fun P hP =>
      statopia_math_node_1172546344_62d35ca0 n X g q0 (p j) hpj (θstar j)
        (paperCblock X (θstar j) c) sj P hP)
  constructor
  · rw [hsig]
    exact Finset.sum_nonneg (fun P hP => mul_nonneg (hNP P hP) (inv_nonneg.mpr hJpos.le))
  · rw [hsig]
    have hkey : ∀ P ∈ paperTau (paperCblock X (θstar j) c) sj,
        (paperPartWeight (paperNcard X (θstar j) c) P *
            (∏ A ∈ P, paperBlockIntegralT g q0 X (θstar j) A)) *
            (paperBlockIntegralT g q0 X (θstar j) (paperCblock X (θstar j) c))⁻¹ ≤
          (2 * (Real.log (n : ℝ)) ^ ((1 : ℝ) / (2 * (t : ℝ))) /
              K ^ ((1 : ℝ) / (t : ℝ))) *
            ((paperNcard X (θstar j) c : ℝ) *
              (paperPartWeight (paperNcard X (θstar j) c) P *
                (∏ A ∈ P, paperBlockIntegralT g q0 X (θstar j) A))) := by
      intro P hP
      refine le_trans (mul_le_mul_of_nonneg_left hJinv (hNP P hP)) (le_of_eq ?_)
      ring
    calc
      ∑ P ∈ paperTau (paperCblock X (θstar j) c) sj,
          (paperPartWeight (paperNcard X (θstar j) c) P *
              (∏ A ∈ P, paperBlockIntegralT g q0 X (θstar j) A)) *
            (paperBlockIntegralT g q0 X (θstar j) (paperCblock X (θstar j) c))⁻¹ ≤
          ∑ P ∈ paperTau (paperCblock X (θstar j) c) sj,
            (2 * (Real.log (n : ℝ)) ^ ((1 : ℝ) / (2 * (t : ℝ))) /
                K ^ ((1 : ℝ) / (t : ℝ))) *
              ((paperNcard X (θstar j) c : ℝ) *
                (paperPartWeight (paperNcard X (θstar j) c) P *
                  (∏ A ∈ P, paperBlockIntegralT g q0 X (θstar j) A))) :=
        Finset.sum_le_sum hkey
      _ = (2 * (Real.log (n : ℝ)) ^ ((1 : ℝ) / (2 * (t : ℝ))) /
              K ^ ((1 : ℝ) / (t : ℝ))) *
            ∑ P ∈ paperTau (paperCblock X (θstar j) c) sj,
              (paperNcard X (θstar j) c : ℝ) *
                (paperPartWeight (paperNcard X (θstar j) c) P *
                  (∏ A ∈ P, paperBlockIntegralT g q0 X (θstar j) A)) := by
        simp only [Finset.mul_sum]
      _ = (2 * (Real.log (n : ℝ)) ^ ((1 : ℝ) / (2 * (t : ℝ))) /
              K ^ ((1 : ℝ) / (t : ℝ))) *
            paperGroupT g q0 X θstar c j sj := by
        congr 1
        unfold paperGroupT
        refine Finset.sum_congr rfl (fun P hP => ?_)
        ring
  /- @proof-region region.target-node.session.c4b9563c7fe57bc8 end -/

end Statlib.Imported
end
