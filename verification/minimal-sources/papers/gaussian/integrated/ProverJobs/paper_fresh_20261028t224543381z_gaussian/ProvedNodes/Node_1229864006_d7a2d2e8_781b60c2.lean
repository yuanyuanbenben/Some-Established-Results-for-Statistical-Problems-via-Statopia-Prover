import ProverJobs.paper_fresh_20261028t224543381z_gaussian.Vocabulary
import ProverJobs.paper_fresh_20261028t224543381z_gaussian.Base

namespace PaperProofTasks.paper_fresh_20261028t224543381z_gaussian

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open _root_.PaperProofTasks.paper_fresh_20261028t224543381z_gaussian.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace Statlib.Imported


set_option autoImplicit false in
theorem statopia_math_node_1229864006_d7a2d2e8 : ∀ (Omega : Type) [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (p : ℕ → ℕ)
    (Sigma : (n : ℕ) → Matrix (Fin (p n)) (Fin (p n)) ℝ)
    (hSigma : ∀ n, (Sigma n).PosSemidef)
    (mu : (n : ℕ) → Fin (p n) → ℝ)
    (Z : (n : ℕ) → Fin n → Omega → Fin (p n) → ℝ)
    (hZint : ∀ (n : ℕ) (i : Fin n) (k l : Fin (p n)),
      Integrable (fun (omega : Omega) => Z n i omega k * Z n i omega l) P)
    (hZcov : ∀ (n : ℕ) (i : Fin n) (k l : Fin (p n)),
      ∫ (omega : Omega), Z n i omega k * Z n i omega l ∂P = if k = l then (1 : ℝ) else 0),
    (∀ (n : ℕ) (hn : 1 ≤ n) (j : Fin (p n)),
      Integrable (fun (omega : Omega) =>
        ((Matrix.mulVec (Matrix.PosSemidef.sqrt (hSigma n)) (Z n ⟨0, hn⟩ omega)) j) ^ 2) P ∧
      ∫ (omega : Omega),
        ((Matrix.mulVec (Matrix.PosSemidef.sqrt (hSigma n)) (Z n ⟨0, hn⟩ omega)) j) ^ 2 ∂P
        = Sigma n j j) ∧
    (∀ (n : ℕ) (hn : 1 ≤ n) (i j : Fin (p n)),
      Integrable (fun (omega : Omega) =>
        ((Matrix.mulVec (Matrix.PosSemidef.sqrt (hSigma n)) (Z n ⟨0, hn⟩ omega)) i) *
        ((Matrix.mulVec (Matrix.PosSemidef.sqrt (hSigma n)) (Z n ⟨0, hn⟩ omega)) j)) P ∧
      ∫ (omega : Omega),
        ((Matrix.mulVec (Matrix.PosSemidef.sqrt (hSigma n)) (Z n ⟨0, hn⟩ omega)) i) *
        ((Matrix.mulVec (Matrix.PosSemidef.sqrt (hSigma n)) (Z n ⟨0, hn⟩ omega)) j) ∂P
        = Sigma n i j) := by
  /- @proof-region region.target-node.session.2b93f6898b45823f begin -/
  intro Omega Omega_meas P P_prob p Sigma hSigma mu Z hZint hZcov
  have hfac : ∀ (n : ℕ), Matrix.PosSemidef.sqrt (hSigma n)
      = (↑(hSigma n).isHermitian.eigenvectorUnitary : Matrix (Fin (p n)) (Fin (p n)) ℝ)
        * Matrix.diagonal (fun i => Real.sqrt ((hSigma n).isHermitian.eigenvalues i))
        * star (↑(hSigma n).isHermitian.eigenvectorUnitary : Matrix (Fin (p n)) (Fin (p n)) ℝ) :=
    fun n => rfl
  have hsq : ∀ (n : ℕ), Matrix.PosSemidef.sqrt (hSigma n) * Matrix.PosSemidef.sqrt (hSigma n) = Sigma n := by
    intro n
    rw [hfac n]
    set U : Matrix (Fin (p n)) (Fin (p n)) ℝ :=
      (↑(hSigma n).isHermitian.eigenvectorUnitary : Matrix (Fin (p n)) (Fin (p n)) ℝ) with hUdef
    set D : Matrix (Fin (p n)) (Fin (p n)) ℝ :=
      Matrix.diagonal (fun i => Real.sqrt ((hSigma n).isHermitian.eigenvalues i)) with hDdef
    have hU : star U * U = 1 :=
      Matrix.UnitaryGroup.star_mul_self (hSigma n).isHermitian.eigenvectorUnitary
    have hDD : D * D = Matrix.diagonal (fun i => (hSigma n).isHermitian.eigenvalues i) := by
      have hD' : D = Matrix.diagonal (fun i => Real.sqrt ((hSigma n).isHermitian.eigenvalues i)) := rfl
      rw [hD', Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      exact Real.mul_self_sqrt ((hSigma n).eigenvalues_nonneg i)
    calc U * D * star U * (U * D * star U)
        = U * D * (star U * U) * D * star U := by noncomm_ring
      _ = U * D * 1 * D * star U := by rw [hU]
      _ = U * (D * D) * star U := by noncomm_ring
      _ = U * Matrix.diagonal (fun i => (hSigma n).isHermitian.eigenvalues i) * star U := by rw [hDD]
      _ = Sigma n := (Matrix.IsHermitian.spectral_theorem (hSigma n).isHermitian).symm
  have hT : ∀ (n : ℕ), (Matrix.PosSemidef.sqrt (hSigma n)).IsHermitian := by
    intro n
    have hDstar : star (Matrix.diagonal (fun i => Real.sqrt ((hSigma n).isHermitian.eigenvalues i)))
        = Matrix.diagonal (fun i => Real.sqrt ((hSigma n).isHermitian.eigenvalues i)) := by
      ext i j
      by_cases h : i = j
      · subst h
        simp [Matrix.conjTranspose_apply, Matrix.diagonal, star_trivial]
      · have h' : j ≠ i := fun hji => h hji.symm
        simp [Matrix.conjTranspose_apply, Matrix.diagonal, star_trivial, h, h']
    rw [hfac n]
    show star ((↑(hSigma n).isHermitian.eigenvectorUnitary : Matrix (Fin (p n)) (Fin (p n)) ℝ)
        * Matrix.diagonal (fun i => Real.sqrt ((hSigma n).isHermitian.eigenvalues i))
        * star (↑(hSigma n).isHermitian.eigenvectorUnitary : Matrix (Fin (p n)) (Fin (p n)) ℝ))
      = (↑(hSigma n).isHermitian.eigenvectorUnitary : Matrix (Fin (p n)) (Fin (p n)) ℝ)
        * Matrix.diagonal (fun i => Real.sqrt ((hSigma n).isHermitian.eigenvalues i))
        * star (↑(hSigma n).isHermitian.eigenvectorUnitary : Matrix (Fin (p n)) (Fin (p n)) ℝ)
    rw [star_mul, star_mul, star_star, hDstar, mul_assoc]
  have hsymm : ∀ (n : ℕ) (k j : Fin (p n)),
      (Matrix.PosSemidef.sqrt (hSigma n)) k j = (Matrix.PosSemidef.sqrt (hSigma n)) j k := by
    intro n k j
    have h2 := congrFun (congrFun (Matrix.IsHermitian.eq (hT n)) j) k
    simp only [Matrix.conjTranspose_apply, star_trivial] at h2
    exact h2
  have hSigmaSum : ∀ (n : ℕ) (i j : Fin (p n)),
      Sigma n i j
        = ∑ k, (Matrix.PosSemidef.sqrt (hSigma n)) i k * (Matrix.PosSemidef.sqrt (hSigma n)) j k := by
    intro n i j
    calc Sigma n i j
        = ((Matrix.PosSemidef.sqrt (hSigma n)) * (Matrix.PosSemidef.sqrt (hSigma n))) i j := by
          rw [hsq n]
      _ = ∑ k, (Matrix.PosSemidef.sqrt (hSigma n)) i k * (Matrix.PosSemidef.sqrt (hSigma n)) k j :=
          Matrix.mul_apply
      _ = ∑ k, (Matrix.PosSemidef.sqrt (hSigma n)) i k * (Matrix.PosSemidef.sqrt (hSigma n)) j k := by
          apply Finset.sum_congr rfl
          intro k _
          rw [hsymm n k j]
  have key : ∀ (n : ℕ) (hn : 1 ≤ n) (i j : Fin (p n)),
      Integrable (fun (ω : Omega) =>
        ((Matrix.mulVec (Matrix.PosSemidef.sqrt (hSigma n)) (Z n ⟨0, hn⟩ ω)) i) *
        ((Matrix.mulVec (Matrix.PosSemidef.sqrt (hSigma n)) (Z n ⟨0, hn⟩ ω)) j)) P ∧
      ∫ (ω : Omega),
        ((Matrix.mulVec (Matrix.PosSemidef.sqrt (hSigma n)) (Z n ⟨0, hn⟩ ω)) i) *
        ((Matrix.mulVec (Matrix.PosSemidef.sqrt (hSigma n)) (Z n ⟨0, hn⟩ ω)) j) ∂P
        = ∑ k, (Matrix.PosSemidef.sqrt (hSigma n)) i k * (Matrix.PosSemidef.sqrt (hSigma n)) j k := by
    intro n hn i j
    classical
    set A : Matrix (Fin (p n)) (Fin (p n)) ℝ := Matrix.PosSemidef.sqrt (hSigma n) with hAdef
    set v : Omega → Fin (p n) → ℝ := Z n ⟨0, hn⟩ with hvdef
    have hmv : ∀ (ω : Omega) (i : Fin (p n)), (A.mulVec (v ω)) i = ∑ k, A i k * v ω k := by
      intro ω i
      rfl
    have hprod : ∀ (ω : Omega),
        (∑ k, A i k * v ω k) * (∑ l, A j l * v ω l)
          = ∑ k, ∑ l, (A i k * A j l) * (v ω k * v ω l) := by
      intro ω
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      ring
    have hterm : ∀ (k l : Fin (p n)),
        Integrable (fun (ω : Omega) => (A i k * A j l) * (v ω k * v ω l)) P := by
      intro k l
      have hz : Integrable (fun (ω : Omega) => v ω k * v ω l) P := by
        simpa only [hvdef] using hZint n ⟨0, hn⟩ k l
      exact hz.const_mul _
    have hInnerInt : ∀ (k : Fin (p n)),
        Integrable (fun (ω : Omega) => ∑ l, (A i k * A j l) * (v ω k * v ω l)) P := by
      intro k
      exact MeasureTheory.integrable_finset_sum Finset.univ (fun l _ => hterm k l)
    have hInnerVal : ∀ (k : Fin (p n)),
        ∫ (ω : Omega), ∑ l, (A i k * A j l) * (v ω k * v ω l) ∂P = A i k * A j k := by
      intro k
      have hpt : ∀ (l : Fin (p n)),
          ∫ (ω : Omega), (A i k * A j l) * (v ω k * v ω l) ∂P
            = (A i k * A j l) * (if k = l then (1 : ℝ) else 0) := by
        intro l
        have hc : ∫ (ω : Omega), v ω k * v ω l ∂P = if k = l then (1 : ℝ) else 0 := by
          simpa only [hvdef] using hZcov n ⟨0, hn⟩ k l
        simp only [MeasureTheory.integral_const_mul, hc]
      rw [MeasureTheory.integral_finset_sum Finset.univ (fun l _ => hterm k l)]
      simp only [hpt]
      simp
    have hIntAll : Integrable (fun (ω : Omega) =>
        ∑ k, ∑ l, (A i k * A j l) * (v ω k * v ω l)) P :=
      MeasureTheory.integrable_finset_sum Finset.univ (fun k _ => hInnerInt k)
    have hValAll : ∫ (ω : Omega), ∑ k, ∑ l, (A i k * A j l) * (v ω k * v ω l) ∂P
        = ∑ k, A i k * A j k := by
      rw [MeasureTheory.integral_finset_sum Finset.univ (fun k _ => hInnerInt k)]
      exact Finset.sum_congr rfl (fun k _ => hInnerVal k)
    exact ⟨by simpa only [hmv, hprod] using hIntAll,
      by simpa only [hmv, hprod] using hValAll⟩
  constructor
  · intro n hn j
    exact ⟨by simpa only [pow_two] using (key n hn j j).1,
      by simpa only [pow_two] using (key n hn j j).2.trans (hSigmaSum n j j).symm⟩
  · intro n hn i j
    exact ⟨(key n hn i j).1, (key n hn i j).2.trans (hSigmaSum n i j).symm⟩
  /- @proof-region region.target-node.session.2b93f6898b45823f end -/

end Statlib.Imported
end

