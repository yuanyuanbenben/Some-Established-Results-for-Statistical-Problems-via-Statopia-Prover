import Statlib.HighDim.MatrixAnalysis.AndoVocabulary
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Vocabulary
import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Base

namespace PaperProofTasks.job_paper_cb04ce35a04d48a9bf96750470ca0eb0

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
open _root_.PaperProofTasks.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Statlib.Imported

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
namespace Statlib.Imported

noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_3046040406_9e149626 : ∀ (pn d : ℕ) (hpn : 1 ≤ pn) (hd1 : 1 ≤ d) (hdle : d ≤ pn)
    (Sigma : Matrix (Fin pn) (Fin pn) ℝ) (hSigma : Sigma.PosSemidef)
    (taun : ℝ) (t : ℝ) (pin : Equiv.Perm (Fin pn)),
    (Measure.map
        (fun z : Fin pn → ℝ =>
          sSup ((((Finset.univ.filter (fun i : Fin pn => i.1 < d)).image pin).image
            (fun j : Fin pn =>
              (Matrix.PosSemidef.sqrt hSigma).mulVec z j /
                Real.rpow (Real.sqrt (Sigma j j)) taun)) : Set ℝ))
        (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi pn)) (Set.Iic t)
      = (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi pn)
          {z : Fin pn → ℝ | ∀ j : Fin pn, ((pin.symm j : Fin pn) : ℕ) < d →
            Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Sigma z j /
              Real.rpow (Real.sqrt (Sigma j j)) taun ≤ t} := by
  /- @proof-region region.target-node.session.b3cc00bdfcb5ebf6 begin -/
  intro pn d hpn hd1 hdle Sigma hSigma taun t pin
  let P : Measure (Fin pn → ℝ) := Statlib.StatFoundation.RandomVariable.Gaussian.standardPi pn
  let A : Matrix (Fin pn) (Fin pn) ℝ := Matrix.PosSemidef.sqrt hSigma
  let J : Finset (Fin pn) := (Finset.univ.filter (fun i : Fin pn => i.1 < d)).image (fun i => pin i)
  let c : Fin pn → ℝ := fun j => Real.rpow (Real.sqrt (Sigma j j)) taun
  let M : (Fin pn → ℝ) → ℝ := fun v => sSup ((J.image (fun j => v j / c j)) : Set ℝ)
  haveI hprobP : IsProbabilityMeasure P :=
    Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.standardPi_probability pn
  haveI hprobS : IsProbabilityMeasure
      (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi pn) :=
    Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.standardPi_probability pn
  change (Measure.map (fun z : Fin pn → ℝ => M (A.mulVec z)) P) (Set.Iic t)
      = P {z : Fin pn → ℝ | ∀ j : Fin pn, ((pin.symm j : Fin pn) : ℕ) < d →
          Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Sigma z j / c j ≤ t}
  let U : Matrix (Fin pn) (Fin pn) ℝ := ↑hSigma.1.eigenvectorUnitary
  let dsq : Fin pn → ℝ := RCLike.ofReal ∘ (fun x : ℝ => √x) ∘ hSigma.1.eigenvalues
  let Dsq : Matrix (Fin pn) (Fin pn) ℝ := Matrix.diagonal dsq
  have hdsq : ∀ j : Fin pn, dsq j = RCLike.ofReal (√(hSigma.1.eigenvalues j)) := fun j => rfl
  have hU1 : star U * U = 1 := Matrix.UnitaryGroup.star_mul_self hSigma.1.eigenvectorUnitary
  have hspecS : Sigma = U * Matrix.diagonal (RCLike.ofReal ∘ hSigma.1.eigenvalues) * star U := by
    refine (Matrix.IsHermitian.spectral_theorem hSigma.1).trans ?_
    show ((Unitary.conjStarAlgAut ℝ (Matrix (Fin pn) (Fin pn) ℝ)) hSigma.1.eigenvectorUnitary)
        (Matrix.diagonal (RCLike.ofReal ∘ hSigma.1.eigenvalues)) =
      (↑hSigma.1.eigenvectorUnitary : Matrix (Fin pn) (Fin pn) ℝ) *
        Matrix.diagonal (RCLike.ofReal ∘ hSigma.1.eigenvalues) *
        star (↑hSigma.1.eigenvectorUnitary : Matrix (Fin pn) (Fin pn) ℝ)
    rw [Unitary.conjStarAlgAut_apply]
  have hDmom : Dsq * Dsq = Matrix.diagonal (RCLike.ofReal ∘ hSigma.1.eigenvalues) := by
    show Matrix.diagonal dsq * Matrix.diagonal dsq =
      Matrix.diagonal (RCLike.ofReal ∘ hSigma.1.eigenvalues)
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    have hl : 0 ≤ hSigma.1.eigenvalues i := Matrix.PosSemidef.eigenvalues_nonneg hSigma i
    show dsq i * dsq i = RCLike.ofReal (hSigma.1.eigenvalues i)
    simp [hdsq, Real.mul_self_sqrt hl]
  have hSD : (star U).transpose = U := by
    show (star (↑hSigma.1.eigenvectorUnitary : Matrix (Fin pn) (Fin pn) ℝ)).transpose
      = ↑hSigma.1.eigenvectorUnitary
    ext i j
    simp
  have hUS : U.transpose = star U := by
    show (↑hSigma.1.eigenvectorUnitary : Matrix (Fin pn) (Fin pn) ℝ).transpose
      = star ↑hSigma.1.eigenvectorUnitary
    ext i j
    simp
  have hDtt : Dsq.transpose = Dsq := by
    show (Matrix.diagonal dsq).transpose = Matrix.diagonal dsq
    exact Matrix.diagonal_transpose dsq
  have hAAt : A * A.transpose = Sigma := by
    have hAform : A = U * Dsq * star U := by
      show Matrix.PosSemidef.sqrt hSigma = U * Dsq * star U
      unfold Matrix.PosSemidef.sqrt
      rfl
    have hsym : (U * Dsq * star U).transpose = U * Dsq * star U := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, hDtt, hSD, hUS]
      noncomm_ring
    rw [hAform, hsym]
    calc (U * Dsq * star U) * (U * Dsq * star U)
        = U * Dsq * (star U * U) * Dsq * star U := by noncomm_ring
      _ = U * Dsq * 1 * Dsq * star U := by rw [hU1]
      _ = U * (Dsq * Dsq) * star U := by noncomm_ring
      _ = U * Matrix.diagonal (RCLike.ofReal ∘ hSigma.1.eigenvalues) * star U := by rw [hDmom]
      _ = Sigma := hspecS.symm
  have htr : Sigma.transpose = Sigma := by
    ext i j
    have h := congrFun (congrFun hSigma.1 i) j
    simpa using h
  have hsymm : (2⁻¹ : ℝ) • (Sigma + Sigma.transpose) = Sigma := by
    rw [htr]
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    ring
  have hmem0 : (⟨0, by omega⟩ : Fin pn) ∈ Finset.univ.filter (fun i : Fin pn => i.1 < d) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simpa using hd1
  have hJne : J.Nonempty := by
    refine ⟨pin ⟨0, by omega⟩, ?_⟩
    show pin ⟨0, by omega⟩ ∈ (Finset.univ.filter (fun i : Fin pn => i.1 < d)).image (fun i => pin i)
    exact Finset.mem_image.mpr ⟨_, hmem0, rfl⟩
  have hJiff : ∀ j : Fin pn, j ∈ J ↔ ((pin.symm j : Fin pn) : ℕ) < d := by
    intro j
    show j ∈ (Finset.univ.filter (fun i : Fin pn => i.1 < d)).image (fun i => pin i) ↔ _
    constructor
    · intro hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simpa using hi
    · intro hj
      refine Finset.mem_image.mpr ⟨pin.symm j, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa using hj
  have hspec : ∀ (v : Fin pn → ℝ) (s : ℝ), M v ≤ s ↔ ∀ j ∈ J, v j / c j ≤ s := by
    intro v s
    have hbdd : BddAbove ((J.image (fun j => v j / c j)) : Set ℝ) := Finset.bddAbove _
    have hne : ((J.image (fun j => v j / c j)) : Set ℝ).Nonempty := by
      obtain ⟨j0, hj0⟩ := hJne
      exact ⟨v j0 / c j0, Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨j0, hj0, rfl⟩)⟩
    constructor
    · intro h j hj
      have hmem : v j / c j ∈ ((J.image (fun j => v j / c j)) : Set ℝ) :=
        Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
      exact le_trans (le_csSup hbdd hmem) h
    · intro h
      exact csSup_le hne (fun b hb => by
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hb)
        exact h j hj)
  have hMmeas : Measurable M := by
    apply measurable_of_Iic
    intro s
    change MeasurableSet {v : Fin pn → ℝ | M v ≤ s}
    have hset : {v : Fin pn → ℝ | M v ≤ s} = ⋂ j ∈ J, {v : Fin pn → ℝ | v j / c j ≤ s} := by
      ext v
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      exact hspec v s
    rw [hset]
    refine Finset.measurableSet_biInter
      (f := fun j : Fin pn => {v : Fin pn → ℝ | v j / c j ≤ s}) J (fun j _ => ?_)
    have hv : Measurable (fun v : Fin pn → ℝ => v j) := measurable_pi_apply j
    have hj : Measurable (fun v : Fin pn → ℝ => v j / c j) := hv.div_const (c j)
    show MeasurableSet {v : Fin pn → ℝ | v j / c j ≤ s}
    rw [show {v : Fin pn → ℝ | v j / c j ≤ s}
        = (fun v : Fin pn → ℝ => v j / c j) ⁻¹' Set.Iic s from by
      ext v
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq]]
    exact hj measurableSet_Iic
  have hAmeas : Measurable (fun z : Fin pn → ℝ => A.mulVec z) := by
    refine measurable_pi_iff.mpr (fun j => ?_)
    have hcoord : (fun z : Fin pn → ℝ => A.mulVec z j) = (fun z : Fin pn → ℝ => ∑ i, A j i * z i) := by
      funext z
      simp [Matrix.mulVec, dotProduct]
    rw [hcoord]
    exact Finset.measurable_sum Finset.univ (fun i _ => measurable_const.mul (measurable_pi_apply i))
  have hcGVmeas : Measurable (fun z : Fin pn → ℝ =>
      Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Sigma z) := by
    refine measurable_pi_iff.mpr (fun j => ?_)
    have hlin : (fun z : Fin pn → ℝ =>
        Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Sigma z j)
        = (fun z : Fin pn → ℝ =>
            ∑ i, (CFC.sqrt Sigma).mulVec (fun k : Fin pn => if k = j then (1:ℝ) else 0) i * z i) := by
      funext z
      have h := Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector_linearCombination
        Sigma hSigma (fun k : Fin pn => if k = j then (1:ℝ) else 0) z
      simpa using h
    rw [hlin]
    exact Finset.measurable_sum Finset.univ (fun i _ => measurable_const.mul (measurable_pi_apply i))
  have hId : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector P
      (fun z : Fin pn → ℝ => z) (1 : Matrix (Fin pn) (Fin pn) ℝ) := by
    have h1 := Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector_isCenteredGaussianVector
      (m := pn) (by omega) (1 : Matrix (Fin pn) (Fin pn) ℝ) Matrix.PosSemidef.one
    rwa [Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.identity_canonicalGaussianVector] at h1
  have hXcov : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector P
      (fun z : Fin pn → ℝ => A.mulVec z) Sigma := by
    have h := Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.linearImage P
      (fun z : Fin pn → ℝ => z) (1 : Matrix (Fin pn) (Fin pn) ℝ) hId A
    rw [mul_one, hAAt] at h
    exact h
  have hlaw : Measure.map (fun z : Fin pn → ℝ => A.mulVec z) P
      = Measure.map (fun z : Fin pn → ℝ =>
          Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Sigma z) P := by
    have hX := Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.map_eq_canonicalGaussianVector
      hXcov hpn
    have hY := Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.map_eq_canonicalGaussianVector
      (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector_isCenteredGaussianVector
        (m := pn) (by omega) Sigma hSigma) hpn
    rw [hsymm] at hX hY
    exact hX.trans hY.symm
  have hpush : Measure.map (fun z : Fin pn → ℝ => M (A.mulVec z)) P
      = Measure.map (fun z : Fin pn → ℝ =>
          M (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Sigma z)) P := by
    calc Measure.map (fun z : Fin pn → ℝ => M (A.mulVec z)) P
        = Measure.map M (Measure.map (fun z : Fin pn → ℝ => A.mulVec z) P) :=
          (Measure.map_map hMmeas hAmeas).symm
      _ = Measure.map M (Measure.map (fun z : Fin pn → ℝ =>
            Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Sigma z) P) := by
          rw [hlaw]
      _ = Measure.map (fun z : Fin pn → ℝ =>
            M (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Sigma z)) P :=
          Measure.map_map hMmeas hcGVmeas
  have hset : {z : Fin pn → ℝ |
        M (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Sigma z) ≤ t}
      = {z : Fin pn → ℝ | ∀ j : Fin pn, ((pin.symm j : Fin pn) : ℕ) < d →
          Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Sigma z j / c j ≤ t} := by
    ext z
    simp only [Set.mem_setOf_eq]
    rw [hspec]
    constructor
    · intro h j hj
      exact h j ((hJiff j).mpr hj)
    · intro h j hj
      exact h j ((hJiff j).mp hj)
  calc (Measure.map (fun z : Fin pn → ℝ => M (A.mulVec z)) P) (Set.Iic t)
      = (Measure.map (fun z : Fin pn → ℝ =>
          M (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Sigma z)) P)
          (Set.Iic t) := by rw [hpush]
    _ = P {z : Fin pn → ℝ |
          M (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Sigma z) ≤ t} := by
        have hcomp : Measurable (fun z : Fin pn → ℝ =>
            M (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Sigma z)) :=
          hMmeas.comp hcGVmeas
        rw [Measure.map_apply hcomp measurableSet_Iic]
        have hpre : (fun z : Fin pn → ℝ =>
            M (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Sigma z)) ⁻¹' Set.Iic t
            = {z : Fin pn → ℝ | M (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Sigma z) ≤ t} := by
          ext z
          simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq]
        rw [hpre]
    _ = P {z : Fin pn → ℝ | ∀ j : Fin pn, ((pin.symm j : Fin pn) : ℕ) < d →
          Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Sigma z j / c j ≤ t} := by
        rw [hset]
  /- @proof-region region.target-node.session.b3cc00bdfcb5ebf6 end -/

end

end Statlib.Imported

