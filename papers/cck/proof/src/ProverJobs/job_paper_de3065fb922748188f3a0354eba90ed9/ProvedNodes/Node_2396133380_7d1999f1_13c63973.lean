import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.Vocabulary
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.Base

namespace PaperProofTasks.job_paper_de3065fb922748188f3a0354eba90ed9

open _root_.PaperProofTasks.job_paper_de3065fb922748188f3a0354eba90ed9.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

set_option autoImplicit false in
theorem statopia_math_node_2396133380_7d1999f1 : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℕ) (hp : 1 ≤ p) (Y : Ω → Fin p → ℝ) (SigmaZ : Matrix (Fin p) (Fin p) ℝ)
    (hG : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ Y SigmaZ)
    (q : ℕ) (hq : 1 ≤ q) (φ : Fin q → Fin p) (hφ : Function.Injective φ),
    Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ
      (fun ω k => Y ω (φ k))
      (fun k l => ∫ ω, Y ω (φ k) * Y ω (φ l) ∂μ) := by
  /- @proof-region region.target-node.session.4ddf9000be749dfa begin -/
  intro Ω _ μ _ p hp Y SigmaZ hG q hq φ hφ
  classical
  set A : Matrix (Fin q) (Fin p) ℝ := fun k j => if j = φ k then 1 else 0 with hA
  set W : Ω → Fin q → ℝ := fun ω k => Y ω (φ k) with hW
  set M : Matrix (Fin q) (Fin q) ℝ := fun k l => ∫ ω, Y ω (φ k) * Y ω (φ l) ∂μ with hM
  have hmulVec : ∀ (y : Fin p → ℝ) (k : Fin q), (A.mulVec y) k = y (φ k) := by
    intro y k
    have h1 : (A.mulVec y) k = ∑ j, A k j * y j := rfl
    rw [h1]
    have h2 : ∀ j : Fin p, A k j * y j = (if j = φ k then y j else 0) := by
      intro j
      have hA' : A k j = (if j = φ k then (1 : ℝ) else 0) := by
        simp [hA]
      rw [hA']
      by_cases hj : j = φ k
      · simp [hj]
      · simp [hj]
    simp only [h2]
    rw [Finset.sum_eq_single (φ k)]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hWA : (fun ω => A.mulVec (Y ω)) = W := by
    funext ω k
    show (A.mulVec (Y ω)) k = W ω k
    rw [hmulVec]
  have hL0 := Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.linearImage μ Y SigmaZ hG A
  have hL : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ W (A * SigmaZ * A.transpose) := by
    rw [← hWA]
    exact hL0
  have hQF : ∀ u : Fin q → ℝ, (∑ k, ∑ l, u k * (A * SigmaZ * A.transpose) k l * u l)
      = ∑ k, ∑ l, u k * M k l * u l := by
    have hmean : ∀ (v : NNReal), ∫ x, x ∂(gaussianReal (0 : ℝ) v) = 0 := by
      intro v
      exact ProbabilityTheory.integral_id_gaussianReal
    have hsq : ∀ (v : NNReal), ∫ x, x ^ 2 ∂(gaussianReal (0 : ℝ) v) = (v : ℝ) := by
      intro v
      have hmem : MemLp (fun x : ℝ => x) 2 (gaussianReal (0 : ℝ) v) :=
        ProbabilityTheory.memLp_id_gaussianReal' (μ := (0 : ℝ)) (v := v) 2 (by simp)
      have h := ProbabilityTheory.variance_eq_sub hmem
      have hvar : Var[fun x : ℝ => x; gaussianReal (0 : ℝ) v] = (v : ℝ) :=
        ProbabilityTheory.variance_id_gaussianReal
      rw [hvar] at h
      have hz : (∫ x, (fun x : ℝ => x) x ∂(gaussianReal (0 : ℝ) v)) = 0 := hmean v
      rw [hz] at h
      simpa using h.symm
    set SigmaS : Matrix (Fin p) (Fin p) ℝ := (2⁻¹ : ℝ) • (SigmaZ + SigmaZ.transpose) with hSigmaS
    set e : Fin p → Fin p → ℝ := fun a j => if j = a then (1 : ℝ) else 0 with he
    have hS : SigmaS.PosSemidef := by
      rw [hSigmaS]
      exact hG.posSemidef_symmetrizedCovariance hp
    have hswap : ∀ u : Fin p → ℝ,
        (∑ i, ∑ j, u i * SigmaZ j i * u j) = ∑ i, ∑ j, u i * SigmaZ i j * u j := by
      intro u
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hQsym : ∀ u : Fin p → ℝ,
        (∑ i, ∑ j, u i * SigmaS i j * u j) = ∑ i, ∑ j, u i * SigmaZ i j * u j := by
      intro u
      have hstep : ∀ i : Fin p, (∑ j, u i * SigmaS i j * u j)
          = 2⁻¹ * (∑ j, u i * SigmaZ i j * u j) + 2⁻¹ * (∑ j, u i * SigmaZ j i * u j) := by
        intro i
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        simp only [hSigmaS, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
          smul_eq_mul]
        ring
      calc ∑ i, ∑ j, u i * SigmaS i j * u j
          = ∑ i, (2⁻¹ * (∑ j, u i * SigmaZ i j * u j)
              + 2⁻¹ * (∑ j, u i * SigmaZ j i * u j)) := by
            apply Finset.sum_congr rfl
            intro i _
            exact hstep i
        _ = 2⁻¹ * (∑ i, ∑ j, u i * SigmaZ i j * u j)
              + 2⁻¹ * (∑ i, ∑ j, u i * SigmaZ j i * u j) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        _ = ∑ i, ∑ j, u i * SigmaZ i j * u j := by
            rw [hswap u]
            ring
    have hGsym : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ Y SigmaS :=
      { measurable := hG.measurable
        integrable_exp := hG.integrable_exp
        mgf_eq := fun u => by rw [hG.mgf_eq u, ← hQsym u] }
    have hZ_meas : ∀ z : Fin p → ℝ, AEMeasurable (fun ω => ∑ j, z j * Y ω j) μ := by
      intro z
      have hcont : Continuous (fun y : Fin p → ℝ => ∑ j, z j * y j) := by
        have hterm : ∀ j : Fin p, Continuous (fun y : Fin p → ℝ => z j * y j) := fun j =>
          continuous_const.mul (continuous_apply j)
        exact continuous_finset_sum Finset.univ (fun j _ => hterm j)
      exact (hcont.measurable.comp hG.measurable).aemeasurable
    have hsingle : ∀ (a : Fin p) (ω : Ω), ∑ j : Fin p, e a j * Y ω j = Y ω a := by
      intro a ω
      rw [Finset.sum_eq_single a]
      · simp [he]
      · intro b _ hb
        simp [he, hb]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hdouble : ∀ (a b : Fin p) (ω : Ω),
        ∑ j : Fin p, (e a + e b) j * Y ω j = Y ω a + Y ω b := by
      intro a b ω
      have h1 : ∀ j : Fin p, (e a + e b) j * Y ω j = e a j * Y ω j + e b j * Y ω j := by
        intro j
        simp only [Pi.add_apply]
        ring
      rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_add_distrib, hsingle a ω,
        hsingle b ω]
    have hsecond : ∀ z : Fin p → ℝ,
        ∫ ω, (∑ j, z j * Y ω j)^2 ∂μ = ∑ i, ∑ j, z i * SigmaS i j * z j := by
      intro z
      have hlaw := hGsym.map_linearCombination μ Y SigmaS hS z
      have h1 : ∫ ω, (∑ j, z j * Y ω j)^2 ∂μ
          = ∫ x, x^2 ∂(Measure.map (fun ω => ∑ j, z j * Y ω j) μ) := by
        refine (MeasureTheory.integral_map (μ := μ) (φ := fun ω => ∑ j, z j * Y ω j)
          (f := fun x : ℝ => x ^ 2) (hZ_meas z) ?_).symm
        exact (continuous_id.pow 2).aestronglyMeasurable
      rw [h1, hlaw, hsq]
      rfl
    have hInt_sq : ∀ z : Fin p → ℝ, Integrable (fun ω => (∑ j, z j * Y ω j)^2) μ := by
      intro z
      have hlaw := hGsym.map_linearCombination μ Y SigmaS hS z
      have hid : MemLp id 2 (Measure.map (fun ω => ∑ j, z j * Y ω j) μ) := by
        rw [hlaw]
        exact ProbabilityTheory.memLp_id_gaussianReal' 2 (by simp)
      have hmem : MemLp (fun ω => ∑ j, z j * Y ω j) 2 μ := by
        have h2 := (MeasureTheory.memLp_map_measure_iff (μ := μ)
          (f := fun ω => ∑ j, z j * Y ω j) (g := id) (p := 2)
          continuous_id.aestronglyMeasurable (hZ_meas z)).mp hid
        simpa using h2
      simpa using hmem.integrable_sq
    have hcollapse2 : ∀ (B : Matrix (Fin p) (Fin p) ℝ) (a b : Fin p),
        (∑ i, ∑ j, e a i * B i j * e b j) = B a b := by
      intro B a b
      rw [Finset.sum_eq_single a]
      · rw [Finset.sum_eq_single b]
        · simp [he]
        · intro j _ hj
          simp [he, hj]
        · intro h
          exact absurd (Finset.mem_univ _) h
      · intro i _ hi
        simp [he, hi]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hSsymm : ∀ i j : Fin p, SigmaS i j = SigmaS j i := by
      intro i j
      simp only [hSigmaS, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
        smul_eq_mul]
      ring
    have hsecond_single : ∀ a : Fin p, ∫ ω, (Y ω a)^2 ∂μ = SigmaS a a := by
      intro a
      have h := hsecond (e a)
      rw [hcollapse2 SigmaS a a] at h
      simpa only [hsingle] using h
    have hInt_single : ∀ a : Fin p, Integrable (fun ω => (Y ω a)^2) μ := by
      intro a
      simpa only [hsingle] using hInt_sq (e a)
    have hQFdouble : ∀ a b : Fin p,
        (∑ i, ∑ j, (e a + e b) i * SigmaS i j * (e a + e b) j)
          = SigmaS a a + 2 * SigmaS a b + SigmaS b b := by
      intro a b
      have hpt : ∀ (i j : Fin p), (e a + e b) i * SigmaS i j * (e a + e b) j
          = (e a i * SigmaS i j * e a j + e a i * SigmaS i j * e b j
            + e b i * SigmaS i j * e a j + e b i * SigmaS i j * e b j) := by
        intro i j
        simp only [Pi.add_apply]
        ring
      have hsplit : (∑ i, ∑ j, (e a i * SigmaS i j * e a j + e a i * SigmaS i j * e b j
            + e b i * SigmaS i j * e a j + e b i * SigmaS i j * e b j))
          = (∑ i, ∑ j, e a i * SigmaS i j * e a j)
            + (∑ i, ∑ j, e a i * SigmaS i j * e b j)
            + (∑ i, ∑ j, e b i * SigmaS i j * e a j)
            + (∑ i, ∑ j, e b i * SigmaS i j * e b j) := by
        simp only [Finset.sum_add_distrib]
        try ring
      rw [show (∑ i, ∑ j, (e a + e b) i * SigmaS i j * (e a + e b) j)
          = ∑ i, ∑ j, (e a i * SigmaS i j * e a j + e a i * SigmaS i j * e b j
            + e b i * SigmaS i j * e a j + e b i * SigmaS i j * e b j) from by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact hpt i j]
      rw [hsplit, hcollapse2 SigmaS a a, hcollapse2 SigmaS a b, hcollapse2 SigmaS b a,
        hcollapse2 SigmaS b b, hSsymm a b]
      ring
    have hsecond_pair : ∀ a b : Fin p,
        ∫ ω, (Y ω a + Y ω b)^2 ∂μ = SigmaS a a + 2 * SigmaS a b + SigmaS b b := by
      intro a b
      have h := hsecond (e a + e b)
      rw [hQFdouble a b] at h
      simpa only [hdouble] using h
    have hInt_pair : ∀ a b : Fin p, Integrable (fun ω => (Y ω a + Y ω b)^2) μ := by
      intro a b
      simpa only [hdouble] using hInt_sq (e a + e b)
    have hmom : ∀ a b : Fin p, ∫ ω, Y ω a * Y ω b ∂μ = SigmaS a b := by
      intro a b
      have hsa := hsecond_single a
      have hsb := hsecond_single b
      have hsp := hsecond_pair a b
      have hIa := hInt_single a
      have hIb := hInt_single b
      have hIp := hInt_pair a b
      have hpt : ∀ ω : Ω, (Y ω a + Y ω b)^2 - ((Y ω a)^2 + (Y ω b)^2)
          = 2 * (Y ω a * Y ω b) := by
        intro ω
        ring
      have hfun : (fun ω => 2 * (Y ω a * Y ω b))
          = (fun ω => (Y ω a + Y ω b)^2 - ((Y ω a)^2 + (Y ω b)^2)) := by
        funext ω
        exact (hpt ω).symm
      have hgsum : Integrable (fun ω => (Y ω a)^2 + (Y ω b)^2) μ := hIa.add hIb
      have hstep1 : ∫ ω, ((Y ω a + Y ω b)^2 - ((Y ω a)^2 + (Y ω b)^2)) ∂μ
          = ∫ ω, (Y ω a + Y ω b)^2 ∂μ - ∫ ω, ((Y ω a)^2 + (Y ω b)^2) ∂μ :=
        integral_sub hIp hgsum
      have hstep2 : ∫ ω, ((Y ω a)^2 + (Y ω b)^2) ∂μ
          = ∫ ω, (Y ω a)^2 ∂μ + ∫ ω, (Y ω b)^2 ∂μ :=
        integral_add hIa hIb
      have hkey : ∫ ω, 2 * (Y ω a * Y ω b) ∂μ
          = ∫ ω, (Y ω a + Y ω b)^2 ∂μ
            - (∫ ω, (Y ω a)^2 ∂μ + ∫ ω, (Y ω b)^2 ∂μ) := by
        rw [hfun, hstep1, hstep2]
      rw [hsp, hsa, hsb, integral_const_mul] at hkey
      linarith
    have hanti : ∀ (B : Fin q → Fin q → ℝ), (∀ k l, B k l = - B l k) →
        ∀ u : Fin q → ℝ, (∑ k, ∑ l, u k * B k l * u l) = 0 := by
      intro B hB u
      have h1 : (∑ k, ∑ l, u k * B k l * u l) = -(∑ k, ∑ l, u k * B k l * u l) := by
        calc (∑ k, ∑ l, u k * B k l * u l)
            = ∑ k, ∑ l, -(u k * B k l * u l) := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro a _
              apply Finset.sum_congr rfl
              intro b _
              rw [hB b a]
              ring
          _ = -(∑ k, ∑ l, u k * B k l * u l) := by
              simp only [Finset.sum_neg_distrib]
      linarith
    have hantiS : ∀ k l : Fin q, SigmaZ (φ k) (φ l) - SigmaS (φ k) (φ l)
        = -(SigmaZ (φ l) (φ k) - SigmaS (φ l) (φ k)) := by
      intro k l
      have h1 : SigmaS (φ k) (φ l)
          = 2⁻¹ * (SigmaZ (φ k) (φ l) + SigmaZ (φ l) (φ k)) := by
        simp only [hSigmaS, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
          smul_eq_mul]
      have h2 : SigmaS (φ l) (φ k)
          = 2⁻¹ * (SigmaZ (φ l) (φ k) + SigmaZ (φ k) (φ l)) := by
        simp only [hSigmaS, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
          smul_eq_mul]
      rw [h1, h2]
      ring
    have heq : ∀ u : Fin q → ℝ, (∑ k, ∑ l, u k * SigmaZ (φ k) (φ l) * u l)
        = ∑ k, ∑ l, u k * SigmaS (φ k) (φ l) * u l := by
      intro u
      have hzero : (∑ k, ∑ l, u k * (SigmaZ (φ k) (φ l) - SigmaS (φ k) (φ l)) * u l) = 0 :=
        hanti (fun k l => SigmaZ (φ k) (φ l) - SigmaS (φ k) (φ l)) hantiS u
      have hsplit : (∑ k, ∑ l, u k * (SigmaZ (φ k) (φ l) - SigmaS (φ k) (φ l)) * u l)
          = (∑ k, ∑ l, u k * SigmaZ (φ k) (φ l) * u l)
            - (∑ k, ∑ l, u k * SigmaS (φ k) (φ l) * u l) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k _
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro l _
        ring
      linarith
    have hAentry : ∀ k l : Fin q, (A * SigmaZ * A.transpose) k l = SigmaZ (φ k) (φ l) := by
      intro k l
      have h1 : (A * SigmaZ * A.transpose) k l
          = ∑ i, (∑ j, A k j * SigmaZ j i) * A l i := rfl
      rw [h1]
      have h2 : ∀ i : Fin p, (∑ j, A k j * SigmaZ j i) = SigmaZ (φ k) i := by
        intro i
        have hh := hmulVec (fun j => SigmaZ j i) k
        rwa [show (A.mulVec (fun j => SigmaZ j i)) k = ∑ j, A k j * SigmaZ j i from rfl] at hh
      simp only [h2]
      rw [Finset.sum_eq_single (φ l)]
      · simp [hA]
      · intro b _ hb
        simp [hA, hb]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hMS : ∀ k l : Fin q, M k l = SigmaS (φ k) (φ l) := by
      intro k l
      simp only [hM, hmom]
    intro u
    calc ∑ k, ∑ l, u k * (A * SigmaZ * A.transpose) k l * u l
        = ∑ k, ∑ l, u k * SigmaZ (φ k) (φ l) * u l := by simp only [hAentry]
      _ = ∑ k, ∑ l, u k * SigmaS (φ k) (φ l) * u l := heq u
      _ = ∑ k, ∑ l, u k * M k l * u l := by simp only [hMS]
  refine ⟨hL.measurable, hL.integrable_exp, ?_⟩
  intro u
  rw [hL.mgf_eq u, hQF u]
  /- @proof-region region.target-node.session.4ddf9000be749dfa end -/

end Statlib.Imported

