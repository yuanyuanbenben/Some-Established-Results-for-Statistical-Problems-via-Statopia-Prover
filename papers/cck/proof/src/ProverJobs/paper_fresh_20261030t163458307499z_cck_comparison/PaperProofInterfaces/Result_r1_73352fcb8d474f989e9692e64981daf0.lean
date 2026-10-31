import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.Vocabulary
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.ProvedNodes
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.Base

namespace PaperProofTasks.job_paper_ea9c51e8f7d246ef967b6629540eeb01

namespace Statlib.Imported

open MeasureTheory ProbabilityTheory

theorem paper_ea9c51e8f7d246ef967b6629540eeb01
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℕ) (hp : 0 < p)
    (X Y : Ω → Fin p → ℝ)
    (SigmaX SigmaY : Matrix (Fin p) (Fin p) ℝ)
    (hX : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ X SigmaX)
    (hY : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ Y SigmaY)
    (β : ℝ) (hβ : 0 < β)
    (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g)
    (hg1 : BddAbove (Set.range fun z : ℝ => |deriv g z|))
    (hg2 : BddAbove (Set.range fun z : ℝ => |deriv (deriv g) z|)) :
      |expSmoothMaxDiff μ X Y β g| ≤
          (supNormR (deriv (deriv g)) / 2 + β * supNormR (deriv g)) * covDiffMax μ X Y ∧
        |expMaxCoordDiff μ X Y g| ≤
          (supNormR (deriv (deriv g)) / 2 + β * supNormR (deriv g)) * covDiffMax μ X Y
            + 2 * β⁻¹ * supNormR (deriv g) * Real.log (p : ℝ)
:= by
  /- @proof-region region.root.7950b4d8e02c begin -/
  classical
  haveI : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  obtain ⟨Ω', hmΩ', μ', hprob, hrest⟩ :=
    statopia_math_node_2966747390_db21bd2d μ p hp X Y SigmaX SigmaY hX hY β hβ g hg hg1
  obtain ⟨X', Y', hX'meas, hY'meas, hrest⟩ := hrest
  obtain ⟨⟨SigmaS, hW⟩, hrest⟩ := hrest
  obtain ⟨hmomX, hrest⟩ := hrest
  obtain ⟨hmomY, hrest⟩ := hrest
  obtain ⟨hmomXY, hrest⟩ := hrest
  obtain ⟨hintgX, hrest⟩ := hrest
  obtain ⟨hintgY, hrest⟩ := hrest
  obtain ⟨hintgX', hrest⟩ := hrest
  obtain ⟨hintgY', hEq⟩ := hrest
  have hXmeas : ∀ j : Fin p, Measurable fun ω => X ω j :=
    fun j => measurable_pi_iff.mp hX.measurable j
  have hYmeas : ∀ j : Fin p, Measurable fun ω => Y ω j :=
    fun j => measurable_pi_iff.mp hY.measurable j
  have hg1' : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hXint : ∀ j : Fin p, Integrable (fun ω => X ω j) μ := by
    intro j
    have hsq : Integrable (fun ω => X ω j * X ω j) μ :=
      (statopia_math_node_2606212885_28c76b68 μ p hp X SigmaX hX j j).1
    have hbd : Integrable (fun ω => (X ω j * X ω j + 1) * (1 / 2)) μ :=
      (hsq.add (MeasureTheory.integrable_const (1 : ℝ))).mul_const (1 / 2)
    refine MeasureTheory.Integrable.mono' hbd (hXmeas j).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    nlinarith [sq_abs (X ω j), abs_nonneg (X ω j), sq_nonneg (|X ω j| - 1)]
  have hYint : ∀ j : Fin p, Integrable (fun ω => Y ω j) μ := by
    intro j
    have hsq : Integrable (fun ω => Y ω j * Y ω j) μ :=
      (statopia_math_node_2606212885_28c76b68 μ p hp Y SigmaY hY j j).1
    have hbd : Integrable (fun ω => (Y ω j * Y ω j + 1) * (1 / 2)) μ :=
      (hsq.add (MeasureTheory.integrable_const (1 : ℝ))).mul_const (1 / 2)
    refine MeasureTheory.Integrable.mono' hbd (hYmeas j).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    nlinarith [sq_abs (Y ω j), abs_nonneg (Y ω j), sq_nonneg (|Y ω j| - 1)]
  have hmain1 : |expSmoothMaxDiff μ X Y β g| ≤
      (supNormR (deriv (deriv g)) / 2 + β * supNormR (deriv g)) * covDiffMax μ X Y := by
    haveI : Nonempty (Fin p × Fin p) := ⟨(⟨0, hp⟩, ⟨0, hp⟩)⟩
    set M : Matrix (Fin p) (Fin p) ℝ :=
      Matrix.of (fun i j => SigmaS (Fin.castAdd p i) (Fin.castAdd p j)) with hMdef
    set N : Matrix (Fin p) (Fin p) ℝ :=
      Matrix.of (fun i j => SigmaS (Fin.natAdd p i) (Fin.natAdd p j)) with hNdef
    set SX : Matrix (Fin p) (Fin p) ℝ := (2 : ℝ)⁻¹ • (M + M.transpose) with hSXdef
    set SY : Matrix (Fin p) (Fin p) ℝ := (2 : ℝ)⁻¹ • (N + N.transpose) with hSYdef
    set W : Ω' → Fin (p + p) → ℝ := fun ω' i => Fin.append (X' ω') (Y' ω') i with hWdef
    have hXm : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ' X' SX := by
      have h := statopia_math_node_3324226015_e4d8bb5d μ' p p W SigmaS hW
      have hfun : (fun ω' (i : Fin p) => W ω' (Fin.castAdd p i)) = X' := by
        funext ω' i
        simp [W, Fin.append_left]
      rw [hfun] at h
      simpa only [hSXdef, hMdef] using h
    have hSXs : SX = SX.transpose := by
      ext i j
      simp only [hSXdef, Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    have hSYs : SY = SY.transpose := by
      ext i j
      simp only [hSYdef, Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    have hmemX : ∀ j k : Fin p, ∫ ω', X' ω' j * X' ω' k ∂μ' = SX j k := by
      intro j k
      have hA := statopia_math_node_2606212885_28c76b68 μ' (p + p) (add_pos hp hp) W SigmaS hW
        (Fin.castAdd p j) (Fin.castAdd p k)
      have hfun : (fun ω' => W ω' (Fin.castAdd p j) * W ω' (Fin.castAdd p k))
          = fun ω' => X' ω' j * X' ω' k := by
        funext ω'
        simp [W, Fin.append_left]
      rw [hfun] at hA
      rw [hA.2.1]
      simp only [hSXdef, hMdef, Matrix.of_apply, Matrix.add_apply, Matrix.transpose_apply,
        Matrix.smul_apply, smul_eq_mul]
    have hmemY : ∀ j k : Fin p, ∫ ω', Y' ω' j * Y' ω' k ∂μ' = SY j k := by
      intro j k
      have hA := statopia_math_node_2606212885_28c76b68 μ' (p + p) (add_pos hp hp) W SigmaS hW
        (Fin.natAdd p j) (Fin.natAdd p k)
      have hfun : (fun ω' => W ω' (Fin.natAdd p j) * W ω' (Fin.natAdd p k))
          = fun ω' => Y' ω' j * Y' ω' k := by
        funext ω'
        have h1 : W ω' (Fin.natAdd p j) = Y' ω' j := Fin.append_right (X' ω') (Y' ω') j
        have h2 : W ω' (Fin.natAdd p k) = Y' ω' k := Fin.append_right (X' ω') (Y' ω') k
        rw [h1, h2]
      rw [hfun] at hA
      rw [hA.2.1]
      simp only [hSYdef, hNdef, Matrix.of_apply, Matrix.add_apply, Matrix.transpose_apply,
        Matrix.smul_apply, smul_eq_mul]
    have hintX : ∀ j k : Fin p, Integrable (fun ω' => X' ω' j * X' ω' k) μ' := by
      intro j k
      have hA := (statopia_math_node_2606212885_28c76b68 μ' (p + p) (add_pos hp hp) W SigmaS hW
        (Fin.castAdd p j) (Fin.castAdd p k)).1
      have hfun : (fun ω' => W ω' (Fin.castAdd p j) * W ω' (Fin.castAdd p k))
          = fun ω' => X' ω' j * X' ω' k := by
        funext ω'
        simp [W, Fin.append_left]
      rwa [hfun] at hA
    have hintY : ∀ j k : Fin p, Integrable (fun ω' => Y' ω' j * Y' ω' k) μ' := by
      intro j k
      have hA := (statopia_math_node_2606212885_28c76b68 μ' (p + p) (add_pos hp hp) W SigmaS hW
        (Fin.natAdd p j) (Fin.natAdd p k)).1
      have hfun : (fun ω' => W ω' (Fin.natAdd p j) * W ω' (Fin.natAdd p k))
          = fun ω' => Y' ω' j * Y' ω' k := by
        funext ω'
        have h1 : W ω' (Fin.natAdd p j) = Y' ω' j := Fin.append_right (X' ω') (Y' ω') j
        have h2 : W ω' (Fin.natAdd p k) = Y' ω' k := Fin.append_right (X' ω') (Y' ω') k
        rw [h1, h2]
      rwa [hfun] at hA
    have hintXY : ∀ j k : Fin p, Integrable (fun ω' => X' ω' j * Y' ω' k) μ' :=
      fun j k => (hmomXY j k).1
    have hmemXY : ∀ j k : Fin p, ∫ ω', X' ω' j * Y' ω' k ∂μ' = 0 :=
      fun j k => (hmomXY j k).2
    have hDelta : ∀ j k : Fin p, |SX j k - SY j k| ≤ covDiffMax μ X Y := by
      intro j k
      have hXe := statopia_math_node_2606212885_28c76b68 μ p hp X SigmaX hX j k
      have hYe := statopia_math_node_2606212885_28c76b68 μ p hp Y SigmaY hY j k
      have hSXjk : SX j k = (2 : ℝ)⁻¹ * (SigmaX j k + SigmaX k j) := by
        rw [← hmemX j k]
        exact (hmomX j k).2
      have hSYjk : SY j k = (2 : ℝ)⁻¹ * (SigmaY j k + SigmaY k j) := by
        rw [← hmemY j k]
        exact (hmomY j k).2
      have hcov : covEntry μ X j k - covEntry μ Y j k = SX j k - SY j k := by
        rw [hXe.2.2.1, hYe.2.2.1, hSXjk, hSYjk]
      rw [← hcov]
      exact le_ciSup (f := fun jk : Fin p × Fin p =>
          |covEntry μ X jk.1 jk.2 - covEntry μ Y jk.1 jk.2|)
        (Set.finite_range (fun jk : Fin p × Fin p =>
          |covEntry μ X jk.1 jk.2 - covEntry μ Y jk.1 jk.2|)).bddAbove (j, k)
    have hvsum : ∀ (u : Fin p → ℝ) (ω' : Ω'),
        (∑ i : Fin (p + p), Fin.append (fun _ : Fin p => (0 : ℝ)) u i * W ω' i)
          = ∑ j : Fin p, u j * Y' ω' j := by
      intro u ω'
      rw [Fin.sum_univ_add]
      have h1 : (∑ i : Fin p, Fin.append (fun _ : Fin p => (0 : ℝ)) u (Fin.castAdd p i)
          * W ω' (Fin.castAdd p i)) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i _
        rw [Fin.append_left]
        simp
      rw [h1, zero_add]
      refine Finset.sum_congr rfl ?_
      intro j _
      have hb : Fin.append (fun _ : Fin p => (0 : ℝ)) u (Fin.natAdd p j) = u j :=
        Fin.append_right (fun _ : Fin p => (0 : ℝ)) u j
      have hWb : W ω' (Fin.natAdd p j) = Y' ω' j := Fin.append_right (X' ω') (Y' ω') j
      rw [hb, hWb]
    have hquad : ∀ u : Fin p → ℝ,
        (∑ i : Fin (p + p), ∑ j : Fin (p + p),
            Fin.append (fun _ : Fin p => (0 : ℝ)) u i * SigmaS i j
              * Fin.append (fun _ : Fin p => (0 : ℝ)) u j)
          = ∑ i : Fin p, ∑ j : Fin p, u i * SY i j * u j := by
      intro u
      have hblock : (∑ i : Fin (p + p), ∑ j : Fin (p + p),
            Fin.append (fun _ : Fin p => (0 : ℝ)) u i * SigmaS i j
              * Fin.append (fun _ : Fin p => (0 : ℝ)) u j)
          = ∑ b : Fin p, ∑ c : Fin p, u b * N b c * u c := by
        simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, zero_mul, mul_zero,
          Finset.sum_const_zero, hNdef, Matrix.of_apply, zero_add, add_zero]
      rw [hblock]
      have hsym : (∑ i : Fin p, ∑ j : Fin p, u i * N.transpose i j * u j)
          = ∑ i : Fin p, ∑ j : Fin p, u i * N i j * u j := by
        simp only [Matrix.transpose_apply]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        refine Finset.sum_congr rfl (fun b _ => ?_)
        ring
      have hsplit : ∀ i j : Fin p, u i * SY i j * u j
          = 2⁻¹ * (u i * N i j * u j) + 2⁻¹ * (u i * N.transpose i j * u j) := by
        intro i j
        simp only [hSYdef, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
          smul_eq_mul]
        ring
      have hfinal : (∑ i : Fin p, ∑ j : Fin p, u i * SY i j * u j)
          = ∑ i : Fin p, ∑ j : Fin p, u i * N i j * u j := by
        calc (∑ i : Fin p, ∑ j : Fin p, u i * SY i j * u j)
            = ∑ i : Fin p, ∑ j : Fin p,
                (2⁻¹ * (u i * N i j * u j) + 2⁻¹ * (u i * N.transpose i j * u j)) := by
              refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
              exact hsplit i j
          _ = 2⁻¹ * (∑ i : Fin p, ∑ j : Fin p, u i * N i j * u j)
                + 2⁻¹ * (∑ i : Fin p, ∑ j : Fin p, u i * N.transpose i j * u j) := by
              simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
          _ = 2⁻¹ * (∑ i : Fin p, ∑ j : Fin p, u i * N i j * u j)
                + 2⁻¹ * (∑ i : Fin p, ∑ j : Fin p, u i * N i j * u j) := by
              rw [hsym]
          _ = ∑ i : Fin p, ∑ j : Fin p, u i * N i j * u j := by
              rw [← add_mul, show (2 : ℝ)⁻¹ + 2⁻¹ = 1 by norm_num, one_mul]
      exact hfinal.symm
    have hYm : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ' Y' SY := by
      refine { measurable := hY'meas, integrable_exp := ?_, mgf_eq := ?_ }
      · intro u
        have h := hW.integrable_exp (Fin.append (fun _ : Fin p => (0 : ℝ)) u)
        simpa only [hvsum u] using h
      · intro u
        have h := hW.mgf_eq (Fin.append (fun _ : Fin p => (0 : ℝ)) u)
        simp only [hvsum u] at h
        rw [h]
        rw [hquad u]
    have hconv :=
      statopia_math_node_4127063291_3362e617 μ' p hp X' Y' SX SY hSXs hSYs hXm hYm
        SigmaS hW hintX hintY hintXY hmemX hmemY hmemXY β hβ g hg hg1 hg2
        (covDiffMax μ X Y) hDelta
    rw [hEq]
    calc |expSmoothMaxDiff μ' X' Y' β g|
        ≤ covDiffMax μ X Y * (supNormR (deriv (deriv g)) / 2 + β * supNormR (deriv g)) := hconv
      _ = (supNormR (deriv (deriv g)) / 2 + β * supNormR (deriv g)) * covDiffMax μ X Y :=
          mul_comm _ _
  have hmain2 : |expMaxCoordDiff μ X Y g| ≤
      (supNormR (deriv (deriv g)) / 2 + β * supNormR (deriv g)) * covDiffMax μ X Y
        + 2 * β⁻¹ * supNormR (deriv g) * Real.log (p : ℝ) := by
    have hmax :=
      statopia_math_node_2452871165_059ca161 μ p hp X Y hXmeas hXint hYmeas hYint β hβ g hg1' hg1
    have hd := hmax.2.2
    calc |expMaxCoordDiff μ X Y g|
        = |(expMaxCoordDiff μ X Y g - expSmoothMaxDiff μ X Y β g)
            + expSmoothMaxDiff μ X Y β g| := by rw [sub_add_cancel]
      _ ≤ |expMaxCoordDiff μ X Y g - expSmoothMaxDiff μ X Y β g|
            + |expSmoothMaxDiff μ X Y β g| := abs_add_le _ _
      _ ≤ 2 * β⁻¹ * supNormR (deriv g) * Real.log (p : ℝ)
            + (supNormR (deriv (deriv g)) / 2 + β * supNormR (deriv g))
              * covDiffMax μ X Y := add_le_add hd hmain1
      _ = (supNormR (deriv (deriv g)) / 2 + β * supNormR (deriv g)) * covDiffMax μ X Y
            + 2 * β⁻¹ * supNormR (deriv g) * Real.log (p : ℝ) := by rw [add_comm]
  exact ⟨hmain1, hmain2⟩
  /- @proof-region region.root.7950b4d8e02c end -/

end Statlib.Imported

