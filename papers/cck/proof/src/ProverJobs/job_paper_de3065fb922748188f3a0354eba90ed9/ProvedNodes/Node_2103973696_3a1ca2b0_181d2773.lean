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
theorem statopia_math_node_2103973696_3a1ca2b0 : ∀ (q : ℕ) (j : Fin q)
    (Sigma : Matrix (Fin q) (Fin q) ℝ) (hSigma : Sigma.PosSemidef)
    (hVar : ∀ k : Fin q, Sigma k k = 1),
    (let S : Matrix {k : Fin q // k ≠ j} {k : Fin q // k ≠ j} ℝ :=
       fun k l => Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j
     S.PosSemidef ∧ ((((1 : ℝ) / 2)) • (S + S.transpose)).PosSemidef) := by
  /- @proof-region region.target-node.session.999e9b53911e5756 begin -/
  intro q j Sigma hSigma hVar
  classical
  let F : Matrix {k : Fin q // k ≠ j} {k : Fin q // k ≠ j} ℝ :=
    fun k l => Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j
  change F.PosSemidef ∧ ((((1 : ℝ) / 2)) • (F + F.transpose)).PosSemidef
  have hsymm : ∀ a b : Fin q, Sigma a b = Sigma b a := by
    intro a b
    have h := (Matrix.PosSemidef.isHermitian hSigma).apply a b
    simpa using h.symm
  have sum_ite_single : ∀ (a : Fin q) (g : Fin q → ℝ),
      (∑ x : Fin q, (if x = a then g x else 0)) = g a := by
    intro a g
    have h := Finset.sum_eq_single (s := Finset.univ)
      (f := fun x => if x = a then g x else 0) a
      (fun b _ hb => if_neg hb) (fun h => absurd (Finset.mem_univ a) h)
    simpa using h
  have sum_two : ∀ (g : Fin q → ℝ) (a b : Fin q), a ≠ b →
      (∀ x, x ≠ a → x ≠ b → g x = 0) → (∑ x : Fin q, g x) = g a + g b := by
    intro g a b hab hzero
    have hpt : ∀ x, g x = (if x = a then g x else 0) + (if x = b then g x else 0) := by
      intro x
      by_cases hxa : x = a
      · rw [hxa, if_pos rfl, if_neg hab]; ring
      · rw [if_neg hxa]
        by_cases hxb : x = b
        · rw [hxb, if_pos rfl]; ring
        · rw [if_neg hxb, hzero x hxa hxb]; ring
    calc (∑ x : Fin q, g x)
        = ∑ x : Fin q, ((if x = a then g x else 0) + (if x = b then g x else 0)) :=
          Finset.sum_congr rfl (fun x _ => hpt x)
      _ = (∑ x : Fin q, (if x = a then g x else 0)) +
            (∑ x : Fin q, (if x = b then g x else 0)) :=
          Finset.sum_add_distrib
      _ = g a + g b := by rw [sum_ite_single, sum_ite_single]
  have hSpsd : F.PosSemidef := by
    let T : Matrix (Fin q) {k : Fin q // k ≠ j} ℝ :=
      fun a l => if a = j then -Sigma l.1 j else if a = l.1 then 1 else 0
    have hTS : T.conjTranspose * Sigma * T = F := by
      ext k l
      rw [Matrix.conjTranspose_eq_transpose_of_trivial T]
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
      have hF : F k l = Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j := rfl
      rw [hF]
      have hinner : ∀ a : Fin q,
          (∑ b : Fin q, T b k * Sigma b a) = Sigma k.1 a - Sigma k.1 j * Sigma j a := by
        intro a
        have hjk : j ≠ k.1 := fun h => k.2 h.symm
        rw [sum_two (fun b => T b k * Sigma b a) j k.1 hjk (by
          intro x hxj hxk
          have e : T x k = (if x = j then -Sigma k.1 j else if x = k.1 then 1 else 0) := rfl
          show T x k * Sigma x a = 0
          rw [e, if_neg hxj, if_neg hxk, zero_mul])]
        have hTj : T j k = -Sigma k.1 j := by
          have e : T j k = (if j = j then -Sigma k.1 j else if j = k.1 then 1 else 0) := rfl
          rw [e, if_pos rfl]
        have hTk : T k.1 k = 1 := by
          have e : T k.1 k = (if k.1 = j then -Sigma k.1 j else if k.1 = k.1 then 1 else 0) := rfl
          rw [e, if_neg k.2, if_pos rfl]
        rw [hTj, hTk]; ring
      simp only [hinner]
      have houter : (∑ a : Fin q, (Sigma k.1 a - Sigma k.1 j * Sigma j a) * T a l)
          = Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j := by
        have hjl : j ≠ l.1 := fun h => l.2 h.symm
        rw [sum_two (fun a => (Sigma k.1 a - Sigma k.1 j * Sigma j a) * T a l) j l.1 hjl (by
          intro x hxj hxl
          have e : T x l = (if x = j then -Sigma l.1 j else if x = l.1 then 1 else 0) := rfl
          show (Sigma k.1 x - Sigma k.1 j * Sigma j x) * T x l = 0
          rw [e, if_neg hxj, if_neg hxl, mul_zero])]
        have hTj : T j l = -Sigma l.1 j := by
          have e : T j l = (if j = j then -Sigma l.1 j else if j = l.1 then 1 else 0) := rfl
          rw [e, if_pos rfl]
        have hTl : T l.1 l = 1 := by
          have e : T l.1 l = (if l.1 = j then -Sigma l.1 j else if l.1 = l.1 then 1 else 0) := rfl
          rw [e, if_neg l.2, if_pos rfl]
        rw [hTj, hTl, hVar j, hsymm j l.1]
        ring
      exact houter
    rw [← hTS]
    exact hSigma.conjTranspose_mul_mul_same T
  have hsym : F.transpose = F := by
    have h1 : F.conjTranspose = F := (Matrix.PosSemidef.isHermitian hSpsd).eq
    rw [Matrix.conjTranspose_eq_transpose_of_trivial F] at h1
    exact h1
  have heq : (((1 : ℝ) / 2)) • (F + F.transpose) = F := by
    rw [hsym, smul_add, ← add_smul,
      show ((1 : ℝ) / 2) + ((1 : ℝ) / 2) = 1 by norm_num, one_smul]
  exact ⟨hSpsd, by rw [heq]; exact hSpsd⟩
  /- @proof-region region.target-node.session.999e9b53911e5756 end -/

end Statlib.Imported

