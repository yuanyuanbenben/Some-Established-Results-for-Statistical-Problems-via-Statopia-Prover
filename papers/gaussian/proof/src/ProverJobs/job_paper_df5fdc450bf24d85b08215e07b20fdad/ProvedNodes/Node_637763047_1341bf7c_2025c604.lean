import ProverJobs.job_paper_df5fdc450bf24d85b08215e07b20fdad.Vocabulary
import ProverJobs.job_paper_df5fdc450bf24d85b08215e07b20fdad.Base

namespace PaperProofTasks.job_paper_df5fdc450bf24d85b08215e07b20fdad

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators
open _root_.PaperProofTasks.job_paper_df5fdc450bf24d85b08215e07b20fdad.Statlib.Imported

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators
namespace Statlib.Imported


set_option autoImplicit false in
theorem statopia_math_node_637763047_1341bf7c : ∀ (alpha : ℝ) (halpha : 0 < alpha)
    (tau : ℕ → ℝ) (htau_zero : ∀ n, 0 ≤ tau n) (htau_one : ∀ n, tau n < 1)
    (ctau : ℝ) (hctau : 0 < ctau) (Ntau : ℕ)
    (hgrowth : ∀ n : ℕ, Ntau ≤ n →
      ctau ≤ (1 - tau n) * Real.sqrt (Real.log (n : ℝ))),
    ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n →
        (qN alpha tau n = Real.log (n : ℝ) ∧
          (qN alpha tau n / max (Real.log (qN alpha tau n)) 1) *
            (n : ℝ) ^ (-(1 / 2 : ℝ) + 1 / qN alpha tau n) ≤ 1 ∧
          (3 ≤ qN alpha tau n ∧ 2 < qN alpha tau n ∧
            1 ≤ max (Real.log (qN alpha tau n)) 1 ∧
            (n : ℝ) ^ (1 / qN alpha tau n) = Real.exp 1)) := by
  /- @proof-region region.target-node.session.a9a51f747b3b3c48 begin -/
  intro alpha halpha tau htau_nonneg htau_lt_one ctau hctau Ntau hgrowth
  let C : ℝ := max (max 100 ((2 / (alpha * ctau)) ^ 2)) (16 * Real.exp 1 + 1)
  have hAC : 0 < alpha * ctau := mul_pos halpha hctau
  obtain ⟨N1, hN1⟩ : ∃ N1 : ℕ, Real.exp C ≤ (N1 : ℝ) := exists_nat_ge (Real.exp C)
  refine ⟨max (max N1 1) Ntau, ?_, ?_⟩
  · exact le_trans (le_max_right N1 1) (le_max_left (max N1 1) Ntau)
  · intro n hn
    have hN1n : N1 ≤ n :=
      le_trans (le_trans (le_max_left N1 1) (le_max_left (max N1 1) Ntau)) hn
    have hNtaun : Ntau ≤ n := le_trans (le_max_right (max N1 1) Ntau) hn
    set L : ℝ := Real.log (n : ℝ) with hLdef
    have hLC : C ≤ L := by
      have hcast : (N1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hN1n
      have h1 : Real.exp C ≤ (n : ℝ) := le_trans hN1 hcast
      have h2 : Real.log (Real.exp C) ≤ Real.log (n : ℝ) := Real.log_le_log (Real.exp_pos C) h1
      have h3 : Real.log (Real.exp C) = C := Real.log_exp C
      rw [h3] at h2
      exact h2
    have h100 : 100 ≤ L :=
      le_trans (le_max_left 100 ((2 / (alpha * ctau)) ^ 2))
        (le_trans (le_max_left (max 100 ((2 / (alpha * ctau)) ^ 2))
          (16 * Real.exp 1 + 1)) hLC)
    have hKey : (2 / (alpha * ctau)) ^ 2 ≤ L :=
      le_trans (le_max_right 100 ((2 / (alpha * ctau)) ^ 2))
        (le_trans (le_max_left (max 100 ((2 / (alpha * ctau)) ^ 2))
          (16 * Real.exp 1 + 1)) hLC)
    have hCbig : 16 * Real.exp 1 + 1 ≤ L :=
      le_trans (le_max_right (max 100 ((2 / (alpha * ctau)) ^ 2))
        (16 * Real.exp 1 + 1)) hLC
    have hLpos : 0 < L := by linarith
    have hLne : L ≠ 0 := ne_of_gt hLpos
    have hnpos : 0 < (n : ℝ) := by
      have h0 : (n : ℝ) ≠ 0 := by
        intro h
        have hlog0 : Real.log (n : ℝ) = 0 := by rw [h, Real.log_zero]
        have hL0 : L = 0 := by rw [hLdef]; exact hlog0
        linarith
      exact lt_of_le_of_ne (Nat.cast_nonneg n) (Ne.symm h0)
    have h1mpos : 0 < 1 - tau n := by linarith [htau_lt_one n]
    have hβpos : 0 < alpha * (1 - tau n) := mul_pos halpha h1mpos
    have hsq : Real.sqrt L * Real.sqrt L = L := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hLpos,
        show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, Real.rpow_one]
    have hg : ctau ≤ (1 - tau n) * Real.sqrt L := hgrowth n hNtaun
    have hk : 2 / (alpha * ctau) ≤ Real.sqrt L := by
      have hknn : 0 ≤ 2 / (alpha * ctau) := le_of_lt (div_pos (by norm_num) hAC)
      calc 2 / (alpha * ctau) = Real.sqrt ((2 / (alpha * ctau)) ^ 2) := (Real.sqrt_sq hknn).symm
        _ ≤ Real.sqrt L := Real.sqrt_le_sqrt hKey
    have h2 : 2 / betaN alpha tau n ≤ L := by
      simp only [betaN]
      rw [div_le_iff₀ hβpos]
      have hsn : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
      have hstep1 : Real.sqrt L * ctau ≤ L * (1 - tau n) := by
        have hmul := mul_le_mul_of_nonneg_left hg hsn
        have heq : Real.sqrt L * ((1 - tau n) * Real.sqrt L)
            = (Real.sqrt L * Real.sqrt L) * (1 - tau n) := by ring
        calc Real.sqrt L * ctau ≤ Real.sqrt L * ((1 - tau n) * Real.sqrt L) := hmul
          _ = (Real.sqrt L * Real.sqrt L) * (1 - tau n) := heq
          _ = L * (1 - tau n) := by rw [hsq]
      have hstep2 : Real.sqrt L * (alpha * ctau) ≤ L * (alpha * (1 - tau n)) := by
        calc Real.sqrt L * (alpha * ctau) = alpha * (Real.sqrt L * ctau) := by ring
          _ ≤ alpha * (L * (1 - tau n)) := mul_le_mul_of_nonneg_left hstep1 (le_of_lt halpha)
          _ = L * (alpha * (1 - tau n)) := by ring
      have hstep3 : 2 ≤ Real.sqrt L * (alpha * ctau) := by
        have h := hk
        rw [div_le_iff₀ hAC] at h
        exact h
      linarith [hstep2, hstep3]
    have hexp : (n : ℝ) ^ (1 / L) = Real.exp 1 := by
      rw [Real.rpow_def_of_pos hnpos (1 / L)]
      rw [show Real.log (n : ℝ) * (1 / L) = 1 by
        rw [show Real.log (n : ℝ) = L from hLdef.symm]
        field_simp]
    have hq : qN alpha tau n = L := by
      have h3 : (3 : ℝ) ≤ L := by linarith
      simp only [qN]
      rw [show Real.log (n : ℝ) = L from hLdef.symm]
      refine le_antisymm ?_ ?_
      · exact max_le (max_le h2 (le_refl L)) h3
      · exact le_trans (le_max_right (2 / betaN alpha tau n) L) (le_max_left _ 3)
    rw [hq]
    refine ⟨hLdef, ?_, by linarith, by linarith, le_max_right (Real.log L) 1, hexp⟩
    have hx : L / max (Real.log L) 1 ≤ L :=
      div_le_self (le_of_lt hLpos) (le_max_right (Real.log L) 1)
    have hsplit : (n : ℝ) ^ (-(1 / 2 : ℝ) + 1 / L)
        = (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp 1 := by
      rw [Real.rpow_add hnpos, hexp]
    rw [hsplit]
    have hstep1 : (L / max (Real.log L) 1) * ((n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp 1)
        ≤ L * ((n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp 1) :=
      mul_le_mul_of_nonneg_right hx
        (mul_nonneg (le_of_lt (Real.rpow_pos_of_pos hnpos (-(1 / 2))))
          (le_of_lt (Real.exp_pos 1)))
    have hstep2 : L * ((n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp 1)
        = (L * Real.exp 1) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by ring
    have hstep3 : (L * Real.exp 1) * (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
      have hnhalf : (n : ℝ) ^ (1 / 2 : ℝ) = Real.exp (L / 2) := by
        rw [Real.rpow_def_of_pos hnpos (1 / 2 : ℝ),
          show Real.log (n : ℝ) = L from hLdef.symm,
          show L * (1 / 2 : ℝ) = L / 2 by ring]
      have hsplitE : Real.exp (L / 2) = Real.exp (L / 4) * Real.exp (L / 4) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hmain : L * Real.exp 1 ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
        rw [hnhalf, hsplitE]
        have h1 : L / 4 + 1 ≤ Real.exp (L / 4) := Real.add_one_le_exp (L / 4)
        have h2 : (0 : ℝ) ≤ L / 4 + 1 := by linarith
        have h3 : (L / 4 + 1) * (L / 4 + 1) ≤ Real.exp (L / 4) * Real.exp (L / 4) :=
          mul_le_mul h1 h1 h2 (le_trans h2 h1)
        have h4 : L * Real.exp 1 ≤ (L / 4 + 1) * (L / 4 + 1) := by
          have he := Real.exp_pos 1
          nlinarith [hCbig]
        linarith
      have hpow1 : (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) = 1 := by
        rw [← Real.rpow_add hnpos, show (1 / 2 : ℝ) + -(1 / 2) = 0 by norm_num,
          Real.rpow_zero]
      calc (L * Real.exp 1) * (n : ℝ) ^ (-(1 / 2 : ℝ))
          ≤ (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_right hmain (le_of_lt (Real.rpow_pos_of_pos hnpos (-(1 / 2))))
        _ = 1 := hpow1
    calc (L / max (Real.log L) 1) * ((n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp 1)
        ≤ L * ((n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp 1) := hstep1
      _ = (L * Real.exp 1) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := hstep2
      _ ≤ 1 := hstep3
  /- @proof-region region.target-node.session.a9a51f747b3b3c48 end -/

end Statlib.Imported

