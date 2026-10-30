import ProverJobs.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Vocabulary
import ProverJobs.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Base
import ProverJobs.job_paper_82217ff9ed45452ea25ea7588fe2ef01.ProvedNodes.Node_1043829637_02d50666_07067a8c
import ProverJobs.job_paper_82217ff9ed45452ea25ea7588fe2ef01.ProvedNodes.Node_1204950056_f3779bef_4863efbe
import ProverJobs.job_paper_82217ff9ed45452ea25ea7588fe2ef01.ExternalNodes.Node_e7e3b4e2028d428ab478

namespace PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01


open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
open _root_.PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported
open _root_.PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.Model

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
namespace Statlib.Imported

noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_2151621483_4d3e915f : ∀ (a c0 alpha cvar ccirc eps0 Ccor : ℝ)
    (halpha : 0 < alpha) (hccirc : ccirc ∈ Set.Ioo (0 : ℝ) 1)
    (heps0 : eps0 ∈ Set.Ioo (0 : ℝ) 1) (hCcor : 0 < Ccor)
    {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) (1 / 2)),
    ∃ CA : ℝ, 0 < CA ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
        (M : Model Ω μ a) (hM : Model.Assumptions M c0 alpha cvar ccirc eps0 Ccor),
        ∃ NA : ℕ, 1 ≤ NA ∧
          ∀ n : ℕ, NA ≤ n → M.kIdx n < M.p n →
            (M.tildeLaw n)
              {w : Fin (M.p n) → ℝ |
                fmax (M.J n (M.kIdx n)) (fun j => w j / (M.sigma n j) ^ (M.tau n)) ≤
                  ccirc * ((M.ell n : ℝ) ^ (-(alpha * (1 - M.tau n)))) *
                    Real.sqrt (Real.log (M.ell n : ℝ))} ≤
              ENNReal.ofReal (CA * (n : ℝ) ^ (-(1 / 2 : ℝ) + δ)) := by
  /- @proof-region region.target-node.session.d6819dcd713dc711 begin -/
  intro a c0 alpha cvar ccirc eps0 Ccor halpha hccirc heps0 hCcor δ hδ
  obtain ⟨CA, hCApos, hCAbound⟩ :=
    statopia_math_node_1204950056_f3779bef a c0 alpha cvar ccirc eps0 Ccor halpha hccirc heps0 hCcor
  refine ⟨CA, hCApos, ?_⟩
  intro Ω _ μ _ M hM
  refine ⟨3, by norm_num, ?_⟩
  intro n hn hk
  have hn1 : 1 ≤ n := by omega
  have hmono :
      (M.tildeLaw n)
        {w : Fin (M.p n) → ℝ |
          fmax (M.J n (M.kIdx n)) (fun j => w j / (M.sigma n j) ^ (M.tau n)) ≤
            ccirc * ((M.ell n : ℝ) ^ (-(alpha * (1 - M.tau n)))) *
              Real.sqrt (Real.log (M.ell n : ℝ))}
      ≤ (M.tildeLaw n)
        {w : Fin (M.p n) → ℝ |
          fmax (M.J n (M.ell n)) (fun j => w j / (M.sigma n j)) ≤
            Real.sqrt (Real.log (M.ell n : ℝ))} := by
    apply MeasureTheory.measure_mono
    intro w hw
    have hn0 : 0 < n := by omega
    have hle_p : M.ell n ≤ M.p n := M.ell_le_p n
    have hell_le_k : M.ell n ≤ M.kIdx n := by
      have h1 : (M.ell n : ℝ) ≤
          min (max (M.ell n : ℝ) ((n : ℝ) ^ (1 / ((Real.log (n : ℝ)) ^ a))))
            (M.p n : ℝ) :=
        le_min (le_max_left _ _) (Nat.cast_le.mpr hle_p)
      have h2 : Nat.ceil (M.ell n : ℝ) ≤ M.kIdx n := Nat.ceil_le_ceil h1
      simpa [Nat.ceil_natCast] using h2
    have hellpos : 0 < M.ell n := by
      have hp1 : (1 : ℝ) ≤ (M.p n : ℝ) := by exact_mod_cast M.hp n
      have hmin : (1 : ℝ) ≤ min (max (1 : ℝ) ((Real.log (n : ℝ)) ^ 3)) (M.p n : ℝ) :=
        le_min (le_max_left _ _) hp1
      have hceil := Nat.le_ceil (min (max (1 : ℝ) ((Real.log (n : ℝ)) ^ 3)) (M.p n : ℝ))
      have h1 : (1 : ℝ) ≤ (M.ell n : ℝ) := le_trans hmin hceil
      have h2 : (1 : ℕ) ≤ M.ell n := by exact_mod_cast h1
      omega
    have hJsub : M.J n (M.ell n) ⊆ M.J n (M.kIdx n) := by
      intro j hj
      have hj' : j ∈ (Finset.univ.filter (fun i : Fin (M.p n) => (i : ℕ) < M.ell n)).image
          (fun i => M.g n i) := hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj'
      rw [Finset.mem_filter] at hi
      change M.g n i ∈ (Finset.univ.filter (fun i : Fin (M.p n) => (i : ℕ) < M.kIdx n)).image
        (fun i => M.g n i)
      exact Finset.mem_image.mpr ⟨i, by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, lt_of_lt_of_le hi.2 hell_le_k⟩, rfl⟩
    have hne : (M.J n (M.ell n)).Nonempty := by
      have hp0 : 0 < M.p n := lt_of_lt_of_le Nat.zero_lt_one (M.hp n)
      refine ⟨M.g n ⟨0, hp0⟩, ?_⟩
      change M.g n ⟨0, hp0⟩ ∈ (Finset.univ.filter (fun i : Fin (M.p n) => (i : ℕ) < M.ell n)).image
        (fun i => M.g n i)
      exact Finset.mem_image.mpr ⟨⟨0, hp0⟩, by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hellpos⟩, rfl⟩
    have le_fmax : ∀ (s : Finset (Fin (M.p n))) (f : Fin (M.p n) → ℝ) (j : Fin (M.p n)),
        j ∈ s → f j ≤ fmax s f := by
      intro s f j hj
      exact le_csSup (Set.Finite.bddAbove (s.finite_toSet.image f))
        ⟨j, Finset.mem_coe.mpr hj, rfl⟩
    have fmax_le : ∀ (s : Finset (Fin (M.p n))) (f : Fin (M.p n) → ℝ) (c : ℝ), s.Nonempty →
        (∀ j ∈ s, f j ≤ c) → fmax s f ≤ c := by
      intro s f c hsne h
      refine csSup_le ?_ ?_
      · obtain ⟨j, hj⟩ := hsne
        exact ⟨f j, j, Finset.mem_coe.mpr hj, rfl⟩
      · rintro _ ⟨j, hj, rfl⟩
        exact h j (Finset.mem_coe.mp hj)
    refine fmax_le (M.J n (M.ell n)) (fun j => w j / M.sigma n j)
      (Real.sqrt (Real.log (M.ell n : ℝ))) hne ?_
    intro j hj
    have hj' : j ∈ (Finset.univ.filter (fun i : Fin (M.p n) => (i : ℕ) < M.ell n)).image
        (fun i => M.g n i) := hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj'
    rw [Finset.mem_filter] at hi
    have hki : (i : ℕ) + 1 ≤ M.kIdx n := by
      have : (i : ℕ) < M.kIdx n := lt_of_lt_of_le hi.2 hell_le_k
      omega
    have hslow : ccirc * (((i : ℕ) + 1 : ℕ) : ℝ) ^ (-alpha) ≤ M.sigma n (M.g n i) :=
      hM.hsig_lower n hn0 i hki
    have hspos : 0 < M.sigma n (M.g n i) := hM.hsig_pos n hn0 (M.g n i)
    have hellposR : (0 : ℝ) < (M.ell n : ℝ) := by exact_mod_cast hellpos
    have hEpos : 0 < (M.ell n : ℝ) ^ (-alpha) := Real.rpow_pos_of_pos hellposR _
    have hcpos : 0 < ccirc * (M.ell n : ℝ) ^ (-alpha) := mul_pos hccirc.1 hEpos
    have hle_c : ccirc * (M.ell n : ℝ) ^ (-alpha) ≤ M.sigma n (M.g n i) := by
      have hbpos : (0 : ℝ) < (((i : ℕ) + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_pos (i : ℕ)
      have hble : (((i : ℕ) + 1 : ℕ) : ℝ) ≤ (M.ell n : ℝ) := Nat.cast_le.mpr (by omega)
      have hrev : (M.ell n : ℝ) ^ (-alpha) ≤ (((i : ℕ) + 1 : ℕ) : ℝ) ^ (-alpha) :=
        Real.rpow_le_rpow_of_nonpos hbpos hble (by linarith [halpha])
      exact le_trans (mul_le_mul_of_nonneg_left hrev hccirc.1.le) hslow
    have hsτpos : 0 < (M.sigma n (M.g n i)) ^ (M.tau n) := Real.rpow_pos_of_pos hspos _
    have hjk : M.g n i ∈ M.J n (M.kIdx n) := by
      change M.g n i ∈ (Finset.univ.filter (fun i : Fin (M.p n) => (i : ℕ) < M.kIdx n)).image
        (fun i => M.g n i)
      exact Finset.mem_image.mpr ⟨i, by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, lt_of_lt_of_le hi.2 hell_le_k⟩, rfl⟩
    have hwj : w (M.g n i) / (M.sigma n (M.g n i)) ^ (M.tau n) ≤
        ccirc * ((M.ell n : ℝ) ^ (-(alpha * (1 - M.tau n)))) *
          Real.sqrt (Real.log (M.ell n : ℝ)) := by
      have hmem : (w (M.g n i) / (M.sigma n (M.g n i)) ^ (M.tau n)) ∈
          (fun j : Fin (M.p n) => w j / (M.sigma n j) ^ (M.tau n)) ''
            ((M.J n (M.kIdx n)) : Set (Fin (M.p n))) :=
        ⟨M.g n i, Finset.mem_coe.mpr hjk, rfl⟩
      have hbdd : BddAbove ((fun j : Fin (M.p n) => w j / (M.sigma n j) ^ (M.tau n)) ''
          ((M.J n (M.kIdx n)) : Set (Fin (M.p n)))) :=
        Set.Finite.bddAbove ((M.J n (M.kIdx n)).finite_toSet.image _)
      exact le_trans (le_csSup hbdd hmem) hw
    have h1' : w (M.g n i) ≤
        (ccirc * ((M.ell n : ℝ) ^ (-(alpha * (1 - M.tau n)))) *
            Real.sqrt (Real.log (M.ell n : ℝ))) * (M.sigma n (M.g n i)) ^ (M.tau n) :=
      (div_le_iff₀ hsτpos).mp hwj
    have hsle : (M.sigma n (M.g n i)) ^ (M.tau n - 1) ≤
        ccirc ^ (-1 : ℝ) * (M.ell n : ℝ) ^ (alpha * (1 - M.tau n)) := by
      have h1 : (M.sigma n (M.g n i)) ^ (M.tau n - 1) ≤
          (ccirc * (M.ell n : ℝ) ^ (-alpha)) ^ (M.tau n - 1) :=
        Real.rpow_le_rpow_of_nonpos hcpos hle_c (by linarith [(hM.htau_mem n).2])
      have h2 : (ccirc * (M.ell n : ℝ) ^ (-alpha)) ^ (M.tau n - 1) =
          ccirc ^ (M.tau n - 1) * ((M.ell n : ℝ) ^ (-alpha)) ^ (M.tau n - 1) :=
        Real.mul_rpow hccirc.1.le hEpos.le
      have h3 : ccirc ^ (M.tau n - 1) ≤ ccirc ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hccirc.1 hccirc.2.le (by linarith [(hM.htau_mem n).1])
      have h4 : ((M.ell n : ℝ) ^ (-alpha)) ^ (M.tau n - 1) =
          (M.ell n : ℝ) ^ (alpha * (1 - M.tau n)) := by
        rw [← Real.rpow_mul hellposR.le,
          show -alpha * (M.tau n - 1) = alpha * (1 - M.tau n) by ring]
      have h4' : (0 : ℝ) ≤ ((M.ell n : ℝ) ^ (-alpha)) ^ (M.tau n - 1) := by
        rw [h4]
        exact (Real.rpow_pos_of_pos hellposR _).le
      calc (M.sigma n (M.g n i)) ^ (M.tau n - 1)
          ≤ (ccirc * (M.ell n : ℝ) ^ (-alpha)) ^ (M.tau n - 1) := h1
        _ = ccirc ^ (M.tau n - 1) * ((M.ell n : ℝ) ^ (-alpha)) ^ (M.tau n - 1) := h2
        _ ≤ ccirc ^ (-1 : ℝ) * ((M.ell n : ℝ) ^ (-alpha)) ^ (M.tau n - 1) :=
            mul_le_mul_of_nonneg_right h3 h4'
        _ = ccirc ^ (-1 : ℝ) * (M.ell n : ℝ) ^ (alpha * (1 - M.tau n)) := by rw [h4]
    have hkey : (ccirc * ((M.ell n : ℝ) ^ (-(alpha * (1 - M.tau n)))) *
          Real.sqrt (Real.log (M.ell n : ℝ))) * (M.sigma n (M.g n i)) ^ (M.tau n - 1) ≤
        Real.sqrt (Real.log (M.ell n : ℝ)) := by
      have hnonneg : 0 ≤ ccirc * ((M.ell n : ℝ) ^ (-(alpha * (1 - M.tau n)))) *
          Real.sqrt (Real.log (M.ell n : ℝ)) :=
        mul_nonneg (mul_nonneg hccirc.1.le (Real.rpow_pos_of_pos hellposR _).le)
          (Real.sqrt_nonneg _)
      have hstep : (ccirc * ((M.ell n : ℝ) ^ (-(alpha * (1 - M.tau n)))) *
            Real.sqrt (Real.log (M.ell n : ℝ))) * (M.sigma n (M.g n i)) ^ (M.tau n - 1) ≤
          (ccirc * ((M.ell n : ℝ) ^ (-(alpha * (1 - M.tau n)))) *
              Real.sqrt (Real.log (M.ell n : ℝ))) *
            (ccirc ^ (-1 : ℝ) * (M.ell n : ℝ) ^ (alpha * (1 - M.tau n))) :=
        mul_le_mul_of_nonneg_left hsle hnonneg
      refine le_trans hstep (le_of_eq ?_)
      have hcc : ccirc * ccirc ^ (-1 : ℝ) = 1 := by
        have h := Real.rpow_add hccirc.1 (1 : ℝ) (-1 : ℝ)
        rw [show (1 : ℝ) + -1 = 0 by norm_num, Real.rpow_zero, Real.rpow_one] at h
        exact h.symm
      have hβ : (M.ell n : ℝ) ^ (-(alpha * (1 - M.tau n))) *
          (M.ell n : ℝ) ^ (alpha * (1 - M.tau n)) = 1 := by
        have h := Real.rpow_add hellposR (-(alpha * (1 - M.tau n))) (alpha * (1 - M.tau n))
        rw [show -(alpha * (1 - M.tau n)) + alpha * (1 - M.tau n) = 0 by ring,
          Real.rpow_zero] at h
        exact h.symm
      rw [show ccirc * (M.ell n : ℝ) ^ (-(alpha * (1 - M.tau n))) *
            Real.sqrt (Real.log (M.ell n : ℝ)) *
            (ccirc ^ (-1 : ℝ) * (M.ell n : ℝ) ^ (alpha * (1 - M.tau n))) =
          (ccirc * ccirc ^ (-1 : ℝ)) *
            ((M.ell n : ℝ) ^ (-(alpha * (1 - M.tau n))) *
              (M.ell n : ℝ) ^ (alpha * (1 - M.tau n))) *
            Real.sqrt (Real.log (M.ell n : ℝ)) by ring,
        hcc, hβ, one_mul, one_mul]
    have hsplit : (M.sigma n (M.g n i)) ^ (M.tau n) =
        (M.sigma n (M.g n i)) ^ (M.tau n - 1) * (M.sigma n (M.g n i)) := by
      conv_lhs => rw [show M.tau n = (M.tau n - 1) + 1 by ring]
      rw [Real.rpow_add hspos, Real.rpow_one]
    rw [div_le_iff₀ hspos]
    calc w (M.g n i) ≤ (ccirc * ((M.ell n : ℝ) ^ (-(alpha * (1 - M.tau n)))) *
          Real.sqrt (Real.log (M.ell n : ℝ))) * (M.sigma n (M.g n i)) ^ (M.tau n) := h1'
      _ = ((ccirc * ((M.ell n : ℝ) ^ (-(alpha * (1 - M.tau n)))) *
            Real.sqrt (Real.log (M.ell n : ℝ))) *
            (M.sigma n (M.g n i)) ^ (M.tau n - 1)) * (M.sigma n (M.g n i)) := by
          rw [hsplit]
          ring
      _ ≤ Real.sqrt (Real.log (M.ell n : ℝ)) * (M.sigma n (M.g n i)) :=
          mul_le_mul_of_nonneg_right hkey hspos.le
  have hext :
      (M.tildeLaw n)
        {w : Fin (M.p n) → ℝ |
          fmax (M.J n (M.ell n)) (fun j => w j / (M.sigma n j)) ≤
            Real.sqrt (Real.log (M.ell n : ℝ))}
      ≤ ENNReal.ofReal (CA * Real.exp (-(1 / 2 : ℝ) * (M.ell n : ℝ) ^ ((1 : ℝ) / 3))) :=
    hCAbound M hM n hn1
  have hasym :
      ENNReal.ofReal (CA * Real.exp (-(1 / 2 : ℝ) * (M.ell n : ℝ) ^ ((1 : ℝ) / 3)))
      ≤ ENNReal.ofReal (CA * (n : ℝ) ^ (-(1 / 2 : ℝ) + δ)) := by
    apply ENNReal.ofReal_le_ofReal
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have h : (0 : ℕ) < n := by omega
      exact_mod_cast h
    have hnge1 : (1 : ℝ) ≤ (n : ℝ) := by
      have h : (1 : ℕ) ≤ n := by omega
      exact_mod_cast h
    have hkdef : M.kIdx n =
        Nat.ceil (min (max (M.ell n : ℝ) ((n : ℝ) ^ (1 / ((Real.log (n : ℝ)) ^ a))))
          (M.p n : ℝ)) := rfl
    have helldef : M.ell n =
        Nat.ceil (min (max (1 : ℝ) ((Real.log (n : ℝ)) ^ 3)) (M.p n : ℝ)) := rfl
    have hcapk : min (max (M.ell n : ℝ) ((n : ℝ) ^ (1 / ((Real.log (n : ℝ)) ^ a))))
        (M.p n : ℝ) < (M.p n : ℝ) := by
      rcases lt_or_ge (min (max (M.ell n : ℝ) ((n : ℝ) ^ (1 / ((Real.log (n : ℝ)) ^ a))))
        (M.p n : ℝ)) (M.p n : ℝ) with h | h
      · exact h
      · exfalso
        have hmin : min (max (M.ell n : ℝ) ((n : ℝ) ^ (1 / ((Real.log (n : ℝ)) ^ a))))
            (M.p n : ℝ) = (M.p n : ℝ) := le_antisymm (min_le_right _ _) h
        have hkp : M.kIdx n = M.p n := by rw [hkdef, hmin, Nat.ceil_natCast]
        omega
    have hmaxk : max (M.ell n : ℝ) ((n : ℝ) ^ (1 / ((Real.log (n : ℝ)) ^ a))) <
        (M.p n : ℝ) := by
      rcases lt_or_ge (max (M.ell n : ℝ) ((n : ℝ) ^ (1 / ((Real.log (n : ℝ)) ^ a))))
        (M.p n : ℝ) with h | h
      · exact h
      · exfalso
        have hmin : min (max (M.ell n : ℝ) ((n : ℝ) ^ (1 / ((Real.log (n : ℝ)) ^ a))))
            (M.p n : ℝ) = (M.p n : ℝ) := min_eq_right h
        rw [hmin] at hcapk
        exact absurd hcapk (lt_irrefl _)
    have hell_lt_p : (M.ell n : ℝ) < (M.p n : ℝ) :=
      lt_of_le_of_lt (le_max_left _ _) hmaxk
    have hcapell : min (max (1 : ℝ) ((Real.log (n : ℝ)) ^ 3)) (M.p n : ℝ) < (M.p n : ℝ) := by
      rcases lt_or_ge (min (max (1 : ℝ) ((Real.log (n : ℝ)) ^ 3)) (M.p n : ℝ)) (M.p n : ℝ) with
        h | h
      · exact h
      · exfalso
        have hmin : min (max (1 : ℝ) ((Real.log (n : ℝ)) ^ 3)) (M.p n : ℝ) = (M.p n : ℝ) :=
          le_antisymm (min_le_right _ _) h
        have hellp : (M.ell n : ℝ) = (M.p n : ℝ) := by rw [helldef, hmin, Nat.ceil_natCast]
        linarith
    have hmax_ell : max (1 : ℝ) ((Real.log (n : ℝ)) ^ 3) < (M.p n : ℝ) := by
      rcases lt_or_ge (max (1 : ℝ) ((Real.log (n : ℝ)) ^ 3)) (M.p n : ℝ) with h | h
      · exact h
      · exfalso
        have hmin : min (max (1 : ℝ) ((Real.log (n : ℝ)) ^ 3)) (M.p n : ℝ) = (M.p n : ℝ) :=
          min_eq_right h
        rw [hmin] at hcapell
        exact absurd hcapell (lt_irrefl _)
    have helleq : M.ell n = Nat.ceil (max (1 : ℝ) ((Real.log (n : ℝ)) ^ 3)) := by
      rw [helldef, min_eq_left (le_of_lt hmax_ell)]
    have hL3 : (Real.log (n : ℝ)) ^ 3 ≤ (M.ell n : ℝ) := by
      have h := Nat.le_ceil (max (1 : ℝ) ((Real.log (n : ℝ)) ^ 3))
      rw [← helleq] at h
      exact le_trans (le_max_right _ _) h
    have hellge1 : (1 : ℝ) ≤ (M.ell n : ℝ) := by
      have h := Nat.le_ceil (max (1 : ℝ) ((Real.log (n : ℝ)) ^ 3))
      rw [← helleq] at h
      exact le_trans (le_max_left _ _) h
    have hlog_le : Real.log (n : ℝ) ≤ (M.ell n : ℝ) ^ ((1 : ℝ) / 3) := by
      rcases lt_or_ge (Real.log (n : ℝ)) 0 with hneg | hpos
      · have h1 : (1 : ℝ) ^ ((1 : ℝ) / 3) ≤ (M.ell n : ℝ) ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow (by norm_num) hellge1 (by norm_num)
        rw [Real.one_rpow] at h1
        linarith
      · have hpow3 : ((Real.log (n : ℝ)) ^ (3 : ℝ)) = (Real.log (n : ℝ)) ^ 3 :=
          Real.rpow_natCast _ 3
        have hpos3 : (0 : ℝ) ≤ (Real.log (n : ℝ)) ^ (3 : ℝ) := by
          rw [hpow3]
          exact pow_nonneg hpos 3
        have hL3' : (Real.log (n : ℝ)) ^ (3 : ℝ) ≤ (M.ell n : ℝ) := by
          rw [hpow3]
          exact hL3
        have h1 : ((Real.log (n : ℝ)) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) ≤
            (M.ell n : ℝ) ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow hpos3 hL3' (by norm_num)
        have h2 : ((Real.log (n : ℝ)) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) = Real.log (n : ℝ) := by
          rw [← Real.rpow_mul hpos, show (3 : ℝ) * (1 / 3) = 1 by norm_num, Real.rpow_one]
        rw [h2] at h1
        exact h1
    calc CA * Real.exp (-(1 / 2 : ℝ) * (M.ell n : ℝ) ^ ((1 : ℝ) / 3))
        ≤ CA * Real.exp (-(1 / 2 : ℝ) * Real.log (n : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ hCApos.le
          exact Real.exp_le_exp_of_le (by linarith)
      _ = CA * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
          rw [Real.rpow_def_of_pos hnpos,
            show Real.log (n : ℝ) * (-(1 / 2 : ℝ)) = -(1 / 2 : ℝ) * Real.log (n : ℝ) by ring]
      _ ≤ CA * (n : ℝ) ^ (-(1 / 2 : ℝ) + δ) := by
          refine mul_le_mul_of_nonneg_left ?_ hCApos.le
          exact Real.rpow_le_rpow_of_exponent_le hnge1 (by linarith [hδ.1])
  exact le_trans hmono (le_trans hext hasym)
  /- @proof-region region.target-node.session.d6819dcd713dc711 end -/

end
end Statlib.Imported

