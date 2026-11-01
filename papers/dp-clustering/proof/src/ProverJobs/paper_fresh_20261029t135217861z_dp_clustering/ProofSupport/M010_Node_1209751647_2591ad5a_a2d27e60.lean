import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M000_Vocabulary
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M001_Base

/- Original module ProverJobs.job_paper_dc88427b52844263b5321fc99eb582d8.ProvedNodes.Node_1209751647_2591ad5a_a2d27e60; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported

open Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_1209751647_2591ad5a : ∀ (t : ℕ) (ht : 1 ≤ t) (n : ℕ) (lab : Fin n → Fin t)
    (E : Finset (Finset (Fin t))) (hE : ∀ e ∈ E, e.card = 2)
    (lam kappa : ℝ) (hlam : 0 < lam) (hkappa_nonneg : 0 ≤ kappa)
    (hkappa_lt : kappa < 1)
    (w : Finset (Fin n) → ℝ)
    (hw_nonneg : ∀ B : Finset (Fin n), B.Nonempty → 0 ≤ w B)
    (hpure : ∀ (B : Finset (Fin n)) (l : Fin t), B.Nonempty →
      B ⊆ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l) →
      w B ≤ lam * ((B.card.factorial : ℝ) / ((B.card : ℝ)) ^ 2))
    (hcross : ∀ (B : Finset (Fin n)) (l k : Fin t), l ≠ k →
      ({l, k} : Finset (Fin t)) ∈ E → B.Nonempty →
      B ⊆ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l) ∪
            (Finset.univ : Finset (Fin n)).filter (fun i => lab i = k) →
      (B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l)).Nonempty →
      (B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = k)).Nonempty →
      w B / (((B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l)).card.factorial : ℝ) *
             ((B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = k)).card.factorial : ℝ))
        ≤ kappa ^ ((B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l)).card +
                   (B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = k)).card) /
          (((B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l)).card +
            (B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = k)).card : ℕ) : ℝ))
    (hother : ∀ B : Finset (Fin n), B.Nonempty →
      (∀ l : Fin t, ¬ B ⊆ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l)) →
      (∀ (l k : Fin t), l ≠ k → ({l, k} : Finset (Fin t)) ∈ E →
        ¬ (B ⊆ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l) ∪
              (Finset.univ : Finset (Fin n)).filter (fun i => lab i = k) ∧
           (B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l)).Nonempty ∧
           (B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = k)).Nonempty)) →
      w B = 0)
    (C0 H B0 K5 : ℝ)
    (hC0nine : 9 ≤ C0) (hHge : 1 ≤ H) (hB0 : B0 = C0 * H)
    (hkap : ∀ p : ℕ, 1 ≤ p → kappa ^ p / Real.sqrt ((p : ℝ)) ≤ H / ((p : ℝ) ^ 2))
    (hconv : ∀ m : ℕ, 2 ≤ m →
      (∑ a ∈ Finset.range m, (1 : ℝ) / (((a : ℝ) ^ 2) * (((m : ℝ) - (a : ℝ)) ^ 2)))
        ≤ 8 / ((m : ℝ) ^ 2))
    (hK5main : B0 * ((t : ℝ) * lam + B0 * (E.card : ℝ) / 2) ≤ K5),
    ∀ S : Finset (Fin n),
      (∑ B ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S),
          w B * ∏ l : Fin t, dpPhi (((S \ B).filter (fun i => lab i = l)).card))
        ≤ (∏ l : Fin t, dpPhi (((S.filter (fun i => lab i = l)).card))) * K5 := by
  /- @proof-region region.target-node.session.933ddd5d81345fe8 begin -/
  intro t ht n lab E hE lam kappa hlam hkappa_nonneg hkappa_lt w hw_nonneg hpure hcross
    hother C0 H B0 K5 hC0nine hHge hB0 hkap hconv hK5main S
  classical
  let Φ : ℕ → ℝ := fun a => if a = 0 then 1 else (a.factorial : ℝ) / (a : ℝ) ^ 2
  have hΦdef : ∀ a : ℕ, Φ a = if a = 0 then (1 : ℝ) else (a.factorial : ℝ) / (a : ℝ) ^ 2 :=
    fun a => rfl
  have hΦpos : ∀ a : ℕ, 0 < Φ a := by
    intro a
    rw [hΦdef a]
    split_ifs with h
    · norm_num
    · have h1 : (0 : ℝ) < (a.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos a
      have h2 : (0 : ℝ) < (a : ℝ) ^ 2 := by
        have h3 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h
        positivity
      exact div_pos h1 h2
  change (∑ B ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S),
      w B * ∏ l : Fin t, Φ ((S \ B).filter (fun i => lab i = l)).card)
    ≤ (∏ l : Fin t, Φ ((S.filter (fun i => lab i = l)).card)) * K5
  have hmemI : ∀ B ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S),
      B ⊆ S := by
    intro B hB
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hB
    exact hB.2
  have hstep : ∀ (B : Finset (Fin n)) (l : Fin t), B ⊆ S →
      (S \ B).filter (fun i => lab i = l) = (S.filter (fun i => lab i = l)) \ B := by
    intro B l hB
    ext i
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    tauto
  have hcard : ∀ (B : Finset (Fin n)) (l : Fin t), B ⊆ S →
      ((S \ B).filter (fun i => lab i = l)).card
        = (S.filter (fun i => lab i = l)).card - (B.filter (fun i => lab i = l)).card := by
    intro B l hB
    have h1 : (S.filter (fun i => lab i = l)) \ B
        = (S.filter (fun i => lab i = l)) \ (B.filter (fun i => lab i = l)) := by
      ext i
      simp only [Finset.mem_sdiff, Finset.mem_filter]
      tauto
    rw [hstep B l hB, h1, Finset.card_sdiff_of_subset]
    intro i hi
    simp only [Finset.mem_filter] at hi ⊢
    exact ⟨hB hi.1, hi.2⟩
  have hcongr : ∀ B ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S),
      w B * ∏ l : Fin t, Φ ((S \ B).filter (fun i => lab i = l)).card
        = w B * ∏ l : Fin t,
            Φ ((S.filter (fun i => lab i = l)).card - (B.filter (fun i => lab i = l)).card) := by
    intro B hB
    have hB' := hmemI B hB
    congr 1
    exact Finset.prod_congr rfl (fun l _ => by rw [hcard B l hB'])
  rw [Finset.sum_congr rfl hcongr]
  have hΦfac : ∀ s : ℕ, 1 ≤ s → Φ s = (s.factorial : ℝ) / (s : ℝ) ^ 2 := by
    intro s hs
    rw [hΦdef s, if_neg (by omega : s ≠ 0)]
  have hkey : ∀ (s a : ℕ), a < s →
      (s.choose a : ℝ) * ((a.factorial : ℝ) / (a : ℝ) ^ 2) * Φ (s - a)
        = (s.factorial : ℝ) / ((a : ℝ) ^ 2 * ((s : ℝ) - (a : ℝ)) ^ 2) := by
    intro s a ha
    have hsa : s - a ≠ 0 := by omega
    have hcast : ((s - a : ℕ) : ℝ) = (s : ℝ) - (a : ℝ) := by
      rw [Nat.cast_sub (le_of_lt ha)]
    rw [hΦdef (s - a), if_neg hsa, hcast]
    have hfac : ((s.choose a : ℕ) : ℝ) * ((a.factorial : ℕ) : ℝ) * (((s - a).factorial : ℕ) : ℝ)
        = ((s.factorial : ℕ) : ℝ) := by
      have h := Nat.choose_mul_factorial_mul_factorial (le_of_lt ha)
      exact_mod_cast h
    have hnum : (s.choose a : ℝ) * ((a.factorial : ℝ) * ((s - a).factorial : ℝ))
        = ((s.factorial : ℕ) : ℝ) := by
      rw [← hfac]; ring
    rw [mul_assoc, div_mul_div_comm, ← mul_div_assoc, hnum]
  have hpure_arith : ∀ s : ℕ, (∑ a ∈ Finset.range (s + 1),
        (s.choose a : ℝ) * ((a.factorial : ℝ) / (a : ℝ) ^ 2) * Φ (s - a)) ≤ 9 * Φ s := by
    intro s
    rcases Nat.eq_zero_or_pos s with hs0 | hs
    · subst hs0
      have h0 : (∑ a ∈ Finset.range (0 + 1),
          ((0 : ℕ).choose a : ℝ) * ((a.factorial : ℝ) / (a : ℝ) ^ 2) * Φ (0 - a)) = 0 := by
        rw [Finset.sum_range_succ]
        simp [hΦdef]
      rw [h0]
      exact mul_nonneg (by norm_num) (le_of_lt (hΦpos 0))
    · have hterm : (s.choose s : ℝ) * ((s.factorial : ℝ) / (s : ℝ) ^ 2) * Φ (s - s)
          = (s.factorial : ℝ) / (s : ℝ) ^ 2 := by
        simp [hΦdef]
      have hsplit : (∑ a ∈ Finset.range (s + 1),
            (s.choose a : ℝ) * ((a.factorial : ℝ) / (a : ℝ) ^ 2) * Φ (s - a))
          = (∑ a ∈ Finset.range s,
              (s.choose a : ℝ) * ((a.factorial : ℝ) / (a : ℝ) ^ 2) * Φ (s - a)) + Φ s := by
        rw [Finset.sum_range_succ, hΦfac s hs, hterm]
      have hstep2 : (∑ a ∈ Finset.range s,
            (s.choose a : ℝ) * ((a.factorial : ℝ) / (a : ℝ) ^ 2) * Φ (s - a))
          = (s.factorial : ℝ) *
              (∑ a ∈ Finset.range s, (1 : ℝ) / ((a : ℝ) ^ 2 * ((s : ℝ) - (a : ℝ)) ^ 2)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a ha => ?_)
        rw [Finset.mem_range] at ha
        rw [hkey s a ha, mul_one_div]
      have htail : (∑ a ∈ Finset.range s,
            (s.choose a : ℝ) * ((a.factorial : ℝ) / (a : ℝ) ^ 2) * Φ (s - a)) ≤ 8 * Φ s := by
        rw [hstep2]
        rcases Nat.lt_or_ge s 2 with h2 | h2
        · have hs1 : s = 1 := by omega
          subst hs1
          have hz : (∑ a ∈ Finset.range 1,
              (1 : ℝ) / ((a : ℝ) ^ 2 * (((1 : ℕ) : ℝ) - (a : ℝ)) ^ 2)) = 0 := by
            rw [Finset.sum_range_succ]
            simp
          rw [hz, mul_zero]
          exact mul_nonneg (by norm_num) (le_of_lt (hΦpos 1))
        · have hc := hconv s h2
          have hfac_nonneg : (0 : ℝ) ≤ (s.factorial : ℝ) := by positivity
          have h1 : (s.factorial : ℝ) *
                (∑ a ∈ Finset.range s, (1 : ℝ) / ((a : ℝ) ^ 2 * ((s : ℝ) - (a : ℝ)) ^ 2))
              ≤ (s.factorial : ℝ) * (8 / (s : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hc hfac_nonneg
          refine le_trans h1 ?_
          rw [hΦfac s hs]
          have key : (s.factorial : ℝ) * (8 / (s : ℝ) ^ 2)
              = 8 * ((s.factorial : ℝ) / (s : ℝ) ^ 2) := by
            ring
          rw [key]
      calc (∑ a ∈ Finset.range (s + 1),
            (s.choose a : ℝ) * ((a.factorial : ℝ) / (a : ℝ) ^ 2) * Φ (s - a))
          = (∑ a ∈ Finset.range s,
              (s.choose a : ℝ) * ((a.factorial : ℝ) / (a : ℝ) ^ 2) * Φ (s - a)) + Φ s := hsplit
        _ ≤ 8 * Φ s + Φ s := by linarith [htail]
        _ = 9 * Φ s := by ring
  have hkey2 : ∀ (s p : ℕ), p < s →
      (s.choose p : ℝ) * (p.factorial : ℝ) * Φ (s - p)
        = (s.factorial : ℝ) / ((s : ℝ) - (p : ℝ)) ^ 2 := by
    intro s p hp
    have hsp : s - p ≠ 0 := by omega
    have hcast : ((s - p : ℕ) : ℝ) = (s : ℝ) - (p : ℝ) := by
      rw [Nat.cast_sub (le_of_lt hp)]
    rw [hΦdef (s - p), if_neg hsp, hcast]
    have hfac : ((s.choose p : ℕ) : ℝ) * ((p.factorial : ℕ) : ℝ) * (((s - p).factorial : ℕ) : ℝ)
        = ((s.factorial : ℕ) : ℝ) := by
      have h := Nat.choose_mul_factorial_mul_factorial (le_of_lt hp)
      exact_mod_cast h
    rw [← mul_div_assoc, hfac]
  have hkap' : ∀ p : ℕ, kappa ^ p / Real.sqrt (p : ℝ) ≤ H / (p : ℝ) ^ 2 := by
    intro p
    rcases Nat.eq_zero_or_pos p with hp0 | hp
    · subst hp0
      simp
    · exact hkap p hp
  have hA : ∀ s : ℕ, 1 ≤ s →
      (∑ p ∈ Finset.range (s + 1),
        (s.choose p : ℝ) * (p.factorial : ℝ) * (kappa ^ p / Real.sqrt (p : ℝ)) * Φ (s - p))
        ≤ 9 * H * Φ s := by
    intro s hs
    have htop : (s.choose s : ℝ) * (s.factorial : ℝ) * (kappa ^ s / Real.sqrt (s : ℝ)) * Φ (s - s)
        ≤ H * Φ s := by
      have heq : (s.choose s : ℝ) * (s.factorial : ℝ) * (kappa ^ s / Real.sqrt (s : ℝ)) *
            Φ (s - s) = (s.factorial : ℝ) * (kappa ^ s / Real.sqrt (s : ℝ)) := by
        simp [hΦdef]
      rw [heq]
      have hk := hkap s hs
      refine le_trans (mul_le_mul_of_nonneg_left hk (by positivity)) ?_
      rw [hΦfac s hs]
      have key : (s.factorial : ℝ) * (H / (s : ℝ) ^ 2) = H * ((s.factorial : ℝ) / (s : ℝ) ^ 2) := by
        ring
      rw [key]
    have htail : (∑ p ∈ Finset.range s,
        (s.choose p : ℝ) * (p.factorial : ℝ) * (kappa ^ p / Real.sqrt (p : ℝ)) * Φ (s - p))
        ≤ 8 * H * Φ s := by
      have hstep : (∑ p ∈ Finset.range s,
          (s.choose p : ℝ) * (p.factorial : ℝ) * (kappa ^ p / Real.sqrt (p : ℝ)) * Φ (s - p))
          ≤ (s.factorial : ℝ) * H *
              (∑ p ∈ Finset.range s, (1 : ℝ) / ((p : ℝ) ^ 2 * ((s : ℝ) - (p : ℝ)) ^ 2)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum (fun p hp => ?_)
        rw [Finset.mem_range] at hp
        rcases Nat.eq_zero_or_pos p with hp0 | hp1
        · subst hp0
          simp
        · conv_lhs => rw [mul_right_comm]
          rw [hkey2 s p hp]
          have hk := hkap p hp1
          have hspos : (0 : ℝ) < (s : ℝ) - (p : ℝ) := by
            have h : (p : ℝ) < (s : ℝ) := by exact_mod_cast hp
            linarith
          have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp1
          have heq : (s.factorial : ℝ) / ((s : ℝ) - (p : ℝ)) ^ 2 * (H / (p : ℝ) ^ 2)
              = (s.factorial : ℝ) * H * ((1 : ℝ) / ((p : ℝ) ^ 2 * ((s : ℝ) - (p : ℝ)) ^ 2)) := by
            field_simp
          refine le_trans (mul_le_mul_of_nonneg_left hk (by positivity)) ?_
          rw [heq]
      refine le_trans hstep ?_
      rcases Nat.lt_or_ge s 2 with h2 | h2
      · have hs1 : s = 1 := by omega
        subst hs1
        have hz : (∑ p ∈ Finset.range 1,
            (1 : ℝ) / ((p : ℝ) ^ 2 * (((1 : ℕ) : ℝ) - (p : ℝ)) ^ 2)) = 0 := by
          rw [Finset.sum_range_succ]
          simp
        rw [hz, mul_zero]
        have hH0 : (0 : ℝ) ≤ H := by linarith
        positivity
      · have hc := hconv s h2
        have hfac_nonneg : (0 : ℝ) ≤ (s.factorial : ℝ) * H := by
          have hH0 : (0 : ℝ) ≤ H := by linarith
          positivity
        refine le_trans (mul_le_mul_of_nonneg_left hc hfac_nonneg) ?_
        rw [hΦfac s hs]
        have key : (s.factorial : ℝ) * H * (8 / (s : ℝ) ^ 2)
            = 8 * H * ((s.factorial : ℝ) / (s : ℝ) ^ 2) := by
          ring
        rw [key]
    calc (∑ p ∈ Finset.range (s + 1),
          (s.choose p : ℝ) * (p.factorial : ℝ) * (kappa ^ p / Real.sqrt (p : ℝ)) * Φ (s - p))
        = (∑ p ∈ Finset.range s,
            (s.choose p : ℝ) * (p.factorial : ℝ) * (kappa ^ p / Real.sqrt (p : ℝ)) * Φ (s - p))
          + (s.choose s : ℝ) * (s.factorial : ℝ) * (kappa ^ s / Real.sqrt (s : ℝ)) * Φ (s - s) := by
          rw [Finset.sum_range_succ]
      _ ≤ 8 * H * Φ s + H * Φ s := by linarith [htail, htop]
      _ = 9 * H * Φ s := by ring
  have hfac : ∀ p q : ℕ, 1 ≤ p → 1 ≤ q →
      kappa ^ (p + q) / ((p + q : ℕ) : ℝ)
        ≤ (kappa ^ p / Real.sqrt (p : ℝ)) * (kappa ^ q / Real.sqrt (q : ℝ)) / 2 := by
    intro p q hp hq
    have hP : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
    have hQ : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    have hden : (0 : ℝ) < 2 * (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ)) := by positivity
    have hsqP : Real.sqrt (p : ℝ) ^ 2 = (p : ℝ) := Real.sq_sqrt hP.le
    have hsqQ : Real.sqrt (q : ℝ) ^ 2 = (q : ℝ) := Real.sq_sqrt hQ.le
    have h2 : 2 * (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ)) ≤ (p : ℝ) + (q : ℝ) := by
      nlinarith [sq_nonneg (Real.sqrt (p : ℝ) - Real.sqrt (q : ℝ))]
    have h1 : (1 : ℝ) / ((p : ℝ) + (q : ℝ)) ≤ 1 / (2 * (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ))) :=
      one_div_le_one_div_of_le hden h2
    have h2' : kappa ^ (p + q) * (1 / ((p : ℝ) + (q : ℝ)))
        ≤ kappa ^ (p + q) * (1 / (2 * (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ)))) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    rw [mul_one_div, mul_one_div] at h2'
    have hc : ((p + q : ℕ) : ℝ) = (p : ℝ) + (q : ℝ) := by push_cast; ring
    rw [hc]
    refine le_trans h2' (le_of_eq ?_)
    rw [pow_add]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have hf_nonneg : ∀ B ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S),
      0 ≤ w B * ∏ l : Fin t,
            Φ ((S.filter (fun i => lab i = l)).card - (B.filter (fun i => lab i = l)).card) := by
    intro B hB
    have hBn : B.Nonempty := ((Finset.mem_filter.mp hB).2).1
    exact mul_nonneg (hw_nonneg B hBn) (Finset.prod_nonneg (fun l _ => (hΦpos _).le))
  have hcount : ∀ (T : Finset (Fin n)) (F : ℕ → ℝ), F 0 = 0 →
      (∑ A ∈ T.powerset.filter (fun A => A.Nonempty), F A.card)
        = ∑ a ∈ Finset.range (T.card + 1), (T.card.choose a : ℝ) * F a := by
    intro T F hF0
    have hA : (∑ A ∈ T.powerset.filter (fun A => A.Nonempty), F A.card)
        = ∑ A ∈ T.powerset, F A.card := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun A _ => ?_)
      by_cases hp : A.Nonempty
      · rw [if_pos hp]
      · rw [if_neg hp, Finset.not_nonempty_iff_eq_empty.mp hp]
        simp [hF0]
    rw [hA]
    have hpt : ∀ A ∈ T.powerset, F A.card
        = ∑ a ∈ Finset.range (T.card + 1), (if A.card = a then F a else 0) := by
      intro A hAmem
      have hAle : A.card ≤ T.card := Finset.card_le_card (Finset.mem_powerset.mp hAmem)
      have hmem : A.card ∈ Finset.range (T.card + 1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le hAle)
      rw [← Finset.sum_filter]
      have hfilter : (Finset.range (T.card + 1)).filter (fun a => A.card = a) = {A.card} := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_singleton]
        exact ⟨fun h => h.2.symm, fun h => ⟨by rw [h]; exact hmem, by rw [h]⟩⟩
      rw [hfilter, Finset.sum_singleton]
    rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_filter, Finset.sum_const]
    have hcardeq : (T.powerset.filter (fun A => A.card = a)).card = T.card.choose a := by
      have hset : T.powerset.filter (fun A => A.card = a) = T.powersetCard a := by
        ext A
        rw [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
      rw [hset, Finset.card_powersetCard]
    rw [hcardeq, nsmul_eq_mul]
  have hself : ∀ (B : Finset (Fin n)) (l : Fin t), B ⊆ S.filter (fun i => lab i = l) →
      B.filter (fun i => lab i = l) = B := by
    intro B l hB
    ext i
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.1, fun h => ⟨h, (Finset.mem_filter.mp (hB h)).2⟩⟩
  have hu_zero : ∀ (B : Finset (Fin n)) (l : Fin t), B ⊆ S.filter (fun i => lab i = l) →
      ∀ j : Fin t, j ≠ l → (B.filter (fun i => lab i = j)).card = 0 := by
    intro B l hB j hj
    have hempty : B.filter (fun i => lab i = j) = ∅ := by
      refine Finset.not_nonempty_iff_eq_empty.mp ?_
      rintro ⟨i, hi⟩
      rw [Finset.mem_filter] at hi
      have hiS := Finset.mem_filter.mp (hB hi.1)
      exact hj (hi.2.symm.trans hiS.2)
    rw [hempty]
    simp
  have hprod : ∀ (B : Finset (Fin n)) (l : Fin t), B ⊆ S.filter (fun i => lab i = l) →
      (∏ j : Fin t,
          Φ ((S.filter (fun i => lab i = j)).card - (B.filter (fun i => lab i = j)).card))
        = Φ ((S.filter (fun i => lab i = l)).card - (B.filter (fun i => lab i = l)).card) *
          ∏ j ∈ (Finset.univ : Finset (Fin t)).erase l,
            Φ ((S.filter (fun i => lab i = j)).card) := by
    intro B l hB
    conv_lhs => rw [← Finset.insert_erase (Finset.mem_univ l)]
    rw [Finset.prod_insert (by simp)]
    congr 1
    refine Finset.prod_congr rfl (fun j hj => ?_)
    rw [Finset.mem_erase] at hj
    rw [hu_zero B l hB j hj.1, Nat.sub_zero]
  have hIclass : ∀ l : Fin t,
      ((Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S)).filter
          (fun B => B ⊆ S.filter (fun i => lab i = l))
        = (S.filter (fun i => lab i = l)).powerset.filter (fun A => A.Nonempty) := by
    intro l
    ext B
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hne, hBS⟩, hBT⟩
      exact ⟨hBT, hne⟩
    · rintro ⟨hBT, hne⟩
      exact ⟨⟨hne, fun x hx => (Finset.mem_filter.mp (hBT hx)).1⟩, hBT⟩
  have hprodl : ∀ l : Fin t,
      (∏ j : Fin t, Φ ((S.filter (fun i => lab i = j)).card))
        = Φ ((S.filter (fun i => lab i = l)).card) *
          ∏ j ∈ (Finset.univ : Finset (Fin t)).erase l, Φ ((S.filter (fun i => lab i = j)).card) := by
    intro l
    conv_lhs => rw [← Finset.insert_erase (Finset.mem_univ l)]
    rw [Finset.prod_insert (by simp)]
  have hcl_ne : ∀ l : Fin t, (0 : ℝ) ≤
      ∏ j ∈ (Finset.univ : Finset (Fin t)).erase l, Φ ((S.filter (fun i => lab i = j)).card) :=
    fun l => Finset.prod_nonneg (fun j _ => (hΦpos _).le)
  have hclass : ∀ l : Fin t,
      (∑ B ∈ ((Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S)).filter
          (fun B => B ⊆ S.filter (fun i => lab i = l)),
          w B * ∏ j : Fin t,
            Φ ((S.filter (fun i => lab i = j)).card - (B.filter (fun i => lab i = j)).card))
        ≤ 9 * lam * ∏ j : Fin t, Φ ((S.filter (fun i => lab i = j)).card) := by
    intro l
    have hterm : ∀ B ∈ ((Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S)).filter
          (fun B => B ⊆ S.filter (fun i => lab i = l)),
        w B * ∏ j : Fin t,
            Φ ((S.filter (fun i => lab i = j)).card - (B.filter (fun i => lab i = j)).card)
          = (w B * Φ ((S.filter (fun i => lab i = l)).card - (B.filter (fun i => lab i = l)).card)) *
            ∏ j ∈ (Finset.univ : Finset (Fin t)).erase l,
              Φ ((S.filter (fun i => lab i = j)).card) := by
      intro B hB
      have hBC : B ⊆ S.filter (fun i => lab i = l) := (Finset.mem_filter.mp hB).2
      rw [hprod B l hBC, mul_assoc]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
    have hinner : (∑ B ∈ ((Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S)).filter
          (fun B => B ⊆ S.filter (fun i => lab i = l)),
          w B * Φ ((S.filter (fun i => lab i = l)).card - (B.filter (fun i => lab i = l)).card))
        ≤ lam * (9 * Φ ((S.filter (fun i => lab i = l)).card)) := by
      have h1 : (∑ B ∈ ((Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S)).filter
            (fun B => B ⊆ S.filter (fun i => lab i = l)),
            w B * Φ ((S.filter (fun i => lab i = l)).card - (B.filter (fun i => lab i = l)).card))
          ≤ (∑ B ∈ ((Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S)).filter
              (fun B => B ⊆ S.filter (fun i => lab i = l)),
              (lam * ((B.card.factorial : ℝ) / ((B.card : ℝ)) ^ 2)) *
                Φ ((S.filter (fun i => lab i = l)).card - B.card)) := by
        refine Finset.sum_le_sum (fun B hB => ?_)
        have hBC : B ⊆ S.filter (fun i => lab i = l) := (Finset.mem_filter.mp hB).2
        have hBn : B.Nonempty := (Finset.mem_filter.mp (Finset.mem_filter.mp hB).1).2.1
        have hBC' : B ⊆ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l) :=
          fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ x, (Finset.mem_filter.mp (hBC hx)).2⟩
        have hp := hpure B l hBn hBC'
        rw [hself B l hBC]
        exact mul_le_mul_of_nonneg_right hp (le_of_lt (hΦpos _))
      refine le_trans h1 ?_
      have h2 : (∑ B ∈ ((Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S)).filter
            (fun B => B ⊆ S.filter (fun i => lab i = l)),
            (lam * ((B.card.factorial : ℝ) / ((B.card : ℝ)) ^ 2)) *
              Φ ((S.filter (fun i => lab i = l)).card - B.card))
          = lam * (∑ B ∈ ((Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S)).filter
              (fun B => B ⊆ S.filter (fun i => lab i = l)),
              ((B.card.factorial : ℝ) / ((B.card : ℝ)) ^ 2) *
                Φ ((S.filter (fun i => lab i = l)).card - B.card)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun B _ => ?_)
        ring
      rw [h2]
      have h3 : (∑ B ∈ ((Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S)).filter
            (fun B => B ⊆ S.filter (fun i => lab i = l)),
            ((B.card.factorial : ℝ) / ((B.card : ℝ)) ^ 2) *
              Φ ((S.filter (fun i => lab i = l)).card - B.card))
          = ∑ a ∈ Finset.range ((S.filter (fun i => lab i = l)).card + 1),
              (((S.filter (fun i => lab i = l)).card.choose a : ℝ) *
                (((a.factorial : ℝ) / ((a : ℝ)) ^ 2) *
                  Φ ((S.filter (fun i => lab i = l)).card - a))) := by
        rw [hIclass l]
        exact hcount (S.filter (fun i => lab i = l))
          (fun a => ((a.factorial : ℝ) / ((a : ℝ)) ^ 2) *
            Φ ((S.filter (fun i => lab i = l)).card - a)) (by simp)
      have h3' : (∑ a ∈ Finset.range ((S.filter (fun i => lab i = l)).card + 1),
              (((S.filter (fun i => lab i = l)).card.choose a : ℝ) *
                (((a.factorial : ℝ) / ((a : ℝ)) ^ 2) *
                  Φ ((S.filter (fun i => lab i = l)).card - a))))
          = ∑ a ∈ Finset.range ((S.filter (fun i => lab i = l)).card + 1),
              ((((S.filter (fun i => lab i = l)).card.choose a : ℝ) *
                ((a.factorial : ℝ) / ((a : ℝ)) ^ 2)) *
                  Φ ((S.filter (fun i => lab i = l)).card - a)) := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        ring
      calc lam * (∑ B ∈ ((Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S)).filter
              (fun B => B ⊆ S.filter (fun i => lab i = l)),
              ((B.card.factorial : ℝ) / ((B.card : ℝ)) ^ 2) *
                Φ ((S.filter (fun i => lab i = l)).card - B.card))
          = lam * (∑ a ∈ Finset.range ((S.filter (fun i => lab i = l)).card + 1),
              (((S.filter (fun i => lab i = l)).card.choose a : ℝ) *
                (((a.factorial : ℝ) / ((a : ℝ)) ^ 2) *
                  Φ ((S.filter (fun i => lab i = l)).card - a)))) := by rw [h3]
        _ = lam * (∑ a ∈ Finset.range ((S.filter (fun i => lab i = l)).card + 1),
              ((((S.filter (fun i => lab i = l)).card.choose a : ℝ) *
                ((a.factorial : ℝ) / ((a : ℝ)) ^ 2)) *
                  Φ ((S.filter (fun i => lab i = l)).card - a))) := by rw [h3']
        _ ≤ lam * (9 * Φ ((S.filter (fun i => lab i = l)).card)) :=
            mul_le_mul_of_nonneg_left (hpure_arith ((S.filter (fun i => lab i = l)).card)) (le_of_lt hlam)
    refine le_trans (mul_le_mul_of_nonneg_right hinner (hcl_ne l)) ?_
    rw [hprodl l]
    exact le_of_eq (by ring)
  have hu_zero2 : ∀ (B : Finset (Fin n)) (l k : Fin t), l ≠ k →
      B ⊆ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l) ∪
          (Finset.univ : Finset (Fin n)).filter (fun i => lab i = k) →
      ∀ j : Fin t, j ≠ l → j ≠ k → (B.filter (fun i => lab i = j)).card = 0 := by
    intro B l k hlk hB j hj1 hj2
    have hempty : B.filter (fun i => lab i = j) = ∅ := by
      refine Finset.not_nonempty_iff_eq_empty.mp ?_
      rintro ⟨i, hi⟩
      rw [Finset.mem_filter] at hi
      rcases Finset.mem_union.mp (hB hi.1) with hc | hc
      · exact hj1 (hi.2.symm.trans (Finset.mem_filter.mp hc).2)
      · exact hj2 (hi.2.symm.trans (Finset.mem_filter.mp hc).2)
    rw [hempty]
    simp
  have hprod2 : ∀ (B : Finset (Fin n)) (l k : Fin t), l ≠ k →
      B ⊆ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l) ∪
          (Finset.univ : Finset (Fin n)).filter (fun i => lab i = k) →
      (∏ j : Fin t, Φ ((S.filter (fun i => lab i = j)).card - (B.filter (fun i => lab i = j)).card))
        = Φ ((S.filter (fun i => lab i = l)).card - (B.filter (fun i => lab i = l)).card) *
          (Φ ((S.filter (fun i => lab i = k)).card - (B.filter (fun i => lab i = k)).card) *
            ∏ j ∈ ((Finset.univ : Finset (Fin t)).erase l).erase k,
              Φ ((S.filter (fun i => lab i = j)).card)) := by
    intro B l k hlk hB
    conv_lhs => rw [← Finset.insert_erase (Finset.mem_univ l)]
    rw [Finset.prod_insert (by simp)]
    congr 1
    have hkl : k ∈ (Finset.univ : Finset (Fin t)).erase l := by
      rw [Finset.mem_erase]
      exact ⟨hlk.symm, Finset.mem_univ k⟩
    conv_lhs => rw [← Finset.insert_erase hkl]
    rw [Finset.prod_insert (by simp)]
    congr 1
    refine Finset.prod_congr rfl (fun j hj => ?_)
    rw [Finset.mem_erase, Finset.mem_erase] at hj
    rw [hu_zero2 B l k hlk hB j hj.2.1 hj.1, Nat.sub_zero]
  have hpair : ∀ e ∈ E,
      (∑ B ∈ ((Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S)).filter
          (fun B => ∃ (l k : Fin t), l ≠ k ∧ ({l, k} : Finset (Fin t)) = e ∧
              B ⊆ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l) ∪
                  (Finset.univ : Finset (Fin n)).filter (fun i => lab i = k) ∧
                (B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l)).Nonempty ∧
                (B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = k)).Nonempty),
          w B * ∏ j : Fin t,
            Φ ((S.filter (fun i => lab i = j)).card - (B.filter (fun i => lab i = j)).card))
        ≤ (B0 ^ 2 / 2) * ∏ j : Fin t, Φ ((S.filter (fun i => lab i = j)).card) := by
    intro e he
    obtain ⟨l0, k0, hlk0, heq⟩ := Finset.card_eq_two.mp (hE e he)
    have hFam : ((Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S)).filter
          (fun B => ∃ (l k : Fin t), l ≠ k ∧ ({l, k} : Finset (Fin t)) = e ∧
              B ⊆ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l) ∪
                  (Finset.univ : Finset (Fin n)).filter (fun i => lab i = k) ∧
                (B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l)).Nonempty ∧
                (B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = k)).Nonempty)
        = ((Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S)).filter
          (fun B => B ⊆ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l0) ∪
                (Finset.univ : Finset (Fin n)).filter (fun i => lab i = k0) ∧
              (B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l0)).Nonempty ∧
              (B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = k0)).Nonempty) := by
      ext B
      constructor
      · intro hB
        obtain ⟨hBI, hrest⟩ := Finset.mem_filter.mp hB
        obtain ⟨l, k, hlk, hkeq, hsub, hne1, hne2⟩ := hrest
        have hkk : ({l, k} : Finset (Fin t)) = {l0, k0} := hkeq.trans heq
        have hcase : (l = l0 ∧ k = k0) ∨ (l = k0 ∧ k = l0) := by
          have hl : l = l0 ∨ l = k0 := by
            have h' : l ∈ ({l0, k0} : Finset (Fin t)) := by rw [← hkk]; simp
            simpa only [Finset.mem_insert, Finset.mem_singleton] using h'
          have hk : k = l0 ∨ k = k0 := by
            have h' : k ∈ ({l0, k0} : Finset (Fin t)) := by rw [← hkk]; simp
            simpa only [Finset.mem_insert, Finset.mem_singleton] using h'
          rcases hl with h1 | h1 <;> rcases hk with h2 | h2
          · exact absurd (h1.trans h2.symm) hlk
          · exact Or.inl ⟨h1, h2⟩
          · exact Or.inr ⟨h1, h2⟩
          · exact absurd (h1.trans h2.symm) hlk
        rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Finset.mem_filter.mpr ⟨hBI, hsub, hne1, hne2⟩
        · exact Finset.mem_filter.mpr ⟨hBI, by rw [Finset.union_comm]; exact hsub, hne2, hne1⟩
      · intro hB
        obtain ⟨hBI, hsub, hne1, hne2⟩ := Finset.mem_filter.mp hB
        exact Finset.mem_filter.mpr ⟨hBI, l0, k0, hlk0, heq.symm, hsub, hne1, hne2⟩
    rw [hFam]
    have hT : ∀ l : Fin t,
        (∑ A ∈ (S.filter (fun i => lab i = l)).powerset.filter (fun A => A.Nonempty),
          (A.card.factorial : ℝ) * (kappa ^ A.card / Real.sqrt (A.card : ℝ)) *
            Φ ((S.filter (fun i => lab i = l)).card - A.card))
          ≤ 9 * H * Φ ((S.filter (fun i => lab i = l)).card) := by
      intro l
      have hc := hcount (S.filter (fun i => lab i = l))
        (fun a => (a.factorial : ℝ) * (kappa ^ a / Real.sqrt (a : ℝ)) *
          Φ ((S.filter (fun i => lab i = l)).card - a)) (by simp)
      rw [hc]
      have hcongr : (∑ a ∈ Finset.range ((S.filter (fun i => lab i = l)).card + 1),
            ((S.filter (fun i => lab i = l)).card.choose a : ℝ) *
              ((a.factorial : ℝ) * (kappa ^ a / Real.sqrt (a : ℝ)) *
                Φ ((S.filter (fun i => lab i = l)).card - a)))
          = ∑ a ∈ Finset.range ((S.filter (fun i => lab i = l)).card + 1),
              (((S.filter (fun i => lab i = l)).card.choose a : ℝ) *
                (a.factorial : ℝ) * (kappa ^ a / Real.sqrt (a : ℝ)) *
                  Φ ((S.filter (fun i => lab i = l)).card - a)) := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        ring
      rw [hcongr]
      rcases Nat.eq_zero_or_pos ((S.filter (fun i => lab i = l)).card) with h0 | h1
      · have hzero : (∑ a ∈ Finset.range ((S.filter (fun i => lab i = l)).card + 1),
            (((S.filter (fun i => lab i = l)).card.choose a : ℝ) *
              (a.factorial : ℝ) * (kappa ^ a / Real.sqrt (a : ℝ)) *
                Φ ((S.filter (fun i => lab i = l)).card - a))) = 0 := by
          rw [h0]
          rw [Finset.sum_range_succ]
          simp
        rw [hzero]
        exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (le_of_lt (hΦpos _))
      · exact hA _ h1
    set Cl : Finset (Fin n) := (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l0) with hCl
    set Ck : Finset (Fin n) := (Finset.univ : Finset (Fin n)).filter (fun i => lab i = k0) with hCk
    let Pr : ℝ := ∏ j ∈ ((Finset.univ : Finset (Fin t)).erase l0).erase k0,
      Φ ((S.filter (fun i => lab i = j)).card)
    have hPrn : (0 : ℝ) ≤ Pr := Finset.prod_nonneg (fun j _ => (hΦpos _).le)
    have hE0 : ({l0, k0} : Finset (Fin t)) ∈ E := heq ▸ he
    have hinter : ∀ (B : Finset (Fin n)) (j : Fin t),
        B.filter (fun i => lab i = j)
          = B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = j) := by
      intro B j
      ext x
      simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_univ, true_and]
    have hbd : ∀ B ∈ ((Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S)).filter
          (fun B => B ⊆ Cl ∪ Ck ∧ (B ∩ Cl).Nonempty ∧ (B ∩ Ck).Nonempty),
        w B * ∏ j : Fin t,
            Φ ((S.filter (fun i => lab i = j)).card - (B.filter (fun i => lab i = j)).card)
          ≤ Pr * ((1 / 2) *
              (((B ∩ Cl).card.factorial : ℝ) *
                  (kappa ^ (B ∩ Cl).card / Real.sqrt ((B ∩ Cl).card : ℝ)) *
                Φ ((S.filter (fun i => lab i = l0)).card - (B ∩ Cl).card)) *
              (((B ∩ Ck).card.factorial : ℝ) *
                  (kappa ^ (B ∩ Ck).card / Real.sqrt ((B ∩ Ck).card : ℝ)) *
                Φ ((S.filter (fun i => lab i = k0)).card - (B ∩ Ck).card))) := by
      intro B hB
      obtain ⟨hBI, hsub, hpne, hqne⟩ := Finset.mem_filter.mp hB
      have hBn : B.Nonempty := (Finset.mem_filter.mp hBI).2.1
      have hp1 : 1 ≤ (B ∩ Cl).card := by
        obtain ⟨x, hx⟩ := hpne
        have h1 : ({x} : Finset (Fin n)).card ≤ (B ∩ Cl).card :=
          Finset.card_le_card (by
            intro y hy
            rw [Finset.mem_singleton] at hy
            subst hy
            exact hx)
        simpa using h1
      have hq1 : 1 ≤ (B ∩ Ck).card := by
        obtain ⟨x, hx⟩ := hqne
        have h1 : ({x} : Finset (Fin n)).card ≤ (B ∩ Ck).card :=
          Finset.card_le_card (by
            intro y hy
            rw [Finset.mem_singleton] at hy
            subst hy
            exact hx)
        simpa using h1
      have hpq : (0 : ℝ) <
          (((B ∩ Cl).card.factorial : ℝ) * ((B ∩ Ck).card.factorial : ℝ)) := by
        have h1 : (0 : ℝ) < ((B ∩ Cl).card.factorial : ℝ) := by
          exact_mod_cast Nat.factorial_pos _
        have h2 : (0 : ℝ) < ((B ∩ Ck).card.factorial : ℝ) := by
          exact_mod_cast Nat.factorial_pos _
        exact mul_pos h1 h2
      have hw := hcross B l0 k0 hlk0 hE0 hBn hsub hpne hqne
      have hw' : w B ≤ (kappa ^ ((B ∩ Cl).card + (B ∩ Ck).card) /
            ((((B ∩ Cl).card + (B ∩ Ck).card : ℕ)) : ℝ)) *
          (((B ∩ Cl).card.factorial : ℝ) * ((B ∩ Ck).card.factorial : ℝ)) := by
        have h2 : w B = (w B / (((B ∩ Cl).card.factorial : ℝ) *
            ((B ∩ Ck).card.factorial : ℝ))) *
            (((B ∩ Cl).card.factorial : ℝ) * ((B ∩ Ck).card.factorial : ℝ)) :=
          (div_mul_cancel₀ _ (ne_of_gt hpq)).symm
        rw [h2]
        exact mul_le_mul_of_nonneg_right hw (le_of_lt hpq)
      have hfac2 := hfac (B ∩ Cl).card (B ∩ Ck).card hp1 hq1
      have hstep : w B *
            (Φ ((S.filter (fun i => lab i = l0)).card - (B ∩ Cl).card) *
              Φ ((S.filter (fun i => lab i = k0)).card - (B ∩ Ck).card))
          ≤ (1 / 2) *
              (((B ∩ Cl).card.factorial : ℝ) *
                  (kappa ^ (B ∩ Cl).card / Real.sqrt ((B ∩ Cl).card : ℝ)) *
                Φ ((S.filter (fun i => lab i = l0)).card - (B ∩ Cl).card)) *
              (((B ∩ Ck).card.factorial : ℝ) *
                  (kappa ^ (B ∩ Ck).card / Real.sqrt ((B ∩ Ck).card : ℝ)) *
                Φ ((S.filter (fun i => lab i = k0)).card - (B ∩ Ck).card)) := by
        have hΦn1 : (0 : ℝ) ≤ Φ ((S.filter (fun i => lab i = l0)).card - (B ∩ Cl).card) :=
          (hΦpos _).le
        have hΦn2 : (0 : ℝ) ≤ Φ ((S.filter (fun i => lab i = k0)).card - (B ∩ Ck).card) :=
          (hΦpos _).le
        have step1 : w B *
              (Φ ((S.filter (fun i => lab i = l0)).card - (B ∩ Cl).card) *
                Φ ((S.filter (fun i => lab i = k0)).card - (B ∩ Ck).card))
            ≤ ((kappa ^ ((B ∩ Cl).card + (B ∩ Ck).card) /
                  ((((B ∩ Cl).card + (B ∩ Ck).card : ℕ)) : ℝ)) *
                (((B ∩ Cl).card.factorial : ℝ) * ((B ∩ Ck).card.factorial : ℝ))) *
              (Φ ((S.filter (fun i => lab i = l0)).card - (B ∩ Cl).card) *
                Φ ((S.filter (fun i => lab i = k0)).card - (B ∩ Ck).card)) :=
          mul_le_mul_of_nonneg_right hw' (mul_nonneg hΦn1 hΦn2)
        have step2 : ((kappa ^ ((B ∩ Cl).card + (B ∩ Ck).card) /
                  ((((B ∩ Cl).card + (B ∩ Ck).card : ℕ)) : ℝ)) *
                (((B ∩ Cl).card.factorial : ℝ) * ((B ∩ Ck).card.factorial : ℝ))) *
              (Φ ((S.filter (fun i => lab i = l0)).card - (B ∩ Cl).card) *
                Φ ((S.filter (fun i => lab i = k0)).card - (B ∩ Ck).card))
            ≤ (((kappa ^ (B ∩ Cl).card / Real.sqrt ((B ∩ Cl).card : ℝ)) *
                  (kappa ^ (B ∩ Ck).card / Real.sqrt ((B ∩ Ck).card : ℝ)) / 2) *
                (((B ∩ Cl).card.factorial : ℝ) * ((B ∩ Ck).card.factorial : ℝ))) *
              (Φ ((S.filter (fun i => lab i = l0)).card - (B ∩ Cl).card) *
                Φ ((S.filter (fun i => lab i = k0)).card - (B ∩ Ck).card)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hfac2 (le_of_lt hpq)) (mul_nonneg hΦn1 hΦn2)
        have step3 : (((kappa ^ (B ∩ Cl).card / Real.sqrt ((B ∩ Cl).card : ℝ)) *
                  (kappa ^ (B ∩ Ck).card / Real.sqrt ((B ∩ Ck).card : ℝ)) / 2) *
                (((B ∩ Cl).card.factorial : ℝ) * ((B ∩ Ck).card.factorial : ℝ))) *
              (Φ ((S.filter (fun i => lab i = l0)).card - (B ∩ Cl).card) *
                Φ ((S.filter (fun i => lab i = k0)).card - (B ∩ Ck).card))
            = (1 / 2) *
              (((B ∩ Cl).card.factorial : ℝ) *
                  (kappa ^ (B ∩ Cl).card / Real.sqrt ((B ∩ Cl).card : ℝ)) *
                Φ ((S.filter (fun i => lab i = l0)).card - (B ∩ Cl).card)) *
              (((B ∩ Ck).card.factorial : ℝ) *
                  (kappa ^ (B ∩ Ck).card / Real.sqrt ((B ∩ Ck).card : ℝ)) *
                Φ ((S.filter (fun i => lab i = k0)).card - (B ∩ Ck).card)) := by
          ring
        exact le_trans step1 (le_trans step2 (le_of_eq step3))
      have hg : w B * ∏ j : Fin t,
            Φ ((S.filter (fun i => lab i = j)).card - (B.filter (fun i => lab i = j)).card)
          = Pr * (w B *
              (Φ ((S.filter (fun i => lab i = l0)).card - (B ∩ Cl).card) *
                Φ ((S.filter (fun i => lab i = k0)).card - (B ∩ Ck).card))) := by
        rw [hprod2 B l0 k0 hlk0 hsub, hinter B l0, hinter B k0]
        ring
      rw [hg]
      exact mul_le_mul_of_nonneg_left hstep hPrn
    let X : Finset (Fin n) → ℝ := fun A =>
      (A.card.factorial : ℝ) * (kappa ^ A.card / Real.sqrt (A.card : ℝ)) *
        Φ ((S.filter (fun i => lab i = l0)).card - A.card)
    let Y : Finset (Fin n) → ℝ := fun A =>
      (A.card.factorial : ℝ) * (kappa ^ A.card / Real.sqrt (A.card : ℝ)) *
        Φ ((S.filter (fun i => lab i = k0)).card - A.card)
    let Pl : Finset (Finset (Fin n)) :=
      (S.filter (fun i => lab i = l0)).powerset.filter (fun A => A.Nonempty)
    let Pk : Finset (Finset (Fin n)) :=
      (S.filter (fun i => lab i = k0)).powerset.filter (fun A => A.Nonempty)
    have hSAn : (0 : ℝ) ≤ ∑ A ∈ Pl, X A :=
      Finset.sum_nonneg (fun A _ => mul_nonneg
        (mul_nonneg (by positivity) (div_nonneg (pow_nonneg hkappa_nonneg _) (Real.sqrt_nonneg _)))
        (hΦpos _).le)
    have hSBn : (0 : ℝ) ≤ ∑ A ∈ Pk, Y A :=
      Finset.sum_nonneg (fun A _ => mul_nonneg
        (mul_nonneg (by positivity) (div_nonneg (pow_nonneg hkappa_nonneg _) (Real.sqrt_nonneg _)))
        (hΦpos _).le)
    have hSA : (∑ A ∈ Pl, X A) ≤ 9 * H * Φ ((S.filter (fun i => lab i = l0)).card) := hT l0
    have hSB : (∑ A ∈ Pk, Y A) ≤ 9 * H * Φ ((S.filter (fun i => lab i = k0)).card) := hT k0
    have hPrEq : (∏ j : Fin t, Φ ((S.filter (fun i => lab i = j)).card))
        = Φ ((S.filter (fun i => lab i = l0)).card) *
          (Φ ((S.filter (fun i => lab i = k0)).card) * Pr) := by
      conv_lhs => rw [← Finset.insert_erase (Finset.mem_univ l0)]
      rw [Finset.prod_insert (by simp)]
      congr 1
      conv_lhs => rw [← Finset.insert_erase (show k0 ∈ (Finset.univ : Finset (Fin t)).erase l0 from by
        rw [Finset.mem_erase]
        exact ⟨hlk0.symm, Finset.mem_univ k0⟩)]
      rw [Finset.prod_insert (by simp)]
    have hcore : (∑ B ∈ ((Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S)).filter
          (fun B => B ⊆ Cl ∪ Ck ∧ (B ∩ Cl).Nonempty ∧ (B ∩ Ck).Nonempty),
          X (B ∩ Cl) * Y (B ∩ Ck)) ≤ (∑ A ∈ Pl, X A) * (∑ A ∈ Pk, Y A) := by
      have hPl : ∀ B ∈ ((Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S)).filter
            (fun B => B ⊆ Cl ∪ Ck ∧ (B ∩ Cl).Nonempty ∧ (B ∩ Ck).Nonempty), B ∩ Cl ∈ Pl := by
        intro B hB
        obtain ⟨hBI, hsub, hne1, hne2⟩ := Finset.mem_filter.mp hB
        have hBS : B ⊆ S := (Finset.mem_filter.mp hBI).2.2
        refine Finset.mem_filter.mpr ⟨?_, hne1⟩
        rw [Finset.mem_powerset]
        intro x hx
        rw [Finset.mem_inter] at hx
        have hxl : lab x = l0 := by
          have h2 : x ∈ Cl := hx.2
          rw [hCl] at h2
          exact (Finset.mem_filter.mp h2).2
        exact Finset.mem_filter.mpr ⟨hBS hx.1, hxl⟩
      have hPk : ∀ B ∈ ((Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S)).filter
            (fun B => B ⊆ Cl ∪ Ck ∧ (B ∩ Cl).Nonempty ∧ (B ∩ Ck).Nonempty), B ∩ Ck ∈ Pk := by
        intro B hB
        obtain ⟨hBI, hsub, hne1, hne2⟩ := Finset.mem_filter.mp hB
        have hBS : B ⊆ S := (Finset.mem_filter.mp hBI).2.2
        refine Finset.mem_filter.mpr ⟨?_, hne2⟩
        rw [Finset.mem_powerset]
        intro x hx
        rw [Finset.mem_inter] at hx
        have hxl : lab x = k0 := by
          have h2 : x ∈ Ck := hx.2
          rw [hCk] at h2
          exact (Finset.mem_filter.mp h2).2
        exact Finset.mem_filter.mpr ⟨hBS hx.1, hxl⟩
      have hcov : ∀ B ∈ ((Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S)).filter
            (fun B => B ⊆ Cl ∪ Ck ∧ (B ∩ Cl).Nonempty ∧ (B ∩ Ck).Nonempty),
          B = (B ∩ Cl) ∪ (B ∩ Ck) := by
        intro B hB
        have hsub : B ⊆ Cl ∪ Ck := (Finset.mem_filter.mp hB).2.1
        ext x
        constructor
        · intro hx
          rcases Finset.mem_union.mp (hsub hx) with h | h
          · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hx, h⟩))
          · exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨hx, h⟩))
        · intro hx
          rcases Finset.mem_union.mp hx with h | h
          · exact (Finset.mem_inter.mp h).1
          · exact (Finset.mem_inter.mp h).1
      have hfiber : ∀ A A' : Finset (Fin n),
          ((((Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S)).filter
            (fun B => B ⊆ Cl ∪ Ck ∧ (B ∩ Cl).Nonempty ∧ (B ∩ Ck).Nonempty)).filter
            (fun B => B ∩ Cl = A ∧ B ∩ Ck = A')).card ≤ 1 := by
        intro A A'
        have hsub : ((((Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S)).filter
            (fun B => B ⊆ Cl ∪ Ck ∧ (B ∩ Cl).Nonempty ∧ (B ∩ Ck).Nonempty)).filter
            (fun B => B ∩ Cl = A ∧ B ∩ Ck = A')) ⊆ {A ∪ A'} := by
          intro B hB
          obtain ⟨hBfam, hBA, hBA'⟩ := Finset.mem_filter.mp hB
          rw [Finset.mem_singleton]
          rw [hcov B hBfam, hBA, hBA']
        have h1 := Finset.card_le_card hsub
        simpa using h1
      have hXn : ∀ A : Finset (Fin n), (0 : ℝ) ≤ X A := fun A =>
        mul_nonneg
          (mul_nonneg (by positivity)
            (div_nonneg (pow_nonneg hkappa_nonneg _) (Real.sqrt_nonneg _)))
          (hΦpos _).le
      have hYn : ∀ A : Finset (Fin n), (0 : ℝ) ≤ Y A := fun A =>
        mul_nonneg
          (mul_nonneg (by positivity)
            (div_nonneg (pow_nonneg hkappa_nonneg _) (Real.sqrt_nonneg _)))
          (hΦpos _).le
      let FAM : Finset (Finset (Fin n)) :=
        ((Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S)).filter
          (fun B => B ⊆ Cl ∪ Ck ∧ (B ∩ Cl).Nonempty ∧ (B ∩ Ck).Nonempty)
      have hexp : ∀ B ∈ FAM,
          (∑ A ∈ Pl, ∑ A' ∈ Pk,
            (if B ∩ Cl = A ∧ B ∩ Ck = A' then X A * Y A' else 0))
            = X (B ∩ Cl) * Y (B ∩ Ck) := by
        intro B hB
        have hBPl : B ∩ Cl ∈ Pl := hPl B hB
        have hBPk : B ∩ Ck ∈ Pk := hPk B hB
        have hinner : ∀ A : Finset (Fin n),
            (∑ A' ∈ Pk, (if B ∩ Cl = A ∧ B ∩ Ck = A' then X A * Y A' else 0))
              = (if B ∩ Cl = A then X A * Y (B ∩ Ck) else 0) := by
          intro A
          by_cases hA : B ∩ Cl = A
          · rw [if_pos hA]
            rw [← Finset.sum_filter]
            have hf : Pk.filter (fun A' => B ∩ Cl = A ∧ B ∩ Ck = A') = {B ∩ Ck} := by
              ext a
              simp only [Finset.mem_filter, Finset.mem_singleton]
              exact ⟨fun h => h.2.2.symm, fun h => ⟨by rw [h]; exact hBPk, hA, h.symm⟩⟩
            rw [hf]
            simp
          · rw [if_neg hA]
            refine Finset.sum_eq_zero (fun A' _ => ?_)
            rw [if_neg (fun hcon => hA hcon.1)]
        have hcg : (∑ A ∈ Pl, ∑ A' ∈ Pk,
              (if B ∩ Cl = A ∧ B ∩ Ck = A' then X A * Y A' else 0))
            = ∑ A ∈ Pl, (if B ∩ Cl = A then X A * Y (B ∩ Ck) else 0) :=
          Finset.sum_congr rfl (fun A _ => hinner A)
        rw [hcg]
        rw [← Finset.sum_filter]
        have hf2 : Pl.filter (fun A => B ∩ Cl = A) = {B ∩ Cl} := by
          ext a
          simp only [Finset.mem_filter, Finset.mem_singleton]
          exact ⟨fun h => h.2.symm, fun h => ⟨by rw [h]; exact hBPl, h.symm⟩⟩
        rw [hf2]
        simp
      have hmain : (∑ B ∈ FAM, X (B ∩ Cl) * Y (B ∩ Ck))
          ≤ (∑ A ∈ Pl, X A) * (∑ A' ∈ Pk, Y A') := by
        rw [Finset.sum_mul_sum]
        calc (∑ B ∈ FAM, X (B ∩ Cl) * Y (B ∩ Ck))
            = ∑ B ∈ FAM, ∑ A ∈ Pl, ∑ A' ∈ Pk,
                (if B ∩ Cl = A ∧ B ∩ Ck = A' then X A * Y A' else 0) :=
              Finset.sum_congr rfl (fun B hB => (hexp B hB).symm)
          _ = ∑ A ∈ Pl, ∑ B ∈ FAM, ∑ A' ∈ Pk,
                (if B ∩ Cl = A ∧ B ∩ Ck = A' then X A * Y A' else 0) := Finset.sum_comm
          _ = ∑ A ∈ Pl, ∑ A' ∈ Pk, ∑ B ∈ FAM,
                (if B ∩ Cl = A ∧ B ∩ Ck = A' then X A * Y A' else 0) :=
              Finset.sum_congr rfl (fun A _ => Finset.sum_comm)
          _ ≤ ∑ A ∈ Pl, ∑ A' ∈ Pk, X A * Y A' := by
              refine Finset.sum_le_sum (fun A _ => Finset.sum_le_sum (fun A' _ => ?_))
              rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
              have hcard : (((FAM.filter (fun B => B ∩ Cl = A ∧ B ∩ Ck = A')).card : ℕ) : ℝ) ≤ 1 := by
                have h0 : (FAM.filter (fun B => B ∩ Cl = A ∧ B ∩ Ck = A')).card ≤ 1 := hfiber A A'
                exact_mod_cast h0
              have hnn : (0 : ℝ) ≤ X A * Y A' := mul_nonneg (hXn A) (hYn A')
              calc (((FAM.filter (fun B => B ∩ Cl = A ∧ B ∩ Ck = A')).card : ℕ) : ℝ) * (X A * Y A')
                  ≤ 1 * (X A * Y A') := mul_le_mul_of_nonneg_right hcard hnn
                _ = X A * Y A' := one_mul (X A * Y A')
      exact hmain
    refine le_trans (Finset.sum_le_sum hbd) ?_
    have hpr1 : (∑ B ∈ ((Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S)).filter
          (fun B => B ⊆ Cl ∪ Ck ∧ (B ∩ Cl).Nonempty ∧ (B ∩ Ck).Nonempty),
          Pr * ((1 / 2) * X (B ∩ Cl) * Y (B ∩ Ck)))
        = Pr * ∑ B ∈ ((Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S)).filter
          (fun B => B ⊆ Cl ∪ Ck ∧ (B ∩ Cl).Nonempty ∧ (B ∩ Ck).Nonempty),
          ((1 / 2) * X (B ∩ Cl) * Y (B ∩ Ck)) := by
      rw [Finset.mul_sum]
    rw [hpr1]
    have hpr2 : (∑ B ∈ ((Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S)).filter
          (fun B => B ⊆ Cl ∪ Ck ∧ (B ∩ Cl).Nonempty ∧ (B ∩ Ck).Nonempty),
          ((1 / 2) * X (B ∩ Cl) * Y (B ∩ Ck)))
        = (1 / 2) * ∑ B ∈ ((Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S)).filter
          (fun B => B ⊆ Cl ∪ Ck ∧ (B ∩ Cl).Nonempty ∧ (B ∩ Ck).Nonempty),
          X (B ∩ Cl) * Y (B ∩ Ck) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun B _ => ?_)
      ring
    rw [hpr2]
    have hstep1 : (1 / 2) * (∑ B ∈ ((Finset.univ : Finset (Finset (Fin n))).filter
          (fun B => B.Nonempty ∧ B ⊆ S)).filter
          (fun B => B ⊆ Cl ∪ Ck ∧ (B ∩ Cl).Nonempty ∧ (B ∩ Ck).Nonempty),
          X (B ∩ Cl) * Y (B ∩ Ck))
        ≤ (1 / 2) * ((∑ A ∈ Pl, X A) * (∑ A ∈ Pk, Y A)) :=
      mul_le_mul_of_nonneg_left hcore (by norm_num)
    refine le_trans (mul_le_mul_of_nonneg_left hstep1 hPrn) ?_
    have hstep2 : Pr * ((1 / 2) * ((∑ A ∈ Pl, X A) * (∑ A ∈ Pk, Y A)))
        ≤ Pr * ((1 / 2) * ((9 * H * Φ ((S.filter (fun i => lab i = l0)).card)) *
            (9 * H * Φ ((S.filter (fun i => lab i = k0)).card)))) := by
      refine mul_le_mul_of_nonneg_left ?_ hPrn
      have hprod : (∑ A ∈ Pl, X A) * (∑ A ∈ Pk, Y A)
          ≤ (9 * H * Φ ((S.filter (fun i => lab i = l0)).card)) *
            (9 * H * Φ ((S.filter (fun i => lab i = k0)).card)) :=
        mul_le_mul hSA hSB hSBn
          (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (hΦpos _).le)
      exact mul_le_mul_of_nonneg_left hprod (by norm_num)
    refine le_trans hstep2 ?_
    rw [hPrEq]
    have hH2 : (81 : ℝ) * H ^ 2 ≤ B0 ^ 2 := by
      have h1 : (81 : ℝ) ≤ C0 ^ 2 := by nlinarith [hC0nine]
      rw [hB0]
      nlinarith [h1, sq_nonneg H, hHge]
    have hcoef : (81 / 2 : ℝ) * H ^ 2 ≤ B0 ^ 2 / 2 := by linarith
    have hfac2 : (0 : ℝ) ≤ Φ ((S.filter (fun i => lab i = l0)).card) *
        (Φ ((S.filter (fun i => lab i = k0)).card) * Pr) :=
      mul_nonneg (hΦpos _).le (mul_nonneg (hΦpos _).le hPrn)
    have heq1 : Pr * ((1 / 2) * ((9 * H * Φ ((S.filter (fun i => lab i = l0)).card)) *
          (9 * H * Φ ((S.filter (fun i => lab i = k0)).card))))
        = ((81 / 2) * H ^ 2) * (Φ ((S.filter (fun i => lab i = l0)).card) *
            (Φ ((S.filter (fun i => lab i = k0)).card) * Pr)) := by
      ring
    rw [heq1]
    exact mul_le_mul_of_nonneg_right hcoef hfac2
  have hcover : ∀ B ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S),
      w B * ∏ j : Fin t, Φ ((S.filter (fun i => lab i = j)).card - (B.filter (fun i => lab i = j)).card)
        ≤ (∑ l : Fin t, (if B ⊆ S.filter (fun i => lab i = l) then
              w B * ∏ j : Fin t,
                Φ ((S.filter (fun i => lab i = j)).card - (B.filter (fun i => lab i = j)).card) else 0))
          + (∑ e ∈ E, (if ∃ (l k : Fin t), l ≠ k ∧ ({l, k} : Finset (Fin t)) = e ∧
              B ⊆ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l) ∪
                  (Finset.univ : Finset (Fin n)).filter (fun i => lab i = k) ∧
                (B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l)).Nonempty ∧
                (B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = k)).Nonempty then
              w B * ∏ j : Fin t,
                Φ ((S.filter (fun i => lab i = j)).card - (B.filter (fun i => lab i = j)).card) else 0)) := by
    intro B hB
    obtain ⟨hBn, hBS⟩ := (Finset.mem_filter.mp hB).2
    have hFnn : (0 : ℝ) ≤ w B * ∏ j : Fin t,
        Φ ((S.filter (fun i => lab i = j)).card - (B.filter (fun i => lab i = j)).card) :=
      hf_nonneg B hB
    have hnn2 : (0 : ℝ) ≤ ∑ e ∈ E, (if ∃ (l k : Fin t), l ≠ k ∧ ({l, k} : Finset (Fin t)) = e ∧
        B ⊆ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l) ∪
            (Finset.univ : Finset (Fin n)).filter (fun i => lab i = k) ∧
          (B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l)).Nonempty ∧
          (B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = k)).Nonempty then
        w B * ∏ j : Fin t,
          Φ ((S.filter (fun i => lab i = j)).card - (B.filter (fun i => lab i = j)).card) else 0) :=
      Finset.sum_nonneg (fun e _ => by
        split_ifs with h
        · exact hFnn
        · exact le_refl 0)
    by_cases hpureB : ∃ l : Fin t, B ⊆ S.filter (fun i => lab i = l)
    · obtain ⟨l0, hl0⟩ := hpureB
      have hnon : ∀ l : Fin t,
          (0 : ℝ) ≤ (if B ⊆ S.filter (fun i => lab i = l) then
              w B * ∏ j : Fin t,
                Φ ((S.filter (fun i => lab i = j)).card - (B.filter (fun i => lab i = j)).card) else 0) := by
        intro l
        by_cases h : B ⊆ S.filter (fun i => lab i = l)
        · rw [if_pos h]; exact hFnn
        · rw [if_neg h]
      have h1 : w B * ∏ j : Fin t,
          Φ ((S.filter (fun i => lab i = j)).card - (B.filter (fun i => lab i = j)).card)
          ≤ ∑ l : Fin t, (if B ⊆ S.filter (fun i => lab i = l) then
              w B * ∏ j : Fin t,
                Φ ((S.filter (fun i => lab i = j)).card - (B.filter (fun i => lab i = j)).card) else 0) := by
        have hgood := Finset.single_le_sum (s := (Finset.univ : Finset (Fin t)))
          (f := fun l : Fin t => if B ⊆ S.filter (fun i => lab i = l) then
              w B * ∏ j : Fin t,
                Φ ((S.filter (fun i => lab i = j)).card - (B.filter (fun i => lab i = j)).card) else 0)
          (fun l _ => hnon l) (Finset.mem_univ l0)
        simpa only [if_pos hl0] using hgood
      exact le_trans h1 (le_add_of_nonneg_right hnn2)
    · push_neg at hpureB
      have hpureC : ∀ l : Fin t,
          ¬ B ⊆ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l) := by
        intro l hBl
        exact hpureB l (fun x hx =>
          Finset.mem_filter.mpr ⟨hBS hx, (Finset.mem_filter.mp (hBl hx)).2⟩)
      have hz : (∑ l : Fin t, (if B ⊆ S.filter (fun i => lab i = l) then
            w B * ∏ j : Fin t,
              Φ ((S.filter (fun i => lab i = j)).card - (B.filter (fun i => lab i = j)).card) else 0)) = 0 := by
        refine Finset.sum_eq_zero (fun l _ => ?_)
        rw [if_neg (hpureB l)]
      rw [hz, zero_add]
      by_cases hcrossB : ∃ (l k : Fin t), l ≠ k ∧ ({l, k} : Finset (Fin t)) ∈ E ∧
          B ⊆ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l) ∪
              (Finset.univ : Finset (Fin n)).filter (fun i => lab i = k) ∧
            (B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l)).Nonempty ∧
            (B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = k)).Nonempty
      · obtain ⟨l0, k0, hne, hE0, hsub, hne1, hne2⟩ := hcrossB
        have hnon2 : ∀ e : Finset (Fin t),
            (0 : ℝ) ≤ (if ∃ (l k : Fin t), l ≠ k ∧ ({l, k} : Finset (Fin t)) = e ∧
                B ⊆ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l) ∪
                    (Finset.univ : Finset (Fin n)).filter (fun i => lab i = k) ∧
                  (B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l)).Nonempty ∧
                  (B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = k)).Nonempty then
              w B * ∏ j : Fin t,
                Φ ((S.filter (fun i => lab i = j)).card - (B.filter (fun i => lab i = j)).card) else 0) := by
          intro e
          by_cases h : ∃ (l k : Fin t), l ≠ k ∧ ({l, k} : Finset (Fin t)) = e ∧
              B ⊆ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l) ∪
                  (Finset.univ : Finset (Fin n)).filter (fun i => lab i = k) ∧
                (B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l)).Nonempty ∧
                (B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = k)).Nonempty
          · rw [if_pos h]; exact hFnn
          · rw [if_neg h]
        have hwit : ∃ (l k : Fin t), l ≠ k ∧ ({l, k} : Finset (Fin t)) = {l0, k0} ∧
            B ⊆ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l) ∪
                (Finset.univ : Finset (Fin n)).filter (fun i => lab i = k) ∧
              (B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l)).Nonempty ∧
              (B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = k)).Nonempty :=
          ⟨l0, k0, hne, rfl, hsub, hne1, hne2⟩
        have hgood2 := Finset.single_le_sum (s := E)
          (f := fun e : Finset (Fin t) => if ∃ (l k : Fin t), l ≠ k ∧ ({l, k} : Finset (Fin t)) = e ∧
              B ⊆ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l) ∪
                  (Finset.univ : Finset (Fin n)).filter (fun i => lab i = k) ∧
                (B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l)).Nonempty ∧
                (B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = k)).Nonempty then
              w B * ∏ j : Fin t,
                Φ ((S.filter (fun i => lab i = j)).card - (B.filter (fun i => lab i = j)).card) else 0)
          (fun e _ => hnon2 e) hE0
        simpa only [if_pos hwit] using hgood2
      · have hw0 : w B = 0 :=
          hother B hBn hpureC (fun l k hlk hElk hconj =>
            hcrossB ⟨l, k, hlk, hElk, hconj.1, hconj.2.1, hconj.2.2⟩)
        have hL : w B * ∏ j : Fin t,
            Φ ((S.filter (fun i => lab i = j)).card - (B.filter (fun i => lab i = j)).card) = 0 := by
          rw [hw0, zero_mul]
        exact le_trans (le_of_eq hL) hnn2
  let I : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S)
  let g : Finset (Fin n) → ℝ := fun B =>
    w B * ∏ j : Fin t,
      Φ ((S.filter (fun i => lab i = j)).card - (B.filter (fun i => lab i = j)).card)
  let P : ℝ := ∏ j : Fin t, Φ ((S.filter (fun i => lab i = j)).card)
  change (∑ B ∈ I, g B) ≤ P * K5
  let X : Finset (Fin t) → Finset (Fin n) → Prop := fun e B =>
    ∃ (l k : Fin t), l ≠ k ∧ ({l, k} : Finset (Fin t)) = e ∧
      B ⊆ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l) ∪
          (Finset.univ : Finset (Fin n)).filter (fun i => lab i = k) ∧
        (B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l)).Nonempty ∧
        (B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = k)).Nonempty
  have hcl : ∀ l : Fin t, (∑ B ∈ I.filter (fun B => B ⊆ S.filter (fun i => lab i = l)), g B)
      ≤ 9 * lam * P := fun l => hclass l
  have hpr : ∀ e ∈ E, (∑ B ∈ I.filter (X e), g B) ≤ (B0 ^ 2 / 2) * P := hpair
  have hcov' : ∀ B ∈ I,
      g B ≤ (∑ l : Fin t, (if B ⊆ S.filter (fun i => lab i = l) then g B else 0))
        + (∑ e ∈ E, (if X e B then g B else 0)) := hcover
  have eq1 : (∑ B ∈ I, ((∑ l : Fin t, (if B ⊆ S.filter (fun i => lab i = l) then g B else 0))
        + (∑ e ∈ E, (if X e B then g B else 0))))
      = (∑ l : Fin t, ∑ B ∈ I, (if B ⊆ S.filter (fun i => lab i = l) then g B else 0))
        + (∑ e ∈ E, ∑ B ∈ I, (if X e B then g B else 0)) := by
    rw [Finset.sum_add_distrib]
    congr 1
    · exact Finset.sum_comm
    · exact Finset.sum_comm
  have eq2 : (∑ l : Fin t, ∑ B ∈ I, (if B ⊆ S.filter (fun i => lab i = l) then g B else 0))
      = ∑ l : Fin t, ∑ B ∈ I.filter (fun B => B ⊆ S.filter (fun i => lab i = l)), g B := by
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [← Finset.sum_filter]
  have eq3 : (∑ e ∈ E, ∑ B ∈ I, (if X e B then g B else 0))
      = ∑ e ∈ E, ∑ B ∈ I.filter (X e), g B := by
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [← Finset.sum_filter]
  have b1 : (∑ l : Fin t, ∑ B ∈ I.filter (fun B => B ⊆ S.filter (fun i => lab i = l)), g B)
      ≤ ∑ l : Fin t, 9 * lam * P := Finset.sum_le_sum (fun l _ => hcl l)
  have b2 : (∑ e ∈ E, ∑ B ∈ I.filter (X e), g B) ≤ ∑ e ∈ E, (B0 ^ 2 / 2) * P :=
    Finset.sum_le_sum hpr
  have e1 : (∑ l : Fin t, 9 * lam * P) = (t : ℝ) * (9 * lam * P) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have e2 : (∑ e ∈ E, (B0 ^ 2 / 2) * P) = (E.card : ℝ) * ((B0 ^ 2 / 2) * P) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hB0ge : (9 : ℝ) ≤ B0 := by
    have hH0 : (0 : ℝ) ≤ H := by linarith
    rw [hB0]
    calc (9 : ℝ) ≤ C0 := hC0nine
      _ = C0 * 1 := (mul_one C0).symm
      _ ≤ C0 * H := mul_le_mul_of_nonneg_left hHge (by linarith)
  have hPpos : 0 < P := Finset.prod_pos (fun j _ => hΦpos _)
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  calc (∑ B ∈ I, g B)
      ≤ (∑ l : Fin t, ∑ B ∈ I, (if B ⊆ S.filter (fun i => lab i = l) then g B else 0))
          + (∑ e ∈ E, ∑ B ∈ I, (if X e B then g B else 0)) :=
        le_trans (Finset.sum_le_sum hcov') (le_of_eq eq1)
    _ = (∑ l : Fin t, ∑ B ∈ I.filter (fun B => B ⊆ S.filter (fun i => lab i = l)), g B)
          + (∑ e ∈ E, ∑ B ∈ I.filter (X e), g B) := by rw [eq2, eq3]
    _ ≤ (∑ l : Fin t, 9 * lam * P) + (∑ e ∈ E, (B0 ^ 2 / 2) * P) := add_le_add b1 b2
    _ = (t : ℝ) * (9 * lam * P) + (E.card : ℝ) * ((B0 ^ 2 / 2) * P) := by rw [e1, e2]
    _ ≤ P * (B0 * ((t : ℝ) * lam + B0 * (E.card : ℝ) / 2)) := by
        have h9 : (9 : ℝ) * ((t : ℝ) * lam * P) ≤ B0 * ((t : ℝ) * lam * P) :=
          mul_le_mul_of_nonneg_right hB0ge
            (le_of_lt (mul_pos (mul_pos htpos hlam) hPpos))
        nlinarith [h9]
    _ ≤ P * K5 := mul_le_mul_of_nonneg_left hK5main (le_of_lt hPpos)
  /- @proof-region region.target-node.session.933ddd5d81345fe8 end -/

end

end Statlib.Imported
end DPCompletedProof
