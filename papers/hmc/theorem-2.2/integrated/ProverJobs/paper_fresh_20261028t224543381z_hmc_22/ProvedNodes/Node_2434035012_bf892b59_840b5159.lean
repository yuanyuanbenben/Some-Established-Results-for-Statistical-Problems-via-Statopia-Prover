import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.Vocabulary
import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.Base

namespace PaperProofTasks.paper_fresh_20261028t224543381z_hmc_22

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open _root_.PaperProofTasks.paper_fresh_20261028t224543381z_hmc_22.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace Statlib.Imported
open _root_.Statlib

set_option autoImplicit false in
theorem statopia_math_node_2434035012_bf892b59 : ∀ (d : ℕ) (U : HMCState d → ℝ)
    (hU : Differentiable ℝ U) (ε : ℝ) (x0 p0 : HMCState d),
    ((leapfrogFlow U ε 1 (x0, p0)).1 = x0 - (ε ^ 2 / 2) • gradient U x0 + ε • p0) ∧
    (∀ i : ℕ, 1 ≤ i →
      (leapfrogFlow U ε (i + 1) (x0, p0)).1 =
        2 • (leapfrogFlow U ε i (x0, p0)).1
          - (leapfrogFlow U ε (i - 1) (x0, p0)).1
          - ε ^ 2 • gradient U ((leapfrogFlow U ε i (x0, p0)).1)) ∧
    (∀ L : ℕ, 1 ≤ L →
      (leapfrogFlow U ε L (x0, p0)).2 =
        p0 - (ε / 2) • gradient U x0
          - ε • (∑ i ∈ Finset.Icc 1 (L - 1),
              gradient U ((leapfrogFlow U ε i (x0, p0)).1))
          - (ε / 2) • gradient U ((leapfrogFlow U ε L (x0, p0)).1)) ∧
    (∀ L : ℕ, 1 ≤ L →
      (leapfrogFlow U ε L (x0, p0)).1 =
        x0 - ((L : ℝ) * ε ^ 2 / 2) • gradient U x0
          - ε ^ 2 • (∑ i ∈ Finset.Icc 1 (L - 1),
              ((L : ℝ) - (i : ℝ)) • gradient U ((leapfrogFlow U ε i (x0, p0)).1))
          + ((L : ℝ) * ε) • p0) ∧
    (leapfrogFlow U ε 0 (x0, p0) = (x0, p0)) := by
  /- @proof-region region.target-node.session.9ff63330b3b7f2d4 begin -/
  intro d U hU ε x0 p0
  set X : ℕ → HMCState d := fun n => (leapfrogFlow U ε n (x0, p0)).1 with hX
  set P : ℕ → HMCState d := fun n => (leapfrogFlow U ε n (x0, p0)).2 with hP
  set Q : ℕ → HMCState d := fun n => P n - (ε / 2) • gradient U (X n) with hQ
  have hXn : ∀ n : ℕ, X n = (leapfrogFlow U ε n (x0, p0)).1 := fun n => congrFun hX n
  have hPn : ∀ n : ℕ, P n = (leapfrogFlow U ε n (x0, p0)).2 := fun n => congrFun hP n
  have hQn : ∀ n : ℕ, Q n = P n - (ε / 2) • gradient U (X n) := fun n => congrFun hQ n
  have hX0 : X 0 = x0 := by
    rw [hXn 0]
    first
      | rfl
      | simp [leapfrogFlow]
      | simp only [leapfrogFlow, Function.iterate_zero_apply]
  have hP0 : P 0 = p0 := by
    rw [hPn 0]
    first
      | rfl
      | simp [leapfrogFlow]
      | simp only [leapfrogFlow, Function.iterate_zero_apply]
  have hpair : ∀ n : ℕ, (X n, P n) = leapfrogFlow U ε n (x0, p0) := by
    intro n
    refine Prod.ext ?_ ?_
    · exact hXn n
    · exact hPn n
  have hiter_comm : ∀ (n : ℕ) (z : HMCState d × HMCState d),
      (leapfrogStep U ε)^[n] (leapfrogStep U ε z)
        = leapfrogStep U ε ((leapfrogStep U ε)^[n] z) := by
    intro n
    induction n with
    | zero =>
        intro z
        rfl
    | succ n ih =>
        intro z
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
          ih (leapfrogStep U ε z)]
  have hiter : ∀ n : ℕ,
      leapfrogFlow U ε (n + 1) (x0, p0) = leapfrogStep U ε (leapfrogFlow U ε n (x0, p0)) := by
    intro n
    simp only [leapfrogFlow]
    rw [Function.iterate_succ_apply]
    exact hiter_comm n (x0, p0)
  have hstep : ∀ n : ℕ, (X (n + 1), P (n + 1)) = leapfrogStep U ε (X n, P n) := by
    intro n
    rw [hpair (n + 1), hiter n, ← hpair n]
  have hXstep : ∀ n : ℕ, X (n + 1) = X n + ε • Q n := by
    intro n
    have h := congrArg Prod.fst (hstep n)
    simp only [leapfrogStep] at h
    rw [← hQn n] at h
    exact h
  have hPstep : ∀ n : ℕ, P (n + 1) = Q n - (ε / 2) • gradient U (X (n + 1)) := by
    intro n
    have h := congrArg Prod.snd (hstep n)
    simp only [leapfrogStep] at h
    have hx : X n + ε • (P n - (ε / 2) • gradient U (X n)) = X (n + 1) := by
      rw [← hQn n]
      exact (hXstep n).symm
    rw [hx, ← hQn n] at h
    exact h
  have hQrec : ∀ n : ℕ, Q (n + 1) = Q n - ε • gradient U (X (n + 1)) := by
    intro n
    calc Q (n + 1) = P (n + 1) - (ε / 2) • gradient U (X (n + 1)) := hQn (n + 1)
      _ = (Q n - (ε / 2) • gradient U (X (n + 1))) - (ε / 2) • gradient U (X (n + 1)) := by
            rw [hPstep n]
      _ = Q n - ε • gradient U (X (n + 1)) := by
            rw [sub_sub]
            congr 1
            rw [← add_smul, show ε / 2 + ε / 2 = ε by ring]
  have ha : X 1 = x0 - (ε ^ 2 / 2) • gradient U x0 + ε • p0 := by
    have h1 : X (0 + 1) = x0 + ε • (p0 - (ε / 2) • gradient U x0) := by
      rw [hXstep 0, hQn 0, hX0, hP0]
    have h2 : x0 + ε • (p0 - (ε / 2) • gradient U x0)
        = x0 - (ε ^ 2 / 2) • gradient U x0 + ε • p0 := by
      rw [smul_sub, smul_smul, show ε * (ε / 2) = ε ^ 2 / 2 by ring]
      abel
    exact h1.trans h2
  have hb : ∀ i : ℕ, 1 ≤ i → X (i + 1) = 2 • X i - X (i - 1) - ε ^ 2 • gradient U (X i) := by
    intro i hi
    have h1 : X i = X (i - 1) + ε • Q (i - 1) := by
      have h := hXstep (i - 1)
      rwa [Nat.sub_add_cancel hi] at h
    have h2 : X (i + 1) = X i + ε • Q i := hXstep i
    have h3 : Q i = Q (i - 1) - ε • gradient U (X i) := by
      have h := hQrec (i - 1)
      rwa [Nat.sub_add_cancel hi] at h
    have h4 : ε • Q (i - 1) = X i - X (i - 1) := by
      rw [h1]
      abel
    rw [h2, h3, smul_sub, smul_smul, h4, show ε * ε = ε ^ 2 by ring]
    abel
  have hIcc0 : (Finset.Icc 1 0 : Finset ℕ) = ∅ := by
    ext x
    simp only [Finset.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      exact absurd h2 (by omega)
    · intro hx
      exact absurd hx (by simp)
  have hIcc_range : ∀ (n : ℕ) (f : ℕ → HMCState d),
      (∑ i ∈ Finset.Icc 1 n, f i) = ∑ k ∈ Finset.range n, f (k + 1) := by
    intro n f
    induction n with
    | zero => rw [hIcc0, Finset.sum_empty, Finset.sum_range_zero]
    | succ n ih =>
        have hmem : (n + 1) ∉ Finset.Icc 1 n := by
          intro h
          have h2 := (Finset.mem_Icc.mp h).2
          omega
        have hins : (Finset.Icc 1 (n + 1) : Finset ℕ) = insert (n + 1) (Finset.Icc 1 n) := by
          ext x
          simp only [Finset.mem_Icc, Finset.mem_insert]
          constructor
          · rintro ⟨h1, h2⟩
            by_cases hx : x = n + 1
            · exact Or.inl hx
            · exact Or.inr ⟨h1, by omega⟩
          · rintro (hx | ⟨h1, h2⟩)
            · subst hx
              exact ⟨by omega, by omega⟩
            · exact ⟨h1, by omega⟩
        rw [hins, Finset.sum_insert hmem, ih, Finset.sum_range_succ, add_comm]
  have hQsum : ∀ j : ℕ,
      Q j = P 0 - (ε / 2) • gradient U (X 0)
        - ε • (∑ k ∈ Finset.range j, gradient U (X (k + 1))) := by
    intro j
    induction j with
    | zero => rw [hQn 0, Finset.sum_range_zero, smul_zero, sub_zero]
    | succ n ih =>
        rw [hQrec n, ih, Finset.sum_range_succ, smul_add]
        abel
  have hzero : leapfrogFlow U ε 0 (x0, p0) = (x0, p0) := by
    first
      | rfl
      | simp [leapfrogFlow]
      | simp only [leapfrogFlow, Function.iterate_zero_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [hXn] using ha
  · intro i hi
    simpa [hXn] using hb i hi
  · intro L hL
    simp only [← hXn, ← hPn]
    have hPL : P L = Q (L - 1) - (ε / 2) • gradient U (X L) := by
      have h := hPstep (L - 1)
      rwa [Nat.sub_add_cancel hL] at h
    rw [hPL, hQsum (L - 1), ← hIcc_range (L - 1) (fun i => gradient U (X i)), hX0, hP0]
  · intro L hL
    simp only [← hXn, ← hPn]
    have hXsum : ∀ N : ℕ, X N = X 0 + ε • (∑ j ∈ Finset.range N, Q j) := by
      intro N
      induction N with
      | zero => rw [Finset.sum_range_zero, smul_zero, add_zero]
      | succ n ih =>
          rw [hXstep n, ih, Finset.sum_range_succ, smul_add]
          abel
    have hsumQ : ∀ N : ℕ,
        (∑ j ∈ Finset.range N, Q j)
          = (N : ℝ) • (P 0 - (ε / 2) • gradient U (X 0))
            - ε • (∑ j ∈ Finset.range N,
                ∑ k ∈ Finset.range j, gradient U (X (k + 1))) := by
      intro N
      induction N with
      | zero =>
          have h1 : (∑ j ∈ Finset.range 0, Q j) = 0 := by rw [Finset.sum_range_zero]
          have h2 : (∑ j ∈ Finset.range 0,
              ∑ k ∈ Finset.range j, gradient U (X (k + 1))) = 0 := by
            rw [Finset.sum_range_zero]
          rw [h1, h2, Nat.cast_zero, zero_smul, smul_zero, sub_zero]
      | succ n ih =>
          rw [Finset.sum_range_succ, ih, hQsum n, Finset.sum_range_succ, smul_add]
          push_cast
          rw [add_smul, one_smul]
          abel
    have htri : ∀ (N : ℕ) (w : ℕ → HMCState d),
        (∑ j ∈ Finset.range N, ∑ k ∈ Finset.range j, w k)
          = ∑ k ∈ Finset.range N, ((N : ℝ) - 1 - (k : ℝ)) • w k := by
      intro N w
      induction N with
      | zero =>
          have h1 : (∑ j ∈ Finset.range 0, ∑ k ∈ Finset.range j, w k) = 0 := by
            rw [Finset.sum_range_zero]
          rw [h1, Finset.sum_range_zero]
      | succ n ih =>
          rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
          push_cast
          have hz : ((n : ℝ) + 1 - 1 - (n : ℝ)) = 0 := by ring
          rw [hz, zero_smul, add_zero, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun k hk => ?_)
          rw [show ((n : ℝ) + 1 - 1 - (k : ℝ)) = ((n : ℝ) - 1 - (k : ℝ)) + 1 by ring,
            add_smul, one_smul]
    have hdrop : ∀ (w : ℕ → HMCState d),
        (∑ k ∈ Finset.range L, ((L : ℝ) - 1 - (k : ℝ)) • w k)
          = ∑ k ∈ Finset.range (L - 1), ((L : ℝ) - 1 - (k : ℝ)) • w k := by
      intro w
      obtain ⟨m, hm⟩ : ∃ m : ℕ, L = m + 1 := ⟨L - 1, (Nat.sub_add_cancel hL).symm⟩
      subst hm
      rw [Nat.add_sub_cancel, Finset.sum_range_succ]
      push_cast
      have hz : ((m : ℝ) + 1 - 1 - (m : ℝ)) = 0 := by ring
      rw [hz, zero_smul, add_zero]
    have hIccEq : (∑ j ∈ Finset.range L, ∑ k ∈ Finset.range j, gradient U (X (k + 1)))
        = ∑ i ∈ Finset.Icc 1 (L - 1), ((L : ℝ) - (i : ℝ)) • gradient U (X i) := by
      rw [htri L (fun k => gradient U (X (k + 1)))]
      rw [hdrop (fun k => gradient U (X (k + 1)))]
      rw [hIcc_range (L - 1) (fun i => ((L : ℝ) - (i : ℝ)) • gradient U (X i))]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hc : ((L : ℝ) - ((k + 1 : ℕ) : ℝ)) = ((L : ℝ) - 1 - (k : ℝ)) := by
        push_cast
        ring
      rw [hc]
    rw [hXsum L, hsumQ L, hIccEq]
    simp only [smul_sub, smul_smul, mul_assoc]
    first
      | rw [show ε * ε = ε ^ 2 by ring,
            show ε * ((L : ℝ) * (ε / 2)) = (L : ℝ) * ε ^ 2 / 2 by ring,
            show ε * (L : ℝ) = (L : ℝ) * ε by ring, hX0, hP0]
      | rw [show ε * ε = ε ^ 2 by ring,
            show (ε * (L : ℝ)) * (ε / 2) = (L : ℝ) * ε ^ 2 / 2 by ring,
            show ε * (L : ℝ) = (L : ℝ) * ε by ring, hX0, hP0]
    abel
  · exact hzero
  /- @proof-region region.target-node.session.9ff63330b3b7f2d4 end -/

end Statlib.Imported

end

