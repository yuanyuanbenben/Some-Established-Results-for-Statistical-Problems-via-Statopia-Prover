import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M021_Vocabulary
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M090_Node_1731977007_59742388_a35aa471
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M092_Node_2595484148_496423c5_cc03b9ad
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M094_Node_3780394876_0799e630_85340ada
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M093_Node_997044813_3ff4e155_b9f10776

/- Original module ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProvedNodes.Node_2236029965_83e9c7f1_0b665f0c; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal
open Statlib.Imported

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_2236029965_83e9c7f1 : ∀ (g q0 : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hg_meas : Measurable g) (hg_nonneg : ∀ x : ℝ, 0 ≤ g x)
    (hg_support : ∀ x : ℝ, x ∉ Set.Icc (-c) c → g x = 0)
    (hq0_meas : Measurable q0) (hq0_nonneg : ∀ x : ℝ, 0 ≤ q0 x)
    (hq0_density : ∫⁻ x, ENNReal.ofReal (q0 x) ∂volume = 1)
    (m M : ℝ) (hm : 0 < m) (hmM : m ≤ M)
    (hT1 : ∀ y ∈ Set.Icc (-c) c, m ≤ g y ∧ g y ≤ M)
    (t : ℕ) (ht : 0 < t) (thetaStar : Fin t → ℝ)
    (hsep : ∀ j k : Fin t, j ≠ k → 2 * c < |thetaStar j - thetaStar k|)
    (L : ℝ) (hL : 0 < L) (delta : Fin t → ℝ) (hdelta : ∀ j : Fin t, 0 < delta j)
    (hT4 : ∀ j : Fin t, ∀ theta ∈ Set.Ioo (thetaStar j - delta j) (thetaStar j + delta j),
      L ≤ q0 theta)
    (n : ℕ) (hn : t + 1 ≤ n) (x : Fin n → ℝ)
    (hx_nonempty : ∀ j : Fin t,
      1 ≤ (Finset.univ.filter
        (fun i : Fin n => x i ∈ Set.Icc (thetaStar j - c) (thetaStar j + c))).card)
    (hx_sum : (Finset.univ.sum (fun j : Fin t =>
        (Finset.univ.filter
          (fun i : Fin n => x i ∈ Set.Icc (thetaStar j - c) (thetaStar j + c))).card)) = n)
    (hx_ne : ∀ (i : Fin n) (j : Fin t), x i ≠ thetaStar j - c ∧ x i ≠ thetaStar j + c),
    Finset.sum (tau n (t + 1)) (fun A =>
        (Finset.prod A (fun B => ((B.card - 1).factorial : ℝ))) *
          Finset.prod A (fun B => margLik g q0 B x)) ≥
      (m * (L * min c (⨅ k : Fin t, delta k)) / (M * (t : ℝ) * ((t : ℝ) + 1))) *
        Finset.sum (tau n t) (fun A =>
          (Finset.prod A (fun B => ((B.card - 1).factorial : ℝ))) *
            Finset.prod A (fun B => margLik g q0 B x)) := by
  /- @proof-region region.target-node.session.024560dee144c39a begin -/
  intro g q0 c hc hg_meas hg_nonneg hg_support hq0_meas hq0_nonneg hq0_density m M hm hmM
    hT1 t ht thetaStar hsep L hL delta hdelta hT4 n hn x hx_nonempty hx_sum hx_ne
  classical
  set rho : ℝ := L * min c (⨅ k : Fin t, delta k) with hrho
  set W : Finset (Finset (Fin n)) → ℝ := fun A =>
    (∏ B ∈ A, ((B.card - 1).factorial : ℝ)) * ∏ B ∈ A, margLik g q0 B x with hW
  have hpoint : ∀ i : Fin n, m * rho ≤ margLik g q0 {i} x := by
    have h := statopia_math_node_3780394876_0799e630 g q0 c hc hg_meas hg_nonneg hg_support
      hq0_meas hq0_nonneg hq0_density m M hm hmM hT1 t ht thetaStar hsep L hL delta hdelta hT4
      n hn x hx_nonempty hx_sum hx_ne
    simpa only [hrho] using h
  have hnonneg : ∀ B : Finset (Fin n), 0 ≤ margLik g q0 B x := by
    intro B
    unfold margLik
    exact integral_nonneg fun θ =>
      mul_nonneg (Finset.prod_nonneg fun i _ => hg_nonneg _) (hq0_nonneg θ)
  have hdom : ∀ (B : Finset (Fin n)) (i : Fin n), i ∈ B →
      margLik g q0 B x ≤ M * margLik g q0 (B.erase i) x :=
    statopia_math_node_1731977007_59742388 g q0 c m M n x hc hg_meas hg_nonneg hg_support
      hq0_meas hq0_nonneg hq0_density hm hmM hT1
  have hWnn : ∀ A : Finset (Finset (Fin n)), 0 ≤ W A := by
    intro A
    rw [hW]
    exact mul_nonneg (Finset.prod_nonneg fun B _ => by exact_mod_cast Nat.zero_le _)
      (Finset.prod_nonneg fun B _ => hnonneg B)
  have hrho_nonneg : 0 ≤ rho := by
    haveI : Nonempty (Fin t) := ⟨⟨0, ht⟩⟩
    have hinf : (0 : ℝ) ≤ ⨅ k : Fin t, delta k := le_ciInf fun k => (hdelta k).le
    rw [hrho]
    exact mul_nonneg hL.le (le_min hc.le hinf)
  have hcombi : (m * rho / M) * (∑ A ∈ tau n t, W A) ≤
      ((t : ℝ) * ((t : ℝ) + 1)) * (∑ A' ∈ tau n (t + 1), W A') := by
    have h := statopia_math_node_2595484148_496423c5 n t ht hn m M rho hm hmM hrho_nonneg
      (fun B => margLik g q0 B x) hnonneg hdom hpoint
    rw [hW]
    exact h
  have hden : m * rho / (M * (t : ℝ) * ((t : ℝ) + 1)) =
      (m * rho / M) / ((t : ℝ) * ((t : ℝ) + 1)) := by
    rw [div_div, mul_assoc]
  have htR : (0 : ℝ) < (t : ℝ) * ((t : ℝ) + 1) := by
    have ht' : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
    nlinarith
  have hmain : (m * rho / (M * (t : ℝ) * ((t : ℝ) + 1))) * (∑ A ∈ tau n t, W A) ≤
      ∑ A' ∈ tau n (t + 1), W A' := by
    rw [hden, div_mul_eq_mul_div]
    rw [div_le_iff₀ htR]
    calc (m * rho / M) * (∑ A ∈ tau n t, W A)
        ≤ ((t : ℝ) * ((t : ℝ) + 1)) * (∑ A' ∈ tau n (t + 1), W A') := hcombi
      _ = (∑ A' ∈ tau n (t + 1), W A') * ((t : ℝ) * ((t : ℝ) + 1)) := by ring
  linarith [hmain]
  /- @proof-region region.target-node.session.024560dee144c39a end -/

end Statlib.Imported
end DPCompletedProof
