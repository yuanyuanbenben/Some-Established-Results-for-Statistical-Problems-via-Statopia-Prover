import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M021_Vocabulary
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M095_Node_2236029965_83e9c7f1_0b665f0c
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M096_Node_2340343151_79e1234f_7a35220e
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M097_Node_385287431_389965bb_66c786bf
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M093_Node_997044813_3ff4e155_b9f10776

/- Original module ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProvedNodes.Node_2291078137_86c48b81_e6a93cbc; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported




open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal
open Statlib.Imported

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_2291078137_86c48b81 : ∀ (g q0 : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
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
    (hx_ne : ∀ (i : Fin n) (j : Fin t), x i ≠ thetaStar j - c ∧ x i ≠ thetaStar j + c)
    (alphaStar : ℝ) (halpha : 0 < alphaStar),
    let c0 : ℝ := alphaStar * (m * (L * min c (⨅ k : Fin t, delta k))) / (M * (t : ℝ) * ((t : ℝ) + 1));
    postProb g q0 (Measure.dirac alphaStar) n t x ≤ 1 / (1 + c0) ∧
      1 / (1 + c0) = 1 - c0 / (1 + c0) := by
  /- @proof-region region.target-node.session.65ad21f7c32f37db begin -/
  classical
  intros g q0 c hc hg_meas hg_nonneg hg_support hq0_meas hq0_nonneg hq0_density m M hm hmM hT1 t ht
    thetaStar hsep L hL delta hdelta hT4 n hn x hx_nonempty hx_sum hx_ne alphaStar halpha
  dsimp only
  let c0 : ℝ := alphaStar * (m * (L * min c (⨅ k : Fin t, delta k))) / (M * (t : ℝ) * ((t : ℝ) + 1))
  change postProb g q0 (Measure.dirac alphaStar) n t x ≤ 1 / (1 + c0) ∧
    1 / (1 + c0) = 1 - c0 / (1 + c0)
  let J : ℕ → ℝ := fun r => jointMass g q0 (Measure.dirac alphaStar) n r x
  let Num : ℕ → ℝ := fun r =>
    ∑ A ∈ tau n r, (∏ B ∈ A, ((B.card - 1).factorial : ℝ)) * (∏ B ∈ A, margLik g q0 B x)
  let P : ℕ → ℝ := fun r => ∫ α, α ^ r / ascFact α n ∂(Measure.dirac alphaStar)
  have hMpos : 0 < M := lt_of_lt_of_le hm hmM
  have htn : t < n := by omega
  have hn1 : 1 ≤ n := by omega
  have ht1n : 1 ≤ t := by omega
  have hDpos : 0 < M * (t : ℝ) * ((t : ℝ) + 1) := by
    have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
    exact mul_pos (mul_pos hMpos htR) (by linarith)
  haveI : Nonempty (Fin t) := ⟨⟨0, ht⟩⟩
  have hinf_nonneg : (0 : ℝ) ≤ ⨅ k : Fin t, delta k :=
    le_ciInf (fun j => le_of_lt (hdelta j))
  have hc0_nonneg : 0 ≤ c0 := by
    have hρ : (0 : ℝ) ≤ L * min c (⨅ k : Fin t, delta k) :=
      mul_nonneg (le_of_lt hL) (le_min (le_of_lt hc) hinf_nonneg)
    have hmρ : (0 : ℝ) ≤ m * (L * min c (⨅ k : Fin t, delta k)) := mul_nonneg (le_of_lt hm) hρ
    exact div_nonneg (mul_nonneg (le_of_lt halpha) hmρ) (le_of_lt hDpos)
  have h1c0 : (0 : ℝ) < 1 + c0 := by linarith
  have hc0ne : (1 + c0) ≠ 0 := ne_of_gt h1c0
  have hGSP := statopia_math_node_2340343151_79e1234f c hc t ht g q0 hg_meas hg_nonneg hg_support
    hq0_meas hq0_nonneg hq0_density ⟨m, M, hm, hmM, hT1⟩ thetaStar hsep L hL delta hdelta hT4 n
    (by omega : 0 < n) x hx_nonempty hx_sum hx_ne
  have hNum_pos : 0 < Num t := by
    have h := hGSP
    dsimp only at h
    exact h.2.2.2
  have hNum_ne : Num t ≠ 0 := ne_of_gt hNum_pos
  have hmarg_nonneg : ∀ B : Finset (Fin n), 0 ≤ margLik g q0 B x := by
    intro B
    show 0 ≤ ∫ θ, (∏ i ∈ B, g (x i - θ)) * q0 θ
    exact MeasureTheory.integral_nonneg
      (fun θ => mul_nonneg (Finset.prod_nonneg (fun i _ => hg_nonneg _)) (hq0_nonneg θ))
  have hNum_nonneg : ∀ r : ℕ, 1 ≤ r → r ≤ n → 0 ≤ Num r := by
    intro r _ _
    exact Finset.sum_nonneg
      (fun A _ => mul_nonneg (Finset.prod_nonneg (fun B _ => by positivity))
        (Finset.prod_nonneg (fun B _ => hmarg_nonneg B)))
  have h_ae : ∀ᵐ α ∂(Measure.dirac alphaStar), 0 < α :=
    (MeasureTheory.mem_ae_dirac_iff measurableSet_Ioi).mpr halpha
  have hRI := statopia_math_node_385287431_389965bb g q0 c M hc hMpos hg_meas hg_nonneg hg_support
    (fun y hy => (hT1 y hy).2) hq0_meas hq0_nonneg hq0_density
  have hJ_eq : ∀ r : ℕ, 1 ≤ r → r ≤ n → J r = P r * Num r := by
    intro r h1 h2
    exact hRI.1 n hn1 (Measure.dirac alphaStar) inferInstance h_ae r h1 h2 x
  have hDirac := hRI.2.2 alphaStar halpha n hn1
  have hPpos : ∀ r : ℕ, 1 ≤ r → r ≤ n → 0 < P r :=
    fun r h1 h2 => (hDirac.1 r h1 h2).2
  have hJ_nonneg : ∀ r : ℕ, 1 ≤ r → r ≤ n → 0 ≤ J r := by
    intro r h1 h2
    rw [hJ_eq r h1 h2]
    exact mul_nonneg (le_of_lt (hPpos r h1 h2)) (hNum_nonneg r h1 h2)
  have hJt_pos : 0 < J t := by
    rw [hJ_eq t ht1n (le_of_lt htn)]
    exact mul_pos (hPpos t ht1n (le_of_lt htn)) hNum_pos
  have hTn_pos : 0 < ∑ r ∈ Finset.Icc 1 n, J r := by
    have hmem : t ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨ht1n, le_of_lt htn⟩
    have hsub : ({t} : Finset ℕ) ⊆ Finset.Icc 1 n := by
      intro a ha
      simp only [Finset.mem_singleton] at ha
      exact ha ▸ hmem
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i hi _ => hJ_nonneg i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2)
    have hJt : J t ≤ ∑ r ∈ Finset.Icc 1 n, J r := by simpa using hle
    linarith
  have hTn_ne : (∑ r ∈ Finset.Icc 1 n, J r) ≠ 0 := ne_of_gt hTn_pos
  have hpost_eq : ∀ r : ℕ, postProb g q0 (Measure.dirac alphaStar) n r x =
      J r / (∑ s ∈ Finset.Icc 1 n, J s) := fun r => rfl
  have hpost_nonneg : ∀ r ∈ Finset.Icc 1 n,
      0 ≤ postProb g q0 (Measure.dirac alphaStar) n r x := by
    intro r hr
    rw [hpost_eq r]
    exact div_nonneg (hJ_nonneg r (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2)
      (le_of_lt hTn_pos)
  have hsum_eq : (∑ r ∈ Finset.Icc 1 n, postProb g q0 (Measure.dirac alphaStar) n r x) = 1 := by
    simp only [hpost_eq]
    rw [← Finset.sum_div]
    exact div_self hTn_ne
  have hpair : postProb g q0 (Measure.dirac alphaStar) n t x +
      postProb g q0 (Measure.dirac alphaStar) n (t + 1) x ≤ 1 := by
    have hsub : ({t, t + 1} : Finset ℕ) ⊆ Finset.Icc 1 n := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with h | h
      · rw [h]
        exact Finset.mem_Icc.mpr ⟨ht1n, le_of_lt htn⟩
      · rw [h]
        exact Finset.mem_Icc.mpr ⟨by omega, hn⟩
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ => hpost_nonneg i hi)
    rw [hsum_eq] at hle
    have hleft : (∑ r ∈ ({t, t + 1} : Finset ℕ),
        postProb g q0 (Measure.dirac alphaStar) n r x) =
        postProb g q0 (Measure.dirac alphaStar) n t x +
          postProb g q0 (Measure.dirac alphaStar) n (t + 1) x := by
      have hne : t ∉ ({t + 1} : Finset ℕ) := by
        simp only [Finset.mem_singleton]
        omega
      rw [Finset.sum_insert hne, Finset.sum_singleton]
    rwa [hleft] at hle
  have hRatio : postProb g q0 (Measure.dirac alphaStar) n (t + 1) x /
      postProb g q0 (Measure.dirac alphaStar) n t x = alphaStar * (Num (t + 1) / Num t) :=
    hDirac.2 t x ht1n htn hTn_ne hNum_ne
  have hsplit := statopia_math_node_2236029965_83e9c7f1 g q0 c hc hg_meas hg_nonneg hg_support
    hq0_meas hq0_nonneg hq0_density m M hm hmM hT1 t ht thetaStar hsep L hL delta hdelta hT4 n hn x
    hx_nonempty hx_sum hx_ne
  have hratio_ge : m * (L * min c (⨅ k : Fin t, delta k)) / (M * (t : ℝ) * ((t : ℝ) + 1)) ≤
      Num (t + 1) / Num t := by
    by_contra hcon
    push_neg at hcon
    have h3 : Num (t + 1) / Num t * Num t = Num (t + 1) := by field_simp
    have h4 := mul_lt_mul_of_pos_right hcon hNum_pos
    rw [h3] at h4
    linarith [hsplit]
  have hratio_ge' : c0 ≤ postProb g q0 (Measure.dirac alphaStar) n (t + 1) x /
      postProb g q0 (Measure.dirac alphaStar) n t x := by
    rw [hRatio]
    have hc0eq : c0 = alphaStar * (m * (L * min c (⨅ k : Fin t, delta k)) /
        (M * (t : ℝ) * ((t : ℝ) + 1))) := by
      show alphaStar * (m * (L * min c (⨅ k : Fin t, delta k))) /
          (M * (t : ℝ) * ((t : ℝ) + 1)) =
        alphaStar * (m * (L * min c (⨅ k : Fin t, delta k)) /
          (M * (t : ℝ) * ((t : ℝ) + 1)))
      ring
    rw [hc0eq]
    exact mul_le_mul_of_nonneg_left hratio_ge (le_of_lt halpha)
  have hPi_pos : 0 < postProb g q0 (Measure.dirac alphaStar) n t x := by
    rw [hpost_eq t]
    exact div_pos hJt_pos hTn_pos
  have hmul : postProb g q0 (Measure.dirac alphaStar) n t x * c0 ≤
      postProb g q0 (Measure.dirac alphaStar) n (t + 1) x := by
    have h2 := mul_le_mul_of_nonneg_right hratio_ge' (le_of_lt hPi_pos)
    have h3 : (postProb g q0 (Measure.dirac alphaStar) n (t + 1) x /
        postProb g q0 (Measure.dirac alphaStar) n t x) *
        postProb g q0 (Measure.dirac alphaStar) n t x =
        postProb g q0 (Measure.dirac alphaStar) n (t + 1) x := by field_simp
    rw [h3] at h2
    linarith [h2]
  have hmain : postProb g q0 (Measure.dirac alphaStar) n t x * (1 + c0) ≤ 1 := by
    have he : postProb g q0 (Measure.dirac alphaStar) n t x * (1 + c0) =
        postProb g q0 (Measure.dirac alphaStar) n t x +
          postProb g q0 (Measure.dirac alphaStar) n t x * c0 := by ring
    rw [he]
    linarith [hpair, hmul]
  constructor
  · have h3 : 1 / (1 + c0) * (1 + c0) = 1 := by field_simp
    by_contra hcon
    push_neg at hcon
    have h4 := mul_lt_mul_of_pos_right hcon h1c0
    rw [h3] at h4
    linarith [hmain]
  · field_simp
    ring
  /- @proof-region region.target-node.session.65ad21f7c32f37db end -/

end Statlib.Imported
end DPCompletedProof
