import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M021_Vocabulary
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M093_Node_997044813_3ff4e155_b9f10776

/- Original module ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProvedNodes.Node_3780394876_0799e630_85340ada; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal
open Statlib.Imported

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_3780394876_0799e630 : ∀ (g q0 : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hg_meas : Measurable g) (hg_nonneg : ∀ y : ℝ, 0 ≤ g y)
    (hg_support : ∀ y : ℝ, y ∉ Set.Icc (-c) c → g y = 0)
    (hq0_meas : Measurable q0) (hq0_nonneg : ∀ y : ℝ, 0 ≤ q0 y)
    (hq0_density : ∫⁻ y, ENNReal.ofReal (q0 y) ∂volume = 1)
    (m M : ℝ) (hm : 0 < m) (hmM : m ≤ M)
    (hT1 : ∀ y ∈ Set.Icc (-c) c, m ≤ g y ∧ g y ≤ M)
    (t : ℕ) (ht : 0 < t)
    (thetaStar : Fin t → ℝ)
    (hsep : ∀ j k : Fin t, j ≠ k → 2 * c < |thetaStar j - thetaStar k|)
    (L : ℝ) (hL : 0 < L)
    (delta : Fin t → ℝ) (hdelta : ∀ j : Fin t, 0 < delta j)
    (hT4 : ∀ j : Fin t, ∀ theta ∈ Set.Ioo (thetaStar j - delta j) (thetaStar j + delta j),
      L ≤ q0 theta)
    (n : ℕ) (hn : t + 1 ≤ n) (x : Fin n → ℝ)
    (hx_nonempty : ∀ j : Fin t,
      1 ≤ (Finset.univ.filter
        (fun i : Fin n => x i ∈ Set.Icc (thetaStar j - c) (thetaStar j + c))).card)
    (hx_sum : ∑ j : Fin t,
      (Finset.univ.filter
        (fun i : Fin n => x i ∈ Set.Icc (thetaStar j - c) (thetaStar j + c))).card = n)
    (hx_ne : ∀ i : Fin n, ∀ j : Fin t, x i ≠ thetaStar j - c ∧ x i ≠ thetaStar j + c),
    ∀ i : Fin n, m * (L * min c (⨅ k : Fin t, delta k)) ≤ margLik g q0 ({i} : Finset (Fin n)) x := by
  /- @proof-region region.target-node.session.3452836f25c04d87 begin -/
  intro g q0 c hc hg_meas hg_nonneg hg_support hq0_meas hq0_nonneg hq0_density m M hm hmM hT1
    t ht thetaStar hsep L hL delta hdelta hT4 n hn x hx_nonempty hx_sum hx_ne i
  have hbdd : BddBelow (Set.range delta) :=
    ⟨0, by rintro _ ⟨k, rfl⟩; exact le_of_lt (hdelta k)⟩
  set C : Fin t → Finset (Fin n) := fun j =>
    Finset.univ.filter (fun i : Fin n => x i ∈ Set.Icc (thetaStar j - c) (thetaStar j + c)) with hC
  have hxsum : ∑ j : Fin t, (C j).card = n := by simpa only [hC] using hx_sum
  have hdisj : ∀ j k : Fin t, j ≠ k → Disjoint (C j) (C k) := by
    intro j k hjk
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    have h1 : |x a - thetaStar j| ≤ c := by
      rw [abs_le]; exact ⟨by linarith, by linarith⟩
    have h2 : |x a - thetaStar k| ≤ c := by
      rw [abs_le]; exact ⟨by linarith, by linarith⟩
    have h3 : |thetaStar j - thetaStar k| ≤ 2 * c := by
      have h4 : thetaStar j - thetaStar k = (thetaStar j - x a) + (x a - thetaStar k) := by ring
      calc |thetaStar j - thetaStar k| = |(thetaStar j - x a) + (x a - thetaStar k)| := by rw [h4]
        _ ≤ |thetaStar j - x a| + |x a - thetaStar k| := abs_add_le _ _
        _ = |x a - thetaStar j| + |x a - thetaStar k| := by rw [abs_sub_comm (thetaStar j) (x a)]
        _ ≤ 2 * c := by linarith
    have h5 := hsep j k hjk
    linarith
  have hcard : (Finset.univ.biUnion C).card = n := by
    have hpw : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin t))) C := by
      intro j _ k _ hjk
      exact hdisj j k hjk
    rw [Finset.card_biUnion hpw]
    simpa using hxsum
  have hbuniv : Finset.univ.biUnion C = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le
    · intro a _
      exact Finset.mem_univ a
    · rw [hcard]
      simp
  have hmem : ∃ j : Fin t, x i ∈ Set.Icc (thetaStar j - c) (thetaStar j + c) := by
    have hi : i ∈ Finset.univ.biUnion C := by rw [hbuniv]; exact Finset.mem_univ i
    rw [Finset.mem_biUnion] at hi
    obtain ⟨j, _, hj⟩ := hi
    exact ⟨j, by simpa only [hC, Finset.mem_filter, Finset.mem_univ, true_and] using hj⟩
  have hmain : ∀ (j : Fin t), x i ∈ Set.Icc (thetaStar j - c) (thetaStar j + c) →
      m * (L * min c (⨅ k : Fin t, delta k)) ≤ ∫ θ, g (x i - θ) * q0 θ ∂volume := by
    intro j hxij
    obtain ⟨hjl, hjr⟩ := hxij
    set A : ℝ := max (x i - c) (thetaStar j - delta j) with hA
    set B : ℝ := min (x i + c) (thetaStar j + delta j) with hB
    have hdpos : 0 < delta j := hdelta j
    have hmc_le_c : min c (delta j) ≤ c := min_le_left c (delta j)
    have hmc_le_d : min c (delta j) ≤ delta j := min_le_right c (delta j)
    have hmcpos : 0 < min c (delta j) := lt_min hc hdpos
    have hAB : A + min c (delta j) ≤ B := by
      have h1 : A + min c (delta j) ≤ x i + c := by
        rw [hA]
        have h : max (x i - c) (thetaStar j - delta j) ≤ (x i + c) - min c (delta j) := by
          apply max_le
          · linarith
          · linarith
        linarith
      have h2 : A + min c (delta j) ≤ thetaStar j + delta j := by
        rw [hA]
        have h : max (x i - c) (thetaStar j - delta j) ≤
            (thetaStar j + delta j) - min c (delta j) := by
          apply max_le
          · linarith
          · linarith
        linarith
      rw [hB]
      exact le_min h1 h2
    have hBAmc : min c (delta j) ≤ B - A := by linarith
    have hABlt : A < B := by linarith
    have hvol : volume.real (Set.Ioo A B) = B - A := by
      have h2 : (ENNReal.ofReal (B - A)).toReal = B - A := ENNReal.toReal_ofReal (by linarith)
      show (volume (Set.Ioo A B)).toReal = B - A
      rw [Real.volume_Ioo]
      exact h2
    have hq0_int : Integrable q0 volume := by
      refine (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hq0_meas.aestronglyMeasurable
        (Filter.Eventually.of_forall hq0_nonneg)).mp ?_
      rw [hq0_density]
      exact ENNReal.one_ne_top
    have hprod_int : Integrable (fun θ : ℝ => g (x i - θ) * q0 θ) volume := by
      have hbound_int : Integrable (fun θ : ℝ => M * q0 θ) volume := hq0_int.const_mul M
      refine MeasureTheory.Integrable.mono' hbound_int ?_ ?_
      · exact ((hg_meas.comp
          ((measurable_const : Measurable (fun _ : ℝ => x i)).sub measurable_id)).mul
          hq0_meas).aestronglyMeasurable
      · filter_upwards with θ
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hg_nonneg _) (hq0_nonneg _))]
        have hgle : g (x i - θ) ≤ M := by
          by_cases hθ : x i - θ ∈ Set.Icc (-c) c
          · exact (hT1 _ hθ).2
          · rw [hg_support _ hθ]
            exact le_of_lt (lt_of_lt_of_le hm hmM)
        exact mul_le_mul_of_nonneg_right hgle (hq0_nonneg θ)
    have hpt : ∀ θ : ℝ, (Set.Ioo A B).indicator (fun _ => m * L) θ ≤ g (x i - θ) * q0 θ := by
      intro θ
      by_cases hθ : θ ∈ Set.Ioo A B
      · rw [Set.indicator_of_mem hθ]
        obtain ⟨hAθ, hθB⟩ := hθ
        have hmemδ : θ ∈ Set.Ioo (thetaStar j - delta j) (thetaStar j + delta j) := by
          refine ⟨?_, ?_⟩
          · have h1 : thetaStar j - delta j ≤ A := by rw [hA]; exact le_max_right _ _
            linarith
          · have h2 : B ≤ thetaStar j + delta j := by rw [hB]; exact min_le_right _ _
            linarith
        have hgc : x i - θ ∈ Set.Icc (-c) c := by
          refine ⟨?_, ?_⟩
          · have h2 : B ≤ x i + c := by rw [hB]; exact min_le_left _ _
            linarith
          · have h1 : x i - c ≤ A := by rw [hA]; exact le_max_left _ _
            linarith
        exact mul_le_mul (hT1 _ hgc).1 (hT4 j θ hmemδ) (le_of_lt hL) (hg_nonneg _)
      · have hzero : (Set.Ioo A B).indicator (fun _ => m * L) θ = 0 := by
          simp [Set.indicator, hθ]
        rw [hzero]
        exact mul_nonneg (hg_nonneg _) (hq0_nonneg _)
    have hmono : ∫ θ, (Set.Ioo A B).indicator (fun _ => m * L) θ ∂volume
        ≤ ∫ θ, g (x i - θ) * q0 θ ∂volume := by
      refine MeasureTheory.integral_mono_of_nonneg ?_ hprod_int ?_
      · filter_upwards with θ
        by_cases hθ : θ ∈ Set.Ioo A B
        · rw [Set.indicator_of_mem hθ]
          exact mul_nonneg (le_of_lt hm) (le_of_lt hL)
        · have hzero : (Set.Ioo A B).indicator (fun _ => m * L) θ = 0 := by
            simp [Set.indicator, hθ]
          rw [hzero]
          exact le_refl 0
      · filter_upwards with θ
        exact hpt θ
    have hval : ∫ θ, (Set.Ioo A B).indicator (fun _ => m * L) θ ∂volume = (m * L) * (B - A) := by
      rw [MeasureTheory.integral_indicator_const (m * L) measurableSet_Ioo, smul_eq_mul, hvol]
      ring
    have hmin_le : min c (⨅ k : Fin t, delta k) ≤ min c (delta j) :=
      le_min (min_le_left c (⨅ k : Fin t, delta k))
        (le_trans (min_le_right c (⨅ k : Fin t, delta k)) (ciInf_le hbdd j))
    calc m * (L * min c (⨅ k : Fin t, delta k)) = (m * L) * min c (⨅ k : Fin t, delta k) := by ring
      _ ≤ (m * L) * min c (delta j) := mul_le_mul_of_nonneg_left hmin_le (le_of_lt (mul_pos hm hL))
      _ ≤ (m * L) * (B - A) := mul_le_mul_of_nonneg_left hBAmc (le_of_lt (mul_pos hm hL))
      _ = ∫ θ, (Set.Ioo A B).indicator (fun _ => m * L) θ ∂volume := hval.symm
      _ ≤ ∫ θ, g (x i - θ) * q0 θ ∂volume := hmono
  obtain ⟨j, hxij⟩ := hmem
  simpa only [margLik, Finset.prod_singleton] using hmain j hxij
  /- @proof-region region.target-node.session.3452836f25c04d87 end -/

end Statlib.Imported
end DPCompletedProof
