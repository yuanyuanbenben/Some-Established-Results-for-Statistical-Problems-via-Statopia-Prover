import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M021_Vocabulary
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions

/- Original module ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProvedNodes.Node_997044813_3ff4e155_b9f10776; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal
open Statlib.Imported

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_997044813_3ff4e155 : ∀ (g q0 : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hg_meas : Measurable g) (hg_nonneg : ∀ x : ℝ, 0 ≤ g x)
    (hg_support : ∀ x : ℝ, x ∉ Set.Icc (-c) c → g x = 0)
    (hg_density : ∫⁻ x, ENNReal.ofReal (g x) ∂volume = 1)
    (hq0_meas : Measurable q0) (hq0_nonneg : ∀ x : ℝ, 0 ≤ q0 x)
    (hq0_density : ∫⁻ x, ENNReal.ofReal (q0 x) ∂volume = 1)
    (t : ℕ) (ht : 0 < t)
    (thetaStar : Fin t → ℝ) (L : ℝ) (hL : 0 < L)
    (delta : Fin t → ℝ) (hdelta : ∀ j : Fin t, 0 < delta j)
    (hT4 : ∀ j : Fin t, ∀ theta ∈ Set.Ioo (thetaStar j - delta j) (thetaStar j + delta j),
      L ≤ q0 theta)
    (m M : ℝ) (hm : 0 < m) (hmM : m ≤ M)
    (hT1 : ∀ x ∈ Set.Icc (-c) c, m ≤ g x ∧ g x ≤ M),
    0 < L * min c (⨅ k : Fin t, delta k) ∧
      ∀ j : Fin t, ∀ x ∈ Set.Icc (thetaStar j - c) (thetaStar j + c),
        m * (L * min c (⨅ k : Fin t, delta k))
          ≤ ∫ theta, g (x - theta) * q0 theta ∂volume := by
  /- @proof-region region.target-node.session.b42354baeb5d87ce begin -/
  intro g q0 c hc hg_meas hg_nonneg hg_support hg_density hq0_meas hq0_nonneg hq0_density t ht
    thetaStar L hL delta hdelta hT4 m M hm hmM hT1
  have hbdd : BddBelow (Set.range (fun k : Fin t => delta k)) :=
    ⟨0, by
      rintro _ ⟨k, rfl⟩
      exact (hdelta k).le⟩
  have hmin_pos : 0 < min c (⨅ k : Fin t, delta k) := by
    haveI hinst : Nonempty (Fin t) := ⟨⟨0, ht⟩⟩
    have hne : (Finset.univ : Finset (Fin t)).Nonempty := ⟨⟨0, ht⟩, Finset.mem_univ _⟩
    obtain ⟨k₀, -, hk₀⟩ :=
      Finset.exists_min_image (Finset.univ : Finset (Fin t)) (fun k => delta k) hne
    have hinf_eq : (⨅ k : Fin t, delta k) = delta k₀ :=
      le_antisymm (ciInf_le hbdd k₀) (le_ciInf fun k => hk₀ k (Finset.mem_univ k))
    rw [hinf_eq]
    exact lt_min hc (hdelta k₀)
  constructor
  · exact mul_pos hL hmin_pos
  · intro j x hx
    set d : ℝ := min c (delta j) with hd
    have hd_le_c : d ≤ c := by rw [hd]; exact min_le_left _ _
    have hd_le_delta : d ≤ delta j := by rw [hd]; exact min_le_right _ _
    have hω_le_d : min c (⨅ k : Fin t, delta k) ≤ d :=
      le_min (min_le_left _ _) (le_trans (min_le_right _ _) (ciInf_le hbdd j))
    have hM_nonneg : 0 ≤ M := le_trans hm.le hmM
    have hg_le_M : ∀ y : ℝ, g y ≤ M := by
      intro y
      by_cases hy : y ∈ Set.Icc (-c) c
      · exact (hT1 y hy).2
      · rw [hg_support y hy]
        linarith
    have hF_nonneg : ∀ θ : ℝ, 0 ≤ g (x - θ) * q0 θ := fun θ =>
      mul_nonneg (hg_nonneg _) (hq0_nonneg _)
    have hshift_meas : Measurable (fun θ : ℝ => x - θ) := measurable_const.sub measurable_id
    have hF_meas : AEStronglyMeasurable (fun θ : ℝ => g (x - θ) * q0 θ) volume :=
      ((hg_meas.comp hshift_meas).mul hq0_meas).aestronglyMeasurable
    have hq_meas : Measurable (fun θ : ℝ => ENNReal.ofReal (q0 θ)) := hq0_meas.ennreal_ofReal
    have hbd : ∀ θ : ℝ, ENNReal.ofReal (g (x - θ) * q0 θ)
        ≤ ENNReal.ofReal M * ENNReal.ofReal (q0 θ) := by
      intro θ
      rw [ENNReal.ofReal_mul (hg_nonneg _)]
      exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (hg_le_M (x - θ))) (by simp)
    have hfin : ∫⁻ θ, ENNReal.ofReal (g (x - θ) * q0 θ) ≠ ⊤ := by
      have hb : ∫⁻ θ, ENNReal.ofReal (g (x - θ) * q0 θ) ≤ ENNReal.ofReal M := by
        calc ∫⁻ θ, ENNReal.ofReal (g (x - θ) * q0 θ)
            ≤ ∫⁻ θ, ENNReal.ofReal M * ENNReal.ofReal (q0 θ) := lintegral_mono hbd
          _ = ENNReal.ofReal M * ∫⁻ θ, ENNReal.ofReal (q0 θ) := lintegral_const_mul _ hq_meas
          _ = ENNReal.ofReal M * 1 := by rw [hq0_density]
          _ = ENNReal.ofReal M := mul_one _
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
    have hconv : ∫ θ, g (x - θ) * q0 θ ∂volume
        = (∫⁻ θ, ENNReal.ofReal (g (x - θ) * q0 θ) ∂volume).toReal :=
      integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hF_nonneg) hF_meas
    have hρ_nonneg : 0 ≤ m * (L * min c (⨅ k : Fin t, delta k)) :=
      (mul_pos hm (mul_pos hL hmin_pos)).le
    have key : ENNReal.ofReal (m * (L * min c (⨅ k : Fin t, delta k)))
        ≤ ∫⁻ θ, ENNReal.ofReal (g (x - θ) * q0 θ) := by
      rcases le_total x (thetaStar j) with hle | hle
      · have hx_in : ∀ θ ∈ Set.Ioo (thetaStar j - d) (thetaStar j), x - θ ∈ Set.Icc (-c) c := by
          intro θ hθ
          exact ⟨by linarith [hθ.2, hx.1], by linarith [hθ.1, hle, hd_le_c]⟩
        have hq_in : ∀ θ ∈ Set.Ioo (thetaStar j - d) (thetaStar j),
            θ ∈ Set.Ioo (thetaStar j - delta j) (thetaStar j + delta j) := by
          intro θ hθ
          exact ⟨by linarith [hθ.1, hd_le_delta], by linarith [hθ.2, hdelta j]⟩
        have hs_meas : MeasurableSet (Set.Ioo (thetaStar j - d) (thetaStar j)) :=
          isOpen_Ioo.measurableSet
        have hvol : volume (Set.Ioo (thetaStar j - d) (thetaStar j)) = ENNReal.ofReal d := by
          rw [Real.volume_Ioo]
          congr 1
          ring
        have hmono : ENNReal.ofReal (m * (L * min c (⨅ k : Fin t, delta k)))
            ≤ ENNReal.ofReal (m * L) * volume (Set.Ioo (thetaStar j - d) (thetaStar j)) := by
          rw [hvol]
          calc ENNReal.ofReal (m * (L * min c (⨅ k : Fin t, delta k)))
              = ENNReal.ofReal ((m * L) * min c (⨅ k : Fin t, delta k)) := by rw [mul_assoc]
            _ ≤ ENNReal.ofReal ((m * L) * d) :=
                ENNReal.ofReal_le_ofReal
                  (mul_le_mul_of_nonneg_left hω_le_d (le_of_lt (mul_pos hm hL)))
            _ = ENNReal.ofReal (m * L) * ENNReal.ofReal d :=
                ENNReal.ofReal_mul (le_of_lt (mul_pos hm hL))
        have hconst : ∫⁻ θ in Set.Ioo (thetaStar j - d) (thetaStar j), ENNReal.ofReal (m * L)
            = ENNReal.ofReal (m * L) * volume (Set.Ioo (thetaStar j - d) (thetaStar j)) := by
          rw [lintegral_const]
          simp
        have hpt : ∫⁻ θ in Set.Ioo (thetaStar j - d) (thetaStar j), ENNReal.ofReal (m * L)
            ≤ ∫⁻ θ in Set.Ioo (thetaStar j - d) (thetaStar j),
                ENNReal.ofReal (g (x - θ) * q0 θ) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem hs_meas] with θ hθ
          exact ENNReal.ofReal_le_ofReal
            (mul_le_mul (hT1 (x - θ) (hx_in θ hθ)).1 (hT4 j θ (hq_in θ hθ))
              hL.le (hg_nonneg _))
        have hsubs : ∫⁻ θ in Set.Ioo (thetaStar j - d) (thetaStar j),
              ENNReal.ofReal (g (x - θ) * q0 θ)
            ≤ ∫⁻ θ, ENNReal.ofReal (g (x - θ) * q0 θ) := by
          have h := lintegral_mono_set (μ := volume) (s := Set.Ioo (thetaStar j - d) (thetaStar j))
            (t := Set.univ) (f := fun θ => ENNReal.ofReal (g (x - θ) * q0 θ)) (Set.subset_univ _)
          simpa using h
        calc ENNReal.ofReal (m * (L * min c (⨅ k : Fin t, delta k)))
            ≤ ENNReal.ofReal (m * L) * volume (Set.Ioo (thetaStar j - d) (thetaStar j)) := hmono
          _ = ∫⁻ θ in Set.Ioo (thetaStar j - d) (thetaStar j), ENNReal.ofReal (m * L) := hconst.symm
          _ ≤ ∫⁻ θ in Set.Ioo (thetaStar j - d) (thetaStar j),
                ENNReal.ofReal (g (x - θ) * q0 θ) := hpt
          _ ≤ ∫⁻ θ, ENNReal.ofReal (g (x - θ) * q0 θ) := hsubs
      · have hx_in : ∀ θ ∈ Set.Ioo (thetaStar j) (thetaStar j + d), x - θ ∈ Set.Icc (-c) c := by
          intro θ hθ
          exact ⟨by linarith [hθ.2, hle, hd_le_c], by linarith [hθ.1, hx.2]⟩
        have hq_in : ∀ θ ∈ Set.Ioo (thetaStar j) (thetaStar j + d),
            θ ∈ Set.Ioo (thetaStar j - delta j) (thetaStar j + delta j) := by
          intro θ hθ
          exact ⟨by linarith [hθ.1, hdelta j], by linarith [hθ.2, hd_le_delta]⟩
        have hs_meas : MeasurableSet (Set.Ioo (thetaStar j) (thetaStar j + d)) :=
          isOpen_Ioo.measurableSet
        have hvol : volume (Set.Ioo (thetaStar j) (thetaStar j + d)) = ENNReal.ofReal d := by
          rw [Real.volume_Ioo]
          congr 1
          ring
        have hmono : ENNReal.ofReal (m * (L * min c (⨅ k : Fin t, delta k)))
            ≤ ENNReal.ofReal (m * L) * volume (Set.Ioo (thetaStar j) (thetaStar j + d)) := by
          rw [hvol]
          calc ENNReal.ofReal (m * (L * min c (⨅ k : Fin t, delta k)))
              = ENNReal.ofReal ((m * L) * min c (⨅ k : Fin t, delta k)) := by rw [mul_assoc]
            _ ≤ ENNReal.ofReal ((m * L) * d) :=
                ENNReal.ofReal_le_ofReal
                  (mul_le_mul_of_nonneg_left hω_le_d (le_of_lt (mul_pos hm hL)))
            _ = ENNReal.ofReal (m * L) * ENNReal.ofReal d :=
                ENNReal.ofReal_mul (le_of_lt (mul_pos hm hL))
        have hconst : ∫⁻ θ in Set.Ioo (thetaStar j) (thetaStar j + d), ENNReal.ofReal (m * L)
            = ENNReal.ofReal (m * L) * volume (Set.Ioo (thetaStar j) (thetaStar j + d)) := by
          rw [lintegral_const]
          simp
        have hpt : ∫⁻ θ in Set.Ioo (thetaStar j) (thetaStar j + d), ENNReal.ofReal (m * L)
            ≤ ∫⁻ θ in Set.Ioo (thetaStar j) (thetaStar j + d),
                ENNReal.ofReal (g (x - θ) * q0 θ) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem hs_meas] with θ hθ
          exact ENNReal.ofReal_le_ofReal
            (mul_le_mul (hT1 (x - θ) (hx_in θ hθ)).1 (hT4 j θ (hq_in θ hθ))
              hL.le (hg_nonneg _))
        have hsubs : ∫⁻ θ in Set.Ioo (thetaStar j) (thetaStar j + d),
              ENNReal.ofReal (g (x - θ) * q0 θ)
            ≤ ∫⁻ θ, ENNReal.ofReal (g (x - θ) * q0 θ) := by
          have h := lintegral_mono_set (μ := volume) (s := Set.Ioo (thetaStar j) (thetaStar j + d))
            (t := Set.univ) (f := fun θ => ENNReal.ofReal (g (x - θ) * q0 θ)) (Set.subset_univ _)
          simpa using h
        calc ENNReal.ofReal (m * (L * min c (⨅ k : Fin t, delta k)))
            ≤ ENNReal.ofReal (m * L) * volume (Set.Ioo (thetaStar j) (thetaStar j + d)) := hmono
          _ = ∫⁻ θ in Set.Ioo (thetaStar j) (thetaStar j + d), ENNReal.ofReal (m * L) := hconst.symm
          _ ≤ ∫⁻ θ in Set.Ioo (thetaStar j) (thetaStar j + d),
                ENNReal.ofReal (g (x - θ) * q0 θ) := hpt
          _ ≤ ∫⁻ θ, ENNReal.ofReal (g (x - θ) * q0 θ) := hsubs
    rw [hconv]
    calc m * (L * min c (⨅ k : Fin t, delta k))
        = (ENNReal.ofReal (m * (L * min c (⨅ k : Fin t, delta k)))).toReal :=
            (ENNReal.toReal_ofReal hρ_nonneg).symm
      _ ≤ (∫⁻ θ, ENNReal.ofReal (g (x - θ) * q0 θ)).toReal := ENNReal.toReal_mono hfin key
  /- @proof-region region.target-node.session.b42354baeb5d87ce end -/

end Statlib.Imported
end DPCompletedProof
