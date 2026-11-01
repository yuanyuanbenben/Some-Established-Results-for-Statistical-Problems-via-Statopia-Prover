import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M000_Vocabulary
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M001_Base

/- Original module ProverJobs.manual_dp_cons_finish_20261031.WindowMass; genuine source relocated, namespace-isolated only. -/
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
theorem statopia_math_node_1091114221_9ffd4ba6 : ∀ (t : ℕ) (ht : 1 ≤ t) (c : ℝ) (hc : 0 < c)
    (g : ℝ → ℝ) (thetaStar : Fin t → ℝ) (m : ℝ) (hm : 0 < m)
    (hg_meas : Measurable g)
    (hg_nonneg : ∀ x : ℝ, 0 ≤ g x)
    (hg_zero : ∀ x : ℝ, x ∉ Set.Icc (-c) c → g x = 0)
    (hg_lower : ∀ x ∈ Set.Icc (-c) c, m ≤ g x)
    (hg_int : ∫ x : ℝ, g x ∂volume = 1)
    (l : Fin t) (theta : ℝ),
    0 ≤ (∫ x in Set.Icc (thetaStar l - c) (thetaStar l + c), g (x - theta) ∂volume) ∧
    (∫ x in Set.Icc (thetaStar l - c) (thetaStar l + c), g (x - theta) ∂volume) ≤
      max 0 (1 - m * |theta - thetaStar l|) ∧
    (2 * c ≤ |theta - thetaStar l| →
      (∫ x in Set.Icc (thetaStar l - c) (thetaStar l + c), g (x - theta) ∂volume) = 0) := by
  /- @proof-region region.target-node.session.8689499de5be4fe9 begin -/
  intro t ht c hc g thetaStar m hm hg_meas hg_nonneg hg_zero hg_min hg_int
  intro ℓ θ
  have hg_int_Icc : ∫ x in Set.Icc (-c) c, g x ∂volume = 1 := by
    have h0 : ∫ x in Set.Icc (-c) c, g x ∂volume = ∫ x, g x ∂volume :=
      MeasureTheory.setIntegral_eq_integral_of_ae_compl_eq_zero (f := g) (s := Set.Icc (-c) c)
        (Filter.Eventually.of_forall (fun x hx => hg_zero x hx))
    rw [h0, hg_int]
  have hg_intble : Integrable g volume := by
    by_contra h
    rw [MeasureTheory.integral_undef h] at hg_int
    exact one_ne_zero hg_int.symm
  have hG_eq : (∫ x in Set.Icc (thetaStar ℓ - c) (thetaStar ℓ + c), g (x - θ) ∂volume)
      = ∫ x in (thetaStar ℓ - θ - c)..(thetaStar ℓ - θ + c), g x := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (show thetaStar ℓ - c ≤ thetaStar ℓ + c by linarith)]
    rw [intervalIntegral.integral_comp_sub_right g θ]
    rw [show (thetaStar ℓ - c) - θ = thetaStar ℓ - θ - c by ring,
        show (thetaStar ℓ + c) - θ = thetaStar ℓ - θ + c by ring]
  have hKzero : ∀ u : ℝ, 2 * c ≤ |u| → (∫ x in (u - c)..(u + c), g x) = 0 := by
    intro u hu
    rw [intervalIntegral.integral_of_le (by linarith : u - c ≤ u + c)]
    apply MeasureTheory.setIntegral_eq_zero_of_ae_eq_zero
    by_cases h : 0 ≤ u
    · have hu' : 2 * c ≤ u := by rwa [abs_of_nonneg h] at hu
      exact Filter.Eventually.of_forall (fun x hx => by
        apply hg_zero x
        rw [Set.mem_Ioc] at hx
        intro hmem
        rw [Set.mem_Icc] at hmem
        linarith [hx.1, hmem.2, hu'])
    · have hu' : 2 * c ≤ -u := by rwa [abs_of_neg (by linarith)] at hu
      have hsub : Set.Ioc (u - c) (u + c) ∩ Set.Icc (-c) c ⊆ {-c} := by
        intro x hx
        obtain ⟨hx1, hx2⟩ := hx
        rw [Set.mem_Ioc] at hx1
        rw [Set.mem_Icc] at hx2
        rw [Set.mem_singleton_iff]
        linarith [hx1.2, hx2.1, hu']
      have hnull : volume (Set.Ioc (u - c) (u + c) ∩ Set.Icc (-c) c) = 0 :=
        MeasureTheory.measure_mono_null hsub (by simp)
      have hae : ∀ᵐ x ∂volume, x ∉ Set.Ioc (u - c) (u + c) ∩ Set.Icc (-c) c := by
        rw [MeasureTheory.ae_iff]
        simpa only [not_not] using hnull
      exact hae.mono (fun x hx hmem => by
        by_contra hgne
        exact hx ⟨hmem, by by_contra hnot; exact hgne (hg_zero x hnot)⟩)
  have hKbound : ∀ u : ℝ, (∫ x in (u - c)..(u + c), g x) ≤ max 0 (1 - m * |u|) := by
    intro u
    have hInt : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b => by
      unfold IntervalIntegrable
      exact ⟨hg_intble.integrableOn, hg_intble.integrableOn⟩
    have hbridge : ∫ x in (-c)..c, g x = 1 := by
      rw [intervalIntegral.integral_of_le (by linarith : -c ≤ c),
        ← MeasureTheory.integral_Icc_eq_integral_Ioc, hg_int_Icc]
    by_cases hu2 : (|u| ≤ 2 * c)
    · by_cases hu : 0 ≤ u
      · have huu : |u| = u := abs_of_nonneg hu
        have hu2c : u ≤ 2 * c := by rw [← huu]; exact hu2
        have hmono : ∫ x in (-c)..(u - c), m ≤ ∫ x in (-c)..(u - c), g x :=
          intervalIntegral.integral_mono_on (show -c ≤ u - c by linarith)
            intervalIntegral.intervalIntegrable_const (hInt (-c) (u - c))
            (fun x hx => by
              rw [Set.mem_Icc] at hx
              exact hg_min x (by
                rw [Set.mem_Icc]
                exact ⟨hx.1, by linarith [hx.2, hu2c]⟩))
        have hconst : ∫ x in (-c)..(u - c), m = u * m := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          ring
        have hlower : m * u ≤ ∫ x in (-c)..(u - c), g x := by
          rw [hconst] at hmono
          nlinarith [hmono]
        have hsplit : (∫ x in (-c)..(u - c), g x) + (∫ x in (u - c)..c, g x) = ∫ x in (-c)..c, g x :=
          intervalIntegral.integral_add_adjacent_intervals (hInt (-c) (u - c)) (hInt (u - c) c)
        have hsplit2 : (∫ x in (u - c)..c, g x) + (∫ x in c..(u + c), g x) = ∫ x in (u - c)..(u + c), g x :=
          intervalIntegral.integral_add_adjacent_intervals (hInt (u - c) c) (hInt c (u + c))
        have hzero_right : ∫ x in c..(u + c), g x = 0 := by
          rw [intervalIntegral.integral_of_le (show c ≤ u + c by linarith)]
          apply MeasureTheory.setIntegral_eq_zero_of_ae_eq_zero
          exact Filter.Eventually.of_forall (fun x hx => by
            apply hg_zero x
            rw [Set.mem_Ioc] at hx
            intro hmem
            rw [Set.mem_Icc] at hmem
            linarith [hx.1, hmem.2])
        have hK_eq : ∫ x in (u - c)..(u + c), g x = ∫ x in (u - c)..c, g x := by
          rw [← hsplit2, hzero_right]
          simp
        have hI2 : ∫ x in (u - c)..c, g x = 1 - ∫ x in (-c)..(u - c), g x := by
          have hs := hsplit
          rw [hbridge] at hs
          rw [← hs]
          ring_nf
        have hfin : ∫ x in (u - c)..(u + c), g x ≤ 1 - m * u := by
          rw [hK_eq, hI2]
          linarith [hlower]
        have hmax : 1 - m * u ≤ max 0 (1 - m * |u|) := by
          rw [huu]
          exact le_max_right 0 _
        exact le_trans hfin hmax
      · have hu0 : u < 0 := not_le.mp hu
        have huu : |u| = -u := abs_of_neg hu0
        have hu2c : -u ≤ 2 * c := by rw [← huu]; exact hu2
        have hmono : ∫ x in (u + c)..c, m ≤ ∫ x in (u + c)..c, g x :=
          intervalIntegral.integral_mono_on (show u + c ≤ c by linarith)
            intervalIntegral.intervalIntegrable_const (hInt (u + c) c)
            (fun x hx => by
              rw [Set.mem_Icc] at hx
              exact hg_min x (by
                rw [Set.mem_Icc]
                exact ⟨by linarith [hx.1, hu2c], hx.2⟩))
        have hconst : ∫ x in (u + c)..c, m = (-u) * m := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          ring
        have hlower : m * (-u) ≤ ∫ x in (u + c)..c, g x := by
          rw [hconst] at hmono
          nlinarith [hmono]
        have hsplit2 : (∫ x in (u - c)..(-c), g x) + (∫ x in (-c)..(u + c), g x) = ∫ x in (u - c)..(u + c), g x :=
          intervalIntegral.integral_add_adjacent_intervals (hInt (u - c) (-c)) (hInt (-c) (u + c))
        have hsplit : (∫ x in (-c)..(u + c), g x) + (∫ x in (u + c)..c, g x) = ∫ x in (-c)..c, g x :=
          intervalIntegral.integral_add_adjacent_intervals (hInt (-c) (u + c)) (hInt (u + c) c)
        have hzero_left : ∫ x in (u - c)..(-c), g x = 0 := by
          rw [intervalIntegral.integral_of_le (show u - c ≤ -c by linarith)]
          apply MeasureTheory.setIntegral_eq_zero_of_ae_eq_zero
          have hsub : Set.Ioc (u - c) (-c) ∩ Set.Icc (-c) c ⊆ {-c} := by
            intro x hx
            obtain ⟨hx1, hx2⟩ := hx
            rw [Set.mem_Ioc] at hx1
            rw [Set.mem_Icc] at hx2
            rw [Set.mem_singleton_iff]
            linarith [hx1.2, hx2.1]
          have hnull : volume (Set.Ioc (u - c) (-c) ∩ Set.Icc (-c) c) = 0 :=
            MeasureTheory.measure_mono_null hsub (by simp)
          have hae : ∀ᵐ x ∂volume, x ∉ Set.Ioc (u - c) (-c) ∩ Set.Icc (-c) c := by
            rw [MeasureTheory.ae_iff]
            simpa only [not_not] using hnull
          exact hae.mono (fun x hx hmem => by
            by_contra hgne
            exact hx ⟨hmem, by by_contra hnot; exact hgne (hg_zero x hnot)⟩)
        have hK_eq : ∫ x in (u - c)..(u + c), g x = ∫ x in (-c)..(u + c), g x := by
          rw [← hsplit2, hzero_left]
          simp
        have hI2 : ∫ x in (-c)..(u + c), g x = 1 - ∫ x in (u + c)..c, g x := by
          have hs := hsplit
          rw [hbridge] at hs
          rw [← hs]
          ring_nf
        have hfin : ∫ x in (u - c)..(u + c), g x ≤ 1 - m * (-u) := by
          rw [hK_eq, hI2]
          linarith [hlower]
        have hmax : 1 - m * (-u) ≤ max 0 (1 - m * |u|) := by
          rw [huu]
          exact le_max_right 0 _
        exact le_trans hfin hmax
    · have h2 : 2 * c ≤ |u| := le_of_lt (not_le.mp hu2)
      rw [hKzero u h2]
      exact le_max_left 0 (1 - m * |u|)
  refine ⟨?_, ?_, ?_⟩
  · exact MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun x _ => hg_nonneg (x - θ))
  · rw [hG_eq, ← abs_sub_comm (thetaStar ℓ) θ]
    exact hKbound (thetaStar ℓ - θ)
  · intro hδ
    have hu : 2 * c ≤ |thetaStar ℓ - θ| := by rw [abs_sub_comm (thetaStar ℓ) θ]; exact hδ
    rw [hG_eq]
    exact hKzero (thetaStar ℓ - θ) hu
  /- @proof-region region.target-node.session.8689499de5be4fe9 end -/

end

end Statlib.Imported

end DPCompletedProof
