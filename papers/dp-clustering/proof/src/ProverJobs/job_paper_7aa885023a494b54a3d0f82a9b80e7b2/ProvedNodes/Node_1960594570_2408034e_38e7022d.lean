import ProverJobs.job_paper_7aa885023a494b54a3d0f82a9b80e7b2.Vocabulary
import ProverJobs.job_paper_7aa885023a494b54a3d0f82a9b80e7b2.Base

open MeasureTheory
open scoped ENNReal BigOperators
open Statlib.Imported

open MeasureTheory
open scoped ENNReal BigOperators
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_1960594570_2408034e : ∀ (t : ℕ) (p thetaStar : Fin t → ℝ) (c : ℝ) (g : ℝ → ℝ)
    (hp_pos : ∀ j : Fin t, 0 < p j)
    (hp_sum : ∑ j : Fin t, p j = 1)
    (hc : 0 < c)
    (hg_pos : ∀ x ∈ Set.Icc (-c) c, 0 < g x)
    (hg_zero : ∀ x, x ∉ Set.Icc (-c) c → g x = 0)
    (hg_meas : Measurable g)
    (hg_int : Integrable g volume)
    (hg_mass : ∫ x, g x ∂volume = 1),
    (mixtureLaw p thetaStar g) Set.univ = 1 ∧
      IsProbabilityMeasure (mixtureLaw p thetaStar g) := by
  /- @proof-region region.target-node.session.15046c23df3e8e0f begin -/
  intro t p thetaStar c g hp_pos hp_sum hc hg_pos hg_zero hg_meas hg_int hg_mass
  have hg_nonneg : ∀ x : ℝ, 0 ≤ g x := by
    intro x
    by_cases hx : x ∈ Set.Icc (-c) c
    · exact (hg_pos x hx).le
    · rw [hg_zero x hx]
  have hsummand_int : ∀ j : Fin t, Integrable (fun x : ℝ => p j * g (x - thetaStar j)) volume := by
    intro j
    exact (hg_int.comp_sub_right (thetaStar j)).const_mul (p j)
  have hsplit : ∫ x, (∑ j : Fin t, p j * g (x - thetaStar j)) ∂volume
      = ∑ j : Fin t, ∫ x, p j * g (x - thetaStar j) ∂volume :=
    integral_finset_sum Finset.univ (fun j _ => hsummand_int j)
  have hsingle : ∀ j : Fin t, ∫ x, p j * g (x - thetaStar j) ∂volume = p j := by
    intro j
    rw [integral_const_mul, integral_sub_right_eq_self, hg_mass, mul_one]
  have hP : (∑ j : Fin t, ∫ x, p j * g (x - thetaStar j) ∂volume) = ∑ j : Fin t, p j :=
    Finset.sum_congr rfl fun j _ => hsingle j
  have hsum_int : ∫ x, (∑ j : Fin t, p j * g (x - thetaStar j)) ∂volume = 1 := by
    rw [hsplit, hP, hp_sum]
  have hρ_int : Integrable (fun x : ℝ => ∑ j : Fin t, p j * g (x - thetaStar j)) volume :=
    integrable_finset_sum Finset.univ (fun j _ => hsummand_int j)
  have hρ_nonneg : ∀ᵐ x ∂volume, 0 ≤ ∑ j : Fin t, p j * g (x - thetaStar j) :=
    Filter.Eventually.of_forall fun x =>
      Finset.sum_nonneg fun j _ => mul_nonneg (hp_pos j).le (hg_nonneg _)
  have hbridge : ENNReal.ofReal (∫ x, (∑ j : Fin t, p j * g (x - thetaStar j)) ∂volume)
      = ∫⁻ x, ENNReal.ofReal (∑ j : Fin t, p j * g (x - thetaStar j)) ∂volume :=
    ofReal_integral_eq_lintegral_ofReal hρ_int hρ_nonneg
  have hmass : ∫⁻ x, ENNReal.ofReal (∑ j : Fin t, p j * g (x - thetaStar j)) ∂volume = 1 := by
    rw [← hbridge, hsum_int]
    simp
  have hmass_univ : mixtureLaw p thetaStar g Set.univ
      = ∫⁻ x, ENNReal.ofReal (∑ j : Fin t, p j * g (x - thetaStar j)) ∂volume := by
    rw [mixtureLaw, withDensity_apply' _ Set.univ]
    simp
  constructor
  · rw [hmass_univ, hmass]
  · exact ⟨by rw [hmass_univ, hmass]⟩
  /- @proof-region region.target-node.session.15046c23df3e8e0f end -/

end Statlib.Imported
