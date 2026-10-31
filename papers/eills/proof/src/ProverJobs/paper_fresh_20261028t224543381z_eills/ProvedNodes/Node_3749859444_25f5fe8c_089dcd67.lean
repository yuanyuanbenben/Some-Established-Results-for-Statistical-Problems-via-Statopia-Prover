import ProverJobs.paper_fresh_20261028t224543381z_eills.Vocabulary
import ProverJobs.paper_fresh_20261028t224543381z_eills.Base

namespace PaperProofTasks.paper_fresh_20261028t224543381z_eills

open _root_.PaperProofTasks.paper_fresh_20261028t224543381z_eills.Statlib.Imported
open _root_.PaperProofTasks.paper_fresh_20261028t224543381z_eills.Statlib.Imported.StrongConvexityMain
open MeasureTheory ProbabilityTheory
open StrongConvexityMain

namespace Statlib.Imported

open MeasureTheory ProbabilityTheory
open _root_.PaperProofTasks.paper_fresh_20261028t224543381z_eills.Statlib.Imported.StrongConvexityMain

set_option autoImplicit false in
theorem statopia_math_node_3749859444_25f5fe8c : ∀ (p : ℕ) {ι : Type*} [Fintype ι] [Nonempty ι]
    (mu : ι → Measure (Eucl p × ℝ))
    (hmu : ∀ e : ι, IsProbabilityMeasure (mu e))
    (betaStar : Eucl p)
    (betaLocal : ι → Finset (Fin p) → Eucl p)
    (kappaL : ℝ) (hkappaL_pos : 0 < kappaL)
    (hIdent : ∀ S : Finset (Fin p), (S ∩ spurSet mu betaStar).Nonempty →
      ∃ e e' : ι, betaLocal e S ≠ betaLocal e' S),
    0 ≤ gammaStar mu betaLocal betaStar kappaL ∧
      ∀ S : Finset (Fin p),
        bCoeff mu betaStar S ≤
          kappaL ^ 3 * gammaStar mu betaLocal betaStar kappaL * dBar betaLocal S := by
  /- @proof-region region.target-node.session.bbdcd158e690afd4 begin -/
  intro p ι _ _ μ hμ βstar betaLocal kappaL hkappaL_pos hIdent
  have hbcoeff_nonneg : ∀ S : Finset (Fin p), 0 ≤ bCoeff μ βstar S := by
    intro S
    unfold bCoeff
    exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hdbar_nonneg : ∀ S : Finset (Fin p), 0 ≤ dBar betaLocal S := by
    intro S
    unfold dBar
    apply Finset.sum_nonneg
    intro e _
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (by unfold l2sq; positivity)
  have hset_nonneg : 0 ≤ sSup {r : ℝ | ∃ S : Finset (Fin p),
      (S ∩ spurSet μ βstar).Nonempty ∧ r = bCoeff μ βstar S / dBar betaLocal S} := by
    apply Real.sSup_nonneg
    intro r hr
    obtain ⟨S, _, rfl⟩ := hr
    exact div_nonneg (hbcoeff_nonneg S) (hdbar_nonneg S)
  have hgammaStar_nonneg : 0 ≤ gammaStar μ betaLocal βstar kappaL := by
    simp only [gammaStar]
    exact mul_nonneg (pow_nonneg (inv_nonneg.mpr (le_of_lt hkappaL_pos)) 3) hset_nonneg
  constructor
  · exact hgammaStar_nonneg
  · intro S
    classical
    have hkey : kappaL ^ 3 * gammaStar μ betaLocal βstar kappaL =
        sSup {r : ℝ | ∃ S : Finset (Fin p),
          (S ∩ spurSet μ βstar).Nonempty ∧ r = bCoeff μ βstar S / dBar betaLocal S} := by
      simp only [gammaStar]
      rw [← mul_assoc]
      have h2 : kappaL ^ 3 * kappaL⁻¹ ^ 3 = (1 : ℝ) := by
        rw [← mul_pow, mul_inv_cancel₀ hkappaL_pos.ne', one_pow]
      rw [h2]
      rw [one_mul]
    have hbdd : BddAbove {r : ℝ | ∃ S : Finset (Fin p),
        (S ∩ spurSet μ βstar).Nonempty ∧ r = bCoeff μ βstar S / dBar betaLocal S} := by
      apply Set.Finite.bddAbove
      apply Set.Finite.subset
        (Set.finite_range (fun S : Finset (Fin p) => bCoeff μ βstar S / dBar betaLocal S))
      intro r hr
      obtain ⟨S, _, rfl⟩ := hr
      exact ⟨S, rfl⟩
    by_cases hSp : (S ∩ spurSet μ βstar).Nonempty
    · have hdbar_pos : 0 < dBar betaLocal S := by
        obtain ⟨e, e', he⟩ := hIdent S hSp
        rcases lt_or_eq_of_le (hdbar_nonneg S) with hlt | heq
        · exact hlt
        · exfalso
          have hcard_pos : (0 : ℝ) < (Fintype.card ι : ℝ) := by
            exact_mod_cast Fintype.card_pos
          have hnni : (0 : ℝ) ≤ (Fintype.card ι : ℝ)⁻¹ :=
            le_of_lt (inv_pos.mpr hcard_pos)
          have hnn : ∀ x : ι, 0 ≤ (Fintype.card ι : ℝ)⁻¹ *
              l2sq (betaLocal x S - betaBar betaLocal S) :=
            fun x => mul_nonneg hnni (by unfold l2sq; positivity)
          have heq0 : dBar betaLocal S = 0 := heq.symm
          unfold dBar at heq0
          have hterm : ∀ x : ι, (Fintype.card ι : ℝ)⁻¹ *
              l2sq (betaLocal x S - betaBar betaLocal S) = 0 := by
            intro x
            have hle : (Fintype.card ι : ℝ)⁻¹ *
                l2sq (betaLocal x S - betaBar betaLocal S) ≤
                ∑ e, (Fintype.card ι : ℝ)⁻¹ *
                  l2sq (betaLocal e S - betaBar betaLocal S) :=
              Finset.single_le_sum (fun e _ => hnn e) (Finset.mem_univ x)
            rw [heq0] at hle
            linarith [hnn x]
          have hbar : ∀ x : ι, betaLocal x S = betaBar betaLocal S := by
            intro x
            have hx := hterm x
            have hinvne : (Fintype.card ι : ℝ)⁻¹ ≠ 0 := ne_of_gt (inv_pos.mpr hcard_pos)
            rcases mul_eq_zero.mp hx with h' | h'
            · exact absurd h' hinvne
            · have hnorm : ‖betaLocal x S - betaBar betaLocal S‖ = 0 := by
                unfold l2sq at h'
                have h2 : ‖betaLocal x S - betaBar betaLocal S‖ *
                    ‖betaLocal x S - betaBar betaLocal S‖ = 0 := by
                  rw [← pow_two]; exact h'
                exact mul_self_eq_zero.mp h2
              exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
          exact he ((hbar e).trans (hbar e').symm)
      have hmermat : bCoeff μ βstar S / dBar betaLocal S ≤
          sSup {r : ℝ | ∃ S : Finset (Fin p),
            (S ∩ spurSet μ βstar).Nonempty ∧ r = bCoeff μ βstar S / dBar betaLocal S} :=
        le_csSup hbdd ⟨S, hSp, rfl⟩
      have hmul : bCoeff μ βstar S ≤
          sSup {r : ℝ | ∃ S : Finset (Fin p),
            (S ∩ spurSet μ βstar).Nonempty ∧ r = bCoeff μ βstar S / dBar betaLocal S} *
          dBar betaLocal S := by
        have hle := mul_le_mul_of_nonneg_right hmermat (le_of_lt hdbar_pos)
        rwa [div_mul_cancel₀ _ (ne_of_gt hdbar_pos)] at hle
      rw [← hkey] at hmul
      exact hmul
    · have hbcoeff_zero : bCoeff μ βstar S = 0 := by
        unfold bCoeff
        apply Finset.sum_eq_zero
        intro j hj
        have hnotin : j ∉ spurSet μ βstar := fun hjin =>
          hSp ⟨j, Finset.mem_inter.mpr ⟨hj, hjin⟩⟩
        have hspur0 : ∑ e, ∫ z, z.1 j * residAt βstar z ∂(μ e) = 0 := by
          by_contra hne
          exact hnotin (by
            simp only [spurSet]
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hne⟩)
        have hsum0 : (∑ e, ∫ z, residAt βstar z * z.1 j ∂(μ e)) = 0 := by
          have hEq : (∑ e, ∫ z, residAt βstar z * z.1 j ∂(μ e)) =
              ∑ e, ∫ z, z.1 j * residAt βstar z ∂(μ e) := by
            apply Finset.sum_congr rfl
            intro e _
            apply integral_congr_ae
            filter_upwards with z
            ring
          rw [hEq, hspur0]
        rw [hsum0]
        simp
      rw [hbcoeff_zero]
      exact mul_nonneg (mul_nonneg (pow_nonneg (le_of_lt hkappaL_pos) 3) hgammaStar_nonneg)
        (hdbar_nonneg S)
  /- @proof-region region.target-node.session.bbdcd158e690afd4 end -/

end Statlib.Imported

