import ProverJobs.manual_dp_cons_finish_20261031.Expectation
import ProverJobs.manual_dp_root_finish_20261031.LabelCells
import ProverJobs.manual_dp_cons_denominator_20261031.Actual
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace ManualDPCons
attribute [local instance] Classical.propDecidable
open Statlib.Imported

lemma product_blocks_truth {t n : ℕ} (c : ℝ) (theta : Fin t → ℝ)
    (hsep : ∀ j k, j ≠ k → 2 * c < |theta j-theta k|)
    (lab : Fin n → Fin t) (omega : ℕ → ℝ) (g : ℝ → ℝ)
    (hcell : ∀ i : Fin n, omega (i : ℕ) ∈ Set.Icc (theta (lab i)-c) (theta (lab i)+c)) :
    (∏ j : Fin t, ∏ i ∈ dpBlock c theta n omega j, g (omega (i : ℕ)-theta j)) =
      ∏ i : Fin n, g (omega (i : ℕ)-theta (lab i)) := by
  classical
  have hblocks : ∀ j : Fin t,
      (∏ i ∈ dpBlock c theta n omega j, g (omega (i : ℕ)-theta j)) =
      ∏ i ∈ Finset.univ.filter (fun i : Fin n => lab i = j), g (omega (i : ℕ)-theta (lab i)) := by
    intro j
    rw [OfflineDPLabelCells.actual_block_eq_fiber c theta hsep lab omega hcell j]
    apply Finset.prod_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  simp_rw [hblocks]
  exact Finset.prod_fiberwise Finset.univ lab (fun i => g (omega (i : ℕ)-theta (lab i)))

lemma label_inverse_product {t n : ℕ} (c : ℝ) (theta : Fin t → ℝ)
    (hsep : ∀ j k, j ≠ k → 2 * c < |theta j-theta k|)
    (lab : Fin n → Fin t) (omega : ℕ → ℝ) (g : ℝ → ℝ)
    (hcell : ∀ i : Fin n, omega (i : ℕ) ∈ Set.Icc (theta (lab i)-c) (theta (lab i)+c)) :
    (∏ j : Fin t, ((dpBlock c theta n omega j).card : ℝ) /
      ((((dpBlock c theta n omega j).card - 1).factorial : ℝ) *
        ∏ i ∈ dpBlock c theta n omega j, g (omega (i : ℕ)-theta j))) =
    (∏ j : Fin t, ((Finset.univ.filter (fun i : Fin n => lab i = j)).card : ℝ) /
      (((Finset.univ.filter (fun i : Fin n => lab i = j)).card - 1).factorial : ℝ)) /
      (∏ i : Fin n, g (omega (i : ℕ)-theta (lab i))) := by
  classical
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib,
    product_blocks_truth c theta hsep lab omega g hcell, div_mul_eq_div_div, ← Finset.prod_div_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [OfflineDPLabelCells.actual_block_eq_fiber c theta hsep lab omega hcell j]

lemma omega_partition_ratio_label {t n : ℕ} (c R L r ell : ℝ)
    (theta : Fin t → ℝ) (N : Fin t → ℕ) (omega : ℕ → ℝ) (g q0 : ℝ → ℝ)
    (hgmeas : Measurable g) (hg0 : ∀ z, 0 ≤ g z)
    (hgpos : ∀ z ∈ Set.Icc (-c) c, 0 < g z)
    (hgdiff : DifferentiableOn ℝ g (Set.Ioo (-c) c))
    (hgderiv : ∀ z ∈ Set.Ioo (-c) c, |deriv g z / g z| ≤ R)
    (hgupper : ∃ M : ℝ, 0 ≤ M ∧ ∀ z, g z ≤ M)
    (hqmeas : Measurable q0) (hq0 : ∀ z, 0 ≤ q0 z) (hqint : Integrable q0 volume)
    (hR : 0 ≤ R) (hL : 0 < L) (hr : 0 < r) (hell : 1 ≤ ell)
    (hT4 : ∀ j z, |z - theta j| < r → L ≤ q0 z)
    (hN : ∀ j, 1 ≤ N j) (hOmega : dpOmega c theta N n omega)
    (hell_def : ell = (Real.log (n : ℝ)) ^ ((1 : ℝ) / (2 * (t : ℝ))))
    (hinterior : ∀ j i, i ∈ dpBlock c theta n omega j → -c < omega (i : ℕ) - theta j)
    (hsep : ∀ j k, j ≠ k → 2 * c < |theta j - theta k|)
    (ht : 1 ≤ t) (hn : 1 < (n : ℝ))
    (k : ℕ) (lab : Fin n → Fin t)
    (hcell : ∀ i : Fin n, omega (i : ℕ) ∈ Set.Icc (theta (lab i)-c) (theta (lab i)+c)) :
    partitionSum g q0 n k (dpXseq n omega) / partitionSum g q0 n t (dpXseq n omega) ≤
      ((Real.log (n : ℝ)) ^ ((1 : ℝ) / 2) /
          (L * Real.exp (-R) * min 1 r / 2) ^ t) *
        (∏ j : Fin t, ((Finset.univ.filter (fun i : Fin n => lab i = j)).card : ℝ) /
          (((Finset.univ.filter (fun i : Fin n => lab i = j)).card - 1).factorial : ℝ)) *
        partitionSum g q0 n k (dpXseq n omega) /
        (∏ i : Fin n, g (omega (i : ℕ)-theta (lab i))) := by
  have hcover : ∀ i : Fin n, ∃ j, omega (i : ℕ) ∈ Set.Icc (theta j-c) (theta j+c) :=
    fun i => ⟨lab i, hcell i⟩
  have h := (omega_denominator_log_inverse c R L r ell theta N omega g q0 hgmeas hg0 hgpos
    hgdiff hgderiv hgupper hqmeas hq0 hqint hR hL hr hell hT4 hN hOmega hell_def
    hinterior hsep hcover ht hn).2
  rw [label_inverse_product c theta hsep lab omega g hcell] at h
  change (partitionSum g q0 n t (dpXseq n omega))⁻¹ ≤ _ at h
  calc
    _ = partitionSum g q0 n k (dpXseq n omega) * (partitionSum g q0 n t (dpXseq n omega))⁻¹ := div_eq_mul_inv _ _
    _ ≤ partitionSum g q0 n k (dpXseq n omega) *
      ((Real.log (n : ℝ)) ^ ((1 : ℝ) / 2) / (L * Real.exp (-R) * min 1 r / 2) ^ t *
       ((∏ j : Fin t, ((Finset.univ.filter (fun i : Fin n => lab i = j)).card : ℝ) /
          (((Finset.univ.filter (fun i : Fin n => lab i = j)).card - 1).factorial : ℝ)) /
        (∏ i : Fin n, g (omega (i : ℕ)-theta (lab i))))) :=
      mul_le_mul_of_nonneg_left h (partitionSum_nonneg g q0 hg0 hq0 n k _)
    _ = _ := by ring


/-- The Omega indicator is handled pointwise, including label cells with an empty class. -/
lemma omega_indicator_partition_ratio_label {t n : ℕ} (c R L r ell : ℝ)
    (theta : Fin t → ℝ) (N : Fin t → ℕ) (omega : ℕ → ℝ) (g q0 : ℝ → ℝ)
    (hgmeas : Measurable g) (hg0 : ∀ z, 0 ≤ g z)
    (hgpos : ∀ z ∈ Set.Icc (-c) c, 0 < g z)
    (hgdiff : DifferentiableOn ℝ g (Set.Ioo (-c) c))
    (hgderiv : ∀ z ∈ Set.Ioo (-c) c, |deriv g z / g z| ≤ R)
    (hgupper : ∃ M : ℝ, 0 ≤ M ∧ ∀ z, g z ≤ M)
    (hqmeas : Measurable q0) (hq0 : ∀ z, 0 ≤ q0 z) (hqint : Integrable q0 volume)
    (hR : 0 ≤ R) (hL : 0 < L) (hr : 0 < r) (hell : 1 ≤ ell)
    (hT4 : ∀ j z, |z - theta j| < r → L ≤ q0 z)
    (hN : ∀ j, 1 ≤ N j)
    (hell_def : ell = (Real.log (n : ℝ)) ^ ((1 : ℝ) / (2 * (t : ℝ))))
    (hinterior : ∀ j i, i ∈ dpBlock c theta n omega j → -c < omega (i : ℕ) - theta j)
    (hsep : ∀ j k, j ≠ k → 2 * c < |theta j - theta k|)
    (ht : 1 ≤ t) (hn : 1 < (n : ℝ))
    (k : ℕ) (lab : Fin n → Fin t)
    (hcell : ∀ i : Fin n, omega (i : ℕ) ∈ Set.Icc (theta (lab i)-c) (theta (lab i)+c)) :
    (if dpOmega c theta N n omega then
      partitionSum g q0 n k (dpXseq n omega) / partitionSum g q0 n t (dpXseq n omega) else 0) ≤
      ((Real.log (n : ℝ)) ^ ((1 : ℝ) / 2) /
          (L * Real.exp (-R) * min 1 r / 2) ^ t) *
        (∏ j : Fin t, ((Finset.univ.filter (fun i : Fin n => lab i = j)).card : ℝ) /
          (((Finset.univ.filter (fun i : Fin n => lab i = j)).card - 1).factorial : ℝ)) *
        partitionSum g q0 n k (dpXseq n omega) /
        (∏ i : Fin n, g (omega (i : ℕ)-theta (lab i))) := by
  classical
  by_cases hOmega : dpOmega c theta N n omega
  · rw [if_pos hOmega]
    exact omega_partition_ratio_label c R L r ell theta N omega g q0 hgmeas hg0 hgpos
      hgdiff hgderiv hgupper hqmeas hq0 hqint hR hL hr hell hT4 hN hOmega hell_def
      hinterior hsep ht hn k lab hcell
  · rw [if_neg hOmega]
    have hF := partitionSum_nonneg g q0 hg0 hq0 n k (dpXseq n omega)
    have hprod : 0 ≤ ∏ i : Fin n, g (omega (i : ℕ)-theta (lab i)) :=
      Finset.prod_nonneg (fun i _ => hg0 _)
    have hfac : 0 ≤ (∏ j : Fin t, ((Finset.univ.filter (fun i : Fin n => lab i = j)).card : ℝ) /
      (((Finset.univ.filter (fun i : Fin n => lab i = j)).card - 1).factorial : ℝ)) := by
      apply Finset.prod_nonneg
      intro j hj
      positivity
    positivity

#print axioms omega_indicator_partition_ratio_label

#print axioms omega_partition_ratio_label
end ManualDPCons
