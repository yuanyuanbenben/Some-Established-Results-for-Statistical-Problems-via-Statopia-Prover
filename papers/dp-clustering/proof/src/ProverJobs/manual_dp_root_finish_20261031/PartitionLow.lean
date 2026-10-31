import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.Base

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal
open Statlib.Imported

noncomputable section
namespace OfflineDPRootPartitionLow

/-- Fewer than t nonempty covering blocks must put two of t marked indices in
one block. The marked indices need not separately be assumed injective. -/
theorem partition_has_two_marked {n t s : ℕ} (idx : Fin t → Fin n)
    (A : Finset (Finset (Fin n))) (hA : IsPartitionOf n s A) (hst : s < t) :
    ∃ B ∈ A, ∃ i j : Fin t, i ≠ j ∧ idx i ∈ B ∧ idx j ∈ B := by
  classical
  by_contra h
  push_neg at h
  let block : Fin t → ↥A := fun j =>
    ⟨Classical.choose (hA.2.2.2 (idx j)), (Classical.choose_spec (hA.2.2.2 (idx j))).1⟩
  have hmem : ∀ j, idx j ∈ (block j).1 := fun j =>
    (Classical.choose_spec (hA.2.2.2 (idx j))).2
  have hinj : Function.Injective block := by
    intro i j hij
    by_contra hne
    have hji : idx j ∈ (block i).1 := by rw [hij]; exact hmem j
    exact h (block i).1 (block i).2 i j hne (hmem i) hji
  have hcard := Fintype.card_le_of_injective block hinj
  have hts : t ≤ s := by simpa only [Fintype.card_fin, Fintype.card_coe, hA.1] using hcard
  omega

/-- A kernel supported on [-c,c] cannot explain two observations more than 2c
apart using a single location parameter. -/
theorem separated_pair_product_zero (g : ℝ → ℝ) (c : ℝ)
    (hsupport : ∀ y : ℝ, y ∉ Set.Icc (-c) c → g y = 0)
    {n : ℕ} (x : Fin n → ℝ) (B : Finset (Fin n)) (i j : Fin n)
    (hi : i ∈ B) (hj : j ∈ B) (hsep : 2 * c < |x i - x j|) (θ : ℝ) :
    (∏ k ∈ B, g (x k - θ)) = 0 := by
  classical
  have hzero : g (x i - θ) = 0 ∨ g (x j - θ) = 0 := by
    by_cases hzi : g (x i - θ) = 0
    · exact Or.inl hzi
    · right
      apply hsupport
      intro hmj
      have hmi : x i - θ ∈ Set.Icc (-c) c := by
        by_contra hmi
        exact hzi (hsupport _ hmi)
      have hbound : |x i - x j| ≤ 2 * c := by
        rw [abs_le]
        constructor <;> linarith [hmi.1, hmi.2, hmj.1, hmj.2]
      exact (not_lt_of_ge hbound) hsep
  rcases hzero with hzero | hzero
  · exact Finset.prod_eq_zero hi hzero
  · exact Finset.prod_eq_zero hj hzero

/-- A block containing an incompatible marked pair has exactly zero marginal
likelihood. No integrability convention is used: the integrand is pointwise zero. -/
theorem separated_pair_margLik_zero (g q0 : ℝ → ℝ) (c : ℝ)
    (hsupport : ∀ y : ℝ, y ∉ Set.Icc (-c) c → g y = 0)
    {n : ℕ} (x : Fin n → ℝ) (B : Finset (Fin n)) (i j : Fin n)
    (hi : i ∈ B) (hj : j ∈ B) (hsep : 2 * c < |x i - x j|) :
    margLik g q0 B x = 0 := by
  unfold margLik
  have hzero : (fun θ : ℝ => (∏ k ∈ B, g (x k - θ)) * q0 θ) = 0 := by
    funext θ
    rw [separated_pair_product_zero g c hsupport x B i j hi hj hsep θ, zero_mul]
    rfl
  simp only [hzero, Pi.zero_def, integral_zero]

/-- The actual EPPF numerator for fewer than t clusters vanishes whenever the
sample contains t observations pairwise farther apart than the kernel width. -/
theorem jointMass_lt_true_zero (g q0 : ℝ → ℝ) (c : ℝ)
    (hsupport : ∀ y : ℝ, y ∉ Set.Icc (-c) c → g y = 0)
    (π : Measure ℝ) {n t s : ℕ} (x : Fin n → ℝ) (idx : Fin t → Fin n)
    (hsep : ∀ i j : Fin t, i ≠ j → 2 * c < |x (idx i) - x (idx j)|)
    (hst : s < t) : jointMass g q0 π n s x = 0 := by
  classical
  unfold jointMass
  apply Finset.sum_eq_zero
  intro A hA
  have hp : IsPartitionOf n s A := (Finset.mem_filter.mp hA).2
  obtain ⟨B, hBA, i, j, hij, hi, hj⟩ := partition_has_two_marked idx A hp hst
  have hBzero := separated_pair_margLik_zero g q0 c hsupport x B (idx i) (idx j)
    hi hj (hsep i j hij)
  rw [Finset.prod_eq_zero hBA hBzero, mul_zero]

/-- Division by a common evidence denominator does not create low-cluster mass,
even at degenerate samples where the real division convention sets 0/0 to zero. -/
theorem postProb_lt_true_zero (g q0 : ℝ → ℝ) (c : ℝ)
    (hsupport : ∀ y : ℝ, y ∉ Set.Icc (-c) c → g y = 0)
    (π : Measure ℝ) {n t s : ℕ} (x : Fin n → ℝ) (idx : Fin t → Fin n)
    (hsep : ∀ i j : Fin t, i ≠ j → 2 * c < |x (idx i) - x (idx j)|)
    (hst : s < t) : postProb g q0 π n s x = 0 := by
  rw [postProb, jointMass_lt_true_zero g q0 c hsupport π x idx hsep hst, zero_div]

theorem low_tail_sum_zero (g q0 : ℝ → ℝ) (c : ℝ)
    (hsupport : ∀ y : ℝ, y ∉ Set.Icc (-c) c → g y = 0)
    (π : Measure ℝ) {n t : ℕ} (x : Fin n → ℝ) (idx : Fin t → Fin n)
    (hsep : ∀ i j : Fin t, i ≠ j → 2 * c < |x (idx i) - x (idx j)|) :
    (∑ s ∈ Finset.Icc 1 (t - 1), postProb g q0 π n s x) = 0 := by
  apply Finset.sum_eq_zero
  intro s hs
  have hst : s < t := by have := Finset.mem_Icc.mp hs; omega
  exact postProb_lt_true_zero g q0 c hsupport π x idx hsep hst

#print axioms partition_has_two_marked
#print axioms jointMass_lt_true_zero
#print axioms low_tail_sum_zero
end OfflineDPRootPartitionLow
