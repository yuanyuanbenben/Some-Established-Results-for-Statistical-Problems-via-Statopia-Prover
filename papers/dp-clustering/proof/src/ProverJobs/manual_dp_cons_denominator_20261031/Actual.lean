import ProverJobs.manual_dp_cons_finish_20261031.Denominator
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace ManualDPCons
open Statlib.Imported

def partitionDenominator {t : ℕ} (g q0 : ℝ → ℝ) (n : ℕ) (omega : ℕ → ℝ) : ℝ :=
  ∑ A ∈ dpTau n t, ∏ B ∈ A, ((B.card - 1).factorial : ℝ) * dpMargLik g q0 (dpXseq n omega) B

lemma marginal_nonneg {n : ℕ} (g q0 : ℝ → ℝ) (hg : ∀ x, 0 ≤ g x)
    (hq : ∀ x, 0 ≤ q0 x) (x : Fin n → ℝ) (B : Finset (Fin n)) :
    0 ≤ dpMargLik g q0 x B := by
  apply integral_nonneg
  intro theta
  exact mul_nonneg (Finset.prod_nonneg (fun i _ => hg _)) (hq _)

/-- The actual true-window partition contributes a quantitative positive denominator.
No partition likelihood or denominator lower bound is assumed. -/
lemma omega_denominator_lower {t n : ℕ} (c R L r ell : ℝ)
    (theta : Fin t → ℝ) (N : Fin t → ℕ) (omega : ℕ → ℝ) (g q0 : ℝ → ℝ)
    (hgmeas : Measurable g) (hg0 : ∀ z, 0 ≤ g z)
    (hgpos : ∀ z ∈ Set.Ioo (-c) c, 0 < g z)
    (hgdiff : DifferentiableOn ℝ g (Set.Ioo (-c) c))
    (hgderiv : ∀ z ∈ Set.Ioo (-c) c, |deriv g z / g z| ≤ R)
    (hgupper : ∃ M : ℝ, 0 ≤ M ∧ ∀ z, g z ≤ M)
    (hqmeas : Measurable q0) (hq0 : ∀ z, 0 ≤ q0 z) (hqint : Integrable q0 volume)
    (hR : 0 ≤ R) (hL : 0 ≤ L) (hr : 0 < r) (hell : 1 ≤ ell)
    (hT4 : ∀ j z, |z - theta j| < r → L ≤ q0 z)
    (hN : ∀ j, 1 ≤ N j) (hOmega : dpOmega c theta N n omega)
    (hell_def : ell = (Real.log (n : ℝ)) ^ ((1 : ℝ) / (2 * (t : ℝ))))
    (hinterior : ∀ j i, i ∈ dpBlock c theta n omega j → -c < omega (i : ℕ) - theta j)
    (hsep : ∀ j k, j ≠ k → 2 * c < |theta j - theta k|)
    (hcover : ∀ i : Fin n, ∃ j, omega (i : ℕ) ∈ Set.Icc (theta j - c) (theta j + c)) :
    (L * Real.exp (-R) * min 1 r / (2 * ell)) ^ t *
      ∏ j : Fin t, (((dpBlock c theta n omega j).card - 1).factorial : ℝ) *
        ((∏ i ∈ dpBlock c theta n omega j, g (omega (i : ℕ) - theta j)) /
          ((dpBlock c theta n omega j).card : ℝ)) ≤
      partitionDenominator (t := t) g q0 n omega := by
  classical
  let B := fun j => dpBlock c theta n omega j
  let a := L * Real.exp (-R) * min 1 r / (2 * ell)
  let f := fun (b : Finset (Fin n)) => ((b.card - 1).factorial : ℝ) * dpMargLik g q0 (dpXseq n omega) b
  have hne : ∀ j, (B j).Nonempty := fun j => Finset.one_le_card.mp ((hN j).trans (hOmega j).1)
  have hinj : Function.Injective B := by
    intro j k heq
    by_contra hjk
    obtain ⟨i, hi⟩ := hne j
    exact Finset.disjoint_left.mp (true_windows_disjoint c theta hsep n omega j k hjk)
      hi (by simpa only [B, ← heq] using hi)
  have hmem := true_partition_mem c theta omega hsep hcover hne
  have hsum : (∏ j : Fin t, f (B j)) ≤ partitionDenominator (t := t) g q0 n omega := by
    have himage : (∏ b ∈ Finset.univ.image B, f b) = ∏ j : Fin t, f (B j) :=
      Finset.prod_image (fun j _ k _ hjk => hinj hjk)
    rw [← himage]
    change (∏ b ∈ Finset.univ.image B, f b) ≤ ∑ A ∈ dpTau n t, ∏ b ∈ A, f b
    apply Finset.single_le_sum (f := fun A : Finset (Finset (Fin n)) => ∏ b ∈ A, f b)
      (a := Finset.univ.image B)
    · intro A hA
      exact Finset.prod_nonneg (fun b _ => mul_nonneg (by positivity) (marginal_nonneg g q0 hg0 hq0 _ b))
    · exact hmem
  apply le_trans _ hsum
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hprod : (∏ j : Fin t, a * ((((B j).card - 1).factorial : ℝ) *
      ((∏ i ∈ B j, g (omega (i : ℕ) - theta j)) / ((B j).card : ℝ)))) ≤
      ∏ j : Fin t, f (B j) := by
    apply Finset.prod_le_prod
    · intro j hj
      exact mul_nonneg ha (mul_nonneg (by positivity)
        (div_nonneg (Finset.prod_nonneg (fun i hi => hg0 _)) (by positivity)))
    · intro j hj
      have h := omega_marginal_lower j c R L r ell theta N omega g q0 hgmeas hg0 hgpos
        hgdiff hgderiv hgupper hqmeas hq0 hqint hR hL hr hell (hT4 j) (hN j)
        hOmega hell_def (hinterior j)
      dsimp only [f, B]
      have hh := mul_le_mul_of_nonneg_left h (show (0:ℝ) ≤ (((dpBlock c theta n omega j).card - 1).factorial : ℝ) by positivity)
      dsimp only [a]
      convert hh using 1 <;> ring
  simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, a, B] using hprod


lemma omega_denominator_positive_inverse {t n : ℕ} (c R L r ell : ℝ)
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
    (hcover : ∀ i : Fin n, ∃ j, omega (i : ℕ) ∈ Set.Icc (theta j - c) (theta j + c)) :
    0 < partitionDenominator (t := t) g q0 n omega ∧
    (partitionDenominator (t := t) g q0 n omega)⁻¹ ≤
      ell ^ t / (L * Real.exp (-R) * min 1 r / 2) ^ t *
        ∏ j : Fin t, ((dpBlock c theta n omega j).card : ℝ) /
          ((((dpBlock c theta n omega j).card - 1).factorial : ℝ) *
            (∏ i ∈ dpBlock c theta n omega j, g (omega (i : ℕ) - theta j))) := by
  classical
  let B := fun j => dpBlock c theta n omega j
  let C := L * Real.exp (-R) * min 1 r / 2
  let u := fun j => (((B j).card - 1).factorial : ℝ) *
    ((∏ i ∈ B j, g (omega (i : ℕ) - theta j)) / ((B j).card : ℝ))
  have hC : 0 < C := by dsimp [C]; positivity
  have hellpos : 0 < ell := by linarith
  have hcard : ∀ j, 0 < ((B j).card : ℝ) := by
    intro j
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one ((hN j).trans (hOmega j).1)
  have hgp : ∀ j, 0 < ∏ i ∈ B j, g (omega (i : ℕ) - theta j) := by
    intro j
    apply Finset.prod_pos
    intro i hi
    have hm : omega (i : ℕ) ∈ Set.Icc (theta j - c) (theta j + c) := by
      simpa [B, dpBlock] using hi
    apply hgpos
    constructor <;> linarith [hm.1, hm.2]
  have hu : ∀ j, 0 < u j := fun j => mul_pos (by positivity) (div_pos (hgp j) (hcard j))
  have hlow := omega_denominator_lower c R L r ell theta N omega g q0 hgmeas hg0
    (fun z hz => hgpos z ⟨hz.1.le, hz.2.le⟩) hgdiff hgderiv hgupper hqmeas hq0 hqint hR
    hL.le hr hell hT4 hN hOmega hell_def hinterior hsep hcover
  have hlow' : (C / ell) ^ t * (∏ j : Fin t, u j) ≤ partitionDenominator (t := t) g q0 n omega := by
    convert hlow using 1
    congr 2
    dsimp [C]
    ring
  have hpos : 0 < (C / ell) ^ t * (∏ j : Fin t, u j) :=
    mul_pos (pow_pos (div_pos hC hellpos) _) (Finset.prod_pos (fun j _ => hu j))
  refine ⟨hpos.trans_le hlow', ?_⟩
  have hinv : (partitionDenominator (t := t) g q0 n omega)⁻¹ ≤
      ((C / ell) ^ t * (∏ j : Fin t, u j))⁻¹ := by
    exact inv_anti₀ hpos hlow'
  apply hinv.trans_eq
  rw [mul_inv, ← Finset.prod_inv_distrib, ← inv_pow, inv_div, div_pow]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  dsimp only [u, B]
  field_simp

lemma logroot_pow (t n : ℕ) (ht : 1 ≤ t) (hn : 1 < (n : ℝ)) :
    ((Real.log (n : ℝ)) ^ ((1 : ℝ) / (2 * (t : ℝ)))) ^ t =
      (Real.log (n : ℝ)) ^ ((1 : ℝ) / 2) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Real.log_pos hn).le]
  congr 1
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one ht))
  field_simp


lemma logroot_one_le (t n : ℕ) (hn : 3 ≤ n) :
    1 ≤ (Real.log (n : ℝ)) ^ ((1 : ℝ) / (2 * (t : ℝ))) := by
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hexp : Real.exp 1 ≤ (n : ℝ) := Real.exp_one_lt_three.le.trans hnR
  have hlog : 1 ≤ Real.log (n : ℝ) := (Real.le_log_iff_exp_le (by linarith)).mpr hexp
  exact Real.one_le_rpow hlog (by positivity)

/-- The denominator loss is exactly a square root of log n; t is fixed and positive. -/
lemma omega_denominator_log_inverse {t n : ℕ} (c R L r ell : ℝ)
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
    (hcover : ∀ i : Fin n, ∃ j, omega (i : ℕ) ∈ Set.Icc (theta j - c) (theta j + c))
    (ht : 1 ≤ t) (hn : 1 < (n : ℝ)) :
    0 < partitionDenominator (t := t) g q0 n omega ∧
    (partitionDenominator (t := t) g q0 n omega)⁻¹ ≤
      (Real.log (n : ℝ)) ^ ((1 : ℝ) / 2) /
        (L * Real.exp (-R) * min 1 r / 2) ^ t *
        ∏ j : Fin t, ((dpBlock c theta n omega j).card : ℝ) /
          ((((dpBlock c theta n omega j).card - 1).factorial : ℝ) *
            (∏ i ∈ dpBlock c theta n omega j, g (omega (i : ℕ) - theta j))) := by
  have h := omega_denominator_positive_inverse c R L r ell theta N omega g q0 hgmeas hg0
    hgpos hgdiff hgderiv hgupper hqmeas hq0 hqint hR hL hr hell hT4 hN hOmega
    hell_def hinterior hsep hcover
  rw [hell_def, logroot_pow t n ht hn] at h
  exact h

#print axioms omega_denominator_log_inverse

#print axioms omega_denominator_positive_inverse
#print axioms logroot_pow

#print axioms omega_denominator_lower
end ManualDPCons
