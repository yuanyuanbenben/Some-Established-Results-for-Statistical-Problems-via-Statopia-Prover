import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M001_Base

/- Original module ProverJobs.manual_dp_cons_finish_20261031.Denominator; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace ManualDPCons
open Statlib.Imported

/-- Interior-point log-derivative estimate; endpoint values are not silently regularized. -/
lemma kernel_shift_lower (c R : ℝ) (g : ℝ → ℝ)
    (hgpos : ∀ x ∈ Set.Ioo (-c) c, 0 < g x)
    (hgdiff : DifferentiableOn ℝ g (Set.Ioo (-c) c))
    (hgderiv : ∀ x ∈ Set.Ioo (-c) c, |deriv g x / g x| ≤ R)
    (y u : ℝ) (hy : y ∈ Set.Ioo (-c) c) (hu : 0 ≤ u)
    (hyu : y + u ∈ Set.Ioo (-c) c) :
    g y * Real.exp (-R * u) ≤ g (y + u) := by
  have hdiff : ∀ x ∈ Set.Ioo (-c) c, DifferentiableAt ℝ (fun z => Real.log (g z)) x := by
    intro x hx
    exact ((hgdiff x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)).log (ne_of_gt (hgpos x hx))
  have hbound : ∀ x ∈ Set.Ioo (-c) c, ‖deriv (fun z => Real.log (g z)) x‖ ≤ R := by
    intro x hx
    rw [deriv.log ((hgdiff x hx).differentiableAt (isOpen_Ioo.mem_nhds hx))
      (ne_of_gt (hgpos x hx)), Real.norm_eq_abs]
    exact hgderiv x hx
  have h := (convex_Ioo (-c) c).norm_image_sub_le_of_norm_deriv_le hdiff hbound hy hyu
  simp only [Real.norm_eq_abs, add_sub_cancel_left, abs_of_nonneg hu] at h
  have hl : Real.log (g y) + -R * u ≤ Real.log (g (y + u)) := by
    have hh := (abs_le.mp h).1
    linarith
  have he := Real.exp_le_exp.mpr hl
  simpa only [Real.exp_add, Real.exp_log (hgpos y hy), Real.exp_log (hgpos (y + u) hyu)] using he

/-- A small one-sided parameter interval gives a concrete whole-block denominator bound. -/
lemma marginal_block_lower {n : ℕ} (B : Finset (Fin n)) (x : Fin n → ℝ)
    (c R L r delta theta : ℝ) (g q0 : ℝ → ℝ)
    (hgmeas : Measurable g) (hg0 : ∀ z, 0 ≤ g z)
    (hgpos : ∀ z ∈ Set.Ioo (-c) c, 0 < g z)
    (hgdiff : DifferentiableOn ℝ g (Set.Ioo (-c) c))
    (hgderiv : ∀ z ∈ Set.Ioo (-c) c, |deriv g z / g z| ≤ R)
    (hgupper : ∃ M : ℝ, 0 ≤ M ∧ ∀ z, g z ≤ M)
    (hqmeas : Measurable q0) (hq0 : ∀ z, 0 ≤ q0 z) (hqint : Integrable q0 volume)
    (hR : 0 ≤ R) (hL : 0 ≤ L) (hdelta : 0 < delta) (hdr : delta ≤ r)
    (hT4 : ∀ z, |z - theta| < r → L ≤ q0 z)
    (hsmall : (B.card : ℝ) * delta ≤ 1)
    (hx : ∀ i ∈ B, -c < x i - theta ∧ x i - theta + delta ≤ c) :
    L * Real.exp (-R) * delta * (∏ i ∈ B, g (x i - theta)) ≤
      dpMargLik g q0 x B := by
  classical
  let f : ℝ → ℝ := fun z => (∏ i ∈ B, g (x i - z)) * q0 z
  let C : ℝ := L * Real.exp (-R) * (∏ i ∈ B, g (x i - theta))
  have hprod0 : 0 ≤ ∏ i ∈ B, g (x i - theta) := Finset.prod_nonneg (fun i hi => hg0 _)
  have hC0 : 0 ≤ C := mul_nonneg (mul_nonneg hL (Real.exp_nonneg _)) hprod0
  have hf0 : ∀ z, 0 ≤ f z := fun z => mul_nonneg (Finset.prod_nonneg (fun i hi => hg0 _)) (hq0 z)
  have hfint : Integrable f volume := by
    obtain ⟨M, hM, hMg⟩ := hgupper
    have hm : AEStronglyMeasurable f volume := by
      apply Measurable.aestronglyMeasurable
      exact (Finset.measurable_prod B (fun i hi => hgmeas.comp (measurable_const.sub measurable_id))).mul hqmeas
    apply Integrable.mono' (hqint.const_mul (M ^ B.card)) hm
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 z)]
    exact mul_le_mul_of_nonneg_right
      (calc (∏ i ∈ B, g (x i - z)) ≤ ∏ i ∈ B, M :=
          Finset.prod_le_prod (fun i hi => hg0 _) (fun i hi => hMg _)
        _ = M ^ B.card := by simp) (hq0 z)
  have hpoint : ∀ z ∈ Set.Ioo (theta - delta) theta, C ≤ f z := by
    intro z hz
    let u := theta - z
    have hu0 : 0 < u := sub_pos.mpr hz.2
    have hud : u < delta := by dsimp [u]; linarith [hz.1]
    have hu1 : (B.card : ℝ) * u ≤ 1 := le_trans
      (mul_le_mul_of_nonneg_left hud.le (Nat.cast_nonneg _)) hsmall
    have hker : ∀ i ∈ B, g (x i - theta) * Real.exp (-R * u) ≤ g (x i - z) := by
      intro i hi
      have hy : x i - theta ∈ Set.Ioo (-c) c := ⟨(hx i hi).1, by linarith [(hx i hi).2]⟩
      have hyu : x i - theta + u ∈ Set.Ioo (-c) c := ⟨by linarith [(hx i hi).1], by linarith [(hx i hi).2]⟩
      have hh := kernel_shift_lower c R g hgpos hgdiff hgderiv (x i - theta) u hy hu0.le hyu
      convert hh using 1 <;> dsimp [u] <;> congr 1 <;> ring
    have hp := Finset.prod_le_prod
      (fun i hi => mul_nonneg (hg0 _) (Real.exp_nonneg _)) hker
    have hpow : (Real.exp (-R * u)) ^ B.card = Real.exp (-R * ((B.card : ℝ) * u)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    simp only [Finset.prod_mul_distrib, Finset.prod_const, hpow] at hp
    have hexp : Real.exp (-R) ≤ Real.exp (-R * ((B.card : ℝ) * u)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hR (sub_nonneg.mpr hu1)]
    have hp2 : Real.exp (-R) * (∏ i ∈ B, g (x i - theta)) ≤ ∏ i ∈ B, g (x i - z) := by
      calc Real.exp (-R) * (∏ i ∈ B, g (x i - theta))
          ≤ Real.exp (-R * ((B.card : ℝ) * u)) * (∏ i ∈ B, g (x i - theta)) :=
            mul_le_mul_of_nonneg_right hexp hprod0
        _ ≤ ∏ i ∈ B, g (x i - z) := by simpa only [mul_comm] using hp
    have hq : L ≤ q0 z := hT4 z (by rw [abs_of_neg (by linarith : z - theta < 0)]; linarith)
    dsimp only [C, f]
    calc L * Real.exp (-R) * (∏ i ∈ B, g (x i - theta))
        = (Real.exp (-R) * (∏ i ∈ B, g (x i - theta))) * L := by ring
      _ ≤ (∏ i ∈ B, g (x i - z)) * q0 z :=
        mul_le_mul hp2 hq hL (Finset.prod_nonneg (fun i hi => hg0 _))
  have hind : ∀ z, (Set.Ioo (theta - delta) theta).indicator (fun _ => C) z ≤ f z := by
    intro z
    by_cases hz : z ∈ Set.Ioo (theta - delta) theta
    · simpa only [Set.indicator_of_mem hz] using hpoint z hz
    · simpa only [Set.indicator_of_notMem hz] using hf0 z
  have hmono := integral_mono_of_nonneg
    (Eventually.of_forall (fun z => Set.indicator_nonneg (fun z hz => hC0) z)) hfint
    (Eventually.of_forall hind)
  have hconst : ∫ z, (Set.Ioo (theta - delta) theta).indicator (fun _ => C) z ∂volume = delta * C := by
    rw [integral_indicator measurableSet_Ioo, setIntegral_const, smul_eq_mul]
    simp only [Measure.real, Real.volume_Ioo, sub_sub_cancel, ENNReal.toReal_ofReal hdelta.le]
  rw [hconst] at hmono
  convert hmono using 1 <;> dsimp only [C, f, dpMargLik] <;> ring


lemma true_windows_disjoint {t : ℕ} (c : ℝ) (theta : Fin t → ℝ)
    (hsep : ∀ j k, j ≠ k → 2 * c < |theta j - theta k|)
    (n : ℕ) (omega : ℕ → ℝ) :
    ∀ j k, j ≠ k → Disjoint (dpBlock c theta n omega j) (dpBlock c theta n omega k) := by
  intro j k hjk
  rw [Finset.disjoint_left]
  intro i hij hik
  simp only [dpBlock, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Icc] at hij hik
  have hdist := hsep j k hjk
  have habs : |theta j - theta k| ≤ 2 * c := by
    rw [abs_le]
    constructor <;> linarith
  linarith

lemma true_partition_mem {t n : ℕ} (c : ℝ) (theta : Fin t → ℝ) (omega : ℕ → ℝ)
    (hsep : ∀ j k, j ≠ k → 2 * c < |theta j - theta k|)
    (hcover : ∀ i : Fin n, ∃ j, omega (i : ℕ) ∈ Set.Icc (theta j - c) (theta j + c))
    (hne : ∀ j, (dpBlock c theta n omega j).Nonempty) :
    Finset.univ.image (fun j => dpBlock c theta n omega j) ∈ dpTau n t := by
  classical
  have hdisj := true_windows_disjoint c theta hsep n omega
  have hinj : Function.Injective (fun j => dpBlock c theta n omega j) := by
    intro j k heq
    by_contra hjk
    obtain ⟨i, hi⟩ := hne j
    have heq' : dpBlock c theta n omega j = dpBlock c theta n omega k := heq
    have hik : i ∈ dpBlock c theta n omega k := by rw [← heq']; exact hi
    exact Finset.disjoint_left.mp (hdisj j k hjk) hi hik
  simp only [dpTau, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  · intro B hB
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hB
    exact hne j
  · intro B hB B' hB' hBB
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hB'
    exact hdisj j k (fun h => hBB (congrArg _ h))
  · intro i
    obtain ⟨j, hj⟩ := hcover i
    exact ⟨dpBlock c theta n omega j, Finset.mem_image_of_mem _ (Finset.mem_univ j), by simpa [dpBlock] using hj⟩

/-- Omega supplies the interval width needed by the one-sided whole-block bound.
The strict left endpoint condition is used only on a null complement under the data law. -/
lemma omega_marginal_lower {t n : ℕ} (j : Fin t) (c R L r ell : ℝ)
    (theta : Fin t → ℝ) (N : Fin t → ℕ) (omega : ℕ → ℝ) (g q0 : ℝ → ℝ)
    (hgmeas : Measurable g) (hg0 : ∀ z, 0 ≤ g z)
    (hgpos : ∀ z ∈ Set.Ioo (-c) c, 0 < g z)
    (hgdiff : DifferentiableOn ℝ g (Set.Ioo (-c) c))
    (hgderiv : ∀ z ∈ Set.Ioo (-c) c, |deriv g z / g z| ≤ R)
    (hgupper : ∃ M : ℝ, 0 ≤ M ∧ ∀ z, g z ≤ M)
    (hqmeas : Measurable q0) (hq0 : ∀ z, 0 ≤ q0 z) (hqint : Integrable q0 volume)
    (hR : 0 ≤ R) (hL : 0 ≤ L) (hr : 0 < r) (hell : 1 ≤ ell)
    (hT4 : ∀ z, |z - theta j| < r → L ≤ q0 z)
    (hN : 1 ≤ N j) (hOmega : dpOmega c theta N n omega)
    (hell_def : ell = (Real.log (n : ℝ)) ^ ((1 : ℝ) / (2 * (t : ℝ))))
    (hinterior : ∀ i ∈ dpBlock c theta n omega j, -c < omega (i : ℕ) - theta j) :
    (L * Real.exp (-R) * min 1 r / (2 * ell)) *
      ((∏ i ∈ dpBlock c theta n omega j, g (omega (i : ℕ) - theta j)) /
        ((dpBlock c theta n omega j).card : ℝ)) ≤
      dpMargLik g q0 (dpXseq n omega) (dpBlock c theta n omega j) := by
  classical
  let B := dpBlock c theta n omega j
  let a : ℝ := min 1 r
  let delta := a / (2 * (B.card : ℝ) * ell)
  have hcard : 1 ≤ B.card := hN.trans (hOmega j).1
  have hcardR : 1 ≤ (B.card : ℝ) := by exact_mod_cast hcard
  have hellpos : 0 < ell := lt_of_lt_of_le zero_lt_one hell
  have ha : 0 < a := lt_min zero_lt_one hr
  have hap : a ≤ 1 := min_le_left _ _
  have har : a ≤ r := min_le_right _ _
  have hdenpos : 0 < 2 * (B.card : ℝ) * ell := by positivity
  have hdelta : 0 < delta := div_pos ha hdenpos
  have hmul : 1 ≤ (B.card : ℝ) * ell := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hcardR) (sub_nonneg.mpr hell)]
  have hden_ge : 1 ≤ 2 * (B.card : ℝ) * ell := by nlinarith
  have hdelta_a : delta ≤ a := div_le_self ha.le hden_ge
  have hdr : delta ≤ r := hdelta_a.trans har
  have hsmall : (B.card : ℝ) * delta ≤ 1 := by
    dsimp only [delta]
    rw [mul_div_assoc', div_le_iff₀ hdenpos]
    nlinarith
  have hy : (1 / 2 : ℝ) ≤ (B.card : ℝ) * ell * (c + theta j - dpMaxStat c theta n omega j) := by
    have hh := (hOmega j).2.1.trans (min_le_right 1 _)
    simpa only [dpY, B, ← hell_def] using hh
  have hne : B.Nonempty := Finset.one_le_card.mp hcard
  have hmax : ∀ i ∈ B, omega (i : ℕ) ≤ dpMaxStat c theta n omega j := by
    intro i hi
    dsimp only [dpMaxStat]
    rw [dif_pos hne]
    exact Finset.le_max' (B.image (fun i : Fin n => omega (i : ℕ))) _
      (Finset.mem_image_of_mem (fun i : Fin n => omega (i : ℕ)) hi)
  have hgap : delta ≤ c + theta j - dpMaxStat c theta n omega j := by
    dsimp only [delta]
    rw [div_le_iff₀ hdenpos]
    nlinarith
  have hx : ∀ i ∈ B, -c < dpXseq n omega i - theta j ∧ dpXseq n omega i - theta j + delta ≤ c := by
    intro i hi
    exact ⟨hinterior i hi, by dsimp [dpXseq]; linarith [hmax i hi]⟩
  have hh := marginal_block_lower B (dpXseq n omega) c R L r delta (theta j) g q0
    hgmeas hg0 hgpos hgdiff hgderiv hgupper hqmeas hq0 hqint hR hL hdelta hdr hT4 hsmall hx
  convert hh using 1
  dsimp only [delta, a, dpXseq]
  field_simp
  <;> ring

end ManualDPCons
end
end DPCompletedProof
