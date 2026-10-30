import ProverJobs.paper_fresh_20261028t224543381z_eills.Vocabulary
import ProverJobs.paper_fresh_20261028t224543381z_eills.Base
import ProverJobs.paper_fresh_20261028t224543381z_eills.ProvedNodes.Node_358034260_300c6b38_04387300

namespace PaperProofTasks.paper_fresh_20261028t224543381z_eills

open _root_.PaperProofTasks.paper_fresh_20261028t224543381z_eills.Statlib.Imported
open _root_.PaperProofTasks.paper_fresh_20261028t224543381z_eills.Statlib.Imported.StrongConvexityMain
open MeasureTheory ProbabilityTheory
open StrongConvexityMain

namespace Statlib.Imported
open _root_.Statlib
open MeasureTheory ProbabilityTheory
open _root_.PaperProofTasks.paper_fresh_20261028t224543381z_eills.Statlib.Imported.StrongConvexityMain

set_option autoImplicit false in
theorem statopia_math_node_2170213884_2b763c53 : ∀ (p : ℕ) {ι : Type*} [Fintype ι] [Nonempty ι]
    (μ : ι → Measure (Eucl p × ℝ))
    (hμ_prob : ∀ e : ι, IsProbabilityMeasure (μ e))
    (βstar : Eucl p) (S_star : Finset (Fin p))
    (hS_star : ∀ j : Fin p, j ∈ S_star ↔ βstar j ≠ 0)
    (β : Eucl p)
    (betaLocal : ι → Finset (Fin p) → Eucl p)
    (hbeta_supp : ∀ (e : ι) (S : Finset (Fin p)), suppVec (betaLocal e S) ⊆ S)
    (hbeta_min : ∀ (e : ι) (S : Finset (Fin p)),
      IsMinOn (fun b : Eucl p => risk (μ e) b) {b : Eucl p | suppVec b ⊆ S} (betaLocal e S))
    (kappaL : ℝ) (hkappaL_pos : 0 < kappaL)
    (hLoewnerL : ∀ (e : ι) (v : Eucl p), kappaL * ‖v‖ ^ 2 ≤ quad (covMat (μ e)) v)
    (ω : ι → ℝ) (hω_unif : ∀ e : ι, ω e = (Fintype.card ι : ℝ)⁻¹)
    (h_cross_int : ∀ (e : ι) (b : Eucl p) (j : Fin p),
      Integrable (fun z : Eucl p × ℝ => (z.2 - dot b z.1) * z.1 j) (μ e))
    (h_partDeriv : ∀ (e : ι) (b : Eucl p) (j : Fin p),
      partDeriv (μ e) b j = -2 * ∫ z, (z.2 - dot b z.1) * z.1 j ∂(μ e)),
    regJ μ ω β ≥ kappaL ^ 2 * dBar betaLocal (suppVec β) := by
  /- @proof-region region.target-node.session.4fb10b84a89fc448 begin -/
  intro p ι instFintype instNonempty μ hμ_prob βstar S_star hS_star β betaLocal hbeta_supp hbeta_min kappaL hkappaL_pos hLoewnerL ω hω_unif hInt hPartDeriv
  classical
  have probeA : ∀ (x : Eucl p), ‖x‖ ^ 2 = ∑ i, (x i) ^ 2 := by
    intro x
    rw [EuclideanSpace.norm_sq_eq]
    simp
  have probeB : ∀ (x y : Eucl p) (i : Fin p), (x + y) i = x i + y i := fun x y i => rfl
  have probeC : ∀ (t : ℝ) (x : Eucl p) (i : Fin p), (t • x) i = t * x i := fun t x i => rfl
  have probeD : ∀ (x y : Eucl p) (i : Fin p), (x - y) i = x i - y i := fun x y i => rfl
  have probeF : ∀ (s : Finset (Fin p)) (f g : Fin p → ℝ),
      (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * (∑ i ∈ s, g i ^ 2) :=
    fun s f g => Finset.sum_mul_sq_le_sq_mul_sq s f g
  have probeG : ∀ (s t : Finset (Fin p)) (f : Fin p → ℝ), s ⊆ t →
      (∀ x ∈ t, x ∉ s → 0 ≤ f x) → ∑ x ∈ s, f x ≤ ∑ x ∈ t, f x :=
    fun s t f h1 h2 => Finset.sum_le_sum_of_subset_of_nonneg h1 h2
  have probeH : ∀ (s t : Finset (Fin p)) (f : Fin p → ℝ), s ⊆ t →
      (∀ x ∈ t, x ∉ s → f x = 0) → ∑ x ∈ s, f x = ∑ x ∈ t, f x :=
    fun s t f h1 h2 => Finset.sum_subset h1 h2
  have probeSumApply : ∀ (s : Finset ι) (f : ι → Eucl p) (i : Fin p),
      (∑ e ∈ s, f e) i = ∑ e ∈ s, f e i := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro f i; simp
    | insert a s ha ih =>
        intro f i
        rw [Finset.sum_insert ha, Finset.sum_insert ha, probeB, ih]
  have probeT : ∀ (s : Finset ι) (c : ℝ) (f : ι → ℝ), c * ∑ e ∈ s, f e = ∑ e ∈ s, c * f e :=
    fun s c f => Finset.mul_sum s f c
  have probeU : ∀ (s : Finset ι) (c : ℝ) (f : ι → ℝ), (∑ e ∈ s, f e) * c = ∑ e ∈ s, f e * c :=
    fun s c f => Finset.sum_mul s f c
  have probeX3 : ∀ (s : Finset ι) (f g : ι → ℝ),
      ∑ e ∈ s, (f e - g e) = ∑ e ∈ s, f e - ∑ e ∈ s, g e := fun s f g => Finset.sum_sub_distrib f g
  have probeX : ∀ (c : ℝ), (∑ _e : ι, c) = (Fintype.card ι : ℝ) * c := fun c => by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have probeAB : ∀ (a : ℝ), a ≠ 0 → a * a⁻¹ = 1 := fun a h => mul_inv_cancel₀ h

  have probeAD : ((Fintype.card ι : ℝ)) ≠ 0 := by
    have h : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
    exact_mod_cast h
  have hmem : ∀ (x : Eucl p) (j : Fin p), j ∈ suppVec x ↔ x j ≠ 0 := by
    intro x j
    simp [suppVec]
  have hdot_single : ∀ (i : Fin p) (x : Eucl p), dot (EuclideanSpace.single i (1 : ℝ)) x = x i := by
    intro i x
    rw [dot, Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [EuclideanSpace.single_apply, hb]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hdot_sub : ∀ (v w x : Eucl p), dot (v - w) x = dot v x - dot w x := by
    intro v w x
    simp only [dot, probeD, sub_mul, Finset.sum_sub_distrib]
  have hdot_smul_single : ∀ (c : ℝ) (i : Fin p) (x : Eucl p),
      dot (c • EuclideanSpace.single i (1 : ℝ)) x = c * x i := by
    intro c i x
    rw [dot]
    calc ∑ j, (c • EuclideanSpace.single i (1 : ℝ) : Eucl p) j * x j
        = ∑ j, c * ((EuclideanSpace.single i (1 : ℝ) : Eucl p) j * x j) := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [probeC, mul_assoc]
      _ = c * ∑ j, (EuclideanSpace.single i (1 : ℝ) : Eucl p) j * x j := by rw [Finset.mul_sum]
      _ = c * x i := by
          congr 1
          exact hdot_single i x
  have hxx : ∀ (e : ι) (i j : Fin p), Integrable (fun z : Eucl p × ℝ => z.1 i * z.1 j) (μ e) := by
    intro e i j
    have h1 : Integrable (fun z : Eucl p × ℝ => (z.2 - z.1 i) * z.1 j) (μ e) := by
      simpa only [hdot_single i] using hInt e (EuclideanSpace.single i (1 : ℝ)) j
    have h2 : Integrable (fun z : Eucl p × ℝ => (z.2 - 2 * z.1 i) * z.1 j) (μ e) := by
      simpa only [hdot_smul_single (2 : ℝ) i] using
        hInt e ((2 : ℝ) • EuclideanSpace.single i (1 : ℝ)) j
    have hd : Integrable (fun z : Eucl p × ℝ =>
        (z.2 - z.1 i) * z.1 j - (z.2 - 2 * z.1 i) * z.1 j) (μ e) := h1.sub h2
    have hkey : (fun z : Eucl p × ℝ => (z.2 - z.1 i) * z.1 j - (z.2 - 2 * z.1 i) * z.1 j)
        = (fun z : Eucl p × ℝ => z.1 i * z.1 j) := by
      funext z
      ring
    rw [hkey] at hd
    exact hd
  have hStepA : ∀ (e : ι) (j : Fin p), j ∈ suppVec β →
      partDeriv (μ e) (betaLocal e (suppVec β)) j = 0 := by
    intro e j hj
    have hsupp : ∀ t : ℝ,
        betaLocal e (suppVec β) + t • EuclideanSpace.single j (1 : ℝ) ∈
          {b : Eucl p | suppVec b ⊆ suppVec β} := by
      intro t i hi
      have hne : (betaLocal e (suppVec β) + t • EuclideanSpace.single j (1 : ℝ) : Eucl p) i ≠ 0 :=
        (hmem _ i).1 hi
      by_contra hcon
      have ha : (betaLocal e (suppVec β)) i = 0 := by
        by_contra h
        exact hcon (hbeta_supp e (suppVec β) ((hmem _ i).2 h))
      have hb : (t • EuclideanSpace.single j (1 : ℝ) : Eucl p) i = 0 := by
        have hij : i ≠ j := fun h => hcon (h ▸ hj)
        simp [probeC, EuclideanSpace.single_apply, hij]
      have hsum : (betaLocal e (suppVec β) + t • EuclideanSpace.single j (1 : ℝ) : Eucl p) i = 0 := by
        rw [probeB, ha, hb, add_zero]
      exact hne hsum
    have hline := (hbeta_min e (suppVec β)).lineDeriv_eq_zero (Filter.Eventually.of_forall hsupp)
    simpa [partDeriv, lineDeriv] using hline
  have hStepB : ∀ (e : ι) (j : Fin p), j ∈ suppVec β →
      ∫ z, (z.2 - dot β z.1) * z.1 j ∂(μ e)
        = ∑ i, (betaLocal e (suppVec β) - β) i * covMat (μ e) i j := by
    intro e j hj
    have hzero : ∫ z, (z.2 - dot (betaLocal e (suppVec β)) z.1) * z.1 j ∂(μ e) = 0 := by
      have hp := hPartDeriv e (betaLocal e (suppVec β)) j
      have hz := hStepA e j hj
      linarith
    have hsplit : (fun z : Eucl p × ℝ => (z.2 - dot β z.1) * z.1 j)
        = (fun z : Eucl p × ℝ => (z.2 - dot (betaLocal e (suppVec β)) z.1) * z.1 j
            + ∑ i, (betaLocal e (suppVec β) - β) i * (z.1 i * z.1 j)) := by
      funext z
      have hd2 : dot (betaLocal e (suppVec β) - β) z.1
          = ∑ i, (betaLocal e (suppVec β) - β) i * z.1 i := rfl
      have hd1 : dot β z.1
          = dot (betaLocal e (suppVec β)) z.1 - dot (betaLocal e (suppVec β) - β) z.1 := by
        rw [hdot_sub]
        ring
      have hd3 : (∑ i, (betaLocal e (suppVec β) - β) i * z.1 i) * z.1 j
          = ∑ i, (betaLocal e (suppVec β) - β) i * (z.1 i * z.1 j) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
      have hL : (z.2 - dot β z.1)
          = (z.2 - dot (betaLocal e (suppVec β)) z.1)
            + ∑ i, (betaLocal e (suppVec β) - β) i * z.1 i := by
        rw [hd1, hd2]
        ring
      rw [hL, add_mul, hd3]
    rw [hsplit]
    have hBint : Integrable (fun z : Eucl p × ℝ =>
        ∑ i, (betaLocal e (suppVec β) - β) i * (z.1 i * z.1 j)) (μ e) :=
      integrable_finset_sum Finset.univ (fun i _ => (hxx e i j).const_mul _)
    have hsum_int : (∫ z, (∑ i, (betaLocal e (suppVec β) - β) i * (z.1 i * z.1 j)) ∂(μ e))
        = ∑ i, ∫ z, (betaLocal e (suppVec β) - β) i * (z.1 i * z.1 j) ∂(μ e) :=
      integral_finset_sum Finset.univ (fun i _ => (hxx e i j).const_mul _)
    rw [integral_add (hInt e (betaLocal e (suppVec β)) j) hBint, hzero, zero_add, hsum_int]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_const_mul]
    rfl
  have hStepC : ∀ (e : ι), kappaL ^ 2 * ‖betaLocal e (suppVec β) - β‖ ^ 2
      ≤ ∑ j ∈ suppVec β, (∫ z, (z.2 - dot β z.1) * z.1 j ∂(μ e)) ^ 2 := by
    intro e
    have hbeta_off : ∀ j : Fin p, j ∉ suppVec β → β j = 0 := by
      intro j hj
      by_contra h
      exact hj ((hmem β j).2 h)
    have hl_off : ∀ j : Fin p, j ∉ suppVec β → (betaLocal e (suppVec β)) j = 0 := by
      intro j hj
      by_contra h
      exact hj (hbeta_supp e (suppVec β) ((hmem _ j).2 h))
    have hv_off : ∀ j : Fin p, j ∉ suppVec β → (betaLocal e (suppVec β) - β) j = 0 := by
      intro j hj
      rw [probeD, hl_off j hj, hbeta_off j hj, sub_zero]
    have hquad : quad (covMat (μ e)) (betaLocal e (suppVec β) - β)
        = ∑ j ∈ suppVec β, (betaLocal e (suppVec β) - β) j
            * ∫ z, (z.2 - dot β z.1) * z.1 j ∂(μ e) := by
      have hswap : (∑ i, ∑ j, covMat (μ e) i j * (betaLocal e (suppVec β) - β) i
            * (betaLocal e (suppVec β) - β) j)
          = ∑ j, ∑ i, covMat (μ e) i j * (betaLocal e (suppVec β) - β) i
            * (betaLocal e (suppVec β) - β) j :=
        Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      simp only [quad]
      rw [hswap]
      have hstep : (∑ j, ∑ i, covMat (μ e) i j * (betaLocal e (suppVec β) - β) i
            * (betaLocal e (suppVec β) - β) j)
          = ∑ j, (betaLocal e (suppVec β) - β) j
              * ∫ z, (z.2 - dot β z.1) * z.1 j ∂(μ e) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        by_cases hj : j ∈ suppVec β
        · rw [hStepB e j hj, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          ring
        · rw [hv_off j hj]
          simp
      rw [hstep]
      exact (probeH (suppVec β) Finset.univ (fun j => (betaLocal e (suppVec β) - β) j
        * ∫ z, (z.2 - dot β z.1) * z.1 j ∂(μ e)) (Finset.subset_univ _)
        (fun j _ hj => by simp [hv_off j hj])).symm
    have hlow : kappaL * ‖betaLocal e (suppVec β) - β‖ ^ 2
        ≤ ∑ j ∈ suppVec β, (betaLocal e (suppVec β) - β) j
            * ∫ z, (z.2 - dot β z.1) * z.1 j ∂(μ e) := by
      rw [← hquad]
      exact hLoewnerL e _
    have hcs := probeF (suppVec β)
      (fun j => (betaLocal e (suppVec β) - β) j)
      (fun j => ∫ z, (z.2 - dot β z.1) * z.1 j ∂(μ e))
    have hA : ∑ j ∈ suppVec β, ((betaLocal e (suppVec β) - β) j) ^ 2
        ≤ ‖betaLocal e (suppVec β) - β‖ ^ 2 := by
      rw [probeA]
      exact probeG (suppVec β) Finset.univ _ (Finset.subset_univ _) (fun x _ _ => sq_nonneg _)
    have hBnn : 0 ≤ ∑ j ∈ suppVec β, (∫ z, (z.2 - dot β z.1) * z.1 j ∂(μ e)) ^ 2 :=
      Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have hnn : 0 ≤ ‖betaLocal e (suppVec β) - β‖ ^ 2 := sq_nonneg _
    by_cases hn : ‖betaLocal e (suppVec β) - β‖ ^ 2 = 0
    · rw [hn, mul_zero]
      exact hBnn
    · have hnpos : 0 < ‖betaLocal e (suppVec β) - β‖ ^ 2 := lt_of_le_of_ne hnn (Ne.symm hn)
      have hkn : 0 ≤ kappaL * ‖betaLocal e (suppVec β) - β‖ ^ 2 :=
        mul_nonneg (le_of_lt hkappaL_pos) hnn
      have hQnn : 0 ≤ ∑ j ∈ suppVec β, (betaLocal e (suppVec β) - β) j
          * ∫ z, (z.2 - dot β z.1) * z.1 j ∂(μ e) := le_trans hkn hlow
      have hsq1 : (kappaL * ‖betaLocal e (suppVec β) - β‖ ^ 2) ^ 2
          ≤ (∑ j ∈ suppVec β, (betaLocal e (suppVec β) - β) j
              * ∫ z, (z.2 - dot β z.1) * z.1 j ∂(μ e)) ^ 2 := by
        have h := mul_le_mul hlow hlow hkn hQnn
        calc (kappaL * ‖betaLocal e (suppVec β) - β‖ ^ 2) ^ 2
            = (kappaL * ‖betaLocal e (suppVec β) - β‖ ^ 2)
                * (kappaL * ‖betaLocal e (suppVec β) - β‖ ^ 2) := by ring
          _ ≤ (∑ j ∈ suppVec β, (betaLocal e (suppVec β) - β) j
                * ∫ z, (z.2 - dot β z.1) * z.1 j ∂(μ e))
              * (∑ j ∈ suppVec β, (betaLocal e (suppVec β) - β) j
                * ∫ z, (z.2 - dot β z.1) * z.1 j ∂(μ e)) := h
          _ = (∑ j ∈ suppVec β, (betaLocal e (suppVec β) - β) j
                * ∫ z, (z.2 - dot β z.1) * z.1 j ∂(μ e)) ^ 2 := by ring
      have hsq2 : (kappaL * ‖betaLocal e (suppVec β) - β‖ ^ 2) ^ 2
          ≤ (∑ j ∈ suppVec β, ((betaLocal e (suppVec β) - β) j) ^ 2)
              * (∑ j ∈ suppVec β, (∫ z, (z.2 - dot β z.1) * z.1 j ∂(μ e)) ^ 2) :=
        le_trans hsq1 hcs
      have hab : (∑ j ∈ suppVec β, ((betaLocal e (suppVec β) - β) j) ^ 2)
              * (∑ j ∈ suppVec β, (∫ z, (z.2 - dot β z.1) * z.1 j ∂(μ e)) ^ 2)
          ≤ ‖betaLocal e (suppVec β) - β‖ ^ 2
              * (∑ j ∈ suppVec β, (∫ z, (z.2 - dot β z.1) * z.1 j ∂(μ e)) ^ 2) :=
        mul_le_mul_of_nonneg_right hA hBnn
      have h1 : (kappaL * ‖betaLocal e (suppVec β) - β‖ ^ 2) ^ 2
          = ‖betaLocal e (suppVec β) - β‖ ^ 2
              * (kappaL ^ 2 * ‖betaLocal e (suppVec β) - β‖ ^ 2) := by ring
      have hkey : ‖betaLocal e (suppVec β) - β‖ ^ 2
              * (kappaL ^ 2 * ‖betaLocal e (suppVec β) - β‖ ^ 2)
          ≤ ‖betaLocal e (suppVec β) - β‖ ^ 2
              * (∑ j ∈ suppVec β, (∫ z, (z.2 - dot β z.1) * z.1 j ∂(μ e)) ^ 2) := by
        rw [← h1]
        exact le_trans hsq2 hab
      exact le_of_mul_le_mul_left hkey hnpos
  have hcard_pos : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    have h : 0 < Fintype.card ι := Fintype.card_pos
    exact_mod_cast h
  have hωnn : ∀ e : ι, (0 : ℝ) ≤ ω e := by
    intro e
    rw [hω_unif e]
    exact le_of_lt (inv_pos.mpr hcard_pos)
  have hregJ1 : regJ μ ω β
      = ∑ j ∈ suppVec β, ∑ e, (ω e / 4) * (partDeriv (μ e) β j) ^ 2 := by
    simp only [regJ]
    exact (Finset.sum_filter (fun j : Fin p => β j ≠ 0)
      (fun j => ∑ e, (ω e / 4) * (partDeriv (μ e) β j) ^ 2)).symm
  have hregJ2 : ∑ j ∈ suppVec β, ∑ e, (ω e / 4) * (partDeriv (μ e) β j) ^ 2
      = ∑ j ∈ suppVec β, ∑ e, ω e * (∫ z, (z.2 - dot β z.1) * z.1 j ∂(μ e)) ^ 2 := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [hPartDeriv e β j]
    ring
  have hregJ3 : ∑ j ∈ suppVec β, ∑ e, ω e * (∫ z, (z.2 - dot β z.1) * z.1 j ∂(μ e)) ^ 2
      = ∑ e, ω e * ∑ j ∈ suppVec β, (∫ z, (z.2 - dot β z.1) * z.1 j ∂(μ e)) ^ 2 := by
    have hsw : (∑ j ∈ suppVec β, ∑ e, ω e * (∫ z, (z.2 - dot β z.1) * z.1 j ∂(μ e)) ^ 2)
        = ∑ e, ∑ j ∈ suppVec β, ω e * (∫ z, (z.2 - dot β z.1) * z.1 j ∂(μ e)) ^ 2 :=
      Finset.sum_comm (s := suppVec β) (t := Finset.univ)
    rw [hsw]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [Finset.mul_sum]
  have hregJ4 : ∑ e, ω e * (kappaL ^ 2 * ‖betaLocal e (suppVec β) - β‖ ^ 2)
      ≤ ∑ e, ω e * ∑ j ∈ suppVec β, (∫ z, (z.2 - dot β z.1) * z.1 j ∂(μ e)) ^ 2 := by
    refine Finset.sum_le_sum (fun e _ => ?_)
    exact mul_le_mul_of_nonneg_left (hStepC e) (hωnn e)
  have hregJ5 : ∑ e, ω e * (kappaL ^ 2 * ‖betaLocal e (suppVec β) - β‖ ^ 2)
      = kappaL ^ 2 * ∑ e, ω e * ‖betaLocal e (suppVec β) - β‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    ring
  have hωsum : (∑ e, ω e * ‖betaLocal e (suppVec β) - β‖ ^ 2)
      = ∑ e, (Fintype.card ι : ℝ)⁻¹ * ‖betaLocal e (suppVec β) - β‖ ^ 2 := by
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [hω_unif e]
  have hStepE : dBar betaLocal (suppVec β)
      ≤ ∑ e, (Fintype.card ι : ℝ)⁻¹ * ‖betaLocal e (suppVec β) - β‖ ^ 2 := by
    have hcoord : ∀ e : ι, ‖betaLocal e (suppVec β) - β‖ ^ 2
        = ‖betaLocal e (suppVec β) - betaBar betaLocal (suppVec β)‖ ^ 2
          + 2 * (∑ j, ((betaLocal e (suppVec β) - betaBar betaLocal (suppVec β)) j
              * (betaBar betaLocal (suppVec β) - β) j))
          + ‖betaBar betaLocal (suppVec β) - β‖ ^ 2 := by
      intro e
      rw [probeA, probeA, probeA]
      rw [show (∑ j, ((betaLocal e (suppVec β) - β) j) ^ 2)
          = ∑ j, (((betaLocal e (suppVec β) - betaBar betaLocal (suppVec β)) j) ^ 2
              + 2 * ((betaLocal e (suppVec β) - betaBar betaLocal (suppVec β)) j
                * (betaBar betaLocal (suppVec β) - β) j)
              + ((betaBar betaLocal (suppVec β) - β) j) ^ 2) from by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [probeD, probeD, probeD]
        ring]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    have hcoef : ∀ j : Fin p, (∑ e, ((betaLocal e (suppVec β)) j
        - (betaBar betaLocal (suppVec β)) j)) = 0 := by
      intro j
      have hbar : (betaBar betaLocal (suppVec β)) j
          = (Fintype.card ι : ℝ)⁻¹ * ∑ e, (betaLocal e (suppVec β)) j := by
        rw [betaBar, probeC, probeSumApply]
      rw [probeX3, probeX]
      rw [hbar]
      have hinv : (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ)⁻¹
            * ∑ e, (betaLocal e (suppVec β)) j) = ∑ e, (betaLocal e (suppVec β)) j := by
        rw [← mul_assoc, probeAB _ probeAD, one_mul]
      rw [hinv, sub_self]
    have hcross : (∑ e, (Fintype.card ι : ℝ)⁻¹
        * (∑ j, ((betaLocal e (suppVec β) - betaBar betaLocal (suppVec β)) j
            * (betaBar betaLocal (suppVec β) - β) j))) = 0 := by
      rw [← probeT]
      have hsw2 : (∑ e, (∑ j, ((betaLocal e (suppVec β) - betaBar betaLocal (suppVec β)) j
              * (betaBar betaLocal (suppVec β) - β) j)))
          = ∑ j, ∑ e, ((betaLocal e (suppVec β) - betaBar betaLocal (suppVec β)) j
              * (betaBar betaLocal (suppVec β) - β) j) :=
        Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      rw [hsw2]
      have hfact : ∀ j : Fin p,
          (∑ e, ((betaLocal e (suppVec β) - betaBar betaLocal (suppVec β)) j
              * (betaBar betaLocal (suppVec β) - β) j))
          = (betaBar betaLocal (suppVec β) - β) j
            * (∑ e, ((betaLocal e (suppVec β)) j - (betaBar betaLocal (suppVec β)) j)) := by
        intro j
        rw [show (∑ e, ((betaLocal e (suppVec β) - betaBar betaLocal (suppVec β)) j
              * (betaBar betaLocal (suppVec β) - β) j))
            = ∑ e, (((betaLocal e (suppVec β)) j - (betaBar betaLocal (suppVec β)) j)
              * (betaBar betaLocal (suppVec β) - β) j) from by
          refine Finset.sum_congr rfl (fun e _ => ?_)
          rw [probeD]]
        rw [← probeU]
        ring
      rw [Finset.sum_congr rfl (fun j _ => hfact j)]
      simp [hcoef]
    have hsumc : (∑ e : ι, (Fintype.card ι : ℝ)⁻¹) = 1 := by
      rw [probeX, probeAB _ probeAD]
    have hA2 : (∑ e, (Fintype.card ι : ℝ)⁻¹
          * ‖betaLocal e (suppVec β) - betaBar betaLocal (suppVec β)‖ ^ 2)
        = dBar betaLocal (suppVec β) := rfl
    have hB2 : (∑ e, 2 * ((Fintype.card ι : ℝ)⁻¹ * ∑ j,
          ((betaLocal e (suppVec β) - betaBar betaLocal (suppVec β)) j
            * (betaBar betaLocal (suppVec β) - β) j))) = 0 := by
      rw [← probeT, hcross, mul_zero]
    have hC2 : (∑ e : ι, (Fintype.card ι : ℝ)⁻¹ * ‖betaBar betaLocal (suppVec β) - β‖ ^ 2)
        = ‖betaBar betaLocal (suppVec β) - β‖ ^ 2 := by
      rw [← probeU, hsumc, one_mul]

    have hmain : (∑ e, (Fintype.card ι : ℝ)⁻¹ * ‖betaLocal e (suppVec β) - β‖ ^ 2)
        = dBar betaLocal (suppVec β) + ‖betaBar betaLocal (suppVec β) - β‖ ^ 2 := by
      calc (∑ e, (Fintype.card ι : ℝ)⁻¹ * ‖betaLocal e (suppVec β) - β‖ ^ 2)
          = ∑ e, ((Fintype.card ι : ℝ)⁻¹
              * ‖betaLocal e (suppVec β) - betaBar betaLocal (suppVec β)‖ ^ 2
              + 2 * ((Fintype.card ι : ℝ)⁻¹ * ∑ j,
                ((betaLocal e (suppVec β) - betaBar betaLocal (suppVec β)) j
                  * (betaBar betaLocal (suppVec β) - β) j))
              + (Fintype.card ι : ℝ)⁻¹ * ‖betaBar betaLocal (suppVec β) - β‖ ^ 2) := by
            refine Finset.sum_congr rfl (fun e _ => ?_)
            rw [hcoord e]
            ring
        _ = (∑ e, ((Fintype.card ι : ℝ)⁻¹
              * ‖betaLocal e (suppVec β) - betaBar betaLocal (suppVec β)‖ ^ 2
              + 2 * ((Fintype.card ι : ℝ)⁻¹ * ∑ j,
                ((betaLocal e (suppVec β) - betaBar betaLocal (suppVec β)) j
                  * (betaBar betaLocal (suppVec β) - β) j))))
            + (∑ e, (Fintype.card ι : ℝ)⁻¹ * ‖betaBar betaLocal (suppVec β) - β‖ ^ 2) := by
            rw [Finset.sum_add_distrib]
        _ = ((∑ e, (Fintype.card ι : ℝ)⁻¹
              * ‖betaLocal e (suppVec β) - betaBar betaLocal (suppVec β)‖ ^ 2)
            + (∑ e, 2 * ((Fintype.card ι : ℝ)⁻¹ * ∑ j,
                ((betaLocal e (suppVec β) - betaBar betaLocal (suppVec β)) j
                  * (betaBar betaLocal (suppVec β) - β) j))))
            + (∑ e, (Fintype.card ι : ℝ)⁻¹ * ‖betaBar betaLocal (suppVec β) - β‖ ^ 2) := by
            rw [Finset.sum_add_distrib]
        _ = (dBar betaLocal (suppVec β) + 0) + ‖betaBar betaLocal (suppVec β) - β‖ ^ 2 := by
            rw [hA2, hB2, hC2]
        _ = dBar betaLocal (suppVec β) + ‖betaBar betaLocal (suppVec β) - β‖ ^ 2 := by ring
    rw [hmain]
    linarith [sq_nonneg (‖betaBar betaLocal (suppVec β) - β‖)]
  rw [hregJ1, hregJ2, hregJ3]
  have hmiddle : kappaL ^ 2 * dBar betaLocal (suppVec β)
      ≤ ∑ e, ω e * (kappaL ^ 2 * ‖betaLocal e (suppVec β) - β‖ ^ 2) := by
    have hleft : kappaL ^ 2 * dBar betaLocal (suppVec β)
        ≤ kappaL ^ 2 * (∑ e, ω e * ‖betaLocal e (suppVec β) - β‖ ^ 2) := by
      rw [hωsum]
      exact mul_le_mul_of_nonneg_left hStepE (sq_nonneg kappaL)
    exact le_trans hleft (le_of_eq hregJ5.symm)
  exact le_trans hmiddle hregJ4
  /- @proof-region region.target-node.session.4fb10b84a89fc448 end -/

end Statlib.Imported

