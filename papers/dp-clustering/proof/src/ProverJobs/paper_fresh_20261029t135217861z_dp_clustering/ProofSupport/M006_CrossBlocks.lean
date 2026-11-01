import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M000_Vocabulary
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M001_Base
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M003_WindowMass
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M005_PairBound

/- Original module ProverJobs.manual_dp_cons_finish_20261031.CrossBlocks; genuine source relocated, namespace-isolated only. -/
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
theorem statopia_math_node_3703788458_48052a86 : ∀ (t : ℕ) (ht : 1 ≤ t) (c : ℝ) (hc : 0 < c)
    (g q0 : ℝ → ℝ) (thetaStar : Fin t → ℝ)
    (m U : ℝ) (hm : 0 < m) (hU : 0 < U)
    (hg_meas : Measurable g)
    (hg_nonneg : ∀ x : ℝ, 0 ≤ g x)
    (hg_zero : ∀ x : ℝ, x ∉ Set.Icc (-c) c → g x = 0)
    (hg_lower : ∀ x ∈ Set.Icc (-c) c, m ≤ g x)
    (hg_int : ∫ x : ℝ, g x ∂volume = 1)
    (hq0_meas : Measurable q0)
    (hq0_nonneg : ∀ θ : ℝ, 0 ≤ q0 θ)
    (hq0_int : ∫ θ : ℝ, q0 θ ∂volume = 1)
    (hT3 : ∀ j : Fin t, ∀ y : ℝ, y ∈ Set.Icc (0 : ℝ) (2 * c) →
      q0 (thetaStar j + y) + q0 (thetaStar j - y) ≤ U)
    (hsep : ∀ j k : Fin t, j ≠ k → 2 * c < |thetaStar j - thetaStar k|)
    (hA : 2 * c * m ≤ 1)
    (n : ℕ) (hn : 1 ≤ n) (lab : Fin n → Fin t),
    let G : Fin t → ℝ → ℝ := fun l θ =>
      ∫ x in Set.Icc (thetaStar l - c) (thetaStar l + c), g (x - θ) ∂volume
    let w : Finset (Fin n) → ℝ := fun B =>
      ((B.card - 1).factorial : ℝ) *
        ∫ θ, (∏ l : Fin t, (G l θ) ^ (B.filter (fun i => lab i = l)).card) * q0 θ ∂volume
    ∀ (B : Finset (Fin n)) (l k : Fin t), l ≠ k →
      (B.filter (fun i => lab i = l)).Nonempty →
      (B.filter (fun i => lab i = k)).Nonempty →
      (∀ i ∈ B, lab i = l ∨ lab i = k) →
      (let p : ℕ := (B.filter (fun i => lab i = l)).card
       let q : ℕ := (B.filter (fun i => lab i = k)).card
       w B ≤ (dpKappa c m thetaStar) ^ (p + q) * ((p + q - 1).factorial : ℝ) *
           (((p : ℝ) / ((p + q : ℕ) : ℝ)) ^ p) *
           (((q : ℝ) / ((p + q : ℕ) : ℝ)) ^ q) ∧
       w B / ((p.factorial : ℝ) * (q.factorial : ℝ)) ≤
           (dpKappa c m thetaStar) ^ (p + q) / ((p + q : ℕ) : ℝ)) := by
  /- @proof-region region.target-node.session.bc3c14c8fbabafab begin -/
  intro t ht c hc g q0 thetaStar m U hm hU hg_meas hg_nonneg hg_zero hg_lower hg_int
    hq0_meas hq0_nonneg hq0_int hT3 hsep hA n hn lab
  intro G w
  intro B l k hlk hBl hBk hB
  intro p q
  have hpv : p = (B.filter (fun i => lab i = l)).card := rfl
  have hqv : q = (B.filter (fun i => lab i = k)).card := rfl
  have hp1 : 1 ≤ p := by rw [hpv]; exact Finset.one_le_card.mpr hBl
  have hq1 : 1 ≤ q := by rw [hqv]; exact Finset.one_le_card.mpr hBk
  have hdisj : Disjoint (B.filter (fun i => lab i = l)) (B.filter (fun i => lab i = k)) := by
    rw [Finset.disjoint_left]
    intro i hi hk
    simp only [Finset.mem_filter] at hi hk
    exact hlk (hi.2.symm.trans hk.2)
  have hunion : B.filter (fun i => lab i = l) ∪ B.filter (fun i => lab i = k) = B := by
    ext i
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hi, _⟩ | ⟨hi, _⟩) <;> exact hi
    · intro hi
      rcases hB i hi with h | h
      · exact Or.inl ⟨hi, h⟩
      · exact Or.inr ⟨hi, h⟩
  have hcard : B.card = p + q := by
    have h := Finset.card_union_of_disjoint hdisj
    rw [hunion] at h
    rw [hpv, hqv]
    exact h
  have hprod : ∀ θ : ℝ,
      (∏ l' : Fin t, (G l' θ) ^ (B.filter (fun i => lab i = l')).card) =
        (G l θ) ^ p * (G k θ) ^ q := by
    intro θ
    have h1 : (∏ l' : Fin t, (G l' θ) ^ (B.filter (fun i => lab i = l')).card)
        = ({l, k} : Finset (Fin t)).prod
            (fun l' => (G l' θ) ^ (B.filter (fun i => lab i = l')).card) := by
      refine (Finset.prod_subset ?_ ?_).symm
      · intro x _; exact Finset.mem_univ x
      · intro x _ hx
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
        have hnem : ¬ (B.filter (fun i => lab i = x)).Nonempty := by
          rintro ⟨i, hi⟩
          simp only [Finset.mem_filter] at hi
          rcases hB i hi.1 with h | h
          · exact hx.1 (hi.2.symm.trans h)
          · exact hx.2 (hi.2.symm.trans h)
        have hc0 : (B.filter (fun i => lab i = x)).card = 0 := by
          have hlt : ¬ (1 ≤ (B.filter (fun i => lab i = x)).card) :=
            fun h1' => hnem (Finset.one_le_card.mp h1')
          omega
        show (G x θ) ^ (B.filter (fun i => lab i = x)).card = 1
        rw [hc0, pow_zero]
    rw [h1, Finset.prod_insert (by simp [hlk]), Finset.prod_singleton]
  have hg_intble : Integrable g volume := by
    by_contra h
    rw [MeasureTheory.integral_undef h] at hg_int
    exact one_ne_zero hg_int.symm
  have hwin := statopia_math_node_1091114221_9ffd4ba6 t ht c hc g thetaStar m hm
    hg_meas hg_nonneg hg_zero hg_lower hg_int
  have hGl0 : ∀ θ : ℝ, 0 ≤ G l θ := fun θ => (hwin l θ).1
  have hGk0 : ∀ θ : ℝ, 0 ≤ G k θ := fun θ => (hwin k θ).1
  have hGlv : ∀ θ : ℝ, 2 * c ≤ |θ - thetaStar l| → G l θ = 0 := fun θ => (hwin l θ).2.2
  have hGkv : ∀ θ : ℝ, 2 * c ≤ |θ - thetaStar k| → G k θ = 0 := fun θ => (hwin k θ).2.2
  have hclose : ∀ a b : Fin t, (a, b) ∈ dpClosePair c thetaStar ↔
      a ≠ b ∧ |thetaStar a - thetaStar b| < 4 * c := by
    intro a b
    unfold dpClosePair
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hdpKsup : ∀ (hne : (dpClosePair c thetaStar).Nonempty),
      dpKappa c m thetaStar = (dpClosePair c thetaStar).sup' hne
        (fun q => 1 - m * (|thetaStar q.1 - thetaStar q.2| - 2 * c)) := by
    intro hne
    unfold dpKappa
    rw [dif_pos hne]
  have hκnn : 0 ≤ dpKappa c m thetaStar := by
    by_cases hne : (dpClosePair c thetaStar).Nonempty
    · obtain ⟨pr, hpr⟩ := hne
      rw [hdpKsup ⟨pr, hpr⟩]
      have hpr' := (hclose pr.1 pr.2).mp hpr
      have hpos : 0 ≤ 1 - m * (|thetaStar pr.1 - thetaStar pr.2| - 2 * c) := by
        have hsep' : 2 * c < |thetaStar pr.1 - thetaStar pr.2| := hsep _ _ hpr'.1
        have h1 : m * (|thetaStar pr.1 - thetaStar pr.2| - 2 * c) < m * (2 * c) := by
          apply mul_lt_mul_of_pos_left _ hm
          linarith
        have h2 : m * (2 * c) ≤ 1 := by
          have h3 : m * (2 * c) = 2 * c * m := by ring
          rw [h3]; exact hA
        linarith
      exact le_trans hpos
        (Finset.le_sup' (fun q => 1 - m * (|thetaStar q.1 - thetaStar q.2| - 2 * c)) hpr)
    · rw [show dpKappa c m thetaStar = 0 from by
        unfold dpKappa
        rw [dif_neg hne]]
  have hκsup : (l, k) ∈ dpClosePair c thetaStar →
      1 - m * (|thetaStar l - thetaStar k| - 2 * c) ≤ dpKappa c m thetaStar := by
    intro hmem
    have hne : (dpClosePair c thetaStar).Nonempty := ⟨(l, k), hmem⟩
    rw [hdpKsup hne]
    exact Finset.le_sup' (fun q => 1 - m * (|thetaStar q.1 - thetaStar q.2| - 2 * c)) hmem
  have hpoint : ∀ θ : ℝ, (G l θ) ^ p * (G k θ) ^ q ≤
      (dpKappa c m thetaStar) ^ (p + q) * (((p : ℝ) / ((p + q : ℕ) : ℝ)) ^ p) *
        (((q : ℝ) / ((p + q : ℕ) : ℝ)) ^ q) :=
    statopia_math_node_247103928_dcf533aa t ht c hc g thetaStar m hm hg_meas hg_nonneg
      hg_zero hg_lower hg_int hg_intble hsep hA l k hlk p q hp1 hq1
  have hq0_intble : Integrable q0 volume := by
    by_contra h
    rw [MeasureTheory.integral_undef h] at hq0_int
    exact one_ne_zero hq0_int.symm
  have hint : ∫ θ, (G l θ) ^ p * (G k θ) ^ q * q0 θ ≤
      (dpKappa c m thetaStar) ^ (p + q) * (((p : ℝ) / ((p + q : ℕ) : ℝ)) ^ p) *
        (((q : ℝ) / ((p + q : ℕ) : ℝ)) ^ q) := by
    refine le_trans (MeasureTheory.integral_mono_of_nonneg
      (f := fun θ : ℝ => (G l θ) ^ p * (G k θ) ^ q * q0 θ)
      (g := fun θ : ℝ => ((dpKappa c m thetaStar) ^ (p + q) *
        (((p : ℝ) / ((p + q : ℕ) : ℝ)) ^ p) * (((q : ℝ) / ((p + q : ℕ) : ℝ)) ^ q)) * q0 θ)
      ?_ ?_ ?_) ?_
    · exact Filter.Eventually.of_forall fun θ =>
        mul_nonneg (mul_nonneg (pow_nonneg (hGl0 θ) p) (pow_nonneg (hGk0 θ) q)) (hq0_nonneg θ)
    · exact hq0_intble.const_mul _
    · exact Filter.Eventually.of_forall fun θ =>
        mul_le_mul_of_nonneg_right (hpoint θ) (hq0_nonneg θ)
    · simp only [MeasureTheory.integral_const_mul, hq0_int, mul_one, le_refl]
  have hw : w B = ((B.card - 1).factorial : ℝ) *
      ∫ θ, (G l θ) ^ p * (G k θ) ^ q * q0 θ := by
    show ((B.card - 1).factorial : ℝ) *
        ∫ θ, (∏ l' : Fin t, (G l' θ) ^ (B.filter (fun i => lab i = l')).card) * q0 θ = _
    simp only [hprod]
  refine ⟨?_, ?_⟩
  · have hle1 : w B ≤ ((B.card - 1).factorial : ℝ) *
        ((dpKappa c m thetaStar) ^ (p + q) * (((p : ℝ) / ((p + q : ℕ) : ℝ)) ^ p) *
          (((q : ℝ) / ((p + q : ℕ) : ℝ)) ^ q)) := by
      rw [hw]
      exact mul_le_mul_of_nonneg_left hint (by positivity)
    calc w B ≤ ((B.card - 1).factorial : ℝ) *
          ((dpKappa c m thetaStar) ^ (p + q) * (((p : ℝ) / ((p + q : ℕ) : ℝ)) ^ p) *
            (((q : ℝ) / ((p + q : ℕ) : ℝ)) ^ q)) := hle1
      _ = (dpKappa c m thetaStar) ^ (p + q) * ((p + q - 1).factorial : ℝ) *
            (((p : ℝ) / ((p + q : ℕ) : ℝ)) ^ p) *
            (((q : ℝ) / ((p + q : ℕ) : ℝ)) ^ q) := by
          rw [hcard]
          ring
  · have hbpos : (0 : ℝ) < ((p + q : ℕ) : ℝ) := by
      have h : 0 < p + q := by omega
      exact_mod_cast h
    have hpf : (0 : ℝ) < (p.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos p
    have hqf : (0 : ℝ) < (q.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos q
    have hdenpos : (0 : ℝ) < (p.factorial : ℝ) * (q.factorial : ℝ) := mul_pos hpf hqf
    have hPnn : 0 ≤ (p : ℝ) / ((p + q : ℕ) : ℝ) := div_nonneg (Nat.cast_nonneg p) hbpos.le
    have hQnn : 0 ≤ (q : ℝ) / ((p + q : ℕ) : ℝ) := div_nonneg (Nat.cast_nonneg q) hbpos.le
    have hpq0 : (p : ℝ) / ((p + q : ℕ) : ℝ) + (q : ℝ) / ((p + q : ℕ) : ℝ) = 1 := by
      have hbne : ((p + q : ℕ) : ℝ) ≠ 0 := ne_of_gt hbpos
      have h1 : ((p + q : ℕ) : ℝ) = (p : ℝ) + (q : ℝ) := by rw [Nat.cast_add]
      rw [← add_div, ← h1, div_self hbne]
    have hbinom : ((p + q).choose p : ℝ) * ((p : ℝ) / ((p + q : ℕ) : ℝ)) ^ p *
        ((q : ℝ) / ((p + q : ℕ) : ℝ)) ^ q ≤ 1 := by
      have hpow : ((p : ℝ) / ((p + q : ℕ) : ℝ) + (q : ℝ) / ((p + q : ℕ) : ℝ)) ^ (p + q) = 1 := by
        rw [hpq0, one_pow]
      have hsum : Finset.sum (Finset.range (p + q + 1))
          (fun j : ℕ => ((p : ℝ) / ((p + q : ℕ) : ℝ)) ^ j *
            ((q : ℝ) / ((p + q : ℕ) : ℝ)) ^ (p + q - j) * (((p + q).choose j : ℕ) : ℝ)) = 1 := by
        rw [← hpow]
        exact (add_pow _ _ _).symm
      have hsingle : ((p : ℝ) / ((p + q : ℕ) : ℝ)) ^ p *
          ((q : ℝ) / ((p + q : ℕ) : ℝ)) ^ (p + q - p) * (((p + q).choose p : ℕ) : ℝ) ≤
          Finset.sum (Finset.range (p + q + 1))
            (fun j : ℕ => ((p : ℝ) / ((p + q : ℕ) : ℝ)) ^ j *
              ((q : ℝ) / ((p + q : ℕ) : ℝ)) ^ (p + q - j) * (((p + q).choose j : ℕ) : ℝ)) := by
        refine Finset.single_le_sum
          (f := fun j : ℕ => ((p : ℝ) / ((p + q : ℕ) : ℝ)) ^ j *
            ((q : ℝ) / ((p + q : ℕ) : ℝ)) ^ (p + q - j) * (((p + q).choose j : ℕ) : ℝ))
          (s := Finset.range (p + q + 1)) (a := p) ?_ ?_
        · intro j hj
          exact mul_nonneg (mul_nonneg (pow_nonneg hPnn j) (pow_nonneg hQnn _)) (Nat.cast_nonneg _)
        · rw [Finset.mem_range]
          omega
      rw [hsum] at hsingle
      have hsub : p + q - p = q := by omega
      rw [hsub] at hsingle
      calc ((p + q).choose p : ℝ) * ((p : ℝ) / ((p + q : ℕ) : ℝ)) ^ p *
            ((q : ℝ) / ((p + q : ℕ) : ℝ)) ^ q
          = ((p : ℝ) / ((p + q : ℕ) : ℝ)) ^ p * ((q : ℝ) / ((p + q : ℕ) : ℝ)) ^ q *
              ((p + q).choose p : ℝ) := by ring
        _ ≤ 1 := hsingle
    have hbfact : ((p + q : ℕ) : ℝ) * (((p + q - 1).factorial : ℕ) : ℝ) =
        (((p + q).factorial : ℕ) : ℝ) := by
      have hb1 : 1 ≤ p + q := by omega
      have h := Nat.factorial_succ (p + q - 1)
      rw [Nat.sub_add_cancel hb1] at h
      rw [h, Nat.cast_mul]
    have hchoose : ((p + q).choose p : ℝ) * (p.factorial : ℝ) * (q.factorial : ℝ) =
        ((p + q).factorial : ℝ) := by
      have hsub : p + q - p = q := by omega
      have h := Nat.choose_mul_factorial_mul_factorial (show p ≤ p + q by omega)
      rw [hsub] at h
      calc ((p + q).choose p : ℝ) * (p.factorial : ℝ) * (q.factorial : ℝ)
          = (((p + q).choose p * p.factorial * q.factorial : ℕ) : ℝ) := by
            rw [Nat.cast_mul, Nat.cast_mul]
        _ = (((p + q).factorial : ℕ) : ℝ) := by rw [h]
    have hnum : ((p + q - 1).factorial : ℝ) * ((p + q : ℕ) : ℝ) =
        ((p + q).choose p : ℝ) * ((p.factorial : ℝ) * (q.factorial : ℝ)) := by
      calc ((p + q - 1).factorial : ℝ) * ((p + q : ℕ) : ℝ)
          = ((p + q : ℕ) : ℝ) * (((p + q - 1).factorial : ℕ) : ℝ) := by ring
        _ = (((p + q).factorial : ℕ) : ℝ) := hbfact
        _ = ((p + q).choose p : ℝ) * (p.factorial : ℝ) * (q.factorial : ℝ) := hchoose.symm
        _ = ((p + q).choose p : ℝ) * ((p.factorial : ℝ) * (q.factorial : ℝ)) := by ring
    have hle : w B * ((p + q : ℕ) : ℝ) ≤
        (((B.card - 1).factorial : ℝ) * ((dpKappa c m thetaStar) ^ (p + q) *
          (((p : ℝ) / ((p + q : ℕ) : ℝ)) ^ p) * (((q : ℝ) / ((p + q : ℕ) : ℝ)) ^ q))) *
          ((p + q : ℕ) : ℝ) := by
      have h1 : w B ≤ ((B.card - 1).factorial : ℝ) *
          ((dpKappa c m thetaStar) ^ (p + q) * (((p : ℝ) / ((p + q : ℕ) : ℝ)) ^ p) *
            (((q : ℝ) / ((p + q : ℕ) : ℝ)) ^ q)) := by
        rw [hw]
        exact mul_le_mul_of_nonneg_left hint (by positivity)
      exact mul_le_mul_of_nonneg_right h1 hbpos.le
    rw [div_le_div_iff₀ hdenpos hbpos]
    refine le_trans hle ?_
    rw [hcard]
    calc (((p + q - 1).factorial : ℝ) * ((dpKappa c m thetaStar) ^ (p + q) *
          (((p : ℝ) / ((p + q : ℕ) : ℝ)) ^ p) * (((q : ℝ) / ((p + q : ℕ) : ℝ)) ^ q))) *
          ((p + q : ℕ) : ℝ)
        = (((p + q - 1).factorial : ℝ) * ((p + q : ℕ) : ℝ)) *
            ((dpKappa c m thetaStar) ^ (p + q) * (((p : ℝ) / ((p + q : ℕ) : ℝ)) ^ p) *
              (((q : ℝ) / ((p + q : ℕ) : ℝ)) ^ q)) := by ring
      _ = (((p + q).choose p : ℝ) * ((p.factorial : ℝ) * (q.factorial : ℝ))) *
            ((dpKappa c m thetaStar) ^ (p + q) * (((p : ℝ) / ((p + q : ℕ) : ℝ)) ^ p) *
              (((q : ℝ) / ((p + q : ℕ) : ℝ)) ^ q)) := by rw [hnum]
      _ = (dpKappa c m thetaStar) ^ (p + q) * ((((p + q).choose p : ℝ) *
            (((p : ℝ) / ((p + q : ℕ) : ℝ)) ^ p) * (((q : ℝ) / ((p + q : ℕ) : ℝ)) ^ q)) *
            ((p.factorial : ℝ) * (q.factorial : ℝ))) := by ring
      _ ≤ (dpKappa c m thetaStar) ^ (p + q) * ((p.factorial : ℝ) * (q.factorial : ℝ)) := by
          have h3 := mul_le_mul_of_nonneg_right hbinom hdenpos.le
          have h3' : ((p + q).choose p : ℝ) * (((p : ℝ) / ((p + q : ℕ) : ℝ)) ^ p) *
              (((q : ℝ) / ((p + q : ℕ) : ℝ)) ^ q) * ((p.factorial : ℝ) * (q.factorial : ℝ)) ≤
              (p.factorial : ℝ) * (q.factorial : ℝ) := by simpa using h3
          exact mul_le_mul_of_nonneg_left h3' (pow_nonneg hκnn (p + q))
  /- @proof-region region.target-node.session.bc3c14c8fbabafab end -/

end

end Statlib.Imported

end DPCompletedProof
