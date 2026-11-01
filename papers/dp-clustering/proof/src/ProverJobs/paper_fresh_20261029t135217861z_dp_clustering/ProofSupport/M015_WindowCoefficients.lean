import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M009_BlockBounds
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M014_Coefficients

/- Original module ProverJobs.manual_dp_cons_finish_20261031.WindowCoefficients; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Topology
noncomputable section
namespace ManualDPCons
open Statlib.Imported
set_option maxHeartbeats 1200000

/-- Concrete full-partition coefficient bound; mixed blocks are retained. -/
theorem window_partition_bound
    (t : ℕ) (ht : 1 ≤ t) (c : ℝ) (hc : 0 < c)
    (g q0 : ℝ → ℝ) (theta : Fin t → ℝ) (m U : ℝ) (hm : 0 < m) (hU : 0 < U)
    (hgmeas : Measurable g) (hg0 : ∀ z, 0 ≤ g z)
    (hgzero : ∀ z, z ∉ Set.Icc (-c) c → g z = 0)
    (hglo : ∀ z ∈ Set.Icc (-c) c, m ≤ g z) (hgnorm : ∫ z, g z ∂volume = 1)
    (hqmeas : Measurable q0) (hq0 : ∀ z, 0 ≤ q0 z) (hqnorm : ∫ z, q0 z ∂volume = 1)
    (hT3 : ∀ j y, y ∈ Set.Icc (0 : ℝ) (2 * c) → q0 (theta j + y) + q0 (theta j - y) ≤ U)
    (hsep : ∀ j k, j ≠ k → 2 * c < |theta j - theta k|)
    (n : ℕ) (hn : 1 ≤ n) (lab : Fin n → Fin t)
    (hnclass : ∀ l, 1 ≤ (Finset.univ.filter (fun i => lab i = l)).card)
    (k : ℕ) (hk : 1 ≤ k) :
    let G := fun l z => ∫ x in Set.Icc (theta l - c) (theta l + c), g (x - z) ∂volume
    let w := fun B : Finset (Fin n) => ((B.card - 1).factorial : ℝ) *
      ∫ z, (∏ l : Fin t, (G l z) ^ (B.filter (fun i => lab i = l)).card) * q0 z ∂volume
    (∑ A ∈ dpTau n k, ∏ B ∈ A, w B) ≤
      (∏ l : Fin t, (((Finset.univ.filter (fun i => lab i = l)).card.factorial : ℝ) /
        (((Finset.univ.filter (fun i => lab i = l)).card : ℝ) ^ 2))) *
          (dpK5 U m c theta) ^ k / (k.factorial : ℝ) := by
  classical
  intro G w
  let E : Finset (Finset (Fin t)) := (dpClosePair c theta).image (fun pr => {pr.1, pr.2})
  have hEmem : ∀ l k : Fin t, l ≠ k → |theta l - theta k| < 4 * c → {l, k} ∈ E := by
    intro l k hlk hdist
    apply Finset.mem_image.mpr
    exact ⟨(l,k), by simpa [dpClosePair] using And.intro hlk hdist, rfl⟩
  have hE : ∀ e ∈ E, e.card = 2 := by
    intro e he
    obtain ⟨⟨l,k⟩, hmem, rfl⟩ := Finset.mem_image.mp he
    have hlk : l ≠ k := (show l ≠ k ∧ |theta l - theta k| < 4 * c by simpa [dpClosePair] using hmem).1
    simp [hlk]
  have hb := statopia_math_node_1011772921_00d6fbb2 t ht c hc g q0 theta m U hm hU
    hgmeas hg0 hgzero hglo hgnorm hqmeas hq0 hqnorm hT3 hsep
  have hg := hb.2.2 n hn lab
  have hG0 : ∀ l z, 0 ≤ G l z := fun l z => integral_nonneg (fun x => hg0 _)
  have hw0 : ∀ B : Finset (Fin n), B.Nonempty → 0 ≤ w B := by
    intro B hB
    exact mul_nonneg (by positivity) (integral_nonneg (fun z =>
      mul_nonneg (Finset.prod_nonneg (fun l hl => pow_nonneg (hG0 l z) _)) (hq0 z)))
  have hpure : ∀ (B : Finset (Fin n)) (l : Fin t), B.Nonempty →
      B ⊆ Finset.univ.filter (fun i => lab i = l) →
      w B ≤ (U / m) * ((B.card.factorial : ℝ) / (B.card : ℝ) ^ 2) := by
    intro B l hB hsub
    exact (hg.1 B l hB (fun i hi => (Finset.mem_filter.mp (hsub hi)).2)).1.trans
      (hg.1 B l hB (fun i hi => (Finset.mem_filter.mp (hsub hi)).2)).2
  have hcross : ∀ (B : Finset (Fin n)) (l k : Fin t), l ≠ k → {l,k} ∈ E → B.Nonempty →
      B ⊆ Finset.univ.filter (fun i => lab i = l) ∪ Finset.univ.filter (fun i => lab i = k) →
      (B ∩ Finset.univ.filter (fun i => lab i = l)).Nonempty →
      (B ∩ Finset.univ.filter (fun i => lab i = k)).Nonempty →
      w B / (((B ∩ Finset.univ.filter (fun i => lab i = l)).card.factorial : ℝ) *
        ((B ∩ Finset.univ.filter (fun i => lab i = k)).card.factorial : ℝ)) ≤
      (dpKappa c m theta) ^ ((B ∩ Finset.univ.filter (fun i => lab i = l)).card +
        (B ∩ Finset.univ.filter (fun i => lab i = k)).card) /
      (((B ∩ Finset.univ.filter (fun i => lab i = l)).card +
        (B ∩ Finset.univ.filter (fun i => lab i = k)).card : ℕ) : ℝ) := by
    intro B l k hlk hE hB hsub hBl hBk
    have heq : ∀ l, B ∩ Finset.univ.filter (fun i => lab i = l) = B.filter (fun i => lab i = l) := by
      intro l; ext i; simp
    simp_rw [heq] at hBl hBk ⊢
    apply (hg.2.1 B l k hlk hBl hBk ?_).2
    intro i hi
    simpa using hsub hi
  have hother : ∀ B : Finset (Fin n), B.Nonempty →
      (∀ l, ¬ B ⊆ Finset.univ.filter (fun i => lab i = l)) →
      (∀ l k, l ≠ k → {l,k} ∈ E →
        ¬ (B ⊆ Finset.univ.filter (fun i => lab i = l) ∪ Finset.univ.filter (fun i => lab i = k) ∧
          (B ∩ Finset.univ.filter (fun i => lab i = l)).Nonempty ∧
          (B ∩ Finset.univ.filter (fun i => lab i = k)).Nonempty)) → w B = 0 := by
    intro B hB hp hc
    by_cases hcard : 3 ≤ (B.image lab).card
    · exact hg.2.2.1 B hcard
    have hcard2 : (B.image lab).card = 2 := by
      by_contra hnot
      have hh : (B.image lab).card ≤ 1 := by omega
      obtain ⟨i, hi⟩ := hB
      have hl : lab i ∈ B.image lab := Finset.mem_image_of_mem _ hi
      apply hp (lab i)
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (Finset.card_le_one.mp hh) (lab a) (Finset.mem_image_of_mem _ ha) (lab i) hl
    obtain ⟨l, k, hlk, himage⟩ := Finset.card_eq_two.mp hcard2
    have hlabels : ∀ i ∈ B, lab i = l ∨ lab i = k := by
      intro i hi
      have hh := Finset.mem_image_of_mem lab hi
      simpa [himage] using hh
    have hBl : (B.filter (fun i => lab i = l)).Nonempty := by
      have hl : l ∈ B.image lab := by simp [himage]
      obtain ⟨i, hi, hil⟩ := Finset.mem_image.mp hl
      exact ⟨i, Finset.mem_filter.mpr ⟨hi, hil⟩⟩
    have hBk : (B.filter (fun i => lab i = k)).Nonempty := by
      have hk : k ∈ B.image lab := by simp [himage]
      obtain ⟨i, hi, hik⟩ := Finset.mem_image.mp hk
      exact ⟨i, Finset.mem_filter.mpr ⟨hi, hik⟩⟩
    apply hg.2.2.2 B l k hlk hBl hBk hlabels
    by_contra hdist
    apply hc l k hlk (hEmem l k hlk (lt_of_not_ge hdist))
    refine ⟨?_, ?_, ?_⟩
    · intro i hi; simpa using hlabels i hi
    · simpa [Finset.inter_filter] using hBl
    · simpa [Finset.inter_filter] using hBk
  let C0 := dpC0
  let H := dpH c m theta
  let B0 := C0 * H
  let K5 := max 1 (B0 * ((t : ℝ) * (U / m) + B0 * (E.card : ℝ) / 2))
  have hcoef := statopia_math_node_1865983872_fc33fb01 t ht n hn lab E hE (U/m)
    (dpKappa c m theta) (div_pos hU hm) hb.2.1.1 hb.2.1.2 w hw0 hpure hcross hother
    hnclass C0 H B0 K5 rfl rfl rfl rfl
  have hB0 : 0 ≤ B0 := by
    have h1 : 1 ≤ C0 := le_max_left _ _
    have h2 : 1 ≤ H := le_max_left _ _
    dsimp only [B0]
    positivity
  have hK5le : K5 ≤ dpK5 U m c theta := by
    apply max_le_max le_rfl
    change B0 * ((t : ℝ) * (U/m) + B0 * (E.card : ℝ) / 2) ≤
      B0 * ((t : ℝ) * (U/m) + B0 * (((dpClosePair c theta).card : ℝ) / 2))
    apply mul_le_mul_of_nonneg_left _ hB0
    apply add_le_add_right
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ hB0
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact_mod_cast Finset.card_image_le (s := dpClosePair c theta) (f := fun pr : Fin t × Fin t => ({pr.1,pr.2} : Finset (Fin t)))
  calc (∑ A ∈ dpTau n k, ∏ B ∈ A, w B)
      ≤ (∏ l : Fin t, (((Finset.univ.filter (fun i => lab i = l)).card.factorial : ℝ) /
        (((Finset.univ.filter (fun i => lab i = l)).card : ℝ) ^ 2))) * K5 ^ k / (k.factorial : ℝ) := hcoef.2.2 k hk
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by dsimp [K5]; positivity) hK5le k)
        (Finset.prod_nonneg (fun l hl => by positivity))) (by positivity)

end ManualDPCons
end
end DPCompletedProof
