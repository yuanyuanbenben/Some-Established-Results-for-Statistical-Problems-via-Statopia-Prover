import ProverJobs.job_paper_dc88427b52844263b5321fc99eb582d8.Base
open MeasureTheory Filter Topology
open scoped BigOperators
open Statlib.Imported
noncomputable section
namespace OfflineDPLabelCells

lemma window_label_unique {t : ℕ} (c : ℝ) (θ : Fin t → ℝ)
    (hsep : ∀ j k, j ≠ k → 2*c < |θ j-θ k|)
    {j k : Fin t} {x : ℝ}
    (hj : x ∈ Set.Icc (θ j-c) (θ j+c))
    (hk : x ∈ Set.Icc (θ k-c) (θ k+c)) : j = k := by
  by_contra hjk
  have hle : |θ j-θ k| ≤ 2*c := by
    rw [abs_le]
    constructor <;> linarith [hj.1,hj.2,hk.1,hk.2]
  exact (not_lt_of_ge hle) (hsep j k hjk)

lemma vector_block_eq_fiber {t n : ℕ} (c : ℝ) (θ : Fin t → ℝ)
    (hsep : ∀ j k, j ≠ k → 2*c < |θ j-θ k|)
    (lab : Fin n → Fin t) (x : Fin n → ℝ)
    (hcell : ∀ i, x i ∈ Set.Icc (θ (lab i)-c) (θ (lab i)+c)) (j : Fin t) :
    Finset.univ.filter (fun i => x i ∈ Set.Icc (θ j-c) (θ j+c)) =
      Finset.univ.filter (fun i => lab i = j) := by
  classical
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact fun hi => window_label_unique c θ hsep (hcell i) hi
  · intro hi
    simpa only [hi] using hcell i

lemma actual_block_eq_fiber {t n : ℕ} (c : ℝ) (θ : Fin t → ℝ)
    (hsep : ∀ j k, j ≠ k → 2*c < |θ j-θ k|)
    (lab : Fin n → Fin t) (ω : ℕ → ℝ)
    (hcell : ∀ i : Fin n, ω (i : ℕ) ∈ Set.Icc (θ (lab i)-c) (θ (lab i)+c))
    (j : Fin t) :
    dpBlock c θ n ω j = Finset.univ.filter (fun i => lab i = j) :=
  vector_block_eq_fiber c θ hsep lab (dpXseq n ω) hcell j

/-- Empty label classes contribute nothing on the source good event. -/
lemma empty_label_not_omega {t n : ℕ} (c : ℝ) (θ : Fin t → ℝ)
    (hsep : ∀ j k, j ≠ k → 2*c < |θ j-θ k|)
    (N : Fin t → ℕ) (hN : ∀ j, 1 ≤ N j)
    (lab : Fin n → Fin t) (ω : ℕ → ℝ)
    (hcell : ∀ i : Fin n, ω (i : ℕ) ∈ Set.Icc (θ (lab i)-c) (θ (lab i)+c))
    (j : Fin t) (hempty : (Finset.univ.filter (fun i => lab i = j)).card = 0) :
    ¬ dpOmega c θ N n ω := by
  intro hOmega
  have h := (hN j).trans (hOmega j).1
  rw [actual_block_eq_fiber c θ hsep lab ω hcell j, hempty] at h
  omega

lemma omega_positive_label_counts {t n : ℕ} (c : ℝ) (θ : Fin t → ℝ)
    (hsep : ∀ j k, j ≠ k → 2*c < |θ j-θ k|)
    (N : Fin t → ℕ) (hN : ∀ j, 1 ≤ N j)
    (lab : Fin n → Fin t) (ω : ℕ → ℝ)
    (hcell : ∀ i : Fin n, ω (i : ℕ) ∈ Set.Icc (θ (lab i)-c) (θ (lab i)+c))
    (hOmega : dpOmega c θ N n ω) :
    ∀ j, 0 < (Finset.univ.filter (fun i => lab i = j)).card := by
  intro j
  have h := (hN j).trans (hOmega j).1
  rw [actual_block_eq_fiber c θ hsep lab ω hcell j] at h
  omega

#print axioms actual_block_eq_fiber
#print axioms empty_label_not_omega
end OfflineDPLabelCells
