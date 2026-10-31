import ProverJobs.job_paper_bd898e13604647fb8e67ad70fa3fcacd.Vocabulary
import ProverJobs.job_paper_bd898e13604647fb8e67ad70fa3fcacd.Base
import ProverJobs.job_paper_bd898e13604647fb8e67ad70fa3fcacd.ProvedNodes.Node_3559146925_0159b75f_83b1b9bc

open Statlib.Imported

namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_360176551_1d2728fd : ∀ (t s : ℕ) (p : Fin t → ℝ),
    ((Fintype.piFinset (fun _ : Fin t => Finset.range (s + 1))).filter
        (fun sv : Fin t → ℕ => ∑ j : Fin t, sv j = s)).sum
        (fun sv : Fin t → ℕ =>
          ((s.factorial : ℝ) / ∏ j : Fin t, ((sv j).factorial : ℝ)) *
            ∏ j : Fin t, (p j) ^ (sv j))
      = (∑ j : Fin t, p j) ^ s := by
  /- @proof-region region.target-node.session.578ed1670d79309b begin -/
  intro t s p
  rw [Fintype.sum_pow]
  set T : Finset (Fin t → ℕ) :=
    (Fintype.piFinset (fun _ : Fin t => Finset.range (s + 1))).filter
      (fun sv : Fin t → ℕ => ∑ j : Fin t, sv j = s) with hT
  set φ : (Fin s → Fin t) → (Fin t → ℕ) :=
    fun f j => (Finset.univ.filter (fun i : Fin s => f i = j)).card with hφ
  set F : (Fin t → ℕ) → Finset (Fin s → Fin t) :=
    fun sv => Finset.univ.filter (fun f => φ f = sv) with hF
  set P : (Fin t → ℕ) → ℝ := fun sv => ∏ j : Fin t, (p j) ^ (sv j) with hP
  set G : (Fin s → Fin t) → ℝ := fun f => ∏ i : Fin s, p (f i) with hG
  have hsumφ : ∀ f : Fin s → Fin t, ∑ j : Fin t, φ f j = s := by
    intro f
    have h := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin s))
      (Finset.univ : Finset (Fin t)) f
    have hR : (Finset.univ.filter (fun i : Fin s => f i ∈ (Finset.univ : Finset (Fin t))))
        = (Finset.univ : Finset (Fin s)) :=
      Finset.filter_true_of_mem (fun i _ => Finset.mem_univ _)
    rw [hR] at h
    simpa [hφ] using h
  have hφT : ∀ f : Fin s → Fin t, φ f ∈ T := by
    intro f
    rw [hT, Finset.mem_filter]
    simp only [Fintype.mem_piFinset]
    refine ⟨fun j => ?_, hsumφ f⟩
    rw [Finset.mem_range]
    have h2 : (Finset.univ.filter (fun i : Fin s => f i = j)).card
        ≤ (Finset.univ : Finset (Fin s)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hle : φ f j ≤ s := by simpa [hφ] using h2
    exact Nat.lt_succ_of_le hle
  have hFeq : ∀ sv : Fin t → ℕ, F sv = Finset.univ.filter
      (fun f : Fin s → Fin t => ∀ j : Fin t,
        (Finset.univ.filter (fun i : Fin s => f i = j)).card = sv j) := by
    intro sv
    ext f
    simp only [hF, hφ, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h j => congrFun h j, fun h => funext h⟩
  have hconst : ∀ (sv : Fin t → ℕ) (f : Fin s → Fin t), f ∈ F sv → G f = P sv := by
    intro sv f hf
    have hφeq : φ f = sv := by
      simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hf
      exact hf
    show (∏ i : Fin s, p (f i)) = ∏ j : Fin t, (p j) ^ (sv j)
    rw [← Finset.prod_fiberwise (Finset.univ : Finset (Fin s))
      (fun i : Fin s => f i) (fun i : Fin s => p (f i))]
    apply Finset.prod_congr rfl
    intro j _
    have hfib : (∏ i ∈ Finset.univ.filter (fun i : Fin s => f i = j), p (f i))
        = (∏ i ∈ Finset.univ.filter (fun i : Fin s => f i = j), p j) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [hi]
    rw [hfib, Finset.prod_const]
    rw [show (Finset.univ.filter (fun i : Fin s => f i = j)).card = sv j from
      congrFun hφeq j]
  have hA : (∑ sv ∈ T,
        ((s.factorial : ℝ) / ∏ j : Fin t, ((sv j).factorial : ℝ)) * P sv)
      = ∑ sv ∈ T, ∑ f ∈ F sv, G f := by
    refine Finset.sum_congr rfl ?_
    intro sv hsv
    have hsvsum : ∑ j : Fin t, sv j = s := by
      rw [hT] at hsv
      exact (Finset.mem_filter.mp hsv).2
    have hcard : ((F sv).card : ℝ) = (s.factorial : ℝ) / ∏ j : Fin t, ((sv j).factorial : ℝ) := by
      rw [hFeq sv]
      exact statopia_math_node_3559146925_0159b75f t s sv hsvsum
    have hsum_g : ∑ f ∈ F sv, G f = (F sv).card * P sv := by
      have h1 : ∑ f ∈ F sv, G f = ∑ f ∈ F sv, P sv :=
        Finset.sum_congr rfl (fun f hf => hconst sv f hf)
      rw [h1, Finset.sum_const]
      simp
    rw [hsum_g, hcard]
  have hB : (∑ sv ∈ T, ∑ f ∈ F sv, G f) = ∑ f : Fin s → Fin t, G f := by
    have hmap : ∀ f ∈ (Finset.univ : Finset (Fin s → Fin t)), φ f ∈ T := fun f _ => hφT f
    have h := Finset.sum_fiberwise_of_maps_to hmap G
    simpa only [hF] using h
  rw [hA, hB]
  /- @proof-region region.target-node.session.578ed1670d79309b end -/

end Statlib.Imported
