import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q18.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q18.Base

open MeasureTheory ProbabilityTheory Filter

open MeasureTheory ProbabilityTheory Filter

set_option autoImplicit false in
theorem statopia_math_node_602889494_40c9f215 : ∀ (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (F : ℝ → ℝ) (hF : StrictMono F)
    (a : Fin m → ℝ) (b : Fin n → ℝ),
    let Delta : (Fin m → ℝ) → (Fin n → ℝ) → ℝ → ℝ := fun a b t =>
      |(m : ℝ)⁻¹ * ∑ i : Fin m, (if a i ≤ t then (1 : ℝ) else 0)
        - (n : ℝ)⁻¹ * ∑ j : Fin n, (if b j ≤ t then (1 : ℝ) else 0)|
    let Mvals : (Fin m → ℝ) → (Fin n → ℝ) → Finset ℝ := fun a b =>
      insert (0 : ℝ) ((Finset.univ.image (fun i : Fin m => Delta a b (a i)))
        ∪ (Finset.univ.image (fun j : Fin n => Delta a b (b j))))
    let M : (Fin m → ℝ) → (Fin n → ℝ) → ℝ := fun a b =>
      (Mvals a b).max' (Finset.insert_nonempty (0 : ℝ) _)
    M (fun i => F (a i)) (fun j => F (b j)) = M a b := by
  /- @proof-region region.target-node.session.20d764f9e754df0d begin -/
  intro m n hm hn F hF a b
  dsimp only
  simp only [hF.le_iff_le]
  /- @proof-region region.target-node.session.20d764f9e754df0d end -/
