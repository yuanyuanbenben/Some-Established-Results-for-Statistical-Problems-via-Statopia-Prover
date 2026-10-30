import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q42.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q42.Base

open Msc62GroundTruth

namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_3469730755_08c680cd : ∀ (n : ℕ) (q : ℝ) (x : Fin n → Bool),
    let p : Fin n → Bool → ℝ := fun i a => if a = x i then q else 1 - q
    let P : (Fin n → Bool) → ℝ := fun y => ∏ i : Fin n, p i (y i)
    (∑ y : Fin n → Bool, P y) = 1 := by
  /- @proof-region region.target-node.session.1bf6d7f929b222f5 begin -/
  intro n q x
  dsimp only
  have hbool : ∀ f : Bool → ℝ, (∑ a : Bool, f a) = f true + f false := by
    intro f
    have hu : (Finset.univ : Finset Bool) = {true, false} := by
      ext a
      cases a <;> simp
    rw [hu]
    simp
  have hcoord : ∀ i : Fin n, (∑ a : Bool, (if a = x i then q else 1 - q)) = 1 := by
    intro i
    rw [hbool]
    cases h : x i <;> simp <;> ring
  have key : (∑ y : Fin n → Bool, ∏ i : Fin n, (if y i = x i then q else 1 - q))
      = ∏ i : Fin n, ∑ a : Bool, (if a = x i then q else 1 - q) := by
    have h1 : (∑ y ∈ Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset Bool)),
          ∏ i : Fin n, (if y i = x i then q else 1 - q))
        = ∏ i : Fin n, ∑ a ∈ (Finset.univ : Finset Bool), (if a = x i then q else 1 - q) :=
      Finset.sum_prod_piFinset (Finset.univ : Finset Bool)
        (fun i a => if a = x i then q else 1 - q)
    have h2 : (Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset Bool)))
        = (Finset.univ : Finset (Fin n → Bool)) := Fintype.piFinset_univ
    rw [h2] at h1
    exact h1
  rw [key]
  exact Finset.prod_eq_one (fun i _ => hcoord i)
  /- @proof-region region.target-node.session.1bf6d7f929b222f5 end -/

end Msc62GroundTruth
