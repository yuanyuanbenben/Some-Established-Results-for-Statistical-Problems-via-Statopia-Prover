import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q33.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q33.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q33.ProvedNodes.Node_1457182788_f9803ee7_6f4b3769

open Msc62GroundTruth

namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_958340259_479a840d : ∀ (N H : ℕ) (group : Fin N → Fin H) (outcome : Fin N → Bool)
    (forecast : Fin H → ℝ) (hN : (N : ℝ) ≠ 0),
    let bit : Bool → ℝ := fun b => if b then 1 else 0
    let bin : Fin H → Finset (Fin N) :=
      fun g => Finset.univ.filter (fun i : Fin N => group i = g)
    let brier : ℝ :=
      (1 / (N : ℝ)) *
        ∑ i : Fin N, (forecast (group i) - bit (outcome i)) ^ 2
    let ybar : ℝ := (1 / (N : ℝ)) * ∑ i : Fin N, bit (outcome i)
    brier =
      (1 / (N : ℝ)) * ∑ g : Fin H, ((bin g).card : ℝ) * (forecast g) ^ 2
        - (2 / (N : ℝ)) * ∑ g : Fin H,
            forecast g * (bin g).sum (fun i => bit (outcome i))
        + ybar := by
  /- @proof-region region.target-node.session.378060b1d3ab010d begin -/
  intro N H group outcome forecast hN
  dsimp only
  let y : Fin N → ℝ := fun i => if outcome i then 1 else 0
  change (1 / (N : ℝ)) * ∑ i : Fin N, (forecast (group i) - y i) ^ 2 = (1 / (N : ℝ)) * ∑ g : Fin H, ((Finset.univ.filter (fun i : Fin N => group i = g)).card : ℝ) * (forecast g) ^ 2 - (2 / (N : ℝ)) * ∑ g : Fin H, forecast g * (∑ i ∈ Finset.univ.filter (fun i : Fin N => group i = g), y i) + (1 / (N : ℝ)) * ∑ i : Fin N, y i
  have hy_sq : ∀ i : Fin N, y i ^ 2 = y i := by
    intro i
    cases h : outcome i <;> simp [y, h]
  have hcongr : ∀ g : Fin H, (∑ i ∈ Finset.univ.filter (fun i : Fin N => group i = g), (forecast (group i) - y i) ^ 2) = ∑ i ∈ Finset.univ.filter (fun i : Fin N => group i = g), (forecast g - y i) ^ 2 := by
    intro g
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_filter] at hi
    rw [hi.2]
  have hbin : ∀ g : Fin H, (∑ i ∈ Finset.univ.filter (fun i : Fin N => group i = g), (forecast g - y i) ^ 2) = ((Finset.univ.filter (fun i : Fin N => group i = g)).card : ℝ) * (forecast g) ^ 2 - 2 * forecast g * (∑ i ∈ Finset.univ.filter (fun i : Fin N => group i = g), y i) + (∑ i ∈ Finset.univ.filter (fun i : Fin N => group i = g), y i) := by
    intro g
    have step1 : (∑ i ∈ Finset.univ.filter (fun i : Fin N => group i = g), (forecast g - y i) ^ 2) = ∑ i ∈ Finset.univ.filter (fun i : Fin N => group i = g), ((forecast g) ^ 2 - 2 * forecast g * y i + y i) := by
      apply Finset.sum_congr rfl
      intro i _
      nlinarith [hy_sq i]
    rw [step1, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  have hpart : ∑ i : Fin N, (forecast (group i) - y i) ^ 2 = ∑ g : Fin H, ∑ i ∈ Finset.univ.filter (fun i : Fin N => group i = g), (forecast (group i) - y i) ^ 2 := by
    simpa using statopia_math_node_1457182788_f9803ee7 N H group (fun i => (forecast (group i) - y i) ^ 2)
  have hT : ∑ i : Fin N, (forecast (group i) - y i) ^ 2 = ∑ g : Fin H, (((Finset.univ.filter (fun i : Fin N => group i = g)).card : ℝ) * (forecast g) ^ 2 - 2 * forecast g * (∑ i ∈ Finset.univ.filter (fun i : Fin N => group i = g), y i) + (∑ i ∈ Finset.univ.filter (fun i : Fin N => group i = g), y i)) := by
    rw [hpart]
    apply Finset.sum_congr rfl
    intro g _
    rw [hcongr g, hbin g]
  have hsum1 : (∑ g : Fin H, (((Finset.univ.filter (fun i : Fin N => group i = g)).card : ℝ) * (forecast g) ^ 2 - 2 * forecast g * (∑ i ∈ Finset.univ.filter (fun i : Fin N => group i = g), y i) + (∑ i ∈ Finset.univ.filter (fun i : Fin N => group i = g), y i))) = (∑ g : Fin H, ((Finset.univ.filter (fun i : Fin N => group i = g)).card : ℝ) * (forecast g) ^ 2) - (∑ g : Fin H, 2 * forecast g * (∑ i ∈ Finset.univ.filter (fun i : Fin N => group i = g), y i)) + (∑ g : Fin H, ∑ i ∈ Finset.univ.filter (fun i : Fin N => group i = g), y i) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hsum2 : (∑ g : Fin H, 2 * forecast g * (∑ i ∈ Finset.univ.filter (fun i : Fin N => group i = g), y i)) = 2 * (∑ g : Fin H, forecast g * (∑ i ∈ Finset.univ.filter (fun i : Fin N => group i = g), y i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    ring
  have hSS : (∑ g : Fin H, ∑ i ∈ Finset.univ.filter (fun i : Fin N => group i = g), y i) = ∑ i : Fin N, y i :=
    (statopia_math_node_1457182788_f9803ee7 N H group y).symm
  have hTc : ∑ i : Fin N, (forecast (group i) - y i) ^ 2 = (∑ g : Fin H, ((Finset.univ.filter (fun i : Fin N => group i = g)).card : ℝ) * (forecast g) ^ 2) - 2 * (∑ g : Fin H, forecast g * (∑ i ∈ Finset.univ.filter (fun i : Fin N => group i = g), y i)) + (∑ i : Fin N, y i) := by
    rw [hT, hsum1, hsum2, hSS]
  rw [hTc]
  ring
  /- @proof-region region.target-node.session.378060b1d3ab010d end -/

end Msc62GroundTruth
