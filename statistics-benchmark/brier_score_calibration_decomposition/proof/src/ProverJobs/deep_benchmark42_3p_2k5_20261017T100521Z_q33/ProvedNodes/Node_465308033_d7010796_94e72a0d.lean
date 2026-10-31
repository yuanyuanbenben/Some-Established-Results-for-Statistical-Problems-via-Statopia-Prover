import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q33.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q33.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q33.ProvedNodes.Node_1457182788_f9803ee7_6f4b3769

open Msc62GroundTruth

namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_465308033_d7010796 : ∀ (N H : ℕ) (hN : (N : ℝ) ≠ 0)
    (group : Fin N → Fin H) (outcome : Fin N → Bool) (forecast : Fin H → ℝ)
    (h_bin_nonzero :
      ∀ g : Fin H,
        ((Finset.univ.filter (fun i : Fin N => group i = g)).card : ℝ) ≠ 0),
    let bit : Bool → ℝ := fun b => if b then (1 : ℝ) else 0
    let bin : Fin H → Finset (Fin N) :=
      fun g => Finset.univ.filter (fun i : Fin N => group i = g)
    let binSize : Fin H → ℝ := fun g => ((bin g).card : ℝ)
    let Sg : Fin H → ℝ := fun g => (bin g).sum (fun i => bit (outcome i))
    let ybar : ℝ := (1 / (N : ℝ)) * ∑ i : Fin N, bit (outcome i)
    let resolution : ℝ :=
      ∑ g : Fin H, (binSize g / (N : ℝ)) * ((1 / binSize g) * Sg g - ybar) ^ 2
    resolution = (1 / (N : ℝ)) * (∑ g : Fin H, (Sg g) ^ 2 / binSize g) - ybar ^ 2 := by
  /- @proof-region region.target-node.session.4228767270bf77ee begin -/
  intro N H hN group outcome forecast h_bin_nonzero
  dsimp only
  set y : Fin N → ℝ := fun i => if outcome i then (1 : ℝ) else 0 with hy
  set bs : Fin H → ℝ :=
    fun g => ((Finset.univ.filter (fun i : Fin N => group i = g)).card : ℝ) with hbs
  set Sg : Fin H → ℝ :=
    fun g => (Finset.univ.filter (fun i : Fin N => group i = g)).sum y with hSg
  set yb : ℝ := (1 / (N : ℝ)) * ∑ i : Fin N, y i with hyb
  have hbn : ∀ g : Fin H, bs g ≠ 0 := fun g => by
    simpa only [hbs] using h_bin_nonzero g
  have hpart1 : ∑ g : Fin H, bs g = (N : ℝ) := by
    have h := statopia_math_node_1457182788_f9803ee7 N H group (fun _ => (1 : ℝ))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
      hbs] at h ⊢
    exact h.symm
  have hpart2 : ∑ g : Fin H, Sg g = ∑ i : Fin N, y i := by
    have h := statopia_math_node_1457182788_f9803ee7 N H group y
    simp only [hSg] at h ⊢
    exact h.symm
  have hNN : (N : ℝ) * (1 / (N : ℝ)) = 1 := by field_simp
  have hsumS : ∑ g : Fin H, Sg g = (N : ℝ) * yb := by
    rw [hpart2, hyb, ← mul_assoc, hNN, one_mul]
  have hsumN : ∑ g : Fin H, bs g / (N : ℝ) = 1 := by
    rw [← Finset.sum_div, hpart1, div_self hN]
  have hterm : ∀ g : Fin H,
      bs g / (N : ℝ) * ((1 / bs g) * Sg g - yb) ^ 2
        = (1 / (N : ℝ)) * (Sg g ^ 2 / bs g) - (2 * yb / (N : ℝ)) * Sg g
          + yb ^ 2 * (bs g / (N : ℝ)) := by
    intro g
    have hg : bs g ≠ 0 := hbn g
    have hg2 : bs g ^ 2 ≠ 0 := pow_ne_zero 2 hg
    have hN2 : (N : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hN
    field_simp
    ring
  have hsplit : ∑ g : Fin H, bs g / (N : ℝ) * ((1 / bs g) * Sg g - yb) ^ 2
      = ∑ g : Fin H, ((1 / (N : ℝ)) * (Sg g ^ 2 / bs g) - (2 * yb / (N : ℝ)) * Sg g
          + yb ^ 2 * (bs g / (N : ℝ))) :=
    Finset.sum_congr rfl (fun g _ => hterm g)
  have hA : ∑ g : Fin H, (1 / (N : ℝ)) * (Sg g ^ 2 / bs g)
      = (1 / (N : ℝ)) * ∑ g : Fin H, Sg g ^ 2 / bs g :=
    (Finset.mul_sum Finset.univ (fun g : Fin H => Sg g ^ 2 / bs g) (1 / (N : ℝ))).symm
  have hB : ∑ g : Fin H, (2 * yb / (N : ℝ)) * Sg g
      = (2 * yb / (N : ℝ)) * ∑ g : Fin H, Sg g :=
    (Finset.mul_sum Finset.univ (fun g : Fin H => Sg g) (2 * yb / (N : ℝ))).symm
  have hC : ∑ g : Fin H, yb ^ 2 * (bs g / (N : ℝ))
      = yb ^ 2 * ∑ g : Fin H, bs g / (N : ℝ) :=
    (Finset.mul_sum Finset.univ (fun g : Fin H => bs g / (N : ℝ)) (yb ^ 2)).symm
  have h2 : (2 * yb / (N : ℝ)) * ((N : ℝ) * yb) = 2 * yb ^ 2 := by
    field_simp
  rw [hsplit, Finset.sum_add_distrib, Finset.sum_sub_distrib, hA, hB, hC, hsumS, hsumN,
    h2, mul_one]
  ring
  /- @proof-region region.target-node.session.4228767270bf77ee end -/

end Msc62GroundTruth
