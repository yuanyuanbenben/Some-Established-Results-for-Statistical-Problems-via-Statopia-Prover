import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q33.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q33.Base

open Msc62GroundTruth

namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_1747001620_9add0747 : ∀ (N H : ℕ)
    (group : Fin N → Fin H)
    (outcome : Fin N → Bool)
    (forecast : Fin H → ℝ)
    (h_nonempty :
      ∀ g : Fin H,
        (((Finset.univ.filter (fun i : Fin N => group i = g)).card : ℝ)) ≠ 0),
    let bit : Bool → ℝ := fun b => if b then 1 else 0
    let bin : Fin H → Finset (Fin N) :=
      fun g => Finset.univ.filter (fun i : Fin N => group i = g)
    let binSize : Fin H → ℝ := fun g => ((bin g).card : ℝ)
    let binSum : Fin H → ℝ := fun g => (bin g).sum (fun i => bit (outcome i))
    let reliability : ℝ :=
      ∑ g : Fin H, (binSize g / (N : ℝ)) * (forecast g - (1 / binSize g) * binSum g) ^ 2
    reliability = (1 / (N : ℝ)) * (∑ g : Fin H, binSize g * (forecast g) ^ 2)
        - (2 / (N : ℝ)) * (∑ g : Fin H, forecast g * binSum g)
        + (1 / (N : ℝ)) * (∑ g : Fin H, (binSum g) ^ 2 / binSize g) := by
  /- @proof-region region.target-node.session.a284b62e4a009f72 begin -/
  intro N H group outcome forecast h_nonempty
  dsimp only
  let n : Fin H → ℝ := fun g => ((Finset.univ.filter (fun i : Fin N => group i = g)).card : ℝ)
  let S : Fin H → ℝ :=
    fun g => (Finset.univ.filter (fun i : Fin N => group i = g)).sum (fun i => if outcome i then (1:ℝ) else 0)
  let f : Fin H → ℝ := forecast
  change (∑ g : Fin H, (n g / (N : ℝ)) * (f g - (1 / n g) * S g) ^ 2) =
      (1 / (N : ℝ)) * (∑ g : Fin H, n g * (f g) ^ 2)
        - (2 / (N : ℝ)) * (∑ g : Fin H, f g * S g)
        + (1 / (N : ℝ)) * (∑ g : Fin H, (S g) ^ 2 / n g)
  have hgen : ∀ g : Fin H, (n g / (N : ℝ)) * (f g - (1 / n g) * S g) ^ 2 =
      (1 / (N : ℝ)) * (n g * (f g) ^ 2) - (2 / (N : ℝ)) * (f g * S g) +
        (1 / (N : ℝ)) * ((S g) ^ 2 / n g) := by
    intro g
    have hg : n g ≠ 0 := h_nonempty g
    have h1 : n g * (f g - (1 / n g) * S g) ^ 2 = n g * (f g) ^ 2 - 2 * f g * S g + (S g) ^ 2 / n g := by
      field_simp
      ring
    calc (n g / (N : ℝ)) * (f g - (1 / n g) * S g) ^ 2
        = (1 / (N : ℝ)) * (n g * (f g - (1 / n g) * S g) ^ 2) := by ring
      _ = (1 / (N : ℝ)) * (n g * (f g) ^ 2 - 2 * f g * S g + (S g) ^ 2 / n g) := by rw [h1]
      _ = (1 / (N : ℝ)) * (n g * (f g) ^ 2) - (2 / (N : ℝ)) * (f g * S g) +
            (1 / (N : ℝ)) * ((S g) ^ 2 / n g) := by ring
  have hL : (∑ g : Fin H, (n g / (N : ℝ)) * (f g - (1 / n g) * S g) ^ 2) =
      ∑ g : Fin H, ((1 / (N : ℝ)) * (n g * (f g) ^ 2) - (2 / (N : ℝ)) * (f g * S g) +
        (1 / (N : ℝ)) * ((S g) ^ 2 / n g)) :=
    Finset.sum_congr rfl (fun g _ => hgen g)
  rw [hL]
  conv_rhs => simp only [Finset.mul_sum]
  conv_rhs => rw [← Finset.sum_sub_distrib]
  conv_rhs => rw [← Finset.sum_add_distrib]
  /- @proof-region region.target-node.session.a284b62e4a009f72 end -/

end Msc62GroundTruth
