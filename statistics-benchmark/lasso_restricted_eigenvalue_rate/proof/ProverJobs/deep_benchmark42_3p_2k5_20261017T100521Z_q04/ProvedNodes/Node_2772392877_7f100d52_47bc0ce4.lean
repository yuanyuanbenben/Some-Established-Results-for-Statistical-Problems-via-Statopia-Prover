import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q04.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q04.Base

open MeasureTheory ProbabilityTheory
open Msc62GroundTruth

open MeasureTheory ProbabilityTheory
namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_2772392877_7f100d52 : ∀ (m n : ℕ) (hm : 1 ≤ m)
    (X : Fin m → Fin n → ℝ)
    (sigmaHat : Matrix (Fin n) (Fin n) ℝ)
    (hSigmaHat : ∀ j k : Fin n,
      sigmaHat j k = (1 / (m : ℝ)) * ∑ i : Fin m, X i j * X i k)
    (S : Finset (Fin n))
    (kappa : ℝ) (hkappa : 0 < kappa)
    (hRE : ∀ v : Fin n → ℝ,
      (∑ j ∈ Finset.univ.filter (fun j => j ∉ S), |v j|) ≤
        3 * (∑ j ∈ S, |v j|) →
      kappa ^ 2 * (∑ j : Fin n, (v j) ^ 2) ≤
        ∑ j : Fin n, ∑ k : Fin n, v j * sigmaHat j k * v k)
    (h : Fin n → ℝ)
    (hcone : (∑ j ∈ Finset.univ.filter (fun j => j ∉ S), |h j|) ≤
      3 * (∑ j ∈ S, |h j|)),
    kappa ^ 2 * (∑ j : Fin n, (h j) ^ 2) ≤
      (1 / (m : ℝ)) * ∑ i : Fin m, (∑ j : Fin n, X i j * h j) ^ 2 := by
  /- @proof-region region.target-node.session.446d5ac0c87ac7fc begin -/
  intro m n hm X sigmaHat hSigmaHat S kappa hkappa hRE h hcone
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hmpos : (0:ℝ) < (m:ℝ) := by linarith
  have hmne : (m:ℝ) ≠ 0 := ne_of_gt hmpos
  have hmul : (m:ℝ) * (1 / (m:ℝ)) = 1 := by rw [one_div, mul_inv_cancel₀ hmne]
  have hmul' : (1 / (m:ℝ)) * (m:ℝ) = 1 := by rw [one_div, inv_mul_cancel₀ hmne]
  have hre := hRE h hcone
  have hsq : ∀ i : Fin m, (∑ j : Fin n, X i j * h j) ^ 2
      = ∑ j : Fin n, ∑ k : Fin n, X i j * X i k * h j * h k := by
    intro i
    rw [pow_two, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  have hgram' : ∀ j k : Fin n, (m:ℝ) * sigmaHat j k = ∑ i : Fin m, X i j * X i k := by
    intro j k
    rw [hSigmaHat j k, ← mul_assoc, hmul, one_mul]
  have hgram : ∀ j k : Fin n, (∑ i : Fin m, X i j * X i k) = (m:ℝ) * sigmaHat j k :=
    fun j k => (hgram' j k).symm
  have hjk : ∀ j k : Fin n, (∑ i : Fin m, X i j * X i k) * h j * h k
      = ∑ i : Fin m, X i j * X i k * h j * h k := by
    intro j k
    rw [Finset.sum_mul, Finset.sum_mul]
  have hcomm : ∑ i : Fin m, ∑ j : Fin n, ∑ k : Fin n, X i j * X i k * h j * h k
      = ∑ j : Fin n, ∑ k : Fin n, (∑ i : Fin m, X i j * X i k) * h j * h k := by
    calc ∑ i : Fin m, ∑ j : Fin n, ∑ k : Fin n, X i j * X i k * h j * h k
        = ∑ j : Fin n, ∑ i : Fin m, ∑ k : Fin n, X i j * X i k * h j * h k := by
            rw [Finset.sum_comm]
      _ = ∑ j : Fin n, ∑ k : Fin n, (∑ i : Fin m, X i j * X i k) * h j * h k := by
            refine Finset.sum_congr rfl (fun j _ => ?_)
            calc ∑ i : Fin m, ∑ k : Fin n, X i j * X i k * h j * h k
                = ∑ k : Fin n, ∑ i : Fin m, X i j * X i k * h j * h k := by
                    rw [Finset.sum_comm]
              _ = ∑ k : Fin n, (∑ i : Fin m, X i j * X i k) * h j * h k :=
                    Finset.sum_congr rfl (fun k _ => (hjk j k).symm)
  have hfinal : ∑ j : Fin n, ∑ k : Fin n, (∑ i : Fin m, X i j * X i k) * h j * h k
      = (m:ℝ) * ∑ j : Fin n, ∑ k : Fin n, h j * sigmaHat j k * h k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hgram j k]
    ring
  have hQ : (1 / (m:ℝ)) * ∑ i : Fin m, (∑ j : Fin n, X i j * h j) ^ 2
      = ∑ j : Fin n, ∑ k : Fin n, h j * sigmaHat j k * h k := by
    have hsum : ∑ i : Fin m, (∑ j : Fin n, X i j * h j) ^ 2
        = ∑ j : Fin n, ∑ k : Fin n, (∑ i : Fin m, X i j * X i k) * h j * h k := by
      calc ∑ i : Fin m, (∑ j : Fin n, X i j * h j) ^ 2
          = ∑ i : Fin m, ∑ j : Fin n, ∑ k : Fin n, X i j * X i k * h j * h k :=
              Finset.sum_congr rfl (fun i _ => hsq i)
        _ = ∑ j : Fin n, ∑ k : Fin n, (∑ i : Fin m, X i j * X i k) * h j * h k := hcomm
    rw [hsum, hfinal, ← mul_assoc, hmul', one_mul]
  rw [hQ]
  exact hre
  /- @proof-region region.target-node.session.446d5ac0c87ac7fc end -/

end Msc62GroundTruth
