import ProverJobs.job_paper_26cf7ed67549489c93e7ce6890ea6ef9.Vocabulary
import ProverJobs.job_paper_26cf7ed67549489c93e7ce6890ea6ef9.Base
import ProverJobs.job_paper_26cf7ed67549489c93e7ce6890ea6ef9.ProvedNodes.Node_424820995_9497e1fc_33b0e511

open scoped BigOperators
open Statlib.Imported

open scoped BigOperators
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_3049368524_c5ddb727 : ∀ (p : ℝ) (hp : 1 < p) (N : ℕ) (hN : 2 ≤ N),
    (∑ a ∈ Finset.Icc 1 (N - 1),
        ((N : ℝ) / ((a : ℝ) * ((N - a : ℕ) : ℝ))) ^ p)
      < Cp p := by
  /- @proof-region region.target-node.session.aa3ef3ff8e623c03 begin -/
  intro p hp N hN
  obtain ⟨-, -, -, hbound⟩ := statopia_math_node_424820995_9497e1fc p hp
  have key : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → (x + y) ^ p ≤ 2 ^ (p - 1) * (x ^ p + y ^ p) := by
    intro x y hx hy
    have h := NNReal.rpow_add_le_mul_rpow_add_rpow (⟨x, hx⟩ : NNReal) (⟨y, hy⟩ : NNReal) (le_of_lt hp)
    have h3 := NNReal.coe_le_coe.mpr h
    simpa using h3
  have hexp : ∀ a : ℕ, 0 < a → ((1 : ℝ) / (a : ℝ)) ^ p = 1 / (a : ℝ) ^ p := by
    intro a ha
    have h0 : (0 : ℝ) ≤ (a : ℝ) := by
      have h1 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
      linarith
    calc ((1 : ℝ) / (a : ℝ)) ^ p = ((a : ℝ)⁻¹) ^ p := by rw [one_div]
      _ = ((a : ℝ) ^ p)⁻¹ := Real.inv_rpow h0 p
      _ = 1 / (a : ℝ) ^ p := (one_div ((a : ℝ) ^ p)).symm
  have hbase : ∀ a ∈ Finset.Icc 1 (N - 1),
      (N : ℝ) / ((a : ℝ) * ((N - a : ℕ) : ℝ)) = 1 / (a : ℝ) + 1 / ((N - a : ℕ) : ℝ) := by
    intro a ha
    obtain ⟨ha1, ha2⟩ := Finset.mem_Icc.mp ha
    have hale : a ≤ N := by omega
    have hA : (a : ℝ) ≠ 0 := by
      have h1 : (0 : ℝ) < (a : ℝ) := by
        have h2 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha1
        linarith
      exact ne_of_gt h1
    have hB : ((N - a : ℕ) : ℝ) ≠ 0 := by
      have h1 : (0 : ℝ) < ((N - a : ℕ) : ℝ) := by
        have h2 : 0 < N - a := by omega
        exact_mod_cast h2
      exact ne_of_gt h1
    have hN' : (N : ℝ) = (a : ℝ) + ((N - a : ℕ) : ℝ) := by
      rw [Nat.cast_sub hale]; ring
    rw [hN']
    field_simp
    ring
  have hpoint : ∀ a ∈ Finset.Icc 1 (N - 1),
      ((N : ℝ) / ((a : ℝ) * ((N - a : ℕ) : ℝ))) ^ p
        ≤ 2 ^ (p - 1) * (1 / (a : ℝ) ^ p + 1 / ((N - a : ℕ) : ℝ) ^ p) := by
    intro a ha
    obtain ⟨ha1, ha2⟩ := Finset.mem_Icc.mp ha
    have hposa : 0 < a := by omega
    have hposb : 0 < N - a := by omega
    have hpa : (0 : ℝ) < (a : ℝ) := by exact_mod_cast hposa
    have hpb : (0 : ℝ) < ((N - a : ℕ) : ℝ) := by exact_mod_cast hposb
    have hA : (0 : ℝ) ≤ 1 / (a : ℝ) := div_nonneg (by norm_num) (le_of_lt hpa)
    have hB : (0 : ℝ) ≤ 1 / ((N - a : ℕ) : ℝ) := div_nonneg (by norm_num) (le_of_lt hpb)
    have hk := key (1 / (a : ℝ)) (1 / ((N - a : ℕ) : ℝ)) hA hB
    have e1 : ((1 : ℝ) / (a : ℝ)) ^ p = 1 / (a : ℝ) ^ p := hexp a hposa
    have e2 : ((1 : ℝ) / ((N - a : ℕ) : ℝ)) ^ p = 1 / ((N - a : ℕ) : ℝ) ^ p :=
      hexp (N - a) hposb
    rw [hbase a ha]
    calc (1 / (a : ℝ) + 1 / ((N - a : ℕ) : ℝ)) ^ p
        ≤ 2 ^ (p - 1) * ((1 / (a : ℝ)) ^ p + (1 / ((N - a : ℕ) : ℝ)) ^ p) := hk
      _ = 2 ^ (p - 1) * (1 / (a : ℝ) ^ p + 1 / ((N - a : ℕ) : ℝ) ^ p) := by rw [e1, e2]
  have hsum_le : (∑ a ∈ Finset.Icc 1 (N - 1),
        ((N : ℝ) / ((a : ℝ) * ((N - a : ℕ) : ℝ))) ^ p)
      ≤ 2 ^ (p - 1) * ((∑ a ∈ Finset.Icc 1 (N - 1), 1 / (a : ℝ) ^ p)
          + ∑ a ∈ Finset.Icc 1 (N - 1), 1 / ((N - a : ℕ) : ℝ) ^ p) := by
    have h1 : (∑ a ∈ Finset.Icc 1 (N - 1),
          ((N : ℝ) / ((a : ℝ) * ((N - a : ℕ) : ℝ))) ^ p)
        ≤ ∑ a ∈ Finset.Icc 1 (N - 1),
            2 ^ (p - 1) * (1 / (a : ℝ) ^ p + 1 / ((N - a : ℕ) : ℝ) ^ p) :=
      Finset.sum_le_sum hpoint
    have h2 : (∑ a ∈ Finset.Icc 1 (N - 1),
          2 ^ (p - 1) * (1 / (a : ℝ) ^ p + 1 / ((N - a : ℕ) : ℝ) ^ p))
        = 2 ^ (p - 1) * ((∑ a ∈ Finset.Icc 1 (N - 1), 1 / (a : ℝ) ^ p)
          + ∑ a ∈ Finset.Icc 1 (N - 1), 1 / ((N - a : ℕ) : ℝ) ^ p) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
    linarith
  have himage : (Finset.Icc 1 (N - 1)).image (fun a => N - a) = Finset.Icc 1 (N - 1) := by
    ext b
    simp only [Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨a, ⟨h1, h2⟩, rfl⟩
      omega
    · rintro ⟨h1, h2⟩
      exact ⟨N - b, ⟨by omega, by omega⟩, by omega⟩
  have hrefl : (∑ a ∈ Finset.Icc 1 (N - 1), 1 / ((N - a : ℕ) : ℝ) ^ p)
      = ∑ a ∈ Finset.Icc 1 (N - 1), 1 / (a : ℝ) ^ p := by
    have hinj : Set.InjOn (fun a : ℕ => N - a) (↑(Finset.Icc 1 (N - 1)) : Set ℕ) := by
      intro x hx y hy hxy
      simp only [Finset.mem_coe, Finset.mem_Icc] at hx hy
      have hxy' : N - x = N - y := hxy
      omega
    have h1 : (∑ a ∈ Finset.Icc 1 (N - 1), 1 / ((N - a : ℕ) : ℝ) ^ p)
        = ∑ b ∈ (Finset.Icc 1 (N - 1)).image (fun a => N - a), 1 / (b : ℝ) ^ p :=
      (Finset.sum_image (f := fun b : ℕ => 1 / (b : ℝ) ^ p) (g := fun a : ℕ => N - a) hinj).symm
    have h2 : (∑ b ∈ (Finset.Icc 1 (N - 1)).image (fun a => N - a), 1 / (b : ℝ) ^ p)
        = ∑ b ∈ Finset.Icc 1 (N - 1), 1 / (b : ℝ) ^ p := by rw [himage]
    exact h1.trans h2
  have hSζ : (∑ a ∈ Finset.Icc 1 (N - 1), 1 / (a : ℝ) ^ p) < zetaSeries p :=
    hbound (N - 1) (by omega)
  have h2p : (2 : ℝ) ^ p = 2 ^ (p - 1) * 2 := by
    have h := Real.rpow_add (x := (2 : ℝ)) (by norm_num : (0 : ℝ) < 2) (p - 1) 1
    rw [show p - 1 + 1 = p by ring] at h
    simpa using h
  calc (∑ a ∈ Finset.Icc 1 (N - 1),
        ((N : ℝ) / ((a : ℝ) * ((N - a : ℕ) : ℝ))) ^ p)
      ≤ 2 ^ (p - 1) * ((∑ a ∈ Finset.Icc 1 (N - 1), 1 / (a : ℝ) ^ p)
          + ∑ a ∈ Finset.Icc 1 (N - 1), 1 / ((N - a : ℕ) : ℝ) ^ p) := hsum_le
    _ = 2 ^ (p - 1) * ((∑ a ∈ Finset.Icc 1 (N - 1), 1 / (a : ℝ) ^ p)
          + ∑ a ∈ Finset.Icc 1 (N - 1), 1 / (a : ℝ) ^ p) := by rw [hrefl]
    _ = (2 ^ (p - 1) * 2) * (∑ a ∈ Finset.Icc 1 (N - 1), 1 / (a : ℝ) ^ p) := by ring
    _ < (2 ^ (p - 1) * 2) * zetaSeries p :=
        mul_lt_mul_of_pos_left hSζ (by
          have hc : (0 : ℝ) < 2 ^ (p - 1) := Real.rpow_pos_of_pos (by norm_num) (p - 1)
          linarith)
    _ = Cp p := by
        rw [← h2p]
        simp [Cp]
  /- @proof-region region.target-node.session.aa3ef3ff8e623c03 end -/

end Statlib.Imported
