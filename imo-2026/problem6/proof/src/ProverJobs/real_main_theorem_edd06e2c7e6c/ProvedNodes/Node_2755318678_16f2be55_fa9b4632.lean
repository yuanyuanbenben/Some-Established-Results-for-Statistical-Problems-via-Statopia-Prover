import ProverJobs.real_main_theorem_edd06e2c7e6c.Vocabulary
import ProverJobs.real_main_theorem_edd06e2c7e6c.Base
import ProverJobs.real_main_theorem_edd06e2c7e6c.ProvedNodes.Node_1319170121_dbae7a97_29dbe775
import ProverJobs.real_main_theorem_edd06e2c7e6c.ProvedNodes.Node_3776635361_5eaf0306_47c63d95



set_option autoImplicit false in
theorem statopia_math_node_2755318678_16f2be55 : ∀ (a : ℕ → ℕ) (ha : IsValidSeq a)
    (x y : ℕ) (hx : 0 < x ∧ ∀ i : ℕ, 1 < Nat.gcd x (a i))
    (hy : 0 < y ∧ ∀ i : ℕ, 1 < Nat.gcd y (a i)),
    1 < Nat.gcd x y := by
  /- @proof-region region.target-node.session.b87527845b4033d0 begin -/
  intro a ha x y hx hy
  obtain ⟨_, _, _, _, _, _, hup, _⟩ := statopia_math_node_3776635361_5eaf0306 a ha
  by_contra hcon
  have hx1 : 1 ≤ x := by omega
  have hy1 : 1 ≤ y := by omega
  have hgpos : 0 < Nat.gcd x y := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left x y) hx.1
  have hgxy : Nat.gcd x y = 1 := by omega
  set z : ℕ := (1 + a 0 * y) * x with hz
  have hkpos : 0 < 1 + a 0 * y := by omega
  have hzpos : 0 < z := by
    rw [hz]
    exact Nat.mul_pos hkpos hx.1
  have hxdz : x ∣ z := by
    rw [hz]
    exact ⟨1 + a 0 * y, Nat.mul_comm (1 + a 0 * y) x⟩
  have hzge : a 0 ≤ z := by
    rw [hz]
    have hzexp : (1 + a 0 * y) * x = x + a 0 * y * x := by ring
    have h1 : a 0 * 1 ≤ a 0 * y := Nat.mul_le_mul_left (a 0) hy1
    have h2 : a 0 * y * 1 ≤ a 0 * y * x := Nat.mul_le_mul_left (a 0 * y) hx1
    omega
  have hgood_z : 0 < z ∧ ∀ i : ℕ, 1 < Nat.gcd z (a i) := hup x z hx hxdz hzpos
  obtain ⟨n, hn⟩ := (statopia_math_node_1319170121_dbae7a97 a ha z).mp ⟨hgood_z, hzge⟩
  have hcop : Nat.gcd y z = 1 := by
    have h1 : Nat.Coprime y x := by
      show Nat.gcd y x = 1
      rw [Nat.gcd_comm]
      exact hgxy
    have hzeq : z = x + (a 0 * x) * y := by
      rw [hz]
      ring
    rw [hzeq]
    exact (Nat.coprime_add_mul_right_right y x (a 0 * x)).mpr h1
  have hyn : 1 < Nat.gcd y z := by
    have h := hy.2 n
    rwa [← hn] at h
  omega
  /- @proof-region region.target-node.session.b87527845b4033d0 end -/
