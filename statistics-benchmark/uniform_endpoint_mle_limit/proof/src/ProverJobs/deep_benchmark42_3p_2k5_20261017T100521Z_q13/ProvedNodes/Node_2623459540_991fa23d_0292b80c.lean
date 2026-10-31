import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q13.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q13.Base

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

set_option autoImplicit false in
theorem statopia_math_node_2623459540_991fa23d : ∀ (f : BoundedContinuousFunction ℝ ℝ) (T ε : ℝ) (hT : 0 ≤ T) (heps : 0 < ε),
    ∃ (m : ℕ) (a c : ℕ → ℝ),
      1 ≤ m ∧ a 0 = -T ∧ a m = T ∧ Monotone a ∧
      (∀ x ∈ Set.Ioc (-T) T,
        ‖f x - ∑ j ∈ Finset.range m,
          (Set.Ioc (a j) (a (j + 1))).indicator (fun _ : ℝ => c j) x‖ ≤ ε) ∧
      (∀ x : ℝ,
        ‖∑ j ∈ Finset.range m,
          (Set.Ioc (a j) (a (j + 1))).indicator (fun _ : ℝ => c j) x‖ ≤ ‖f‖) ∧
      (∀ x : ℝ, x ∉ Set.Ioc (-T) T →
        ∑ j ∈ Finset.range m,
          (Set.Ioc (a j) (a (j + 1))).indicator (fun _ : ℝ => c j) x = 0) := by
  /- @proof-region region.target-node.session.5f1b35c538a5c77e begin -/
  intro f T ε hT heps
  rcases eq_or_lt_of_le hT with hT0 | hTpos
  · subst hT0
    refine ⟨1, fun _ => 0, fun _ => 0, by norm_num, by simp, by simp, fun _ _ _ => le_rfl, ?_, ?_, ?_⟩
    · rintro x hx
      exfalso
      linarith [hx.1, hx.2]
    · intro x
      simp
    · intro x _
      simp
  · have huc : UniformContinuousOn (⇑f) (Set.Icc (-T) T) :=
      isCompact_Icc.uniformContinuousOn_of_continuous (BoundedContinuousFunction.continuous f).continuousOn
    have hmod := Metric.uniformContinuousOn_iff.mp huc
    obtain ⟨δ, hδpos, hδ⟩ := hmod ε heps
    obtain ⟨n, hnδ⟩ := exists_nat_gt (2 * T / δ)
    have hqpos : (0:ℝ) < 2 * T / δ := by positivity
    have hnpos : (0:ℝ) < (n:ℝ) := lt_trans hqpos hnδ
    have hn1 : 1 ≤ n := by
      have hz : (0:ℝ) < (n:ℝ) := hnpos
      have hz' : 0 < n := by exact_mod_cast hz
      omega
    let h : ℝ := 2 * T / (n:ℝ)
    have hnne : (n:ℝ) ≠ 0 := ne_of_gt hnpos
    have hpos : 0 < h := by
      show (0:ℝ) < 2 * T / (n:ℝ)
      positivity
    have hlt : h < δ := by
      show 2 * T / (n:ℝ) < δ
      have h2 : 2 * T < (n:ℝ) * δ := by
        have h3 : 2 * T / δ < (n:ℝ) := hnδ
        rw [div_lt_iff₀ hδpos] at h3
        exact h3
      rw [div_lt_iff₀ hnpos, mul_comm δ (n:ℝ)]
      exact h2
    let a : ℕ → ℝ := fun j => -T + (j:ℝ) * h
    let c : ℕ → ℝ := fun j => f (a j)
    have ha0 : a 0 = -T := by
      show -T + ((0:ℕ):ℝ) * h = -T
      simp
    have han : a n = T := by
      have hc : (n:ℝ) * h = 2 * T := by
        show (n:ℝ) * (2 * T / (n:ℝ)) = 2 * T
        field_simp
      show -T + (n:ℝ) * h = T
      rw [hc]
      ring
    have hmono : Monotone a := by
      refine monotone_nat_of_le_succ (fun k => ?_)
      show -T + (k:ℝ) * h ≤ -T + ((k+1:ℕ):ℝ) * h
      push_cast
      nlinarith [hpos.le]
    have hmem : ∀ k ≤ n, a k ∈ Set.Icc (-T) T := by
      intro k hk
      exact ⟨by rw [← ha0]; exact hmono (Nat.zero_le k), by rw [← han]; exact hmono hk⟩
    have hkey : ∀ x ∈ Set.Ioc (-T) T, ∃ k < n,
        (∑ j ∈ Finset.range n,
          (Set.Ioc (a j) (a (j + 1))).indicator (fun _ : ℝ => c j) x) = c k ∧
        dist x (a k) < δ := by
      intro x hx
      obtain ⟨hxlow, hxup⟩ := hx
      have hne : ∃ j, x ≤ a (j + 1) :=
        ⟨n, le_trans hxup (by rw [← han]; exact hmono (Nat.le_succ n))⟩
      set k := Nat.find hne with hk
      have hkspec : x ≤ a (k + 1) := by rw [hk]; exact Nat.find_spec hne
      have hkmin : ∀ i < k, a (i + 1) < x := by
        intro i hi
        rw [hk] at hi
        exact not_le.mp (Nat.find_min hne hi)
      have hkn : k < n := by
        by_contra hcon
        have hnk : n ≤ k := Nat.le_of_not_lt hcon
        have hlt1 : n - 1 < k := by omega
        have h1 : a (n - 1 + 1) < x := hkmin (n - 1) hlt1
        rw [Nat.sub_add_cancel hn1, han] at h1
        linarith
      have hak : a k < x := by
        rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · rw [hk0, ha0]
          exact hxlow
        · have h1 : a (k - 1 + 1) < x := hkmin (k - 1) (by omega)
          rwa [Nat.sub_add_cancel hkpos] at h1
      have hgap : a (k + 1) - a k = h := by
        show -T + ((k + 1 : ℕ) : ℝ) * h - (-T + (k : ℝ) * h) = h
        push_cast
        ring
      have hxak : x - a k ≤ h := by linarith
      have hdist : dist x (a k) < δ := by
        rw [Real.dist_eq, abs_of_nonneg (by linarith : (0:ℝ) ≤ x - a k)]
        linarith
      have hxint : x ∈ Set.Ioc (a k) (a (k + 1)) := ⟨hak, hkspec⟩
      refine ⟨k, hkn, ?_, hdist⟩
      have hsingle : (∑ j ∈ Finset.range n,
            (Set.Ioc (a j) (a (j + 1))).indicator (fun _ : ℝ => c j) x)
          = (Set.Ioc (a k) (a (k + 1))).indicator (fun _ : ℝ => c k) x := by
        refine Finset.sum_eq_single (s := Finset.range n)
          (f := fun j => (Set.Ioc (a j) (a (j + 1))).indicator (fun _ : ℝ => c j) x) k ?_ ?_
        · intro j _ hjk
          have hmemj : x ∉ Set.Ioc (a j) (a (j + 1)) := by
            intro hxint'
            obtain ⟨h1, h2⟩ := hxint'
            rcases lt_or_gt_of_ne hjk with hlt' | hgt'
            · have h3 : a (j + 1) ≤ a k := hmono (by omega)
              linarith
            · have h3 : a (k + 1) ≤ a j := hmono (by omega)
              linarith
          exact Set.indicator_of_notMem hmemj _
        · intro hknot
          exact absurd (Finset.mem_range.mpr hkn) hknot
      rw [hsingle]
      exact Set.indicator_of_mem hxint (fun _ : ℝ => c k)

    have hzero : ∀ x : ℝ, x ∉ Set.Ioc (-T) T →
        (∑ j ∈ Finset.range n,
          (Set.Ioc (a j) (a (j + 1))).indicator (fun _ : ℝ => c j) x) = 0 := by
      intro x hx
      refine Finset.sum_eq_zero (fun j hj => ?_)
      have hjn : j < n := Finset.mem_range.mp hj
      have haj : -T ≤ a j := by rw [← ha0]; exact hmono (Nat.zero_le j)
      have haj1 : a (j + 1) ≤ T := by rw [← han]; exact hmono hjn
      have hmemj : x ∉ Set.Ioc (a j) (a (j + 1)) := by
        intro hxint
        obtain ⟨h1, h2⟩ := hxint
        exact hx ⟨by linarith, by linarith⟩
      exact Set.indicator_of_notMem hmemj _

    have hbnd : ∀ x : ℝ,
        ‖∑ j ∈ Finset.range n,
          (Set.Ioc (a j) (a (j + 1))).indicator (fun _ : ℝ => c j) x‖ ≤ ‖f‖ := by
      intro x
      by_cases hx : x ∈ Set.Ioc (-T) T
      · obtain ⟨k, _hkn, hsum, _hdist⟩ := hkey x hx
        rw [hsum]
        show ‖f (a k)‖ ≤ ‖f‖
        exact BoundedContinuousFunction.norm_coe_le_norm f (a k)
      · rw [hzero x hx]
        simp
    have hmain : ∀ x ∈ Set.Ioc (-T) T,
        ‖f x - ∑ j ∈ Finset.range n,
          (Set.Ioc (a j) (a (j + 1))).indicator (fun _ : ℝ => c j) x‖ ≤ ε := by
      intro x hx
      obtain ⟨k, hkn, hsum, hdist⟩ := hkey x hx
      have hxk : x ∈ Set.Icc (-T) T := ⟨hx.1.le, hx.2⟩
      have hak : a k ∈ Set.Icc (-T) T := hmem k hkn.le
      have hd := hδ x hxk (a k) hak hdist
      rw [dist_eq_norm] at hd
      rw [hsum]
      show ‖f x - f (a k)‖ ≤ ε
      linarith
    exact ⟨n, a, c, hn1, ha0, han, hmono, hmain, hbnd, hzero⟩

  /- @proof-region region.target-node.session.5f1b35c538a5c77e end -/
