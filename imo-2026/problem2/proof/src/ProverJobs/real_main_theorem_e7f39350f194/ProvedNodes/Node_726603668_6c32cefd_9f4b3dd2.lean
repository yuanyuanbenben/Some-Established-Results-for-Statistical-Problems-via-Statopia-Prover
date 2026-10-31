import ProverJobs.real_main_theorem_e7f39350f194.Vocabulary
import ProverJobs.real_main_theorem_e7f39350f194.Base

open EuclideanGeometry

open EuclideanGeometry

set_option autoImplicit false in
theorem statopia_math_node_726603668_6c32cefd : ∀ (A B C K L : Plane)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    (M N : Plane) (hM : M = midpoint ℝ A B) (hN : N = midpoint ℝ A C)
    (hK : InsideTriangle B M C K) (hL : InsideTriangle B N C L)
    (hKangle : InsideAngle L B A K)
    (s t u v : ℝ)
    (hs : 0 < s) (hs1 : s < 1) (ht : 0 < t) (ht1 : t < 1)
    (hu : 0 < u) (hu1 : u < 1) (hv : 0 < v) (hv1 : v < 1)
    (Y X : Plane)
    (hY : Y = A + s • (C - A)) (hX : X = A + t • (B - A))
    (hKtrace : K = B + u • (Y - B)) (hLtrace : L = C + v • (X - C))
    (h2 : ∠ L B Y = ∠ L N C),
    (1 - v) - (1 - v * t) * s > 0 := by
  /- @proof-region region.target-node.session.ba88bef9834916f6 begin -/
  intro A B C K L hABC M N hM hN hK hL hKangle s t u v hs hs1 ht ht1 hu hu1 hv hv1 Y X hY hX hKtrace hLtrace h2
  obtain ⟨s₁, t₁, hs₁, ht₁, hKexp⟩ := hKangle
  have hKB : K - B = u • (Y - B) := by simp [hKtrace]
  have hexp : u • (Y - B) = s₁ • (L - B) + t₁ • (A - B) := hKB ▸ hKexp
  have hLI : LinearIndependent ℝ ![B - A, C - A] := by
    by_contra hdep
    rw [LinearIndependent.pair_iff] at hdep
    push_neg at hdep
    obtain ⟨a, b, hab, hne⟩ := hdep
    have hdisj : a ≠ 0 ∨ b ≠ 0 := by
      by_cases ha0 : a = 0
      · exact Or.inr (hne ha0)
      · exact Or.inl ha0
    apply hABC
    unfold Collinear vectorSpan
    rcases hdisj with ha | hb
    · have hP : B - A = (a⁻¹ * (-b)) • (C - A) := by
        have h1 : a • (B - A) = (-b) • (C - A) := by
          have hz := congrArg (fun z : Plane => z - b • (C - A)) hab
          simpa using hz
        calc
          B - A = 1 • (B - A) := (one_smul ℝ (B - A)).symm
          _ = (a⁻¹ * a) • (B - A) := by rw [inv_mul_cancel₀ ha]
          _ = a⁻¹ • (a • (B - A)) := mul_smul a⁻¹ a (B - A)
          _ = a⁻¹ • ((-b) • (C - A)) := by rw [h1]
          _ = (a⁻¹ * (-b)) • (C - A) := (mul_smul a⁻¹ (-b) (C - A)).symm
      have hQmem : C - A ∈ Submodule.span ℝ ({C - A} : Set Plane) :=
        Submodule.subset_span (Set.mem_singleton _)
      have hPmem : B - A ∈ Submodule.span ℝ ({C - A} : Set Plane) := by
        rw [hP]
        exact Submodule.mem_span_singleton.mpr ⟨_, rfl⟩
      have hle : Submodule.span ℝ (({A, B, C} : Set Plane) -ᵥ ({A, B, C} : Set Plane))
          ≤ Submodule.span ℝ ({C - A} : Set Plane) := by
        rw [Submodule.span_le]
        intro x hx
        rw [Set.mem_vsub] at hx
        obtain ⟨p, hp, q, hq, rfl⟩ := hx
        have hpA : p - A ∈ Submodule.span ℝ ({C - A} : Set Plane) := by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
          rcases hp with rfl | rfl | rfl
          · simp
          · exact hPmem
          · exact hQmem
        have hqA : q - A ∈ Submodule.span ℝ ({C - A} : Set Plane) := by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
          rcases hq with rfl | rfl | rfl
          · simp
          · exact hPmem
          · exact hQmem
        have hpq : p -ᵥ q = (p - A) - (q - A) := by rw [vsub_eq_sub]; abel
        rw [hpq]
        obtain ⟨β, hβ⟩ := Submodule.mem_span_singleton.mp hpA
        obtain ⟨γ, hγ⟩ := Submodule.mem_span_singleton.mp hqA
        exact Submodule.mem_span_singleton.mpr ⟨β - γ, by rw [sub_smul, hβ, hγ]⟩
      have hrank : Module.rank ℝ ↥(Submodule.span ℝ ({C - A} : Set Plane)) ≤ 1 := by
        simpa using rank_span_le ({C - A} : Set Plane)
      exact le_trans (Submodule.rank_mono hle) hrank
    · have hP2 : C - A = (b⁻¹ * (-a)) • (B - A) := by
        have h1 : b • (C - A) = (-a) • (B - A) := by
          have hz := congrArg (fun z : Plane => z - a • (B - A)) hab
          simpa using hz
        calc
          C - A = 1 • (C - A) := (one_smul ℝ (C - A)).symm
          _ = (b⁻¹ * b) • (C - A) := by rw [inv_mul_cancel₀ hb]
          _ = b⁻¹ • (b • (C - A)) := mul_smul b⁻¹ b (C - A)
          _ = b⁻¹ • ((-a) • (B - A)) := by rw [h1]
          _ = (b⁻¹ * (-a)) • (B - A) := (mul_smul b⁻¹ (-a) (B - A)).symm
      have hBAmem : B - A ∈ Submodule.span ℝ ({B - A} : Set Plane) :=
        Submodule.subset_span (Set.mem_singleton _)
      have hCAmem : C - A ∈ Submodule.span ℝ ({B - A} : Set Plane) := by
        rw [hP2]
        exact Submodule.mem_span_singleton.mpr ⟨_, rfl⟩
      have hle2 : Submodule.span ℝ (({A, B, C} : Set Plane) -ᵥ ({A, B, C} : Set Plane))
          ≤ Submodule.span ℝ ({B - A} : Set Plane) := by
        rw [Submodule.span_le]
        intro x hx
        rw [Set.mem_vsub] at hx
        obtain ⟨p, hp, q, hq, rfl⟩ := hx
        have hpA : p - A ∈ Submodule.span ℝ ({B - A} : Set Plane) := by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
          rcases hp with rfl | rfl | rfl
          · simp
          · exact hBAmem
          · exact hCAmem
        have hqA : q - A ∈ Submodule.span ℝ ({B - A} : Set Plane) := by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
          rcases hq with rfl | rfl | rfl
          · simp
          · exact hBAmem
          · exact hCAmem
        have hpq : p -ᵥ q = (p - A) - (q - A) := by rw [vsub_eq_sub]; abel
        rw [hpq]
        obtain ⟨β, hβ⟩ := Submodule.mem_span_singleton.mp hpA
        obtain ⟨γ, hγ⟩ := Submodule.mem_span_singleton.mp hqA
        exact Submodule.mem_span_singleton.mpr ⟨β - γ, by rw [sub_smul, hβ, hγ]⟩
      have hrank2 : Module.rank ℝ ↥(Submodule.span ℝ ({B - A} : Set Plane)) ≤ 1 := by
        simpa using rank_span_le ({B - A} : Set Plane)
      exact le_trans (Submodule.rank_mono hle2) hrank2
  have key_eq : (-u - s₁ * (v * t - 1) + t₁) • (B - A) + (u * s - s₁ * (1 - v)) • (C - A)
      = u • (Y - B) - (s₁ • (L - B) + t₁ • (A - B)) := by
    simp only [hLtrace, hX, hY]
    module
  have hmain : (-u - s₁ * (v * t - 1) + t₁) • (B - A) + (u * s - s₁ * (1 - v)) • (C - A) = 0 := by
    rw [key_eq, hexp]
    simp
  have key := (LinearIndependent.pair_iff.mp hLI) (-u - s₁ * (v * t - 1) + t₁) (u * s - s₁ * (1 - v)) hmain
  have hv_pos : 0 < 1 - v := by linarith
  have hs₁_eq : s₁ * (1 - v) = u * s := by linarith [key.2]
  have ht₁_eq : t₁ = u + s₁ * (v * t - 1) := by linarith [key.1]
  have hscr : t₁ * (1 - v) = u * ((1 - v) + s * (v * t - 1)) := by
    rw [ht₁_eq]
    calc (u + s₁ * (v * t - 1)) * (1 - v)
        = u * (1 - v) + (s₁ * (1 - v)) * (v * t - 1) := by ring
      _ = u * (1 - v) + (u * s) * (v * t - 1) := by rw [hs₁_eq]
      _ = u * ((1 - v) + s * (v * t - 1)) := by ring
  have hpos_raw : 0 < (1 - v) + s * (v * t - 1) := by
    have hprod : 0 < t₁ * (1 - v) := mul_pos ht₁ hv_pos
    rw [hscr] at hprod
    exact pos_of_mul_pos_right hprod (le_of_lt hu)
  have hgoal_eq : (1 - v) - (1 - v * t) * s = (1 - v) + s * (v * t - 1) := by ring
  rw [hgoal_eq]
  exact hpos_raw
  /- @proof-region region.target-node.session.ba88bef9834916f6 end -/
