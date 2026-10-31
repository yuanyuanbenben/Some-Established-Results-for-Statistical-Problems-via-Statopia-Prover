import ProverJobs.real_main_theorem_e7f39350f194.Vocabulary
import ProverJobs.real_main_theorem_e7f39350f194.MainSupport
import ProverJobs.real_main_theorem_e7f39350f194.Base

open EuclideanGeometry

theorem main_theorem
    (A B C K L O : Plane)
    
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    
    (M N : Plane) (hM : M = midpoint ℝ A B) (hN : N = midpoint ℝ A C)
    
    (hK : InsideTriangle B M C K)
    (hL : InsideTriangle B N C L)
    
    (hKangle : InsideAngle L B A K)
    (hLangle : InsideAngle A C K L)
    
    (h1 : ∠ K B A = ∠ A C L)
    (h2 : ∠ L B K = ∠ L N C)
    (h3 : ∠ L C K = ∠ B M K)
    
    (hO : IsCircumcentre A K L O) :
    dist O M = dist O N
:= by
  /- @proof-region region.root.7f04673fd438 begin -/
  have key : ∃ (s t : ℝ) (W : Plane) (rho2 : ℝ) (Q : Plane → ℝ),
      0 < s ∧ s < 1 ∧ 0 < t ∧ t < 1 ∧
      (∀ P : Plane, Q P = ‖P - W‖ ^ 2 - rho2) ∧
      Q A = 0 ∧ Q K = 0 ∧ Q L = 0 ∧
      Q B = dist A B ^ 2 * (1 - t) / 2 ∧
      Q C = dist A C ^ 2 * (1 - s) / 2 ∧
      dist A B ^ 2 * t = dist A C ^ 2 * s := by
    obtain ⟨s, t, u, v, hs, hs1, ht, ht1, hu, hu1, hv, hv1, hrest⟩ :=
      statopia_math_node_2572412618_fc84ca75 A B C K L hABC M N hM hN hK hL
    dsimp only at hrest
    obtain ⟨_, _, hKu, hLv, _⟩ := hrest
    have hE : dist A B ^ 2 * t = dist A C ^ 2 * s :=
      statopia_math_node_3691240324_1176a2cb A B C K L hABC M N hM hN hK hL
        s t u v hs hs1 ht ht1 hu hu1 hv hv1 (A + s • (C - A)) (A + t • (B - A))
        rfl rfl hKu hLv h1
    obtain ⟨U, r2, hA0, hK0, hL0, hB0, hC0⟩ :=
      statopia_math_node_1043730491_6ab9cbac A B C K L hABC M N hM hN hK hL hKangle hLangle
        h2 h3 s t u v hs hs1 ht ht1 hu hu1 hv hv1 (A + t • (B - A)) (A + s • (C - A))
        rfl rfl hKu hLv hE
    exact ⟨s, t, U, r2, fun P => ‖P - U‖ ^ 2 - r2, hs, hs1, ht, ht1,
      fun P => rfl, hA0, hK0, hL0, hB0, hC0, hE⟩
  obtain ⟨s, t, W, rho2, Q, hs, hs1, ht, ht1, hQ, hQA, hQK, hQL, hQB, hQC, hE⟩ := key
  obtain ⟨_, hQOB, hQOC⟩ :=
    statopia_math_node_2640265524_f2e3bdd6 A B C K L O hABC M N hM hN hK hL hKangle hO
      s t hs hs1 ht ht1 Q W rho2 hQ hQA hQK hQL hQB hQC
  have hmid := statopia_math_node_2602239205_e64b9839 A B C O M N hM hN
  have hval : (dist O B) ^ 2 - (dist O A) ^ 2 - ((dist O C) ^ 2 - (dist O A) ^ 2)
      = (dist A B ^ 2 - dist A C ^ 2) / 2 := by
    have ht' : dist A B ^ 2 * (1 - t) = dist A B ^ 2 - dist A B ^ 2 * t := by ring
    have hs' : dist A C ^ 2 * (1 - s) = dist A C ^ 2 - dist A C ^ 2 * s := by ring
    rw [hQOB, hQOC, ht', hs', hE]
    ring
  have hprod : (dist O M - dist O N) * (dist O M + dist O N) = 0 := by
    have hsq : (dist O M) ^ 2 = (dist O N) ^ 2 := by linarith
    nlinarith [hsq]
  rcases mul_eq_zero.mp hprod with h | h
  · linarith
  · have ha : (0 : ℝ) ≤ dist O M := dist_nonneg
    have hb : (0 : ℝ) ≤ dist O N := dist_nonneg
    linarith
  /- @proof-region region.root.7f04673fd438 end -/
