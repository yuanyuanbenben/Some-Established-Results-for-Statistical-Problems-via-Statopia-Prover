import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q40.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q40.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q40.Base

open Matrix

theorem extrinsic_sample_mean_on_unit_sphere
    (d n : ℕ) (hd : 2 ≤ d) (hn : 1 ≤ n)
    (x : Fin n → Fin d → ℝ)
    (hx : ∀ i, dotProduct (x i) (x i) = 1) :
    let xBar : Fin d → ℝ := (n : ℝ)⁻¹ • ∑ i, x i
    xBar ≠ 0 →
      let objective : (Fin d → ℝ) → ℝ := fun p ↦
        (n : ℝ)⁻¹ *
          ∑ i, dotProduct (x i - p) (x i - p)
      {p : Fin d → ℝ |
        dotProduct p p = 1 ∧
          ∀ q, dotProduct q q = 1 → objective p ≤ objective q} =
        {((Real.sqrt (dotProduct xBar xBar))⁻¹ : ℝ) • xBar}
:= by
  /- @proof-region region.root.99022f819e66 begin -/
  dsimp only
  intro hne
  ext p
  constructor
  · rintro ⟨hp, hmin⟩
    simp only [Set.mem_singleton_iff]
    exact statopia_math_node_646129307_86263361 d n hn x hx hne p hp hmin
  · intro hp
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    have hnn := statopia_math_node_3852170914_d7d89bd9 d ((n : ℝ)⁻¹ • ∑ i, x i) hne
    dsimp only at hnn
    obtain ⟨hs, hv1, hav⟩ := hnn
    refine ⟨hv1, ?_⟩
    intro q hq
    have e1 := statopia_math_node_3652586393_a25bccab d n hn x hx
      ((Real.sqrt (dotProduct ((n : ℝ)⁻¹ • ∑ i, x i) ((n : ℝ)⁻¹ • ∑ i, x i)))⁻¹ • ((n : ℝ)⁻¹ • ∑ i, x i))
    have e2 := statopia_math_node_3652586393_a25bccab d n hn x hx q
    have hb := statopia_math_node_2474807198_d38bf418 d ((n : ℝ)⁻¹ • ∑ i, x i) q hq
    linarith [e1, e2, hb, hv1, hq, hav]
  /- @proof-region region.root.99022f819e66 end -/
