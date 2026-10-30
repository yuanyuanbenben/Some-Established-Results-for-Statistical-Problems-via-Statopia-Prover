import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q41.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q41.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q41.Base

open Matrix

theorem leading_principal_component
    (n d : ℕ) (hn : 1 ≤ n) (hd : 2 ≤ d)
    (x : Fin n → Fin d → ℝ)
    (hcenter : ∑ i, x i = 0)
    (v : Fin d → Fin d → ℝ)
    (lambda : Fin d → ℝ)
    (horth : ∀ j k, dotProduct (v j) (v k) = if j = k then 1 else 0)
    (hspan : Submodule.span ℝ (Set.range v) = ⊤) :
    let S : Matrix (Fin d) (Fin d) ℝ :=
      (n : ℝ)⁻¹ • ∑ i, vecMulVec (x i) (x i)
    let first : Fin d := ⟨0, by omega⟩
    (∀ j, S *ᵥ v j = lambda j • v j) →
    Antitone lambda →
    (∀ j, j ≠ first → lambda first > lambda j) →
      let objective : (Fin d → ℝ) → ℝ := fun u ↦
        (n : ℝ)⁻¹ * ∑ i, (dotProduct u (x i)) ^ 2
      {u : Fin d → ℝ |
        dotProduct u u = 1 ∧
          ∀ w, dotProduct w w = 1 → objective w ≤ objective u} =
        {-v first, v first}
:= by
  /- @proof-region region.root.8598d6f29bdc begin -/
  intro S first hE hAnti hg
  ext u
  simpa only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_empty_iff_false, or_false, or_comm]
    using statopia_math_node_1552826666_55d89ddc n d hn (by omega : 1 ≤ d) x v lambda first
      rfl horth hspan S rfl hE hg u
  /- @proof-region region.root.8598d6f29bdc end -/
