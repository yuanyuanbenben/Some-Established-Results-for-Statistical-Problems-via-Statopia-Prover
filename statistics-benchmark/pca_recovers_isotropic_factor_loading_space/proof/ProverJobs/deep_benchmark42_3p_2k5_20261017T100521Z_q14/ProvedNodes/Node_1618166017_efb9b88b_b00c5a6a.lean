import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q14.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q14.Base

open MeasureTheory Matrix

open MeasureTheory Matrix

set_option autoImplicit false in
theorem statopia_math_node_1618166017_efb9b88b : ∀ (d q : ℕ) (f : Fin d → ℝ)
    (hanti : Antitone f) (hnonneg : ∀ j : Fin d, 0 ≤ f j)
    (hcard : q ≤ (Finset.univ.filter (fun j : Fin d => f j ≠ 0)).card),
    ∀ j : Fin d, j.val < q → 0 < f j := by
  /- @proof-region region.target-node.session.dcfe5de0eb8206cc begin -/
  intro d q f hanti hnonneg hcard j hj
  by_contra hcon
  rw [not_lt] at hcon
  have hfj : f j = 0 := le_antisymm hcon (hnonneg j)
  have hsub : Finset.univ.filter (fun k : Fin d => f k ≠ 0) ⊆ Finset.Iio j := by
    intro k hk
    have hk0 : f k ≠ 0 := by simpa using hk
    rw [Finset.mem_Iio]
    by_contra hlt
    have h1 : f k ≤ f j := hanti (not_lt.mp hlt)
    rw [hfj] at h1
    exact hk0 (le_antisymm h1 (hnonneg k))
  have hcardle : (Finset.univ.filter (fun k : Fin d => f k ≠ 0)).card ≤ (Finset.Iio j).card :=
    Finset.card_le_card hsub
  rw [Fin.card_Iio] at hcardle
  exact absurd (le_trans hcard hcardle) (not_le_of_gt hj)
  /- @proof-region region.target-node.session.dcfe5de0eb8206cc end -/
