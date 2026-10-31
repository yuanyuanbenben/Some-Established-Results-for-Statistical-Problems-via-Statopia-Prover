import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q33.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q33.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q33.Base

namespace Msc62GroundTruth

theorem brier_score_calibration_decomposition
    (N H : ℕ) (hN : 1 ≤ N) (hH : 1 ≤ H)
    (group : Fin N → Fin H)
    (forecast : Fin H → ℝ)
    (h_forecast_prob : ∀ g : Fin H, 0 ≤ forecast g ∧ forecast g ≤ 1)
    (outcome : Fin N → Bool)
    (h_nonempty :
      ∀ g : Fin H,
        0 < (Finset.univ.filter (fun i : Fin N => group i = g)).card) :
    let bit : Bool → ℝ := fun b => if b then 1 else 0
    let bin : Fin H → Finset (Fin N) :=
      fun g => Finset.univ.filter (fun i : Fin N => group i = g)
    let binSize : Fin H → ℝ := fun g => ((bin g).card : ℝ)
    let ybar : ℝ := (1 / (N : ℝ)) * ∑ i : Fin N, bit (outcome i)
    let ybarBin : Fin H → ℝ :=
      fun g => (1 / binSize g) * (bin g).sum (fun i => bit (outcome i))
    let weight : Fin H → ℝ := fun g => binSize g / (N : ℝ)
    let brier : ℝ :=
      (1 / (N : ℝ)) *
        ∑ i : Fin N, (forecast (group i) - bit (outcome i)) ^ 2
    let reliability : ℝ :=
      ∑ g : Fin H, weight g * (forecast g - ybarBin g) ^ 2
    let resolution : ℝ :=
      ∑ g : Fin H, weight g * (ybarBin g - ybar) ^ 2
    let uncertainty : ℝ := ybar * (1 - ybar)
    brier = reliability - resolution + uncertainty
:= by
  /- @proof-region region.root.def14fe751ed begin -/
  dsimp only
  have hNne : (N : ℝ) ≠ 0 := by
    have h : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hbin_ne : ∀ g : Fin H, ((Finset.univ.filter (fun i : Fin N => group i = g)).card : ℝ) ≠ 0 := by
    intro g
    have h : (0 : ℝ) < ((Finset.univ.filter (fun i : Fin N => group i = g)).card : ℝ) := by
      exact_mod_cast h_nonempty g
    linarith
  have hbrier := statopia_math_node_958340259_479a840d N H group outcome forecast hNne
  have hrel := statopia_math_node_1747001620_9add0747 N H group outcome forecast hbin_ne
  have hres := statopia_math_node_465308033_d7010796 N H hNne group outcome forecast hbin_ne
  dsimp only at hbrier hrel hres
  rw [hbrier, hrel, hres]
  ring
  /- @proof-region region.root.def14fe751ed end -/

end Msc62GroundTruth
