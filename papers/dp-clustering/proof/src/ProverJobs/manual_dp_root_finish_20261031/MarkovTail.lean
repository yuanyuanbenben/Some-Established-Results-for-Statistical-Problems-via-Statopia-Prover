import ProverJobs.manual_dp_root_finish_20261031.ConsMeasurability
open MeasureTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace OfflineDPConsGeneral

/-- Nonnegative-part expectation decay gives a tail bound without any free
probabilistic conclusion; this is the real-valued Markov step used below. -/
theorem tail_of_expectation {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : ℕ → X → ℝ) (hf : ∀ n, Measurable (f n))
    (hE : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (f n x) ∂μ) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => μ {x | ε < f n x}) atTop (𝓝 0) := by
  intro ε hε
  have he : ENNReal.ofReal ε ≠ 0 := (ENNReal.ofReal_pos.mpr hε).ne'
  have hlim := ENNReal.Tendsto.div_const hE (b := ENNReal.ofReal ε) (Or.inr he)
  simp only [ENNReal.zero_div] at hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le _)
  intro n
  apply (measure_mono (show {x | ε < f n x} ⊆ {x | ENNReal.ofReal ε ≤ ENNReal.ofReal (f n x)} from ?_)).trans
    (meas_ge_le_lintegral_div (hf n).ennreal_ofReal.aemeasurable he ENNReal.ofReal_ne_top)
  intro x hx
  exact ENNReal.ofReal_le_ofReal hx.le

end OfflineDPConsGeneral
#print axioms OfflineDPConsGeneral.tail_of_expectation
