import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M000_Vocabulary
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M001_Base

/- Original module ProverJobs.job_paper_dc88427b52844263b5321fc99eb582d8.ProvedNodes.Node_4208862229_4f2341a0_322e10ba; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported

open Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_4208862229_4f2341a0 : ∀ (c : ℝ) (g : ℝ → ℝ) (m θ p1 p2 : ℝ)
    (hc : 0 < c)
    (hm : 0 < m)
    (hg_meas : Measurable g)
    (hg_nonneg : ∀ x : ℝ, 0 ≤ g x)
    (hg_zero : ∀ x : ℝ, x ∉ Set.Icc (-c) c → g x = 0)
    (hg_lower : ∀ x ∈ Set.Icc (-c) c, m ≤ g x)
    (hg_int : ∫ (x : ℝ), g x ∂volume = 1)
    (h1 : |θ - p1| < 2 * c)
    (h2 : |θ - p2| < 2 * c)
    (hsep : 2 * c < |p1 - p2|),
    (∫ (x : ℝ) in Set.Icc (p1 - c) (p1 + c), g (x - θ) ∂volume)
        + (∫ (x : ℝ) in Set.Icc (p2 - c) (p2 + c), g (x - θ) ∂volume)
      ≤ 1 - m * (|p1 - p2| - 2 * c) := by
  /- @proof-region region.target-node.session.3e5a142f28c85193 begin -/
  intro c g m θ p1 p2 hc hm _ hg_nonneg hg_zero hg_lower hg_int h1 h2 h3
  have hgI : Integrable g volume := by
    by_contra hcon
    have h0 : ∫ (x : ℝ), g x ∂volume = 0 := MeasureTheory.integral_undef hcon
    rw [hg_int] at h0
    norm_num at h0
  have key : ∀ a b : ℝ, |θ - a| < 2 * c → |θ - b| < 2 * c → a ≤ b → 2 * c < b - a →
      (∫ x in Set.Icc (a - c) (a + c), g (x - θ) ∂volume)
        + (∫ x in Set.Icc (b - c) (b + c), g (x - θ) ∂volume)
      ≤ 1 - m * (b - a - 2 * c) := by
    intro a b hda hdb hab hlt
    have hig : ∀ s t : ℝ, s ≤ t → IntervalIntegrable g volume s t := by
      intro s t hst
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (f := g) (μ := volume) hst).2
        hgI.integrableOn
    have hif : ∀ s t : ℝ, s ≤ t → IntervalIntegrable (fun x => g (x - θ)) volume s t := by
      intro s t hst
      have h' := (hig (s - θ) (t - θ) (by linarith)).comp_sub_right θ
      rwa [sub_add_cancel, sub_add_cancel] at h'
    have hup : ∫ x in (a - c)..(b + c), g (x - θ) ≤ 1 := by
      have hsh : ∫ x in (a - c)..(b + c), g (x - θ) = ∫ x in (a - c) - θ..(b + c) - θ, g x :=
        intervalIntegral.integral_comp_sub_right (fun x => g x) θ
      rw [hsh, intervalIntegral.integral_of_le (by linarith)]
      have hbb := MeasureTheory.setIntegral_le_integral (μ := volume) (f := g)
        (s := Set.Ioc ((a - c) - θ) ((b + c) - θ)) hgI
        (Filter.Eventually.of_forall hg_nonneg)
      linarith [hbb, hg_int]
    have hgap : m * (b - a - 2 * c) ≤ ∫ x in (a + c)..(b - c), g (x - θ) := by
      have hle1 : a + c ≤ b - c := by linarith
      have hpt : ∀ x ∈ Set.Icc (a + c) (b - c), (fun _ => m) x ≤ g (x - θ) := by
        intro x hx
        have ha := abs_lt.1 hda
        have hb := abs_lt.1 hdb
        rw [Set.mem_Icc] at hx
        exact hg_lower (x - θ) (by
          rw [Set.mem_Icc]
          constructor <;> linarith [hx.1, hx.2, ha.1, ha.2, hb.1, hb.2])
      have hmono : ∫ x in (a + c)..(b - c), m ≤ ∫ x in (a + c)..(b - c), g (x - θ) :=
        intervalIntegral.integral_mono_on hle1 (intervalIntegral.intervalIntegrable_const (c := m))
          (hif (a + c) (b - c) (by linarith)) hpt
      have hconst : ∫ x in (a + c)..(b - c), m = (b - c - (a + c)) * m := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
      calc m * (b - a - 2 * c) = (b - c - (a + c)) * m := by ring
        _ = ∫ x in (a + c)..(b - c), m := hconst.symm
        _ ≤ ∫ x in (a + c)..(b - c), g (x - θ) := hmono
    have hsplit1 : (∫ x in (a - c)..(a + c), g (x - θ)) + ∫ x in (a + c)..(b + c), g (x - θ)
        = ∫ x in (a - c)..(b + c), g (x - θ) :=
      intervalIntegral.integral_add_adjacent_intervals (hif (a - c) (a + c) (by linarith))
        (hif (a + c) (b + c) (by linarith))
    have hsplit2 : (∫ x in (a + c)..(b - c), g (x - θ)) + ∫ x in (b - c)..(b + c), g (x - θ)
        = ∫ x in (a + c)..(b + c), g (x - θ) :=
      intervalIntegral.integral_add_adjacent_intervals (hif (a + c) (b - c) (by linarith))
        (hif (b - c) (b + c) (by linarith))
    have hW1 : ∫ x in Set.Icc (a - c) (a + c), g (x - θ) = ∫ x in (a - c)..(a + c), g (x - θ) := by
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc (μ := volume),
        intervalIntegral.integral_of_le (by linarith)]
    have hW2 : ∫ x in Set.Icc (b - c) (b + c), g (x - θ) = ∫ x in (b - c)..(b + c), g (x - θ) := by
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc (μ := volume),
        intervalIntegral.integral_of_le (by linarith)]
    rw [hW1, hW2]
    linarith [hsplit1, hsplit2, hup, hgap]
  rcases le_total p1 p2 with hle | hle
  · have hpa : |p1 - p2| = p2 - p1 := by
      rw [abs_of_nonpos (by linarith)]
      ring
    have hk := key p1 p2 h1 h2 hle (by rw [hpa] at h3; linarith)
    rw [hpa]
    exact hk
  · have hpa : |p1 - p2| = p1 - p2 := by
      rw [abs_of_nonneg (by linarith)]
    have hk := key p2 p1 h2 h1 hle (by rw [hpa] at h3; linarith)
    rw [hpa]
    linarith [hk]
  /- @proof-region region.target-node.session.3e5a142f28c85193 end -/

end

end Statlib.Imported
end DPCompletedProof
