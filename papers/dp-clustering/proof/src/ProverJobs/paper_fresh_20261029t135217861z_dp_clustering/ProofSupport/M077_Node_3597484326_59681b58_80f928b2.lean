import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M021_Vocabulary
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions

/- Original module ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProvedNodes.Node_3597484326_59681b58_80f928b2; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal
open Statlib.Imported

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_3597484326_59681b58 : ∀ (g : ℝ → ℝ) (c m M : ℝ) (hc : 0 < c) (hm : 0 < m)
    (hg_meas : Measurable g)
    (hg_bound : ∀ x ∈ Set.Icc (-c) c, m ≤ g x ∧ g x ≤ M)
    (hg_support : ∀ x : ℝ, x ∉ Set.Icc (-c) c → g x = 0)
    (t : ℕ) (P : Measure ℝ) (hP : IsProbabilityMeasure P)
    (p : Fin t → ℝ) (hp : ∀ j : Fin t, 0 < p j)
    (thetaStar : Fin t → ℝ)
    (hsep : ∀ j k : Fin t, j ≠ k → 2 * c < |thetaStar j - thetaStar k|)
    (Rm : Fin t → Measure ℝ)
    (hRm : ∀ j : Fin t,
      Rm j = volume.withDensity (fun x : ℝ => ENNReal.ofReal (g (x - thetaStar j))))
    (hP_eq : P = ∑ j : Fin t, ENNReal.ofReal (p j) • Rm j)
    (j : Fin t),
    (ENNReal.ofReal (p j * (m * (2 * c))) ≤
        P (Set.Icc (thetaStar j - c) (thetaStar j + c))) ∧
      (∀ u : ℝ, 0 ≤ u → u ≤ 2 * c →
        P (Set.Ioc (thetaStar j + c - u) (thetaStar j + c)) ≤
          ENNReal.ofReal (p j * (M * u))) := by
  /- @proof-region region.target-node.session.faa127614e83572b begin -/
  intro g c m M hc hm hg_meas hg_bound hg_support t P hP p hp thetaStar hsep Rm hRm hP_eq j
  have hdens_meas :
      ∀ k : Fin t, AEMeasurable (fun x : ℝ => ENNReal.ofReal (g (x - thetaStar k))) volume := by
    intro k
    measurability
  have hRm_apply : ∀ (k : Fin t) (E : Set ℝ), MeasurableSet E →
      Rm k E = ∫⁻ x in E, ENNReal.ofReal (g (x - thetaStar k)) ∂volume := by
    intro k E hE
    rw [hRm k]
    have h := MeasureTheory.setLIntegral_withDensity_eq_lintegral_mul₀
      (μ := volume) (f := fun x : ℝ => ENNReal.ofReal (g (x - thetaStar k)))
      (hdens_meas k) (g := fun _ => (1 : ENNReal)) aemeasurable_const (s := E) hE
    simpa [MeasureTheory.setLIntegral_const] using h
  have hP_apply : ∀ E : Set ℝ, P E = ∑ k : Fin t, ENNReal.ofReal (p k) * Rm k E := by
    intro E
    rw [hP_eq, Measure.finset_sum_apply]
    simp [Measure.smul_apply, smul_eq_mul]
  have hbound_mem : ∀ x ∈ Set.Icc (thetaStar j - c) (thetaStar j + c),
      x - thetaStar j ∈ Set.Icc (-c) c := by
    intro x hx
    rw [Set.mem_Icc] at hx ⊢
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hzero_pt : ∀ (k : Fin t), k ≠ j →
      ∀ x ∈ Set.Icc (thetaStar j - c) (thetaStar j + c), g (x - thetaStar k) = 0 := by
    intro k hk x hx
    rw [Set.mem_Icc] at hx
    have hxj : |x - thetaStar j| ≤ c := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    apply hg_support
    intro hmem
    rw [Set.mem_Icc] at hmem
    have hxk : |x - thetaStar k| ≤ c := abs_le.mpr hmem
    have h3 : |thetaStar j - thetaStar k| ≤ |x - thetaStar k| + |x - thetaStar j| := by
      have e : thetaStar j - thetaStar k = (thetaStar j - x) + (x - thetaStar k) := by ring
      calc |thetaStar j - thetaStar k| = |(thetaStar j - x) + (x - thetaStar k)| := by rw [e]
        _ ≤ |thetaStar j - x| + |x - thetaStar k| := abs_add_le _ _
        _ = |x - thetaStar j| + |x - thetaStar k| := by rw [abs_sub_comm]
        _ = |x - thetaStar k| + |x - thetaStar j| := by ring
    linarith [hsep j k (Ne.symm hk)]
  have hRm_zero : ∀ (k : Fin t), k ≠ j → ∀ (E : Set ℝ), MeasurableSet E →
      E ⊆ Set.Icc (thetaStar j - c) (thetaStar j + c) → Rm k E = 0 := by
    intro k hk E hE hsub
    rw [hRm_apply k E hE]
    have hpt : ∀ x : ℝ, E.indicator (fun y => ENNReal.ofReal (g (y - thetaStar k))) x = 0 := by
      intro x
      by_cases hx : x ∈ E
      · rw [Set.indicator_of_mem hx, hzero_pt k hk x (hsub hx)]
        exact ENNReal.ofReal_zero
      · rw [Set.indicator_of_notMem hx]
    rw [← MeasureTheory.lintegral_indicator hE]
    simp [hpt]
  have hP_le : ∀ E : Set ℝ, ENNReal.ofReal (p j) * Rm j E ≤ P E := by
    intro E
    rw [hP_apply E]
    rw [← Finset.insert_erase (Finset.mem_univ j), Finset.sum_insert (by simp)]
    calc ENNReal.ofReal (p j) * Rm j E
        = ENNReal.ofReal (p j) * Rm j E + 0 := (add_zero _).symm
      _ ≤ ENNReal.ofReal (p j) * Rm j E +
            (Finset.univ.erase j).sum (fun k => ENNReal.ofReal (p k) * Rm k E) :=
            add_le_add_right (zero_le _) _
  have hM_nonneg : 0 ≤ M := by
    have h0 : (0 : ℝ) ∈ Set.Icc (-c) c := by
      rw [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
    exact le_trans hm.le (le_trans (hg_bound 0 h0).1 (hg_bound 0 h0).2)
  constructor
  · have hI_meas : MeasurableSet (Set.Icc (thetaStar j - c) (thetaStar j + c)) :=
      measurableSet_Icc
    have hRmj :
        ENNReal.ofReal (m * (2 * c)) ≤ Rm j (Set.Icc (thetaStar j - c) (thetaStar j + c)) := by
      rw [hRm_apply j _ hI_meas]
      calc ENNReal.ofReal (m * (2 * c))
          = ENNReal.ofReal m * ENNReal.ofReal (2 * c) := ENNReal.ofReal_mul hm.le
        _ = ENNReal.ofReal m * volume (Set.Icc (thetaStar j - c) (thetaStar j + c)) := by
              rw [Real.volume_Icc, show (thetaStar j + c) - (thetaStar j - c) = 2 * c by ring]
        _ = ∫⁻ x in Set.Icc (thetaStar j - c) (thetaStar j + c), ENNReal.ofReal m ∂volume :=
              (MeasureTheory.setLIntegral_const _ _).symm
        _ ≤ ∫⁻ x in Set.Icc (thetaStar j - c) (thetaStar j + c),
              ENNReal.ofReal (g (x - thetaStar j)) ∂volume := by
              rw [← MeasureTheory.lintegral_indicator hI_meas (f := fun _ => ENNReal.ofReal m),
                ← MeasureTheory.lintegral_indicator hI_meas
                  (f := fun y => ENNReal.ofReal (g (y - thetaStar j)))]
              apply MeasureTheory.lintegral_mono
              intro x
              by_cases hx : x ∈ Set.Icc (thetaStar j - c) (thetaStar j + c)
              · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
                exact ENNReal.ofReal_le_ofReal (hg_bound _ (hbound_mem x hx)).1
              · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    calc ENNReal.ofReal (p j * (m * (2 * c)))
        = ENNReal.ofReal (p j) * ENNReal.ofReal (m * (2 * c)) := ENNReal.ofReal_mul (hp j).le
      _ ≤ ENNReal.ofReal (p j) * Rm j (Set.Icc (thetaStar j - c) (thetaStar j + c)) :=
            mul_le_mul_left' hRmj _
      _ ≤ P (Set.Icc (thetaStar j - c) (thetaStar j + c)) := hP_le _
  · intro u hu0 hu2c
    have huI_meas : MeasurableSet (Set.Ioc (thetaStar j + c - u) (thetaStar j + c)) :=
      measurableSet_Ioc
    have hsub : Set.Ioc (thetaStar j + c - u) (thetaStar j + c) ⊆
        Set.Icc (thetaStar j - c) (thetaStar j + c) := by
      intro x hx
      rw [Set.mem_Ioc] at hx
      rw [Set.mem_Icc]
      exact ⟨by linarith [hx.1, hu2c], by linarith [hx.2]⟩
    have hRmj_u : Rm j (Set.Ioc (thetaStar j + c - u) (thetaStar j + c)) ≤
        ENNReal.ofReal (M * u) := by
      rw [hRm_apply j _ huI_meas]
      calc ∫⁻ x in Set.Ioc (thetaStar j + c - u) (thetaStar j + c),
              ENNReal.ofReal (g (x - thetaStar j)) ∂volume
          ≤ ∫⁻ x in Set.Ioc (thetaStar j + c - u) (thetaStar j + c),
              ENNReal.ofReal M ∂volume := by
              rw [← MeasureTheory.lintegral_indicator huI_meas
                  (f := fun y => ENNReal.ofReal (g (y - thetaStar j))),
                ← MeasureTheory.lintegral_indicator huI_meas (f := fun _ => ENNReal.ofReal M)]
              apply MeasureTheory.lintegral_mono
              intro x
              by_cases hx : x ∈ Set.Ioc (thetaStar j + c - u) (thetaStar j + c)
              · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
                exact ENNReal.ofReal_le_ofReal (hg_bound _ (hbound_mem x (hsub hx))).2
              · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
        _ = ENNReal.ofReal M * volume (Set.Ioc (thetaStar j + c - u) (thetaStar j + c)) :=
              MeasureTheory.setLIntegral_const _ _
        _ = ENNReal.ofReal M * ENNReal.ofReal u := by
              rw [Real.volume_Ioc, show (thetaStar j + c) - (thetaStar j + c - u) = u by ring]
        _ = ENNReal.ofReal (M * u) := (ENNReal.ofReal_mul hM_nonneg).symm
    have hterm : ∀ k ∈ (Finset.univ : Finset (Fin t)).erase j,
        ENNReal.ofReal (p k) * Rm k (Set.Ioc (thetaStar j + c - u) (thetaStar j + c)) = 0 := by
      intro k hk
      rw [hRm_zero k (Finset.mem_erase.mp hk).1 _ huI_meas hsub, mul_zero]
    calc P (Set.Ioc (thetaStar j + c - u) (thetaStar j + c))
        = ENNReal.ofReal (p j) * Rm j (Set.Ioc (thetaStar j + c - u) (thetaStar j + c)) := by
            rw [hP_apply (Set.Ioc (thetaStar j + c - u) (thetaStar j + c)),
              ← Finset.insert_erase (Finset.mem_univ j),
              Finset.sum_insert (by simp),
              Finset.sum_eq_zero hterm, add_zero]
      _ ≤ ENNReal.ofReal (p j) * ENNReal.ofReal (M * u) := mul_le_mul_left' hRmj_u _
      _ = ENNReal.ofReal (p j * (M * u)) := (ENNReal.ofReal_mul (hp j).le).symm
  /- @proof-region region.target-node.session.faa127614e83572b end -/

end Statlib.Imported
end DPCompletedProof
