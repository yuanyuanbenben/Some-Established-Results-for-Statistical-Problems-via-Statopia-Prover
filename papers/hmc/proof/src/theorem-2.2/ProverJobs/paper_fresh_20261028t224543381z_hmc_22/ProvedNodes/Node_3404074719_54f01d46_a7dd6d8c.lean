import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.Vocabulary
import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.Base
import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.ProvedNodes.Node_1760066137_9d09a34f_f99c9d1e
import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.ProvedNodes.Node_2631634989_f6938273_03115d3b

namespace PaperProofTasks.paper_fresh_20261028t224543381z_hmc_22


open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open _root_.PaperProofTasks.paper_fresh_20261028t224543381z_hmc_22.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace Statlib.Imported


set_option autoImplicit false in
theorem statopia_math_node_3404074719_54f01d46 : ∀ (d : ℕ) (hd : 0 < d) (U : HMCState d → ℝ) (ε : ℝ) (hε : 0 < ε)
    (Ldist : Measure ℕ) [IsProbabilityMeasure Ldist]
    (hzero : ∀ x : HMCState d,
      (((gaussianMomentum d).prod (volume.restrict (Set.Icc (0 : ℝ) 1))).map
        (fun w : HMCState d × ℝ => hmcStep U ε 0 x w.1 w.2)) {x} = 1)
    (hself : ∀ (L : ℕ), 1 ≤ L → ∀ x : HMCState d,
      ENNReal.ofReal (∫ p, (1 - acceptProb U ε L (x, p)) ∂(gaussianMomentum d))
        ≤ (((gaussianMomentum d).prod (volume.restrict (Set.Icc (0 : ℝ) 1))).map
            (fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2)) {x})
    (hreject : ∀ (L : ℕ), 1 ≤ L → Ldist {L} ≠ 0 → ∀ δ : ℝ, 0 < δ → ∃ S : ℝ,
      ∀ x : HMCState d, S ≤ ‖x‖ →
        (1 - (∫ p, (1 - acceptProb U ε L (x, p)) ∂(gaussianMomentum d))) ≤ δ)
    (δ : ℝ) (hδ : 0 < δ),
    ∃ S : ℝ, ∀ x : HMCState d, S ≤ ‖x‖ →
      ENNReal.ofReal (1 - δ) ≤
        (∫⁻ L, (((gaussianMomentum d).prod (volume.restrict (Set.Icc (0 : ℝ) 1))).map
            (fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2)) {x} ∂Ldist) := by
  /- @proof-region region.target-node.session.56335931ac2cecd5 begin -/
  intro d hd U ε hε Ldist hLdist hzero hself hreject δ hδ
  classical
  by_cases hδ1 : (1:ℝ) ≤ δ
  · refine ⟨0, fun x _ => ?_⟩
    rw [ENNReal.ofReal_eq_zero.mpr (by linarith)]
    exact zero_le _
  have hhalf : (0:ℝ) < δ / 2 := by linarith
  have hslice : (0:ℝ) ≤ 1 - δ / 2 := by linarith
  have hbad : Ldist {L : ℕ | Ldist {L} = 0} = 0 := by
    have heq : {L : ℕ | Ldist {L} = 0} = ⋃ (L : {L : ℕ // Ldist {L} = 0}), ({L.1} : Set ℕ) := by
      ext L
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_singleton_iff]
      exact ⟨fun h => ⟨⟨L, h⟩, rfl⟩, fun h => by rcases h with ⟨⟨M, hM⟩, rfl⟩; exact hM⟩
    rw [heq]
    exact MeasureTheory.measure_iUnion_null (fun L => L.2)
  have hrange : ∃ n : ℕ, Ldist ((↑(Finset.range n) : Set ℕ))ᶜ ≤ ENNReal.ofReal (δ / 4) := by
    have hunion : (⋃ n, (↑(Finset.range n) : Set ℕ)) = Set.univ := by
      ext m
      constructor
      · intro _; exact Set.mem_univ m
      · intro _; rw [Set.mem_iUnion]; exact ⟨m + 1, by simp⟩
    have hmono : Monotone (fun n : ℕ => (↑(Finset.range n) : Set ℕ)) := by
      intro a b hab x hx
      simp only [Finset.mem_coe, Finset.mem_range] at hx ⊢
      omega
    have hsup : (⨆ n, Ldist ((↑(Finset.range n) : Set ℕ))) = 1 := by
      rw [← Monotone.measure_iUnion hmono, hunion, MeasureTheory.measure_univ]
    have hlt : ENNReal.ofReal (1 - δ / 4) < (1:ENNReal) := by
      rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
      linarith
    rw [← hsup] at hlt
    obtain ⟨n, hn⟩ := lt_iSup_iff.mp hlt
    exact ⟨n, by
      have hmeas : MeasurableSet (↑(Finset.range n) : Set ℕ) := (Finset.range n).finite_toSet.measurableSet
      have hsum : Ldist (↑(Finset.range n) : Set ℕ) + Ldist ((↑(Finset.range n) : Set ℕ))ᶜ = 1 := by
        rw [MeasureTheory.measure_add_measure_compl hmeas]
        exact MeasureTheory.measure_univ
      have hkey : ENNReal.ofReal (δ/4) + ENNReal.ofReal (1 - δ/4) = 1 := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith [not_le.mp hδ1]),
          show δ/4 + (1 - δ/4) = 1 by ring, ENNReal.ofReal_one]
      exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp (by
        calc Ldist ((↑(Finset.range n) : Set ℕ))ᶜ + ENNReal.ofReal (1 - δ/4)
            ≤ Ldist ((↑(Finset.range n) : Set ℕ))ᶜ + Ldist (↑(Finset.range n) : Set ℕ) := add_le_add le_rfl hn.le
          _ = 1 := by rw [add_comm]; exact hsum
          _ = ENNReal.ofReal (δ/4) + ENNReal.ofReal (1 - δ/4) := hkey.symm)⟩
  obtain ⟨n, hn⟩ := hrange
  let Fr : Finset ℕ := insert 0 ((Finset.range n).filter (fun L => Ldist {L} ≠ 0))
  have hFmeas : MeasurableSet (↑Fr : Set ℕ) := Fr.finite_toSet.measurableSet
  have hFcompl4 : Ldist (↑Fr : Set ℕ)ᶜ ≤ ENNReal.ofReal (δ / 4) := by
    have hsub : (↑Fr : Set ℕ)ᶜ ⊆ (↑(Finset.range n) : Set ℕ)ᶜ ∪ {L : ℕ | Ldist {L} = 0} := by
      intro L hL
      simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq] at hL ⊢
      by_cases hmem : L ∈ Finset.range n
      · right
        by_contra hne
        apply hL
        exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hmem, hne⟩))
      · left
        simpa using hmem
    calc Ldist (↑Fr : Set ℕ)ᶜ
        ≤ Ldist ((↑(Finset.range n) : Set ℕ)ᶜ ∪ {L : ℕ | Ldist {L} = 0}) := MeasureTheory.measure_mono hsub
      _ ≤ Ldist (↑(Finset.range n) : Set ℕ)ᶜ + Ldist {L : ℕ | Ldist {L} = 0} := MeasureTheory.measure_union_le _ _
      _ ≤ ENNReal.ofReal (δ / 4) := by simpa [hbad] using hn
  have hFcompl : Ldist (↑Fr : Set ℕ)ᶜ ≤ ENNReal.ofReal (δ / 2) := by
    refine le_trans hFcompl4 ?_
    rw [ENNReal.ofReal_le_ofReal_iff (by linarith)]
    linarith
  have hFne : Fr.Nonempty := ⟨0, Finset.mem_insert_self 0 _⟩
  have hthresh : ∀ L : ℕ, ∃ Sx : ℝ, L ∈ Fr → ∀ x : HMCState d, Sx ≤ ‖x‖ →
      (1 - δ/2) ≤ (if L = 0 then (1:ℝ) else ∫ p, (1 - acceptProb U ε L (x, p)) ∂(gaussianMomentum d)) := by
    intro L
    by_cases hL : L ∈ Fr
    · rw [Finset.mem_insert] at hL
      rcases hL with hL0 | hLf
      · subst hL0
        exact ⟨0, fun _ x _ => by rw [if_pos rfl]; linarith⟩
      · rw [Finset.mem_filter] at hLf
        obtain ⟨-, hw⟩ := hLf
        by_cases hL0' : L = 0
        · subst hL0'
          exact ⟨0, fun _ x _ => by rw [if_pos rfl]; linarith⟩
        · obtain ⟨Sx, hSx⟩ := hreject L (by omega) hw (δ / 2) hhalf
          exact ⟨Sx, fun _ x hx => by rw [if_neg hL0']; linarith [hSx x hx]⟩
    · exact ⟨0, fun hmem => absurd hmem hL⟩
  choose f hf using hthresh
  refine ⟨Fr.sup' hFne f, fun x hx => ?_⟩
  have hFs : ∀ L : ℕ, ENNReal.ofReal (if L = 0 then (1:ℝ) else ∫ p, (1 - acceptProb U ε L (x, p)) ∂(gaussianMomentum d))
      ≤ (((gaussianMomentum d).prod (volume.restrict (Set.Icc (0:ℝ) 1))).map (fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2)) {x} := by
    intro L
    rcases eq_or_ne L 0 with h | h
    · subst h
      rw [if_pos rfl, ENNReal.ofReal_one, hzero x]
    · rw [if_neg h]
      exact hself L (by omega) x
  have hgF : ∀ L ∈ Fr, ENNReal.ofReal (1 - δ/2) ≤ ENNReal.ofReal (if L = 0 then (1:ℝ) else ∫ p, (1 - acceptProb U ε L (x, p)) ∂(gaussianMomentum d)) := by
    intro L hL
    have hle1 : f L ≤ Fr.sup' hFne f := Finset.le_sup' f hL
    have hbound := hf L hL x (le_trans hle1 hx)
    exact ENNReal.ofReal_le_ofReal hbound
  have hle : ∫⁻ L, (↑Fr : Set ℕ).indicator (fun _ => ENNReal.ofReal (1 - δ/2)) L ∂Ldist
      ≤ ∫⁻ L, (((gaussianMomentum d).prod (volume.restrict (Set.Icc (0:ℝ) 1))).map (fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2)) {x} ∂Ldist := by
    apply lintegral_mono
    intro L
    by_cases hL : L ∈ (↑Fr : Set ℕ)
    · rw [Set.indicator_of_mem hL]
      exact le_trans (hgF L (by simpa using hL)) (hFs L)
    · have h0 : (↑Fr : Set ℕ).indicator (fun _ => ENNReal.ofReal (1 - δ/2)) L = 0 := by
        simp [hL]
      rw [h0]
      exact zero_le _
  have hind : ∫⁻ L, (↑Fr : Set ℕ).indicator (fun _ => ENNReal.ofReal (1 - δ/2)) L ∂Ldist
      = ENNReal.ofReal (1 - δ/2) * Ldist (↑Fr : Set ℕ) :=
    MeasureTheory.lintegral_indicator_const hFmeas (ENNReal.ofReal (1 - δ/2))
  have hFge : ENNReal.ofReal (1 - δ/2) ≤ Ldist (↑Fr : Set ℕ) := by
    have hsum : Ldist (↑Fr : Set ℕ) + Ldist ((↑Fr : Set ℕ))ᶜ = 1 := by
      rw [MeasureTheory.measure_add_measure_compl hFmeas]
      exact MeasureTheory.measure_univ
    have hne : Ldist ((↑Fr : Set ℕ))ᶜ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hFcompl
    have key : ENNReal.ofReal (1 - δ/2) + Ldist ((↑Fr : Set ℕ))ᶜ ≤ Ldist (↑Fr : Set ℕ) + Ldist ((↑Fr : Set ℕ))ᶜ := by
      rw [hsum]
      calc ENNReal.ofReal (1 - δ/2) + Ldist ((↑Fr : Set ℕ))ᶜ
          ≤ ENNReal.ofReal (1 - δ/2) + ENNReal.ofReal (δ/2) := add_le_add le_rfl hFcompl
        _ = ENNReal.ofReal ((1 - δ/2) + δ/2) := (ENNReal.ofReal_add hslice hhalf.le).symm
        _ = ENNReal.ofReal 1 := by rw [show (1 - δ/2) + δ/2 = 1 by ring]
        _ = 1 := ENNReal.ofReal_one
    exact (ENNReal.add_le_add_iff_right hne).mp key
  have hsq : ENNReal.ofReal (1 - δ) ≤ ENNReal.ofReal (1 - δ/2) * ENNReal.ofReal (1 - δ/2) := by
    rw [← ENNReal.ofReal_mul hslice]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [hδ.le, not_le.mp hδ1])
  calc ENNReal.ofReal (1 - δ)
      ≤ ENNReal.ofReal (1 - δ/2) * ENNReal.ofReal (1 - δ/2) := hsq
    _ ≤ ENNReal.ofReal (1 - δ/2) * Ldist (↑Fr : Set ℕ) := by gcongr
    _ = ∫⁻ L, (↑Fr : Set ℕ).indicator (fun _ => ENNReal.ofReal (1 - δ/2)) L ∂Ldist := hind.symm
    _ ≤ ∫⁻ L, (((gaussianMomentum d).prod (volume.restrict (Set.Icc (0:ℝ) 1))).map (fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2)) {x} ∂Ldist := hle
  /- @proof-region region.target-node.session.56335931ac2cecd5 end -/

end Statlib.Imported

end

