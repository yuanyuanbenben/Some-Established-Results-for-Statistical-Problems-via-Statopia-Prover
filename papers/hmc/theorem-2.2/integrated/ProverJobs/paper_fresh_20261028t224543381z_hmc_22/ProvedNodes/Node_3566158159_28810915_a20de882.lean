import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.Vocabulary
import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.Base

namespace PaperProofTasks.paper_fresh_20261028t224543381z_hmc_22

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open _root_.PaperProofTasks.paper_fresh_20261028t224543381z_hmc_22.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace Statlib.Imported
open _root_.Statlib

set_option autoImplicit false in
theorem statopia_math_node_3566158159_28810915 : ∀ (d : ℕ) (U : HMCState d → ℝ) (hU : Differentiable ℝ U)
    (eps : ℝ) (heps : 0 < eps) (L : ℕ)
    (B : Set (HMCState d)) (hB : MeasurableSet B),
    ∫⁻ (z : HMCState d × HMCState d),
        (Measure.restrict (volume : Measure ℝ) (Set.Icc (0 : ℝ) 1))
          {u : ℝ | (if Real.log u <
                      hamiltonian U z - hamiltonian U (leapfrogFlow U eps L z)
                    then leapfrogFlow U eps L z else z) ∈
              B ×ˢ (Set.univ : Set (HMCState d))}
        ∂((volume.prod volume : Measure (HMCState d × HMCState d)).withDensity
            (fun z => ENNReal.ofReal (Real.exp (-(hamiltonian U z)))))
      = ((volume.prod volume : Measure (HMCState d × HMCState d)).withDensity
            (fun z => ENNReal.ofReal (Real.exp (-(hamiltonian U z)))))
          (B ×ˢ (Set.univ : Set (HMCState d))) := by
  /- @proof-region region.target-node.session.deecda9cfd71d797 begin -/
  intro d U hU eps heps L D hD
  classical
  set Φ : HMCState d × HMCState d → HMCState d × HMCState d := leapfrogFlow U eps L with hΦ
  set R : HMCState d × HMCState d → HMCState d × HMCState d := fun z => (z.1, -z.2) with hR
  set Ψ : HMCState d × HMCState d → HMCState d × HMCState d := fun z => R (Φ z) with hΨ
  set f : HMCState d × HMCState d → ℝ≥0∞ :=
    fun z => ENNReal.ofReal (Real.exp (-(hamiltonian U z))) with hf
  set Λ : Measure (HMCState d × HMCState d) := volume.prod volume with hΛ
  set κ : Measure ℝ := Measure.restrict volume (Set.Icc (0 : ℝ) 1) with hκ
  have hgrad : Measurable (gradient U) := by
    have hfd : Measurable (fderiv ℝ U) := measurable_fderiv ℝ U
    exact (InnerProductSpace.toDual ℝ (HMCState d)).symm.continuous.measurable.comp hfd
  set K : HMCState d × HMCState d → HMCState d × HMCState d :=
    fun z => (z.1, z.2 - (eps / 2) • gradient U z.1) with hKdef
  set Dd : HMCState d × HMCState d → HMCState d × HMCState d :=
    fun z => (z.1 + eps • z.2, z.2) with hDdef
  have hKmeas : Measurable K := by
    rw [hKdef]
    measurability
  have hDmeas : Measurable Dd := by
    rw [hDdef]
    measurability
  have hstep_eq : leapfrogStep U eps = fun z => K (Dd (K z)) := by
    funext z
    obtain ⟨x, p⟩ := z
    simp only [hKdef, hDdef, leapfrogStep]
  have hstep_meas : Measurable (leapfrogStep U eps) := by
    rw [hstep_eq]
    exact hKmeas.comp (hDmeas.comp hKmeas)
  have hΦmeas : Measurable Φ := by
    rw [hΦ, leapfrogFlow]
    exact hstep_meas.iterate L
  have hshift_add : ∀ a : HMCState d,
      (volume : Measure (HMCState d)).map (fun p => p + a) = volume :=
    fun a => Measure.IsAddRightInvariant.map_add_right_eq_self a
  have hshift_sub : ∀ a : HMCState d,
      (volume : Measure (HMCState d)).map (fun p => p - a) = volume :=
    fun a => map_sub_right_eq_self ℙ a
  have hKinv : Λ.map K = Λ := by
    refine MeasureTheory.Measure.ext ?_
    intro s hs
    rw [Measure.map_apply hKmeas hs, hΛ]
    rw [Measure.prod_apply (s := K ⁻¹' s) (hs.preimage hKmeas)]
    rw [Measure.prod_apply hs]
    refine MeasureTheory.lintegral_congr fun x => ?_
    have hTx : MeasurableSet {q : HMCState d | (x, q) ∈ s} := by
      have hm : Measurable fun q : HMCState d => (x, q) := by measurability
      exact hs.preimage hm
    have hmp : Measurable fun p : HMCState d => p - (eps / 2) • gradient U x := by
      measurability
    have hpre : {p : HMCState d | (x, p - (eps / 2) • gradient U x) ∈ s}
        = (fun p : HMCState d => p - (eps / 2) • gradient U x) ⁻¹' {q | (x, q) ∈ s} := rfl
    have hsec : volume {p : HMCState d | (x, p - (eps / 2) • gradient U x) ∈ s}
        = volume {p : HMCState d | (x, p) ∈ s} := by
      rw [hpre, ← Measure.map_apply hmp hTx, hshift_sub ((eps / 2) • gradient U x)]
    exact hsec
  have hDinv : Λ.map Dd = Λ := by
    refine MeasureTheory.Measure.ext ?_
    intro s hs
    rw [Measure.map_apply hDmeas hs, hΛ]
    rw [Measure.prod_apply_symm (s := Dd ⁻¹' s) (hs.preimage hDmeas)]
    rw [Measure.prod_apply_symm hs]
    refine MeasureTheory.lintegral_congr fun p => ?_
    have hTp : MeasurableSet {y : HMCState d | (y, p) ∈ s} := by
      have hm : Measurable fun y : HMCState d => (y, p) := by measurability
      exact hs.preimage hm
    have hmp : Measurable fun x : HMCState d => x + eps • p := by measurability
    have hpre : {x : HMCState d | (x + eps • p, p) ∈ s}
        = (fun x : HMCState d => x + eps • p) ⁻¹' {y : HMCState d | (y, p) ∈ s} := rfl
    have hsec : volume {x : HMCState d | (x + eps • p, p) ∈ s}
        = volume {x : HMCState d | (x, p) ∈ s} := by
      rw [hpre, ← Measure.map_apply hmp hTp, hshift_add (eps • p)]
    exact hsec
  have hstep_inv : Λ.map (leapfrogStep U eps) = Λ := by
    rw [hstep_eq]
    rw [show (fun z => K (Dd (K z))) = K ∘ Dd ∘ K from rfl]
    rw [← Measure.map_map hKmeas (hDmeas.comp hKmeas)]
    rw [← Measure.map_map hDmeas hKmeas]
    rw [hKinv, hDinv, hKinv]
  have hΛΦ : Λ.map Φ = Λ := by
    have hL : ∀ n : ℕ, Λ.map ((leapfrogStep U eps)^[n]) = Λ := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [Function.iterate_succ']
          rw [← Measure.map_map hstep_meas (hstep_meas.iterate n)]
          rw [ih, hstep_inv]
    rw [hΦ, leapfrogFlow]
    exact hL L
  have hmneg : Measurable (fun p : HMCState d => -p) := continuous_neg.measurable
  have hneg : (volume : Measure (HMCState d)).map (fun p => -p) = volume := by simp
  have hR' : R = Prod.map (id : HMCState d → HMCState d) (fun p => -p) := rfl
  have hRmeas : Measurable R := by
    rw [hR']
    measurability
  have hΛR : Λ.map R = Λ := by
    rw [hΛ, hR', ← MeasureTheory.Measure.map_prod_map (volume : Measure (HMCState d))
      (volume : Measure (HMCState d)) measurable_id hmneg]
    simp only [Measure.map_id, hneg]
  have hΛΨ : Λ.map Ψ = Λ := by
    have hΨeq : Ψ = R ∘ Φ := rfl
    rw [hΨeq, ← Measure.map_map hRmeas hΦmeas, hΛΦ, hΛR]
  have hHR : ∀ z : HMCState d × HMCState d, hamiltonian U (R z) = hamiltonian U z := by
    intro z
    simp [hamiltonian, hR]
  have hstep_rev : ∀ y : HMCState d × HMCState d,
      leapfrogStep U eps (R (leapfrogStep U eps y)) = R y := by
    intro y
    obtain ⟨x, p⟩ := y
    set A : HMCState d := p - (eps / 2) • gradient U x with hA
    set x1 : HMCState d := x + eps • A with hx1
    set B : HMCState d := A - (eps / 2) • gradient U x1 with hB
    have hstep : leapfrogStep U eps (x, p) = (x1, B) := by
      simp only [leapfrogStep, ← hA, ← hx1, ← hB]
    have hB' : -B - (eps / 2) • gradient U x1 = -A := by
      rw [hB, neg_sub]
      abel
    have hx' : x1 + eps • (-B - (eps / 2) • gradient U x1) = x := by
      rw [hB', hx1, smul_neg]
      abel
    have h2 : -A - (eps / 2) • gradient U x = -p := by
      rw [hA, neg_sub]
      abel
    have hstep2 : leapfrogStep U eps (x1, -B) = (x, -p) := by
      simp only [leapfrogStep]
      rw [hx', hB', h2]
    rw [hstep]
    simp only [hR]
    exact hstep2
  have hΦRΦ : ∀ w : HMCState d × HMCState d, Φ (R (Φ w)) = R w := by
    have hgen : ∀ n : ℕ, ∀ w : HMCState d × HMCState d,
        (leapfrogStep U eps)^[n] (R ((leapfrogStep U eps)^[n] w)) = R w := by
      intro n
      induction n with
      | zero =>
          intro w
          simp
      | succ n ih =>
          intro w
          nth_rewrite 1 [Function.iterate_succ_apply]
          rw [Function.iterate_succ_apply', hstep_rev ((leapfrogStep U eps)^[n] w)]
          exact ih w
    intro w
    simpa only [hΦ, leapfrogFlow] using hgen L w
  have hinv : Function.Involutive Ψ := by
    intro w
    simp only [hΨ]
    rw [hΦRΦ w]
    simp [hR]
  have hκlog : ∀ c : ℝ,
      κ {u : ℝ | Real.log u < c} = ENNReal.ofReal (min 1 (Real.exp c)) := by
    intro c
    have hSm : MeasurableSet {u : ℝ | Real.log u < c} := Real.measurable_log measurableSet_Iio
    have hvol : κ {u : ℝ | Real.log u < c}
        = volume ({u : ℝ | Real.log u < c} ∩ Set.Icc (0 : ℝ) 1) := by
      rw [hκ]
      exact Measure.restrict_apply hSm
    rcases lt_trichotomy c 0 with hc | hc | hc
    · have hlt1 : Real.exp c < 1 := by
        have h := Real.exp_lt_exp.mpr hc
        rwa [Real.exp_zero] at h
      have hset : {u : ℝ | Real.log u < c} ∩ Set.Icc (0 : ℝ) 1
          = Set.Ioo (0 : ℝ) (Real.exp c) := by
        ext u
        constructor
        · intro hu
          obtain ⟨h1, h0, h2⟩ := hu
          have h1' : Real.log u < c := h1
          have hpos : 0 < u := by
            rcases lt_or_eq_of_le h0 with h | h
            · exact h
            · exfalso
              have hu0 : u = 0 := h.symm
              rw [hu0, Real.log_zero] at h1'
              exact absurd h1' (not_lt.mpr (le_of_lt hc))
          refine ⟨hpos, ?_⟩
          have hexp : Real.exp (Real.log u) < Real.exp c := Real.exp_lt_exp.mpr h1'
          rwa [Real.exp_log hpos] at hexp
        · intro hu
          obtain ⟨h1, h2⟩ := hu
          refine ⟨?_, le_of_lt h1, le_of_lt (lt_trans h2 hlt1)⟩
          have h3 := Real.log_lt_log h1 h2
          rwa [Real.log_exp] at h3
      rw [hvol, hset, Real.volume_Ioo]
      congr 1
      rw [min_eq_right (le_of_lt hlt1)]
      simp
    · subst hc
      have hset : {u : ℝ | Real.log u < 0} ∩ Set.Icc (0 : ℝ) 1 = Set.Ioo (0 : ℝ) 1 := by
        ext u
        constructor
        · intro hu
          obtain ⟨h1, h0, h2⟩ := hu
          have h1' : Real.log u < 0 := h1
          have hpos : 0 < u := by
            rcases lt_or_eq_of_le h0 with h | h
            · exact h
            · exfalso
              have hu0 : u = 0 := h.symm
              rw [hu0, Real.log_zero] at h1'
              exact lt_irrefl 0 h1'
          refine ⟨hpos, ?_⟩
          have hexp : Real.exp (Real.log u) < 1 := by
            have h := Real.exp_lt_exp.mpr h1'
            rwa [Real.exp_zero] at h
          rwa [Real.exp_log hpos] at hexp
        · intro hu
          obtain ⟨h1, h2⟩ := hu
          refine ⟨?_, le_of_lt h1, le_of_lt h2⟩
          have h3 := Real.log_lt_log h1 h2
          rwa [Real.log_one] at h3
      rw [hvol, hset, Real.volume_Ioo]
      congr 1
      simp
    · have hone : (1 : ℝ) < Real.exp c := by
        have h := Real.exp_lt_exp.mpr hc
        rwa [Real.exp_zero] at h
      have hset : {u : ℝ | Real.log u < c} ∩ Set.Icc (0 : ℝ) 1 = Set.Icc (0 : ℝ) 1 := by
        refine Set.inter_eq_right.2 ?_
        intro u hu
        obtain ⟨h0, h1⟩ := hu
        have h1' : Real.log u < c := by
          rcases eq_or_lt_of_le h0 with h | h
          · have hu0 : u = 0 := h.symm
            rw [hu0, Real.log_zero]
            exact hc
          · have h3 := Real.log_lt_log h (lt_of_le_of_lt h1 hone)
            rwa [Real.log_exp] at h3
        exact h1'
      rw [hvol, hset, Real.volume_Icc]
      congr 1
      rw [min_eq_left (le_of_lt hone)]
      simp
  have hακ : ∀ z : HMCState d × HMCState d,
      κ {u : ℝ | Real.log u < hamiltonian U z - hamiltonian U (Φ z)}
        = ENNReal.ofReal (min 1 (Real.exp (hamiltonian U z - hamiltonian U (Φ z)))) :=
    fun z => hκlog _
  have hmain : ∫⁻ z, κ {u : ℝ |
        (if Real.log u < hamiltonian U z - hamiltonian U (Φ z) then Φ z else z) ∈
          D ×ˢ (Set.univ : Set (HMCState d))} ∂Λ.withDensity f
      = Λ.withDensity f (D ×ˢ (Set.univ : Set (HMCState d))) := by
    set C : Set (HMCState d × HMCState d) := D ×ˢ (Set.univ : Set (HMCState d)) with hC
    set α : HMCState d × HMCState d → ℝ :=
      fun z => min 1 (Real.exp (hamiltonian U z - hamiltonian U (Φ z))) with hα
    have hUmeas : Measurable U := hU.continuous.measurable
    have hHmeas : Measurable fun z : HMCState d × HMCState d => hamiltonian U z := by
      have h2 : Measurable fun z : HMCState d × HMCState d => ‖z.2‖ ^ 2 := by measurability
      exact (hUmeas.comp measurable_fst).add (measurable_const.mul h2)
    have hHΦmeas : Measurable fun z : HMCState d × HMCState d => hamiltonian U (Φ z) :=
      hHmeas.comp hΦmeas
    have hαmeas : Measurable α := by
      rw [hα]
      exact measurable_const.min (Real.measurable_exp.comp (hHmeas.sub hHΦmeas))
    have hofα : Measurable fun z : HMCState d × HMCState d => ENNReal.ofReal (α z) :=
      ENNReal.measurable_ofReal.comp hαmeas
    have hfmeas : Measurable f := by
      rw [hf]
      exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hHmeas.neg)
    have hCmeas : MeasurableSet C := by
      rw [hC]
      exact hD.prod MeasurableSet.univ
    have hΦpre : MeasurableSet (Φ ⁻¹' C) := hCmeas.preimage hΦmeas
    have hΨmeas : Measurable Ψ := by
      rw [hΨ]
      exact hRmeas.comp hΦmeas
    have hκuniv : κ (Set.univ) = 1 := by
      rw [hκ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
      norm_num
    have hSmeas : ∀ z : HMCState d × HMCState d,
        MeasurableSet {u : ℝ | Real.log u < hamiltonian U z - hamiltonian U (Φ z)} :=
      fun z => Real.measurable_log measurableSet_Iio
    have hκSmeas : Measurable fun z : HMCState d × HMCState d =>
        κ {u : ℝ | Real.log u < hamiltonian U z - hamiltonian U (Φ z)} := by
      have hl : Measurable fun p : (HMCState d × HMCState d) × ℝ => Real.log p.2 :=
        Real.measurable_log.comp measurable_snd
      have hc : Measurable fun p : (HMCState d × HMCState d) × ℝ =>
          hamiltonian U p.1 - hamiltonian U (Φ p.1) :=
        (hHmeas.comp measurable_fst).sub (hHΦmeas.comp measurable_fst)
      exact measurable_measure_prodMk_left (measurableSet_lt hl hc)
    have hcompl : ∀ z : HMCState d × HMCState d,
        κ {u : ℝ | Real.log u < hamiltonian U z - hamiltonian U (Φ z)}ᶜ
          = 1 - ENNReal.ofReal (α z) := by
      intro z
      have hfin : κ {u : ℝ | Real.log u < hamiltonian U z - hamiltonian U (Φ z)} ≠ ⊤ := by
        rw [hακ z]
        exact ENNReal.ofReal_ne_top
      have h := MeasureTheory.measure_compl (μ := κ) (hSmeas z) hfin
      rwa [hκuniv, hακ z] at h
    have hsplit : ∀ z : HMCState d × HMCState d,
        κ {u : ℝ | (if Real.log u < hamiltonian U z - hamiltonian U (Φ z) then Φ z else z) ∈ C}
          = (if (Φ z) ∈ C then ENNReal.ofReal (α z) else 0)
            + (if z ∈ C then κ {u : ℝ | Real.log u < hamiltonian U z - hamiltonian U (Φ z)}ᶜ
              else 0) := by
      intro z
      by_cases h2 : (Φ z) ∈ C
      · by_cases h3 : z ∈ C
        · have hset : {u : ℝ | (if Real.log u < hamiltonian U z - hamiltonian U (Φ z) then Φ z else z) ∈ C}
              = Set.univ := by
            ext u
            by_cases h1 : Real.log u < hamiltonian U z - hamiltonian U (Φ z)
            · simp [h1, h2]
            · simp [h1, h3]
          rw [hset, if_pos h2, if_pos h3, hκuniv, ← hακ z, ← hκuniv]
          exact (MeasureTheory.measure_add_measure_compl (hSmeas z)).symm
        · have hset : {u : ℝ | (if Real.log u < hamiltonian U z - hamiltonian U (Φ z) then Φ z else z) ∈ C}
              = {u : ℝ | Real.log u < hamiltonian U z - hamiltonian U (Φ z)} := by
            ext u
            by_cases h1 : Real.log u < hamiltonian U z - hamiltonian U (Φ z)
            · simp [h1, h2]
            · simp [h1, h3]
          rw [hset, if_pos h2, if_neg h3, add_zero, hακ z]
      · by_cases h3 : z ∈ C
        · have hset : {u : ℝ | (if Real.log u < hamiltonian U z - hamiltonian U (Φ z) then Φ z else z) ∈ C}
              = {u : ℝ | Real.log u < hamiltonian U z - hamiltonian U (Φ z)}ᶜ := by
            ext u
            by_cases h1 : Real.log u < hamiltonian U z - hamiltonian U (Φ z)
            · simp [h1, h2]
            · simp [h1, h3]
          rw [hset, if_neg h2, if_pos h3, zero_add]
        · have hset : {u : ℝ | (if Real.log u < hamiltonian U z - hamiltonian U (Φ z) then Φ z else z) ∈ C}
              = ∅ := by
            ext u
            by_cases h1 : Real.log u < hamiltonian U z - hamiltonian U (Φ z)
            · simp [h1, h2]
            · simp [h1, h3]
          rw [hset, if_neg h2, if_neg h3, MeasureTheory.measure_empty, add_zero]
    have hsplit' : ∀ z : HMCState d × HMCState d,
        κ {u : ℝ | (if Real.log u < hamiltonian U z - hamiltonian U (Φ z) then Φ z else z) ∈ C}
          = (if (Φ z) ∈ C then ENNReal.ofReal (α z) else 0)
            + (if z ∈ C then 1 - ENNReal.ofReal (α z) else 0) := by
      intro z
      rw [hsplit z, hcompl z]
    have hsplit_meas : AEMeasurable (fun z : HMCState d × HMCState d =>
        (if (Φ z) ∈ C then ENNReal.ofReal (α z) else 0)
          + (if z ∈ C then 1 - ENNReal.ofReal (α z) else 0)) Λ :=
      (Measurable.add (Measurable.ite hΦpre hofα measurable_const)
        (Measurable.ite hCmeas (measurable_const.sub hofα) measurable_const)).aemeasurable
    have hpreC : Φ ⁻¹' C = Ψ ⁻¹' C := by
      ext z
      simp only [Set.mem_preimage, hC, Set.mem_prod, Set.mem_univ, and_true]
      rw [show (Ψ z).1 = (Φ z).1 from rfl]
    have hchar : ∀ (A : Set (HMCState d × HMCState d)) (g : HMCState d × HMCState d → ℝ≥0∞),
        MeasurableSet A → Measurable g →
        ∫⁻ z in Ψ ⁻¹' A, g z ∂Λ = ∫⁻ z in A, g (Ψ z) ∂Λ := by
      intro A g hA hg
      rw [← MeasureTheory.lintegral_indicator (hA.preimage hΨmeas) g]
      have hp : ∀ z, (Ψ ⁻¹' A).indicator g z = A.indicator (fun z => g (Ψ z)) (Ψ z) := by
        intro z
        by_cases h : Ψ z ∈ A
        · simp [Set.indicator, h]
          exact (congrArg g (hinv z)).symm
        · simp [Set.indicator, h]
      rw [show (fun z => (Ψ ⁻¹' A).indicator g z)
            = (fun z => A.indicator (fun z => g (Ψ z)) (Ψ z)) from funext hp]
      have hFL : Measurable (A.indicator (fun z => g (Ψ z))) :=
        Measurable.indicator (hg.comp hΨmeas) hA
      rw [← MeasureTheory.lintegral_map hFL hΨmeas, hΛΨ]
      rw [MeasureTheory.lintegral_indicator hA (fun z => g (Ψ z))]
    have hsym_pt : ∀ w : HMCState d × HMCState d,
        f (Ψ w) * ENNReal.ofReal (α (Ψ w)) = f w * ENNReal.ofReal (α w) := by
      intro w
      have hHΨ : hamiltonian U (Ψ w) = hamiltonian U (Φ w) := by
        rw [hΨ]
        exact hHR (Φ w)
      have hΦΨ : hamiltonian U (Φ (Ψ w)) = hamiltonian U w := by
        rw [hΦRΦ w]
        exact hHR w
      have key : ∀ p q : ℝ, 0 < p → p * min 1 (Real.exp q) = min p (p * Real.exp q) := by
        intro p q hp
        rcases le_total (Real.exp q) 1 with h | h
        · have hle : p * Real.exp q ≤ p := by
            simpa using mul_le_mul_of_nonneg_left h hp.le
          rw [min_eq_right h, min_eq_right hle]
        · have hle : p ≤ p * Real.exp q := le_mul_of_one_le_right hp.le h
          rw [min_eq_left h, min_eq_left hle, mul_one]
      have eL : f (Ψ w) * ENNReal.ofReal (α (Ψ w))
          = ENNReal.ofReal (min (Real.exp (-(hamiltonian U (Φ w)))) (Real.exp (-(hamiltonian U w)))) := by
        have hkey : Real.exp (-(hamiltonian U (Φ w))) * α (Ψ w)
            = min (Real.exp (-(hamiltonian U (Φ w)))) (Real.exp (-(hamiltonian U w))) := by
          have hexp : α (Ψ w)
              = min 1 (Real.exp (hamiltonian U (Φ w) - hamiltonian U w)) := by
            show min 1 (Real.exp (hamiltonian U (Ψ w) - hamiltonian U (Φ (Ψ w))))
              = min 1 (Real.exp (hamiltonian U (Φ w) - hamiltonian U w))
            rw [hHΨ, hΦΨ]
          rw [hexp,
            key (Real.exp (-(hamiltonian U (Φ w)))) (hamiltonian U (Φ w) - hamiltonian U w)
              (Real.exp_pos _),
            ← Real.exp_add,
            show -(hamiltonian U (Φ w)) + (hamiltonian U (Φ w) - hamiltonian U w)
              = -(hamiltonian U w) from by ring]
        simp only [hf]
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, hHΨ, hkey]
      have eR : f w * ENNReal.ofReal (α w)
          = ENNReal.ofReal (min (Real.exp (-(hamiltonian U w))) (Real.exp (-(hamiltonian U (Φ w))))) := by
        have hkey : Real.exp (-(hamiltonian U w)) * α w
            = min (Real.exp (-(hamiltonian U w))) (Real.exp (-(hamiltonian U (Φ w)))) := by
          have hexp : α w = min 1 (Real.exp (hamiltonian U w - hamiltonian U (Φ w))) := rfl
          rw [hexp,
            key (Real.exp (-(hamiltonian U w))) (hamiltonian U w - hamiltonian U (Φ w))
              (Real.exp_pos _),
            ← Real.exp_add,
            show -(hamiltonian U w) + (hamiltonian U w - hamiltonian U (Φ w))
              = -(hamiltonian U (Φ w)) from by ring]
        simp only [hf]
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, hkey]
      rw [eL, eR, min_comm]
    have hA : ∫⁻ z, κ {u : ℝ |
          (if Real.log u < hamiltonian U z - hamiltonian U (Φ z) then Φ z else z) ∈ C}
          ∂Λ.withDensity f = ∫⁻ w in C, f w ∂Λ := by
      have e1 : ∫⁻ z, κ {u : ℝ |
            (if Real.log u < hamiltonian U z - hamiltonian U (Φ z) then Φ z else z) ∈ C}
            ∂Λ.withDensity f
          = ∫⁻ z, (fun z : HMCState d × HMCState d =>
              (if (Φ z) ∈ C then ENNReal.ofReal (α z) else 0)
                + (if z ∈ C then 1 - ENNReal.ofReal (α z) else 0)) z ∂Λ.withDensity f :=
        MeasureTheory.lintegral_congr fun z => hsplit' z
      rw [e1]
      rw [MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀ hfmeas.aemeasurable hsplit_meas]
      have e2 : ∫⁻ z, (f * (fun z : HMCState d × HMCState d =>
              (if (Φ z) ∈ C then ENNReal.ofReal (α z) else 0)
                + (if z ∈ C then 1 - ENNReal.ofReal (α z) else 0))) z ∂Λ
          = ∫⁻ z, (f z * (if (Φ z) ∈ C then ENNReal.ofReal (α z) else 0)
              + f z * (if z ∈ C then
                  κ {u : ℝ | Real.log u < hamiltonian U z - hamiltonian U (Φ z)}ᶜ else 0)) ∂Λ := by
        refine MeasureTheory.lintegral_congr fun z => ?_
        rw [Pi.mul_apply, ← hcompl z, mul_add]
      rw [e2]
      rw [MeasureTheory.lintegral_add_left (f := fun z : HMCState d × HMCState d =>
          f z * (if (Φ z) ∈ C then ENNReal.ofReal (α z) else 0))
          (hfmeas.mul (Measurable.ite hΦpre hofα measurable_const))
          (fun z => f z * (if z ∈ C then
            κ {u : ℝ | Real.log u < hamiltonian U z - hamiltonian U (Φ z)}ᶜ else 0))]
      have hAterm : ∫⁻ z, f z * (if (Φ z) ∈ C then ENNReal.ofReal (α z) else 0) ∂Λ
          = ∫⁻ z in Φ ⁻¹' C, f z * ENNReal.ofReal (α z) ∂Λ := by
        rw [← MeasureTheory.lintegral_indicator hΦpre (fun z => f z * ENNReal.ofReal (α z))]
        refine MeasureTheory.lintegral_congr fun z => ?_
        by_cases h : (Φ z) ∈ C <;> simp [h]
      have hchange2 : ∫⁻ z in Φ ⁻¹' C, f z * ENNReal.ofReal (α z) ∂Λ
          = ∫⁻ w in C, f w * κ {u : ℝ | Real.log u < hamiltonian U w - hamiltonian U (Φ w)} ∂Λ := by
        have s1 : ∫⁻ z in Φ ⁻¹' C, f z * ENNReal.ofReal (α z) ∂Λ
            = ∫⁻ z in Ψ ⁻¹' C, f z * ENNReal.ofReal (α z) ∂Λ := by rw [hpreC]
        have s2 : ∫⁻ z in Ψ ⁻¹' C, f z * ENNReal.ofReal (α z) ∂Λ
            = ∫⁻ z in C, f (Ψ z) * ENNReal.ofReal (α (Ψ z)) ∂Λ :=
          hchar C (fun z => f z * ENNReal.ofReal (α z)) hCmeas (hfmeas.mul hofα)
        have s3 : ∫⁻ z in C, f (Ψ z) * ENNReal.ofReal (α (Ψ z)) ∂Λ
            = ∫⁻ z in C, f z * ENNReal.ofReal (α z) ∂Λ :=
          MeasureTheory.lintegral_congr fun z => hsym_pt z
        have s4 : ∫⁻ z in C, f z * ENNReal.ofReal (α z) ∂Λ
            = ∫⁻ z in C, f z * κ {u : ℝ | Real.log u < hamiltonian U z - hamiltonian U (Φ z)} ∂Λ :=
          MeasureTheory.lintegral_congr fun z => by rw [← hακ z]
        exact ((s1.trans s2).trans s3).trans s4
      have hBterm : ∫⁻ z, f z * (if z ∈ C then
            κ {u : ℝ | Real.log u < hamiltonian U z - hamiltonian U (Φ z)}ᶜ else 0) ∂Λ
          = ∫⁻ z in C, f z * κ {u : ℝ | Real.log u < hamiltonian U z - hamiltonian U (Φ z)}ᶜ ∂Λ := by
        rw [← MeasureTheory.lintegral_indicator hCmeas
          (fun z => f z * κ {u : ℝ | Real.log u < hamiltonian U z - hamiltonian U (Φ z)}ᶜ)]
        refine MeasureTheory.lintegral_congr fun z => ?_
        by_cases h : z ∈ C <;> simp [h]
      have hcombine : ∫⁻ w in C, f w * κ {u : ℝ | Real.log u < hamiltonian U w - hamiltonian U (Φ w)} ∂Λ
            + ∫⁻ w in C, f w * κ {u : ℝ |
                Real.log u < hamiltonian U w - hamiltonian U (Φ w)}ᶜ ∂Λ
          = ∫⁻ w in C, f w ∂Λ := by
        rw [← MeasureTheory.lintegral_add_left (f := fun w : HMCState d × HMCState d =>
            f w * κ {u : ℝ | Real.log u < hamiltonian U w - hamiltonian U (Φ w)})
            (hfmeas.mul hκSmeas)
            (fun w => f w * κ {u : ℝ |
              Real.log u < hamiltonian U w - hamiltonian U (Φ w)}ᶜ)]
        refine MeasureTheory.lintegral_congr fun w => ?_
        rw [← mul_add, MeasureTheory.measure_add_measure_compl (hSmeas w), hκuniv, mul_one]
      rw [hAterm, hchange2, hBterm, hcombine]
    have hB : Λ.withDensity f C = ∫⁻ z in C, f z ∂Λ := by
      rw [← MeasureTheory.setLIntegral_one C]
      rw [MeasureTheory.setLIntegral_withDensity_eq_lintegral_mul₀
        (g := fun _ : HMCState d × HMCState d => (1 : ℝ≥0∞))
        hfmeas.aemeasurable measurable_const.aemeasurable hCmeas]
      refine MeasureTheory.lintegral_congr fun x => ?_
      rw [Pi.mul_apply, mul_one]
    rw [hA, hB]
  simpa only [hκ, hΛ, hf, hΦ] using hmain
  /- @proof-region region.target-node.session.deecda9cfd71d797 end -/

end Statlib.Imported

end

