import ProverJobs.paper_fresh_20261030t143835550708z_hulc.Vocabulary
import ProverJobs.paper_fresh_20261030t143835550708z_hulc.Base

namespace PaperProofTasks.paper_fresh_20261030t143835550708z_hulc

open _root_.PaperProofTasks.paper_fresh_20261030t143835550708z_hulc.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_411957280_656443f1 : ∀ (theta0 : ℝ) (Delta : ℝ) (hDelta_nonneg : 0 ≤ Delta) (hDelta_lt_half : Delta < 1 / 2)
    (Balpha : ℕ) (hBalpha_ge_one : 1 ≤ Balpha)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (thetaHat : ℕ → Ω → ℝ) (hthetaHat_meas : ∀ j, Measurable (thetaHat j))
    (hthetaHat_indep : iIndepFun (fun j : Fin Balpha => thetaHat ((j : ℕ) + 1)) P)
    (h_tail_eq : ∀ j : Fin Balpha,
      (P {ω | thetaHat ((j : ℕ) + 1) ω ≤ theta0}).toReal
        = (P {ω | thetaHat 1 ω ≤ theta0}).toReal)
    (h_atom_zero : ∀ j : Fin Balpha, P {ω | thetaHat ((j : ℕ) + 1) ω = theta0} = 0)
    (h_medBias : ∀ j : Fin Balpha, medBias P theta0 (thetaHat ((j : ℕ) + 1)) = Delta)
    (k : ℕ) (hk_ge_one : 1 ≤ k) (hk_le : k ≤ Balpha),
    P {ω | ¬ inCI theta0 thetaHat (fun (_ : Ω) => k) ω} = ENNReal.ofReal (Pmis Delta k) := by
  /- @proof-region region.target-node.session.c0f7d492fbcf706e begin -/
  intro theta0 Delta hDelta_nonneg hDelta_lt_half Balpha hBalpha_ge_one Ω mΩ P hP thetaHat
    hthetaHat_meas hthetaHat_indep h_tail_eq h_atom_zero h_medBias k hk_ge_one hk_le
  set a : ℝ := (P {ω | theta0 ≤ thetaHat 1 ω}).toReal with ha
  set b : ℝ := (P {ω | thetaHat 1 ω ≤ theta0}).toReal with hb
  have ha_nonneg : 0 ≤ a := by rw [ha]; exact ENNReal.toReal_nonneg
  have hb_nonneg : 0 ≤ b := by rw [hb]; exact ENNReal.toReal_nonneg
  set A : Set Ω := {ω | ∀ j ∈ Finset.Icc 1 k, theta0 < thetaHat j ω} with hA
  set B : Set Ω := {ω | ∀ j ∈ Finset.Icc 1 k, thetaHat j ω < theta0} with hB
  have hA_eq : A = ⋂ j ∈ Finset.Icc 1 k, {ω | theta0 < thetaHat j ω} := by
    rw [hA]; ext ω; simp
  have hB_eq : B = ⋂ j ∈ Finset.Icc 1 k, {ω | thetaHat j ω < theta0} := by
    rw [hB]; ext ω; simp
  have hA_meas : MeasurableSet A := by
    rw [hA_eq]
    exact Finset.measurableSet_biInter (Finset.Icc 1 k)
      (fun j _ => (hthetaHat_meas j) measurableSet_Ioi)
  have hB_meas : MeasurableSet B := by
    rw [hB_eq]
    exact Finset.measurableSet_biInter (Finset.Icc 1 k)
      (fun j _ => (hthetaHat_meas j) measurableSet_Iio)
  have hne : (Finset.Icc 1 k).Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hk_ge_one⟩⟩
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    intro ω hωA hωB
    obtain ⟨j, hj⟩ := hne
    exact (lt_asymm (hωA j hj)) (hωB j hj)
  have hsplit : {ω | ¬ inCI theta0 thetaHat (fun (_ : Ω) => k) ω} = A ∪ B := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union, hA, hB, inCI]
    constructor
    · intro h
      by_cases hcase : ∀ j ∈ Finset.Icc 1 k, theta0 < thetaHat j ω
      · exact Or.inl hcase
      · right
        push_neg at hcase
        obtain ⟨j, hj, hjle⟩ := hcase
        intro j' hj'
        by_contra hlt'
        push_neg at hlt'
        exact h ⟨⟨j, hj, hjle⟩, ⟨j', hj', hlt'⟩⟩
    · rintro (h | h)
      · rintro ⟨⟨j, hj, hjle⟩, _⟩
        exact (not_lt.mpr hjle) (h j hj)
      · rintro ⟨_, ⟨j', hj', hge⟩⟩
        exact (not_lt.mpr hge) (h j' hj')
  have hUpperEq : ∀ (f : Ω → ℝ), P {ω | f ω = theta0} = 0 →
      P {ω | theta0 ≤ f ω} = P {ω | theta0 < f ω} := by
    intro f hzero
    have hsub1 : {ω | theta0 < f ω} ⊆ {ω | theta0 ≤ f ω} := by
      intro x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      exact le_of_lt hx
    have hsub2 : {ω | theta0 ≤ f ω} ⊆ ({ω | theta0 < f ω} ∪ {ω | f ω = theta0}) := by
      intro x hx
      simp only [Set.mem_setOf_eq, Set.mem_union] at hx ⊢
      rcases lt_or_eq_of_le hx with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'.symm
    have hub : P ({ω | theta0 < f ω} ∪ {ω | f ω = theta0}) ≤ P {ω | theta0 < f ω} := by
      calc P ({ω | theta0 < f ω} ∪ {ω | f ω = theta0})
          ≤ P {ω | theta0 < f ω} + P {ω | f ω = theta0} := measure_union_le _ _
        _ = P {ω | theta0 < f ω} := by rw [hzero, add_zero]
    exact le_antisymm ((measure_mono hsub2).trans hub) (measure_mono hsub1)
  have hLowerEq : ∀ (f : Ω → ℝ), P {ω | f ω = theta0} = 0 →
      P {ω | f ω ≤ theta0} = P {ω | f ω < theta0} := by
    intro f hzero
    have hsub1 : {ω | f ω < theta0} ⊆ {ω | f ω ≤ theta0} := by
      intro x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      exact le_of_lt hx
    have hsub2 : {ω | f ω ≤ theta0} ⊆ ({ω | f ω < theta0} ∪ {ω | f ω = theta0}) := by
      intro x hx
      simp only [Set.mem_setOf_eq, Set.mem_union] at hx ⊢
      rcases lt_or_eq_of_le hx with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
    have hub : P ({ω | f ω < theta0} ∪ {ω | f ω = theta0}) ≤ P {ω | f ω < theta0} := by
      calc P ({ω | f ω < theta0} ∪ {ω | f ω = theta0})
          ≤ P {ω | f ω < theta0} + P {ω | f ω = theta0} := measure_union_le _ _
        _ = P {ω | f ω < theta0} := by rw [hzero, add_zero]
    exact le_antisymm ((measure_mono hsub2).trans hub) (measure_mono hsub1)
  have hcompl_sum : ∀ (f : Ω → ℝ), Measurable f →
      (P {ω | theta0 < f ω}).toReal + (P {ω | f ω ≤ theta0}).toReal = 1 := by
    intro f hf
    have hcompl : {ω | theta0 < f ω} = {ω | f ω ≤ theta0}ᶜ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
    have hs : MeasurableSet ({ω | f ω ≤ theta0} : Set Ω) := hf measurableSet_Iic
    have hsum : P {ω | theta0 < f ω} + P {ω | f ω ≤ theta0} = 1 := by
      have h : P {ω | f ω ≤ theta0} + P ({ω | f ω ≤ theta0}ᶜ) = P Set.univ :=
        measure_add_measure_compl hs
      rw [measure_univ] at h
      rw [hcompl, add_comm]
      exact h
    have h1 := congrArg ENNReal.toReal hsum
    have h2 : (P {ω | theta0 < f ω} + P {ω | f ω ≤ theta0}).toReal
        = (P {ω | theta0 < f ω}).toReal + (P {ω | f ω ≤ theta0}).toReal :=
      ENNReal.toReal_add (measure_ne_top P _) (measure_ne_top P _)
    rw [h2] at h1
    simpa using h1
  have hzero_one : P {ω | thetaHat 1 ω = theta0} = 0 := by
    have h := h_atom_zero ⟨0, hBalpha_ge_one⟩
    simpa using h
  have hab : a + b = 1 := by
    have h1 := hcompl_sum (thetaHat 1) (hthetaHat_meas 1)
    have h2 : (P {ω | theta0 < thetaHat 1 ω}).toReal = a := by
      rw [ha, ← hUpperEq (thetaHat 1) hzero_one]
    rw [h2, ← hb] at h1
    exact h1
  have hfacA : ∀ (j : ℕ), 1 ≤ j → j ≤ Balpha →
      P {ω | theta0 < thetaHat j ω} = ENNReal.ofReal a := by
    intro j hj1 hjk
    have hjB : j - 1 < Balpha := by omega
    have hidx : ((⟨j - 1, hjB⟩ : Fin Balpha) : ℕ) + 1 = j := by
      simp only [Fin.val_mk]; omega
    have hzero : P {ω | thetaHat j ω = theta0} = 0 := by
      have h := h_atom_zero ⟨j - 1, hjB⟩
      rw [hidx] at h
      exact h
    have htail : (P {ω | thetaHat j ω ≤ theta0}).toReal = b := by
      have h := h_tail_eq ⟨j - 1, hjB⟩
      rw [hidx] at h
      exact h.trans hb.symm
    have hsum := hcompl_sum (thetaHat j) (hthetaHat_meas j)
    rw [htail] at hsum
    have hgoal : (P {ω | theta0 < thetaHat j ω}).toReal = a := by linarith
    rw [← ENNReal.ofReal_toReal (measure_ne_top P _), hgoal]
  have hfacB : ∀ (j : ℕ), 1 ≤ j → j ≤ Balpha →
      P {ω | thetaHat j ω < theta0} = ENNReal.ofReal b := by
    intro j hj1 hjk
    have hjB : j - 1 < Balpha := by omega
    have hidx : ((⟨j - 1, hjB⟩ : Fin Balpha) : ℕ) + 1 = j := by
      simp only [Fin.val_mk]; omega
    have hzero : P {ω | thetaHat j ω = theta0} = 0 := by
      have h := h_atom_zero ⟨j - 1, hjB⟩
      rw [hidx] at h
      exact h
    have htail : (P {ω | thetaHat j ω ≤ theta0}).toReal = b := by
      have h := h_tail_eq ⟨j - 1, hjB⟩
      rw [hidx] at h
      exact h.trans hb.symm
    rw [← hLowerEq (thetaHat j) hzero]
    rw [← ENNReal.ofReal_toReal (measure_ne_top P _), htail]
  have hDelta_eq : Delta = max (1 / 2 - min a b) 0 := by
    have h := h_medBias ⟨0, hBalpha_ge_one⟩
    have h0 : ((⟨0, hBalpha_ge_one⟩ : Fin Balpha) : ℕ) + 1 = 1 := rfl
    rw [h0] at h
    rw [← h]
    simp only [medBias]
    rw [← ha, ← hb]
  have hmin : min a b = 1 / 2 - Delta := by
    have h0 : (0 : ℝ) ≤ 1 / 2 - min a b := by
      nlinarith [min_le_left a b, min_le_right a b, hab]
    have h1 : Delta ≤ 1 / 2 - min a b := by
      rw [hDelta_eq]; exact max_le le_rfl h0
    have h2 : 1 / 2 - min a b ≤ Delta := by
      rw [hDelta_eq]; exact le_max_left _ _
    linarith
  have hpow : a ^ k + b ^ k = Pmis Delta k := by
    simp only [Pmis]
    by_cases hble : b ≤ 1 / 2
    · have hba : b ≤ a := by linarith
      have hminb : min a b = b := min_eq_right hba
      have hbv : b = 1 / 2 - Delta := by linarith
      have hav : a = 1 / 2 + Delta := by linarith
      rw [hav, hbv, add_comm]
    · have hbgt : 1 / 2 < b := not_le.mp hble
      have hab' : a ≤ b := by linarith
      have hmina : min a b = a := min_eq_left hab'
      have hav : a = 1 / 2 - Delta := by linarith
      have hbv : b = 1 / 2 + Delta := by linarith
      rw [hav, hbv]
  set S : Finset (Fin Balpha) :=
    Finset.univ.filter (fun i => (i : ℕ) + 1 ∈ Finset.Icc 1 k) with hS
  have hS_mem : ∀ i : Fin Balpha, i ∈ S ↔ (i : ℕ) + 1 ∈ Finset.Icc 1 k := by
    intro i
    rw [hS]
    simp
  have hS_card : S.card = k := by
    have hinjS : Set.InjOn (fun i : Fin Balpha => (i : ℕ)) (↑S : Set (Fin Balpha)) := by
      intro x _ y _ hxy
      exact Fin.ext hxy
    have himg : S.image (fun i : Fin Balpha => (i : ℕ)) = Finset.range k := by
      ext m
      simp only [Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨i, hi, rfl⟩
        have hmem := (hS_mem i).mp hi
        have h2 : (i : ℕ) + 1 ≤ k := (Finset.mem_Icc.mp hmem).2
        omega
      · intro hm
        have hmB : m < Balpha := by omega
        refine ⟨⟨m, hmB⟩, ?_, rfl⟩
        rw [hS_mem]
        show m + 1 ∈ Finset.Icc 1 k
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have h1 : S.card = (S.image (fun i : Fin Balpha => (i : ℕ))).card :=
      (Finset.card_image_of_injOn hinjS).symm
    rw [h1, himg, Finset.card_range]
  have hA_int : A = ⋂ i ∈ S, {ω | theta0 < thetaHat ((i : ℕ) + 1) ω} := by
    ext ω
    simp only [hA, Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h i hi
      exact h _ ((hS_mem i).mp hi)
    · intro h j hj
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      have hjk : j ≤ k := (Finset.mem_Icc.mp hj).2
      have hjB : j - 1 < Balpha := by omega
      have hidx : ((⟨j - 1, hjB⟩ : Fin Balpha) : ℕ) + 1 = j := by
        show (j - 1) + 1 = j
        omega
      have hmem : (⟨j - 1, hjB⟩ : Fin Balpha) ∈ S := by
        rw [hS_mem, hidx]
        exact hj
      have := h ⟨j - 1, hjB⟩ hmem
      rwa [hidx] at this
  have hB_int : B = ⋂ i ∈ S, {ω | thetaHat ((i : ℕ) + 1) ω < theta0} := by
    ext ω
    simp only [hB, Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h i hi
      exact h _ ((hS_mem i).mp hi)
    · intro h j hj
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      have hjk : j ≤ k := (Finset.mem_Icc.mp hj).2
      have hjB : j - 1 < Balpha := by omega
      have hidx : ((⟨j - 1, hjB⟩ : Fin Balpha) : ℕ) + 1 = j := by
        show (j - 1) + 1 = j
        omega
      have hmem : (⟨j - 1, hjB⟩ : Fin Balpha) ∈ S := by
        rw [hS_mem, hidx]
        exact hj
      have := h ⟨j - 1, hjB⟩ hmem
      rwa [hidx] at this
  have hPA : P A = ENNReal.ofReal (a ^ k) := by
    have hstep : P A = (ENNReal.ofReal a) ^ k := by
      have hA_int' : A = ⋂ i ∈ S, thetaHat ((i : ℕ) + 1) ⁻¹' Set.Ioi theta0 := hA_int
      have hkey : P (⋂ i ∈ S, thetaHat ((i : ℕ) + 1) ⁻¹' Set.Ioi theta0)
          = ∏ i ∈ S, P (thetaHat ((i : ℕ) + 1) ⁻¹' Set.Ioi theta0) :=
        (ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul
          (μ := P) (f := fun j : Fin Balpha => thetaHat ((j : ℕ) + 1))).mp
          hthetaHat_indep S (sets := fun _ => Set.Ioi theta0) (fun i _ => measurableSet_Ioi)
      have hfac : ∀ i ∈ S,
          P (thetaHat ((i : ℕ) + 1) ⁻¹' Set.Ioi theta0) = ENNReal.ofReal a := by
        intro i hi
        have hmem := (hS_mem i).mp hi
        exact hfacA ((i : ℕ) + 1) (Finset.mem_Icc.mp hmem).1
          (le_trans (Finset.mem_Icc.mp hmem).2 hk_le)
      rw [hA_int', hkey]
      calc ∏ i ∈ S, P (thetaHat ((i : ℕ) + 1) ⁻¹' Set.Ioi theta0)
          = ∏ i ∈ S, ENNReal.ofReal a := Finset.prod_congr rfl hfac
        _ = (ENNReal.ofReal a) ^ S.card := Finset.prod_const (ENNReal.ofReal a)
        _ = (ENNReal.ofReal a) ^ k := by rw [hS_card]
    exact hstep.trans (ENNReal.ofReal_pow ha_nonneg k).symm
  have hPB : P B = ENNReal.ofReal (b ^ k) := by
    have hstep : P B = (ENNReal.ofReal b) ^ k := by
      have hB_int' : B = ⋂ i ∈ S, thetaHat ((i : ℕ) + 1) ⁻¹' Set.Iio theta0 := hB_int
      have hkey : P (⋂ i ∈ S, thetaHat ((i : ℕ) + 1) ⁻¹' Set.Iio theta0)
          = ∏ i ∈ S, P (thetaHat ((i : ℕ) + 1) ⁻¹' Set.Iio theta0) :=
        (ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul
          (μ := P) (f := fun j : Fin Balpha => thetaHat ((j : ℕ) + 1))).mp
          hthetaHat_indep S (sets := fun _ => Set.Iio theta0) (fun i _ => measurableSet_Iio)
      have hfac : ∀ i ∈ S,
          P (thetaHat ((i : ℕ) + 1) ⁻¹' Set.Iio theta0) = ENNReal.ofReal b := by
        intro i hi
        have hmem := (hS_mem i).mp hi
        exact hfacB ((i : ℕ) + 1) (Finset.mem_Icc.mp hmem).1
          (le_trans (Finset.mem_Icc.mp hmem).2 hk_le)
      rw [hB_int', hkey]
      calc ∏ i ∈ S, P (thetaHat ((i : ℕ) + 1) ⁻¹' Set.Iio theta0)
          = ∏ i ∈ S, ENNReal.ofReal b := Finset.prod_congr rfl hfac
        _ = (ENNReal.ofReal b) ^ S.card := Finset.prod_const (ENNReal.ofReal b)
        _ = (ENNReal.ofReal b) ^ k := by rw [hS_card]
    exact hstep.trans (ENNReal.ofReal_pow hb_nonneg k).symm
  rw [hsplit, measure_union hdisj hB_meas, hPA, hPB,
    ← ENNReal.ofReal_add (pow_nonneg ha_nonneg k) (pow_nonneg hb_nonneg k), hpow]
  /- @proof-region region.target-node.session.c0f7d492fbcf706e end -/

end

end Statlib.Imported

