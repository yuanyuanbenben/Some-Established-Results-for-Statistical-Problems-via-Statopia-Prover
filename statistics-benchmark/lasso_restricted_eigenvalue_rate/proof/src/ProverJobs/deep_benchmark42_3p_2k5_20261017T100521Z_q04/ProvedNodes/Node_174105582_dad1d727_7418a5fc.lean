import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q04.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q04.Base

open MeasureTheory ProbabilityTheory
open Msc62GroundTruth

open MeasureTheory ProbabilityTheory
namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_174105582_dad1d727 : ∀ {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Z : Omega → ℝ) (c a : ℝ) (hc : 0 < c) (ha : 0 < a)
    (hint : ∀ t : ℝ, Integrable (fun omega => Real.exp (t * Z omega)) P)
    (hmgf : ∀ t : ℝ,
      ∫ omega, Real.exp (t * Z omega) ∂P ≤ Real.exp (c * t ^ 2 / 2)),
    P.real {omega | a ≤ |Z omega|} ≤ 2 * Real.exp (-(a ^ 2) / (2 * c)) := by
  /- @proof-region region.target-node.session.e7ebb0ae0f2ad0ba begin -/
  intro Omega _ P _ Z c a hc ha hint hmgf
  have hcne : c ≠ 0 := ne_of_gt hc
  have hpos : 0 < a / c := div_pos ha hc
  have hsubset : {omega | a ≤ |Z omega|} ⊆ {omega | a ≤ Z omega} ∪ {omega | Z omega ≤ -a} := by
    intro omega hω
    have hω' : a ≤ |Z omega| := hω
    show a ≤ Z omega ∨ Z omega ≤ -a
    by_cases h : 0 ≤ Z omega
    · left
      rw [abs_of_nonneg h] at hω'
      exact hω'
    · right
      have hlt : Z omega < 0 := by
        by_contra hcon
        push_neg at hcon
        exact h hcon
      rw [abs_of_neg hlt] at hω'
      linarith
  have hupper : P.real {omega | a ≤ Z omega} ≤ Real.exp (-(a ^ 2) / (2 * c)) := by
    have h1 := ProbabilityTheory.measure_ge_le_exp_mul_mgf (μ := P) (X := Z) (t := a / c) a
      (le_of_lt hpos) (hint (a / c))
    have hm : ProbabilityTheory.mgf Z P (a / c) ≤ Real.exp (c * (a / c) ^ 2 / 2) := by
      simpa only [ProbabilityTheory.mgf] using hmgf (a / c)
    have hkey : Real.exp (-(a / c) * a) * Real.exp (c * (a / c) ^ 2 / 2) =
        Real.exp (-(a ^ 2) / (2 * c)) := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    calc
      P.real {omega | a ≤ Z omega}
          ≤ Real.exp (-(a / c) * a) * ProbabilityTheory.mgf Z P (a / c) := h1
      _ ≤ Real.exp (-(a / c) * a) * Real.exp (c * (a / c) ^ 2 / 2) :=
            mul_le_mul_of_nonneg_left hm (le_of_lt (Real.exp_pos _))
      _ = Real.exp (-(a ^ 2) / (2 * c)) := hkey
  have hlower : P.real {omega | Z omega ≤ -a} ≤ Real.exp (-(a ^ 2) / (2 * c)) := by
    have hside : -a / c ≤ 0 := by
      have h3 : -a / c = -(a / c) := by ring_nf
      linarith
    have h1 := ProbabilityTheory.measure_le_le_exp_mul_mgf (μ := P) (X := Z) (t := -a / c) (-a)
      hside (hint (-a / c))
    have hm : ProbabilityTheory.mgf Z P (-a / c) ≤ Real.exp (c * (-a / c) ^ 2 / 2) := by
      simpa only [ProbabilityTheory.mgf] using hmgf (-a / c)
    have hkey : Real.exp (-(-a / c) * (-a)) * Real.exp (c * (-a / c) ^ 2 / 2) =
        Real.exp (-(a ^ 2) / (2 * c)) := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    calc
      P.real {omega | Z omega ≤ -a}
          ≤ Real.exp (-(-a / c) * (-a)) * ProbabilityTheory.mgf Z P (-a / c) := h1
      _ ≤ Real.exp (-(-a / c) * (-a)) * Real.exp (c * (-a / c) ^ 2 / 2) :=
            mul_le_mul_of_nonneg_left hm (le_of_lt (Real.exp_pos _))
      _ = Real.exp (-(a ^ 2) / (2 * c)) := hkey
  have hfin : ∀ s : Set Omega, P s ≠ ⊤ := by
    intro s
    first
      | exact measure_ne_top s
      | exact measure_ne_top P s
  have hcomb : P.real {omega | a ≤ |Z omega|} ≤
      P.real {omega | a ≤ Z omega} + P.real {omega | Z omega ≤ -a} := by
    have hT : P {omega | a ≤ Z omega} ≠ ⊤ := hfin _
    have hU : P {omega | Z omega ≤ -a} ≠ ⊤ := hfin _
    have hsum : P {omega | a ≤ Z omega} + P {omega | Z omega ≤ -a} ≠ ⊤ := by
      first
        | exact ENNReal.add_ne_top.mpr ⟨hT, hU⟩
        | (intro h
           rcases ENNReal.add_eq_top.mp h with h' | h'
           · exact hT h'
           · exact hU h')
    have hmono : P {omega | a ≤ |Z omega|} ≤
        P ({omega | a ≤ Z omega} ∪ {omega | Z omega ≤ -a}) :=
      MeasureTheory.measure_mono hsubset
    have hunion : P ({omega | a ≤ Z omega} ∪ {omega | Z omega ≤ -a}) ≤
        P {omega | a ≤ Z omega} + P {omega | Z omega ≤ -a} :=
      MeasureTheory.measure_union_le _ _
    have hbr : ∀ s : Set Omega, P.real s = (P s).toReal := by
      intro s
      first
        | rfl
        | exact MeasureTheory.Measure.real_def P s
        | exact MeasureTheory.Measure.real_def s
    simp only [hbr]
    calc
      (P {omega | a ≤ |Z omega|}).toReal
          ≤ (P {omega | a ≤ Z omega} + P {omega | Z omega ≤ -a}).toReal :=
            ENNReal.toReal_mono hsum (le_trans hmono hunion)
      _ ≤ (P {omega | a ≤ Z omega}).toReal + (P {omega | Z omega ≤ -a}).toReal :=
            ENNReal.toReal_add_le
  linarith
  /- @proof-region region.target-node.session.e7ebb0ae0f2ad0ba end -/

end Msc62GroundTruth
