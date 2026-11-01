import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M021_Vocabulary
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions

/- Original module ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProvedNodes.Node_1731977007_59742388_a35aa471; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal
open Statlib.Imported

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_1731977007_59742388 : ∀ (g q0 : ℝ → ℝ) (c : ℝ) (m M : ℝ) (n : ℕ) (x : Fin n → ℝ)
    (hc : 0 < c) (hg_meas : Measurable g) (hg_nonneg : ∀ y, 0 ≤ g y)
    (hg_support : ∀ y ∉ Set.Icc (-c) c, g y = 0)
    (hq0_meas : Measurable q0) (hq0_nonneg : ∀ y, 0 ≤ q0 y)
    (hq0_density : ∫⁻ y, ENNReal.ofReal (q0 y) ∂volume = 1)
    (hm : 0 < m) (hmM : m ≤ M)
    (hT1 : ∀ y ∈ Set.Icc (-c) c, m ≤ g y ∧ g y ≤ M),
    ∀ (B : Finset (Fin n)) (i : Fin n), i ∈ B →
      margLik g q0 B x ≤ M * margLik g q0 (B.erase i) x := by
  /- @proof-region region.target-node.session.10a514d588d3e2ca begin -/
  intro g q0 c m M n x hc hg_meas hg_nonneg hg_support hq0_meas hq0_nonneg hq0_density hm hmM hT1
  intro B i hi
  have hM_nonneg : 0 ≤ M := le_of_lt (lt_of_lt_of_le hm hmM)
  have hgM : ∀ y : ℝ, g y ≤ M := by
    intro y
    by_cases hy : y ∈ Set.Icc (-c) c
    · exact (hT1 y hy).2
    · rw [hg_support y hy]
      linarith
  have hprod_nonneg : ∀ (A : Finset (Fin n)) (θ : ℝ), 0 ≤ ∏ l ∈ A, g (x l - θ) :=
    fun A θ => Finset.prod_nonneg fun l _ => hg_nonneg _
  have hprod_le : ∀ (A : Finset (Fin n)) (θ : ℝ), ∏ l ∈ A, g (x l - θ) ≤ M ^ A.card := by
    intro A θ
    calc ∏ l ∈ A, g (x l - θ) ≤ ∏ l ∈ A, M :=
          Finset.prod_le_prod (fun l _ => hg_nonneg _) fun l _ => hgM _
      _ = M ^ A.card := Finset.prod_const M
  have hmeas_prod : ∀ A : Finset (Fin n), Measurable fun θ : ℝ => ∏ l ∈ A, g (x l - θ) := by
    intro A
    induction A using Finset.induction_on with
    | empty => simpa using (measurable_const : Measurable fun _ : ℝ => (1 : ℝ))
    | insert a s ha ih =>
        have ha' : Measurable fun θ : ℝ => g (x a - θ) :=
          hg_meas.comp (measurable_const.sub measurable_id)
        simpa [Finset.prod_insert ha] using ha'.mul ih
  have hint : ∀ A : Finset (Fin n), Integrable fun θ : ℝ => (∏ l ∈ A, g (x l - θ)) * q0 θ := by
    intro A
    have haesm : AEStronglyMeasurable (fun θ : ℝ => (∏ l ∈ A, g (x l - θ)) * q0 θ) volume :=
      ((hmeas_prod A).mul hq0_meas).aestronglyMeasurable
    have hnonneg : ∀ᵐ θ ∂volume, 0 ≤ (∏ l ∈ A, g (x l - θ)) * q0 θ :=
      ae_of_all volume fun θ => mul_nonneg (hprod_nonneg A θ) (hq0_nonneg θ)
    refine (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable haesm hnonneg).mp ?_
    have hq0_enn : Measurable fun θ : ℝ => ENNReal.ofReal (q0 θ) := by measurability
    have hle : ∫⁻ θ, ENNReal.ofReal ((∏ l ∈ A, g (x l - θ)) * q0 θ) ∂volume
        ≤ ENNReal.ofReal (M ^ A.card) := by
      calc ∫⁻ θ, ENNReal.ofReal ((∏ l ∈ A, g (x l - θ)) * q0 θ) ∂volume
          ≤ ∫⁻ θ, ENNReal.ofReal (M ^ A.card * q0 θ) ∂volume :=
            MeasureTheory.lintegral_mono fun θ =>
              ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hprod_le A θ) (hq0_nonneg θ))
        _ = ∫⁻ θ, ENNReal.ofReal (M ^ A.card) * ENNReal.ofReal (q0 θ) ∂volume :=
            MeasureTheory.lintegral_congr fun θ =>
              ENNReal.ofReal_mul (pow_nonneg hM_nonneg A.card)
        _ = ENNReal.ofReal (M ^ A.card) * ∫⁻ θ, ENNReal.ofReal (q0 θ) ∂volume :=
            MeasureTheory.lintegral_const_mul (r := ENNReal.ofReal (M ^ A.card))
              (f := fun θ : ℝ => ENNReal.ofReal (q0 θ)) hq0_enn
        _ = ENNReal.ofReal (M ^ A.card) := by rw [hq0_density, mul_one]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have hpt : ∀ θ : ℝ, (∏ l ∈ B, g (x l - θ)) * q0 θ
      ≤ M * ((∏ l ∈ B.erase i, g (x l - θ)) * q0 θ) := by
    intro θ
    have hP : 0 ≤ (∏ l ∈ B.erase i, g (x l - θ)) * q0 θ :=
      mul_nonneg (hprod_nonneg _ _) (hq0_nonneg _)
    calc (∏ l ∈ B, g (x l - θ)) * q0 θ
        = (g (x i - θ) * ∏ l ∈ B.erase i, g (x l - θ)) * q0 θ := by
            rw [← Finset.mul_prod_erase B (fun l => g (x l - θ)) hi]
      _ = g (x i - θ) * ((∏ l ∈ B.erase i, g (x l - θ)) * q0 θ) := by rw [mul_assoc]
      _ ≤ M * ((∏ l ∈ B.erase i, g (x l - θ)) * q0 θ) :=
          mul_le_mul_of_nonneg_right (hgM _) hP
  have hMh_int : Integrable fun θ : ℝ => M * ((∏ l ∈ B.erase i, g (x l - θ)) * q0 θ) :=
    (hint (B.erase i)).const_mul M
  have key : ∫ θ, (∏ l ∈ B, g (x l - θ)) * q0 θ
      ≤ ∫ θ, M * ((∏ l ∈ B.erase i, g (x l - θ)) * q0 θ) :=
    MeasureTheory.integral_mono_of_nonneg
      (ae_of_all volume fun θ => mul_nonneg (hprod_nonneg B θ) (hq0_nonneg θ)) hMh_int
      (ae_of_all volume hpt)
  have hconst : ∫ θ, M * ((∏ l ∈ B.erase i, g (x l - θ)) * q0 θ)
      = M * ∫ θ, (∏ l ∈ B.erase i, g (x l - θ)) * q0 θ :=
    MeasureTheory.integral_const_mul M _
  show ∫ θ, (∏ l ∈ B, g (x l - θ)) * q0 θ
      ≤ M * ∫ θ, (∏ l ∈ B.erase i, g (x l - θ)) * q0 θ
  rw [← hconst]
  exact key
  /- @proof-region region.target-node.session.10a514d588d3e2ca end -/

end Statlib.Imported
end DPCompletedProof
