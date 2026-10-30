import Statlib.Nonparametric.Approximation.Metric
import Statlib.Nonparametric.Vocabulary.NeuralNetwork

open Set MeasureTheory
open Statlib.Nonparametric.Vocabulary

/-! # Neural-Network Approximation Bounds -/

namespace Statlib.Nonparametric.Approximation.NeuralNetwork

theorem reluNetworkClass_classApproximationError_le_of_pointwise_candidate
    (d depth width parameterCount : ℕ)
    (nu : Measure (Fin d → ℝ)) [IsFiniteMeasure nu]
    (f0 : (Fin d → ℝ) → ℝ)
    (N : FullyConnectedReLUNet d)
    (eps : ℝ)
    (hN_depth_pos : 0 < N.depth)
    (hN_depth : N.depth ≤ depth)
    (hN_width : N.width ≤ width)
    (hN_paramCount : N.parameterCount ≤ parameterCount)
    (h_eps_nonneg : 0 ≤ eps)
    (hN_meas : Measurable N.realize)
    (hf0_meas : Measurable f0)
    (h_pointwise : ∀ (x : Fin d → ℝ), |N.realize x - f0 x| ≤ eps)
    (h_bdd_below : BddBelow ((fun (f : (Fin d → ℝ) → ℝ) => integratedSquaredError nu f f0) '' (reluNetworkClass d depth width parameterCount)))
      : classApproximationError nu (reluNetworkClass d depth width parameterCount) f0 ≤ (nu Set.univ).toReal * eps ^ 2 := by
    -- N.realize belongs to reluNetworkClass due to the bound hypotheses
    have h_mem : N.realize ∈ reluNetworkClass d depth width parameterCount := by
      dsimp [reluNetworkClass]
      refine ⟨N, hN_depth_pos, hN_depth, hN_width, hN_paramCount, ?_⟩
      intro x; rfl
    -- Therefore integratedSquaredError nu N.realize f0 belongs to the image set
    have h_mem_image : integratedSquaredError nu N.realize f0 ∈
        ((fun (f : (Fin d → ℝ) → ℝ) => integratedSquaredError nu f f0) '' (reluNetworkClass d depth width parameterCount)) := by
      refine ⟨N.realize, h_mem, rfl⟩
    -- classApproximationError is defined as sInf of that image set
    have h_sInf_le : classApproximationError nu (reluNetworkClass d depth width parameterCount) f0 ≤ integratedSquaredError nu N.realize f0 := by
      dsimp [classApproximationError]
      exact csInf_le h_bdd_below h_mem_image
    -- apply the pointwise bound to bound the integrated squared error
    have h_integral_bound : integratedSquaredError nu N.realize f0 ≤ (nu Set.univ).toReal * eps ^ 2 :=
      Metric.integratedSquaredError_le_of_pointwise_bound nu N.realize f0 hN_meas hf0_meas eps h_eps_nonneg h_pointwise
    -- combine
    exact le_trans h_sInf_le h_integral_bound

theorem reluNetworkClass_classApproximationError_le_of_candidate_ise
    (d depth width parameterCount : ℕ) (f0 : (Fin d → ℝ) → ℝ) (nu : Measure (Fin d → ℝ))
    (N : FullyConnectedReLUNet d) (eps : ℝ)
    (hf0_meas : Measurable f0) (hNmeas : Measurable N.realize)
    (hdepth_pos : 0 < N.depth)
    (hdepth : N.depth ≤ depth) (hwidth : N.width ≤ width) (hparam : N.parameterCount ≤ parameterCount)
    (hise : integratedSquaredError nu N.realize f0 ≤ eps)
    (hint : Integrable (fun (x : Fin d → ℝ) => (N.realize x - f0 x)^2) nu)
    (hbdd : BddBelow (Set.image (fun (g : (Fin d → ℝ) → ℝ) => integratedSquaredError nu g f0)
                                (reluNetworkClass d depth width parameterCount))) :
    classApproximationError nu (reluNetworkClass d depth width parameterCount) f0 ≤ eps := by
  have hmem : N.realize ∈ reluNetworkClass d depth width parameterCount := by
    refine ⟨N, hdepth_pos, hdepth, hwidth, hparam, fun x => rfl⟩
  have hval : integratedSquaredError nu N.realize f0 ∈
      ((fun (g : (Fin d → ℝ) → ℝ) => integratedSquaredError nu g f0) '' (reluNetworkClass d depth width parameterCount)) := by
    refine ⟨N.realize, hmem, rfl⟩
  have h_sInf_le : classApproximationError nu (reluNetworkClass d depth width parameterCount) f0 ≤
      integratedSquaredError nu N.realize f0 := by
    -- classApproximationError is defined as sInf of that image set; hbdd gives BddBelow
    rw [show classApproximationError nu (reluNetworkClass d depth width parameterCount) f0 =
        sInf ((fun (g : (Fin d → ℝ) → ℝ) => integratedSquaredError nu g f0) '' (reluNetworkClass d depth width parameterCount)) from rfl]
    exact csInf_le hbdd hval
  calc
    classApproximationError nu (reluNetworkClass d depth width parameterCount) f0 ≤ integratedSquaredError nu N.realize f0 := h_sInf_le
    _ ≤ eps := hise

theorem reluNetworkClass_classApproximationError_le_of_exists_pointwise
  (d depth width parameterCount : ℕ)
  (f0 : (Fin d → ℝ) → ℝ)
  (nu : Measure (Fin d → ℝ))
  (eps : ℝ)
  (h_f0_meas : Measurable f0)
  (h_nu_fin : IsFiniteMeasure nu)
  (h_eps_nonneg : 0 ≤ eps)

  (h_exists_net : ∃ N : FullyConnectedReLUNet d, 0 < N.depth ∧
    N.depth ≤ depth ∧ N.width ≤ width ∧ N.parameterCount ≤ parameterCount ∧
      Measurable (N.realize) ∧ ∀ x : Fin d → ℝ, |N.realize x - f0 x| ≤ eps)
  (h_bdd_below : BddBelow (Set.image (fun (f : (Fin d → ℝ) → ℝ) => integratedSquaredError nu f f0) (reluNetworkClass d depth width parameterCount)))
  : classApproximationError nu (reluNetworkClass d depth width parameterCount) f0 ≤ (nu Set.univ).toReal * eps ^ 2 := by
  rcases h_exists_net with
    ⟨N, hN_depth_pos, hN_depth, hN_width, hN_param, hN_meas, hN_bound⟩
  have hN_mem : N.realize ∈ reluNetworkClass d depth width parameterCount := by
    dsimp [reluNetworkClass, Set.mem_setOf_eq]
    exact ⟨N, hN_depth_pos, hN_depth, hN_width, hN_param, fun x => rfl⟩
  set E := integratedSquaredError nu (N.realize) f0 with hE_def
  set S := (fun (f : (Fin d → ℝ) → ℝ) => integratedSquaredError nu f f0) '' (reluNetworkClass d depth width parameterCount) with hS_def
  have h_classApprox_eq_sInf : classApproximationError nu (reluNetworkClass d depth width parameterCount) f0 = sInf S := by
    dsimp [classApproximationError, S]
  have hE_mem_S : E ∈ S := by
    dsimp [E, S]
    refine ⟨N.realize, hN_mem, rfl⟩
  have h_sInf_le_E : sInf S ≤ E :=
    csInf_le h_bdd_below hE_mem_S
  have hE_bound : E ≤ (nu Set.univ).toReal * eps ^ 2 :=
    Statlib.Nonparametric.Approximation.Metric.integratedSquaredError_le_of_pointwise_bound nu (N.realize) f0 hN_meas h_f0_meas eps h_eps_nonneg hN_bound
  calc
    classApproximationError nu (reluNetworkClass d depth width parameterCount) f0 = sInf S := h_classApprox_eq_sInf
    _ ≤ E := h_sInf_le_E
    _ ≤ (nu Set.univ).toReal * eps ^ 2 := hE_bound

end Statlib.Nonparametric.Approximation.NeuralNetwork
