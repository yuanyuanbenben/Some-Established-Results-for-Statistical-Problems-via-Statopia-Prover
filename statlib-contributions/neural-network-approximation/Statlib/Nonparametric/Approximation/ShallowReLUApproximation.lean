import Statlib.Nonparametric.Approximation.ShallowReLUApproximationGeometry

open Statlib.Nonparametric.Vocabulary

/-! # Shallow ReLU Approximation

The public entry point gives the uniform Holder-smooth approximation rate in
terms of fully connected network depth and width.
-/

namespace Statlib.Nonparametric.Approximation.NeuralNetworkAlgebra

-- The finite phase assembly elaborates all concrete network witnesses at once.
set_option maxHeartbeats 2000000 in
private theorem holder_smooth_shallow_relu_neural_network_approximation_at_resolution
    {d r : Nat} {beta C B : Real}
    (hd : 0 < d)
    (hbeta_pos : 0 < beta) (hbeta_le_one : beta <= 1)
    (hC_nonneg : 0 <= C) (hB_nonneg : 0 <= B) :
    exists W0 M0 Dblock : Nat,
      0 < W0 /\ 0 < M0 /\ 0 < Dblock /\
      exists cState : Real, 0 < cState /\
        forall M : Nat, M0 <= M ->
          forall f : (Fin d -> Real) -> Real,
            f ∈ holderSmoothBall r beta C B ->
              exists N : FullyConnectedReLUNet d,
                N.depth = (M ^ d) * (Dblock + 1) /\
                N.width <= W0 /\
                N.parameterCount <=
                  fullyConnectedReLUParameterCount d
                    ((M ^ d) * (Dblock + 1)) W0 /\
                forall x : Fin d -> Real,
                  (forall q : Fin d, x q ∈ Set.Icc (0 : Real) 1) ->
                    |N.realize x - f x| <=
                      cState * shallowReLUResolutionRate M r beta := by
  classical
  obtain ⟨A, hA_nonneg, hAcoeff⟩ :=
    holderSmoothBall_taylor_coefficients_admit_uniform_bound
      d r hbeta_pos.le hC_nonneg hB_nonneg
  let Phase := Fin d -> Fin 2
  let phaseCard : Nat := Fintype.card Phase
  let depthFactor : Nat := twoScalePhaseDepthFactor d r
  let phaseWidth : Nat := max 1 (twoScalePhaseWidthBound d r)
  let W0 : Nat := 2 * d + phaseWidth + 3
  let Dblock : Nat := (phaseCard + 1) * (depthFactor + 1)
  let Kphase : Real :=
    twoScalePhaseRateConstant d r beta C A
  let alpha : Real := (r : Real) + beta
  let Ktaylor : Real :=
    (C / (Nat.factorial r : Real)) * Real.rpow 4 alpha
  let cState : Real := 1 + (phaseCard : Real) * Kphase + Ktaylor
  have hKphase : 0 <= Kphase := by
    exact twoScalePhaseRateConstant_nonneg d r hC_nonneg hA_nonneg
  have hfactorial : 0 < (Nat.factorial r : Real) := by positivity
  have hKtaylor : 0 <= Ktaylor := by
    dsimp [Ktaylor]
    positivity
  have hW0 : 0 < W0 := by
    dsimp [W0]
    omega
  have hDblock : 0 < Dblock := by
    dsimp [Dblock, depthFactor, phaseCard]
    positivity
  have hcState : 0 < cState := by
    dsimp [cState]
    positivity
  refine ⟨W0, 2, Dblock, hW0, by norm_num, hDblock, cState, hcState, ?_⟩
  intro M hM f hf
  have hMtwo : 2 <= M := hM
  have hMpos : 0 < M := by omega
  let T : Nat := M ^ d
  have hTpos : 0 < T := by
    dsimp [T]
    positivity
  obtain ⟨orderC, _horderC0, _horderCstep⟩ :=
    exists_reluApprox_serpentine_fineGrid_equiv M d hMpos
  obtain ⟨orderF, _horderF0, horderFstep⟩ :=
    exists_reluApprox_serpentine_fineGrid_equiv M d hMpos
  have horderFstepProp : forall (k : Nat) (hk : k + 1 < M ^ d),
      exists q : Fin d,
        Int.natAbs
          ((orderF ⟨k + 1, hk⟩ q).val -
            (orderF ⟨k, Nat.lt_of_succ_lt hk⟩ q).val) = 1 /\
        forall u : Fin d, u ≠ q ->
          orderF ⟨k + 1, hk⟩ u =
            orderF ⟨k, Nat.lt_of_succ_lt hk⟩ u := by
    intro k hk
    rcases horderFstep k hk with ⟨q, hstep, hfixed⟩
    refine ⟨q, by simpa using hstep, ?_⟩
    intro u hu
    exact hfixed u (by simp [hu])
  have hphaseWitness : forall phase : Phase,
      exists N : FullyConnectedReLUNet d,
        0 < N.depth /\
        N.depth <= depthFactor * T /\
        N.width <= phaseWidth /\
        N.parameterCount <= fullyConnectedReLUParameterCount d N.depth N.width /\
        forall x : Fin d -> Real,
          (forall q, x q ∈ Set.Icc (0 : Real) 1) ->
          |N.realize x -
            (Finset.univ.sum fun b : Fin T =>
              Finset.univ.sum fun t : Fin T =>
                axisAlignedBoxTentWeight
                    (twoScaleShiftedCenter M orderC orderF phase b t)
                    (twoScaleShiftedScale M phase b t) x *
                  finiteLinearCombination
                    (Finset.univ : Finset (TaylorMultiindex r d))
                    (fun a => ((Nat.factorial a.1.val : Real)⁻¹) *
                      (iteratedFDeriv Real a.1.val f
                        (twoScaleShiftedCenter M orderC orderF phase b t))
                          (fun k : Fin a.1.val => fun q : Fin d =>
                            if q = a.2 k then 1 else 0))
                    (fun a y => Finset.univ.prod fun k : Fin a.1.val =>
                      y (a.2 k) -
                        twoScaleShiftedCenter M orderC orderF phase b t
                          (a.2 k)) x)| <=
            Kphase * shallowReLUResolutionRate M r beta := by
    intro phase
    rcases exists_two_scale_phase_network_rate
        hd hMtwo hbeta_pos hbeta_le_one hC_nonneg hA_nonneg
        orderC orderF horderFstepProp phase f hf (hAcoeff f hf) with
      ⟨N, hNpos, hNdepth, hNwidth, hNparam, hNerror⟩
    refine ⟨N, hNpos, ?_, ?_, hNparam, ?_⟩
    · simpa [T, depthFactor] using hNdepth
    · exact le_trans hNwidth (le_max_right 1 _)
    · simpa [Phase, T, Kphase] using hNerror
  let phaseNet : Phase -> FullyConnectedReLUNet d := fun phase =>
    Classical.choose (hphaseWitness phase)
  have hphaseSpec : forall phase : Phase,
      0 < (phaseNet phase).depth /\
      (phaseNet phase).depth <= depthFactor * T /\
      (phaseNet phase).width <= phaseWidth /\
      (phaseNet phase).parameterCount <=
        fullyConnectedReLUParameterCount d (phaseNet phase).depth
          (phaseNet phase).width /\
      forall x : Fin d -> Real,
        (forall q, x q ∈ Set.Icc (0 : Real) 1) ->
        |(phaseNet phase).realize x -
          (Finset.univ.sum fun b : Fin T =>
            Finset.univ.sum fun t : Fin T =>
              axisAlignedBoxTentWeight
                  (twoScaleShiftedCenter M orderC orderF phase b t)
                  (twoScaleShiftedScale M phase b t) x *
                finiteLinearCombination
                  (Finset.univ : Finset (TaylorMultiindex r d))
                  (fun a => ((Nat.factorial a.1.val : Real)⁻¹) *
                    (iteratedFDeriv Real a.1.val f
                      (twoScaleShiftedCenter M orderC orderF phase b t))
                        (fun k : Fin a.1.val => fun q : Fin d =>
                          if q = a.2 k then 1 else 0))
                  (fun a y => Finset.univ.prod fun k : Fin a.1.val =>
                    y (a.2 k) -
                      twoScaleShiftedCenter M orderC orderF phase b t
                        (a.2 k)) x)| <=
          Kphase * shallowReLUResolutionRate M r beta := by
    intro phase
    exact Classical.choose_spec (hphaseWitness phase)
  let D0 : Nat := depthFactor * T
  have hD0 : 0 < D0 := by
    dsimp [D0, depthFactor]
    positivity
  let padded : Phase -> FullyConnectedReLUNet d := fun phase =>
    reluApproxPadDepth (phaseNet phase) D0
  let approx : Phase -> (Fin d -> Real) -> Real := fun phase =>
    (padded phase).realize
  have hclass : forall phase : Phase,
      approx phase ∈ reluNetworkClass d D0 phaseWidth
        (fullyConnectedReLUParameterCount d D0 phaseWidth) := by
    intro phase
    rw [reluNetworkClass]
    refine ⟨padded phase, ?_, ?_, ?_, ?_, fun _ => rfl⟩
    · simpa [padded] using hD0
    · simp [padded]
    · simpa [padded] using (hphaseSpec phase).2.2.1
    · rw [show padded phase =
          reluApproxPadDepth (phaseNet phase) D0 by rfl,
        reluApproxPadDepth_parameterCount]
      exact fullyConnectedReLUParameterCount_mono_width d D0
        (hphaseSpec phase).2.2.1
  obtain ⟨Nsum, hNsumPos, hNsumDepth, hNsumWidth, _hNsumParam, hNsumRealize⟩ :=
    finite_linear_combination_reluNetworkClass_serial_fixed_width_network_witness_bound
      hD0 (show 0 < phaseWidth by simp [phaseWidth])
      (fun _ : Phase => (1 : Real)) approx hclass
  let Dtarget : Nat := T * (Dblock + 1)
  have hNsumDepthTarget : Nsum.depth <= Dtarget := by
    apply le_trans hNsumDepth
    dsimp [Dtarget, Dblock, D0, phaseCard]
    have hTone : 1 <= T := hTpos
    nlinarith
  let N : FullyConnectedReLUNet d := reluApproxPadDepth Nsum Dtarget
  refine ⟨N, ?_, ?_, ?_, ?_⟩
  · simp [N, Dtarget, T]
  · simpa [N, W0, phaseCard, Phase] using hNsumWidth
  · rw [show N = reluApproxPadDepth Nsum Dtarget by rfl,
      reluApproxPadDepth_parameterCount]
    apply fullyConnectedReLUParameterCount_mono_width
    simpa [W0, phaseCard, Phase] using hNsumWidth
  · intro x hx
    have hfamily := two_scale_phase_family_holder_error
      hd hMtwo hbeta_pos hC_nonneg orderC orderF f hf
      (fun phase : Phase => approx phase x) x hx (by
        intro phase
        have hs := (hphaseSpec phase).2.2.2.2 x hx
        change |approx phase x - _| <= _
        rw [show approx phase x = (padded phase).realize x by rfl]
        rw [reluApproxPadDepth_realize (phaseNet phase) D0
          (hphaseSpec phase).2.1 x]
        simpa [T, Kphase] using hs)
    have halpha : 0 <= alpha := by
      dsimp [alpha]
      positivity
    have hinv_nonneg :
        0 <= (((M ^ 2 - 1 : Nat) : Real)⁻¹) := by positivity
    have hinv_le_two :
        (((M ^ 2 - 1 : Nat) : Real)⁻¹) <=
          2 * (((M ^ 2 - 1 : Nat) : Real)⁻¹) := by
      linarith
    have htaylorPow :
        Real.rpow (((M ^ 2 - 1 : Nat) : Real)⁻¹) alpha <=
          Real.rpow 4 alpha * shallowReLUResolutionRate M r beta := by
      exact le_trans (Real.rpow_le_rpow hinv_nonneg hinv_le_two halpha)
        (two_inv_grid_rpow_le_shallow_rate
          (r := r) hMtwo hbeta_pos.le)
    have hCfactor : 0 <= C / (Nat.factorial r : Real) :=
      div_nonneg hC_nonneg hfactorial.le
    have hrate : 0 <= shallowReLUResolutionRate M r beta := by
      unfold shallowReLUResolutionRate
      exact Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le M)) _
    have herror :
        |Finset.univ.sum (fun phase : Phase => approx phase x) - f x| <=
          cState * shallowReLUResolutionRate M r beta := by
      calc
        |Finset.univ.sum (fun phase : Phase => approx phase x) - f x| <=
            (phaseCard : Real) *
                (Kphase * shallowReLUResolutionRate M r beta) +
              (C / (Nat.factorial r : Real)) *
                Real.rpow (((M ^ 2 - 1 : Nat) : Real)⁻¹) alpha := by
          simpa [Phase, phaseCard, alpha, T, Kphase] using hfamily
        _ <= (phaseCard : Real) *
                (Kphase * shallowReLUResolutionRate M r beta) +
              Ktaylor * shallowReLUResolutionRate M r beta := by
          exact add_le_add le_rfl (by
            calc
              (C / (Nat.factorial r : Real)) *
                  Real.rpow (((M ^ 2 - 1 : Nat) : Real)⁻¹) alpha <=
                  (C / (Nat.factorial r : Real)) *
                    (Real.rpow 4 alpha * shallowReLUResolutionRate M r beta) :=
                mul_le_mul_of_nonneg_left htaylorPow hCfactor
              _ = Ktaylor * shallowReLUResolutionRate M r beta := by
                dsimp [Ktaylor]
                ring)
        _ = ((phaseCard : Real) * Kphase + Ktaylor) *
              shallowReLUResolutionRate M r beta := by ring
        _ <= cState * shallowReLUResolutionRate M r beta := by
          apply mul_le_mul_of_nonneg_right _ hrate
          dsimp [cState]
          linarith
    rw [show N = reluApproxPadDepth Nsum Dtarget by rfl,
      reluApproxPadDepth_realize Nsum Dtarget hNsumDepthTarget x,
      hNsumRealize]
    simpa [approx] using herror

end Statlib.Nonparametric.Approximation.NeuralNetworkAlgebra

namespace Statlib.Nonparametric.Approximation

open NeuralNetworkAlgebra

/-- Fixed-width fully connected ReLU networks uniformly approximate every
function in a Holder-smooth ball on the unit cube at the shallow-network rate
`(L * W^2)^(-2(r + beta) / d)`. -/
theorem holder_smooth_shallow_relu_neural_network_approximation
    {d r : ℕ} {beta C B : ℝ}
    (hd : 0 < d)
    (hbeta_pos : 0 < beta) (hbeta_le_one : beta ≤ 1)
    (hC_nonneg : 0 ≤ C) (hB_nonneg : 0 ≤ B) :
    ∃ W M0 : ℕ,
      0 < W ∧ 0 < M0 ∧
      ∃ cRate : ℝ, 0 < cRate ∧
        ∀ M : ℕ, M0 ≤ M →
          ∃ L P : ℕ,
            0 < L ∧
            P = fullyConnectedReLUParameterCount d L W ∧
            ∀ f : (Fin d → ℝ) → ℝ,
              f ∈ holderSmoothBall r beta C B →
                ∃ g : (Fin d → ℝ) → ℝ,
                  g ∈ reluNetworkClass d L W P ∧
                  ∀ x : Fin d → ℝ, x ∈ unitCubeSet d →
                    |g x - f x| ≤
                      cRate *
                        (((L : ℝ) * (W : ℝ) ^ 2).rpow
                          (-(2 * ((r : ℝ) + beta) / (d : ℝ)))) := by
  obtain ⟨W, M0, Dblock, hW, hM0, hDblock, cState, hcState, hApprox⟩ :=
    holder_smooth_shallow_relu_neural_network_approximation_at_resolution
      hd hbeta_pos hbeta_le_one hC_nonneg hB_nonneg
  let smoothness : ℝ := (r : ℝ) + beta
  let exponent : ℝ := 2 * smoothness / (d : ℝ)
  let architectureScale : ℝ := ((Dblock + 1 : ℕ) : ℝ) * (W : ℝ) ^ 2
  let cRate : ℝ := cState * architectureScale ^ exponent
  have hsmoothness_pos : 0 < smoothness := by
    dsimp [smoothness]
    positivity
  have hd_real : 0 < (d : ℝ) := by exact_mod_cast hd
  have hd_real_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_real
  have hexponent_pos : 0 < exponent := by
    exact div_pos (mul_pos two_pos hsmoothness_pos) hd_real
  have hscale_pos : 0 < architectureScale := by
    dsimp [architectureScale]
    positivity
  have hcRate_pos : 0 < cRate := by
    exact mul_pos hcState (Real.rpow_pos_of_pos hscale_pos exponent)
  refine ⟨W, M0, hW, hM0, cRate, hcRate_pos, ?_⟩
  intro M hM
  have hM_pos : 0 < M := lt_of_lt_of_le hM0 hM
  have hM_real_pos : 0 < (M : ℝ) := by exact_mod_cast hM_pos
  have hM_real_nonneg : 0 ≤ (M : ℝ) := hM_real_pos.le
  let L : ℕ := M ^ d * (Dblock + 1)
  let P : ℕ := fullyConnectedReLUParameterCount d L W
  have hL_pos : 0 < L := by
    dsimp [L]
    positivity
  refine ⟨L, P, hL_pos, rfl, ?_⟩
  intro f hf
  obtain ⟨N, hNdepth, hNwidth, hNparameter, hNerror⟩ := hApprox M hM f hf
  refine ⟨N.realize, ?_, ?_⟩
  · refine ⟨N, ?_, ?_, hNwidth, ?_, fun _ => rfl⟩
    · rw [hNdepth]
      exact hL_pos
    · rw [hNdepth]
    · simpa [P, L] using hNparameter
  · intro x hx
    have hbase := hNerror x hx
    have hM_power :
        ((M : ℝ) ^ d) ^ (-exponent) =
          (M : ℝ) ^ (-(2 * smoothness)) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hM_real_nonneg]
      congr 1
      dsimp [exponent]
      field_simp [hd_real_ne]
    have hL_real : (L : ℝ) = (M : ℝ) ^ d * ((Dblock + 1 : ℕ) : ℝ) := by
      simp [L]
    have hsize :
        (L : ℝ) * (W : ℝ) ^ 2 = (M : ℝ) ^ d * architectureScale := by
      rw [hL_real]
      dsimp [architectureScale]
      ring
    have hrate_identity :
        cRate *
            (((L : ℝ) * (W : ℝ) ^ 2) ^ (-exponent)) =
          cState * shallowReLUResolutionRate M r beta := by
      rw [hsize]
      rw [Real.mul_rpow (pow_nonneg hM_real_nonneg d) hscale_pos.le]
      rw [hM_power]
      dsimp [cRate]
      rw [show shallowReLUResolutionRate M r beta =
          (M : ℝ) ^ (-(2 * smoothness)) by rfl]
      calc
        (cState * architectureScale ^ exponent) *
              ((M : ℝ) ^ (-(2 * smoothness)) *
                architectureScale ^ (-exponent)) =
            cState * (M : ℝ) ^ (-(2 * smoothness)) *
              (architectureScale ^ exponent *
                architectureScale ^ (-exponent)) := by ring
        _ = cState * (M : ℝ) ^ (-(2 * smoothness)) *
              architectureScale ^ (exponent + -exponent) := by
            rw [← Real.rpow_add hscale_pos]
        _ = cState * (M : ℝ) ^ (-(2 * smoothness)) := by
            ring_nf
            rw [Real.rpow_zero]
            ring
    calc
      |N.realize x - f x| ≤ cState * shallowReLUResolutionRate M r beta := hbase
      _ = cRate *
          (((L : ℝ) * (W : ℝ) ^ 2).rpow
            (-(2 * ((r : ℝ) + beta) / (d : ℝ)))) := by
        rw [show -(2 * ((r : ℝ) + beta) / (d : ℝ)) = -exponent by rfl]
        exact hrate_identity.symm

end Statlib.Nonparametric.Approximation
