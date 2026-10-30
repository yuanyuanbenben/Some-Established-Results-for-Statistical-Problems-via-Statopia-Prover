import Statlib.Nonparametric.Approximation.ReLUStateMachine

open scoped BigOperators
open Statlib.Nonparametric.Vocabulary

/-! # Two-Scale Geometry for Shallow ReLU Approximation

Shifted grids, boundary handling, and phasewise approximation estimates used
by the fixed-width shallow-network construction.
-/

namespace Statlib.Nonparametric.Approximation.NeuralNetworkAlgebra

/-- Unit-spaced ReLU hats indexed by all integers needed on `[0, 2K]` form a
partition of unity.  The extra right endpoint lets the same statement include
`z = 2K` without a separate boundary convention. -/
private theorem reluApprox_integerTent_sum_eq_one
    {K : Nat} (hK : 0 < K) (z : Real) (hz0 : 0 <= z)
    (hzK : z <= 2 * (K : Real)) :
    (Finset.univ.sum fun i : Fin (2 * (K + 1)) =>
      relu (1 - |z - (i.val : Real)|)) = 1 := by
  let n : Nat := Int.toNat (Int.floor z)
  have hn_cast : (n : Int) = Int.floor z := by
    dsimp [n]
    exact Int.toNat_of_nonneg (Int.floor_nonneg.mpr hz0)
  have hnR : (n : Real) = (Int.floor z : Real) := by
    exact_mod_cast hn_cast
  have hn_le : (n : Real) <= z := by
    rw [hnR]
    exact Int.floor_le z
  have hz_le : z < (n : Real) + 1 := by
    rw [hnR]
    exact Int.lt_floor_add_one z
  have hn_bound : n <= 2 * K := by
    exact_mod_cast (le_trans hn_le hzK)
  have hn_fin : n < 2 * (K + 1) := by omega
  have hn1_fin : n + 1 < 2 * (K + 1) := by omega
  let en : Fin (2 * (K + 1)) := ⟨n, hn_fin⟩
  let en1 : Fin (2 * (K + 1)) := ⟨n + 1, hn1_fin⟩
  have hen1_ne_en : en1 ≠ en := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [en, en1] at hv
    omega
  let g : Fin (2 * (K + 1)) -> Real :=
    fun i => relu (1 - |z - (i.val : Real)|)
  have hg_en : g en = 1 - (z - (n : Real)) := by
    have hdist0 : 0 <= z - (n : Real) := sub_nonneg.mpr hn_le
    have hrelu0 : 0 <= 1 - (z - (n : Real)) := by linarith
    simp [g, en, abs_of_nonneg hdist0, relu, max_eq_left hrelu0]
  have hg_en1 : g en1 = 1 - ((n : Real) + 1 - z) := by
    have hdist1 : z - ((n : Real) + 1) <= 0 := by linarith
    have hrelu1 : 0 <= 1 - ((n : Real) + 1 - z) := by linarith
    simp [g, en1, abs_of_nonpos hdist1, relu, max_eq_left hrelu1]
  have hzero : forall i : Fin (2 * (K + 1)), i ≠ en -> i ≠ en1 -> g i = 0 := by
    intro i hi_en hi_en1
    have hi_ne_n : i.val ≠ n := by
      intro h
      exact hi_en (Fin.ext h)
    have hi_ne_n1 : i.val ≠ n + 1 := by
      intro h
      exact hi_en1 (Fin.ext h)
    rcases lt_or_gt_of_ne hi_ne_n with hi_lt | hn_lt
    · have hi1_le : ((i.val : Nat) : Real) + 1 <= (n : Real) := by
        exact_mod_cast (Nat.succ_le_of_lt hi_lt)
      have hdist : 1 <= |z - (i.val : Real)| := by
        rw [abs_of_nonneg (by linarith : 0 <= z - (i.val : Real))]
        linarith
      simp [g, relu, max_eq_right (sub_nonpos.mpr hdist)]
    · have hn1_lt_i : n + 1 < i.val := by
        rcases lt_or_eq_of_le (Nat.succ_le_of_lt hn_lt) with hlt | heq
        · exact hlt
        · exact False.elim (hi_en1 (Fin.ext heq.symm))
      have hn2_le_i : (n : Real) + 2 <= (i.val : Real) := by
        exact_mod_cast (Nat.succ_le_of_lt hn1_lt_i)
      have hdist : 1 <= |z - (i.val : Real)| := by
        rw [abs_of_nonpos (by linarith : z - (i.val : Real) <= 0)]
        linarith
      simp [g, relu, max_eq_right (sub_nonpos.mpr hdist)]
  have hdecomp : (Finset.univ.sum g) =
      g en + g en1 +
        (Finset.sum (((Finset.univ : Finset (Fin (2 * (K + 1)))) \ {en}) \ {en1}) g) := by
    rw [Finset.sum_eq_add_sum_diff_singleton
      (s := (Finset.univ : Finset (Fin (2 * (K + 1)))))
      (i := en) (by simp)]
    rw [Finset.sum_eq_add_sum_diff_singleton
      (s := ((Finset.univ : Finset (Fin (2 * (K + 1)))) \ {en}))
      (i := en1) (by simp [hen1_ne_en])]
    ring
  have hrest :
      Finset.sum (((Finset.univ : Finset (Fin (2 * (K + 1)))) \ {en}) \ {en1}) g = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton,
      true_and] at hi
    exact hzero i hi.1 hi.2
  change Finset.univ.sum g = 1
  rw [hdecomp, hrest, hg_en, hg_en1]
  ring

/-- Tensorization of `reluApprox_integerTent_sum_eq_one`. -/
private theorem reluApprox_integerTensorTent_sum_eq_one
    {d K : Nat} (hK : 0 < K) (z : Fin d -> Real)
    (hz0 : forall q, 0 <= z q) (hzK : forall q, z q <= 2 * (K : Real)) :
    (Finset.univ.sum fun v : Fin d -> Fin (2 * (K + 1)) =>
      Finset.univ.prod fun q : Fin d =>
        relu (1 - |z q - ((v q).val : Real)|)) = 1 := by
  calc
    (Finset.univ.sum fun v : Fin d -> Fin (2 * (K + 1)) =>
        Finset.univ.prod fun q : Fin d =>
          relu (1 - |z q - ((v q).val : Real)|)) =
        Finset.univ.prod fun q : Fin d =>
          Finset.univ.sum fun i : Fin (2 * (K + 1)) =>
            relu (1 - |z q - (i.val : Real)|) := by
      simpa [Fintype.piFinset_univ] using
        (Finset.sum_prod_piFinset
          (s := (Finset.univ : Finset (Fin (2 * (K + 1)))))
          (g := fun q i => relu (1 - |z q - (i.val : Real)|)))
    _ = Finset.univ.prod fun _q : Fin d => (1 : Real) := by
      apply Finset.prod_congr rfl
      intro q _hq
      exact reluApprox_integerTent_sum_eq_one hK (z q) (hz0 q) (hzK q)
    _ = 1 := by simp

/-- The affine change of variables from a shifted physical tent to the
unit-spaced integer tent used above. -/
private theorem reluApprox_coordinateTent_shifted_eq_integerTent
    {d K : Nat} (hK : 0 < K) (q : Fin d) (x : Fin d -> Real) (j : Nat) :
    coordinateTentReLUFunction q ((j : Real) / (K : Real) - 1) (K : Real) x =
      relu (1 - |(K : Real) * (x q + 1) - (j : Real)|) := by
  have hKR : (0 : Real) < (K : Real) := by exact_mod_cast hK
  have hKne : (K : Real) ≠ 0 := ne_of_gt hKR
  have hrelu_abs : forall y : Real, relu y + relu (-y) = |y| := by
    intro y
    by_cases hy : 0 <= y
    · simp [relu, max_eq_left hy, max_eq_right (by linarith : -y <= 0),
        abs_of_nonneg hy]
    · have hy' : y <= 0 := le_of_not_ge hy
      simp [relu, max_eq_right hy', max_eq_left (by linarith : 0 <= -y),
        abs_of_nonpos hy']
  unfold coordinateTentReLUFunction
  have hneg : ((j : Real) / (K : Real) - 1) - x q =
      -(x q - ((j : Real) / (K : Real) - 1)) := by ring
  rw [hneg, hrelu_abs]
  have habs :
      (K : Real) * |x q - ((j : Real) / (K : Real) - 1)| =
        |(K : Real) * (x q - ((j : Real) / (K : Real) - 1))| := by
    rw [abs_mul, abs_of_pos hKR]
  rw [habs]
  have halgebra :
      (K : Real) * (x q - ((j : Real) / (K : Real) - 1)) =
        (K : Real) * (x q + 1) - (j : Real) := by
    field_simp
    ring
  rw [halgebra]

/-! ## Explicit indexing of the shifted paper grid -/

/-- Split one base-`M^2` node into its coarse and fine base-`M` digits. -/
private def reluApproxPaperPairDigitEquiv (M : Nat) :
    Fin M × Fin M ≃ Fin (M ^ 2) :=
  finProdFinEquiv.trans (finCongr (by rw [pow_two]))

/-- Coordinatewise coarse/fine indexing of the unshifted node grid. -/
private noncomputable def reluApproxPaperNodeGridEquiv
    {d M : Nat} (orderC orderF : Fin (M ^ d) ≃ (Fin d -> Fin M)) :
    (Fin (M ^ d) × Fin (M ^ d)) ≃ (Fin d -> Fin (M ^ 2)) :=
  (orderC.prodCongr orderF).trans
    ((Equiv.arrowProdEquivProdArrow
      (Fin d) (fun _ => Fin M) (fun _ => Fin M)).symm.trans
        (Equiv.piCongrRight fun _ => reluApproxPaperPairDigitEquiv M))

/-- Interlace the two one-dimensional shifts at every base-`M^2` node. -/
private def reluApproxPaperPhaseDigitEquiv (M : Nat) :
    Fin (M ^ 2) × Fin 2 ≃ Fin (2 * M ^ 2) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm (M ^ 2) 2))

/-- The `2^d` shifted coarse/fine indices are exactly the integer tensor grid
with `2 * M^2` entries in every coordinate. -/
private noncomputable def reluApproxPhaseShiftedGridEquiv
    {d M : Nat} (orderC orderF : Fin (M ^ d) ≃ (Fin d -> Fin M)) :
    ((Fin d -> Fin 2) × (Fin (M ^ d) × Fin (M ^ d))) ≃
      (Fin d -> Fin (2 * M ^ 2)) :=
  ((Equiv.refl (Fin d -> Fin 2)).prodCongr
      (reluApproxPaperNodeGridEquiv orderC orderF)).trans
    ((Equiv.prodComm (Fin d -> Fin 2) (Fin d -> Fin (M ^ 2))).trans
      ((Equiv.arrowProdEquivProdArrow
        (Fin d) (fun _ => Fin (M ^ 2)) (fun _ => Fin 2)).symm.trans
          (Equiv.piCongrRight fun _ => reluApproxPaperPhaseDigitEquiv M)))

private theorem reluApproxPhaseShiftedGridEquiv_val
    {d M : Nat} (orderC orderF : Fin (M ^ d) ≃ (Fin d -> Fin M))
    (phase : Fin d -> Fin 2) (b t : Fin (M ^ d)) (q : Fin d) :
    (reluApproxPhaseShiftedGridEquiv orderC orderF (phase, (b, t)) q).val =
      2 * ((orderC b q).val * M + (orderF t q).val) + (phase q).val := by
  simp [reluApproxPhaseShiftedGridEquiv,
    reluApproxPaperNodeGridEquiv, reluApproxPaperPairDigitEquiv,
    reluApproxPaperPhaseDigitEquiv, finProdFinEquiv]
  ring

/-- Every point of `[0,2K]` lies within one half-unit of one of the integer
nodes carried by `Fin (2 * (K + 1))`. -/
private theorem exists_reluApprox_nearbyIntegerNode
    {K : Nat} (z : Real) (hz0 : 0 <= z) (hzK : z <= 2 * (K : Real)) :
    exists j : Fin (2 * (K + 1)), |z - (j.val : Real)| <= (2 : Real)⁻¹ := by
  let n : Nat := Int.toNat (Int.floor (z + (2 : Real)⁻¹))
  have hhalf : (2 : Real)⁻¹ = 1 / 2 := by norm_num
  have hfloor_nonneg : 0 <= Int.floor (z + (2 : Real)⁻¹) := by
    apply Int.floor_nonneg.mpr
    positivity
  have hn_cast : (n : Int) = Int.floor (z + (2 : Real)⁻¹) := by
    dsimp [n]
    exact Int.toNat_of_nonneg hfloor_nonneg
  have hnR : (n : Real) = (Int.floor (z + (2 : Real)⁻¹) : Real) := by
    exact_mod_cast hn_cast
  have hn_le : (n : Real) <= z + (2 : Real)⁻¹ := by
    rw [hnR]
    exact Int.floor_le _
  have hz_lt : z + (2 : Real)⁻¹ < (n : Real) + 1 := by
    rw [hnR]
    exact Int.lt_floor_add_one _
  have hn_lt_boundR : (n : Real) < (2 * K + 1 : Nat) := by
    push_cast
    rw [hhalf] at hn_le hz_lt
    norm_num at hn_le hz_lt ⊢
    nlinarith
  have hn_lt_bound : n < 2 * K + 1 := by
    exact_mod_cast hn_lt_boundR
  have hn_fin : n < 2 * (K + 1) := by omega
  refine ⟨⟨n, hn_fin⟩, ?_⟩
  rw [abs_le]
  rw [hhalf] at hn_le hz_lt ⊢
  constructor <;> norm_num <;> linarith

/-- Center of one cell in one of the `2^d` shifted paper partitions. -/
noncomputable def twoScaleShiftedCenter
    (M : Nat) (orderC orderF : Fin (M ^ d) ≃ (Fin d -> Fin M))
    (phase : Fin d -> Fin 2) (b t : Fin (M ^ d)) (q : Fin d) : Real :=
  let K : Nat := M ^ 2 - 1
  let node : Nat := (orderC b q).val * M + (orderF t q).val
  ((2 * node + (phase q).val : Nat) : Real) / (K : Real) - 1

/-- Shifted paper-grid centers stay in a fixed box, uniformly in the mesh
resolution and in all coarse, fine, and phase indices. -/
private theorem abs_twoScaleShiftedCenter_le_two
    {d M : Nat} (hM : 2 <= M)
    (orderC orderF : Fin (M ^ d) ≃ (Fin d -> Fin M))
    (phase : Fin d -> Fin 2) (b t : Fin (M ^ d)) (q : Fin d) :
    |twoScaleShiftedCenter M orderC orderF phase b t q| <= 2 := by
  let K : Nat := M ^ 2 - 1
  let node : Nat := (orderC b q).val * M + (orderF t q).val
  have hMpos : 0 < M := by omega
  have hnode_lt : node < M * M := by
    calc
      node < (orderC b q).val * M + M := by
        dsimp [node]
        exact Nat.add_lt_add_left (orderF t q).isLt _
      _ = ((orderC b q).val + 1) * M := by ring
      _ <= M * M := Nat.mul_le_mul_right M (Nat.succ_le_of_lt (orderC b q).isLt)
  have hnode : node <= K := by
    dsimp [K]
    rw [pow_two]
    exact Nat.le_sub_one_of_lt hnode_lt
  have hK : 0 < K := by
    dsimp [K]
    have hMM : 4 <= M * M := Nat.mul_le_mul hM hM
    simpa [pow_two] using (show 0 < M * M - 1 by omega)
  have hKR : (0 : Real) < (K : Real) := by exact_mod_cast hK
  have hnum :
      ((2 * node + (phase q).val : Nat) : Real) <= 2 * (K : Real) + 1 := by
    have hnumNat : 2 * node + (phase q).val <= 2 * K + 1 := by omega
    exact_mod_cast hnumNat
  have hnum_nonneg :
      (0 : Real) <= ((2 * node + (phase q).val : Nat) : Real) := by positivity
  have hquot_nonneg :
      (0 : Real) <= ((2 * node + (phase q).val : Nat) : Real) / (K : Real) :=
    div_nonneg hnum_nonneg hKR.le
  have hquot_le_three :
      ((2 * node + (phase q).val : Nat) : Real) / (K : Real) <= 3 := by
    apply (div_le_iff₀ hKR).2
    have hKone : (1 : Real) <= (K : Real) := by exact_mod_cast (show 1 <= K by omega)
    nlinarith
  unfold twoScaleShiftedCenter
  dsimp only
  rw [abs_le]
  constructor <;> nlinarith

/-- Every shifted paper tent has reciprocal radius `M^2 - 1`. -/
noncomputable def twoScaleShiftedScale (M : Nat)
    (_phase : Fin d -> Fin 2) (_b _t : Fin (M ^ d)) (_q : Fin d) : Real :=
  ((M ^ 2 - 1 : Nat) : Real)

/-- Every point of the unit cube has a shifted coarse/fine center at distance
at most half of the fine-cell radius in every coordinate. -/
private theorem exists_twoScaleShiftedCenter_near
    {d M : Nat} (hM : 2 <= M)
    (orderC orderF : Fin (M ^ d) ≃ (Fin d -> Fin M))
    (x : Fin d -> Real) (hx : forall q : Fin d, x q ∈ Set.Icc (0 : Real) 1) :
    exists (phase : Fin d -> Fin 2) (b t : Fin (M ^ d)),
      forall q : Fin d,
        |x q - twoScaleShiftedCenter M orderC orderF phase b t q| <=
          (2 * ((M ^ 2 - 1 : Nat) : Real))⁻¹ := by
  classical
  let K : Nat := M ^ 2 - 1
  have hK : 0 < K := by
    dsimp [K]
    have hM2 : 4 <= M ^ 2 := by
      have hm := Nat.mul_le_mul hM hM
      norm_num at hm
      simpa [pow_two] using hm
    omega
  have hKR : (0 : Real) < (K : Real) := by exact_mod_cast hK
  have hKRne : (K : Real) ≠ 0 := ne_of_gt hKR
  have hKsucc : K + 1 = M ^ 2 := by
    dsimp [K]
    omega
  have hcard : 2 * (K + 1) = 2 * M ^ 2 := by rw [hKsucc]
  let z : Fin d -> Real := fun q => (K : Real) * (x q + 1)
  have hz0 : forall q, 0 <= z q := by
    intro q
    dsimp [z]
    exact mul_nonneg hKR.le (by linarith [(Set.mem_Icc.mp (hx q)).1])
  have hzK : forall q, z q <= 2 * (K : Real) := by
    intro q
    dsimp [z]
    nlinarith [(Set.mem_Icc.mp (hx q)).2]
  choose j hj using fun q =>
    exists_reluApprox_nearbyIntegerNode (K := K) (z q) (hz0 q) (hzK q)
  let v : Fin d -> Fin (2 * M ^ 2) := fun q => Fin.cast hcard (j q)
  let p := (reluApproxPhaseShiftedGridEquiv orderC orderF).symm v
  refine ⟨p.1, p.2.1, p.2.2, ?_⟩
  intro q
  have hp := congrArg Fin.val
    (congrFun ((reluApproxPhaseShiftedGridEquiv orderC orderF).apply_symm_apply v) q)
  have hvj : (v q).val = (j q).val := by simp [v]
  have hindex :
      (j q).val =
        2 * ((orderC p.2.1 q).val * M + (orderF p.2.2 q).val) +
          (p.1 q).val := by
    rw [← hvj, ← hp]
    exact reluApproxPhaseShiftedGridEquiv_val orderC orderF
      p.1 p.2.1 p.2.2 q
  have halgebra :
      x q - twoScaleShiftedCenter M orderC orderF p.1 p.2.1 p.2.2 q =
        (K : Real)⁻¹ * (z q - ((j q).val : Real)) := by
    unfold twoScaleShiftedCenter
    dsimp only
    rw [← hindex]
    change x q - (((j q).val : Real) / (K : Real) - 1) =
      (K : Real)⁻¹ * ((K : Real) * (x q + 1) - ((j q).val : Real))
    field_simp [hKRne]
    ring
  rw [halgebra, abs_mul, abs_of_pos (inv_pos.mpr hKR)]
  calc
    (K : Real)⁻¹ * |z q - ((j q).val : Real)| <=
        (K : Real)⁻¹ * (2 : Real)⁻¹ :=
      mul_le_mul_of_nonneg_left (hj q) (inv_nonneg.mpr hKR.le)
    _ = (2 * ((M ^ 2 - 1 : Nat) : Real))⁻¹ := by
      change (K : Real)⁻¹ * (2 : Real)⁻¹ = (2 * (K : Real))⁻¹
      field_simp [hKRne]

private noncomputable def reluApproxPhaseShiftedFineLower
    (M : Nat) (orderC orderF : Fin (M ^ d) ≃ (Fin d -> Fin M))
    (phase : Fin d -> Fin 2) (b t : Fin (M ^ d)) (q : Fin d) : Real :=
  twoScaleShiftedCenter M orderC orderF phase b t q -
    ((M ^ 2 - 1 : Nat) : Real)⁻¹

private noncomputable def reluApproxPhaseShiftedFineUpper
    (M : Nat) (orderC orderF : Fin (M ^ d) ≃ (Fin d -> Fin M))
    (phase : Fin d -> Fin 2) (b t : Fin (M ^ d)) (q : Fin d) : Real :=
  twoScaleShiftedCenter M orderC orderF phase b t q +
    ((M ^ 2 - 1 : Nat) : Real)⁻¹

/-- A sufficiently sharp selector has a genuinely safe shifted fine cell at
every point of the unit cube. -/
private theorem exists_reluApproxPhaseShiftedFineCell_safe
    {d M : Nat} (hM : 2 <= M)
    (orderC orderF : Fin (M ^ d) ≃ (Fin d -> Fin M))
    (R : Real)
    (hmargin : R⁻¹ <= (2 * ((M ^ 2 - 1 : Nat) : Real))⁻¹)
    (x : Fin d -> Real) (hx : forall q : Fin d, x q ∈ Set.Icc (0 : Real) 1) :
    exists (phase : Fin d -> Fin 2) (b t : Fin (M ^ d)),
      forall q : Fin d,
        reluApproxPhaseShiftedFineLower M orderC orderF phase b t q + R⁻¹ <= x q /\
          x q <= reluApproxPhaseShiftedFineUpper M orderC orderF phase b t q - R⁻¹ := by
  obtain ⟨phase, b, t, hnear⟩ :=
    exists_twoScaleShiftedCenter_near hM orderC orderF x hx
  refine ⟨phase, b, t, ?_⟩
  intro q
  let K : Nat := M ^ 2 - 1
  have hK : 0 < K := by
    dsimp [K]
    have hM2 : 4 <= M ^ 2 := by
      have hm := Nat.mul_le_mul hM hM
      norm_num at hm
      simpa [pow_two] using hm
    omega
  have hKR : (0 : Real) < (K : Real) := by exact_mod_cast hK
  have hdouble : (K : Real)⁻¹ =
      2 * (2 * (K : Real))⁻¹ := by
    field_simp [ne_of_gt hKR]
  have hnear' :
      |x q - twoScaleShiftedCenter M orderC orderF phase b t q| <=
        (2 * (K : Real))⁻¹ := by
    simpa [K] using hnear q
  have habs := (abs_le.mp hnear')
  have hmargin' : R⁻¹ <= (2 * (K : Real))⁻¹ := by
    simpa [K] using hmargin
  unfold reluApproxPhaseShiftedFineLower
  unfold reluApproxPhaseShiftedFineUpper
  change
    twoScaleShiftedCenter M orderC orderF phase b t q - (K : Real)⁻¹ + R⁻¹ <= x q /\
      x q <= twoScaleShiftedCenter M orderC orderF phase b t q + (K : Real)⁻¹ - R⁻¹
  rw [hdouble]
  constructor <;> linarith

/-- Within one phase and one coarse block, distinct fine cells have disjoint
interiors. -/
private theorem reluApprox_phaseShiftedFineBoxes_pairwise_disjoint
    {d M : Nat} (hM : 2 <= M)
    (orderC orderF : Fin (M ^ d) ≃ (Fin d -> Fin M))
    (phase : Fin d -> Fin 2) (b : Fin (M ^ d)) :
    forall t u : Fin (M ^ d), t ≠ u -> exists q : Fin d,
      reluApproxPhaseShiftedFineUpper M orderC orderF phase b t q <=
          reluApproxPhaseShiftedFineLower M orderC orderF phase b u q \/
        reluApproxPhaseShiftedFineUpper M orderC orderF phase b u q <=
          reluApproxPhaseShiftedFineLower M orderC orderF phase b t q := by
  let K : Nat := M ^ 2 - 1
  have hK : 0 < K := by
    dsimp [K]
    have hM2 : 4 <= M ^ 2 := by
      have hm := Nat.mul_le_mul hM hM
      norm_num at hm
      simpa [pow_two] using hm
    omega
  have hKR : (0 : Real) < (K : Real) := by exact_mod_cast hK
  intro t u htu
  have horders_ne : orderF t ≠ orderF u := fun h => htu (orderF.injective h)
  have hcoord : exists q : Fin d, (orderF t q).val ≠ (orderF u q).val := by
    by_contra hnone
    push_neg at hnone
    apply horders_ne
    funext q
    exact Fin.ext (hnone q)
  rcases hcoord with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  have hsep : forall {n m : Nat}, n < m ->
      (((2 * n + (phase q).val : Nat) : Real) / (K : Real) - 1) +
          (K : Real)⁻¹ <=
        (((2 * m + (phase q).val : Nat) : Real) / (K : Real) - 1) -
          (K : Real)⁻¹ := by
    intro n m hnm
    have hnmR : (n : Real) + 1 <= (m : Real) := by
      exact_mod_cast (Nat.succ_le_of_lt hnm)
    have hnumR :
        2 * (n : Real) + ((phase q).val : Real) + 1 <=
          2 * (m : Real) + ((phase q).val : Real) - 1 := by
      linarith
    have hleft :
        (((2 * n + (phase q).val : Nat) : Real) / (K : Real) - 1) +
            (K : Real)⁻¹ =
          (2 * (n : Real) + ((phase q).val : Real) + 1) / (K : Real) - 1 := by
      push_cast
      field_simp
      ring
    have hright :
        (((2 * m + (phase q).val : Nat) : Real) / (K : Real) - 1) -
            (K : Real)⁻¹ =
          (2 * (m : Real) + ((phase q).val : Real) - 1) / (K : Real) - 1 := by
      push_cast
      field_simp
      ring
    rw [hleft, hright]
    exact sub_le_sub_right ((div_le_div_iff_of_pos_right hKR).2 hnumR) 1
  rcases lt_or_gt_of_ne hq with hlt | hgt
  · left
    unfold reluApproxPhaseShiftedFineUpper
    unfold reluApproxPhaseShiftedFineLower
    apply hsep
    exact Nat.add_lt_add_left hlt ((orderC b q).val * M)
  · right
    unfold reluApproxPhaseShiftedFineUpper
    unfold reluApproxPhaseShiftedFineLower
    apply hsep
    exact Nat.add_lt_add_left hgt ((orderC b q).val * M)

/-- Outside the safely shrunken part of a shifted fine cell, its tensor-tent
weight is controlled by the width of the selector transition strip.  Choosing
`R` at the paper scale therefore makes every boundary-shell contribution have
the target `M^(-2p)` size. -/
private theorem reluApproxPhaseShiftedTentWeight_le_selector_margin
    {d M : Nat} (hM : 2 <= M)
    (orderC orderF : Fin (M ^ d) ≃ (Fin d -> Fin M))
    (phase : Fin d -> Fin 2) (b t : Fin (M ^ d))
    {R : Real} (hR : 0 < R) (x : Fin d -> Real)
    (hunsafe : ¬ forall q : Fin d,
      reluApproxPhaseShiftedFineLower M orderC orderF phase b t q + R⁻¹ <= x q /\
        x q <= reluApproxPhaseShiftedFineUpper M orderC orderF phase b t q - R⁻¹) :
    axisAlignedBoxTentWeight
        (twoScaleShiftedCenter M orderC orderF phase b t)
        (twoScaleShiftedScale M phase b t) x <=
      ((M ^ 2 - 1 : Nat) : Real) * R⁻¹ := by
  classical
  let K : Nat := M ^ 2 - 1
  have hK : 0 < K := by
    dsimp [K]
    have hM2 : 4 <= M ^ 2 := by
      have hm := Nat.mul_le_mul hM hM
      norm_num at hm
      simpa [pow_two] using hm
    omega
  have hKR : (0 : Real) < (K : Real) := by exact_mod_cast hK
  have hKinv : (K : Real) * (K : Real)⁻¹ = 1 :=
    mul_inv_cancel₀ (ne_of_gt hKR)
  have hRinv : 0 <= R⁻¹ := (inv_pos.mpr hR).le
  push_neg at hunsafe
  obtain ⟨q, hunsafe_q⟩ := hunsafe
  by_cases hleftsafe :
      reluApproxPhaseShiftedFineLower M orderC orderF phase b t q + R⁻¹ <= x q
  · have hright :
        reluApproxPhaseShiftedFineUpper M orderC orderF phase b t q - R⁻¹ < x q :=
      hunsafe_q hleftsafe
    have harg :
        1 - (K : Real) *
            (relu (x q - twoScaleShiftedCenter M orderC orderF phase b t q) +
              relu (twoScaleShiftedCenter M orderC orderF phase b t q - x q)) <=
          (K : Real) * R⁻¹ := by
      unfold reluApproxPhaseShiftedFineUpper at hright
      have hrelu :
          x q - twoScaleShiftedCenter M orderC orderF phase b t q <=
            relu (x q - twoScaleShiftedCenter M orderC orderF phase b t q) :=
        le_max_left _ _
      have hother :
          0 <= relu (twoScaleShiftedCenter M orderC orderF phase b t q - x q) :=
        le_max_right _ _
      dsimp [K] at hright hKinv ⊢
      nlinarith
    have hfactor :
        coordinateTentReLUFunction q
            (twoScaleShiftedCenter M orderC orderF phase b t q)
            (twoScaleShiftedScale M phase b t q) x <=
          (K : Real) * R⁻¹ := by
      unfold coordinateTentReLUFunction relu
      simp only [twoScaleShiftedScale]
      exact max_le harg (mul_nonneg hKR.le hRinv)
    unfold axisAlignedBoxTentWeight
    rw [← Finset.mul_prod_erase Finset.univ
      (fun u : Fin d => coordinateTentReLUFunction u
        (twoScaleShiftedCenter M orderC orderF phase b t u)
        (twoScaleShiftedScale M phase b t u) x)
      (Finset.mem_univ q)]
    calc
      coordinateTentReLUFunction q
            (twoScaleShiftedCenter M orderC orderF phase b t q)
            (twoScaleShiftedScale M phase b t q) x *
          ∏ u ∈ Finset.univ.erase q,
            coordinateTentReLUFunction u
              (twoScaleShiftedCenter M orderC orderF phase b t u)
              (twoScaleShiftedScale M phase b t u) x <=
          coordinateTentReLUFunction q
            (twoScaleShiftedCenter M orderC orderF phase b t q)
            (twoScaleShiftedScale M phase b t q) x * 1 := by
        apply mul_le_mul_of_nonneg_left
        · apply Finset.prod_le_one
          · intro u _hu
            unfold coordinateTentReLUFunction relu
            exact le_max_right _ _
          · intro u _hu
            unfold coordinateTentReLUFunction relu
            exact max_le (by
              have hnonneg : 0 <=
                  (twoScaleShiftedScale M phase b t u) *
                    (max (x u - twoScaleShiftedCenter M orderC orderF phase b t u) 0 +
                      max (twoScaleShiftedCenter M orderC orderF phase b t u - x u) 0) := by
                positivity
              linarith) (by norm_num)
        · unfold coordinateTentReLUFunction relu
          exact le_max_right _ _
      _ <= (K : Real) * R⁻¹ := by simpa using hfactor
  · have hleft :
        x q < reluApproxPhaseShiftedFineLower M orderC orderF phase b t q + R⁻¹ :=
      lt_of_not_ge hleftsafe
    have harg :
        1 - (K : Real) *
            (relu (x q - twoScaleShiftedCenter M orderC orderF phase b t q) +
              relu (twoScaleShiftedCenter M orderC orderF phase b t q - x q)) <=
          (K : Real) * R⁻¹ := by
      unfold reluApproxPhaseShiftedFineLower at hleft
      have hrelu :
          twoScaleShiftedCenter M orderC orderF phase b t q - x q <=
            relu (twoScaleShiftedCenter M orderC orderF phase b t q - x q) :=
        le_max_left _ _
      have hother :
          0 <= relu (x q - twoScaleShiftedCenter M orderC orderF phase b t q) :=
        le_max_right _ _
      dsimp [K] at hleft hKinv ⊢
      nlinarith
    have hfactor :
        coordinateTentReLUFunction q
            (twoScaleShiftedCenter M orderC orderF phase b t q)
            (twoScaleShiftedScale M phase b t q) x <=
          (K : Real) * R⁻¹ := by
      unfold coordinateTentReLUFunction relu
      simp only [twoScaleShiftedScale]
      exact max_le harg (mul_nonneg hKR.le hRinv)
    unfold axisAlignedBoxTentWeight
    rw [← Finset.mul_prod_erase Finset.univ
      (fun u : Fin d => coordinateTentReLUFunction u
        (twoScaleShiftedCenter M orderC orderF phase b t u)
        (twoScaleShiftedScale M phase b t u) x)
      (Finset.mem_univ q)]
    calc
      coordinateTentReLUFunction q
            (twoScaleShiftedCenter M orderC orderF phase b t q)
            (twoScaleShiftedScale M phase b t q) x *
          ∏ u ∈ Finset.univ.erase q,
            coordinateTentReLUFunction u
              (twoScaleShiftedCenter M orderC orderF phase b t u)
              (twoScaleShiftedScale M phase b t u) x <=
          coordinateTentReLUFunction q
            (twoScaleShiftedCenter M orderC orderF phase b t q)
            (twoScaleShiftedScale M phase b t q) x * 1 := by
        apply mul_le_mul_of_nonneg_left
        · apply Finset.prod_le_one
          · intro u _hu
            unfold coordinateTentReLUFunction relu
            exact le_max_right _ _
          · intro u _hu
            unfold coordinateTentReLUFunction relu
            exact max_le (by
              have hnonneg : 0 <=
                  (twoScaleShiftedScale M phase b t u) *
                    (max (x u - twoScaleShiftedCenter M orderC orderF phase b t u) 0 +
                      max (twoScaleShiftedCenter M orderC orderF phase b t u - x u) 0) := by
                positivity
              linarith) (by norm_num)
        · unfold coordinateTentReLUFunction relu
          exact le_max_right _ _
      _ <= (K : Real) * R⁻¹ := by simpa using hfactor

private noncomputable def reluApproxPhaseShiftedCoarseLower
    (M : Nat) (orderC : Fin (M ^ d) ≃ (Fin d -> Fin M))
    (phase : Fin d -> Fin 2) (b : Fin (M ^ d)) (q : Fin d) : Real :=
  let K : Nat := M ^ 2 - 1
  (2 * ((orderC b q).val : Real) * (M : Real) + ((phase q).val : Real)) /
      (K : Real) - 1 - (K : Real)⁻¹

private noncomputable def reluApproxPhaseShiftedCoarseUpper
    (M : Nat) (orderC : Fin (M ^ d) ≃ (Fin d -> Fin M))
    (phase : Fin d -> Fin 2) (b : Fin (M ^ d)) (q : Fin d) : Real :=
  let K : Nat := M ^ 2 - 1
  (2 * (((orderC b q).val : Real) * (M : Real) + (M : Real) - 1) +
      ((phase q).val : Real)) / (K : Real) - 1 + (K : Real)⁻¹

/-- The fine box indexed by `t` is contained in its coarse block. -/
private theorem reluApproxPhaseShiftedFineBox_subset_coarse
    {d M : Nat} (hM : 2 <= M)
    (orderC orderF : Fin (M ^ d) ≃ (Fin d -> Fin M))
    (phase : Fin d -> Fin 2) (b t : Fin (M ^ d)) (q : Fin d) :
    reluApproxPhaseShiftedCoarseLower M orderC phase b q <=
        reluApproxPhaseShiftedFineLower M orderC orderF phase b t q /\
      reluApproxPhaseShiftedFineUpper M orderC orderF phase b t q <=
        reluApproxPhaseShiftedCoarseUpper M orderC phase b q := by
  let K : Nat := M ^ 2 - 1
  have hK : 0 < K := by
    dsimp [K]
    have hM2 : 4 <= M ^ 2 := by
      have hm := Nat.mul_le_mul hM hM
      norm_num at hm
      simpa [pow_two] using hm
    omega
  have hKR : (0 : Real) < (K : Real) := by exact_mod_cast hK
  have ht_le : ((orderF t q).val : Real) <= (M : Real) - 1 := by
    have ht_succ : (orderF t q).val + 1 <= M := by omega
    have ht_succR : ((orderF t q).val : Real) + 1 <= (M : Real) := by
      exact_mod_cast ht_succ
    linarith
  constructor
  · unfold reluApproxPhaseShiftedCoarseLower
    unfold reluApproxPhaseShiftedFineLower
    unfold twoScaleShiftedCenter
    dsimp only
    have hnum :
        2 * ((orderC b q).val : Real) * (M : Real) + ((phase q).val : Real) <=
          (2 * ((orderC b q).val * M + (orderF t q).val) +
            (phase q).val : Nat) := by
      push_cast
      have ht0 : (0 : Real) <= ((orderF t q).val : Real) := by positivity
      nlinarith
    have hdiv := (div_le_div_iff_of_pos_right hKR).2 hnum
    linarith
  · unfold reluApproxPhaseShiftedCoarseUpper
    unfold reluApproxPhaseShiftedFineUpper
    unfold twoScaleShiftedCenter
    dsimp only
    have hnum :
        (2 * ((orderC b q).val * M + (orderF t q).val) +
            (phase q).val : Nat) <=
          2 * (((orderC b q).val : Real) * (M : Real) + (M : Real) - 1) +
            ((phase q).val : Real) := by
      push_cast
      linarith
    have hdiv := (div_le_div_iff_of_pos_right hKR).2 hnum
    linarith

/-- The safe fine cell supplied by the interlaced grid is also safe for its
enclosing coarse scan box. -/
private theorem exists_reluApproxPhaseShiftedCoarseFineCells_safe
    {d M : Nat} (hM : 2 <= M)
    (orderC orderF : Fin (M ^ d) ≃ (Fin d -> Fin M))
    (R : Real)
    (hmargin : R⁻¹ <= (2 * ((M ^ 2 - 1 : Nat) : Real))⁻¹)
    (x : Fin d -> Real) (hx : forall q : Fin d, x q ∈ Set.Icc (0 : Real) 1) :
    exists (phase : Fin d -> Fin 2) (b t : Fin (M ^ d)),
      (forall q : Fin d,
        reluApproxPhaseShiftedCoarseLower M orderC phase b q + R⁻¹ <= x q /\
          x q <= reluApproxPhaseShiftedCoarseUpper M orderC phase b q - R⁻¹) /\
      (forall q : Fin d,
        reluApproxPhaseShiftedFineLower M orderC orderF phase b t q + R⁻¹ <= x q /\
          x q <= reluApproxPhaseShiftedFineUpper M orderC orderF phase b t q - R⁻¹) := by
  obtain ⟨phase, b, t, hfine⟩ :=
    exists_reluApproxPhaseShiftedFineCell_safe hM orderC orderF R hmargin x hx
  refine ⟨phase, b, t, ?_, hfine⟩
  intro q
  obtain ⟨hlower, hupper⟩ :=
    reluApproxPhaseShiftedFineBox_subset_coarse hM orderC orderF phase b t q
  constructor
  · exact le_trans (add_le_add hlower le_rfl) (hfine q).1
  · exact le_trans (hfine q).2 (sub_le_sub_right hupper R⁻¹)

/-- Consecutive fine indices in a serpentine order move a shifted center by
exactly `2 / (M^2 - 1)` in one coordinate. -/
private theorem twoScaleShiftedCenter_fine_adjacent
    {d M : Nat}
    (orderC orderF : Fin (M ^ d) ≃ (Fin d -> Fin M))
    (horderStep : forall (k : Nat) (hk : k + 1 < M ^ d),
      exists q : Fin d,
        Int.natAbs
          ((orderF ⟨k + 1, hk⟩ q).val -
            (orderF ⟨k, Nat.lt_of_succ_lt hk⟩ q).val) = 1 /\
        forall u : Fin d, u ≠ q ->
          orderF ⟨k + 1, hk⟩ u =
            orderF ⟨k, Nat.lt_of_succ_lt hk⟩ u)
    (phase : Fin d -> Fin 2) (b : Fin (M ^ d))
    (k : Nat) (hk : k + 1 < M ^ d) :
    exists q : Fin d,
      (twoScaleShiftedCenter M orderC orderF phase b ⟨k + 1, hk⟩ q =
          twoScaleShiftedCenter M orderC orderF phase b
            ⟨k, Nat.lt_of_succ_lt hk⟩ q +
              2 * ((M ^ 2 - 1 : Nat) : Real)⁻¹ /\
        forall u : Fin d, u ≠ q ->
          twoScaleShiftedCenter M orderC orderF phase b ⟨k + 1, hk⟩ u =
            twoScaleShiftedCenter M orderC orderF phase b
              ⟨k, Nat.lt_of_succ_lt hk⟩ u) \/
      (twoScaleShiftedCenter M orderC orderF phase b ⟨k + 1, hk⟩ q =
          twoScaleShiftedCenter M orderC orderF phase b
            ⟨k, Nat.lt_of_succ_lt hk⟩ q -
              2 * ((M ^ 2 - 1 : Nat) : Real)⁻¹ /\
        forall u : Fin d, u ≠ q ->
          twoScaleShiftedCenter M orderC orderF phase b ⟨k + 1, hk⟩ u =
            twoScaleShiftedCenter M orderC orderF phase b
              ⟨k, Nat.lt_of_succ_lt hk⟩ u) := by
  obtain ⟨q, hstep, hfixed⟩ := horderStep k hk
  refine ⟨q, ?_⟩
  have hsign :
      ((orderF ⟨k + 1, hk⟩ q).val : Int) -
            ((orderF ⟨k, Nat.lt_of_succ_lt hk⟩ q).val : Int) = 1 \/
        ((orderF ⟨k + 1, hk⟩ q).val : Int) -
            ((orderF ⟨k, Nat.lt_of_succ_lt hk⟩ q).val : Int) = -1 := by
    simpa using (Int.natAbs_eq_iff.mp hstep)
  rcases hsign with hplus | hminus
  · left
    constructor
    · have hval :
          (orderF ⟨k + 1, hk⟩ q).val =
            (orderF ⟨k, Nat.lt_of_succ_lt hk⟩ q).val + 1 := by omega
      unfold twoScaleShiftedCenter
      dsimp only
      rw [hval]
      push_cast
      ring
    · intro u hu
      unfold twoScaleShiftedCenter
      rw [hfixed u hu]
  · right
    constructor
    · have hval :
          (orderF ⟨k + 1, hk⟩ q).val + 1 =
            (orderF ⟨k, Nat.lt_of_succ_lt hk⟩ q).val := by omega
      unfold twoScaleShiftedCenter
      dsimp only
      have hvalR :
          ((orderF ⟨k + 1, hk⟩ q).val : Real) + 1 =
            ((orderF ⟨k, Nat.lt_of_succ_lt hk⟩ q).val : Real) := by
        exact_mod_cast hval
      push_cast
      rw [← hvalR]
      ring
    · intro u hu
      unfold twoScaleShiftedCenter
      rw [hfixed u hu]

/-- For one shifted phase, freeze every finite serpentine fine-grid path after
its final center.  The resulting coordinate and signed-step data have exactly
the interface consumed by the canonical Taylor-correction encoder. -/
private theorem exists_reluApproxPhaseShiftedFinePathData
    {d M : Nat} (hd : 0 < d) (hM : 2 <= M)
    (orderC orderF : Fin (M ^ d) ≃ (Fin d -> Fin M))
    (horderStep : forall (k : Nat) (hk : k + 1 < M ^ d),
      exists q : Fin d,
        Int.natAbs
          ((orderF ⟨k + 1, hk⟩ q).val -
            (orderF ⟨k, Nat.lt_of_succ_lt hk⟩ q).val) = 1 /\
        forall u : Fin d, u ≠ q ->
          orderF ⟨k + 1, hk⟩ u =
            orderF ⟨k, Nat.lt_of_succ_lt hk⟩ u)
    (phase : Fin d -> Fin 2) :
    let rho : Real := 2 * ((M ^ 2 - 1 : Nat) : Real)⁻¹
    exists centerPath : Fin (M ^ d) -> Nat -> Fin d -> Real,
    exists coordinate : Fin (M ^ d) -> Nat -> Fin d,
    exists signedStep : Fin (M ^ d) -> Nat -> Real,
      (forall b k, forall hk : k < M ^ d,
        centerPath b k =
          twoScaleShiftedCenter M orderC orderF phase b ⟨k, hk⟩) /\
      (forall b k, centerPath b (k + 1) - centerPath b k =
        reluApproxCoordinateStep (coordinate b k) (signedStep b k)) /\
      forall b k, |signedStep b k| <= rho := by
  dsimp only
  have hT : 0 < M ^ d := Nat.pow_pos (by omega)
  have hrho : 0 <= 2 * ((M ^ 2 - 1 : Nat) : Real)⁻¹ := by positivity
  have hex : forall b : Fin (M ^ d),
      exists path : Nat -> Fin d -> Real,
      exists coordinate : Nat -> Fin d,
      exists step : Nat -> Real,
        (forall k, forall hk : k < M ^ d,
          path k = twoScaleShiftedCenter M orderC orderF phase b ⟨k, hk⟩) /\
        (forall k, path (k + 1) - path k =
          reluApproxCoordinateStep (coordinate k) (step k)) /\
        forall k, |step k| <= 2 * ((M ^ 2 - 1 : Nat) : Real)⁻¹ := by
    intro b
    apply exists_reluApproxFrozenCenterPathData hd hT
      (twoScaleShiftedCenter M orderC orderF phase b)
      (2 * ((M ^ 2 - 1 : Nat) : Real)⁻¹) hrho
    intro k hk
    obtain ⟨q, h⟩ := twoScaleShiftedCenter_fine_adjacent
      orderC orderF horderStep phase b k hk
    rcases h with h | h
    · exact ⟨q, Or.inl h.1, h.2⟩
    · exact ⟨q, Or.inr h.1, h.2⟩
  choose centerPath coordinate signedStep hpath hmove hstep using hex
  exact ⟨centerPath, coordinate, signedStep, hpath, hmove, hstep⟩

/-- All coarse blocks in one shifted phase share the same fine-step schedule.
Only a block-dependent translation distinguishes their center paths.  This is
the interface required by the compiled coarse/fine machine. -/
private theorem exists_reluApproxPhaseShiftedCommonFinePathData
    {d M : Nat} (hd : 0 < d) (hM : 2 <= M)
    (orderC orderF : Fin (M ^ d) ≃ (Fin d -> Fin M))
    (horderStep : forall (k : Nat) (hk : k + 1 < M ^ d),
      exists q : Fin d,
        Int.natAbs
          ((orderF ⟨k + 1, hk⟩ q).val -
            (orderF ⟨k, Nat.lt_of_succ_lt hk⟩ q).val) = 1 /\
        forall u : Fin d, u ≠ q ->
          orderF ⟨k + 1, hk⟩ u =
            orderF ⟨k, Nat.lt_of_succ_lt hk⟩ u)
    (phase : Fin d -> Fin 2) :
    let rho : Real := 2 * ((M ^ 2 - 1 : Nat) : Real)⁻¹
    exists centerPath : Fin (M ^ d) -> Nat -> Fin d -> Real,
    exists coordinate : Nat -> Fin d,
    exists signedStep : Nat -> Real,
      (forall b k, forall hk : k < M ^ d,
        centerPath b k =
          twoScaleShiftedCenter M orderC orderF phase b ⟨k, hk⟩) /\
      (forall b k, centerPath b (k + 1) - centerPath b k =
        reluApproxCoordinateStep (coordinate k) (signedStep k)) /\
      forall k, |signedStep k| <= rho := by
  classical
  dsimp only
  have hT : 0 < M ^ d := Nat.pow_pos (by omega)
  let b0 : Fin (M ^ d) := ⟨0, hT⟩
  let t0 : Fin (M ^ d) := ⟨0, hT⟩
  let rho : Real := 2 * ((M ^ 2 - 1 : Nat) : Real)⁻¹
  have hrho : 0 <= rho := by
    dsimp [rho]
    positivity
  obtain ⟨path0, coordinate, signedStep, hpath0, hmove0, hstep⟩ :=
    exists_reluApproxFrozenCenterPathData hd hT
      (twoScaleShiftedCenter M orderC orderF phase b0) rho hrho (by
        intro k hk
        obtain ⟨q, hq⟩ := twoScaleShiftedCenter_fine_adjacent
          orderC orderF horderStep phase b0 k hk
        rcases hq with hq | hq
        · exact ⟨q, Or.inl (by simpa [rho] using hq.1), hq.2⟩
        · exact ⟨q, Or.inr (by simpa [rho] using hq.1), hq.2⟩)
  let centerPath : Fin (M ^ d) -> Nat -> Fin d -> Real := fun b k q =>
    path0 k q +
      (twoScaleShiftedCenter M orderC orderF phase b t0 q -
        twoScaleShiftedCenter M orderC orderF phase b0 t0 q)
  refine ⟨centerPath, coordinate, signedStep, ?_, ?_, hstep⟩
  · intro b k hk
    funext q
    have hp0 := congrFun (hpath0 k hk) q
    dsimp [centerPath]
    rw [hp0]
    unfold twoScaleShiftedCenter
    dsimp only
    push_cast
    ring
  · intro b k
    funext q
    have hm0 := congrFun (hmove0 k) q
    dsimp [centerPath]
    calc
      path0 (k + 1) q +
            (twoScaleShiftedCenter M orderC orderF phase b t0 q -
              twoScaleShiftedCenter M orderC orderF phase b0 t0 q) -
          (path0 k q +
            (twoScaleShiftedCenter M orderC orderF phase b t0 q -
              twoScaleShiftedCenter M orderC orderF phase b0 t0 q)) =
        path0 (k + 1) q - path0 k q := by ring
      _ = reluApproxCoordinateStep (coordinate k) (signedStep k) q := hm0

/-- One shifted two-scale phase admits a concrete hierarchical fine-boundary
checker.  The coarse pass selects the active coarse block, and the shared
serpentine fine pass accumulates the fine-box gates within that block. -/
private theorem exists_reluApproxPhaseShiftedHierarchicalFineBoundaryCheckNetRadius_exactDepth
    {d r M D W : Nat} (hd : 0 < d) (hM : 2 <= M)
    (orderC orderF : Fin (M ^ d) ≃ (Fin d -> Fin M))
    (horderStep : forall (k : Nat) (hk : k + 1 < M ^ d),
      exists q : Fin d,
        Int.natAbs
          ((orderF ⟨k + 1, hk⟩ q).val -
            (orderF ⟨k, Nat.lt_of_succ_lt hk⟩ q).val) = 1 /\
        forall u : Fin d, u ≠ q ->
          orderF ⟨k + 1, hk⟩ u =
            orderF ⟨k, Nat.lt_of_succ_lt hk⟩ u)
    (phase : Fin d -> Fin 2) (Rscan Rselect innerRadius : Real)
    (hRscan : 2 <= Rscan)
    (hdepth : 2 * ((M ^ d) * 2 + (M ^ d) * 3) + 1 <= D)
    (hwidth :
      let s := reluApproxVectorBoxScanStateSize d
        (Fintype.card (ReLUApproxFineAccumulator d r))
      let hscan := reluApproxVectorBoxScanFeatureSize d
        (Fintype.card (ReLUApproxFineAccumulator d r))
      let h := hscan + (hscan + fineTaylorFeatureSize d r 0)
      (s + s) + h <= W) :
    exists N : FullyConnectedReLUNet d,
      N.depth = D /\ N.width <= W /\
        N.parameterCount <= fullyConnectedReLUParameterCount d D W /\
        forall (x : Fin d -> Real) (active : Fin (M ^ d)),
          (forall q,
            reluApproxPhaseShiftedCoarseLower M orderC phase active q +
                Rscan⁻¹ <= x q /\
              x q <= reluApproxPhaseShiftedCoarseUpper M orderC phase active q -
                Rscan⁻¹) ->
          (forall i, i ≠ active -> exists q,
            x q <= reluApproxPhaseShiftedCoarseLower M orderC phase i q \/
              reluApproxPhaseShiftedCoarseUpper M orderC phase i q <= x q) ->
          N.realize x =
            reluApproxBoundaryCheck Rselect
              (fun (k : Fin (M ^ d)) q =>
                twoScaleShiftedCenter
                  M orderC orderF phase active k q - innerRadius)
              (fun (k : Fin (M ^ d)) q =>
                twoScaleShiftedCenter
                  M orderC orderF phase active k q + innerRadius) x := by
  classical
  obtain ⟨path, coordinate, signedStep, hpath, hmove, _hstep⟩ :=
    exists_reluApproxPhaseShiftedCommonFinePathData
      hd hM orderC orderF horderStep phase
  let step : Fin (M ^ d) -> Fin d -> Real := fun k =>
    reluApproxCoordinateStep (coordinate k.val) (signedStep k.val)
  have hRscan_pos : 0 < Rscan := lt_of_lt_of_le (by norm_num) hRscan
  have hT : 0 < M ^ d := Nat.pow_pos (by omega)
  have hpayload : forall b (p : ReLUApproxFineAccumulator d r),
      |(Sum.elim
          (reluApproxTaylorPayloadState (r := r) (path b 0)
            (fun _ : TaylorMultiindex r d => 1)
            (fun _ : TaylorMultiindex r d => 0))
          (reluApproxSelectedTaylorState (r := r)
            (fun _ : Fin d => 0)
            (fun _ : TaylorMultiindex r d => 0))) p| <= Rscan := by
    intro b p
    rcases p with (((q | a) | a) | (q | a))
    · have hpath0 := congrFun (hpath b 0 hT) q
      simp only [Sum.elim_inl, reluApproxTaylorPayloadState]
      rw [hpath0]
      exact le_trans
        (abs_twoScaleShiftedCenter_le_two hM orderC orderF
          phase b ⟨0, hT⟩ q)
        hRscan
    · simp [reluApproxTaylorPayloadState]
      linarith
    · simp [reluApproxTaylorPayloadState]
      exact hRscan_pos.le
    · simp [reluApproxSelectedTaylorState]
      exact hRscan_pos.le
    · simp [reluApproxSelectedTaylorState]
      exact hRscan_pos.le
  have hpathStep : forall b k, forall hk : k < M ^ d,
      path b (k + 1) - path b k = step ⟨k, hk⟩ := by
    intro b k hk
    exact hmove b k
  obtain ⟨N, hNdepth, hNwidth, hNparam, hNrealize⟩ :=
    exists_reluApproxHierarchicalFineBoundaryCheckNet_exactDepth
      Rscan Rselect innerRadius
      (reluApproxPhaseShiftedCoarseLower M orderC phase)
      (reluApproxPhaseShiftedCoarseUpper M orderC phase)
      path step hRscan_pos hpayload hpathStep hdepth hwidth
  refine ⟨N, hNdepth, hNwidth, hNparam, ?_⟩
  intro x active hactive hinactive
  rw [hNrealize x active hactive hinactive]
  congr 1 <;> funext k q
  · rw [hpath active k.val k.isLt]
  · rw [hpath active k.val k.isLt]

/-- The paper fine-boundary checker at the native shifted-cell radius. -/
private theorem exists_reluApproxPhaseShiftedHierarchicalFineBoundaryCheckNet_exactDepth
    {d r M D W : Nat} (hd : 0 < d) (hM : 2 <= M)
    (orderC orderF : Fin (M ^ d) ≃ (Fin d -> Fin M))
    (horderStep : forall (k : Nat) (hk : k + 1 < M ^ d),
      exists q : Fin d,
        Int.natAbs
          ((orderF ⟨k + 1, hk⟩ q).val -
            (orderF ⟨k, Nat.lt_of_succ_lt hk⟩ q).val) = 1 /\
        forall u : Fin d, u ≠ q ->
          orderF ⟨k + 1, hk⟩ u =
            orderF ⟨k, Nat.lt_of_succ_lt hk⟩ u)
    (phase : Fin d -> Fin 2) (Rscan Rselect : Real)
    (hRscan : 2 <= Rscan)
    (hdepth : 2 * ((M ^ d) * 2 + (M ^ d) * 3) + 1 <= D)
    (hwidth :
      let s := reluApproxVectorBoxScanStateSize d
        (Fintype.card (ReLUApproxFineAccumulator d r))
      let hscan := reluApproxVectorBoxScanFeatureSize d
        (Fintype.card (ReLUApproxFineAccumulator d r))
      let h := hscan + (hscan + fineTaylorFeatureSize d r 0)
      (s + s) + h <= W) :
    exists N : FullyConnectedReLUNet d,
      N.depth = D /\ N.width <= W /\
        N.parameterCount <= fullyConnectedReLUParameterCount d D W /\
        forall (x : Fin d -> Real) (active : Fin (M ^ d)),
          (forall q,
            reluApproxPhaseShiftedCoarseLower M orderC phase active q +
                Rscan⁻¹ <= x q /\
              x q <= reluApproxPhaseShiftedCoarseUpper M orderC phase active q -
                Rscan⁻¹) ->
          (forall i, i ≠ active -> exists q,
            x q <= reluApproxPhaseShiftedCoarseLower M orderC phase i q \/
              reluApproxPhaseShiftedCoarseUpper M orderC phase i q <= x q) ->
          N.realize x =
            reluApproxBoundaryCheck Rselect
              (fun (k : Fin (M ^ d)) q =>
                reluApproxPhaseShiftedFineLower
                  M orderC orderF phase active k q)
              (fun (k : Fin (M ^ d)) q =>
                reluApproxPhaseShiftedFineUpper
                  M orderC orderF phase active k q) x := by
  exact exists_reluApproxPhaseShiftedHierarchicalFineBoundaryCheckNetRadius_exactDepth
    hd hM orderC orderF horderStep phase Rscan Rselect
      (((M ^ 2 - 1 : Nat) : Real)⁻¹) hRscan hdepth hwidth

/-- Distinct coarse blocks of one shifted partition have disjoint interiors. -/
private theorem reluApprox_phaseShiftedCoarseBoxes_pairwise_disjoint
    {d M : Nat} (hM : 2 <= M)
    (orderC : Fin (M ^ d) ≃ (Fin d -> Fin M))
    (phase : Fin d -> Fin 2) :
    forall b c : Fin (M ^ d), b ≠ c -> exists q : Fin d,
      reluApproxPhaseShiftedCoarseUpper M orderC phase b q <=
          reluApproxPhaseShiftedCoarseLower M orderC phase c q \/
        reluApproxPhaseShiftedCoarseUpper M orderC phase c q <=
          reluApproxPhaseShiftedCoarseLower M orderC phase b q := by
  let K : Nat := M ^ 2 - 1
  have hK : 0 < K := by
    dsimp [K]
    have hM2 : 4 <= M ^ 2 := by
      have hm := Nat.mul_le_mul hM hM
      norm_num at hm
      simpa [pow_two] using hm
    omega
  have hKR : (0 : Real) < (K : Real) := by exact_mod_cast hK
  intro b c hbc
  have horders_ne : orderC b ≠ orderC c := fun h => hbc (orderC.injective h)
  have hcoord : exists q : Fin d, (orderC b q).val ≠ (orderC c q).val := by
    by_contra hnone
    push_neg at hnone
    apply horders_ne
    funext q
    exact Fin.ext (hnone q)
  rcases hcoord with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  have hsep : forall {n m : Nat}, n < m ->
      (2 * ((n : Real) * (M : Real) + (M : Real) - 1) +
          ((phase q).val : Real)) / (K : Real) - 1 + (K : Real)⁻¹ <=
        (2 * (m : Real) * (M : Real) + ((phase q).val : Real)) /
          (K : Real) - 1 - (K : Real)⁻¹ := by
    intro n m hnm
    have hnmR : ((n + 1 : Nat) : Real) <= (m : Real) := by
      exact_mod_cast (Nat.succ_le_of_lt hnm)
    have hMR : (0 : Real) <= (M : Real) := by positivity
    have hnumR :
        2 * ((n : Real) * (M : Real) + (M : Real) - 1) +
            ((phase q).val : Real) + 1 <=
          2 * (m : Real) * (M : Real) + ((phase q).val : Real) - 1 := by
      push_cast at hnmR
      nlinarith
    have hleft :
        (2 * ((n : Real) * (M : Real) + (M : Real) - 1) +
            ((phase q).val : Real)) / (K : Real) - 1 + (K : Real)⁻¹ =
          (2 * ((n : Real) * (M : Real) + (M : Real) - 1) +
            ((phase q).val : Real) + 1) / (K : Real) - 1 := by
      field_simp
      ring
    have hright :
        (2 * (m : Real) * (M : Real) + ((phase q).val : Real)) /
            (K : Real) - 1 - (K : Real)⁻¹ =
          (2 * (m : Real) * (M : Real) + ((phase q).val : Real) - 1) /
            (K : Real) - 1 := by
      field_simp
      ring
    rw [hleft, hright]
    exact sub_le_sub_right ((div_le_div_iff_of_pos_right hKR).2 hnumR) 1
  rcases lt_or_gt_of_ne hq with hlt | hgt
  · left
    exact hsep hlt
  · right
    exact hsep hgt

/-- All fine boxes in a fixed shifted phase are pairwise interior-disjoint,
including boxes belonging to different coarse blocks. -/
private theorem reluApprox_phaseShiftedAllFineBoxes_pairwise_disjoint
    {d M : Nat} (hM : 2 <= M)
    (orderC orderF : Fin (M ^ d) ≃ (Fin d -> Fin M))
    (phase : Fin d -> Fin 2) :
    forall p u : Fin (M ^ d) × Fin (M ^ d), p ≠ u -> exists q : Fin d,
      reluApproxPhaseShiftedFineUpper M orderC orderF phase p.1 p.2 q <=
          reluApproxPhaseShiftedFineLower M orderC orderF phase u.1 u.2 q \/
        reluApproxPhaseShiftedFineUpper M orderC orderF phase u.1 u.2 q <=
          reluApproxPhaseShiftedFineLower M orderC orderF phase p.1 p.2 q := by
  intro p u hpu
  by_cases hb : p.1 = u.1
  · have ht : p.2 ≠ u.2 := by
      intro ht
      apply hpu
      exact Prod.ext hb ht
    have h := reluApprox_phaseShiftedFineBoxes_pairwise_disjoint
      hM orderC orderF phase p.1 p.2 u.2 ht
    simpa [← hb] using h
  · obtain ⟨q, hsep | hsep⟩ :=
      reluApprox_phaseShiftedCoarseBoxes_pairwise_disjoint
        hM orderC phase p.1 u.1 hb
    · refine ⟨q, Or.inl ?_⟩
      have hp := reluApproxPhaseShiftedFineBox_subset_coarse
        hM orderC orderF phase p.1 p.2 q
      have hu := reluApproxPhaseShiftedFineBox_subset_coarse
        hM orderC orderF phase u.1 u.2 q
      exact le_trans hp.2 (le_trans hsep hu.1)
    · refine ⟨q, Or.inr ?_⟩
      have hp := reluApproxPhaseShiftedFineBox_subset_coarse
        hM orderC orderF phase p.1 p.2 q
      have hu := reluApproxPhaseShiftedFineBox_subset_coarse
        hM orderC orderF phase u.1 u.2 q
      exact le_trans hu.2 (le_trans hsep hp.1)

/-- At a fixed input, two distinct fine cells in the same shifted phase cannot
both have nonzero tensor-tent weight. -/
private theorem reluApproxPhaseShiftedTentWeight_eq_zero_of_ne_of_nonzero
    {d M : Nat} (hM : 2 <= M)
    (orderC orderF : Fin (M ^ d) ≃ (Fin d -> Fin M))
    (phase : Fin d -> Fin 2) (x : Fin d -> Real)
    (active other : Fin (M ^ d) × Fin (M ^ d))
    (hne : active ≠ other)
    (hactive : axisAlignedBoxTentWeight
      (twoScaleShiftedCenter M orderC orderF phase active.1 active.2)
      (twoScaleShiftedScale M phase active.1 active.2) x ≠ 0) :
    axisAlignedBoxTentWeight
      (twoScaleShiftedCenter M orderC orderF phase other.1 other.2)
      (twoScaleShiftedScale M phase other.1 other.2) x = 0 := by
  let K : Nat := M ^ 2 - 1
  have hK : 0 < K := by
    dsimp [K]
    have hM2 : 4 <= M ^ 2 := by
      have hm := Nat.mul_le_mul hM hM
      norm_num at hm
      simpa [pow_two] using hm
    omega
  have hKR : (0 : Real) < (K : Real) := by exact_mod_cast hK
  have hKinv : (K : Real) * (K : Real)⁻¹ = 1 :=
    mul_inv_cancel₀ (ne_of_gt hKR)
  have hactiveInterior : forall q : Fin d,
      reluApproxPhaseShiftedFineLower M orderC orderF phase active.1 active.2 q < x q /\
        x q < reluApproxPhaseShiftedFineUpper M orderC orderF phase active.1 active.2 q := by
    intro q
    have hscale : forall u : Fin d,
        0 <= twoScaleShiftedScale M phase active.1 active.2 u := by
      intro u
      simp [twoScaleShiftedScale]
    have hsmall :
        (K : Real) *
            (relu (x q - twoScaleShiftedCenter M orderC orderF phase active.1 active.2 q) +
              relu (twoScaleShiftedCenter M orderC orderF phase active.1 active.2 q - x q)) < 1 := by
      by_contra hnot
      have hzero := (axisAlignedBoxTentWeight_bounds_and_support
        (twoScaleShiftedCenter M orderC orderF phase active.1 active.2)
        (twoScaleShiftedScale M phase active.1 active.2) x hscale).2.2
      apply hactive
      apply hzero
      refine ⟨q, ?_⟩
      simpa [twoScaleShiftedScale, K] using le_of_not_gt hnot
    have hleftRelu :
        x q - twoScaleShiftedCenter M orderC orderF phase active.1 active.2 q <=
          relu (x q - twoScaleShiftedCenter M orderC orderF phase active.1 active.2 q) := by
      unfold relu
      exact le_max_left _ _
    have hrightRelu :
        twoScaleShiftedCenter M orderC orderF phase active.1 active.2 q - x q <=
          relu (twoScaleShiftedCenter M orderC orderF phase active.1 active.2 q - x q) := by
      unfold relu
      exact le_max_left _ _
    have hreluLeftNonneg : 0 <=
        relu (x q - twoScaleShiftedCenter M orderC orderF phase active.1 active.2 q) := by
      unfold relu
      exact le_max_right _ _
    have hreluRightNonneg : 0 <=
        relu (twoScaleShiftedCenter M orderC orderF phase active.1 active.2 q - x q) := by
      unfold relu
      exact le_max_right _ _
    unfold reluApproxPhaseShiftedFineLower
    unfold reluApproxPhaseShiftedFineUpper
    dsimp [K] at hsmall hKinv ⊢
    constructor <;> nlinarith
  obtain ⟨q, hsep | hsep⟩ :=
    reluApprox_phaseShiftedAllFineBoxes_pairwise_disjoint
      hM orderC orderF phase active other hne
  · have hx : x q <
        reluApproxPhaseShiftedFineLower M orderC orderF phase other.1 other.2 q :=
      lt_of_lt_of_le (hactiveInterior q).2 hsep
    have hdist : (K : Real)⁻¹ <
        twoScaleShiftedCenter M orderC orderF phase other.1 other.2 q - x q := by
      unfold reluApproxPhaseShiftedFineLower at hx
      dsimp [K] at hx ⊢
      linarith
    have hrelu :
        twoScaleShiftedCenter M orderC orderF phase other.1 other.2 q - x q <=
          relu (twoScaleShiftedCenter M orderC orderF phase other.1 other.2 q - x q) := by
      unfold relu
      exact le_max_left _ _
    have hother : 0 <= relu
        (x q - twoScaleShiftedCenter M orderC orderF phase other.1 other.2 q) := by
      unfold relu
      exact le_max_right _ _
    apply (axisAlignedBoxTentWeight_bounds_and_support
      (twoScaleShiftedCenter M orderC orderF phase other.1 other.2)
      (twoScaleShiftedScale M phase other.1 other.2) x
      (by intro u; simp [twoScaleShiftedScale])).2.2
    refine ⟨q, ?_⟩
    simp only [twoScaleShiftedScale]
    dsimp [K] at hdist hKinv ⊢
    nlinarith
  · have hx :
        reluApproxPhaseShiftedFineUpper M orderC orderF phase other.1 other.2 q < x q :=
      lt_of_le_of_lt hsep (hactiveInterior q).1
    have hdist : (K : Real)⁻¹ <
        x q - twoScaleShiftedCenter M orderC orderF phase other.1 other.2 q := by
      unfold reluApproxPhaseShiftedFineUpper at hx
      dsimp [K] at hx ⊢
      linarith
    have hrelu :
        x q - twoScaleShiftedCenter M orderC orderF phase other.1 other.2 q <=
          relu (x q - twoScaleShiftedCenter M orderC orderF phase other.1 other.2 q) := by
      unfold relu
      exact le_max_left _ _
    have hother : 0 <= relu
        (twoScaleShiftedCenter M orderC orderF phase other.1 other.2 q - x q) := by
      unfold relu
      exact le_max_right _ _
    apply (axisAlignedBoxTentWeight_bounds_and_support
      (twoScaleShiftedCenter M orderC orderF phase other.1 other.2)
      (twoScaleShiftedScale M phase other.1 other.2) x
      (by intro u; simp [twoScaleShiftedScale])).2.2
    refine ⟨q, ?_⟩
    simp only [twoScaleShiftedScale]
    dsimp [K] at hdist hKinv ⊢
    nlinarith

/-- If no fine cell in a shifted phase contains the input with the requested
safety margin, then the total tent mass of that phase is controlled by the
selector transition width.  Pairwise-disjoint supports prevent a factor equal
to the number of fine cells from entering this bound. -/
private theorem reluApproxPhaseShifted_phase_tent_sum_le_selector_margin
    {d M : Nat} (hM : 2 <= M)
    (orderC orderF : Fin (M ^ d) ≃ (Fin d -> Fin M))
    (phase : Fin d -> Fin 2) {R : Real} (hR : 0 < R)
    (x : Fin d -> Real)
    (hunsafe : forall (b t : Fin (M ^ d)),
      ¬ forall q : Fin d,
        reluApproxPhaseShiftedFineLower M orderC orderF phase b t q + R⁻¹ <= x q /\
          x q <= reluApproxPhaseShiftedFineUpper M orderC orderF phase b t q - R⁻¹) :
    (Finset.univ.sum fun b : Fin (M ^ d) =>
      Finset.univ.sum fun t : Fin (M ^ d) =>
        axisAlignedBoxTentWeight
          (twoScaleShiftedCenter M orderC orderF phase b t)
          (twoScaleShiftedScale M phase b t) x) <=
      ((M ^ 2 - 1 : Nat) : Real) * R⁻¹ := by
  let w : (Fin (M ^ d) × Fin (M ^ d)) -> Real := fun p =>
    axisAlignedBoxTentWeight
      (twoScaleShiftedCenter M orderC orderF phase p.1 p.2)
      (twoScaleShiftedScale M phase p.1 p.2) x
  have hrewrite :
      (Finset.univ.sum fun b : Fin (M ^ d) =>
        Finset.univ.sum fun t : Fin (M ^ d) =>
          axisAlignedBoxTentWeight
            (twoScaleShiftedCenter M orderC orderF phase b t)
            (twoScaleShiftedScale M phase b t) x) =
        Finset.univ.sum w := by
    exact (Fintype.sum_prod_type w).symm
  rw [hrewrite]
  by_cases hex : exists active, w active ≠ 0
  · obtain ⟨active, hactive⟩ := hex
    rw [Finset.sum_eq_single active]
    · exact reluApproxPhaseShiftedTentWeight_le_selector_margin
        hM orderC orderF phase active.1 active.2 hR x
          (hunsafe active.1 active.2)
    · intro other _hother hne
      exact reluApproxPhaseShiftedTentWeight_eq_zero_of_ne_of_nonzero
        hM orderC orderF phase x active other (Ne.symm hne) hactive
    · simp
  · push_neg at hex
    have hzero : w = 0 := by
      funext p
      exact hex p
    rw [hzero]
    simpa using mul_nonneg
      (show 0 <= (((M ^ 2 - 1 : Nat) : Real)) by positivity)
      (inv_nonneg.mpr hR.le)

/-- A bad shifted phase contributes only its selector-margin mass when all
local values are uniformly bounded. -/
private theorem reluApproxPhaseShifted_phase_weighted_sum_abs_le_selector_margin
    {d M : Nat} (hM : 2 <= M)
    (orderC orderF : Fin (M ^ d) ≃ (Fin d -> Fin M))
    (phase : Fin d -> Fin 2) {R Bval : Real}
    (hR : 0 < R) (hBval : 0 <= Bval)
    (x : Fin d -> Real)
    (value : (Fin (M ^ d) × Fin (M ^ d)) -> Real)
    (hvalue : forall p, |value p| <= Bval)
    (hunsafe : forall (b t : Fin (M ^ d)),
      ¬ forall q : Fin d,
        reluApproxPhaseShiftedFineLower M orderC orderF phase b t q + R⁻¹ <= x q /\
          x q <= reluApproxPhaseShiftedFineUpper M orderC orderF phase b t q - R⁻¹) :
    |Finset.univ.sum fun b : Fin (M ^ d) =>
      Finset.univ.sum fun t : Fin (M ^ d) =>
        axisAlignedBoxTentWeight
            (twoScaleShiftedCenter M orderC orderF phase b t)
            (twoScaleShiftedScale M phase b t) x * value (b, t)| <=
      Bval * (((M ^ 2 - 1 : Nat) : Real) * R⁻¹) := by
  let w : Fin (M ^ d) -> Fin (M ^ d) -> Real := fun b t =>
    axisAlignedBoxTentWeight
      (twoScaleShiftedCenter M orderC orderF phase b t)
      (twoScaleShiftedScale M phase b t) x
  have hw : forall b t, 0 <= w b t := by
    intro b t
    exact (axisAlignedBoxTentWeight_bounds_and_support
      (twoScaleShiftedCenter M orderC orderF phase b t)
      (twoScaleShiftedScale M phase b t) x
      (by intro q; simp [twoScaleShiftedScale])).1
  have habs :
      |Finset.univ.sum fun b : Fin (M ^ d) =>
        Finset.univ.sum fun t : Fin (M ^ d) => w b t * value (b, t)| <=
        Finset.univ.sum fun b : Fin (M ^ d) =>
          Finset.univ.sum fun t : Fin (M ^ d) => w b t * Bval := by
    calc
      |Finset.univ.sum fun b : Fin (M ^ d) =>
          Finset.univ.sum fun t : Fin (M ^ d) => w b t * value (b, t)| <=
          Finset.univ.sum fun b : Fin (M ^ d) =>
            |Finset.univ.sum fun t : Fin (M ^ d) => w b t * value (b, t)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= Finset.univ.sum fun b : Fin (M ^ d) =>
          Finset.univ.sum fun t : Fin (M ^ d) => |w b t * value (b, t)| := by
        apply Finset.sum_le_sum
        intro b _hb
        exact Finset.abs_sum_le_sum_abs _ _
      _ <= Finset.univ.sum fun b : Fin (M ^ d) =>
          Finset.univ.sum fun t : Fin (M ^ d) => w b t * Bval := by
        apply Finset.sum_le_sum
        intro b _hb
        apply Finset.sum_le_sum
        intro t _ht
        rw [abs_mul, abs_of_nonneg (hw b t)]
        exact mul_le_mul_of_nonneg_left (hvalue (b, t)) (hw b t)
  have hfactor :
      (Finset.univ.sum fun b : Fin (M ^ d) =>
        Finset.univ.sum fun t : Fin (M ^ d) => w b t * Bval) =
      Bval * (Finset.univ.sum fun b : Fin (M ^ d) =>
        Finset.univ.sum fun t : Fin (M ^ d) => w b t) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _hb
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _ht
    ring
  have hmass := reluApproxPhaseShifted_phase_tent_sum_le_selector_margin
    hM orderC orderF phase hR x hunsafe
  change |Finset.univ.sum fun b : Fin (M ^ d) =>
      Finset.univ.sum fun t : Fin (M ^ d) => w b t * value (b, t)| <= _
  calc
    _ <= Finset.univ.sum fun b : Fin (M ^ d) =>
        Finset.univ.sum fun t : Fin (M ^ d) => w b t * Bval := habs
    _ = Bval * (Finset.univ.sum fun b : Fin (M ^ d) =>
        Finset.univ.sum fun t : Fin (M ^ d) => w b t) := hfactor
    _ <= Bval * (((M ^ 2 - 1 : Nat) : Real) * R⁻¹) :=
      mul_le_mul_of_nonneg_left (by simpa [w] using hmass) hBval

/-- If one shifted fine cell contains the input with a positive safety margin,
every other tent in the same phase vanishes. -/
private theorem reluApproxPhaseShiftedTentWeight_eq_zero_of_safe_ne
    {d M : Nat} (hM : 2 <= M)
    (orderC orderF : Fin (M ^ d) ≃ (Fin d -> Fin M))
    (phase : Fin d -> Fin 2) {R : Real} (hR : 0 < R)
    (x : Fin d -> Real)
    (active other : Fin (M ^ d) × Fin (M ^ d))
    (hsafe : forall q : Fin d,
      reluApproxPhaseShiftedFineLower M orderC orderF phase active.1 active.2 q + R⁻¹ <= x q /\
        x q <= reluApproxPhaseShiftedFineUpper M orderC orderF phase active.1 active.2 q - R⁻¹)
    (hne : other ≠ active) :
    axisAlignedBoxTentWeight
        (twoScaleShiftedCenter M orderC orderF phase other.1 other.2)
        (twoScaleShiftedScale M phase other.1 other.2) x = 0 := by
  let K : Nat := M ^ 2 - 1
  have hK : 0 < K := by
    dsimp [K]
    have hM2 : 4 <= M ^ 2 := by
      have hm := Nat.mul_le_mul hM hM
      norm_num at hm
      simpa [pow_two] using hm
    omega
  have hKR : (0 : Real) < (K : Real) := by exact_mod_cast hK
  have hKinv : (K : Real) * (K : Real)⁻¹ = 1 :=
    mul_inv_cancel₀ (ne_of_gt hKR)
  have hRinv : 0 < R⁻¹ := inv_pos.mpr hR
  obtain ⟨q, hsep | hsep⟩ :=
    reluApprox_phaseShiftedAllFineBoxes_pairwise_disjoint
      hM orderC orderF phase active other (Ne.symm hne)
  · have hxlower : x q <=
        reluApproxPhaseShiftedFineLower M orderC orderF phase other.1 other.2 q := by
      linarith [(hsafe q).2]
    have hdist : (K : Real)⁻¹ <=
        twoScaleShiftedCenter M orderC orderF phase other.1 other.2 q - x q := by
      unfold reluApproxPhaseShiftedFineLower at hxlower
      dsimp [K]
      linarith
    have hrelu1 : 0 <= relu (x q -
        twoScaleShiftedCenter M orderC orderF phase other.1 other.2 q) := by
      unfold relu
      exact le_max_right _ _
    have hrelu2 :
        twoScaleShiftedCenter M orderC orderF phase other.1 other.2 q - x q <=
          relu (twoScaleShiftedCenter M orderC orderF phase other.1 other.2 q - x q) := by
      unfold relu
      exact le_max_left _ _
    have hsum : (K : Real)⁻¹ <=
        relu (x q - twoScaleShiftedCenter M orderC orderF phase other.1 other.2 q) +
          relu (twoScaleShiftedCenter M orderC orderF phase other.1 other.2 q - x q) := by
      linarith
    have hone : 1 <= (K : Real) *
        (relu (x q - twoScaleShiftedCenter M orderC orderF phase other.1 other.2 q) +
          relu (twoScaleShiftedCenter M orderC orderF phase other.1 other.2 q - x q)) := by
      calc
        (1 : Real) = (K : Real) * (K : Real)⁻¹ := hKinv.symm
        _ <= (K : Real) *
            (relu (x q - twoScaleShiftedCenter M orderC orderF phase other.1 other.2 q) +
              relu (twoScaleShiftedCenter M orderC orderF phase other.1 other.2 q - x q)) :=
          mul_le_mul_of_nonneg_left hsum hKR.le
    exact (axisAlignedBoxTentWeight_bounds_and_support
      (twoScaleShiftedCenter M orderC orderF phase other.1 other.2)
      (twoScaleShiftedScale M phase other.1 other.2) x
      (by intro u; simp [twoScaleShiftedScale])).2.2 ⟨q, by
        simpa [twoScaleShiftedScale, K] using hone⟩
  · have hxupper :
        reluApproxPhaseShiftedFineUpper M orderC orderF phase other.1 other.2 q <= x q := by
      linarith [(hsafe q).1]
    have hdist : (K : Real)⁻¹ <=
        x q - twoScaleShiftedCenter M orderC orderF phase other.1 other.2 q := by
      unfold reluApproxPhaseShiftedFineUpper at hxupper
      dsimp [K]
      linarith
    have hrelu1 :
        x q - twoScaleShiftedCenter M orderC orderF phase other.1 other.2 q <=
          relu (x q - twoScaleShiftedCenter M orderC orderF phase other.1 other.2 q) := by
      unfold relu
      exact le_max_left _ _
    have hrelu2 : 0 <= relu
        (twoScaleShiftedCenter M orderC orderF phase other.1 other.2 q - x q) := by
      unfold relu
      exact le_max_right _ _
    have hsum : (K : Real)⁻¹ <=
        relu (x q - twoScaleShiftedCenter M orderC orderF phase other.1 other.2 q) +
          relu (twoScaleShiftedCenter M orderC orderF phase other.1 other.2 q - x q) := by
      linarith
    have hone : 1 <= (K : Real) *
        (relu (x q - twoScaleShiftedCenter M orderC orderF phase other.1 other.2 q) +
          relu (twoScaleShiftedCenter M orderC orderF phase other.1 other.2 q - x q)) := by
      calc
        (1 : Real) = (K : Real) * (K : Real)⁻¹ := hKinv.symm
        _ <= (K : Real) *
            (relu (x q - twoScaleShiftedCenter M orderC orderF phase other.1 other.2 q) +
              relu (twoScaleShiftedCenter M orderC orderF phase other.1 other.2 q - x q)) :=
          mul_le_mul_of_nonneg_left hsum hKR.le
    exact (axisAlignedBoxTentWeight_bounds_and_support
      (twoScaleShiftedCenter M orderC orderF phase other.1 other.2)
      (twoScaleShiftedScale M phase other.1 other.2) x
      (by intro u; simp [twoScaleShiftedScale])).2.2 ⟨q, by
        simpa [twoScaleShiftedScale, K] using hone⟩

/-- On a safely selected fine cell, a complete weighted sum over one shifted
phase is exactly its unique active term. -/
private theorem reluApproxPhaseShifted_weighted_sum_eq_of_safe
    {d M : Nat} (hM : 2 <= M)
    (orderC orderF : Fin (M ^ d) ≃ (Fin d -> Fin M))
    (phase : Fin d -> Fin 2) {R : Real} (hR : 0 < R)
    (x : Fin d -> Real)
    (active : Fin (M ^ d) × Fin (M ^ d))
    (hsafe : forall q : Fin d,
      reluApproxPhaseShiftedFineLower M orderC orderF phase active.1 active.2 q + R⁻¹ <= x q /\
        x q <= reluApproxPhaseShiftedFineUpper M orderC orderF phase active.1 active.2 q - R⁻¹)
    (value : (Fin (M ^ d) × Fin (M ^ d)) -> Real) :
    (Finset.univ.sum fun b : Fin (M ^ d) =>
      Finset.univ.sum fun t : Fin (M ^ d) =>
        axisAlignedBoxTentWeight
            (twoScaleShiftedCenter M orderC orderF phase b t)
            (twoScaleShiftedScale M phase b t) x * value (b, t)) =
      axisAlignedBoxTentWeight
          (twoScaleShiftedCenter M orderC orderF phase active.1 active.2)
          (twoScaleShiftedScale M phase active.1 active.2) x * value active := by
  rw [show (Finset.univ.sum fun b : Fin (M ^ d) =>
      Finset.univ.sum fun t : Fin (M ^ d) =>
        axisAlignedBoxTentWeight
            (twoScaleShiftedCenter M orderC orderF phase b t)
            (twoScaleShiftedScale M phase b t) x * value (b, t)) =
      Finset.univ.sum fun p : Fin (M ^ d) × Fin (M ^ d) =>
        axisAlignedBoxTentWeight
            (twoScaleShiftedCenter M orderC orderF phase p.1 p.2)
            (twoScaleShiftedScale M phase p.1 p.2) x * value p by
        exact (Fintype.sum_prod_type (fun p : Fin (M ^ d) × Fin (M ^ d) =>
          axisAlignedBoxTentWeight
              (twoScaleShiftedCenter M orderC orderF phase p.1 p.2)
              (twoScaleShiftedScale M phase p.1 p.2) x * value p)).symm]
  apply Finset.sum_eq_single active
  · intro p _hp hpne
    rw [reluApproxPhaseShiftedTentWeight_eq_zero_of_safe_ne
      hM orderC orderF phase hR x active p hsafe hpne]
    simp
  · simp

/-- Robust one-phase error bound when the boundary branch carries an explicit
additional approximation budget.  This is the form used after clipping an
approximate Taylor evaluator: outside every safe cell, the exact shifted phase
is controlled by the selector margin while the clipped output may retain a
separate evaluator error. -/
private theorem reluApproxPhaseShifted_phase_robust_error_of_unsafe_bound
    {d M : Nat} (hM : 2 <= M)
    (orderC orderF : Fin (M ^ d) ≃ (Fin d -> Fin M))
    (phase : Fin d -> Fin 2) {R Bval eps unsafeBound : Real}
    (hR : 0 < R) (hBval : 0 <= Bval) (heps : 0 <= eps)
    (hunsafeBound : 0 <= unsafeBound)
    (x : Fin d -> Real)
    (value : (Fin (M ^ d) × Fin (M ^ d)) -> Real)
    (hvalue : forall p, |value p| <= Bval)
    (phaseApprox : Real)
    (hsafeError : forall active : Fin (M ^ d) × Fin (M ^ d),
      (forall q : Fin d,
        reluApproxPhaseShiftedFineLower M orderC orderF phase
              active.1 active.2 q + R⁻¹ <= x q /\
          x q <= reluApproxPhaseShiftedFineUpper M orderC orderF phase
              active.1 active.2 q - R⁻¹) ->
      |phaseApprox -
        axisAlignedBoxTentWeight
            (twoScaleShiftedCenter M orderC orderF phase active.1 active.2)
            (twoScaleShiftedScale M phase active.1 active.2) x *
          value active| <= eps)
    (hunsafeOutput :
      (forall (b t : Fin (M ^ d)),
        ¬ forall q : Fin d,
          reluApproxPhaseShiftedFineLower M orderC orderF phase b t q + R⁻¹ <= x q /\
            x q <= reluApproxPhaseShiftedFineUpper M orderC orderF phase b t q - R⁻¹) ->
      |phaseApprox| <= unsafeBound) :
    |phaseApprox -
      (Finset.univ.sum fun b : Fin (M ^ d) =>
        Finset.univ.sum fun t : Fin (M ^ d) =>
          axisAlignedBoxTentWeight
              (twoScaleShiftedCenter M orderC orderF phase b t)
              (twoScaleShiftedScale M phase b t) x * value (b, t))| <=
      eps + unsafeBound +
        Bval * (((M ^ 2 - 1 : Nat) : Real) * R⁻¹) := by
  let target := Finset.univ.sum fun b : Fin (M ^ d) =>
    Finset.univ.sum fun t : Fin (M ^ d) =>
      axisAlignedBoxTentWeight
          (twoScaleShiftedCenter M orderC orderF phase b t)
          (twoScaleShiftedScale M phase b t) x * value (b, t)
  let delta := ((M ^ 2 - 1 : Nat) : Real) * R⁻¹
  have hdelta : 0 <= delta := by
    dsimp [delta]
    exact mul_nonneg (by positivity) (inv_nonneg.mpr hR.le)
  by_cases hex : exists active : Fin (M ^ d) × Fin (M ^ d),
      forall q : Fin d,
        reluApproxPhaseShiftedFineLower M orderC orderF phase
              active.1 active.2 q + R⁻¹ <= x q /\
          x q <= reluApproxPhaseShiftedFineUpper M orderC orderF phase
              active.1 active.2 q - R⁻¹
  · obtain ⟨active, hsafe⟩ := hex
    have hcollapse := reluApproxPhaseShifted_weighted_sum_eq_of_safe
      hM orderC orderF phase hR x active hsafe value
    change |phaseApprox - target| <= _
    rw [show target =
        axisAlignedBoxTentWeight
            (twoScaleShiftedCenter M orderC orderF phase active.1 active.2)
            (twoScaleShiftedScale M phase active.1 active.2) x *
          value active by exact hcollapse]
    calc
      |phaseApprox -
          axisAlignedBoxTentWeight
              (twoScaleShiftedCenter M orderC orderF phase active.1 active.2)
              (twoScaleShiftedScale M phase active.1 active.2) x *
            value active| <= eps := hsafeError active hsafe
      _ <= eps + unsafeBound +
          Bval * (((M ^ 2 - 1 : Nat) : Real) * R⁻¹) := by
        have hmargin : 0 <= ((M ^ 2 - 1 : Nat) : Real) * R⁻¹ :=
          mul_nonneg (by positivity) (inv_nonneg.mpr hR.le)
        nlinarith [mul_nonneg hBval hmargin]
  · have hunsafe : forall (b t : Fin (M ^ d)),
        ¬ forall q : Fin d,
          reluApproxPhaseShiftedFineLower M orderC orderF phase b t q + R⁻¹ <= x q /\
            x q <= reluApproxPhaseShiftedFineUpper M orderC orderF phase b t q - R⁻¹ := by
      intro b t hsafe
      exact hex ⟨(b, t), hsafe⟩
    have htarget : |target| <= Bval * delta := by
      dsimp [target, delta]
      exact reluApproxPhaseShifted_phase_weighted_sum_abs_le_selector_margin
        hM orderC orderF phase hR hBval x value hvalue hunsafe
    have houtput : |phaseApprox| <= unsafeBound := hunsafeOutput hunsafe
    change |phaseApprox - target| <= _
    calc
      |phaseApprox - target| <= |phaseApprox| + |target| := abs_sub _ _
      _ <= unsafeBound + Bval * delta := add_le_add houtput htarget
      _ <= eps + unsafeBound + Bval * delta := by linarith

/-- Paper Lemma 15's safe/boundary-shell split for one shifted phase.  On a
safe cell the phase sum collapses to that cell; if no safe cell exists, both
the target phase and the robust network output are controlled by the selector
margin. -/
private theorem reluApproxPhaseShifted_phase_robust_approximation_error
    {d M : Nat} (hM : 2 <= M)
    (orderC orderF : Fin (M ^ d) ≃ (Fin d -> Fin M))
    (phase : Fin d -> Fin 2) {R Bval eps : Real}
    (hR : 0 < R) (hBval : 0 <= Bval) (heps : 0 <= eps)
    (x : Fin d -> Real)
    (value : (Fin (M ^ d) × Fin (M ^ d)) -> Real)
    (hvalue : forall p, |value p| <= Bval)
    (phaseApprox : Real)
    (hsafeError : forall active : Fin (M ^ d) × Fin (M ^ d),
      (forall q : Fin d,
        reluApproxPhaseShiftedFineLower M orderC orderF phase
              active.1 active.2 q + R⁻¹ <= x q /\
          x q <= reluApproxPhaseShiftedFineUpper M orderC orderF phase
              active.1 active.2 q - R⁻¹) ->
      |phaseApprox -
        axisAlignedBoxTentWeight
            (twoScaleShiftedCenter M orderC orderF phase active.1 active.2)
            (twoScaleShiftedScale M phase active.1 active.2) x *
          value active| <= eps)
    (hunsafeOutput :
      (forall (b t : Fin (M ^ d)),
        ¬ forall q : Fin d,
          reluApproxPhaseShiftedFineLower M orderC orderF phase b t q + R⁻¹ <= x q /\
            x q <= reluApproxPhaseShiftedFineUpper M orderC orderF phase b t q - R⁻¹) ->
      |phaseApprox| <= Bval * (((M ^ 2 - 1 : Nat) : Real) * R⁻¹)) :
    |phaseApprox -
      (Finset.univ.sum fun b : Fin (M ^ d) =>
        Finset.univ.sum fun t : Fin (M ^ d) =>
          axisAlignedBoxTentWeight
              (twoScaleShiftedCenter M orderC orderF phase b t)
              (twoScaleShiftedScale M phase b t) x * value (b, t))| <=
      eps + 2 * (Bval * (((M ^ 2 - 1 : Nat) : Real) * R⁻¹)) := by
  let target := Finset.univ.sum fun b : Fin (M ^ d) =>
    Finset.univ.sum fun t : Fin (M ^ d) =>
      axisAlignedBoxTentWeight
          (twoScaleShiftedCenter M orderC orderF phase b t)
          (twoScaleShiftedScale M phase b t) x * value (b, t)
  let delta := ((M ^ 2 - 1 : Nat) : Real) * R⁻¹
  have hdelta : 0 <= delta := by
    dsimp [delta]
    exact mul_nonneg (by positivity) (inv_nonneg.mpr hR.le)
  by_cases hex : exists active : Fin (M ^ d) × Fin (M ^ d),
      forall q : Fin d,
        reluApproxPhaseShiftedFineLower M orderC orderF phase
              active.1 active.2 q + R⁻¹ <= x q /\
          x q <= reluApproxPhaseShiftedFineUpper M orderC orderF phase
              active.1 active.2 q - R⁻¹
  · obtain ⟨active, hsafe⟩ := hex
    have hcollapse := reluApproxPhaseShifted_weighted_sum_eq_of_safe
      hM orderC orderF phase hR x active hsafe value
    change |phaseApprox - target| <= _
    rw [show target =
        axisAlignedBoxTentWeight
            (twoScaleShiftedCenter M orderC orderF phase active.1 active.2)
            (twoScaleShiftedScale M phase active.1 active.2) x *
          value active by exact hcollapse]
    exact le_trans (hsafeError active hsafe)
      (le_add_of_nonneg_right (mul_nonneg (by norm_num)
        (mul_nonneg hBval hdelta)))
  · have hunsafe : forall (b t : Fin (M ^ d)),
        ¬ forall q : Fin d,
          reluApproxPhaseShiftedFineLower M orderC orderF phase b t q + R⁻¹ <= x q /\
            x q <= reluApproxPhaseShiftedFineUpper M orderC orderF phase b t q - R⁻¹ := by
      intro b t hsafe
      exact hex ⟨(b, t), hsafe⟩
    have htarget : |target| <= Bval * delta := by
      dsimp [target, delta]
      exact reluApproxPhaseShifted_phase_weighted_sum_abs_le_selector_margin
        hM orderC orderF phase hR hBval x value hvalue hunsafe
    have houtput : |phaseApprox| <= Bval * delta := by
      simpa [delta] using hunsafeOutput hunsafe
    change |phaseApprox - target| <= _
    calc
      |phaseApprox - target| <= |phaseApprox| + |target| := abs_sub _ _
      _ <= Bval * delta + Bval * delta := add_le_add houtput htarget
      _ <= eps + 2 * (Bval * delta) := by ring_nf; linarith

/-- The two-margin boundary suppression used in the deep paper construction.
The coarse/fine selectors are exact on boxes shrunken by `R⁻¹`.  The two
checkers scan those already-shrunken boxes, so they vanish on the boxes
shrunken by `2 * R⁻¹` and are identically one before either selector can cease
to be exact.  Consequently the three-branch clip is globally accurate even
though the recursive Taylor state is specified only on uniquely selected
coarse and fine cells. -/
private theorem reluApproxPhaseShifted_twoMarginBoundaryClip_phase_error
    {d M : Nat} (hM : 2 <= M)
    (orderC orderF : Fin (M ^ d) ≃ (Fin d -> Fin M))
    (phase : Fin d -> Fin 2) {R Bval eps Bclip : Real}
    (hR : 2 <= R) (hBval : 0 <= Bval) (heps : 0 <= eps)
    (hBclip : 0 <= Bclip)
    (x : Fin d -> Real)
    (value : (Fin (M ^ d) × Fin (M ^ d)) -> Real)
    (hvalue : forall p, |value p| <= Bval)
    (raw coarseCheck fineCheck : Real)
    (hrawBound : |raw| <= Bclip)
    (hcoarseCheck :
      coarseCheck = reluApproxBoundaryCheck R
        (fun b q =>
          reluApproxPhaseShiftedCoarseLower M orderC phase b q + R⁻¹)
        (fun b q =>
          reluApproxPhaseShiftedCoarseUpper M orderC phase b q - R⁻¹) x)
    (hfineCheck : forall activeCoarse : Fin (M ^ d),
      (forall q,
        reluApproxPhaseShiftedCoarseLower M orderC phase activeCoarse q + R⁻¹ <= x q /\
          x q <= reluApproxPhaseShiftedCoarseUpper M orderC phase activeCoarse q - R⁻¹) ->
      (forall i, i ≠ activeCoarse -> exists q,
        x q <= reluApproxPhaseShiftedCoarseLower M orderC phase i q \/
          reluApproxPhaseShiftedCoarseUpper M orderC phase i q <= x q) ->
      fineCheck = reluApproxBoundaryCheck R
        (fun t q =>
          reluApproxPhaseShiftedFineLower
            M orderC orderF phase activeCoarse t q + R⁻¹)
        (fun t q =>
          reluApproxPhaseShiftedFineUpper
            M orderC orderF phase activeCoarse t q - R⁻¹) x)
    (hrawError : forall (activeCoarse activeFine : Fin (M ^ d)),
      (forall q,
        reluApproxPhaseShiftedCoarseLower M orderC phase activeCoarse q + R⁻¹ <= x q /\
          x q <= reluApproxPhaseShiftedCoarseUpper M orderC phase activeCoarse q - R⁻¹) ->
      (forall i, i ≠ activeCoarse -> exists q,
        x q <= reluApproxPhaseShiftedCoarseLower M orderC phase i q \/
          reluApproxPhaseShiftedCoarseUpper M orderC phase i q <= x q) ->
      (forall q,
        reluApproxPhaseShiftedFineLower M orderC orderF phase
              activeCoarse activeFine q + R⁻¹ <= x q /\
          x q <= reluApproxPhaseShiftedFineUpper M orderC orderF phase
              activeCoarse activeFine q - R⁻¹) ->
      (forall t, t ≠ activeFine -> exists q,
        x q <= reluApproxPhaseShiftedFineLower
            M orderC orderF phase activeCoarse t q \/
          reluApproxPhaseShiftedFineUpper
            M orderC orderF phase activeCoarse t q <= x q) ->
      |raw -
        axisAlignedBoxTentWeight
            (twoScaleShiftedCenter M orderC orderF phase
              activeCoarse activeFine)
            (twoScaleShiftedScale M phase activeCoarse activeFine) x *
          value (activeCoarse, activeFine)| <= eps) :
    |reluApproxBoundaryClip Bclip raw (max coarseCheck fineCheck) -
      (Finset.univ.sum fun b : Fin (M ^ d) =>
        Finset.univ.sum fun t : Fin (M ^ d) =>
          axisAlignedBoxTentWeight
              (twoScaleShiftedCenter M orderC orderF phase b t)
              (twoScaleShiftedScale M phase b t) x * value (b, t))| <=
      2 * eps + 2 *
        (Bval * (((M ^ 2 - 1 : Nat) : Real) * (R / 2)⁻¹)) := by
  classical
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hRone : 1 <= R := le_trans (by norm_num) hR
  have hRinv : 0 <= R⁻¹ := (inv_pos.mpr hRpos).le
  have hhalfPos : 0 < R / 2 := by positivity
  have hhalfInv : (R / 2)⁻¹ = 2 * R⁻¹ := by
    field_simp [ne_of_gt hRpos]
  let coarseLower : Fin (M ^ d) -> Fin d -> Real := fun b q =>
    reluApproxPhaseShiftedCoarseLower M orderC phase b q
  let coarseUpper : Fin (M ^ d) -> Fin d -> Real := fun b q =>
    reluApproxPhaseShiftedCoarseUpper M orderC phase b q
  let fineLower : Fin (M ^ d) -> Fin (M ^ d) -> Fin d -> Real := fun b t q =>
    reluApproxPhaseShiftedFineLower M orderC orderF phase b t q
  let fineUpper : Fin (M ^ d) -> Fin (M ^ d) -> Fin d -> Real := fun b t q =>
    reluApproxPhaseShiftedFineUpper M orderC orderF phase b t q
  have hinactive_of_safe : forall {T : Nat}
      (lower upper : Fin T -> Fin d -> Real)
      (hdisjoint : forall i j : Fin T, i ≠ j -> exists q,
        upper i q <= lower j q \/ upper j q <= lower i q)
      (active : Fin T),
      (forall q, lower active q <= x q /\ x q <= upper active q) ->
      forall i, i ≠ active -> exists q,
        x q <= lower i q \/ upper i q <= x q := by
    intro T lower upper hdisjoint active hactive i hi
    obtain ⟨q, hsep | hsep⟩ := hdisjoint active i (Ne.symm hi)
    · exact ⟨q, Or.inl (le_trans (hactive q).2 hsep)⟩
    · exact ⟨q, Or.inr (le_trans hsep (hactive q).1)⟩
  have hshrink_disjoint : forall {T : Nat}
      (lower upper : Fin T -> Fin d -> Real),
      (forall i j : Fin T, i ≠ j -> exists q,
        upper i q <= lower j q \/ upper j q <= lower i q) ->
      forall i j : Fin T, i ≠ j -> exists q,
        upper i q - R⁻¹ <= lower j q + R⁻¹ \/
          upper j q - R⁻¹ <= lower i q + R⁻¹ := by
    intro T lower upper hdisjoint i j hij
    obtain ⟨q, hsep | hsep⟩ := hdisjoint i j hij
    · exact ⟨q, Or.inl (by linarith)⟩
    · exact ⟨q, Or.inr (by linarith)⟩
  have hcoarseDisjoint : forall b c : Fin (M ^ d), b ≠ c -> exists q,
      coarseUpper b q <= coarseLower c q \/
        coarseUpper c q <= coarseLower b q := by
    simpa [coarseLower, coarseUpper] using
      reluApprox_phaseShiftedCoarseBoxes_pairwise_disjoint
        hM orderC phase
  have hfineDisjoint : forall b : Fin (M ^ d),
      forall s t : Fin (M ^ d), s ≠ t -> exists q,
        fineUpper b s q <= fineLower b t q \/
          fineUpper b t q <= fineLower b s q := by
    intro b s t hst
    simpa [fineLower, fineUpper] using
      reluApprox_phaseShiftedFineBoxes_pairwise_disjoint
        hM orderC orderF phase b s t hst
  have hcoarseCheckIcc : coarseCheck ∈ Set.Icc (0 : Real) 1 := by
    rw [hcoarseCheck]
    exact reluApproxBoundaryCheck_mem_Icc_of_pairwise_disjoint
      hRpos hRone _ _ (hshrink_disjoint coarseLower coarseUpper hcoarseDisjoint) x
  let margin : Real := ((M ^ 2 - 1 : Nat) : Real) * (R / 2)⁻¹
  let phaseApprox : Real :=
    reluApproxBoundaryClip Bclip raw (max coarseCheck fineCheck)
  have hsafeError : forall active : Fin (M ^ d) × Fin (M ^ d),
      (forall q : Fin d,
        fineLower active.1 active.2 q + (R / 2)⁻¹ <= x q /\
          x q <= fineUpper active.1 active.2 q - (R / 2)⁻¹) ->
      |phaseApprox -
        axisAlignedBoxTentWeight
            (twoScaleShiftedCenter M orderC orderF phase active.1 active.2)
            (twoScaleShiftedScale M phase active.1 active.2) x *
          value active| <= eps := by
    intro active hdeepFine
    have hfineSelector : forall q,
        fineLower active.1 active.2 q + R⁻¹ <= x q /\
          x q <= fineUpper active.1 active.2 q - R⁻¹ := by
      intro q
      rw [hhalfInv] at hdeepFine
      constructor <;> linarith [(hdeepFine q).1, (hdeepFine q).2]
    have hcoarseSelector : forall q,
        coarseLower active.1 q + R⁻¹ <= x q /\
          x q <= coarseUpper active.1 q - R⁻¹ := by
      intro q
      obtain ⟨hl, hu⟩ := reluApproxPhaseShiftedFineBox_subset_coarse
        hM orderC orderF phase active.1 active.2 q
      constructor
      · exact le_trans (add_le_add hl le_rfl) (hfineSelector q).1
      · exact le_trans (hfineSelector q).2 (sub_le_sub_right hu R⁻¹)
    have hcoarseInactive := hinactive_of_safe coarseLower coarseUpper
      hcoarseDisjoint active.1
      (fun q => ⟨le_trans (le_add_of_nonneg_right hRinv) (hcoarseSelector q).1,
        le_trans (hcoarseSelector q).2 (sub_le_self _ hRinv)⟩)
    have hfineInactive := hinactive_of_safe (fineLower active.1) (fineUpper active.1)
      (hfineDisjoint active.1) active.2
      (fun q => ⟨le_trans (le_add_of_nonneg_right hRinv) (hfineSelector q).1,
        le_trans (hfineSelector q).2 (sub_le_self _ hRinv)⟩)
    have hcoarseDeep : forall q,
        (coarseLower active.1 q + R⁻¹) + R⁻¹ <= x q /\
          x q <= (coarseUpper active.1 q - R⁻¹) - R⁻¹ := by
      intro q
      rw [hhalfInv] at hdeepFine
      obtain ⟨hl, hu⟩ := reluApproxPhaseShiftedFineBox_subset_coarse
        hM orderC orderF phase active.1 active.2 q
      constructor <;> dsimp [coarseLower, coarseUpper, fineLower, fineUpper] at * <;>
        linarith [(hdeepFine q).1, (hdeepFine q).2]
    have hfineDeep : forall q,
        (fineLower active.1 active.2 q + R⁻¹) + R⁻¹ <= x q /\
          x q <= (fineUpper active.1 active.2 q - R⁻¹) - R⁻¹ := by
      intro q
      rw [hhalfInv] at hdeepFine
      constructor <;> linarith [(hdeepFine q).1, (hdeepFine q).2]
    have hcoarseInnerInactive := hinactive_of_safe
      (fun b q => coarseLower b q + R⁻¹)
      (fun b q => coarseUpper b q - R⁻¹)
      (hshrink_disjoint coarseLower coarseUpper hcoarseDisjoint)
      active.1 (fun q => by
        constructor <;> linarith [(hcoarseDeep q).1, (hcoarseDeep q).2])
    have hfineInnerInactive := hinactive_of_safe
      (fun t q => fineLower active.1 t q + R⁻¹)
      (fun t q => fineUpper active.1 t q - R⁻¹)
      (hshrink_disjoint (fineLower active.1) (fineUpper active.1)
        (hfineDisjoint active.1)) active.2 (fun q => by
          constructor <;> linarith [(hfineDeep q).1, (hfineDeep q).2])
    have hcoarseZero : coarseCheck = 0 := by
      rw [hcoarseCheck]
      exact reluApproxBoundaryCheck_eq_zero_of_unique hRpos hRone _ _ x active.1
        hcoarseDeep hcoarseInnerInactive
    have hfineEq := hfineCheck active.1 hcoarseSelector hcoarseInactive
    have hfineZero : fineCheck = 0 := by
      rw [hfineEq]
      exact reluApproxBoundaryCheck_eq_zero_of_unique hRpos hRone _ _ x active.2
        hfineDeep hfineInnerInactive
    dsimp [phaseApprox]
    rw [hcoarseZero, hfineZero, max_self,
      reluApproxBoundaryClip_eq_raw]
    exact hrawError active.1 active.2 hcoarseSelector hcoarseInactive
      hfineSelector hfineInactive
  have hunsafeOutput :
      (forall (b t : Fin (M ^ d)),
        ¬ forall q : Fin d,
          fineLower b t q + (R / 2)⁻¹ <= x q /\
            x q <= fineUpper b t q - (R / 2)⁻¹) ->
      |phaseApprox| <= eps + Bval * margin := by
    intro hnoDeep
    by_cases hselector : exists active : Fin (M ^ d) × Fin (M ^ d),
        forall q,
          fineLower active.1 active.2 q + R⁻¹ <= x q /\
            x q <= fineUpper active.1 active.2 q - R⁻¹
    · obtain ⟨active, hfineSelector⟩ := hselector
      have hcoarseSelector : forall q,
          coarseLower active.1 q + R⁻¹ <= x q /\
            x q <= coarseUpper active.1 q - R⁻¹ := by
        intro q
        obtain ⟨hl, hu⟩ := reluApproxPhaseShiftedFineBox_subset_coarse
          hM orderC orderF phase active.1 active.2 q
        constructor
        · exact le_trans (add_le_add hl le_rfl) (hfineSelector q).1
        · exact le_trans (hfineSelector q).2 (sub_le_sub_right hu R⁻¹)
      have hcoarseInactive := hinactive_of_safe coarseLower coarseUpper
        hcoarseDisjoint active.1
        (fun q => ⟨le_trans (le_add_of_nonneg_right hRinv) (hcoarseSelector q).1,
          le_trans (hcoarseSelector q).2 (sub_le_self _ hRinv)⟩)
      have hfineInactive := hinactive_of_safe (fineLower active.1) (fineUpper active.1)
        (hfineDisjoint active.1) active.2
        (fun q => ⟨le_trans (le_add_of_nonneg_right hRinv) (hfineSelector q).1,
          le_trans (hfineSelector q).2 (sub_le_self _ hRinv)⟩)
      have hfineEq := hfineCheck active.1 hcoarseSelector hcoarseInactive
      have hfineIcc : fineCheck ∈ Set.Icc (0 : Real) 1 := by
        rw [hfineEq]
        exact reluApproxBoundaryCheck_mem_Icc_of_pairwise_disjoint
          hRpos hRone _ _
            (hshrink_disjoint (fineLower active.1) (fineUpper active.1)
              (hfineDisjoint active.1)) x
      have hcheckNonneg : 0 <= max coarseCheck fineCheck := by
        exact le_trans hfineIcc.1 (le_max_right _ _)
      have hclipRaw : |phaseApprox| <= |raw| := by
        dsimp [phaseApprox]
        exact abs_reluApproxBoundaryClip_le_abs hBclip hcheckNonneg
      have hrawErr := hrawError active.1 active.2 hcoarseSelector hcoarseInactive
        hfineSelector hfineInactive
      have htent : axisAlignedBoxTentWeight
          (twoScaleShiftedCenter M orderC orderF phase active.1 active.2)
          (twoScaleShiftedScale M phase active.1 active.2) x <=
          ((M ^ 2 - 1 : Nat) : Real) * (R / 2)⁻¹ := by
        exact reluApproxPhaseShiftedTentWeight_le_selector_margin
          hM orderC orderF phase active.1 active.2 hhalfPos x
            (hnoDeep active.1 active.2)
      have htentNonneg : 0 <= axisAlignedBoxTentWeight
          (twoScaleShiftedCenter M orderC orderF phase active.1 active.2)
          (twoScaleShiftedScale M phase active.1 active.2) x :=
        (axisAlignedBoxTentWeight_bounds_and_support _ _ _
          (fun q => by simp [twoScaleShiftedScale])).1
      have htarget : |axisAlignedBoxTentWeight
            (twoScaleShiftedCenter M orderC orderF phase active.1 active.2)
            (twoScaleShiftedScale M phase active.1 active.2) x *
          value active| <= Bval * margin := by
        rw [abs_mul, abs_of_nonneg htentNonneg]
        dsimp [margin]
        calc
          axisAlignedBoxTentWeight
                (twoScaleShiftedCenter M orderC orderF phase active.1 active.2)
                (twoScaleShiftedScale M phase active.1 active.2) x *
              |value active| <=
              (((M ^ 2 - 1 : Nat) : Real) * (R / 2)⁻¹) * Bval :=
            mul_le_mul htent (hvalue active) (abs_nonneg _)
              (mul_nonneg (by positivity) (inv_nonneg.mpr hhalfPos.le))
          _ = Bval * (((M ^ 2 - 1 : Nat) : Real) * (R / 2)⁻¹) := by ring
      calc
        |phaseApprox| <= |raw| := hclipRaw
        _ <= |raw -
              axisAlignedBoxTentWeight
                  (twoScaleShiftedCenter M orderC orderF phase
                    active.1 active.2)
                  (twoScaleShiftedScale M phase active.1 active.2) x *
                value active| +
              |axisAlignedBoxTentWeight
                  (twoScaleShiftedCenter M orderC orderF phase
                    active.1 active.2)
                  (twoScaleShiftedScale M phase active.1 active.2) x *
                value active| := by
            calc
              |raw| = |(raw -
                    axisAlignedBoxTentWeight
                        (twoScaleShiftedCenter M orderC orderF phase
                          active.1 active.2)
                        (twoScaleShiftedScale M phase active.1 active.2) x *
                      value active) +
                    axisAlignedBoxTentWeight
                        (twoScaleShiftedCenter M orderC orderF phase
                          active.1 active.2)
                        (twoScaleShiftedScale M phase active.1 active.2) x *
                      value active| := by congr 1 <;> ring
              _ <= _ := abs_add_le _ _
        _ <= eps + Bval * margin := add_le_add hrawErr htarget
    · push_neg at hselector
      have hclipZero : |phaseApprox| <= 0 := by
        have hcheckOne : 1 <= max coarseCheck fineCheck := by
          by_cases hcoarseSelectorExists : exists activeCoarse : Fin (M ^ d),
              forall q,
                coarseLower activeCoarse q + R⁻¹ <= x q /\
                  x q <= coarseUpper activeCoarse q - R⁻¹
          · obtain ⟨activeCoarse, hcoarseSelector⟩ := hcoarseSelectorExists
            have hcoarseInactive := hinactive_of_safe coarseLower coarseUpper
              hcoarseDisjoint activeCoarse
              (fun q => ⟨le_trans (le_add_of_nonneg_right hRinv)
                  (hcoarseSelector q).1,
                le_trans (hcoarseSelector q).2 (sub_le_self _ hRinv)⟩)
            have hfineEq := hfineCheck activeCoarse hcoarseSelector hcoarseInactive
            have hallOutside : forall t : Fin (M ^ d), exists q,
                x q <= fineLower activeCoarse t q + R⁻¹ \/
                  fineUpper activeCoarse t q - R⁻¹ <= x q := by
              intro t
              have hn := hselector (activeCoarse, t)
              obtain ⟨q, hq⟩ := hn
              by_cases hl : fineLower activeCoarse t q + R⁻¹ <= x q
              · exact ⟨q, Or.inr (le_of_lt (hq hl))⟩
              · exact ⟨q, Or.inl (le_of_not_ge hl)⟩
            have hfineOne : fineCheck = 1 := by
              rw [hfineEq]
              exact reluApproxBoundaryCheck_eq_one_of_all_outside
                hRpos hRone _ _ x hallOutside
            rw [hfineOne]
            exact le_max_right _ _
          · push_neg at hcoarseSelectorExists
            have hallOutside : forall b : Fin (M ^ d), exists q,
                x q <= coarseLower b q + R⁻¹ \/
                  coarseUpper b q - R⁻¹ <= x q := by
              intro b
              have hn := hcoarseSelectorExists b
              obtain ⟨q, hq⟩ := hn
              by_cases hl : coarseLower b q + R⁻¹ <= x q
              · exact ⟨q, Or.inr (le_of_lt (hq hl))⟩
              · exact ⟨q, Or.inl (le_of_not_ge hl)⟩
            have hcoarseOne : coarseCheck = 1 := by
              rw [hcoarseCheck]
              exact reluApproxBoundaryCheck_eq_one_of_all_outside
                hRpos hRone _ _ x hallOutside
            rw [hcoarseOne]
            exact le_max_left _ _
        have hzero := abs_reluApproxBoundaryClip_le_complement_of_le
          hBclip hrawBound (show (1 : Real) ∈ Set.Icc 0 1 by simp) hcheckOne
        simpa [phaseApprox] using hzero
      have hnonneg : 0 <= eps + Bval * margin := by
        dsimp [margin]
        positivity
      exact le_trans hclipZero hnonneg
  have hresult := reluApproxPhaseShifted_phase_robust_error_of_unsafe_bound
    hM orderC orderF phase hhalfPos hBval heps
      (add_nonneg heps (mul_nonneg hBval (by dsimp [margin]; positivity)))
      x value hvalue phaseApprox hsafeError hunsafeOutput
  dsimp [phaseApprox, margin, fineLower, fineUpper] at hresult ⊢
  linarith

/-- Concrete network form of the two-margin shifted-phase robustifier.  It
combines an already compiled weighted Taylor branch with a direct coarse
checker and the hierarchical `O(M^d)` fine checker, then compiles the final
three-branch clipping program. -/
private theorem exists_reluApproxPhaseShifted_twoMarginBoundaryClipNet
    {d r M Dfine Wfine : Nat} (hd : 0 < d) (hM : 2 <= M)
    (orderC orderF : Fin (M ^ d) ≃ (Fin d -> Fin M))
    (horderStep : forall (k : Nat) (hk : k + 1 < M ^ d),
      exists q : Fin d,
        Int.natAbs
          ((orderF ⟨k + 1, hk⟩ q).val -
            (orderF ⟨k, Nat.lt_of_succ_lt hk⟩ q).val) = 1 /\
        forall u : Fin d, u ≠ q ->
          orderF ⟨k + 1, hk⟩ u =
            orderF ⟨k, Nat.lt_of_succ_lt hk⟩ u)
    (phase : Fin d -> Fin 2) {R Bval eps Bclip : Real}
    (hR : 2 <= R) (hBval : 0 <= Bval) (heps : 0 <= eps)
    (hBclip : 0 <= Bclip)
    (value : (Fin (M ^ d) × Fin (M ^ d)) ->
      (Fin d -> Real) -> Real)
    (hvalue : forall p x,
      (forall q, x q ∈ Set.Icc (0 : Real) 1) -> |value p x| <= Bval)
    (Nraw : FullyConnectedReLUNet d)
    (hrawBound : forall x : Fin d -> Real,
      (forall q, x q ∈ Set.Icc (0 : Real) 1) -> |Nraw.realize x| <= Bclip)
    (hrawError : forall (x : Fin d -> Real),
      (forall q, x q ∈ Set.Icc (0 : Real) 1) ->
      forall (activeCoarse activeFine : Fin (M ^ d)),
      (forall q,
        reluApproxPhaseShiftedCoarseLower M orderC phase activeCoarse q + R⁻¹ <= x q /\
          x q <= reluApproxPhaseShiftedCoarseUpper M orderC phase activeCoarse q - R⁻¹) ->
      (forall i, i ≠ activeCoarse -> exists q,
        x q <= reluApproxPhaseShiftedCoarseLower M orderC phase i q \/
          reluApproxPhaseShiftedCoarseUpper M orderC phase i q <= x q) ->
      (forall q,
        reluApproxPhaseShiftedFineLower M orderC orderF phase
              activeCoarse activeFine q + R⁻¹ <= x q /\
          x q <= reluApproxPhaseShiftedFineUpper M orderC orderF phase
              activeCoarse activeFine q - R⁻¹) ->
      (forall t, t ≠ activeFine -> exists q,
        x q <= reluApproxPhaseShiftedFineLower
            M orderC orderF phase activeCoarse t q \/
          reluApproxPhaseShiftedFineUpper
            M orderC orderF phase activeCoarse t q <= x q) ->
      |Nraw.realize x -
        axisAlignedBoxTentWeight
            (twoScaleShiftedCenter M orderC orderF phase
              activeCoarse activeFine)
            (twoScaleShiftedScale M phase activeCoarse activeFine) x *
          value (activeCoarse, activeFine) x| <= eps)
    (hFineDepth : 2 * ((M ^ d) * 2 + (M ^ d) * 3) + 1 <= Dfine)
    (hFineWidth :
      let s := reluApproxVectorBoxScanStateSize d
        (Fintype.card (ReLUApproxFineAccumulator d r))
      let hscan := reluApproxVectorBoxScanFeatureSize d
        (Fintype.card (ReLUApproxFineAccumulator d r))
      let h := hscan + (hscan + fineTaylorFeatureSize d r 0)
      (s + s) + h <= Wfine) :
    exists N : FullyConnectedReLUNet d,
      0 < N.depth /\
      N.depth <= 2 *
          (Nraw.depth + (M ^ d + 1) * 3 + Dfine + 10) + 1 /\
      N.width <= 42 *
        (d + 3 + Nraw.width + (2 * d + ((d + d) + 2) + 3) + Wfine + 5) /\
      N.parameterCount <= fullyConnectedReLUParameterCount d N.depth N.width /\
      forall x : Fin d -> Real,
        (forall q, x q ∈ Set.Icc (0 : Real) 1) ->
        |N.realize x -
          (Finset.univ.sum fun b : Fin (M ^ d) =>
            Finset.univ.sum fun t : Fin (M ^ d) =>
              axisAlignedBoxTentWeight
                  (twoScaleShiftedCenter M orderC orderF phase b t)
                  (twoScaleShiftedScale M phase b t) x * value (b, t) x)| <=
          2 * eps + 2 *
            (Bval * (((M ^ 2 - 1 : Nat) : Real) * (R / 2)⁻¹)) := by
  classical
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR
  let innerRadius : Real :=
    ((M ^ 2 - 1 : Nat) : Real)⁻¹ - R⁻¹
  obtain ⟨Ncoarse, _hNcoarseDepth, hNcoarseDepthLe,
      hNcoarseWidth, _hNcoarseParam, hNcoarseRealize⟩ :=
    exists_reluApproxBoundaryCheckNet hd R
      (fun b q =>
        reluApproxPhaseShiftedCoarseLower M orderC phase b q + R⁻¹)
      (fun b q =>
        reluApproxPhaseShiftedCoarseUpper M orderC phase b q - R⁻¹)
  obtain ⟨Nfine, hNfineDepth, hNfineWidth, _hNfineParam,
      hNfineRealize⟩ :=
    exists_reluApproxPhaseShiftedHierarchicalFineBoundaryCheckNetRadius_exactDepth
      hd hM orderC orderF horderStep phase R R innerRadius hR
        hFineDepth hFineWidth
  let P := reluApproxThreeBranchBoundaryClipProgram Bclip Nraw Ncoarse Nfine
  let D : Nat := 2 * P.stepCount + 1
  let W : Nat := (P.stateSize + P.stateSize) + P.featureSize
  obtain ⟨N, hNdepth, hNwidth, hNparam, hNrealize⟩ :=
    exists_reluApproxThreeBranchBoundaryClipNet_exactDepth
      Bclip Nraw Ncoarse Nfine (D := D) (W := W) le_rfl le_rfl
  refine ⟨N, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hNdepth]
    dsimp [D]
    omega
  · rw [hNdepth]
    dsimp [D, P, reluApproxThreeBranchBoundaryClipProgram,
      ReLUApproxMacroProgram.appendNetwork, reluApproxInputRegisterProgram,
      reluApproxBinaryMaxNet, reluApproxBoundaryClipNet]
    omega
  · apply le_trans hNwidth
    dsimp [W, P, reluApproxThreeBranchBoundaryClipProgram,
      ReLUApproxMacroProgram.appendNetwork, reluApproxInputRegisterProgram,
      reluApproxMacroWithPersistentSuffixFeatureSize,
      reluApproxPersistentWorkFeatureSize,
      reluApproxBinaryMaxNet, reluApproxBoundaryClipNet]
    omega
  · rfl
  · intro x hx
    rw [hNrealize]
    apply reluApproxPhaseShifted_twoMarginBoundaryClip_phase_error
      hM orderC orderF phase hR hBval heps hBclip x (fun p => value p x)
        (fun p => hvalue p x hx)
        (Nraw.realize x) (Ncoarse.realize x) (Nfine.realize x)
        (hrawBound x hx)
    · exact hNcoarseRealize x
    · intro activeCoarse hactiveCoarse hinactiveCoarse
      rw [hNfineRealize x activeCoarse hactiveCoarse hinactiveCoarse]
      congr 1
      · funext t q
        dsimp [innerRadius]
        unfold reluApproxPhaseShiftedFineLower
        ring
      · funext t q
        dsimp [innerRadius]
        unfold reluApproxPhaseShiftedFineUpper
        ring
    · exact hrawError x hx

/-- Input radius used by the uniform Taylor-polynomial evaluator. -/
private noncomputable def reluApproxPhaseShiftedPolynomialInputRadius
    (A C : Real) : Real :=
  max 1 (A + C + 1)

/-- A canonical, resolution-independent propagation constant for the finite
Taylor polynomial evaluator. -/
private noncomputable def reluApproxPhaseShiftedPolynomialErrorConstant
    (d r : Nat) (A C : Real) : Real :=
  Classical.choose
    (exists_finiteCenteredMonomialPolynomialFixedWidthApproxError_linear_mul_error_bound
      (reluApproxPhaseShiftedPolynomialInputRadius A C)
      (le_trans (by norm_num) (le_max_left 1 (A + C + 1)))
      (fun a : TaylorMultiindex r d => reluApproxTaylorEvaluationDegree a))

private theorem reluApproxPhaseShiftedPolynomialErrorConstant_nonneg
    (d r : Nat) (A C : Real) :
    0 <= reluApproxPhaseShiftedPolynomialErrorConstant d r A C :=
  (Classical.choose_spec
    (exists_finiteCenteredMonomialPolynomialFixedWidthApproxError_linear_mul_error_bound
      (reluApproxPhaseShiftedPolynomialInputRadius A C)
      (le_trans (by norm_num) (le_max_left 1 (A + C + 1)))
      (fun a : TaylorMultiindex r d => reluApproxTaylorEvaluationDegree a))).1

private theorem reluApproxPhaseShiftedPolynomialErrorConstant_bound
    (d r : Nat) (A C e : Real) (he : 0 <= e) (he8 : e <= 8) :
    finiteCenteredMonomialPolynomialFixedWidthApproxError e
        (reluApproxPhaseShiftedPolynomialInputRadius A C) 1
        (Finset.univ : Finset (TaylorMultiindex r d)) (fun _ => (1 : Real))
        (fun a => reluApproxTaylorEvaluationDegree a) <=
      reluApproxPhaseShiftedPolynomialErrorConstant d r A C * e :=
  (Classical.choose_spec
    (exists_finiteCenteredMonomialPolynomialFixedWidthApproxError_linear_mul_error_bound
      (reluApproxPhaseShiftedPolynomialInputRadius A C)
      (le_trans (by norm_num) (le_max_left 1 (A + C + 1)))
      (fun a : TaylorMultiindex r d => reluApproxTaylorEvaluationDegree a))).2 e he he8

/-- Canonical rate constant for the raw branch of one shifted two-scale phase. -/
private noncomputable def reluApproxPhaseShiftedRawRateConstant
    (d r : Nat) (A C : Real) : Real :=
  let Rin := reluApproxPhaseShiftedPolynomialInputRadius A C
  let Rt := (Fintype.card (TaylorMultiindex r d) : Real) * Rin ^ (r + 1)
  let Kpoly := reluApproxPhaseShiftedPolynomialErrorConstant d r A C
  let Ktent := tentProductRateConstant d
  let Rprod := 1 + Rt + 8 * Kpoly + Ktent
  8 * Rprod ^ 2 + Rprod * Ktent + Rprod * (8 * Kpoly)

private theorem reluApproxPhaseShiftedRawRateConstant_nonneg
    (d r : Nat) {A C : Real} (hA : 0 <= A) (hC : 0 <= C) :
    0 <= reluApproxPhaseShiftedRawRateConstant d r A C := by
  have hRin : 0 <= reluApproxPhaseShiftedPolynomialInputRadius A C :=
    le_trans (by norm_num) (le_max_left 1 (A + C + 1))
  have hKpoly := reluApproxPhaseShiftedPolynomialErrorConstant_nonneg d r A C
  have hKtent := tentProductRateConstant_nonneg d
  unfold reluApproxPhaseShiftedRawRateConstant
  positivity

/-- Uniform depth factor for the raw network of one shifted two-scale phase. -/
private abbrev reluApproxPhaseShiftedRawDepthFactor (d r : Nat) : Nat :=
  2 * (5 + weightedTaylorDepthFactor d r + 2) + 1

/-- Uniform width bound for the raw network of one shifted two-scale phase. -/
private noncomputable def reluApproxPhaseShiftedRawWidthBound (d r : Nat) : Nat :=
  let cDigit := Nat.ceil (Real.exp (d : Real))
  let floorB := 4 + 2 * cDigit - 1
  let s := ReLUApproxCoarseFineStateSize d r
  let h := ReLUApproxCoarseFineFeatureSize d r floorB
  let w := weightedTaylorWidthBound d r
  6 * s + 6 * w + h

set_option maxHeartbeats 2000000 in
/-- The complete raw branch for one shifted phase.  The theorem constructs the
shared fine path, encodes all bounded Taylor corrections into finite base
tails, compiles the coarse/fine state machine, and appends the dynamic
tent-times-Taylor evaluator.  Its error is stated directly against the exact
Taylor polynomial at the selected shifted-grid center. -/
private theorem exists_reluApproxPhaseShifted_weightedTaylorRawNet
    {d r M : Nat} {beta C B A : Real}
    (hd : 0 < d) (hM : 2 <= M)
    (hbeta_pos : 0 < beta) (hbeta_le_one : beta <= 1)
    (hC_nonneg : 0 <= C) (hA_nonneg : 0 <= A)
    (orderC orderF : Fin (M ^ d) ≃ (Fin d -> Fin M))
    (horderStep : forall (k : Nat) (hk : k + 1 < M ^ d),
      exists q : Fin d,
        Int.natAbs
          ((orderF ⟨k + 1, hk⟩ q).val -
            (orderF ⟨k, Nat.lt_of_succ_lt hk⟩ q).val) = 1 /\
        forall u : Fin d, u ≠ q ->
          orderF ⟨k + 1, hk⟩ u =
            orderF ⟨k, Nat.lt_of_succ_lt hk⟩ u)
    (phase : Fin d -> Fin 2)
    (f : (Fin d -> Real) -> Real) (hf : f ∈ holderSmoothBall r beta C B)
    (hAcoeff : forall y : Fin d -> Real, forall a : TaylorMultiindex r d,
      |((Nat.factorial a.1.val : Real)⁻¹) *
        (iteratedFDeriv Real a.1.val f y)
          (fun k : Fin a.1.val => fun q : Fin d =>
            if q = a.2 k then 1 else 0)| <= A) :
    exists (R : Real) (Nraw : FullyConnectedReLUNet d),
      2 <= R /\
      Nraw.depth <= reluApproxPhaseShiftedRawDepthFactor d r * M ^ d /\
      Nraw.width <= reluApproxPhaseShiftedRawWidthBound d r /\
      ((M ^ 2 - 1 : Nat) : Real) * (R / 2)⁻¹ <=
        shallowReLUResolutionRate M r beta /\
      forall (x : Fin d -> Real) (activeCoarse activeFine : Fin (M ^ d)),
        (forall q,
          reluApproxPhaseShiftedCoarseLower M orderC phase activeCoarse q + R⁻¹ <= x q /\
            x q <= reluApproxPhaseShiftedCoarseUpper M orderC phase activeCoarse q - R⁻¹) ->
        (forall i, i ≠ activeCoarse -> exists q,
          x q <= reluApproxPhaseShiftedCoarseLower M orderC phase i q \/
            reluApproxPhaseShiftedCoarseUpper M orderC phase i q <= x q) ->
        (forall q,
          reluApproxPhaseShiftedFineLower M orderC orderF phase
                activeCoarse activeFine q + R⁻¹ <= x q /\
            x q <= reluApproxPhaseShiftedFineUpper M orderC orderF phase
                activeCoarse activeFine q - R⁻¹) ->
        (forall t, t ≠ activeFine -> exists q,
          x q <= reluApproxPhaseShiftedFineLower
              M orderC orderF phase activeCoarse t q \/
            reluApproxPhaseShiftedFineUpper
              M orderC orderF phase activeCoarse t q <= x q) ->
        |Nraw.realize x -
          axisAlignedBoxTentWeight
              (twoScaleShiftedCenter M orderC orderF phase
                activeCoarse activeFine)
              (twoScaleShiftedScale M phase activeCoarse activeFine) x *
            finiteLinearCombination
              (Finset.univ : Finset (TaylorMultiindex r d))
              (fun a => ((Nat.factorial a.1.val : Real)⁻¹) *
                (iteratedFDeriv Real a.1.val f
                  (twoScaleShiftedCenter M orderC orderF phase
                    activeCoarse activeFine))
                    (fun k : Fin a.1.val => fun q : Fin d =>
                      if q = a.2 k then 1 else 0))
              (fun a y => Finset.univ.prod fun k : Fin a.1.val =>
                y (a.2 k) -
                  twoScaleShiftedCenter M orderC orderF phase
                    activeCoarse activeFine (a.2 k)) x| <=
          reluApproxPhaseShiftedRawRateConstant d r A C *
              shallowReLUResolutionRate M r beta +
            (Fintype.card (TaylorMultiindex r d) : Real) *
              ((C + 1) * Real.rpow
                (2 * ((M ^ 2 - 1 : Nat) : Real)⁻¹)
                ((r : Real) + beta)) := by
  classical
  let T : Nat := M ^ d
  have hMpos : 0 < M := by omega
  have hTpos : 0 < T := by
    dsimp [T]
    exact Nat.pow_pos hMpos
  have hTone : 1 <= T := hTpos
  have hKnat : 0 < M ^ 2 - 1 := by
    have hM2 : 4 <= M ^ 2 := by
      have hh := Nat.mul_le_mul hM hM
      norm_num at hh
      simpa [pow_two] using hh
    omega
  let Kgrid : Real := ((M ^ 2 - 1 : Nat) : Real)
  have hKgrid_pos : 0 < Kgrid := by
    dsimp [Kgrid]
    exact_mod_cast hKnat
  let rho : Real := 2 * Kgrid⁻¹
  have hrho_pos : 0 < rho := by
    dsimp [rho]
    positivity
  have hrho_nonneg : 0 <= rho := hrho_pos.le
  have hKgridInv_le_one : Kgrid⁻¹ <= 1 := by
    apply (inv_le_one₀ hKgrid_pos).2
    dsimp [Kgrid]
    exact_mod_cast (show 1 <= M ^ 2 - 1 by omega)
  have hKgridTwo : (2 : Real) <= Kgrid := by
    dsimp [Kgrid]
    have hM2 : 4 <= M ^ 2 := by
      have hh := Nat.mul_le_mul hM hM
      norm_num at hh
      simpa [pow_two] using hh
    exact_mod_cast (show 2 <= M ^ 2 - 1 by omega)
  have hrho_le_one : rho <= 1 := by
    have hinv_nonneg : 0 <= Kgrid⁻¹ := (inv_pos.mpr hKgrid_pos).le
    have hcancel : Kgrid⁻¹ * Kgrid = 1 := inv_mul_cancel₀ (ne_of_gt hKgrid_pos)
    dsimp [rho]
    nlinarith
  obtain ⟨centerPath, coordinate, signedStep, hpath, hmove, hstep⟩ :=
    exists_reluApproxPhaseShiftedCommonFinePathData
      hd hM orderC orderF horderStep phase
  let coordinateB : Fin T -> Nat -> Fin d := fun _ => coordinate
  let signedStepB : Fin T -> Nat -> Real := fun _ => signedStep
  have hmoveB : forall b k,
      centerPath b (k + 1) - centerPath b k =
        reluApproxCoordinateStep (coordinateB b k) (signedStepB b k) := by
    intro b k
    simpa [coordinateB, signedStepB] using hmove b k
  have hstepB : forall b k, |signedStepB b k| <= rho := by
    intro b k
    simpa [signedStepB] using hstep k
  obtain ⟨correction, digit, _code, hcodeSpec, hcorrection⟩ :=
    exists_reluApproxCanonicalTaylorCorrectionCode
      hd hMpos hbeta_pos hC_nonneg hrho_pos f hf centerPath coordinateB
        signedStepB hmoveB hstepB
  let cDigit : Nat := Nat.ceil (Real.exp (d : Real))
  let base : Nat := 4 + 2 * cDigit
  let floorB : Nat := base - 1
  have hcDigit : cDigit = Nat.ceil (Real.exp (d : Real)) := rfl
  have hbase : 4 + 2 * cDigit <= base := le_rfl
  have hfloorB : floorB + 1 = base := by
    dsimp [floorB, base]
    omega
  have hbaseTwo : 2 <= base := by
    dsimp [base]
    omega
  have hdigitShift : forall b k a,
      (digit b k a : Int) = correction b k a + (cDigit + 2 : Int) := by
    intro b k a
    exact (hcodeSpec.2.1 b k a).1
  have hdigitLower : forall b k a, 1 <= digit b k a := by
    intro b k a
    exact (hcodeSpec.2.1 b k a).2.1
  have hdigitUpper : forall b k a, digit b k a <= 2 * cDigit + 3 := by
    intro b k a
    exact (hcodeSpec.2.1 b k a).2.2
  obtain ⟨Rfloor, hRfloor_pos, hRfloorSep⟩ :=
    exists_reluApproxDecoderScale_for_finiteTail base T hbaseTwo
  let tail0 : Fin T -> TaylorMultiindex r d -> Real := fun b a =>
    reluApproxFiniteBaseTail (base : Real)
      (reluApproxSentinelDigit (digit b) a) 0 (T + 1)
  have hfloorDigit : forall b k a,
      truncatedFloorReLUFunction Rfloor floorB
          ((base : Real) *
            reluApproxTaylorTailRecursion (base : Real) (digit b)
              (tail0 b) k.val a) = (digit b k a : Real) := by
    intro b k a
    exact reluApproxTaylorTailRecursion_floor_exact
      (d : Real) cDigit hcDigit base hbase floorB hfloorB Rfloor
        hRfloor_pos hRfloorSep (digit b) (hdigitLower b) (hdigitUpper b) k a
  let stepFin : Fin T -> Fin d -> Real := fun k =>
    reluApproxCoordinateStep (coordinate k.val) (signedStep k.val)
  let scaleCoeff : TaylorMultiindex r d -> Real :=
    reluApproxTaylorResidualScale beta C rho
  let trans : Fin T -> TaylorMultiindex r d -> TaylorMultiindex r d -> Real :=
    fun k => reluApproxTaylorPathTransport coordinate signedStep k.val
  let coefficient0 : Fin T -> TaylorMultiindex r d -> Real := fun b =>
    reluApproxCanonicalTaylorState beta C rho f (centerPath b)
      coordinate signedStep 0
  let coefficientState : Fin T -> Nat -> TaylorMultiindex r d -> Real := fun b =>
    reluApproxTaylorCoefficientRecursion scaleCoeff trans (correction b)
      (coefficient0 b)
  have hcenterState : forall b n, n <= T ->
      reluApproxTaylorCenterRecursion stepFin (centerPath b 0) n =
        centerPath b n := by
    intro b n hn
    exact reluApproxTaylorCenterRecursion_eq_path stepFin (centerPath b 0)
      (centerPath b) rfl (fun k hk => by simpa [stepFin] using hmove b k) n hn
  have hcoefficientState : forall b n, n <= T ->
      coefficientState b n =
        reluApproxCorrectedAffineRecursion scaleCoeff
          (reluApproxExactTaylorState f (centerPath b))
          (reluApproxTaylorPathTransport coordinate signedStep) n := by
    intro b n hn
    exact reluApproxTaylorCoefficientRecursion_eq_canonical scaleCoeff
      (reluApproxExactTaylorState f (centerPath b))
      (reluApproxTaylorPathTransport coordinate signedStep) (correction b)
      (coefficient0 b) rfl (fun k a => by
        simpa [coordinateB, signedStepB, scaleCoeff] using hcorrection b k a) n hn
  have hcoefficientTracks : forall b n, n <= T -> forall a,
      |coefficientState b n a -
        reluApproxExactTaylorState f (centerPath b) n a| < scaleCoeff a := by
    intro b n hn a
    rw [hcoefficientState b n hn]
    exact reluApproxCorrectedAffineRecursion_tracks_target scaleCoeff
      (reluApproxTaylorResidualScale_pos hbeta_pos hC_nonneg hrho_pos)
      (reluApproxExactTaylorState f (centerPath b))
      (reluApproxTaylorPathTransport coordinate signedStep) n hn a
  let payload : Fin T -> ReLUApproxFineAccumulator d r -> Real := fun b =>
    Sum.elim
      (reluApproxTaylorPayloadState (centerPath b 0) (coefficient0 b) (tail0 b))
      (reluApproxSelectedTaylorState (fun _ => 0) (fun _ => 0))
  let payloadMass : Real :=
    Finset.univ.sum fun b : Fin T =>
      Finset.univ.sum fun p : ReLUApproxFineAccumulator d r => |payload b p|
  let coefficientMass : Real :=
    Finset.univ.sum fun b : Fin T =>
      Finset.univ.sum fun k : Fin T =>
        Finset.univ.sum fun a : TaylorMultiindex r d => |coefficientState b k.val a|
  let rate : Real := shallowReLUResolutionRate M r beta
  have hrate_pos : 0 < rate := by
    dsimp [rate, shallowReLUResolutionRate]
    exact Real.rpow_pos_of_pos (by exact_mod_cast hMpos) _
  let Rstate : Real := 2 + payloadMass + coefficientMass
  have hpayloadMass : 0 <= payloadMass := by
    dsimp [payloadMass]
    positivity
  have hcoefficientMass : 0 <= coefficientMass := by
    dsimp [coefficientMass]
    positivity
  have hRstate : 2 <= Rstate := by
    dsimp [Rstate]
    linarith
  let R : Real := max Rstate (2 * Kgrid / rate)
  have hR : 2 <= R := le_trans hRstate (le_max_left _ _)
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hmargin : Kgrid * (R / 2)⁻¹ <= rate := by
    have hlarge : 2 * Kgrid / rate <= R := le_max_right _ _
    have hscaled : 2 * Kgrid <= rate * R :=
      by simpa [mul_comm] using (div_le_iff₀ hrate_pos).mp hlarge
    have hhalf : Kgrid * (R / 2)⁻¹ = (2 * Kgrid) / R := by
      field_simp [ne_of_gt hRpos]
    rw [hhalf]
    exact (div_le_iff₀ hRpos).2 (by nlinarith)
  have hpayloadBound : forall b p, |payload b p| <= R := by
    intro b p
    have hp : |payload b p| <=
        Finset.univ.sum fun p' : ReLUApproxFineAccumulator d r =>
          |payload b p'| :=
      Finset.single_le_sum (fun i _ => abs_nonneg (payload b i)) (Finset.mem_univ p)
    have hb : (Finset.univ.sum fun p' : ReLUApproxFineAccumulator d r =>
          |payload b p'|) <= payloadMass := by
      simpa [payloadMass] using
        (Finset.single_le_sum
          (s := (Finset.univ : Finset (Fin T)))
          (f := fun b' : Fin T =>
            Finset.univ.sum fun p' : ReLUApproxFineAccumulator d r =>
              |payload b' p'|)
          (fun b' _ => Finset.sum_nonneg fun p' _ => abs_nonneg (payload b' p'))
          (Finset.mem_univ b))
    exact le_trans (le_trans hp hb)
      (le_trans (by dsimp [Rstate]; linarith [hcoefficientMass]) (le_max_left _ _))
  have hcoefficientBound : forall (b k : Fin T) (a : TaylorMultiindex r d),
      |coefficientState b k.val a| <= R := by
    intro b k a
    have ha : |coefficientState b k.val a| <=
        Finset.univ.sum fun a' : TaylorMultiindex r d =>
          |coefficientState b k.val a'| :=
      Finset.single_le_sum (fun i _ => abs_nonneg (coefficientState b k.val i))
        (Finset.mem_univ a)
    have hk : (Finset.univ.sum fun a' : TaylorMultiindex r d =>
          |coefficientState b k.val a'|) <=
        Finset.univ.sum fun k' : Fin T =>
          Finset.univ.sum fun a' : TaylorMultiindex r d =>
            |coefficientState b k'.val a'| :=
      Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin T)))
        (f := fun k' : Fin T => Finset.univ.sum fun a' : TaylorMultiindex r d =>
          |coefficientState b k'.val a'|)
        (fun k' _ => Finset.sum_nonneg fun a' _ =>
          abs_nonneg (coefficientState b k'.val a'))
        (Finset.mem_univ k)
    have hb : (Finset.univ.sum fun k' : Fin T =>
          Finset.univ.sum fun a' : TaylorMultiindex r d =>
            |coefficientState b k'.val a'|) <= coefficientMass := by
      simpa [coefficientMass] using
        (Finset.single_le_sum
          (s := (Finset.univ : Finset (Fin T)))
          (f := fun b' : Fin T => Finset.univ.sum fun k' : Fin T =>
            Finset.univ.sum fun a' : TaylorMultiindex r d =>
              |coefficientState b' k'.val a'|)
          (fun b' _ => Finset.sum_nonneg fun k' _ =>
            Finset.sum_nonneg fun a' _ => abs_nonneg (coefficientState b' k'.val a'))
          (Finset.mem_univ b))
    exact le_trans (le_trans (le_trans ha hk) hb)
      (le_trans (by dsimp [Rstate]; linarith [hpayloadMass]) (le_max_left _ _))
  have hcenterBound : forall (b k : Fin T) (q : Fin d),
      |reluApproxTaylorCenterRecursion stepFin (centerPath b 0) k.val q| <= R := by
    intro b k q
    rw [hcenterState b k.val (Nat.le_of_lt k.isLt)]
    have hp := congrFun (hpath b k.val k.isLt) q
    rw [hp]
    exact le_trans
      (abs_twoScaleShiftedCenter_le_two hM orderC orderF
        phase b k q) hR
  let Rin : Real := reluApproxPhaseShiftedPolynomialInputRadius A C
  have hRin : 0 < Rin := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hRinOne : 1 <= Rin := le_max_left _ _
  let Rt : Real :=
    (Fintype.card (TaylorMultiindex r d) : Real) * Rin ^ (r + 1)
  have hRt : 0 <= Rt := by
    dsimp [Rt]
    positivity
  let Kpoly : Real :=
    reluApproxPhaseShiftedPolynomialErrorConstant d r A C
  have hKpoly : 0 <= Kpoly := by
    exact reluApproxPhaseShiftedPolynomialErrorConstant_nonneg d r A C
  have hKpolyBound : forall e : Real, 0 <= e -> e <= 8 ->
      finiteCenteredMonomialPolynomialFixedWidthApproxError e Rin 1
          (Finset.univ : Finset (TaylorMultiindex r d)) (fun _ => (1 : Real))
          (fun a => reluApproxTaylorEvaluationDegree a) <= Kpoly * e := by
    intro e he he8
    exact reluApproxPhaseShiftedPolynomialErrorConstant_bound d r A C e he he8
  obtain ⟨Neval, hNevalDepth, hNevalWidth, hNevalError⟩ :=
    exists_fullyConnectedReLUNet_weightedTaylorInput_fixed_width_rate_uniformResource
      hd hM hbeta_pos hbeta_le_one hRin hRt hKpoly hKpolyBound
      (fun _ : Fin d => Kgrid) (fun _ => hKgrid_pos.le)
  let Ktent : Real := tentProductRateConstant d
  let Rprod : Real := 1 + Rt + 8 * Kpoly + Ktent
  let Kraw : Real := reluApproxPhaseShiftedRawRateConstant d r A C
  have hKraw : 0 <= Kraw := by
    have hKt : 0 <= Ktent := tentProductRateConstant_nonneg d
    dsimp [Kraw, reluApproxPhaseShiftedRawRateConstant, Rprod, Rt, Rin]
    positivity
  let P := reluApproxCoarseFineProgram (B := floorB)
    R R Rfloor Kgrid⁻¹ (base : Real)
    (reluApproxPhaseShiftedCoarseLower M orderC phase)
    (reluApproxPhaseShiftedCoarseUpper M orderC phase)
    payload stepFin (cDigit + 2) scaleCoeff trans
  let Q := P.appendNetwork Neval
    (reluApproxFineSelectedUnitMassIndex d r)
    (reluApproxNormalizedTaylorEvaluationReadMatrix d r Neval.width)
    (fun _ => 0)
  let Draw : Nat := 2 * Q.stepCount + 1
  let Wraw : Nat := (Q.stateSize + Q.stateSize) + Q.featureSize
  obtain ⟨Nraw, hNrawDepth, hNrawWidth, _hNrawParam, hNrawRealize⟩ :=
    exists_reluApproxCoarseFineNormalizedEvaluatorNet_exactDepth
      R R Rfloor Kgrid⁻¹ (base : Real)
      (reluApproxPhaseShiftedCoarseLower M orderC phase)
      (reluApproxPhaseShiftedCoarseUpper M orderC phase)
      payload stepFin (cDigit + 2) scaleCoeff trans Neval
      (reluApproxFineSelectedUnitMassIndex d r)
      (D := Draw) (W := Wraw) le_rfl le_rfl
  have hRawDepth :
      Nraw.depth <= reluApproxPhaseShiftedRawDepthFactor d r * M ^ d := by
    rw [hNrawDepth]
    have hEvalSteps : ((Neval.depth - 1) + 1) + 1 <=
        (weightedTaylorDepthFactor d r + 2) * T := by
      calc
        ((Neval.depth - 1) + 1) + 1 <= Neval.depth + 2 := by omega
        _ <= weightedTaylorDepthFactor d r * T + 2 := by
          exact Nat.add_le_add_right hNevalDepth 2
        _ <= weightedTaylorDepthFactor d r * T + 2 * T := by
          exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 hTone) _
        _ = (weightedTaylorDepthFactor d r + 2) * T := by ring
    have hInside : Q.stepCount <=
        (5 + weightedTaylorDepthFactor d r + 2) * T := by
      dsimp [Q, P, ReLUApproxMacroProgram.appendNetwork,
        reluApproxCoarseFineProgram, ReLUApproxCoarseFineStepCount]
      calc
        T * 2 + T * 3 + ((Neval.depth - 1 + 1) + 1) <=
            T * 2 + T * 3 +
              (weightedTaylorDepthFactor d r + 2) * T := by
                gcongr
        _ = (5 + weightedTaylorDepthFactor d r + 2) * T := by ring
    have hscaled := Nat.mul_le_mul_left 2 hInside
    have hadd := Nat.add_le_add hscaled hTone
    simpa [Draw, reluApproxPhaseShiftedRawDepthFactor, Nat.mul_assoc,
      Nat.add_mul] using hadd
  have hRawWidth :
      Nraw.width <= reluApproxPhaseShiftedRawWidthBound d r := by
    apply le_trans hNrawWidth
    dsimp [Wraw, Q, P, ReLUApproxMacroProgram.appendNetwork,
      reluApproxCoarseFineProgram, reluApproxPhaseShiftedRawWidthBound,
      reluApproxMacroWithPersistentSuffixFeatureSize,
      reluApproxPersistentWorkFeatureSize, floorB, base, cDigit]
    omega
  refine ⟨R, Nraw, hR, hRawDepth, hRawWidth, ?_, ?_⟩
  · simpa [Kgrid, rate] using hmargin
  · intro x activeCoarse activeFine hactiveCoarse hinactiveCoarse
      hactiveFine hinactiveFine
    have hreal := hNrawRealize x activeCoarse hRpos hpayloadBound
      hactiveCoarse hinactiveCoarse (digit activeCoarse) (correction activeCoarse)
      (centerPath activeCoarse 0) (coefficient0 activeCoarse) (tail0 activeCoarse)
      (fun _ => 0) (fun _ => 0) (hdigitShift activeCoarse) rfl
      (hfloorDigit activeCoarse)
    rw [hreal]
    have hactiveFine' : forall q,
        reluApproxTaylorCenterRecursion stepFin (centerPath activeCoarse 0)
              activeFine.val q - Kgrid⁻¹ + R⁻¹ <= x q /\
          x q <=
            reluApproxTaylorCenterRecursion stepFin (centerPath activeCoarse 0)
              activeFine.val q + Kgrid⁻¹ - R⁻¹ := by
      intro q
      rw [hcenterState activeCoarse activeFine.val (Nat.le_of_lt activeFine.isLt)]
      rw [hpath activeCoarse activeFine.val activeFine.isLt]
      simpa [reluApproxPhaseShiftedFineLower,
        reluApproxPhaseShiftedFineUpper, Kgrid] using hactiveFine q
    have hinactiveFine' : forall k : Fin T, k ≠ activeFine -> exists q,
        x q <= reluApproxTaylorCenterRecursion stepFin (centerPath activeCoarse 0)
              k.val q - Kgrid⁻¹ \/
          reluApproxTaylorCenterRecursion stepFin (centerPath activeCoarse 0)
              k.val q + Kgrid⁻¹ <= x q := by
      intro k hk
      obtain ⟨q, hq⟩ := hinactiveFine k hk
      refine ⟨q, ?_⟩
      rw [hcenterState activeCoarse k.val (Nat.le_of_lt k.isLt)]
      rw [hpath activeCoarse k.val k.isLt]
      simpa [reluApproxPhaseShiftedFineLower,
        reluApproxPhaseShiftedFineUpper, Kgrid] using hq
    have hcenterSelected := reluApproxFineSelectedRecursions_eq_of_unique
      (radius := Kgrid⁻¹) hRpos x
      (reluApproxTaylorCenterRecursion stepFin (centerPath activeCoarse 0))
      (coefficientState activeCoarse) activeFine
      (hcenterBound activeCoarse) (hcoefficientBound activeCoarse)
      hactiveFine' hinactiveFine'
    rw [hcenterSelected.1, hcenterSelected.2]
    rw [hcenterState activeCoarse activeFine.val (Nat.le_of_lt activeFine.isLt)]
    have hpathActive : centerPath activeCoarse activeFine.val =
        twoScaleShiftedCenter M orderC orderF phase
          activeCoarse activeFine := by
      simpa using hpath activeCoarse activeFine.val activeFine.isLt
    rw [hpathActive]
    let center := twoScaleShiftedCenter M orderC orderF phase
      activeCoarse activeFine
    let decoded := coefficientState activeCoarse activeFine.val
    let exact : TaylorMultiindex r d -> Real :=
      reluApproxExactTaylorState (r := r) f (centerPath activeCoarse) activeFine.val
    have hdecoded : forall a, |decoded a - exact a| <= scaleCoeff a := by
      intro a
      exact le_of_lt (hcoefficientTracks activeCoarse activeFine.val
        (Nat.le_of_lt activeFine.isLt) a)
    have hdir : forall a : TaylorMultiindex r d,
        reluApproxTaylorDirections a =
          fun k : Fin a.1.val => fun q : Fin d =>
            if q = a.2 k then 1 else 0 := by
      intro a
      funext k q
      by_cases hq : q = a.2 k
      · subst q
        simp [reluApproxTaylorDirections]
      · have hq' : a.2 k ≠ q := Ne.symm hq
        simp [reluApproxTaylorDirections, hq, hq']
    have hexactCoeff : forall a,
        |((Nat.factorial a.1.val : Real)⁻¹) * exact a| <= A := by
      intro a
      dsimp [exact, reluApproxExactTaylorState,
        reluApproxRawTaylorCoefficient]
      rw [hpathActive, hdir a]
      exact hAcoeff center a
    have hdecodedCoeff : forall a,
        |((Nat.factorial a.1.val : Real)⁻¹) * decoded a| <= A + C + 1 := by
      intro a
      exact abs_normalized_taylor_coefficient_le_of_residual_profile
        hbeta_pos.le hC_nonneg hrho_nonneg hrho_le_one
          exact decoded hexactCoeff hdecoded a
    have hdelta : forall q, |x q - center q| <= Kgrid⁻¹ := by
      intro q
      dsimp [center]
      unfold reluApproxPhaseShiftedFineLower at hactiveFine
      unfold reluApproxPhaseShiftedFineUpper at hactiveFine
      have hri : 0 <= R⁻¹ := (inv_pos.mpr hRpos).le
      rw [abs_le]
      constructor <;> linarith [(hactiveFine q).1, (hactiveFine q).2]
    have hinput : forall i,
        |reluApproxNormalizedTaylorEvaluationInputValue x center decoded i| <= Rin := by
      intro i
      generalize hz : (reluApproxTaylorEvaluationInputEquivFin d r).symm i = z
      have hi : reluApproxTaylorEvaluationInputEquivFin d r z = i := by
        rw [← hz]
        exact (reluApproxTaylorEvaluationInputEquivFin d r).apply_symm_apply i
      rcases z with q | a
      · subst i
        simp only [reluApproxNormalizedTaylorEvaluationInputValue,
          reluApproxTaylorEvaluationInputValue_delta]
        exact le_trans (hdelta q) (le_trans hKgridInv_le_one hRinOne)
      · subst i
        simp only [reluApproxNormalizedTaylorEvaluationInputValue,
          reluApproxTaylorEvaluationInputValue_coefficient]
        exact le_trans (hdecodedCoeff a) (le_max_right _ _)
    have htargetBound :
        |Finset.univ.sum fun a : TaylorMultiindex r d =>
          Finset.univ.prod fun q : Fin (reluApproxTaylorEvaluationDegree a) =>
            reluApproxNormalizedTaylorEvaluationInputValue x center decoded
              (reluApproxTaylorEvaluationCoord a q)| <= Rt := by
      exact abs_reluApproxTaylorEvaluation_sum_le hRinOne _ hinput
    have heval := hNevalError
      (reluApproxNormalizedTaylorEvaluationInputValue x center decoded)
      hinput htargetBound
    have htentIdentity :
        axisAlignedBoxTentWeight (fun _ : Fin d => 0) (fun _ : Fin d => Kgrid)
            (fun q => reluApproxNormalizedTaylorEvaluationInputValue
              x center decoded
                (reluApproxTaylorEvaluationInputEquivFin d r (Sum.inl q))) =
          axisAlignedBoxTentWeight center (fun _ : Fin d => Kgrid) x := by
      simpa [reluApproxNormalizedTaylorEvaluationInputValue,
        reluApproxTaylorEvaluationInputValue] using
        axisAlignedBoxTentWeight_zero_center_difference
          x center (fun _ : Fin d => Kgrid)
    have hsumIdentity :
        (Finset.univ.sum fun a : TaylorMultiindex r d =>
          Finset.univ.prod fun q : Fin (reluApproxTaylorEvaluationDegree a) =>
            reluApproxNormalizedTaylorEvaluationInputValue x center decoded
              (reluApproxTaylorEvaluationCoord a q)) =
          finiteLinearCombination
            (Finset.univ : Finset (TaylorMultiindex r d))
            (fun a => ((Nat.factorial a.1.val : Real)⁻¹) * decoded a)
            (fun a y => Finset.univ.prod fun k : Fin a.1.val =>
              y (a.2 k) - center (a.2 k)) x := by
      unfold finiteLinearCombination
      apply Finset.sum_congr rfl
      intro a _ha
      simpa [reluApproxNormalizedTaylorEvaluationInputValue] using
        reluApproxTaylorEvaluation_monomial_identity x center
          (fun a : TaylorMultiindex r d =>
            ((Nat.factorial a.1.val : Real)⁻¹) * decoded a) a
    have hevalTarget :
        |Neval.realize
              (reluApproxNormalizedTaylorEvaluationInputValue x center decoded) -
            axisAlignedBoxTentWeight center (fun _ : Fin d => Kgrid) x *
              finiteLinearCombination
                (Finset.univ : Finset (TaylorMultiindex r d))
                (fun a => ((Nat.factorial a.1.val : Real)⁻¹) * decoded a)
                (fun a y => Finset.univ.prod fun k : Fin a.1.val =>
                  y (a.2 k) - center (a.2 k)) x| <= Kraw * rate := by
      rw [htentIdentity, hsumIdentity] at heval
      simpa [Kraw, Rprod, Ktent, rate] using heval
    have hpoly := normalized_centered_taylor_polynomial_error_of_residual_profile
      hC_nonneg hrho_pos center x exact decoded hdecoded (fun q =>
        le_trans (hdelta q) (by dsimp [rho]; linarith [hKgridInv_le_one]))
    have htentBounds := axisAlignedBoxTentWeight_bounds_and_support
      center (fun _ : Fin d => Kgrid) x (fun _ => hKgrid_pos.le)
    have hweightedPoly :
        |axisAlignedBoxTentWeight center (fun _ : Fin d => Kgrid) x *
            finiteLinearCombination
              (Finset.univ : Finset (TaylorMultiindex r d))
              (fun a => ((Nat.factorial a.1.val : Real)⁻¹) * decoded a)
              (fun a y => Finset.univ.prod fun k : Fin a.1.val =>
                y (a.2 k) - center (a.2 k)) x -
          axisAlignedBoxTentWeight center (fun _ : Fin d => Kgrid) x *
            finiteLinearCombination
              (Finset.univ : Finset (TaylorMultiindex r d))
              (fun a => ((Nat.factorial a.1.val : Real)⁻¹) * exact a)
              (fun a y => Finset.univ.prod fun k : Fin a.1.val =>
                y (a.2 k) - center (a.2 k)) x| <=
          (Fintype.card (TaylorMultiindex r d) : Real) *
            ((C + 1) * Real.rpow rho ((r : Real) + beta)) := by
      rw [← mul_sub, abs_mul, abs_of_nonneg htentBounds.1]
      have hboundNonneg : 0 <=
          (Fintype.card (TaylorMultiindex r d) : Real) *
            ((C + 1) * Real.rpow rho ((r : Real) + beta)) := by
        exact mul_nonneg (by positivity)
          (mul_nonneg (by linarith) (Real.rpow_nonneg hrho_nonneg _))
      calc
        axisAlignedBoxTentWeight center (fun _ : Fin d => Kgrid) x *
            |finiteLinearCombination
                (Finset.univ : Finset (TaylorMultiindex r d))
                (fun a => ((Nat.factorial a.1.val : Real)⁻¹) * decoded a)
                (fun a y => Finset.univ.prod fun k : Fin a.1.val =>
                  y (a.2 k) - center (a.2 k)) x -
              finiteLinearCombination
                (Finset.univ : Finset (TaylorMultiindex r d))
                (fun a => ((Nat.factorial a.1.val : Real)⁻¹) * exact a)
                (fun a y => Finset.univ.prod fun k : Fin a.1.val =>
                  y (a.2 k) - center (a.2 k)) x| <=
            axisAlignedBoxTentWeight center (fun _ : Fin d => Kgrid) x *
              ((Fintype.card (TaylorMultiindex r d) : Real) *
                ((C + 1) * Real.rpow rho ((r : Real) + beta))) :=
          mul_le_mul_of_nonneg_left hpoly htentBounds.1
        _ <= 1 * ((Fintype.card (TaylorMultiindex r d) : Real) *
              ((C + 1) * Real.rpow rho ((r : Real) + beta))) :=
          mul_le_mul_of_nonneg_right htentBounds.2.1 hboundNonneg
        _ = _ := one_mul _
    have hscale :
        twoScaleShiftedScale M phase activeCoarse activeFine =
          fun _ : Fin d => Kgrid := by
      funext q
      rfl
    have hexactPolynomial :
        finiteLinearCombination
            (Finset.univ : Finset (TaylorMultiindex r d))
            (fun a => ((Nat.factorial a.1.val : Real)⁻¹) * exact a)
            (fun a y => Finset.univ.prod fun k : Fin a.1.val =>
              y (a.2 k) - center (a.2 k)) x =
          finiteLinearCombination
            (Finset.univ : Finset (TaylorMultiindex r d))
            (fun a => ((Nat.factorial a.1.val : Real)⁻¹) *
              (iteratedFDeriv Real a.1.val f center)
                (fun k : Fin a.1.val => fun q : Fin d =>
                  if q = a.2 k then 1 else 0))
            (fun a y => Finset.univ.prod fun k : Fin a.1.val =>
              y (a.2 k) - center (a.2 k)) x := by
      apply Finset.sum_congr rfl
      intro a _ha
      congr 1
      dsimp [exact, reluApproxExactTaylorState,
        reluApproxRawTaylorCoefficient]
      rw [hpathActive, hdir a]
    rw [hscale, ← hexactPolynomial]
    calc
      |Neval.realize
            (reluApproxNormalizedTaylorEvaluationInputValue x center decoded) -
          axisAlignedBoxTentWeight center (fun _ : Fin d => Kgrid) x *
            finiteLinearCombination
              (Finset.univ : Finset (TaylorMultiindex r d))
              (fun a => ((Nat.factorial a.1.val : Real)⁻¹) * exact a)
              (fun a y => Finset.univ.prod fun k : Fin a.1.val =>
                y (a.2 k) - center (a.2 k)) x| <=
          |Neval.realize
              (reluApproxNormalizedTaylorEvaluationInputValue x center decoded) -
            axisAlignedBoxTentWeight center (fun _ : Fin d => Kgrid) x *
              finiteLinearCombination
                (Finset.univ : Finset (TaylorMultiindex r d))
                (fun a => ((Nat.factorial a.1.val : Real)⁻¹) * decoded a)
                (fun a y => Finset.univ.prod fun k : Fin a.1.val =>
                  y (a.2 k) - center (a.2 k)) x| +
          |axisAlignedBoxTentWeight center (fun _ : Fin d => Kgrid) x *
              finiteLinearCombination
                (Finset.univ : Finset (TaylorMultiindex r d))
                (fun a => ((Nat.factorial a.1.val : Real)⁻¹) * decoded a)
                (fun a y => Finset.univ.prod fun k : Fin a.1.val =>
                  y (a.2 k) - center (a.2 k)) x -
            axisAlignedBoxTentWeight center (fun _ : Fin d => Kgrid) x *
              finiteLinearCombination
                (Finset.univ : Finset (TaylorMultiindex r d))
                (fun a => ((Nat.factorial a.1.val : Real)⁻¹) * exact a)
                (fun a y => Finset.univ.prod fun k : Fin a.1.val =>
                  y (a.2 k) - center (a.2 k)) x| := abs_sub_le _ _ _
      _ <= Kraw * rate +
          (Fintype.card (TaylorMultiindex r d) : Real) *
            ((C + 1) * Real.rpow rho ((r : Real) + beta)) :=
        add_le_add hevalTarget hweightedPoly
      _ = Kraw * shallowReLUResolutionRate M r beta +
          (Fintype.card (TaylorMultiindex r d) : Real) *
            ((C + 1) * Real.rpow
              (2 * ((M ^ 2 - 1 : Nat) : Real)⁻¹)
              ((r : Real) + beta)) := by rfl

/-- The inverse shifted-grid scale has the same `M^(-2s)` order as the
shallow ReLU rate.  The factor four is a uniform consequence of `M >= 2`. -/
theorem two_inv_grid_rpow_le_shallow_rate
    {M r : Nat} {beta : Real} (hM : 2 <= M) (hbeta : 0 <= beta) :
    Real.rpow (2 * ((M ^ 2 - 1 : Nat) : Real)⁻¹) ((r : Real) + beta) <=
      Real.rpow 4 ((r : Real) + beta) * shallowReLUResolutionRate M r beta := by
  let alpha : Real := (r : Real) + beta
  have halpha : 0 <= alpha := by
    dsimp [alpha]
    positivity
  have hMreal : (2 : Real) <= (M : Real) := by exact_mod_cast hM
  have hMpos : (0 : Real) < (M : Real) := lt_of_lt_of_le (by norm_num) hMreal
  have hMnonneg : (0 : Real) <= (M : Real) := hMpos.le
  have hM2ge1 : (1 : Nat) <= M ^ 2 := by
    have hMposNat : 0 < M := by omega
    exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (Nat.ne_of_gt hMposNat))
  have hgridEq : ((M ^ 2 - 1 : Nat) : Real) = (M : Real) ^ 2 - 1 := by
    rw [Nat.cast_sub hM2ge1, Nat.cast_pow]
    norm_num
  have hsqGe4 : (4 : Real) <= (M : Real) ^ 2 := by nlinarith
  have hgridPos : (0 : Real) < ((M ^ 2 - 1 : Nat) : Real) := by
    rw [hgridEq]
    nlinarith
  have hinvLe : ((M ^ 2 - 1 : Nat) : Real)⁻¹ <=
      (2 : Real) * ((M : Real) ^ 2)⁻¹ := by
    rw [hgridEq]
    have hhalfPos : (0 : Real) < (M : Real) ^ 2 / 2 := by nlinarith
    have hhalfLe : (M : Real) ^ 2 / 2 <= (M : Real) ^ 2 - 1 := by
      nlinarith
    have hinv := one_div_le_one_div_of_le hhalfPos hhalfLe
    calc
      ((M : Real) ^ 2 - 1)⁻¹ = 1 / ((M : Real) ^ 2 - 1) := by rw [one_div]
      _ <= 1 / ((M : Real) ^ 2 / 2) := hinv
      _ = (2 : Real) * ((M : Real) ^ 2)⁻¹ := by
        rw [one_div, inv_div, div_eq_mul_inv]
  have hrhoPos : (0 : Real) < 2 * ((M ^ 2 - 1 : Nat) : Real)⁻¹ := by
    positivity
  have hrhoLe : 2 * ((M ^ 2 - 1 : Nat) : Real)⁻¹ <=
      (4 : Real) * ((M : Real) ^ 2)⁻¹ := by nlinarith
  have hM2invNonneg : (0 : Real) <= ((M : Real) ^ 2)⁻¹ := by positivity
  have hpowId : (((M : Real) ^ 2)⁻¹) ^ alpha =
      (M : Real) ^ (-(2 * alpha)) := by
    rw [← Real.rpow_neg_one ((M : Real) ^ 2)]
    rw [← Real.rpow_mul (sq_nonneg (M : Real)) (-1 : Real) alpha]
    rw [← Real.rpow_natCast (M : Real) 2]
    rw [← Real.rpow_mul hMnonneg ((2 : Nat) : Real) ((-1 : Real) * alpha)]
    congr 1
    ring
  calc
    Real.rpow (2 * ((M ^ 2 - 1 : Nat) : Real)⁻¹) ((r : Real) + beta) <=
        (4 * ((M : Real) ^ 2)⁻¹) ^ alpha := by
      exact Real.rpow_le_rpow hrhoPos.le hrhoLe halpha
    _ = (4 : Real) ^ alpha * (((M : Real) ^ 2)⁻¹) ^ alpha := by
      rw [Real.mul_rpow (by norm_num : (0 : Real) <= 4) hM2invNonneg]
    _ = (4 : Real) ^ alpha * (M : Real) ^ (-(2 * alpha)) := by
      rw [hpowId]
    _ = Real.rpow 4 ((r : Real) + beta) * shallowReLUResolutionRate M r beta := by
      rfl

/-- Uniform width of the hierarchical fine-cell boundary checker. -/
private noncomputable def reluApproxPhaseShiftedFineWidthBound (d r : Nat) : Nat :=
  let s := reluApproxVectorBoxScanStateSize d
    (Fintype.card (ReLUApproxFineAccumulator d r))
  let hscan := reluApproxVectorBoxScanFeatureSize d
    (Fintype.card (ReLUApproxFineAccumulator d r))
  let h := hscan + (hscan + fineTaylorFeatureSize d r 0)
  (s + s) + h

/-- Uniform depth factor for one globally clipped shifted two-scale phase. -/
abbrev twoScalePhaseDepthFactor (d r : Nat) : Nat :=
  2 * (reluApproxPhaseShiftedRawDepthFactor d r + 27) + 1

/-- Uniform width bound for one globally clipped shifted two-scale phase. -/
noncomputable def twoScalePhaseWidthBound (d r : Nat) : Nat :=
  42 *
    (d + 3 + reluApproxPhaseShiftedRawWidthBound d r +
      (2 * d + ((d + d) + 2) + 3) +
      reluApproxPhaseShiftedFineWidthBound d r + 5)

/-- Canonical approximation constant after clipping one shifted phase. -/
noncomputable def twoScalePhaseRateConstant
    (d r : Nat) (beta C A : Real) : Real :=
  let Kraw := reluApproxPhaseShiftedRawRateConstant d r A C
  let Bval := (Fintype.card (TaylorMultiindex r d) : Real) *
    (max 3 A) ^ (r + 1)
  2 * Kraw +
    2 * (Fintype.card (TaylorMultiindex r d) : Real) * (C + 1) *
      Real.rpow 4 ((r : Real) + beta) + 2 * Bval

theorem twoScalePhaseRateConstant_nonneg
    (d r : Nat) {beta C A : Real} (hC : 0 <= C) (hA : 0 <= A) :
    0 <= twoScalePhaseRateConstant d r beta C A := by
  have hKraw := reluApproxPhaseShiftedRawRateConstant_nonneg d r hA hC
  have hfourpow : 0 <= Real.rpow 4 ((r : Real) + beta) :=
    Real.rpow_nonneg (by norm_num) _
  unfold twoScalePhaseRateConstant
  positivity

set_option maxHeartbeats 2000000 in
/-- One shifted phase admits a globally valid clipped network with the
shallow ReLU `M^(-2(r+beta))` approximation rate. -/
theorem exists_two_scale_phase_network_rate
    {d r M : Nat} {beta C B A : Real}
    (hd : 0 < d) (hM : 2 <= M)
    (hbeta_pos : 0 < beta) (hbeta_le_one : beta <= 1)
    (hC_nonneg : 0 <= C) (hA_nonneg : 0 <= A)
    (orderC orderF : Fin (M ^ d) ≃ (Fin d -> Fin M))
    (horderStep : forall (k : Nat) (hk : k + 1 < M ^ d),
      exists q : Fin d,
        Int.natAbs
          ((orderF ⟨k + 1, hk⟩ q).val -
            (orderF ⟨k, Nat.lt_of_succ_lt hk⟩ q).val) = 1 /\
        forall u : Fin d, u ≠ q ->
          orderF ⟨k + 1, hk⟩ u =
            orderF ⟨k, Nat.lt_of_succ_lt hk⟩ u)
    (phase : Fin d -> Fin 2)
    (f : (Fin d -> Real) -> Real) (hf : f ∈ holderSmoothBall r beta C B)
    (hAcoeff : forall y : Fin d -> Real, forall a : TaylorMultiindex r d,
      |((Nat.factorial a.1.val : Real)⁻¹) *
        (iteratedFDeriv Real a.1.val f y)
          (fun k : Fin a.1.val => fun q : Fin d =>
            if q = a.2 k then 1 else 0)| <= A) :
    exists N : FullyConnectedReLUNet d,
      0 < N.depth /\
      N.depth <= twoScalePhaseDepthFactor d r * M ^ d /\
      N.width <= twoScalePhaseWidthBound d r /\
      N.parameterCount <= fullyConnectedReLUParameterCount d N.depth N.width /\
      forall x : Fin d -> Real,
        (forall q, x q ∈ Set.Icc (0 : Real) 1) ->
        |N.realize x -
          (Finset.univ.sum fun b : Fin (M ^ d) =>
            Finset.univ.sum fun t : Fin (M ^ d) =>
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
          twoScalePhaseRateConstant d r beta C A *
            shallowReLUResolutionRate M r beta := by
  classical
  let value : (Fin (M ^ d) × Fin (M ^ d)) ->
      (Fin d -> Real) -> Real := fun p x =>
    finiteLinearCombination
      (Finset.univ : Finset (TaylorMultiindex r d))
      (fun a => ((Nat.factorial a.1.val : Real)⁻¹) *
        (iteratedFDeriv Real a.1.val f
          (twoScaleShiftedCenter M orderC orderF phase p.1 p.2))
            (fun k : Fin a.1.val => fun q : Fin d =>
              if q = a.2 k then 1 else 0))
      (fun a y => Finset.univ.prod fun k : Fin a.1.val =>
        y (a.2 k) -
          twoScaleShiftedCenter M orderC orderF phase p.1 p.2
            (a.2 k)) x
  let Rval : Real := max 3 A
  let Bval : Real :=
    (Fintype.card (TaylorMultiindex r d) : Real) * Rval ^ (r + 1)
  have hRvalOne : 1 <= Rval := by
    exact le_trans (by norm_num) (le_max_left _ _)
  have hBval : 0 <= Bval := by
    dsimp [Bval]
    positivity
  have hvalue : forall p x,
      (forall q, x q ∈ Set.Icc (0 : Real) 1) -> |value p x| <= Bval := by
    intro p x hx
    let center := twoScaleShiftedCenter M orderC orderF phase p.1 p.2
    let coefficient : TaylorMultiindex r d -> Real := fun a =>
      (iteratedFDeriv Real a.1.val f center)
        (fun k : Fin a.1.val => fun q : Fin d =>
          if q = a.2 k then 1 else 0)
    let y := reluApproxNormalizedTaylorEvaluationInputValue x center coefficient
    have hy : forall i, |y i| <= Rval := by
      intro i
      generalize hz : (reluApproxTaylorEvaluationInputEquivFin d r).symm i = z
      have hi : reluApproxTaylorEvaluationInputEquivFin d r z = i := by
        rw [← hz]
        exact (reluApproxTaylorEvaluationInputEquivFin d r).apply_symm_apply i
      rcases z with q | a
      · subst i
        simp only [y, reluApproxNormalizedTaylorEvaluationInputValue,
          reluApproxTaylorEvaluationInputValue_delta]
        have hxabs : |x q| <= 1 := by
          rw [abs_of_nonneg (Set.mem_Icc.mp (hx q)).1]
          exact (Set.mem_Icc.mp (hx q)).2
        exact le_trans (abs_sub _ _)
          (le_trans
            (add_le_add hxabs
              (abs_twoScaleShiftedCenter_le_two hM orderC orderF
                phase p.1 p.2 q))
            (by
              norm_num [Rval]))
      · subst i
        simp only [y, reluApproxNormalizedTaylorEvaluationInputValue,
          reluApproxTaylorEvaluationInputValue_coefficient]
        exact le_trans (hAcoeff center a) (le_max_right _ _)
    have hsum := abs_reluApproxTaylorEvaluation_sum_le hRvalOne y hy
    have hidentity :
        (Finset.univ.sum fun a : TaylorMultiindex r d =>
          Finset.univ.prod fun q : Fin (reluApproxTaylorEvaluationDegree a) =>
            y (reluApproxTaylorEvaluationCoord a q)) = value p x := by
      unfold value finiteLinearCombination
      apply Finset.sum_congr rfl
      intro a _ha
      simpa [y, center, coefficient,
        reluApproxNormalizedTaylorEvaluationInputValue] using
        reluApproxTaylorEvaluation_monomial_identity x center
          (fun a : TaylorMultiindex r d =>
            ((Nat.factorial a.1.val : Real)⁻¹) * coefficient a) a
    rw [hidentity] at hsum
    exact hsum
  obtain ⟨R, Nraw, hR, hRawDepth, hRawWidth,
      hmargin, hrawError⟩ :=
    exists_reluApproxPhaseShifted_weightedTaylorRawNet
      hd hM hbeta_pos hbeta_le_one hC_nonneg hA_nonneg orderC orderF
        horderStep phase f hf hAcoeff
  let Kraw : Real := reluApproxPhaseShiftedRawRateConstant d r A C
  have hKraw : 0 <= Kraw := by
    exact reluApproxPhaseShiftedRawRateConstant_nonneg d r hA_nonneg hC_nonneg
  obtain ⟨Bclip, hBclip, hrawBound⟩ :=
    fullyConnectedReLUNet_exists_abs_realize_bound_on_unitCube Nraw
  have hrate : 0 <= shallowReLUResolutionRate M r beta := by
    unfold shallowReLUResolutionRate
    exact (Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < M by omega)) _).le
  have hrho_nonneg :
      0 <= 2 * ((M ^ 2 - 1 : Nat) : Real)⁻¹ := by
    exact mul_nonneg (by norm_num) (inv_nonneg.mpr (by positivity))
  let eps : Real := Kraw * shallowReLUResolutionRate M r beta +
    (Fintype.card (TaylorMultiindex r d) : Real) *
      ((C + 1) * Real.rpow
        (2 * ((M ^ 2 - 1 : Nat) : Real)⁻¹) ((r : Real) + beta))
  have heps : 0 <= eps := by
    dsimp [eps]
    exact add_nonneg (mul_nonneg hKraw hrate)
      (mul_nonneg (by positivity)
        (mul_nonneg (by linarith) (Real.rpow_nonneg hrho_nonneg _)))
  let Dfine : Nat := 2 * ((M ^ d) * 2 + (M ^ d) * 3) + 1
  let Wfine : Nat :=
    let s := reluApproxVectorBoxScanStateSize d
      (Fintype.card (ReLUApproxFineAccumulator d r))
    let hscan := reluApproxVectorBoxScanFeatureSize d
      (Fintype.card (ReLUApproxFineAccumulator d r))
    let h := hscan + (hscan + fineTaylorFeatureSize d r 0)
    (s + s) + h
  obtain ⟨N, hNdepth, hNdepthBound, hNwidthBound, hNparam, hNerror⟩ :=
    exists_reluApproxPhaseShifted_twoMarginBoundaryClipNet
      hd hM orderC orderF horderStep phase hR hBval heps hBclip value hvalue
        Nraw hrawBound (by
          intro x hx activeCoarse activeFine hactiveCoarse hinactiveCoarse
            hactiveFine hinactiveFine
          simpa [eps, value] using
            hrawError x activeCoarse activeFine hactiveCoarse hinactiveCoarse
              hactiveFine hinactiveFine)
        (Dfine := Dfine) (Wfine := Wfine) le_rfl le_rfl
  let Kphase : Real :=
    twoScalePhaseRateConstant d r beta C A
  have hfourpow : 0 <= Real.rpow 4 ((r : Real) + beta) :=
    Real.rpow_nonneg (by norm_num) _
  have hKphase : 0 <= Kphase := by
    dsimp [Kphase, twoScalePhaseRateConstant, Bval, Rval, Kraw]
    exact add_nonneg
      (add_nonneg (mul_nonneg (by norm_num) hKraw)
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num) (by positivity)) (by linarith))
          hfourpow))
      (mul_nonneg (by norm_num) hBval)
  have hTpos : 0 < M ^ d := by
    positivity
  have hphaseDepth :
      N.depth <= twoScalePhaseDepthFactor d r * M ^ d := by
    let T : Nat := M ^ d
    have hTpos' : 0 < T := by simpa [T] using hTpos
    have hRawDepthT :
        Nraw.depth <= reluApproxPhaseShiftedRawDepthFactor d r * T := by
      simpa [T] using hRawDepth
    have hcoarse : (T + 1) * 3 <= 6 * T := by omega
    have hfine : Dfine <= 11 * T := by
      dsimp [Dfine, T]
      omega
    have hover : 10 <= 10 * T := by omega
    calc
      N.depth <= 2 * (Nraw.depth + (T + 1) * 3 + Dfine + 10) + 1 := by
        simpa [T] using hNdepthBound
      _ <= 2 *
          (reluApproxPhaseShiftedRawDepthFactor d r * T +
            6 * T + 11 * T + 10 * T) + 1 := by
        omega
      _ = 2 * (reluApproxPhaseShiftedRawDepthFactor d r + 27) * T + 1 := by
        ring
      _ <= 2 * (reluApproxPhaseShiftedRawDepthFactor d r + 27) * T + T := by
        omega
      _ = (2 * (reluApproxPhaseShiftedRawDepthFactor d r + 27) + 1) * T := by
        ring
      _ = twoScalePhaseDepthFactor d r * M ^ d := by
        rfl
  have hphaseWidth : N.width <= twoScalePhaseWidthBound d r := by
    apply le_trans hNwidthBound
    dsimp [Wfine, twoScalePhaseWidthBound,
      reluApproxPhaseShiftedFineWidthBound]
    omega
  refine ⟨N, hNdepth, hphaseDepth, hphaseWidth, hNparam, ?_⟩
  intro x hx
  have hrho := two_inv_grid_rpow_le_shallow_rate
    (r := r) hM hbeta_pos.le
  have hcard : 0 <= (Fintype.card (TaylorMultiindex r d) : Real) := by positivity
  have hC1 : 0 <= C + 1 := by linarith
  have hTaylor :
      (Fintype.card (TaylorMultiindex r d) : Real) *
          ((C + 1) * Real.rpow
            (2 * ((M ^ 2 - 1 : Nat) : Real)⁻¹) ((r : Real) + beta)) <=
        ((Fintype.card (TaylorMultiindex r d) : Real) * (C + 1) *
          Real.rpow 4 ((r : Real) + beta)) * shallowReLUResolutionRate M r beta := by
    calc
      (Fintype.card (TaylorMultiindex r d) : Real) *
          ((C + 1) * Real.rpow
            (2 * ((M ^ 2 - 1 : Nat) : Real)⁻¹) ((r : Real) + beta)) <=
          (Fintype.card (TaylorMultiindex r d) : Real) *
            ((C + 1) *
              (Real.rpow 4 ((r : Real) + beta) *
                shallowReLUResolutionRate M r beta)) := by
            gcongr
      _ = ((Fintype.card (TaylorMultiindex r d) : Real) * (C + 1) *
          Real.rpow 4 ((r : Real) + beta)) * shallowReLUResolutionRate M r beta := by
            ring
  have hboundary :
      Bval * (((M ^ 2 - 1 : Nat) : Real) * (R / 2)⁻¹) <=
        Bval * shallowReLUResolutionRate M r beta :=
    mul_le_mul_of_nonneg_left hmargin hBval
  have hphaseError := hNerror x hx
  have hepsRate : eps <=
      Kraw * shallowReLUResolutionRate M r beta +
        ((Fintype.card (TaylorMultiindex r d) : Real) * (C + 1) *
          Real.rpow 4 ((r : Real) + beta)) * shallowReLUResolutionRate M r beta := by
    dsimp [eps]
    exact add_le_add le_rfl hTaylor
  have hscaledEps := mul_le_mul_of_nonneg_left hepsRate (by norm_num : (0 : Real) <= 2)
  have hscaledBoundary :=
    mul_le_mul_of_nonneg_left hboundary (by norm_num : (0 : Real) <= 2)
  dsimp [value] at hphaseError ⊢
  calc
    |N.realize x - _| <=
        2 * eps + 2 *
          (Bval * (((M ^ 2 - 1 : Nat) : Real) * (R / 2)⁻¹)) := hphaseError
    _ <= 2 * (Kraw * shallowReLUResolutionRate M r beta +
          ((Fintype.card (TaylorMultiindex r d) : Real) * (C + 1) *
            Real.rpow 4 ((r : Real) + beta)) *
              shallowReLUResolutionRate M r beta) +
        2 * (Bval * shallowReLUResolutionRate M r beta) := by
          exact add_le_add hscaledEps hscaledBoundary
    _ = Kphase * shallowReLUResolutionRate M r beta := by
      dsimp [Kphase, twoScalePhaseRateConstant, Bval, Rval, Kraw]
      ring

/-- The `2^d` interlaced paper partitions jointly form a tensor hat partition
of unity on the target cube. -/
private theorem reluApprox_phaseShiftedTent_partition
    {d M : Nat} (hM : 2 <= M)
    (orderC orderF : Fin (M ^ d) ≃ (Fin d -> Fin M))
    (x : Fin d -> Real)
    (hx : forall q : Fin d, x q ∈ Set.Icc (0 : Real) 1) :
    (Finset.univ.sum fun phase : Fin d -> Fin 2 =>
      Finset.univ.sum fun b : Fin (M ^ d) =>
        Finset.univ.sum fun t : Fin (M ^ d) =>
          axisAlignedBoxTentWeight
            (twoScaleShiftedCenter M orderC orderF phase b t)
            (twoScaleShiftedScale M phase b t) x) = 1 := by
  let K : Nat := M ^ 2 - 1
  have hK : 0 < K := by
    dsimp [K]
    have hM2 : 4 <= M ^ 2 := by
      have hm := Nat.mul_le_mul hM hM
      norm_num at hm
      simpa [pow_two] using hm
    omega
  have hcardK : M * M = K + 1 := by
    dsimp [K]
    rw [pow_two]
    have hMMpos : 0 < M * M := Nat.mul_pos (by omega) (by omega)
    omega
  let pairDigit : Fin M × Fin M ≃ Fin (K + 1) :=
    finProdFinEquiv.trans (finCongr hcardK)
  let nodeGrid : (Fin (M ^ d) × Fin (M ^ d)) ≃ (Fin d -> Fin (K + 1)) :=
    (orderC.prodCongr orderF).trans
      ((Equiv.arrowProdEquivProdArrow
        (Fin d) (fun _ => Fin M) (fun _ => Fin M)).symm.trans
          (Equiv.piCongrRight fun _ => pairDigit))
  let phaseDigit : Fin (K + 1) × Fin 2 ≃ Fin (2 * (K + 1)) :=
    finProdFinEquiv.trans (finCongr (Nat.mul_comm (K + 1) 2))
  let phaseNode :
      ((Fin d -> Fin 2) × (Fin d -> Fin (K + 1))) ≃
        (Fin d -> Fin (2 * (K + 1))) :=
    (Equiv.prodComm (Fin d -> Fin 2) (Fin d -> Fin (K + 1))).trans
      ((Equiv.arrowProdEquivProdArrow
        (Fin d) (fun _ => Fin (K + 1)) (fun _ => Fin 2)).symm.trans
          (Equiv.piCongrRight fun _ => phaseDigit))
  let gridEquiv :
      ((Fin d -> Fin 2) × (Fin (M ^ d) × Fin (M ^ d))) ≃
        (Fin d -> Fin (2 * (K + 1))) :=
    ((Equiv.refl (Fin d -> Fin 2)).prodCongr nodeGrid).trans phaseNode
  have hgrid_val : forall phase b t q,
      (gridEquiv (phase, (b, t)) q).val =
        2 * ((orderC b q).val * M + (orderF t q).val) + (phase q).val := by
    intro phase b t q
    simp [gridEquiv, phaseNode, phaseDigit, nodeGrid, pairDigit,
      finProdFinEquiv]
    ring
  let z : Fin d -> Real := fun q => (K : Real) * (x q + 1)
  have hz0 : forall q, 0 <= z q := by
    intro q
    exact mul_nonneg (by positivity) (by linarith [(Set.mem_Icc.mp (hx q)).1])
  have hzK : forall q, z q <= 2 * (K : Real) := by
    intro q
    dsimp [z]
    have hx1 := (Set.mem_Icc.mp (hx q)).2
    nlinarith [show (0 : Real) <= (K : Real) by positivity]
  calc
    (Finset.univ.sum fun phase : Fin d -> Fin 2 =>
        Finset.univ.sum fun b : Fin (M ^ d) =>
          Finset.univ.sum fun t : Fin (M ^ d) =>
            axisAlignedBoxTentWeight
              (twoScaleShiftedCenter M orderC orderF phase b t)
              (twoScaleShiftedScale M phase b t) x) =
        Finset.univ.sum fun p :
            (Fin d -> Fin 2) × (Fin (M ^ d) × Fin (M ^ d)) =>
          axisAlignedBoxTentWeight
            (twoScaleShiftedCenter M orderC orderF p.1 p.2.1 p.2.2)
            (twoScaleShiftedScale M p.1 p.2.1 p.2.2) x := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro phase _hphase
      exact (Fintype.sum_prod_type fun p : Fin (M ^ d) × Fin (M ^ d) =>
        axisAlignedBoxTentWeight
          (twoScaleShiftedCenter M orderC orderF phase p.1 p.2)
          (twoScaleShiftedScale M phase p.1 p.2) x).symm
    _ = Finset.univ.sum fun p :
            (Fin d -> Fin 2) × (Fin (M ^ d) × Fin (M ^ d)) =>
          Finset.univ.prod fun q : Fin d =>
            relu (1 - |z q - ((gridEquiv p q).val : Real)|) := by
      apply Finset.sum_congr rfl
      intro p _hp
      unfold axisAlignedBoxTentWeight
      apply Finset.prod_congr rfl
      intro q _hq
      change coordinateTentReLUFunction q
          ((((2 * ((orderC p.2.1 q).val * M + (orderF p.2.2 q).val) +
            (p.1 q).val : Nat) : Real) / (K : Real)) - 1)
          (K : Real) x =
        relu (1 - |z q - ((gridEquiv p q).val : Real)|)
      rw [reluApprox_coordinateTent_shifted_eq_integerTent hK]
      congr 3
      rw [hgrid_val]
    _ = Finset.univ.sum fun v : Fin d -> Fin (2 * (K + 1)) =>
          Finset.univ.prod fun q : Fin d =>
            relu (1 - |z q - ((v q).val : Real)|) := by
      exact Equiv.sum_comp gridEquiv (fun v =>
        Finset.univ.prod fun q : Fin d =>
          relu (1 - |z q - ((v q).val : Real)|))
    _ = 1 := reluApprox_integerTensorTent_sum_eq_one hK z hz0 hzK

/-- Every active shifted tent lies within one inverse fine-grid scale of its
center in each coordinate. -/
private theorem reluApproxPhaseShifted_active_coord_le_inv
    {d M : Nat} (hM : 2 <= M)
    (orderC orderF : Fin (M ^ d) ≃ (Fin d -> Fin M))
    (phase : Fin d -> Fin 2) (b t : Fin (M ^ d))
    (x : Fin d -> Real)
    (hactive : forall q : Fin d,
      twoScaleShiftedScale M phase b t q *
          (relu (x q - twoScaleShiftedCenter M orderC orderF phase b t q) +
            relu (twoScaleShiftedCenter M orderC orderF phase b t q - x q)) < 1) :
    forall q : Fin d,
      |x q - twoScaleShiftedCenter M orderC orderF phase b t q| <=
        ((M ^ 2 - 1 : Nat) : Real)⁻¹ := by
  let K : Nat := M ^ 2 - 1
  have hK : 0 < K := by
    dsimp [K]
    have hM2 : 4 <= M ^ 2 := by
      have hm := Nat.mul_le_mul hM hM
      norm_num at hm
      simpa [pow_two] using hm
    omega
  have hKR : (0 : Real) < (K : Real) := by exact_mod_cast hK
  have hKne : (K : Real) ≠ 0 := ne_of_gt hKR
  intro q
  have hrelu_abs : forall y : Real, relu y + relu (-y) = |y| := by
    intro y
    by_cases hy : 0 <= y
    · simp [relu, max_eq_left hy, max_eq_right (by linarith : -y <= 0),
        abs_of_nonneg hy]
    · have hy' : y <= 0 := le_of_not_ge hy
      simp [relu, max_eq_right hy', max_eq_left (by linarith : 0 <= -y),
        abs_of_nonpos hy']
  have hneg :
      twoScaleShiftedCenter M orderC orderF phase b t q - x q =
        -(x q - twoScaleShiftedCenter M orderC orderF phase b t q) := by
    ring
  have hmul : (K : Real) *
      |x q - twoScaleShiftedCenter M orderC orderF phase b t q| < 1 := by
    have h := hactive q
    simp only [twoScaleShiftedScale] at h
    rw [hneg, hrelu_abs] at h
    simpa [K] using h
  have hinv : (0 : Real) < (K : Real)⁻¹ := inv_pos.mpr hKR
  have hscaled := mul_lt_mul_of_pos_left hmul hinv
  have hlt :
      |x q - twoScaleShiftedCenter M orderC orderF phase b t q| <
        (K : Real)⁻¹ := by
    calc
      |x q - twoScaleShiftedCenter M orderC orderF phase b t q| =
          (K : Real)⁻¹ * ((K : Real) *
            |x q - twoScaleShiftedCenter M orderC orderF phase b t q|) := by
              rw [← mul_assoc, inv_mul_cancel₀ hKne, one_mul]
      _ < (K : Real)⁻¹ * 1 := hscaled
      _ = (K : Real)⁻¹ := mul_one _
  simpa [K] using le_of_lt hlt

/-- The active shifted tent also satisfies the corresponding sup-norm bound. -/
private theorem reluApproxPhaseShifted_active_norm_le_inv
    {d M : Nat} (hM : 2 <= M)
    (orderC orderF : Fin (M ^ d) ≃ (Fin d -> Fin M))
    (phase : Fin d -> Fin 2) (b t : Fin (M ^ d))
    (x : Fin d -> Real)
    (hactive : forall q : Fin d,
      twoScaleShiftedScale M phase b t q *
          (relu (x q - twoScaleShiftedCenter M orderC orderF phase b t q) +
            relu (twoScaleShiftedCenter M orderC orderF phase b t q - x q)) < 1) :
    ‖x - twoScaleShiftedCenter M orderC orderF phase b t‖ <=
      ((M ^ 2 - 1 : Nat) : Real)⁻¹ := by
  have hinv_nonneg : (0 : Real) <= ((M ^ 2 - 1 : Nat) : Real)⁻¹ := by positivity
  apply (pi_norm_le_iff_of_nonneg hinv_nonneg).2
  intro q
  simpa using
    (reluApproxPhaseShifted_active_coord_le_inv hM orderC orderF phase b t x hactive q)

/-- Exact Taylor partition associated with all `2^d` shifted coarse/fine
grids used in the paper construction. -/
private noncomputable def reluApproxPhaseShiftedWeightedTaylorSum
    (r d M : Nat)
    (orderC orderF : Fin (M ^ d) ≃ (Fin d -> Fin M))
    (f : (Fin d -> Real) -> Real) (x : Fin d -> Real) : Real :=
  Finset.univ.sum fun phase : Fin d -> Fin 2 =>
    Finset.univ.sum fun b : Fin (M ^ d) =>
      Finset.univ.sum fun t : Fin (M ^ d) =>
        axisAlignedBoxTentWeight
            (twoScaleShiftedCenter M orderC orderF phase b t)
            (twoScaleShiftedScale M phase b t) x *
          finiteLinearCombination (Finset.univ : Finset (TaylorMultiindex r d))
            (fun a => ((Nat.factorial a.1.val : Real)⁻¹) *
              (iteratedFDeriv Real a.1.val f
                (twoScaleShiftedCenter M orderC orderF phase b t))
                  (fun k : Fin a.1.val => fun q : Fin d =>
                    if q = a.2 k then 1 else 0))
            (fun a y => Finset.univ.prod fun k : Fin a.1.val =>
              y (a.2 k) -
                twoScaleShiftedCenter M orderC orderF phase b t (a.2 k)) x

/-- The exact Taylor sum over all shifted paper grids has the local Holder
remainder at the fine-grid radius. -/
private theorem reluApproxPhaseShiftedWeightedTaylorSum_error
    {d r M : Nat} {beta C B : Real}
    (hd : 0 < d) (hM : 2 <= M)
    (hbeta_pos : 0 < beta) (hC_nonneg : 0 <= C)
    (orderC orderF : Fin (M ^ d) ≃ (Fin d -> Fin M))
    (f : (Fin d -> Real) -> Real) (hf : f ∈ holderSmoothBall r beta C B)
    (x : Fin d -> Real)
    (hx : forall q : Fin d, x q ∈ Set.Icc (0 : Real) 1) :
    |reluApproxPhaseShiftedWeightedTaylorSum r d M orderC orderF f x - f x| <=
      (C / (Nat.factorial r : Real)) *
        (((M ^ 2 - 1 : Nat) : Real)⁻¹).rpow ((r : Real) + beta) := by
  classical
  let I := (Fin d -> Fin 2) × (Fin (M ^ d) × Fin (M ^ d))
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  have hMd : 0 < M ^ d := Nat.pow_pos (by omega)
  have hI : Nonempty I := by
    dsimp [I]
    exact ⟨(fun _ => 0, (⟨0, hMd⟩, ⟨0, hMd⟩))⟩
  letI : Nonempty I := hI
  have hcardI : 0 < Fintype.card I := Fintype.card_pos_iff.mpr hI
  letI : Nonempty (Fin (Fintype.card I)) := ⟨⟨0, hcardI⟩⟩
  let center : Fin (Fintype.card I) -> Fin d -> Real := fun j =>
    twoScaleShiftedCenter M orderC orderF
      (e.symm j).1 (e.symm j).2.1 (e.symm j).2.2
  let scale : Fin (Fintype.card I) -> Fin d -> Real := fun j =>
    twoScaleShiftedScale M
      (e.symm j).1 (e.symm j).2.1 (e.symm j).2.2
  let coeff : Fin (Fintype.card I) -> TaylorMultiindex r d -> Real := fun j a =>
    ((Nat.factorial a.1.val : Real)⁻¹) *
      (iteratedFDeriv Real a.1.val f (center j))
        (fun k : Fin a.1.val => fun q : Fin d => if q = a.2 k then 1 else 0)
  let basis : Fin (Fintype.card I) -> TaylorMultiindex r d ->
      (Fin d -> Real) -> Real := fun j a y =>
    Finset.univ.prod fun k : Fin a.1.val => y (a.2 k) - center j (a.2 k)
  let weight : Fin (Fintype.card I) -> Unit -> Real := fun j _ =>
    axisAlignedBoxTentWeight (center j) (scale j) x
  let approx : Fin (Fintype.card I) -> Unit -> Real := fun j _ =>
    finiteLinearCombination (Finset.univ : Finset (TaylorMultiindex r d))
      (coeff j) (basis j) x
  let target : Unit -> Real := fun _ => f x
  let eps : Real := (C / (Nat.factorial r : Real)) *
    (((M ^ 2 - 1 : Nat) : Real)⁻¹).rpow ((r : Real) + beta)
  have hscale_nonneg : forall j q, 0 <= scale j q := by
    intro j q
    simp [scale, twoScaleShiftedScale]
  have hweight_nonneg : forall j u, 0 <= weight j u := by
    intro j u
    exact (axisAlignedBoxTentWeight_bounds_and_support
      (center j) (scale j) x (hscale_nonneg j)).1
  have hpartition : forall u : Unit,
      (Finset.univ.sum fun j : Fin (Fintype.card I) => weight j u) = 1 := by
    intro u
    have hreindex :
        (Finset.univ.sum fun j : Fin (Fintype.card I) =>
          axisAlignedBoxTentWeight (center j) (scale j) x) =
        Finset.univ.sum fun p : I =>
          axisAlignedBoxTentWeight
            (twoScaleShiftedCenter M orderC orderF p.1 p.2.1 p.2.2)
            (twoScaleShiftedScale M p.1 p.2.1 p.2.2) x := by
      exact Equiv.sum_comp e.symm (fun p : I =>
        axisAlignedBoxTentWeight
          (twoScaleShiftedCenter M orderC orderF p.1 p.2.1 p.2.2)
          (twoScaleShiftedScale M p.1 p.2.1 p.2.2) x)
    rw [show (Finset.univ.sum fun j : Fin (Fintype.card I) => weight j u) =
        Finset.univ.sum fun j : Fin (Fintype.card I) =>
          axisAlignedBoxTentWeight (center j) (scale j) x by rfl]
    rw [hreindex]
    change (Finset.univ.sum fun p :
        (Fin d -> Fin 2) × (Fin (M ^ d) × Fin (M ^ d)) =>
      axisAlignedBoxTentWeight
        (twoScaleShiftedCenter M orderC orderF p.1 p.2.1 p.2.2)
        (twoScaleShiftedScale M p.1 p.2.1 p.2.2) x) = 1
    calc
      (Finset.univ.sum fun p :
          (Fin d -> Fin 2) × (Fin (M ^ d) × Fin (M ^ d)) =>
        axisAlignedBoxTentWeight
          (twoScaleShiftedCenter M orderC orderF p.1 p.2.1 p.2.2)
          (twoScaleShiftedScale M p.1 p.2.1 p.2.2) x) =
          Finset.univ.sum fun phase : Fin d -> Fin 2 =>
            Finset.univ.sum fun p : Fin (M ^ d) × Fin (M ^ d) =>
              axisAlignedBoxTentWeight
                (twoScaleShiftedCenter M orderC orderF phase p.1 p.2)
                (twoScaleShiftedScale M phase p.1 p.2) x := by
            exact Fintype.sum_prod_type _
      _ = Finset.univ.sum fun phase : Fin d -> Fin 2 =>
            Finset.univ.sum fun b : Fin (M ^ d) =>
              Finset.univ.sum fun t : Fin (M ^ d) =>
                axisAlignedBoxTentWeight
                  (twoScaleShiftedCenter M orderC orderF phase b t)
                  (twoScaleShiftedScale M phase b t) x := by
            apply Finset.sum_congr rfl
            intro phase _hphase
            exact Fintype.sum_prod_type _
      _ = 1 := reluApprox_phaseShiftedTent_partition hM orderC orderF x hx
  have hlocal : forall j u, weight j u ≠ 0 ->
      |approx j u - target u| <= eps := by
    intro j u hj
    have hsupport := axisAlignedBoxTentWeight_bounds_and_support
      (center j) (scale j) x (hscale_nonneg j)
    have hactive : forall q,
        scale j q * (relu (x q - center j q) + relu (center j q - x q)) < 1 := by
      by_contra hnot
      push_neg at hnot
      exact hj (hsupport.2.2 hnot)
    have hnorm : ‖x - center j‖ <= ((M ^ 2 - 1 : Nat) : Real)⁻¹ := by
      simpa [center, scale] using
        (reluApproxPhaseShifted_active_norm_le_inv hM orderC orderF
          (e.symm j).1 (e.symm j).2.1 (e.symm j).2.2 x (by simpa [scale, center] using hactive))
    have htaylor := holderSmoothBall_finite_centered_coordinate_polynomial_error_on_norm_ball
      hbeta_pos.le hC_nonneg
      (show (0 : Real) <= ((M ^ 2 - 1 : Nat) : Real)⁻¹ by positivity)
      f hf (center j) x hnorm
    rw [abs_sub_comm] at htaylor
    simpa [approx, target, eps, coeff, basis] using htaylor
  have hres :=
    Statlib.Nonparametric.Approximation.Sieve.partition_of_unity_weighted_function_pointwise_approximation_error_bound
      (Fintype.card I) weight approx target eps hweight_nonneg hpartition hlocal ()
  have hsum :
      (Finset.univ.sum fun j : Fin (Fintype.card I) => weight j () * approx j ()) =
        reluApproxPhaseShiftedWeightedTaylorSum r d M orderC orderF f x := by
    calc
      (Finset.univ.sum fun j : Fin (Fintype.card I) => weight j () * approx j ()) =
          Finset.univ.sum fun p : I =>
            axisAlignedBoxTentWeight
                (twoScaleShiftedCenter M orderC orderF p.1 p.2.1 p.2.2)
                (twoScaleShiftedScale M p.1 p.2.1 p.2.2) x *
              finiteLinearCombination (Finset.univ : Finset (TaylorMultiindex r d))
                (fun a => ((Nat.factorial a.1.val : Real)⁻¹) *
                  (iteratedFDeriv Real a.1.val f
                    (twoScaleShiftedCenter M orderC orderF p.1 p.2.1 p.2.2))
                      (fun k : Fin a.1.val => fun q : Fin d =>
                        if q = a.2 k then 1 else 0))
                (fun a y => Finset.univ.prod fun k : Fin a.1.val =>
                  y (a.2 k) -
                    twoScaleShiftedCenter M orderC orderF p.1 p.2.1 p.2.2
                      (a.2 k)) x := by
            simpa [weight, approx, center, scale, coeff, basis] using
              (Equiv.sum_comp e.symm (fun p : I =>
                axisAlignedBoxTentWeight
                    (twoScaleShiftedCenter M orderC orderF p.1 p.2.1 p.2.2)
                    (twoScaleShiftedScale M p.1 p.2.1 p.2.2) x *
                  finiteLinearCombination (Finset.univ : Finset (TaylorMultiindex r d))
                    (fun a => ((Nat.factorial a.1.val : Real)⁻¹) *
                      (iteratedFDeriv Real a.1.val f
                        (twoScaleShiftedCenter M orderC orderF p.1 p.2.1 p.2.2))
                          (fun k : Fin a.1.val => fun q : Fin d =>
                            if q = a.2 k then 1 else 0))
                    (fun a y => Finset.univ.prod fun k : Fin a.1.val =>
                      y (a.2 k) -
                        twoScaleShiftedCenter M orderC orderF
                          p.1 p.2.1 p.2.2 (a.2 k)) x))
      _ = reluApproxPhaseShiftedWeightedTaylorSum r d M orderC orderF f x := by
        unfold reluApproxPhaseShiftedWeightedTaylorSum
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro phase _hphase
        exact Fintype.sum_prod_type fun p : Fin (M ^ d) × Fin (M ^ d) =>
          axisAlignedBoxTentWeight
              (twoScaleShiftedCenter M orderC orderF phase p.1 p.2)
              (twoScaleShiftedScale M phase p.1 p.2) x *
            finiteLinearCombination (Finset.univ : Finset (TaylorMultiindex r d))
              (fun a => ((Nat.factorial a.1.val : Real)⁻¹) *
                (iteratedFDeriv Real a.1.val f
                  (twoScaleShiftedCenter M orderC orderF phase p.1 p.2))
                    (fun k : Fin a.1.val => fun q : Fin d =>
                      if q = a.2 k then 1 else 0))
              (fun a y => Finset.univ.prod fun k : Fin a.1.val =>
                y (a.2 k) -
                  twoScaleShiftedCenter M orderC orderF phase p.1 p.2
                    (a.2 k)) x
  rw [hsum] at hres
  exact hres

/-- Summing one robust approximation for each shifted phase multiplies the
per-phase error only by the number of phases. -/
private theorem reluApproxPhaseShifted_phase_family_robust_error
    {d M : Nat} {eps : Real}
    (orderC orderF : Fin (M ^ d) ≃ (Fin d -> Fin M))
    (phaseApprox : (Fin d -> Fin 2) -> Real)
    (value : (Fin d -> Fin 2) ->
      (Fin (M ^ d) × Fin (M ^ d)) -> Real)
    (x : Fin d -> Real)
    (hphase : forall phase : Fin d -> Fin 2,
      |phaseApprox phase -
        (Finset.univ.sum fun b : Fin (M ^ d) =>
          Finset.univ.sum fun t : Fin (M ^ d) =>
            axisAlignedBoxTentWeight
                (twoScaleShiftedCenter M orderC orderF phase b t)
                (twoScaleShiftedScale M phase b t) x *
              value phase (b, t))| <= eps) :
    |(Finset.univ.sum phaseApprox) -
      (Finset.univ.sum fun phase : Fin d -> Fin 2 =>
        Finset.univ.sum fun b : Fin (M ^ d) =>
          Finset.univ.sum fun t : Fin (M ^ d) =>
            axisAlignedBoxTentWeight
                (twoScaleShiftedCenter M orderC orderF phase b t)
                (twoScaleShiftedScale M phase b t) x *
              value phase (b, t))| <=
      (Fintype.card (Fin d -> Fin 2) : Real) * eps := by
  let target : (Fin d -> Fin 2) -> Real := fun phase =>
    Finset.univ.sum fun b : Fin (M ^ d) =>
      Finset.univ.sum fun t : Fin (M ^ d) =>
        axisAlignedBoxTentWeight
            (twoScaleShiftedCenter M orderC orderF phase b t)
            (twoScaleShiftedScale M phase b t) x *
          value phase (b, t)
  change |Finset.univ.sum phaseApprox - Finset.univ.sum target| <= _
  rw [← Finset.sum_sub_distrib]
  calc
    |Finset.univ.sum fun phase => phaseApprox phase - target phase| <=
        Finset.univ.sum fun phase => |phaseApprox phase - target phase| :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= Finset.univ.sum fun _phase : Fin d -> Fin 2 => eps := by
      exact Finset.sum_le_sum fun phase _ => hphase phase
    _ = (Fintype.card (Fin d -> Fin 2) : Real) * eps := by simp

/-- Combining the robust shifted-phase programs with the exact shifted Taylor
partition leaves only the summed phase error and the Holder Taylor remainder. -/
theorem two_scale_phase_family_holder_error
    {d r M : Nat} {beta C B eps : Real}
    (hd : 0 < d) (hM : 2 <= M)
    (hbeta_pos : 0 < beta) (hC_nonneg : 0 <= C)
    (orderC orderF : Fin (M ^ d) ≃ (Fin d -> Fin M))
    (f : (Fin d -> Real) -> Real) (hf : f ∈ holderSmoothBall r beta C B)
    (phaseApprox : (Fin d -> Fin 2) -> Real)
    (x : Fin d -> Real)
    (hx : forall q : Fin d, x q ∈ Set.Icc (0 : Real) 1)
    (hphase : forall phase : Fin d -> Fin 2,
      |phaseApprox phase -
        (Finset.univ.sum fun b : Fin (M ^ d) =>
          Finset.univ.sum fun t : Fin (M ^ d) =>
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
                      (a.2 k)) x)| <= eps) :
    |Finset.univ.sum phaseApprox - f x| <=
      (Fintype.card (Fin d -> Fin 2) : Real) * eps +
        (C / (Nat.factorial r : Real)) *
          (((M ^ 2 - 1 : Nat) : Real)⁻¹).rpow ((r : Real) + beta) := by
  let exactSum := reluApproxPhaseShiftedWeightedTaylorSum
    r d M orderC orderF f x
  have hfamily :
      |Finset.univ.sum phaseApprox - exactSum| <=
        (Fintype.card (Fin d -> Fin 2) : Real) * eps := by
    apply reluApproxPhaseShifted_phase_family_robust_error
      orderC orderF phaseApprox
      (fun phase p =>
        finiteLinearCombination (Finset.univ : Finset (TaylorMultiindex r d))
          (fun a => ((Nat.factorial a.1.val : Real)⁻¹) *
            (iteratedFDeriv Real a.1.val f
              (twoScaleShiftedCenter M orderC orderF phase p.1 p.2))
                (fun k : Fin a.1.val => fun q : Fin d =>
                  if q = a.2 k then 1 else 0))
          (fun a y => Finset.univ.prod fun k : Fin a.1.val =>
            y (a.2 k) -
              twoScaleShiftedCenter M orderC orderF phase p.1 p.2
                (a.2 k)) x)
      x
    exact hphase
  have hTaylor := reluApproxPhaseShiftedWeightedTaylorSum_error
    hd hM hbeta_pos hC_nonneg orderC orderF f hf x hx
  calc
    |Finset.univ.sum phaseApprox - f x| <=
        |Finset.univ.sum phaseApprox - exactSum| + |exactSum - f x| :=
      abs_sub_le _ _ _
    _ <= (Fintype.card (Fin d -> Fin 2) : Real) * eps +
        (C / (Nat.factorial r : Real)) *
          (((M ^ 2 - 1 : Nat) : Real)⁻¹).rpow ((r : Real) + beta) :=
      add_le_add hfamily hTaylor

end Statlib.Nonparametric.Approximation.NeuralNetworkAlgebra
