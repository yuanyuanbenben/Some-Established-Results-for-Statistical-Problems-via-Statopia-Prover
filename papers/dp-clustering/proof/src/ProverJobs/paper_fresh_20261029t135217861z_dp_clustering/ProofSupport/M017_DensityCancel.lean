import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions
import Mathlib

/- Original module ProverJobs.manual_dp_cons_density_20261031.DensityCancel; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace ManualDPConsDensity

lemma lintegral_fin_prod {n : ℕ} (mu : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (mu i)] (f : Fin n → ℝ → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x : Fin n → ℝ, ∏ i, f i (x i) ∂Measure.pi mu) = ∏ i, ∫⁻ x, f i x ∂mu i := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = ∫⁻ x : ℝ × (Fin n → ℝ), f 0 x.1 * ∏ i : Fin n, f i.succ (x.2 i)
          ∂(mu 0).prod (Measure.pi (fun i => mu i.succ)) := by
        rw [← ((measurePreserving_piFinSuccAbove mu 0).symm).lintegral_comp (by fun_prop)]
        simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
          Fin.zero_succAbove, cast_eq, Fin.cons_zero]
      _ = (∫⁻ x, f 0 x ∂mu 0) * ∏ i : Fin n, ∫⁻ x, f i.succ x ∂mu i.succ := by
        rw [← ih (fun i => mu i.succ) (fun i => f i.succ) (fun i => hf i.succ)]
        exact lintegral_prod_mul (μ := mu 0) (ν := Measure.pi (fun i : Fin n => mu i.succ)) (f := f 0) (g := fun x : Fin n → ℝ => ∏ i, f i.succ (x i))
          (hf 0).aemeasurable
          (Finset.measurable_prod Finset.univ (fun i _ => (hf i.succ).comp (measurable_pi_apply i))).aemeasurable
      _ = _ := by rw [Fin.prod_univ_succ]

lemma pi_withDensity {n : ℕ} (mu : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (mu i)] (f : Fin n → ℝ → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((mu i).withDensity (f i))] :
    Measure.pi (fun i => (mu i).withDensity (f i)) =
      (Measure.pi mu).withDensity (fun x => ∏ i, f i (x i)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  rw [lintegral_fin_prod (fun i => (mu i).restrict (s i)) f hf]
  apply Finset.prod_congr rfl
  intro i hi
  exact (withDensity_apply (f i) (hs i)).symm

/-- Finite-product density cancellation, with no measurability requirement on the bounded
integrand. The dominating numerator need not be integrable. -/
lemma pi_density_cancel {n : ℕ} (mu : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (mu i)] (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, Measurable (f i)) (hf0 : ∀ i x, 0 ≤ f i x)
    (hpos : ∀ᵐ x : Fin n → ℝ ∂Measure.pi mu, 0 < ∏ i, f i (x i))
    (A : ℝ) (hA : 0 ≤ A) (F Z : (Fin n → ℝ) → ℝ)
    (hbound : ∀ᵐ x : Fin n → ℝ ∂Measure.pi (fun i => (mu i).withDensity (fun y => ENNReal.ofReal (f i y))),
      Z x ≤ A * F x / (∏ i, f i (x i))) :
    (∫⁻ x : Fin n → ℝ, ENNReal.ofReal (Z x)
      ∂Measure.pi (fun i => (mu i).withDensity (fun y => ENNReal.ofReal (f i y)))) ≤
      ENNReal.ofReal A * ∫⁻ x : Fin n → ℝ, ENNReal.ofReal (F x) ∂Measure.pi mu := by
  let D := fun x : Fin n → ℝ => ∏ i, f i (x i)
  have hm : Measurable D := Finset.measurable_prod Finset.univ (fun i _ => (hf i).comp (measurable_pi_apply i))
  have hD0 : ∀ x, 0 ≤ D x := fun x => Finset.prod_nonneg (fun i _ => hf0 i _)
  have hmu : Measure.pi (fun i => (mu i).withDensity (fun y => ENNReal.ofReal (f i y))) =
      (Measure.pi mu).withDensity (fun x => ENNReal.ofReal (D x)) := by
    rw [pi_withDensity mu (fun i y => ENNReal.ofReal (f i y)) (fun i => (hf i).ennreal_ofReal)]
    congr 1
    funext x
    exact (ENNReal.ofReal_prod_of_nonneg (fun i _ => hf0 i (x i))).symm
  rw [hmu] at hbound ⊢
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (A * F x / D x) ∂(Measure.pi mu).withDensity (fun x => ENNReal.ofReal (D x)) :=
      lintegral_mono_ae (hbound.mono (fun x hx => ENNReal.ofReal_le_ofReal hx))
    _ = ∫⁻ x, ENNReal.ofReal (D x) * ENNReal.ofReal (A * F x / D x) ∂Measure.pi mu := by
      exact lintegral_withDensity_eq_lintegral_mul_non_measurable _ hm.ennreal_ofReal
        (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)) _
    _ = ∫⁻ x, ENNReal.ofReal A * ENNReal.ofReal (F x) ∂Measure.pi mu := by
      apply lintegral_congr_ae
      filter_upwards [hpos] with x hx
      rw [← ENNReal.ofReal_mul (hD0 x)]
      have he : D x * (A * F x / D x) = A * F x := by
        dsimp only [D] at hx ⊢
        field_simp
      rw [he, ENNReal.ofReal_mul hA]
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

lemma withDensity_supported (f : ℝ → ℝ) (W : Set ℝ) (hW : MeasurableSet W)
    (hzero : ∀ x, x ∉ W → f x = 0) :
    volume.withDensity (fun x => ENNReal.ofReal (f x)) =
      (volume.restrict W).withDensity (fun x => ENNReal.ofReal (f x)) := by
  rw [← restrict_withDensity hW]
  symm
  apply Measure.restrict_eq_self_of_ae_mem
  rw [ae_iff]
  change (volume.withDensity (fun x => ENNReal.ofReal (f x))) Wᶜ = 0
  rw [withDensity_apply _ hW.compl]
  apply setLIntegral_eq_zero hW.compl
  intro x hx
  simp [hzero x hx]

/-- Cancellation for actual compact-window sampling laws, written against the unnormalized
Lebesgue window volumes appearing in the partition coefficient calculation. -/
lemma window_density_cancel {n : ℕ} (f : Fin n → ℝ → ℝ) (W : Fin n → Set ℝ)
    (hf : ∀ i, Measurable (f i)) (hf0 : ∀ i x, 0 ≤ f i x)
    (hW : ∀ i, MeasurableSet (W i))
    (hzero : ∀ i x, x ∉ W i → f i x = 0)
    (hpositive : ∀ i x, x ∈ W i → 0 < f i x)
    (A : ℝ) (hA : 0 ≤ A) (F Z : (Fin n → ℝ) → ℝ)
    (hbound : ∀ᵐ x : Fin n → ℝ ∂Measure.pi (fun i => volume.withDensity (fun y => ENNReal.ofReal (f i y))),
      Z x ≤ A * F x / (∏ i, f i (x i))) :
    (∫⁻ x : Fin n → ℝ, ENNReal.ofReal (Z x)
      ∂Measure.pi (fun i => volume.withDensity (fun y => ENNReal.ofReal (f i y)))) ≤
      ENNReal.ofReal A * ∫⁻ x : Fin n → ℝ, ENNReal.ofReal (F x)
        ∂Measure.pi (fun i => volume.restrict (W i)) := by
  have hmu : Measure.pi (fun i => volume.withDensity (fun y => ENNReal.ofReal (f i y))) =
      Measure.pi (fun i => (volume.restrict (W i)).withDensity (fun y => ENNReal.ofReal (f i y))) := by
    congr 1
    funext i
    exact withDensity_supported (f i) (W i) (hW i) (hzero i)
  rw [hmu] at hbound ⊢
  apply pi_density_cancel (fun i => volume.restrict (W i)) f hf hf0 _ A hA F Z hbound
  have hmem : ∀ᵐ x : Fin n → ℝ ∂Measure.pi (fun i => volume.restrict (W i)), ∀ i, x i ∈ W i := by
    apply ae_all_iff.mpr
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun i => volume.restrict (W i)) (i := i)).eventually
      (ae_restrict_mem (hW i))
  filter_upwards [hmem] with x hx
  exact Finset.prod_pos (fun i _ => hpositive i (x i) (hx i))

end ManualDPConsDensity
end
end DPCompletedProof
