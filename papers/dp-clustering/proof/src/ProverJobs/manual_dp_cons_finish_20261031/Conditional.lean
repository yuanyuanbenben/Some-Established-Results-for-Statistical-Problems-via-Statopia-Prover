import ProverJobs.manual_dp_cons_finish_20261031.Expectation
import ProverJobs.manual_dp_cons_density_20261031.DensityCancel
import ProverJobs.manual_dp_root_finish_20261031.LabelCells
import ProverJobs.manual_dp_root_finish_20261031.MixtureLabels
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace ManualDPCons
open Statlib.Imported

/-- Source analytic assumptions only; no likelihood, expectation, or convergence field. -/
structure LocationConfig where
  t : ℕ
  ht : 1 ≤ t
  c : ℝ
  hc : 0 < c
  g : ℝ → ℝ
  q0 : ℝ → ℝ
  theta : Fin t → ℝ
  m : ℝ
  U : ℝ
  M : ℝ
  R : ℝ
  L : ℝ
  r : ℝ
  hm : 0 < m
  hU : 0 < U
  hM : 0 ≤ M
  hR : 0 ≤ R
  hL : 0 < L
  hr : 0 < r
  N : Fin t → ℕ
  hN : ∀ j, 1 ≤ N j
  hg : Measurable g
  hg0 : ∀ z, 0 ≤ g z
  hgpos : ∀ z ∈ Set.Icc (-c) c, 0 < g z
  hgzero : ∀ z, z ∉ Set.Icc (-c) c → g z = 0
  hglo : ∀ z ∈ Set.Icc (-c) c, m ≤ g z
  hgM : ∀ z, g z ≤ M
  hgnorm : ∫ z, g z ∂volume = 1
  hgdiff : DifferentiableOn ℝ g (Set.Ioo (-c) c)
  hgderiv : ∀ z ∈ Set.Ioo (-c) c, |deriv g z / g z| ≤ R
  hq : Measurable q0
  hq0 : ∀ z, 0 ≤ q0 z
  hqnorm : ∫ z, q0 z ∂volume = 1
  hqint : Integrable q0 volume
  hQ : IsProbabilityMeasure (dpQ0 q0)
  hRprob : ∀ j, IsProbabilityMeasure (dpRmeasure g theta j)
  hT3 : ∀ j y, y ∈ Set.Icc (0 : ℝ) (2*c) → q0 (theta j+y)+q0 (theta j-y) ≤ U
  hT4 : ∀ j z, |z-theta j| < r → L ≤ q0 z
  hsep : ∀ j k, j ≠ k → 2*c < |theta j-theta k|

/-- A canonical finite observation vector extension. All model expressions use only its prefix. -/
def prefixPath {n : ℕ} (x : Fin n → ℝ) (i : ℕ) : ℝ := if h : i < n then x ⟨i,h⟩ else 0

@[simp] lemma prefixPath_apply {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : prefixPath x i = x i := by
  simp [prefixPath]
@[simp] lemma Xseq_prefixPath {n : ℕ} (x : Fin n → ℝ) : dpXseq n (prefixPath x) = x := by
  funext i
  exact prefixPath_apply x i

lemma prefixPath_measurable (n : ℕ) : Measurable (@prefixPath n) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : i < n
  · simpa only [prefixPath, dif_pos hi] using measurable_pi_apply (⟨i,hi⟩ : Fin n)
  · simpa only [prefixPath, dif_neg hi] using (measurable_const : Measurable (fun _ : Fin n → ℝ => (0:ℝ)))

def ratioIntegrand (C : LocationConfig) (n k : ℕ) (x : Fin n → ℝ) : ℝ := by
  classical
  exact if dpOmega C.c C.theta C.N n (prefixPath x) then
    partitionSum C.g C.q0 n k x / partitionSum C.g C.q0 n C.t x else 0

def labelLaw (C : LocationConfig) (n : ℕ) (lab : Fin n → Fin C.t) : Measure (Fin n → ℝ) :=
  Measure.pi (fun i => dpRmeasure C.g C.theta (lab i))

def labelCounts (C : LocationConfig) {n : ℕ} (lab : Fin n → Fin C.t) (j : Fin C.t) : ℕ :=
  (Finset.univ.filter (fun i => lab i = j)).card

def denominatorLoss (C : LocationConfig) (n : ℕ) : ℝ :=
  (Real.log (n : ℝ)) ^ ((1:ℝ)/2) / (C.L * Real.exp (-C.R) * min 1 C.r / 2) ^ C.t

lemma denominatorLoss_nonneg (C : LocationConfig) (n : ℕ) : 0 ≤ denominatorLoss C n := by
  dsimp [denominatorLoss]
  have hlog : 0 ≤ Real.log (n : ℝ) := by
    by_cases hn : n = 0
    · simp [hn]
    · exact Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn))
  exact div_nonneg (Real.rpow_nonneg hlog _) (pow_nonneg (by
    have h1 := C.hL
    have h2 := C.hr
    positivity) _)

lemma labelLaw_ae_cell (C : LocationConfig) (n : ℕ) (lab : Fin n → Fin C.t) :
    ∀ᵐ x ∂labelLaw C n lab, ∀ i, x i ∈ Set.Icc (C.theta (lab i)-C.c) (C.theta (lab i)+C.c) := by
  haveI : ∀ i : Fin n, IsProbabilityMeasure (dpRmeasure C.g C.theta (lab i)) := fun i => C.hRprob _
  apply ae_all_iff.mpr
  intro i
  apply (Measure.tendsto_eval_ae_ae (μ := fun i => dpRmeasure C.g C.theta (lab i)) (i := i)).eventually
  apply (ae_withDensity_iff ((C.hg.comp (measurable_id.sub_const _)).ennreal_ofReal)).mpr
  apply Eventually.of_forall
  intro y hy
  by_contra hmem
  have hz : C.g (y-C.theta (lab i)) = 0 := C.hgzero _ (by
    intro h
    exact hmem ⟨by linarith [h.1], by linarith [h.2]⟩)
  exact hy (by simpa only [Function.comp_apply, id_eq, hz, ENNReal.ofReal_zero])

lemma labelLaw_ae_interior (C : LocationConfig) (n : ℕ) (lab : Fin n → Fin C.t) :
    ∀ᵐ x ∂labelLaw C n lab, ∀ j i,
      i ∈ dpBlock C.c C.theta n (prefixPath x) j → -C.c < x i-C.theta j := by
  haveI : ∀ i : Fin n, IsProbabilityMeasure (dpRmeasure C.g C.theta (lab i)) := fun i => C.hRprob _
  have havoid : ∀ᵐ x ∂labelLaw C n lab, ∀ (i : Fin n) (j : Fin C.t), x i ≠ C.theta j-C.c := by
    apply ae_all_iff.mpr
    intro i
    change ∀ᵐ x ∂Measure.pi (fun i => dpRmeasure C.g C.theta (lab i)), ∀ j : Fin C.t, x i ≠ C.theta j-C.c
    have hcoord : ∀ᵐ y ∂dpRmeasure C.g C.theta (lab i), ∀ j : Fin C.t, y ≠ C.theta j-C.c := by
      apply ae_all_iff.mpr
      intro j
      apply (withDensity_absolutelyContinuous volume (fun y => ENNReal.ofReal (C.g (y-C.theta (lab i))))).ae_le
      exact ae_iff.mpr (by simp)
    exact (Measure.tendsto_eval_ae_ae (μ := fun i => dpRmeasure C.g C.theta (lab i)) (i := i)).eventually hcoord
  filter_upwards [havoid] with x hx
  intro j i hi
  have hm : C.theta j-C.c ≤ x i := by simpa [dpBlock] using (show prefixPath x (i:ℕ) ∈ Set.Icc (C.theta j-C.c) (C.theta j+C.c) from by simpa [dpBlock] using hi).1
  have hh : C.theta j-C.c < x i := lt_of_le_of_ne hm (Ne.symm (hx i j))
  linarith

#print axioms labelLaw_ae_cell
#print axioms labelLaw_ae_interior
end ManualDPCons
