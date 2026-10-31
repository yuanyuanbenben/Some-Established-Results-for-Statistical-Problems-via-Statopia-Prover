import ProverJobs.manual_dp_cons_finish_20261031.Conditional
import Mathlib.MeasureTheory.Order.Lattice
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace OfflineDPConsMeas
open Statlib.Imported ManualDPCons

lemma block_fiber {t : ℕ} (c : ℝ) (theta : Fin t → ℝ) (n : ℕ) (j : Fin t)
    (B : Finset (Fin n)) : MeasurableSet {ω : ℕ → ℝ | dpBlock c theta n ω j = B} := by
  classical
  have heq : {ω : ℕ → ℝ | dpBlock c theta n ω j = B} =
      ⋂ i : Fin n, {ω | (ω (i:ℕ) ∈ Set.Icc (theta j-c) (theta j+c)) ↔ i ∈ B} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h i
      have := Finset.ext_iff.mp h i
      simpa [dpBlock] using this
    · intro h
      ext i
      simpa [dpBlock] using h i
  rw [heq]
  apply MeasurableSet.iInter
  intro i
  have hi : MeasurableSet {ω : ℕ → ℝ | ω (i:ℕ) ∈ Set.Icc (theta j-c) (theta j+c)} := isClosed_Icc.measurableSet.preimage (measurable_pi_apply (i:ℕ))
  by_cases h : i ∈ B
  · simpa [h] using hi
  · simpa only [h, iff_false] using hi.compl

lemma block_card {t : ℕ} (c : ℝ) (theta : Fin t → ℝ) (n : ℕ) (j : Fin t) :
    Measurable (fun ω : ℕ → ℝ => (dpBlock c theta n ω j).card) := by
  classical
  have heq : (fun ω : ℕ → ℝ => (dpBlock c theta n ω j).card) =
      fun ω => ∑ B : Finset (Fin n), if dpBlock c theta n ω j = B then B.card else 0 := by
    funext ω
    simp
  rw [heq]
  exact Finset.measurable_sum _ (fun B _ => Measurable.ite (block_fiber c theta n j B) measurable_const measurable_const)

lemma max_stat {t : ℕ} (c : ℝ) (theta : Fin t → ℝ) (n : ℕ) (j : Fin t) :
    Measurable (fun ω : ℕ → ℝ => dpMaxStat c theta n ω j) := by
  classical
  let f : Finset (Fin n) → (ℕ → ℝ) → ℝ := fun B ω =>
    if h : B.Nonempty then B.sup' h (fun i => ω (i:ℕ)) else 0
  have hf (B : Finset (Fin n)) : Measurable (f B) := by
    dsimp [f]
    split_ifs with h
    · convert (Finset.measurable_sup' h (f := fun i (ω : ℕ → ℝ) => ω (i:ℕ)) (fun i _ => measurable_pi_apply (i:ℕ))) using 1
      funext ω
      exact (Finset.sup'_apply h (fun i (ω : ℕ → ℝ) => ω (i:ℕ)) ω).symm
    · exact measurable_const
  have heq : (fun ω : ℕ → ℝ => dpMaxStat c theta n ω j) =
      fun ω => ∑ B : Finset (Fin n), if dpBlock c theta n ω j = B then f B ω else 0 := by
    funext ω
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    dsimp [dpMaxStat, f]
    split_ifs with h
    · rw [Finset.max'_eq_sup', Finset.sup'_image]
      rfl
    · rfl
  rw [heq]
  exact Finset.measurable_sum _ (fun B _ => Measurable.ite (block_fiber c theta n j B) (hf B) measurable_const)

lemma y_stat {t : ℕ} (c : ℝ) (theta : Fin t → ℝ) (n : ℕ) (j : Fin t) :
    Measurable (fun ω : ℕ → ℝ => dpY c theta n ω j) := by
  unfold dpY
  have hcast : Measurable (fun ω : ℕ → ℝ => ((dpBlock c theta n ω j).card : ℝ)) :=
    (measurable_of_countable (fun a : ℕ => (a : ℝ))).comp (block_card c theta n j)
  exact measurable_const.min ((hcast.mul_const _).mul
    (measurable_const.sub (max_stat c theta n j)))

lemma omega {t : ℕ} (c : ℝ) (theta : Fin t → ℝ) (N : Fin t → ℕ) (n : ℕ) :
    MeasurableSet {ω : ℕ → ℝ | dpOmega c theta N n ω} := by
  simp only [dpOmega, Set.setOf_forall]
  apply MeasurableSet.iInter
  intro j
  exact (measurableSet_le measurable_const (block_card c theta n j)).inter
    ((measurableSet_le measurable_const (y_stat c theta n j)).inter
      (measurableSet_le (y_stat c theta n j) measurable_const))

lemma marginal {n : ℕ} (g q : ℝ → ℝ) (hg : Measurable g) (hq : Measurable q)
    (B : Finset (Fin n)) : Measurable (fun x : Fin n → ℝ => dpMargLik g q x B) := by
  unfold dpMargLik
  let F : (Fin n → ℝ) × ℝ → ℝ := fun z => (∏ i ∈ B, g (z.1 i-z.2)) * q z.2
  have hF : Measurable F := by
    exact (Finset.measurable_prod _ (fun i _ => hg.comp (((measurable_pi_apply i).comp measurable_fst).sub measurable_snd))).mul (hq.comp measurable_snd)
  exact hF.stronglyMeasurable.integral_prod_right'.measurable

lemma partition_sum (g q : ℝ → ℝ) (hg : Measurable g) (hq : Measurable q) (n k : ℕ) :
    Measurable (partitionSum g q n k) := by
  unfold partitionSum
  exact Finset.measurable_sum _ (fun A _ => Finset.measurable_prod _ (fun B _ => (marginal g q hg hq B).const_mul _))

lemma ratio_integrand (C : LocationConfig) (n k : ℕ) : Measurable (ratioIntegrand C n k) := by
  unfold ratioIntegrand
  exact Measurable.ite ((omega C.c C.theta C.N n).preimage (prefixPath_measurable n))
    ((partition_sum _ _ C.hg C.hq n k).div (partition_sum _ _ C.hg C.hq n C.t)) measurable_const
lemma npost (g q piDens : ℝ → ℝ) (hg : Measurable g) (hq : Measurable q)
    (hpi : Measurable piDens) (n k : ℕ) : Measurable (dpNpost g q piDens n k) := by
  let F : (Fin n → ℝ) × ℝ → ℝ := fun z =>
    (∑ A ∈ dpTau n k, dpPartPrior z.2 n A * ∏ B ∈ A, dpMargLik g q z.1 B) * piDens z.2
  have hprior (A : Finset (Finset (Fin n))) : Measurable (fun z : (Fin n → ℝ) × ℝ => dpPartPrior z.2 n A) := by
    unfold dpPartPrior dpRisingFactorial
    exact ((measurable_snd.pow_const _).div (Finset.measurable_prod _ (fun j _ => measurable_snd.add_const _))).mul_const _
  have hF : Measurable F := by
    exact (Finset.measurable_sum _ (fun A _ => (hprior A).mul
      (Finset.measurable_prod _ (fun B _ => (marginal g q hg hq B).comp measurable_fst)))).mul (hpi.comp measurable_snd)
  exact hF.stronglyMeasurable.integral_prod_right'.measurable

lemma postK (g q piDens : ℝ → ℝ) (hg : Measurable g) (hq : Measurable q)
    (hpi : Measurable piDens) (n k : ℕ) : Measurable (dpPostK g q piDens n k) := by
  have hZ : Measurable (dpZpost g q piDens n) := Finset.measurable_sum _ (fun j _ => npost g q piDens hg hq hpi n j)
  exact Measurable.ite (measurableSet_eq_fun hZ measurable_const) measurable_const ((npost g q piDens hg hq hpi n k).div hZ)

lemma postProb (g q piDens : ℝ → ℝ) (hg : Measurable g) (hq : Measurable q)
    (hpi : Measurable piDens) (n k : ℕ) : Measurable (dpPostProb g q piDens n k) :=
  (postK g q piDens hg hq hpi n k).comp (measurable_pi_lambda _ (fun _ => measurable_pi_apply _))

lemma ratio (g q piDens : ℝ → ℝ) (hg : Measurable g) (hq : Measurable q)
    (hpi : Measurable piDens) (t n s : ℕ) : Measurable (dpRatio g q piDens t n s) := by
  unfold dpRatio
  exact Measurable.ite (measurableSet_eq_fun (postProb g q piDens hg hq hpi n t) measurable_const)
    measurable_const ((postProb g q piDens hg hq hpi n (t+s)).div (postProb g q piDens hg hq hpi n t))

lemma prefix_law (P : Measure ℝ) [IsProbabilityMeasure P] (n : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => P)).map (dpXseq n) = Measure.pi (fun _ : Fin n => P) := by
  have hind : iIndepFun (fun i : ℕ => fun ω : ℕ → ℝ => ω i) (Measure.infinitePi (fun _ : ℕ => P)) :=
    iIndepFun_infinitePi (X := fun _ : ℕ => (id : ℝ → ℝ)) (fun _ => measurable_id)
  have hfin := hind.precomp (g := fun i : Fin n => (i:ℕ)) Fin.val_injective
  have heq := (iIndepFun_iff_map_fun_eq_pi_map (fun i : Fin n => (measurable_pi_apply (i:ℕ)).aemeasurable)).mp hfin
  simpa only [Measure.infinitePi_map_eval] using heq

lemma prefix_lintegral (P : Measure ℝ) [IsProbabilityMeasure P] (n : ℕ)
    (F : (Fin n → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ω, F (dpXseq n ω) ∂Measure.infinitePi (fun _ : ℕ => P)) =
      ∫⁻ x, F x ∂Measure.pi (fun _ : Fin n => P) := by
  rw [← prefix_law P n]
  exact (lintegral_map hF (measurable_pi_lambda _ (fun _ => measurable_pi_apply _))).symm

lemma omega_prefix {t : ℕ} (c : ℝ) (theta : Fin t → ℝ) (N : Fin t → ℕ) (n : ℕ) (ω : ℕ → ℝ) :
    dpOmega c theta N n (prefixPath (dpXseq n ω)) ↔ dpOmega c theta N n ω := by
  classical
  have hblock (j : Fin t) : dpBlock c theta n (prefixPath (dpXseq n ω)) j = dpBlock c theta n ω j := by
    ext i
    simp [dpBlock, dpXseq]
  unfold dpOmega dpY dpMaxStat
  simp only [hblock]
  have himage (j : Fin t) : (dpBlock c theta n ω j).image (fun i : Fin n => prefixPath (dpXseq n ω) (i:ℕ)) =
      (dpBlock c theta n ω j).image (fun i : Fin n => ω (i:ℕ)) := by
    congr 1
    funext i
    simp [dpXseq]
  simp only [himage]

lemma ratio_prefix (g q piDens : ℝ → ℝ) (t n s : ℕ) (ω : ℕ → ℝ) :
    dpRatio g q piDens t n s (prefixPath (dpXseq n ω)) = dpRatio g q piDens t n s ω := by
  simp only [dpRatio, dpPostProb, Xseq_prefixPath]

end OfflineDPConsMeas
#print axioms OfflineDPConsMeas.ratio_integrand
#print axioms OfflineDPConsMeas.ratio
#print axioms OfflineDPConsMeas.prefix_lintegral
#print axioms OfflineDPConsMeas.omega_prefix
