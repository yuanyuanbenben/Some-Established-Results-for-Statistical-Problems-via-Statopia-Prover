import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.Vocabulary
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.Base
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.ProvedNodes.Node_486505997_f29df050_c92f1a1a
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.ProvedNodes.Node_643971460_c175e112_fb332a25
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.ProvedNodes.Node_862494992_033c9fee_08689c54

namespace PaperProofTasks.job_paper_de3065fb922748188f3a0354eba90ed9



open _root_.PaperProofTasks.job_paper_de3065fb922748188f3a0354eba90ed9.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

set_option autoImplicit false in
theorem statopia_math_node_3799861955_1c292e8a : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : ℕ) (hq : 1 ≤ q)
    (V : Ω → Fin q → ℝ) (hV : Measurable V)
    (Sigma : Matrix (Fin q) (Fin q) ℝ) (nu : Fin q → ℝ)
    (b : ℝ) (hb : 0 ≤ b)
    (hVar : ∀ k : Fin q, Sigma k k = 1)
    (hMean : ∀ k : Fin q, nu k = ∫ ω, V ω k ∂μ)
    (hCov : ∀ k l : Fin q, Sigma k l = ∫ ω, (V ω k - nu k) * (V ω l - nu l) ∂μ)
    (hGauss : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ
      (fun ω k => V ω k - nu k) Sigma)
    (hL2 : ∀ k : Fin q, MemLp (fun ω => V ω k) 2 μ)
    (hCorr : ∀ k l : Fin q, k ≠ l → Sigma k l < 1)
    (hnu_nonneg : ∀ k : Fin q, 0 ≤ nu k)
    (hnu_le : ∀ k : Fin q, nu k ≤ b)
    (hInt : Integrable (fun ω => coordMax (fun ω' k => V ω' k - nu k) ω) μ)
    (y : ℝ) (t : ℝ) (ht : 0 < t),
    μ {ω | |coordMax V ω - y| ≤ t} ≤
      ENNReal.ofReal
        (4 * t * (b + (∫ ω, coordMax (fun ω' k => V ω' k - nu k) ω ∂μ) + 1)) := by
  /- @proof-region region.target-node.session.d2ff6efc34d65858 begin -/
  intro Ω _ μ _ q hq V hV Sigma nu b hb hVar hMean hCov hGauss hL2 hCorr hnu_nonneg hnu_le hInt y t ht
  set Y : Ω → Fin q → ℝ := fun ω k => V ω k - nu k with hY
  set aM : ℝ := ∫ ω, coordMax Y ω ∂μ with haM
  obtain ⟨hac, hf_meas, hmap, hG_nonneg, hG_mono⟩ :=
    statopia_math_node_862494992_033c9fee μ q hq V hV Sigma nu b hb hVar hMean hCov hGauss hL2 hCorr hnu_nonneg hnu_le
  have haM_nonneg : 0 ≤ aM := by
    let k0 : Fin q := ⟨0, Nat.zero_lt_one.trans_le hq⟩
    have hyk : (fun ω : Ω => Y ω k0) = fun ω : Ω => V ω k0 - nu k0 := by
      funext ω; simp only [hY]
    have hInt0 : Integrable (fun ω : Ω => V ω k0) μ := (hL2 k0).integrable (by norm_num)
    have hconst : Integrable (fun ω : Ω => nu k0) μ := integrable_const (nu k0)
    have hintk : Integrable (fun ω : Ω => Y ω k0) μ := by
      rw [hyk]; exact hInt0.sub hconst
    have hmeanzero : ∫ ω : Ω, Y ω k0 ∂μ = 0 := by
      have h1 : ∫ ω : Ω, Y ω k0 ∂μ = ∫ ω : Ω, V ω k0 ∂μ - ∫ ω : Ω, nu k0 ∂μ := by
        rw [hyk]; exact integral_sub hInt0 hconst
      have hc : ∫ ω : Ω, nu k0 ∂μ = nu k0 := by simp
      rw [h1, (hMean k0).symm, hc]; ring
    have hle : (fun ω : Ω => Y ω k0) ≤ fun ω : Ω => coordMax Y ω := by
      intro ω
      exact le_ciSup (Set.finite_range (fun j : Fin q => Y ω j) |>.bddAbove) k0
    calc (0:ℝ) = ∫ ω : Ω, Y ω k0 ∂μ := hmeanzero.symm
      _ ≤ ∫ ω : Ω, coordMax Y ω ∂μ := integral_mono hintk hInt hle
      _ = aM := haM.symm
  have hZmeas : Measurable (fun ω => coordMax V ω) := by
    have hcoord : ∀ j : Fin q, Measurable (fun ω => V ω j) := fun j => (measurable_pi_iff.mp hV) j
    exact Measurable.iSup hcoord
  set phi : ℝ → ℝ := fun x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2) with hphi
  set G : ℝ → ℝ := fun z =>
      ∑ j : Fin q,
        Real.exp (nu j * z - nu j ^ 2 / 2) *
          (Statlib.Imported.gaussianVecMeasure
            (fun k : {k : Fin q // k ≠ j} => nu k.1 + (z - nu j) * Sigma k.1 j)
            (fun k l : {k : Fin q // k ≠ j} => Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j)
            {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ z}).toReal with hG
  have hG_nonneg' : ∀ z : ℝ, 0 ≤ G z := hG_nonneg
  have hG_mono' : Monotone G := hG_mono
  have hphi_nonneg : ∀ x : ℝ, 0 ≤ phi x := by
    intro x
    exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (Real.exp_pos _).le
  have hφeq : ∀ x : ℝ, phi x = ProbabilityTheory.gaussianPDFReal 0 1 x := by
    intro x
    rw [hphi, ProbabilityTheory.gaussianPDFReal_def]
    simp
  have hvar : ∀ j : Fin q, ∫ ω, (Y ω j) ^ 2 ∂μ ≤ 1 := by
    intro j
    have h1 : ∫ ω, (Y ω j) ^ 2 ∂μ
        = ∫ ω, (V ω j - nu j) * (V ω j - nu j) ∂μ := by
      simp only [hY, pow_two]
    rw [h1, ← hCov j j, hVar j]
  have hf_bound : ∀ z : ℝ, phi z * G z ≤ 2 * (b + aM + 1) := by
    obtain ⟨hMillPos, hMill⟩ := statopia_math_node_486505997_f29df050
    haveI hne : Nonempty (Fin q) := ⟨⟨0, Nat.zero_lt_one.trans_le hq⟩⟩
    have hsubAll : ∀ z : ℝ, {ω | z < coordMax V ω} ⊆ {ω | z - b < coordMax Y ω} := by
      intro z ω hω
      obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun j : Fin q => V ω j)
      have hzi : z < V ω i := (show coordMax V ω = V ω i from hi.symm) ▸ hω
      have hYle : Y ω i ≤ coordMax Y ω :=
        le_ciSup (Finite.bddAbove_range (fun j : Fin q => Y ω j)) i
      have hzY : z - b < Y ω i := by
        show z - b < V ω i - nu i
        linarith [hzi, hnu_le i]
      exact lt_of_lt_of_le hzY hYle
    have hTail : ∀ z : ℝ, μ {ω | z - b < coordMax Y ω}
        ≤ ENNReal.ofReal (Real.exp (-((max (z - b - aM) 0) ^ 2) / 2)) := by
      intro z
      by_cases hr : 0 < z - b - aM
      · have hrpos : 0 < max (z - b - aM) 0 := by
          rw [max_eq_left (le_of_lt hr)]; exact hr
        have htb := statopia_math_node_643971460_c175e112 μ q hq Y Sigma hGauss 1 one_pos hvar hInt (max (z - b - aM) 0) hrpos
        have hseteq : {ω | ∫ ω', coordMax Y ω' ∂μ + max (z - b - aM) 0 ≤ coordMax Y ω}
            = {ω | z - b ≤ coordMax Y ω} := by
          ext ω
          simp only [Set.mem_setOf_eq]
          have h1 : (∫ ω', coordMax Y ω' ∂μ) = aM := haM.symm
          have h2 : aM + max (z - b - aM) 0 = z - b := by
            rw [max_eq_left (le_of_lt hr)]; ring
          rw [h1, h2]
        rw [hseteq] at htb
        calc μ {ω | z - b < coordMax Y ω}
            ≤ μ {ω | z - b ≤ coordMax Y ω} := measure_mono (fun ω h => by
                simp only [Set.mem_setOf_eq] at h ⊢
                exact le_of_lt h)
          _ ≤ ENNReal.ofReal (Real.exp (-((max (z - b - aM) 0) ^ 2) / 2)) := by
                simpa using htb
      · have hzero : max (z - b - aM) 0 = 0 := max_eq_right (not_lt.mp hr)
        rw [hzero]
        have hb1 : μ {ω | z - b < coordMax Y ω} ≤ 1 := by
          have := measure_mono (Set.subset_univ {ω | z - b < coordMax Y ω}) (μ := μ)
          simpa using this
        simpa using hb1
    have hInner : ∀ z : ℝ,
        ENNReal.ofReal ((1 - ∫ u in Set.Iic z, ProbabilityTheory.gaussianPDFReal 0 1 u) * G z)
          ≤ μ {ω | z < coordMax V ω} := by
      intro z
      set P : ℝ := ∫ u in Set.Iic z, ProbabilityTheory.gaussianPDFReal 0 1 u with hP
      have hPpos : 0 < 1 - P := by rw [hP]; exact hMillPos z
      have hset : {ω | z < coordMax V ω} = (fun ω => coordMax V ω) ⁻¹' (Set.Ioi z) := by
        ext ω; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioi]
      rw [hset, ← MeasureTheory.Measure.map_apply hZmeas measurableSet_Ioi]
      rw [hmap (Set.Ioi z) measurableSet_Ioi]
      have hphiFn : phi = fun x => ProbabilityTheory.gaussianPDFReal 0 1 x := funext hφeq
      have hIntPhi : Integrable phi volume := by
        rw [hphiFn]; exact ProbabilityTheory.integrable_gaussianPDFReal 0 1
      have hIntPhiRestr : Integrable phi (volume.restrict (Set.Ioi z)) := hIntPhi.restrict
      have hstep3 : ∫⁻ x in Set.Ioi z, ENNReal.ofReal (phi x) = ENNReal.ofReal (1 - P) := by
        rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntPhiRestr
              (Filter.Eventually.of_forall hphi_nonneg)]
        congr 1
        have hcompl := MeasureTheory.integral_add_compl (μ := volume) (s := Set.Iic z) measurableSet_Iic hIntPhi
        rw [Set.compl_Iic] at hcompl
        have hPval : ∫ u in Set.Iic z, phi u = P := by
          simp only [hφeq]
          rw [hP]
        have hTot : ∫ x, phi x = 1 := by
          rw [hphiFn]; exact ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 (by norm_num)
        linarith [hcompl, hPval, hTot]
      have hpm : Measurable phi := by
        rw [hphiFn]; exact ProbabilityTheory.measurable_gaussianPDFReal 0 1
      have hfac : ∫⁻ x in Set.Ioi z, ENNReal.ofReal (phi x * G z)
          = ENNReal.ofReal (G z) * ∫⁻ x in Set.Ioi z, ENNReal.ofReal (phi x) := by
        have hpt : (fun x => ENNReal.ofReal (phi x * G z))
            = fun x => ENNReal.ofReal (phi x) * ENNReal.ofReal (G z) := by
          funext x
          exact ENNReal.ofReal_mul (p := phi x) (q := G z) (hp := hphi_nonneg x)
        rw [hpt, MeasureTheory.lintegral_mul_const]
        · exact mul_comm _ _
        · exact hpm.ennreal_ofReal
      have hmono : ∫⁻ x in Set.Ioi z, ENNReal.ofReal (phi x * G z)
          ≤ ∫⁻ x in Set.Ioi z, ENNReal.ofReal (phi x * G x) := by
        rw [← MeasureTheory.lintegral_indicator measurableSet_Ioi]
        rw [← MeasureTheory.lintegral_indicator measurableSet_Ioi]
        apply MeasureTheory.lintegral_mono
        intro x
        by_cases hx : x ∈ Set.Ioi z
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
          exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hG_mono' (le_of_lt hx)) (hphi_nonneg x))
        · simp [hx]
      rw [show ENNReal.ofReal ((1 - ∫ u in Set.Iic z, ProbabilityTheory.gaussianPDFReal 0 1 u) * G z)
            = ENNReal.ofReal (1 - P) * ENNReal.ofReal (G z) from by
          rw [← hP]
          exact ENNReal.ofReal_mul (p := 1 - P) (q := G z) (hp := hPpos.le)]
      calc ENNReal.ofReal (1 - P) * ENNReal.ofReal (G z)
          = ENNReal.ofReal (G z) * ENNReal.ofReal (1 - P) := mul_comm _ _
        _ = ENNReal.ofReal (G z) * ∫⁻ x in Set.Ioi z, ENNReal.ofReal (phi x) := by rw [hstep3]
        _ = ∫⁻ x in Set.Ioi z, ENNReal.ofReal (phi x * G z) := hfac.symm
        _ ≤ ∫⁻ x in Set.Ioi z, ENNReal.ofReal (phi x * G x) := hmono
    have helem : ∀ z : ℝ, max z 1 * Real.exp (-((max (z - b - aM) 0) ^ 2) / 2) ≤ b + aM + 1 := by
      have hA : 0 ≤ b + aM := by linarith
      have hexp_helper : ∀ w : ℝ, 0 < w → w * Real.exp (-(w ^ 2) / 2) ≤ 1 := by
        intro w hw
        have h1 : w ≤ Real.exp (w ^ 2 / 2) := by
          by_cases hw1 : w ≤ 1
          · calc w ≤ 1 := hw1
              _ ≤ Real.exp (w ^ 2 / 2) := by
                    rw [← Real.exp_zero]
                    exact Real.exp_le_exp.mpr (by positivity)
          · have hlog : Real.log w ≤ w - 1 := Real.log_le_sub_one_of_pos hw
            have h2 : w - 1 ≤ w ^ 2 / 2 := by nlinarith [sq_nonneg (w - 1)]
            have hlog2 : Real.log w ≤ w ^ 2 / 2 := le_trans hlog h2
            calc w = Real.exp (Real.log w) := (Real.exp_log hw).symm
              _ ≤ Real.exp (w ^ 2 / 2) := Real.exp_le_exp.mpr hlog2
        calc w * Real.exp (-(w ^ 2) / 2)
            ≤ Real.exp (w ^ 2 / 2) * Real.exp (-(w ^ 2) / 2) :=
              mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
          _ = Real.exp (w ^ 2 / 2 + -(w ^ 2) / 2) := (Real.exp_add _ _).symm
          _ = 1 := by rw [show w ^ 2 / 2 + -(w ^ 2) / 2 = 0 by ring, Real.exp_zero]
      intro z
      by_cases hzle : z ≤ b + aM
      · have hr : max (z - b - aM) 0 = 0 := by
          rw [max_eq_right]; linarith
        rw [hr]
        have hexp1 : Real.exp (-((0:ℝ) ^ 2) / 2) = 1 := by simp
        rw [hexp1, mul_one, max_le_iff]
        exact ⟨by linarith, by linarith⟩
      · have hzgt : b + aM < z := not_le.mp hzle
        have hmaxr : max (z - b - aM) 0 = z - b - aM := by
          rw [max_eq_left]; linarith
        rw [hmaxr]
        by_cases hz1 : z ≤ 1
        · rw [max_eq_right hz1, one_mul]
          have hexp_le1 : Real.exp (-((z - b - aM) ^ 2) / 2) ≤ 1 := by
            rw [← Real.exp_zero]
            exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (z - b - aM)])
          linarith
        · rw [max_eq_left (le_of_lt (not_le.mp hz1))]
          set w : ℝ := z - b - aM with hw
          have hwpos : 0 < w := by rw [hw]; linarith
          have hz_eq : z = (b + aM) + w := by rw [hw]; ring
          have hexp_le1 : Real.exp (-(w ^ 2) / 2) ≤ 1 := by
            rw [← Real.exp_zero]
            exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg w])
          have hwle := hexp_helper w hwpos
          have hAe : (b + aM) * Real.exp (-(w ^ 2) / 2) ≤ (b + aM) * 1 :=
            mul_le_mul_of_nonneg_left hexp_le1 hA
          rw [hz_eq]
          calc ((b + aM) + w) * Real.exp (-(w ^ 2) / 2)
              = (b + aM) * Real.exp (-(w ^ 2) / 2) + w * Real.exp (-(w ^ 2) / 2) := by ring
            _ ≤ (b + aM) + 1 := by linarith [hAe, hwle]
    intro z
    have h2max : (0:ℝ) ≤ 2 * max z 1 := by
      have := le_max_right z 1; linarith
    have hMillz : phi z ≤ (2 * max z 1) * (1 - ∫ u in Set.Iic z, ProbabilityTheory.gaussianPDFReal 0 1 u) := by
      have hpos : 0 < 1 - ∫ u in Set.Iic z, ProbabilityTheory.gaussianPDFReal 0 1 u := hMillPos z
      have hle : ProbabilityTheory.gaussianPDFReal 0 1 z / (1 - ∫ u in Set.Iic z, ProbabilityTheory.gaussianPDFReal 0 1 u) ≤ 2 * max z 1 := hMill z
      have h1 : ProbabilityTheory.gaussianPDFReal 0 1 z
          = (ProbabilityTheory.gaussianPDFReal 0 1 z / (1 - ∫ u in Set.Iic z, ProbabilityTheory.gaussianPDFReal 0 1 u))
            * (1 - ∫ u in Set.Iic z, ProbabilityTheory.gaussianPDFReal 0 1 u) := by
        rw [div_mul_cancel₀ _ hpos.ne']
      rw [hφeq z, h1]
      exact mul_le_mul_of_nonneg_right hle (le_of_lt hpos)
    have hinner_tail : (1 - ∫ u in Set.Iic z, ProbabilityTheory.gaussianPDFReal 0 1 u) * G z
        ≤ Real.exp (-((max (z - b - aM) 0) ^ 2) / 2) := by
      have h1 : ENNReal.ofReal ((1 - ∫ u in Set.Iic z, ProbabilityTheory.gaussianPDFReal 0 1 u) * G z)
          ≤ ENNReal.ofReal (Real.exp (-((max (z - b - aM) 0) ^ 2) / 2)) :=
        le_trans (hInner z) (le_trans (measure_mono (hsubAll z)) (hTail z))
      have hAnn : 0 ≤ (1 - ∫ u in Set.Iic z, ProbabilityTheory.gaussianPDFReal 0 1 u) * G z :=
        mul_nonneg (le_of_lt (hMillPos z)) (hG_nonneg' z)
      have h2 := ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le h1
      rwa [ENNReal.toReal_ofReal hAnn] at h2
    calc phi z * G z
        ≤ ((2 * max z 1) * (1 - ∫ u in Set.Iic z, ProbabilityTheory.gaussianPDFReal 0 1 u)) * G z :=
          mul_le_mul_of_nonneg_right hMillz (hG_nonneg' z)
      _ = (2 * max z 1) * ((1 - ∫ u in Set.Iic z, ProbabilityTheory.gaussianPDFReal 0 1 u) * G z) := by
          rw [mul_assoc]
      _ ≤ (2 * max z 1) * Real.exp (-((max (z - b - aM) 0) ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left hinner_tail h2max
      _ = 2 * (max z 1 * Real.exp (-((max (z - b - aM) 0) ^ 2) / 2)) := by ring
      _ ≤ 2 * (b + aM + 1) := mul_le_mul_of_nonneg_left (helem z) (by norm_num)
  have hvol : volume (Set.Icc (y - t) (y + t)) = ENNReal.ofReal (2 * t) := by
    rw [Real.volume_Icc]
    congr 1
    ring
  have hkey : μ {ω | |coordMax V ω - y| ≤ t}
      ≤ ENNReal.ofReal (2 * (b + aM + 1)) * ENNReal.ofReal (2 * t) := by
    have hset : {ω | |coordMax V ω - y| ≤ t}
        = (fun ω => coordMax V ω) ⁻¹' (Set.Icc (y - t) (y + t)) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Icc]
      rw [abs_le]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
      · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    rw [hset, ← MeasureTheory.Measure.map_apply hZmeas measurableSet_Icc]
    rw [hmap (Set.Icc (y - t) (y + t)) measurableSet_Icc]
    calc ∫⁻ x in Set.Icc (y - t) (y + t),
          ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2) *
            (∑ j : Fin q,
              Real.exp (nu j * x - nu j ^ 2 / 2) *
                (Statlib.Imported.gaussianVecMeasure
                  (fun k : {k : Fin q // k ≠ j} => nu k.1 + (x - nu j) * Sigma k.1 j)
                  (fun k l : {k : Fin q // k ≠ j} => Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j)
                  {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ x}).toReal))
        ≤ ∫⁻ x in Set.Icc (y - t) (y + t), ENNReal.ofReal (2 * (b + aM + 1)) := by
          apply MeasureTheory.lintegral_mono
          intro x
          exact ENNReal.ofReal_le_ofReal (hf_bound x)
      _ = ENNReal.ofReal (2 * (b + aM + 1)) * volume (Set.Icc (y - t) (y + t)) := by
          rw [MeasureTheory.lintegral_const]
          simp
      _ = ENNReal.ofReal (2 * (b + aM + 1)) * ENNReal.ofReal (2 * t) := by rw [hvol]
  have hmain : μ {ω | |coordMax V ω - y| ≤ t} ≤ ENNReal.ofReal (4 * t * (b + aM + 1)) := by
    calc μ {ω | |coordMax V ω - y| ≤ t}
        ≤ ENNReal.ofReal (2 * (b + aM + 1)) * ENNReal.ofReal (2 * t) := hkey
      _ = ENNReal.ofReal (2 * (b + aM + 1) * (2 * t)) := by
            rw [ENNReal.ofReal_mul (p := 2 * (b + aM + 1)) (q := 2 * t) (hp := by linarith [hb, haM_nonneg])]
      _ = ENNReal.ofReal (4 * t * (b + aM + 1)) := by congr 1; ring
  have hEq : (4:ℝ) * t * (b + aM + 1)
      = 4 * t * (b + (∫ ω, coordMax (fun ω' k => V ω' k - nu k) ω ∂μ) + 1) := by
    rw [haM, hY]
  rw [← hEq]
  exact hmain
  /- @proof-region region.target-node.session.d2ff6efc34d65858 end -/

end Statlib.Imported

