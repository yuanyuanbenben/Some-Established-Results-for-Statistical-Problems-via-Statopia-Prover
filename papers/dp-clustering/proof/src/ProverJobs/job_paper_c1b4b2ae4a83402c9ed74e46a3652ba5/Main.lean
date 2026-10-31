import Statlib.StatFoundation.Convergence.AnalysisTools.ConvergenceModes
import ProverJobs.job_paper_c1b4b2ae4a83402c9ed74e46a3652ba5.Vocabulary
import ProverJobs.job_paper_c1b4b2ae4a83402c9ed74e46a3652ba5.ProvedNodes
import ProverJobs.job_paper_c1b4b2ae4a83402c9ed74e46a3652ba5.Base

open MeasureTheory Filter Topology
open scoped ENNReal
namespace Statlib.Imported

theorem paper_c1b4b2ae4a83402c9ed74e46a3652ba5
    {X Θ : Type*} [TopologicalSpace X] [MeasureSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) (hμ : μ = volume ∨ μ = Measure.count)
    (k : Θ → X → ℝ) (hK : ∀ θ, IsProbDensity μ (k θ))
    (s : ℕ) (hs : 1 ≤ s)
    (F : ℕ → ExactMixture Θ X μ k s)
    (f : X → ℝ) (hf : IsProbDensity μ f)
    (hconv : Statlib.StatFoundation.Convergence.WeakConvergence
      (fun i => probOfDensity μ (F i).f (F i).dens) (probOfDensity μ f hf)) :
    ∃ (s' : ℕ) (_ : 1 ≤ s') (_ : s' ≤ s) (F' : ℕ → ExactMixture Θ X μ k s'),
      Statlib.StatFoundation.Convergence.WeakConvergence
        (fun i => probOfDensity μ (F' i).f (F' i).dens) (probOfDensity μ f hf) ∧
      ∀ j : Fin s', 0 < liminf (fun i => (F' i).weights j) atTop
:= by
  /- @proof-region region.root.84d2d36d034e begin -/
  have main : ∀ (t : ℕ), 1 ≤ t →
      ∀ (W : ℕ → ExactMixture Θ X μ k t) (P : ProbabilityMeasure X),
        Statlib.StatFoundation.Convergence.WeakConvergence
          (fun i => probOfDensity μ (W i).f (W i).dens) P →
        ∃ s' : ℕ, 1 ≤ s' ∧ s' ≤ t ∧ ∃ G : ℕ → ExactMixture Θ X μ k s',
          Statlib.StatFoundation.Convergence.WeakConvergence
            (fun i => probOfDensity μ (G i).f (G i).dens) P ∧
          ∀ j : Fin s', 0 < liminf (fun i => (G i).weights j) atTop := by
    intro t0
    refine Nat.strong_induction_on t0 ?_
    intro m ih hm W P hWconv
    by_cases h2 : 1 < m
    · obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
      have hn1 : 1 ≤ n := by omega
      have h2n : 2 ≤ n + 1 := by omega
      by_cases hpos : ∀ j : Fin (n + 1), 0 < liminf (fun i => (W i).weights j) atTop
      · exact ⟨n + 1, by omega, le_rfl, W, hWconv, hpos⟩
      · push_neg at hpos
        obtain ⟨l, hl⟩ := hpos
        have hw_nonneg : ∀ i, 0 ≤ (W i).weights l := fun i => ((W i).weights_pos l).le
        have hw_bdd : ∃ C : ℝ, ∀ i, (W i).weights l ≤ C := by
          refine ⟨1, fun i => ?_⟩
          have h1le : (W i).weights l ≤ ∑ j, (W i).weights j :=
            Finset.single_le_sum (fun j _ => ((W i).weights_pos j).le) (Finset.mem_univ l)
          rwa [(W i).weights_sum] at h1le
        have h0liminf : 0 ≤ liminf (fun i => (W i).weights l) atTop := by
          have hbdd : BddAbove {a : ℝ | ∀ᶠ i in atTop, a ≤ (W i).weights l} := by
            obtain ⟨C, hC⟩ := hw_bdd
            refine ⟨C, ?_⟩
            intro a ha
            have hev : ∀ᶠ i in atTop, a ≤ (W i).weights l := ha
            obtain ⟨i, hi⟩ := hev.exists
            exact hi.trans (hC i)
          have hmem : (0 : ℝ) ∈ {a : ℝ | ∀ᶠ i in atTop, a ≤ (W i).weights l} :=
            Eventually.of_forall hw_nonneg
          have hcs : 0 ≤ sSup {a : ℝ | ∀ᶠ i in atTop, a ≤ (W i).weights l} :=
            le_csSup hbdd hmem
          simpa only [Filter.liminf] using hcs
        have hlim : liminf (fun i => (W i).weights l) atTop = 0 := le_antisymm hl h0liminf
        obtain ⟨ψ, hψmono, hψge, hψtend⟩ :=
          statopia_math_node_2189732141_d478625f (fun i => (W i).weights l) hw_nonneg hw_bdd hlim
        have hψT : Tendsto ψ atTop atTop := hψmono.tendsto_atTop
        have hWtend : Tendsto (fun i => probOfDensity μ (W i).f (W i).dens) atTop (nhds P) := by
          simpa [Statlib.StatFoundation.Convergence.WeakConvergence] using hWconv
        have hWψconv : Statlib.StatFoundation.Convergence.WeakConvergence
            (fun i => probOfDensity μ (W (ψ i)).f (W (ψ i)).dens) P := by
          have hcomp : Tendsto (fun i => probOfDensity μ (W (ψ i)).f (W (ψ i)).dens) atTop (nhds P) :=
            Filter.Tendsto.comp hWtend hψT
          simpa [Statlib.StatFoundation.Convergence.WeakConvergence] using hcomp
        have hσmono : StrictMono (fun r : Fin n => l.succAbove r) := by
          simpa using l.strictMono_succAbove
        have hσinj : Function.Injective (fun r : Fin n => l.succAbove r) := by
          simpa [Fin.coe_succAboveEmb] using l.succAboveEmb.injective
        have hσrange1 : Set.range (fun r : Fin n => l.succAbove r) = ({l} : Set (Fin (n + 1)))ᶜ := by
          simpa using l.range_succAbove
        have hσrange2 : Set.range (fun r : Fin n => l.succAbove r) = {j : Fin (n + 1) | j ≠ l} := by
          rw [hσrange1]
          ext j
          simp
        obtain ⟨G, _hGw, _hGp, hGf⟩ :=
          statopia_math_node_1032661153_b6ef2974 μ k hK (n + 1) h2n
            (fun i => W (ψ i)) l (fun r => l.succAbove r) hσinj hσmono hσrange2
        have hdel : Tendsto (fun i => (W (ψ i)).weights l) atTop (nhds 0) := hψtend
        have hGconv : Statlib.StatFoundation.Convergence.WeakConvergence
            (fun i => probOfDensity μ (G i).f (G i).dens) P :=
          statopia_math_node_3655512486_d9d5ae90 μ k hK (n + 1) h2n
            (fun i => W (ψ i)) P l (fun r => l.succAbove r) hσmono hσrange1 G hGf hWψconv hdel
        obtain ⟨s', hs'1, hs'le, G', hG'conv, hG'pos⟩ := ih n (by omega) hn1 G P hGconv
        exact ⟨s', hs'1, le_trans hs'le (by omega), G', hG'conv, hG'pos⟩
    · obtain rfl : m = 1 := by omega
      refine ⟨1, le_rfl, le_rfl, W, hWconv, ?_⟩
      intro j
      fin_cases j
      have hone : ∀ i, (W i).weights 0 = 1 := fun i => by
        simpa using (W i).weights_sum
      have hlim1 : liminf (fun i => (W i).weights 0) atTop = 1 := by
        have hfun : (fun i => (W i).weights 0) = fun _ => (1 : ℝ) := funext hone
        rw [hfun]
        exact tendsto_const_nhds.liminf_eq
      have hgoal : 0 < liminf (fun i => (W i).weights 0) atTop := by
        rw [hlim1]
        norm_num
      exact hgoal
  obtain ⟨s', hs'1, hs'le, G, hGconv, hGpos⟩ := main s hs F (probOfDensity μ f hf) hconv
  exact ⟨s', hs'1, hs'le, G, hGconv, hGpos⟩
  /- @proof-region region.root.84d2d36d034e end -/

end Statlib.Imported
