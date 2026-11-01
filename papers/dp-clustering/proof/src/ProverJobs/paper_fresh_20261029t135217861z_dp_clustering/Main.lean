import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.Vocabulary
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProvedNodes
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.Base

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
namespace Statlib.Imported

theorem Theorem_1_th_ConsBounded
    (g q0 : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hg_meas : Measurable g) (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_density : ∫⁻ x, ENNReal.ofReal (g x) ∂volume = 1)
    (hq0_meas : Measurable q0) (hq0_nonneg : ∀ x, 0 ≤ q0 x)
    (hq0_density : ∫⁻ x, ENNReal.ofReal (q0 x) ∂volume = 1)
    (hT1 : ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧ ∀ x ∈ Set.Icc (-c) c, m ≤ g x ∧ g x ≤ M)
    
    
    (hg_support : ∀ x : ℝ, x ∉ Set.Icc (-c) c → g x = 0)
    (hT2 : DifferentiableOn ℝ g (Set.Ioo (-c) c) ∧
      ∃ Rd : ℝ, 0 < Rd ∧ ∀ x ∈ Set.Ioo (-c) c, |deriv g x / g x| ≤ Rd)
    (hB3 : ∃ B : ℝ, ∀ x, q0 x ≤ B) :
    ( 
     
     
     
     
     
     ∀ (t : ℕ) (P : Measure ℝ) (p : Fin t → ℝ) (Rm : Fin t → Measure ℝ) (θstar : Fin t → ℝ),
        IsDataConfig g q0 c t P p Rm θstar →
        ∃ ρ0 : ℝ, 0 < ρ0 ∧
          ∀ (π : Measure ℝ) (πdens : ℝ → ℝ),
            IsProbabilityMeasure π →
            Measurable πdens →
            
            π = volume.withDensity (fun α => ENNReal.ofReal (πdens α)) →
            (∀ᵐ α ∂π, 0 < α) →
            
            A2Cond πdens →
            
            (∃ ρ : ℝ, ρ0 ≤ ρ ∧ A3AtRate π ρ) →
            TendstoInMeasure (iidLaw P)
              (fun (n : ℕ) (ω : ℕ → ℝ) => postProb g q0 π n t (fun i : Fin n => ω (i : ℕ)))
              atTop (fun _ => (1 : ℝ))) ∧
    ( 
     ∀ (αstar : ℝ), 0 < αstar →
        ∀ (t : ℕ) (P : Measure ℝ) (p : Fin t → ℝ) (Rm : Fin t → Measure ℝ)
          (θstar : Fin t → ℝ),
          IsDataConfig g q0 c t P p Rm θstar →
          ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
            iidLaw P {ω : ℕ → ℝ |
                1 - η <
                  postProb g q0 (Measure.dirac αstar) n t (fun i : Fin n => ω (i : ℕ))} ≤
              ENNReal.ofReal ε)
:= by
  /- @proof-region region.root.09d6b1abc2b2 begin -/ exact DPCompletedProof.OfflineDPSourceMain.source_theorem_1 g q0 c hc hg_meas hg_nonneg hg_density hq0_meas hq0_nonneg hq0_density hT1 hg_support hT2 hB3 /- @proof-region region.root.09d6b1abc2b2 end -/

end Statlib.Imported

-- Paper root revision 787709b0-1f88-4978-818f-0570d68d8654
