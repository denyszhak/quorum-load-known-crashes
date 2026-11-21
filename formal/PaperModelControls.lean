import PaperClaims
import MixedCircleControls

namespace QuorumAudit.Paper
noncomputable section
open Finset

theorem empty_phase_rejected {ι : Type*} [DecidableEq ι]
    (V F : Finset ι) (p : Finset ι → ℝ) : ¬ Distribution ∅ V F p := by
  intro hp
  have hh := hp.2
  simpa [liveQuorums] using hh

theorem zero_probability_rejected (A : Finset (Finset ℕ)) (V F : Finset ℕ) :
    ¬ Distribution A V F (fun _ => 0) := by
  intro hp
  have hh := hp.2
  simpa using hh

theorem zero_read_fraction_requires_live_reads :
    ¬ RoutesAt ({{0}} : Finset (Finset ℕ)) {{1}} {0, 1} {0} 0 1 := by
  rintro ⟨p, q, hp, hq, hload⟩
  have hh := hp.2
  have hl : liveQuorums ({{0}} : Finset (Finset ℕ)) {0, 1} {0} = ∅ := by decide +kernel
  rw [hl, sum_empty] at hh
  norm_num at hh

theorem wrong_phase_normalization_rejected :
    ¬ Distribution ({{0}} : Finset (Finset ℕ)) {0} ∅ (fun _ => 2) := by
  intro hp
  have hh := hp.2
  have hl : liveQuorums ({{0}} : Finset (Finset ℕ)) {0} ∅ = {{0}} := by decide +kernel
  rw [hl, sum_singleton] at hh
  norm_num at hh

theorem read_write_coefficients_and_peak :
    let R : Finset (Finset ℕ) := {{0}}
    let W : Finset (Finset ℕ) := {{0, 1}}
    let V : Finset ℕ := {0, 1}
    let p : Finset ℕ → ℝ := fun _ => 1
    Distribution R V ∅ p ∧ Distribution W V ∅ p ∧
    ((1 / 4 : ℝ) * contact R V ∅ p 0 + (1 - 1 / 4) * contact W V ∅ p 0 = 1) ∧
    ((1 / 4 : ℝ) * contact R V ∅ p 1 + (1 - 1 / 4) * contact W V ∅ p 1 = 3 / 4) ∧
    ¬ (∀ i ∈ V, (1 / 4 : ℝ) * contact R V ∅ p i + (1 - 1 / 4) * contact W V ∅ p i ≤ 7 / 8) := by
  have hR : liveQuorums ({{0}} : Finset (Finset ℕ)) {0, 1} ∅ = {{0}} := by decide +kernel
  have hW : liveQuorums ({{0, 1}} : Finset (Finset ℕ)) {0, 1} ∅ = {{0, 1}} := by decide +kernel
  dsimp only
  norm_num [Distribution, contact, hR, hW, filter_singleton]

theorem cyclic_below_optimum_rejected : ¬ Feasible (range 11) 2 (3 / 13) (1 / 3) := by
  rw [cyclic_exact_in_paper_model 3 (by decide) (3 / 13) (1 / 3) (by norm_num) (by norm_num)]
  norm_num

theorem balanced_below_optimum_rejected :
    ¬ FixedReadsFeasible (univ : Finset (ZMod 24)) 2 (Circle.reads 24 5) (1 / 2) (1 / 5) := by
  rw [balanced_fixed_reads_exact_in_paper_model 24 5 (by decide) (by decide) (1 / 5)]
  norm_num

#print axioms empty_phase_rejected
#print axioms zero_probability_rejected
#print axioms zero_read_fraction_requires_live_reads
#print axioms wrong_phase_normalization_rejected
#print axioms read_write_coefficients_and_peak
#print axioms cyclic_below_optimum_rejected
#print axioms balanced_below_optimum_rejected
#print axioms MixedCircle.surviving_reads_are_not_enough
end
end QuorumAudit.Paper
