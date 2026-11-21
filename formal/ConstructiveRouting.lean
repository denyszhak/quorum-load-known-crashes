import IndexedRouting
import Mathlib.Algebra.BigOperators.Field

namespace QuorumAudit
noncomputable section
open scoped BigOperators
open Finset
variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

def readMultiplicity (Q : Nat → Finset ι) (i : ι) : ℝ :=
  ∑ j ∈ range 3, if i ∈ Q j then 1 else 0

def writeProbability (k a : ℝ) (C U : κ → ℝ) (j : κ) : ℝ :=
  ((a / 3) * C j + ((1 - a / critical k) / k) * U j) / (1 - a)

theorem writeProbability_normalized (I : Finset κ) (C U : κ → ℝ) (k a : ℝ)
    (hk : 3 ≤ k) (ha : a < 1)
    (hC : ∑ j ∈ I, C j = (k - 1) * (k + 2))
    (hU : ∑ j ∈ I, U j = k) :
    ∑ j ∈ I, writeProbability k a C U j = 1 := by
  unfold writeProbability
  rw [← sum_div, sum_add_distrib, ← mul_sum, ← mul_sum, hC, hU]
  have hkn : k ≠ 0 := by linarith
  have han : 1 - a ≠ 0 := by linarith
  have hm : (a / 3) * ((k - 1) * (k + 2)) + ((1 - a / critical k) / k) * k =
      1 - a := by
    rw [div_mul_cancel₀ _ hkn]
    convert write_phase_normalization k a hk using 1 <;> ring
  rw [hm, div_self han]

theorem readProbability_incidence (Q : Nat → Finset ι) (i : ι) :
    (∑ j ∈ range 3, if i ∈ Q j then (1 / 3 : ℝ) else 0) =
      readMultiplicity Q i / 3 := by
  unfold readMultiplicity
  rw [sum_div]
  apply sum_congr rfl
  intro j hj
  split_ifs <;> simp

theorem writeProbability_incidence (I : Finset κ) (Q : κ → Finset ι)
    (C U : κ → ℝ) (k a : ℝ) (i : ι) :
    (∑ j ∈ I, if i ∈ Q j then writeProbability k a C U j else 0) =
      ((a / 3) * (∑ j ∈ I, if i ∈ Q j then C j else 0) +
       ((1 - a / critical k) / k) * (∑ j ∈ I, if i ∈ Q j then U j else 0)) / (1 - a) := by
  unfold writeProbability
  calc
    (∑ j ∈ I, if i ∈ Q j then
        ((a / 3) * C j + ((1 - a / critical k) / k) * U j) / (1 - a) else 0) =
      ∑ j ∈ I, ((a / 3) * (if i ∈ Q j then C j else 0) +
        ((1 - a / critical k) / k) * (if i ∈ Q j then U j else 0)) / (1 - a) := by
      apply sum_congr rfl
      intro j hj
      split_ifs <;> simp
    _ = _ := by rw [← sum_div, sum_add_distrib, ← mul_sum, ← mul_sum]

theorem routing_incidence_outside {family : Finset (Finset ι)} {U F : Finset ι}
    (r : Routing family U F) (i : ι) (hi : i ∉ U \ F) :
    incidence r.quorums r.p i = 0 := by
  unfold incidence
  apply sum_eq_zero
  intro q hq
  have hnot : i ∉ q := fun h => hi (r.live q hq h)
  exact ite_eq_right hnot

/-- Finite semantic witnesses yield actual normalized Routing objects and
    the target load. Repeated quorum choices are merged rather than assumed
    distinct. This theorem still requires the geometric witness premises. -/
theorem upper_routing_from_witnesses
    (R W : Finset (Finset ι)) (V F : Finset ι)
    (Qread : Nat → Finset ι) (I : Finset κ) (Qwrite : κ → Finset ι)
    (C U : κ → ℝ) (k a : ℝ) (hk : 3 ≤ k) (ha : 0 ≤ a) (hareg : a ≤ critical k)
    (hrFamily : ∀ j ∈ range 3, Qread j ∈ R)
    (hrLive : ∀ j ∈ range 3, Qread j ⊆ V \ F)
    (hwFamily : ∀ j ∈ I, Qwrite j ∈ W)
    (hwLive : ∀ j ∈ I, Qwrite j ⊆ V \ F)
    (hCpos : ∀ j ∈ I, 0 ≤ C j) (hUpos : ∀ j ∈ I, 0 ≤ U j)
    (hCmass : ∑ j ∈ I, C j = (k - 1) * (k + 2))
    (hUmass : ∑ j ∈ I, U j = k)
    (hCdeg : ∀ i ∈ V \ F, (∑ j ∈ I, if i ∈ Qwrite j then C j else 0) =
      k + 2 - readMultiplicity Qread i)
    (hUdeg : ∀ i ∈ V \ F, (∑ j ∈ I, if i ∈ Qwrite j then U j else 0) = 1) :
    ∃ r : Routing R V F, ∃ w : Routing W V F,
      ∀ i ∈ V, combined r w a i ≤ target k a := by
  obtain ⟨ha3, hcoef, ha1⟩ := phase_coefficients_nonnegative k a hk ha hareg
  have han : a < 1 := by linarith
  let r : Routing R V F := routing_from_indexed (range 3) Qread (fun _ => (1 / 3 : ℝ)) R V F
    hrFamily hrLive (by intros; positivity) (by norm_num)
  have hwp : ∀ j ∈ I, 0 ≤ writeProbability k a C U j := by
    intro j hj
    exact div_nonneg (add_nonneg (mul_nonneg ha3 (hCpos j hj))
      (mul_nonneg hcoef (hUpos j hj))) (le_of_lt ha1)
  let w := routing_from_indexed I Qwrite (writeProbability k a C U) W V F
    hwFamily hwLive hwp (writeProbability_normalized I C U k a hk han hCmass hUmass)
  refine ⟨r, w, ?_⟩
  intro i hi
  by_cases hlive : i ∈ V \ F
  · have hrinc : incidence r.quorums r.p i = readMultiplicity Qread i / 3 := by
      change incidence ((range 3).image Qread)
        (mergedProbability (range 3) Qread (fun _ => (1 / 3 : ℝ))) i = _
      rw [merged_incidence, readProbability_incidence]
    have hwinc : incidence w.quorums w.p i =
        ((a / 3) * (k + 2 - readMultiplicity Qread i) +
          ((1 - a / critical k) / k)) / (1 - a) := by
      change incidence (I.image Qwrite) (mergedProbability I Qwrite (writeProbability k a C U)) i = _
      rw [merged_incidence, writeProbability_incidence, hCdeg i hlive, hUdeg i hlive, mul_one]
    unfold combined
    rw [hrinc, hwinc, mul_div_cancel₀ _ (ne_of_gt ha1)]
    have hload := interpolated_node_load k a (readMultiplicity Qread i) hk
    have heq : a * (readMultiplicity Qread i / 3) +
        ((a / 3) * (k + 2 - readMultiplicity Qread i) + (1 - a / critical k) / k) =
        target k a := by
      convert hload using 1 <;> ring
    exact le_of_eq heq
  · unfold combined
    rw [routing_incidence_outside r i hlive, routing_incidence_outside w i hlive]
    have hk0 : 0 ≤ k := by linarith
    have hkm : 0 ≤ k - 1 := by linarith
    have ht : 0 ≤ target k a := by unfold target; positivity
    simpa using ht

#print axioms upper_routing_from_witnesses
end
end QuorumAudit
