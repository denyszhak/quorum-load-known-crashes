import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
Kernel-checked components of the access-load theorem.
These statements explicitly expose their premises. In particular, the
arbitrary-size certificate construction is NOT assumed to be formalized.
-/
namespace QuorumAudit

noncomputable section

def target (k a : ℝ) : ℝ := (3 + (k - 1) * a) / (3 * k)
def critical (k : ℝ) : ℝ := 3 / (k * k + k + 1)

/-- The small-read alternative cannot improve the claimed line in the interval. -/
theorem small_read_bound (k a : ℝ) (hk : 3 ≤ k)
    (ha : a ≤ critical k) : target k a ≤ (1 - a) / (k - 1) := by
  have hk0 : 0 < k := by linarith
  have hkm : 0 < k - 1 := by linarith
  have hD : 0 < k * k + k + 1 := by positivity
  have hreg : a * (k * k + k + 1) ≤ 3 := (le_div_iff₀ hD).mp ha
  unfold target
  apply (div_le_div_iff₀ (by positivity : 0 < 3 * k) hkm).mpr
  nlinarith [hreg]

/-- Arithmetic specialization of the universal dichotomy, for arbitrary real k. -/
theorem dichotomy_implies_bound (k a L : ℝ) (hk : 3 ≤ k)
    (ha : a ≤ critical k)
    (h : (1 - a) / (k - 1) ≤ L ∨ target k a ≤ L) : target k a ≤ L := by
  rcases h with h | h
  · exact le_trans (small_read_bound k a hk ha) h
  · exact h

/-- Interpolating phase masses gives exactly the target line at every node.
    c is the read multiplicity; U has degree 1 and C degree k+2-c. -/
theorem interpolated_node_load (k a c : ℝ) (hk : 3 ≤ k) :
    a * (c / 3) + (a * (k + 2 - c) / 3 + (1 - a / critical k) / k)
      = target k a := by
  have hk0 : k ≠ 0 := by linarith
  have hD : k * k + k + 1 ≠ 0 := ne_of_gt (by positivity)
  unfold target critical
  field_simp
  ring

theorem critical_less_one (k : ℝ) (hk : 3 ≤ k) : critical k < 1 := by
  have hD : 0 < k * k + k + 1 := by positivity
  unfold critical
  apply (div_lt_one hD).mpr
  nlinarith [sq_nonneg (k - 3)]

/-- Total write phase mass is 1-a when C has total (k-1)(k+2)
    and U has total k. This is a universal algebraic identity. -/
theorem write_phase_normalization (k a : ℝ) (hk : 3 ≤ k) :
    a * ((k - 1) * (k + 2)) / 3 + (1 - a / critical k) = 1 - a := by
  have hD : k * k + k + 1 ≠ 0 := ne_of_gt (by positivity)
  unfold critical
  field_simp
  ring

theorem phase_coefficients_nonnegative (k a : ℝ) (hk : 3 ≤ k)
    (ha : 0 ≤ a) (hareg : a ≤ critical k) :
    0 ≤ a / 3 ∧ 0 ≤ (1 - a / critical k) / k ∧ 0 < 1 - a := by
  have hcrit : 0 < critical k := by unfold critical; positivity
  have hfrac : a / critical k ≤ 1 := (div_le_one hcrit).mpr hareg
  have ha1 := lt_of_le_of_lt hareg (critical_less_one k hk)
  exact ⟨by positivity, div_nonneg (by linarith) (by linarith), by linarith⟩

theorem critical_in_voting_interval (k : ℝ) (hk : 3 ≤ k) :
    critical k ≤ 1 / (k + 1) := by
  have hD : 0 < k * k + k + 1 := by positivity
  unfold critical
  apply (div_le_div_iff₀ hD (by linarith : 0 < k + 1)).mpr
  nlinarith [sq_nonneg (k - 3)]

/-- Exact access-load gap, without a throughput claim. -/
theorem voting_gap (k a : ℝ) (hk : 3 ≤ k) :
    (a + 3 * (1 - a) / (3 * k)) - target k a =
      2 * (k - 1) * a / (3 * k) := by
  have hk0 : k ≠ 0 := by linarith
  unfold target
  field_simp
  ring

theorem voting_gap_positive (k a : ℝ) (hk : 3 ≤ k) (ha : 0 < a) :
    target k a < a + 3 * (1 - a) / (3 * k) := by
  have h := voting_gap k a hk
  have hp : 0 < 2 * (k - 1) * a / (3 * k) := by
    apply div_pos
    · have : 0 < k - 1 := by linarith
      positivity
    · linarith
  linarith

/-- Scalar-voting prefix inequality. The combinatorial prefix argument is a
    separate premise, rather than hidden in this arithmetic theorem. -/
theorem voting_prefix_bound (m r a q : ℝ)
    (hm : 0 < m) (hr : 0 < r) (hrm : r ≤ m)
    (ha : 0 ≤ a) (_hq : 0 ≤ q) (hreg : m * a ≤ q * (1 - a)) :
    a + q * (1 - a) / m ≤
      (a * max 0 (2 * r - m) + q * (1 - a)) / r := by
  by_cases h : 0 ≤ 2 * r - m
  · rw [max_eq_right h]
    apply (le_div_iff₀ hr).mpr
    have hid : (a + q * (1 - a) / m) * r * m =
        a * r * m + q * (1 - a) * r := by field_simp
    have hc : 0 ≤ (q * (1 - a) - m * a) * (m - r) :=
      mul_nonneg (by linarith) (by linarith)
    apply (mul_le_mul_iff_left₀ hm).mp
    nlinarith [hc, hid]
  · rw [max_eq_left (le_of_not_ge h)]
    apply (le_div_iff₀ hr).mpr
    have hqa : 0 ≤ q * (1 - a) := le_trans (mul_nonneg (le_of_lt hm) ha) hreg
    have hid : (a + q * (1 - a) / m) * r * m =
        a * r * m + q * (1 - a) * r := by field_simp
    have hc : 0 ≤ q * (1 - a) * (m - 2 * r) := mul_nonneg hqa (by linarith)
    have hc2 : 0 ≤ (q * (1 - a) - m * a) * r := mul_nonneg (by linarith) (le_of_lt hr)
    apply (mul_le_mul_iff_left₀ hm).mp
    nlinarith [hid, hc, hc2]

/-- Plain averaging, used by both combinatorial lower-bound branches. -/
theorem average_bound {ι : Type*} (s : Finset ι) (load : ι → ℝ)
    (L total : ℝ) (hload : ∀ i ∈ s, load i ≤ L)
    (htotal : total ≤ ∑ i ∈ s, load i) : total ≤ (s.card : ℝ) * L := by
  calc
    total ≤ ∑ i ∈ s, load i := htotal
    _ ≤ ∑ _i ∈ s, L := Finset.sum_le_sum hload
    _ = (s.card : ℝ) * L := by simp

#print axioms small_read_bound
#print axioms dichotomy_implies_bound
#print axioms interpolated_node_load
#print axioms write_phase_normalization
#print axioms phase_coefficients_nonnegative
#print axioms critical_in_voting_interval
#print axioms voting_gap_positive
#print axioms voting_prefix_bound
#print axioms average_bound
end
end QuorumAudit
