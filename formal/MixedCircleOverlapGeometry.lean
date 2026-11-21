import MixedCircleOverlapProfiles

set_option maxHeartbeats 3000000

namespace QuorumAudit.MixedCircle
open Finset
open scoped BigOperators

def overlapMass (r a b δA δB d i : ℕ) : ℕ :=
  placedMass r a δA 1 i + placedMass r b δB (d + 1) i

theorem overlap_lineA (r a b δA δB d s ℓ : ℕ)
    (hs : 1 ≤ s) (hroom : s + ℓ ≤ d) :
    lineSum (overlapMass r a b δA δB d) s ℓ =
      lineSum (pairedMass r a δA) (s - 1) ℓ := by
  have he : lineSum (overlapMass r a b δA δB d) s ℓ =
      lineSum (placedMass r a δA 1) s ℓ + lineSum (placedMass r b δB (d + 1)) s ℓ := by
    simp [lineSum, overlapMass, sum_add_distrib]
  rw [he, placed_line_before r b δB (d + 1) s ℓ (by omega), add_zero]
  rw [show s = 1 + (s - 1) by omega, placed_line]
  congr 1 <;> omega

theorem overlap_lineB (r a b δA δB d s ℓ : ℕ) (hr : 5 ≤ r)
    (ha : 2 ≤ a) (hδA : δA ≤ 2) (hA : 1 + (a * r - δA) = d) (hs : d + 1 ≤ s) :
    lineSum (overlapMass r a b δA δB d) s ℓ =
      lineSum (pairedMass r b δB) (s - (d + 1)) ℓ := by
  have he : lineSum (overlapMass r a b δA δB d) s ℓ =
      lineSum (placedMass r a δA 1) s ℓ + lineSum (placedMass r b δB (d + 1)) s ℓ := by
    simp [lineSum, overlapMass, sum_add_distrib]
  rw [he, placed_line_after r a δA 1 s ℓ (by omega) ha (by omega) (by omega), zero_add]
  rw [show s = (d + 1) + (s - (d + 1)) by omega, placed_line]
  congr 1 <;> omega

theorem overlap_window_classification (n r a b δA δB d : ℕ) (hr : 5 ≤ r)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : a + b = r)
    (hδA : 1 ≤ δA ∧ δA ≤ 2) (hδB : 1 ≤ δB ∧ δB ≤ 2)
    (hA : 1 + (a * r - δA) = d) (hB : d + 1 + (b * r - δB) = n)
    (s : ℕ) (hs : s < n) :
    ((natArc n r s ∩ {0, d}).card = 0 ∧
      cyclicSum n (overlapMass r a b δA δB d) s r ≤ 2 * r * r + 4) ∨
    ((natArc n r s ∩ {0, d}).card = 1 ∧
      cyclicSum n (overlapMass r a b δA δB d) s r ≤ 2 * ((r - 1) ^ 2 + 2)) := by
  have hpa : 2 * r ≤ a * r := Nat.mul_le_mul_right r ha
  have hpb : 2 * r ≤ b * r := Nat.mul_le_mul_right r hb
  have hx0 : overlapMass r a b δA δB d 0 = 0 := by
    rw [overlapMass, placed_zero_left r a δA 1 0 (by omega),
      placed_zero_left r b δB (d + 1) 0 (by omega)]
  have hxd : overlapMass r a b δA δB d d = 0 := by
    rw [overlapMass, placed_zero_right r a δA 1 d (by omega) ha (by omega) (by omega),
      placed_zero_left r b δB (d + 1) d (by omega)]
  apply far_windows_bound n r d _ _ _ (by omega) (by omega) (by omega) hx0 hxd
  · intro u hu hur
    rw [overlap_lineA r a b δA δB d u r hu hur]
    have hw := paired_window r a δA (u - 1) (by omega) ha (by omega) hδA (by omega)
    exact hw.trans (by omega)
  · intro u hu hur
    rw [overlap_lineB r a b δA δB d u r hr ha hδA.2 hA hu]
    have hw := paired_window r b δB (u - (d + 1)) (by omega) hb (by omega) hδB (by omega)
    exact hw.trans (by omega)
  · intro ℓ hℓ
    rw [overlap_lineB r a b δA δB d (n - ℓ) ℓ hr ha hδA.2 hA (by omega),
      overlap_lineA r a b δA δB d 1 (r - 1 - ℓ) (by omega) (by omega)]
    have he : n - ℓ - (d + 1) = b * r - δB - ℓ := by omega
    rw [he, paired_suffix_eq_prefix r b δB ℓ (by omega) hb (by omega) hδB (by omega)]
    simpa [Nat.sub_self, add_comm] using
      paired_cross_bound r b a δB δA ℓ hr hb ha (by omega) hδB hδA hℓ
  · intro ℓ hℓ
    rw [overlap_lineA r a b δA δB d (d - ℓ) ℓ (by omega) (by omega),
      overlap_lineB r a b δA δB d (d + 1) (r - 1 - ℓ) hr ha hδA.2 hA le_rfl]
    have he : d - ℓ - 1 = a * r - δA - ℓ := by omega
    rw [he, paired_suffix_eq_prefix r a δA ℓ (by omega) ha (by omega) hδA (by omega)]
    simpa using paired_cross_bound r a b δA δB ℓ hr ha hb hab hδA hδB hℓ
  · exact hs

theorem overlap_exceptional_window (n r a b δA δB d : ℕ) (hr : 5 ≤ r)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : a + b = r) (hle : a ≤ b)
    (hδA : 1 ≤ δA ∧ δA ≤ 2) (hδB : 1 ≤ δB ∧ δB ≤ 2)
    (hA : 1 + (a * r - δA) = d) (hB : d + 1 + (b * r - δB) = n) :
    cyclicSum n (overlapMass r a b δA δB d) (n - 1) r ≤
      2 * ((r - 2) * (r - 1) + 6) := by
  have hpa : 2 * r ≤ a * r := Nat.mul_le_mul_right r ha
  have hpb : 2 * r ≤ b * r := Nat.mul_le_mul_right r hb
  have hx0 : overlapMass r a b δA δB d 0 = 0 := by
    rw [overlapMass, placed_zero_left r a δA 1 0 (by omega),
      placed_zero_left r b δB (d + 1) 0 (by omega)]
  rw [cyclicSum_wrap n _ (n - 1) r (by omega) (by omega) (by omega)]
  have he1 : n - (n - 1) = 1 := by omega
  rw [he1, lineSum_split_zero _ 0 (r - 1) 0 (by omega) (by omega) hx0]
  simp only [Nat.sub_zero, lineSum, range_zero, sum_empty, zero_add]
  change lineSum (overlapMass r a b δA δB d) (n - 1) 1 +
    lineSum (overlapMass r a b δA δB d) 1 (r - 1 - 1) ≤ _
  rw [overlap_lineB r a b δA δB d (n - 1) 1 hr ha hδA.2 hA (by omega),
    overlap_lineA r a b δA δB d 1 (r - 1 - 1) (by omega) (by omega)]
  have he2 : n - 1 - (d + 1) = b * r - δB - 1 := by omega
  rw [he2, paired_suffix_eq_prefix r b δB 1 (by omega) hb (by omega) hδB (by omega)]
  have he3 : r - 1 - 1 = r - 2 := by omega
  rw [he3]
  simpa [add_comm] using paired_exceptional_bound r a b δA δB hr ha hb hab hle hδA hδB

#print axioms overlap_window_classification
#print axioms overlap_exceptional_window
end QuorumAudit.MixedCircle
