import IndexedRouting
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Periodic
import Mathlib.Data.Finset.Powerset

namespace QuorumAudit.Circle
noncomputable section
open Finset
open scoped BigOperators

variable {n h : ℕ} [NeZero n] [NeZero h]

def arc (r : ℕ) (s : ZMod n) : Finset (ZMod n) :=
  (range r).image (fun j : ℕ => s + (j : ZMod n))

def partialSum (w : ZMod n → ℕ) (l : ℕ) : ℕ :=
  ∑ j ∈ range l, w (j : ZMod n)

def colors (h P a : ℕ) : Finset (ZMod h) :=
  (range a).image (fun j => ((P + j : ℕ) : ZMod h))

def block (w : ZMod n → ℕ) (i : ZMod n) : Finset (ZMod h) :=
  colors h (partialSum w i.val) (w i)

def sample (w : ZMod n → ℕ) (t : ZMod h) : Finset (ZMod n) :=
  univ.filter (fun i => t ∈ block w i)

omit [NeZero n] in
theorem cast_injective_below {a b : ℕ} (ha : a < n) (hb : b < n)
    (hab : (a : ZMod n) = (b : ZMod n)) : a = b := by
  have := congrArg ZMod.val hab
  simpa [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this

omit [NeZero n] in
theorem arc_card (r : ℕ) (hr : r ≤ n) (s : ZMod n) : (arc r s).card = r := by
  unfold arc
  rw [card_image_of_injOn, card_range]
  intro a ha b hb hab
  exact cast_injective_below (lt_of_lt_of_le (mem_range.mp ha) hr)
    (lt_of_lt_of_le (mem_range.mp hb) hr) (add_left_cancel hab)

omit [NeZero h] in
theorem colors_card (P a : ℕ) (ha : a ≤ h) : (colors h P a).card = a := by
  unfold colors
  rw [card_image_of_injOn, card_range]
  intro x hx y hy hxy
  simp only [Nat.cast_add] at hxy
  exact cast_injective_below (lt_of_lt_of_le (mem_range.mp hx) ha)
    (lt_of_lt_of_le (mem_range.mp hy) ha) (add_left_cancel hxy)

omit [NeZero h] in
theorem colors_concat (P a b : ℕ) :
    colors h P (a + b) = colors h P a ∪ colors h (P + a) b := by
  ext t
  simp only [colors, mem_image, mem_range, mem_union]
  constructor
  · rintro ⟨j, hj, rfl⟩
    by_cases hja : j < a
    · exact Or.inl ⟨j, hja, rfl⟩
    · right
      refine ⟨j - a, by omega, ?_⟩
      congr 1
      omega
  · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
    · exact ⟨j, by omega, rfl⟩
    · exact ⟨a + j, by omega, by congr 1; omega⟩

theorem colors_full (P a : ℕ) (ha : h ≤ a) : colors h P a = univ := by
  apply eq_univ_of_forall
  intro t
  let j := (t - (P : ZMod h)).val
  have hj : j < h := ZMod.val_lt _
  apply mem_image.mpr
  refine ⟨j, mem_range.mpr (lt_of_lt_of_le hj ha), ?_⟩
  simp [j, Nat.cast_add]

omit [NeZero n] in
theorem partialSum_add (w : ZMod n → ℕ) (s r : ℕ) :
    partialSum w (s + r) = partialSum w s + ∑ j ∈ range r, w ((s + j : ℕ) : ZMod n) := by
  exact sum_range_add _ s r

omit [NeZero n] [NeZero h] in
theorem partialSum_periodic (w : ZMod n → ℕ) (hzero : (partialSum w n : ZMod h) = 0) :
    Function.Periodic (fun j => (partialSum w j : ZMod h)) n := by
  intro j
  change (partialSum w (j + n) : ZMod h) = (partialSum w j : ZMod h)
  rw [add_comm j n, partialSum_add, Nat.cast_add, hzero, zero_add]
  congr 1
  apply sum_congr rfl
  intro i hi
  simp [Nat.cast_add]

omit [NeZero n] [NeZero h] in
theorem block_lift (w : ZMod n → ℕ) (hzero : (partialSum w n : ZMod h) = 0) (j : ℕ) :
    block w (j : ZMod n) = colors h (partialSum w j) (w (j : ZMod n)) := by
  have hp := (partialSum_periodic w hzero).map_mod_nat j
  unfold block colors
  apply image_congr
  intro z hz
  simp only [Nat.cast_add, ZMod.val_natCast]
  rw [hp]

omit [NeZero n] [NeZero h] in
theorem window_colors (w : ZMod n → ℕ) (hzero : (partialSum w n : ZMod h) = 0)
    (s r : ℕ) :
    (range r).biUnion (fun j => block w ((s + j : ℕ) : ZMod n)) =
      colors h (partialSum w s) (∑ j ∈ range r, w ((s + j : ℕ) : ZMod n)) := by
  induction r with
  | zero => simp [colors]
  | succ r ih =>
    rw [range_add_one, biUnion_insert, ih, sum_insert notMem_range_self]
    rw [add_comm (w _), colors_concat, ← partialSum_add, block_lift w hzero]
    exact union_comm _ _

theorem sample_hits (w : ZMod n → ℕ) (hzero : (partialSum w n : ZMod h) = 0)
    (r : ℕ) (s : ZMod n) (t : ZMod h)
    (hmass : h ≤ ∑ j ∈ range r, w (s + (j : ZMod n))) :
    (arc r s ∩ sample w t).Nonempty := by
  have heq : (∑ j ∈ range r, w ((s.val + j : ℕ) : ZMod n)) =
      ∑ j ∈ range r, w (s + (j : ZMod n)) := by
    simp [Nat.cast_add]
  have ht : t ∈ (range r).biUnion (fun j => block w ((s.val + j : ℕ) : ZMod n)) := by
    rw [window_colors w hzero, heq, colors_full _ _ hmass]
    exact mem_univ _
  obtain ⟨j, hj, ht⟩ := mem_biUnion.mp ht
  refine ⟨s + (j : ZMod n), mem_inter.mpr ⟨mem_image.mpr ⟨j, hj, rfl⟩, ?_⟩⟩
  simpa [sample, Nat.cast_add] using ht

theorem sample_marginal (w : ZMod n → ℕ) (hw : ∀ i, w i ≤ h) (i : ZMod n) :
    (∑ t : ZMod h, if i ∈ sample w t then (1 / (h : ℝ)) else 0) = (w i : ℝ) / h := by
  have hc : (block (h := h) w i).card = w i := by simpa [block] using colors_card (partialSum w i.val) (w i) (hw i)
  simp only [sample, mem_filter, mem_univ, true_and]
  rw [← sum_filter]
  simp [hc, div_eq_mul_inv]

#print axioms sample_hits
#print axioms sample_marginal
end
end QuorumAudit.Circle
