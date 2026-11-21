import CircleExactCardinality
import MixedCircleArithmetic

set_option maxHeartbeats 2000000

namespace QuorumAudit.MixedCircle
noncomputable section
open Finset Circle
open scoped BigOperators
variable {n : ℕ} [NeZero n]

def bottleneckFailures (r : ℕ) : Finset (ZMod n) := {0, (r : ZMod n)}
def longSide (r : ℕ) : Finset (ZMod n) := univ.filter (fun i => r < i.val)

theorem zero_mem_wrapping_arc (r : ℕ) (s : ZMod n) (h : n < s.val + r) :
    (0 : ZMod n) ∈ arc r s := by
  apply mem_image.mpr
  refine ⟨n - s.val, mem_range.mpr (by have := ZMod.val_lt s; omega), ?_⟩
  have he : s.val + (n - s.val) = n := by have := ZMod.val_lt s; omega
  have hc := congrArg (fun j : ℕ => (j : ZMod n)) he
  simpa using hc

theorem point_mem_linear_arc (r : ℕ) (s : ZMod n) (i : ℕ)
    (hsi : s.val ≤ i) (hir : i < s.val + r) : (i : ZMod n) ∈ arc r s := by
  apply mem_image.mpr
  refine ⟨i - s.val, mem_range.mpr (by omega), ?_⟩
  have he : s.val + (i - s.val) = i := by omega
  have hc := congrArg (fun j : ℕ => (j : ZMod n)) he
  simpa using hc

theorem live_read_on_long_side (r : ℕ) (s : ZMod n)
    (hlive : Disjoint (arc r s) (bottleneckFailures (n := n) r)) :
    arc r s ⊆ longSide (n := n) r := by
  by_cases hr : r = 0
  · subst r; simp [arc]
  have hrp : 0 < r := by omega
  have hnowrap : s.val + r ≤ n := by
    by_contra h
    exact disjoint_left.mp hlive (zero_mem_wrapping_arc r s (by omega)) (by simp [bottleneckFailures])
  have hs : r < s.val := by
    by_contra h
    have hspos : 0 < s.val := by
      by_contra hz
      have he : s = 0 := by
        apply ZMod.val_injective
        simpa using (show s.val = 0 by omega)
      have hm : s ∈ arc r s := mem_image.mpr ⟨0, mem_range.mpr hrp, by simp⟩
      exact disjoint_left.mp hlive (by simpa [he] using hm) (by simp [bottleneckFailures])
    exact disjoint_left.mp hlive (point_mem_linear_arc r s r (by omega) (by omega))
      (by simp [bottleneckFailures])
  intro i hi
  obtain ⟨j, hj, he⟩ := mem_image.mp hi
  have hjr := mem_range.mp hj
  have hbound : s.val + j < n := by omega
  have hv : i.val = s.val + j := by
    rw [← he]
    have heq : s + (j : ZMod n) = ((s.val + j : ℕ) : ZMod n) := by simp
    rw [heq, ZMod.val_natCast, Nat.mod_eq_of_lt hbound]
  simp [longSide, hv, hs.trans_le (Nat.le_add_right _ _)]

theorem longSide_card (r : ℕ) (hrn : r + 1 ≤ n) :
    (longSide (n := n) r).card = n - (r + 1) := by
  have he : longSide (n := n) r = (Ico (r + 1) n).image (fun i : ℕ => (i : ZMod n)) := by
    ext i
    constructor
    · intro hi
      have hh : r < i.val := (mem_filter.mp hi).2
      exact mem_image.mpr ⟨i.val, mem_Ico.mpr ⟨by omega, ZMod.val_lt i⟩, by simp⟩
    · rintro hi
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
      simp only [longSide, mem_filter, mem_univ, true_and]
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_Ico.mp hj).2]
      have := (mem_Ico.mp hj).1
      omega
  rw [he, card_image_of_injOn, Nat.card_Ico]
  intro a ha b hb hab
  exact cast_injective_below (mem_Ico.mp ha).2 (mem_Ico.mp hb).2 hab

theorem live_partition_read_bucket (r j : ℕ) (hr : 2 ≤ r) (hn : n + 1 = r * r)
    (hj : j ∈ Ico 1 r) (i : ZMod n)
    (hi : i ∈ arc r ((j * r : ℕ) : ZMod n))
    (hif : i ∉ bottleneckFailures (n := n) r) :
    i ∈ longSide (n := n) r ∧ i.val / r = j := by
  obtain ⟨t, ht, he⟩ := mem_image.mp hi
  have htr := mem_range.mp ht
  have hj0 := (mem_Ico.mp hj).1
  have hjr := (mem_Ico.mp hj).2
  have hsum : j * r + t ≤ n := by nlinarith
  have hlt : j * r + t < n := by
    by_contra h
    have hh : j * r + t = n := by omega
    have hz : i = 0 := by rw [← he, ← Nat.cast_add, hh]; simp
    exact hif (by simp [bottleneckFailures, hz])
  have hv : i.val = j * r + t := by
    rw [← he, ← Nat.cast_add, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
  have hnotr : i.val ≠ r := by
    intro hh
    have hiR : i = (r : ZMod n) := by
      calc i = (i.val : ZMod n) := by simp
           _ = (r : ZMod n) := by rw [hh]
    exact hif (by simp [bottleneckFailures, hiR])
  refine ⟨?_, ?_⟩
  · simp only [longSide, mem_filter, mem_univ, true_and]
    rw [hv] at hnotr ⊢
    have hprod : r ≤ j * r := by simpa using Nat.mul_le_mul_right r hj0
    omega
  · simp [hv, Nat.add_div (by omega : 0 < r), Nat.mod_eq_of_lt htr,
      Nat.div_eq_of_lt htr, Nat.mul_div_left _ (by omega : 0 < r), Nat.not_le.mpr htr]

theorem every_live_write_meets_side (r : ℕ) (hr : 5 ≤ r) (hn : n + 1 = r * r)
    (w : Finset (ZMod n)) (hlive : Disjoint w (bottleneckFailures (n := n) r))
    (hhit : ∀ s : ZMod n, (arc r s ∩ w).Nonempty) :
    r - 1 ≤ (longSide (n := n) r ∩ w).card := by
  have hsub : Ico 1 r ⊆ (longSide (n := n) r ∩ w).image (fun i => i.val / r) := by
    intro j hj
    obtain ⟨i, hi⟩ := hhit ((j * r : ℕ) : ZMod n)
    obtain ⟨hiR, hiW⟩ := mem_inter.mp hi
    have hif : i ∉ bottleneckFailures (n := n) r := fun hiF => disjoint_left.mp hlive hiW hiF
    obtain ⟨hiS, hbucket⟩ := live_partition_read_bucket r j (by omega) hn hj i hiR hif
    exact mem_image.mpr ⟨i, mem_inter.mpr ⟨hiS, hiW⟩, hbucket⟩
  have hc := (card_le_card hsub).trans card_image_le
  simpa using hc

theorem interval_read_family_lower_bound (r : ℕ) (hr : 5 ≤ r)
    (hn : n + 1 = r * r) (W : Finset (Finset (ZMod n)))
    (hsafe : ∀ q ∈ reads n r, ∀ w ∈ W, (q ∩ w).Nonempty)
    (read : Routing (reads n r) univ (bottleneckFailures (n := n) r))
    (write : Routing W univ (bottleneckFailures (n := n) r))
    (a L : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hL : ∀ i ∈ univ \ bottleneckFailures (n := n) r, combined read write a i ≤ L) :
    ((r : ℝ) - 1 + a) / den r ≤ L := by
  have hrn : r + 1 ≤ n := by nlinarith
  have hR : (r : ℝ) ≤ ∑ i ∈ longSide (n := n) r, incidence read.quorums read.p i := by
    apply intersection_mass_bound _ _ _ _ read.nonnegative read.normalized
    intro q hq
    obtain ⟨s, _, rfl⟩ := mem_image.mp (read.subset hq)
    have hlive : Disjoint (arc r s) (bottleneckFailures (n := n) r) := by
      exact disjoint_left.mpr (fun i hi hiF => (mem_sdiff.mp (read.live _ hq hi)).2 hiF)
    rw [inter_eq_right.mpr (live_read_on_long_side r s hlive), arc_card _ (by omega)]
  have hW : ((r : ℝ) - 1) ≤ ∑ i ∈ longSide (n := n) r, incidence write.quorums write.p i := by
    apply intersection_mass_bound _ _ _ _ write.nonnegative write.normalized
    intro w hw
    have hlive : Disjoint w (bottleneckFailures (n := n) r) := by
      exact disjoint_left.mpr (fun i hi hiF => (mem_sdiff.mp (write.live _ hw hi)).2 hiF)
    have hc := every_live_write_meets_side r hr hn w hlive (fun s =>
      hsafe _ (mem_image.mpr ⟨s, mem_univ _, rfl⟩) _ (write.subset hw))
    have hcR : ((r - 1 : ℕ) : ℝ) ≤ ((longSide (n := n) r ∩ w).card : ℝ) := by exact_mod_cast hc
    rw [Nat.cast_sub (by omega : 1 ≤ r)] at hcR
    norm_num at hcR
    linarith
  have hside : longSide (n := n) r ⊆ univ \ bottleneckFailures (n := n) r := by
    intro i hi
    have hh : r < i.val := (mem_filter.mp hi).2
    apply mem_sdiff.mpr
    refine ⟨mem_univ _, ?_⟩
    simp only [bottleneckFailures, mem_insert, mem_singleton]
    rintro (rfl | rfl)
    · simpa using hh
    · rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : r < n)] at hh
      omega
  have hsum := sum_le_sum (fun i hi => hL i (hside hi))
  simp only [combined, sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul] at hsum
  have hcard : ((longSide (n := n) r).card : ℝ) = den r := by
    rw [longSide_card r hrn, Nat.cast_sub hrn]
    have hnR : (n : ℝ) + 1 = (r : ℝ) * r := by exact_mod_cast hn
    push_cast
    unfold den
    nlinarith
  rw [hcard] at hsum
  have hd := den_pos r (by exact_mod_cast hr)
  apply (div_le_iff₀ hd).mpr
  have h1 := mul_le_mul_of_nonneg_left hR ha
  have h2 := mul_le_mul_of_nonneg_left hW (by linarith : 0 ≤ 1 - a)
  nlinarith

#print axioms interval_read_family_lower_bound
end
end QuorumAudit.MixedCircle
