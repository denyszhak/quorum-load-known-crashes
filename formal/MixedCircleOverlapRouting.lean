import MixedCircleOverlapGeometry
import MixedCircleRawAttainment

set_option maxHeartbeats 4000000

namespace QuorumAudit.MixedCircle
noncomputable section
open Finset Circle
open scoped BigOperators
variable {n : ℕ} [NeZero n]

theorem overlap_read_route (r a b δA δB d : ℕ) (hr : 5 ≤ r)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : a + b = r)
    (hδA : 1 ≤ δA ∧ δA ≤ 2) (hδB : 1 ≤ δB ∧ δB ≤ 2)
    (hA : 1 + (a * r - δA) = d) (hB : d + 1 + (b * r - δB) = n) :
    ∃ read : Routing (reads n r) univ {0, (d : ZMod n)},
      ∀ i, incidence read.quorums read.p i =
        (overlapMass r a b δA δB d i.val : ℝ) / (2 * (r - 2) * (r + 1) : ℕ) := by
  have hpa : 2 * r ≤ a * r := Nat.mul_le_mul_right r ha
  have hpb : 2 * r ≤ b * r := Nat.mul_le_mul_right r hb
  have hF : ({0, d} : Finset ℕ) ⊆ range n := by
    intro i hi
    simp only [mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl <;> exact mem_range.mpr (by omega)
  let A := pairedReadDistribution r a δA 1
  let B := pairedReadDistribution r b δB (d + 1)
  have hAv := pairedReadDistribution_valid (n := n) r a δA 1 (by omega) ha
    (by omega) hδA {0, d} (by omega) (by
      intro i hi; have := mem_Ico.mp hi; simp only [mem_insert, mem_singleton]; omega)
  have hBv := pairedReadDistribution_valid (n := n) r b δB (d + 1) (by omega) hb
    (by omega) hδB {0, d} (by omega) (by
      intro i hi; have := mem_Ico.mp hi; simp only [mem_insert, mem_singleton]; omega)
  have hroute := read_distribution_route r (appendReadDistribution A B) {0, d}
    hF (append_read_valid r {0, d} A B hAv hBv)
  obtain ⟨oldRead, hread⟩ := hroute
  have hcast : ({0, d} : Finset ℕ).image (fun i : ℕ => (i : ZMod n)) = {0, (d : ZMod n)} := by simp
  let read : Routing (reads n r) univ {0, (d : ZMod n)} := {
    quorums := oldRead.quorums
    subset := oldRead.subset
    live := by intro q hq; rw [← hcast]; exact oldRead.live q hq
    p := oldRead.p
    nonnegative := oldRead.nonnegative
    normalized := oldRead.normalized }
  refine ⟨read, ?_⟩
  intro i
  rw [hread, append_read_degree]
  simp only [A, B, pairedReadDistribution_degree]
  have hscale : (appendReadDistribution A B).scale = 2 * (r - 2) * (r + 1) := by
    change 2 * (a - 1) * (r + 1) + 2 * (b - 1) * (r + 1) = _
    have ha1 : a - 1 + 1 = a := by omega
    have hb1 : b - 1 + 1 = b := by omega
    have hr2 : r - 2 + 2 = r := by omega
    nlinarith
  rw [hscale]
  rfl

theorem overlap_attains (r a b δA δB d : ℕ) (hr : 5 ≤ r) (hn : n + 1 = r * r)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : a + b = r) (hle : a ≤ b)
    (hδA : 1 ≤ δA ∧ δA ≤ 2) (hδB : 1 ≤ δB ∧ δB ≤ 2)
    (hA : 1 + (a * r - δA) = d) (hB : d + 1 + (b * r - δB) = n) :
    ∃ read : Routing (reads n r) univ {0, (d : ZMod n)},
    ∃ write : Routing (mixedWrites n r) univ {0, (d : ZMod n)},
      ∀ i ∈ univ \ {0, (d : ZMod n)}, combined read write (1 / 2) i = cap r / 2 := by
  have hpa : 2 * r ≤ a * r := Nat.mul_le_mul_right r ha
  have hpb : 2 * r ≤ b * r := Nat.mul_le_mul_right r hb
  have hr1 : r - 1 + 1 = r := by omega
  have hr2 : r - 2 + 2 = r := by omega
  have hr5 : r - 5 + 5 = r := by omega
  have h2r1 : 2 * r - 1 + 1 = 2 * r := by omega
  have hμle : 2 * (r - 5) ≤ 2 * (r - 2) * (r + 1) := by nlinarith
  have hμsub := Nat.sub_add_cancel hμle
  have hlast := last_stride (n := n) r (by omega) hn
  have hshift : r - 2 + (r - 1) * r = n - 1 := by omega
  have hroom : r - 2 + (r - 1) * r < n := by omega
  have hd : d < n := by omega
  have hd0 : (d : ZMod n) ≠ 0 := by
    intro he
    have hv := congrArg ZMod.val he
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hd] at hv
    simp at hv
    omega
  have hF : ({0, (d : ZMod n)} : Finset (ZMod n)).card = 2 := by
    simp [Ne.symm hd0]
  let q := rotatedStride (n := n) r ((r - 2 : ℕ) : ZMod n)
  have hq := rotated_stride_ranked (n := n) r (by omega) hn ((r - 2 : ℕ) : ZMod n)
  have hq0 : (0 : ZMod n) ∉ q := by
    intro hi
    have hm := rotated_stride_mod (n := n) r (r - 2) 0 (by omega) hn (by omega) hroom
      (NeZero.pos n) (by simpa only [Nat.cast_zero] using hi)
    simp at hm
    omega
  have hqd : (d : ZMod n) ∉ q := by
    intro hi
    have hm := rotated_stride_mod (n := n) r (r - 2) d (by omega) hn (by omega) hroom hd hi
    have hc : δA = 1 ∨ δA = 2 := by omega
    rcases hc with hδ | hδ
    · have he : d = a * r := by omega
      simp only [he, Nat.mul_mod_left] at hm
      omega
    · have he : d = (a - 1) * r + (r - 1) := by
        have hp : (a - 1) * r + r = a * r := by
          calc _ = (a - 1 + 1) * r := by ring
               _ = _ := by rw [Nat.sub_add_cancel (by omega : 1 ≤ a)]
        omega
      rw [he, Nat.add_mod, Nat.mul_mod_left, zero_add,
        Nat.mod_eq_of_lt (by omega : r - 1 < r)] at hm
      simp only [Nat.mod_eq_of_lt (by omega : r - 1 < r)] at hm
      omega
  have hqlive : q ⊆ univ \ {0, (d : ZMod n)} := by
    intro i hi
    refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
    simp only [mem_insert, mem_singleton]
    rintro (rfl | rfl)
    · exact hq0 hi
    · exact hqd hi
  obtain ⟨read, hread⟩ := overlap_read_route (n := n) r a b δA δB d hr ha hb hab hδA hδB hA hB
  refine ⟨read, ?_⟩
  apply raw_attains r hr hn {0, (d : ZMod n)} hF read (overlapMass r a b δA δB d)
    (2 * (r - 2) * (r + 1)) (2 * (r - 5)) (2 * (2 * r - 1))
    (by exact Nat.mul_pos (Nat.mul_pos (by decide) (by omega)) (by omega))
    hread (twice_parameters r hr).1 (twice_parameters r hr).2 q hq hqlive
  · intro i _
    have hx : overlapMass r a b δA δB d i ≤ 2 * r + 2 := by
      unfold overlapMass
      by_cases hi : i ≤ d
      · rw [placed_zero_left r b δB (d + 1) i (by omega), add_zero]
        exact placed_point_bound r a δA 1 i (by omega) ha (by omega) hδA
      · rw [placed_zero_right r a δA 1 i (by omega) ha (by omega) (by omega), zero_add]
        exact placed_point_bound r b δB (d + 1) i (by omega) hb (by omega) hδB
    have hm := Nat.mul_le_mul_left ((r - 2) * (r + 1)) hx
    nlinarith
  · intro s
    have hcount := rotated_stride_count (n := n) r (by omega) hn ((r - 2 : ℕ) : ZMod n) s
    change (arc r s ∩ q).card = _ at hcount
    have hex : ((r - 2 : ℕ) : ZMod n) + ((r - 1) * r : ℕ) = ((n - 1 : ℕ) : ZMod n) := by
      rw [← Nat.cast_add, hshift]
    rw [hex] at hcount
    have hFc := cast_pair_count r d hd s
    by_cases he : s = ((n - 1 : ℕ) : ZMod n)
    · have hsv : s.val = n - 1 := by
        rw [he, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : n - 1 < n)]
      rw [hcount, if_pos he, hsv]
      have hw := overlap_exceptional_window n r a b δA δB d hr ha hb hab hle hδA hδB hA hB
      have hc := overlap_window_classification n r a b δA δB d hr ha hb hab hδA hδB hA hB
        (n - 1) (by omega)
      rw [hFc, hsv]
      rcases hc with ⟨hc, _⟩ | ⟨hc, _⟩ <;> rw [hc] <;> (try simp only [Nat.sub_zero]) <;> nlinarith
    · rw [hcount, if_neg he, hFc]
      have hc := overlap_window_classification n r a b δA δB d hr ha hb hab hδA hδB hA hB
        s.val (ZMod.val_lt s)
      rcases hc with ⟨hc, hw⟩ | ⟨hc, hw⟩ <;> rw [hc] <;> (try simp only [Nat.sub_zero]) <;> nlinarith

#print axioms overlap_read_route
#print axioms overlap_attains
end
end QuorumAudit.MixedCircle
