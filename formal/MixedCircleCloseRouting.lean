import MixedCircleCloseGeometry
import MixedCircleRawAttainment

set_option maxHeartbeats 3000000

namespace QuorumAudit.MixedCircle
noncomputable section
open Finset Circle
open scoped BigOperators
variable {n : ℕ} [NeZero n]

theorem close_attains (r a d : ℕ) (hr : 5 ≤ r) (hn : n + 1 = r * r)
    (hd : 1 ≤ d ∧ d ≤ r) (ha0 : 2 * a ≤ r - d) (ha1 : r - d ≤ 2 * a + 1) :
    ∃ read : Routing (reads n r) univ {(a : ZMod n), ((a + d : ℕ) : ZMod n)},
    ∃ write : Routing (mixedWrites n r) univ {(a : ZMod n), ((a + d : ℕ) : ZMod n)},
      ∀ i ∈ univ \ {(a : ZMod n), ((a + d : ℕ) : ZMod n)},
        combined read write (1 / 2) i = cap r / 2 := by
  have hlast := last_stride (n := n) r (by omega) hn
  have hlarge : 2 * r < n := by nlinarith
  have had : a + d ≤ r := by omega
  have hL : r + 1 + ((r - 1) * r - 2) = n := by omega
  let w := if d ≤ r - 2 then 0 else 1
  have hw : w ≤ 1 := by dsimp [w]; split_ifs <;> omega
  have hroom : w + (r - 1) * r < n := by omega
  have hFNat : ({a, a + d} : Finset ℕ) ⊆ range n := by
    intro i hi
    simp only [mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl <;> exact mem_range.mpr (by omega)
  have hv := pairedReadDistribution_valid (n := n) r (r - 1) 2 (r + 1) (by omega)
    (by omega) (by omega) (by omega) {a, a + d} (by omega) (by
      intro i hi; have := mem_Ico.mp hi; simp only [mem_insert, mem_singleton]; omega)
  have hroute := read_distribution_route r (pairedReadDistribution r (r - 1) 2 (r + 1))
    {a, a + d} hFNat hv
  obtain ⟨oldRead, holdRead⟩ := hroute
  have hcast : ({a, a + d} : Finset ℕ).image (fun i : ℕ => (i : ZMod n)) =
      {(a : ZMod n), ((a + d : ℕ) : ZMod n)} := by simp
  let read : Routing (reads n r) univ {(a : ZMod n), ((a + d : ℕ) : ZMod n)} := {
    quorums := oldRead.quorums
    subset := oldRead.subset
    live := by intro q hq; rw [← hcast]; exact oldRead.live q hq
    p := oldRead.p
    nonnegative := oldRead.nonnegative
    normalized := oldRead.normalized }
  have hread : ∀ i : ZMod n, incidence read.quorums read.p i =
      (closeMass r i.val : ℝ) / (2 * (r - 2) * (r + 1) : ℕ) := by
    intro i
    change incidence oldRead.quorums oldRead.p i = _
    rw [holdRead, pairedReadDistribution_degree]
    change (closeMass r i.val : ℝ) / (2 * (r - 1 - 1) * (r + 1) : ℕ) = _
    rw [show r - 1 - 1 = r - 2 by omega]
  have hne : (a : ZMod n) ≠ ((a + d : ℕ) : ZMod n) := by
    intro he
    have hv := cast_injective_below (by omega : a < n) (by omega : a + d < n) he
    omega
  have hF : ({(a : ZMod n), ((a + d : ℕ) : ZMod n)} : Finset (ZMod n)).card = 2 := by
    rw [card_insert_of_notMem (by simpa only [mem_singleton] using hne), card_singleton]
  let q := rotatedStride (n := n) r (w : ZMod n)
  have hqlive : q ⊆ univ \ {(a : ZMod n), ((a + d : ℕ) : ZMod n)} := by
    intro i hi
    refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
    simp only [mem_insert, mem_singleton]
    rintro (rfl | rfl)
    · have hm := rotated_stride_mod (n := n) r w a (by omega) hn (by omega) hroom (by omega) hi
      rw [Nat.mod_eq_of_lt (by omega : a < r)] at hm
      dsimp [w] at hm
      split_ifs at hm <;> omega
    · have hm := rotated_stride_mod (n := n) r w (a + d) (by omega) hn (by omega) hroom (by omega) hi
      dsimp [w] at hm
      by_cases hsmall : d ≤ r - 2
      · rw [if_pos hsmall, Nat.mod_eq_of_lt (by omega : a + d < r)] at hm
        omega
      · rw [if_neg hsmall] at hm
        have ha : a = 0 := by omega
        have hdc : d = r - 1 ∨ d = r := by omega
        rcases hdc with hdc | hdc
        · rw [ha, zero_add, hdc, Nat.mod_eq_of_lt (by omega : r - 1 < r)] at hm
          omega
        · rw [ha, zero_add, hdc, Nat.mod_self] at hm
          omega
  refine ⟨read, ?_⟩
  apply raw_attains r hr hn _ hF read (closeMass r) (2 * (r - 2) * (r + 1))
    (2 * (r - 5)) (2 * (2 * r - 1))
    (by exact Nat.mul_pos (Nat.mul_pos (by decide) (by omega)) (by omega)) hread
    (twice_parameters r hr).1 (twice_parameters r hr).2 q
    (rotated_stride_ranked r (by omega) hn (w : ZMod n)) hqlive
  · intro i _
    have hx := placed_point_bound r (r - 1) 2 (r + 1) i (by omega) (by omega) (by omega) (by omega)
    have hm := Nat.mul_le_mul_left ((r - 2) * (r + 1)) hx
    change (r - 2) * (r + 1) * closeMass r i ≤ _
    change closeMass r i ≤ 2 * r + 2 at hx
    change (r - 2) * (r + 1) * closeMass r i ≤ (r - 2) * (r + 1) * (2 * r + 2) at hm
    exact hm.trans_eq (by ring)
  · intro s
    have hA : natArc n r s.val ⊆ range n := by
      intro i hi
      obtain ⟨j, _, rfl⟩ := mem_image.mp hi
      exact mem_range.mpr (Nat.mod_lt _ (NeZero.pos n))
    have heCast := cast_intersection (natArc n r s.val) {a, a + d} hA hFNat
    rw [cast_natArc, ZMod.natCast_zmod_val] at heCast
    simp only [image_insert, image_singleton] at heCast
    have hFc : (arc r s ∩ {(a : ZMod n), ((a + d : ℕ) : ZMod n)}).card =
        (natArc n r s.val ∩ {a, a + d}).card := by
      rw [← heCast]
      apply card_image_of_injOn
      intro i hi j hj hij
      exact cast_injective_below (mem_range.mp (hA (mem_inter.mp hi).1))
        (mem_range.mp (hA (mem_inter.mp hj).1)) hij
    have hcount := rotated_stride_count (n := n) r (by omega) hn (w : ZMod n) s
    have hex : (w : ZMod n) + (((r - 1) * r : ℕ) : ZMod n) =
        ((w + (r - 1) * r : ℕ) : ZMod n) := by simp
    rw [hex] at hcount
    have heiff : s = ((w + (r - 1) * r : ℕ) : ZMod n) ↔ s.val = w + (r - 1) * r := by
      constructor
      · intro he; rw [he, ZMod.val_natCast, Nat.mod_eq_of_lt hroom]
      · intro he; rw [← he]; exact (ZMod.natCast_zmod_val s).symm
    simp only [heiff] at hcount
    change (arc r s ∩ q).card = _ at hcount
    rw [hcount, hFc]
    have hwEq : w + (r - 1) * r = (r - 1) * r + (if d ≤ r - 2 then 0 else 1) := by
      dsimp [w]; omega
    rw [hwEq]
    exact close_raw_window n r a d s.val hr hn hd ha0 ha1 (ZMod.val_lt s)

#print axioms close_attains
end
end QuorumAudit.MixedCircle
