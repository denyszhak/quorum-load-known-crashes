import MixedCircleTransport
import MixedCircleWindows

set_option maxHeartbeats 2000000

namespace QuorumAudit.MixedCircle
noncomputable section
open Finset Circle
open scoped BigOperators
variable {n : ℕ} [NeZero n]

def natStride (r : ℕ) : Finset ℕ := (range r).image (fun j => j * r)
def stride (r : ℕ) : Finset (ZMod n) := (natStride r).image (fun i : ℕ => (i : ZMod n))

theorem last_stride (r : ℕ) (hr : 2 ≤ r) (hn : n + 1 = r * r) :
    (r - 1) * r + r = n + 1 := by
  calc
    _ = (r - 1 + 1) * r := by ring
    _ = r * r := by rw [Nat.sub_add_cancel (by omega : 1 ≤ r)]
    _ = _ := hn.symm

theorem natStride_subset (r : ℕ) (hr : 2 ≤ r) (hn : n + 1 = r * r) :
    natStride r ⊆ range n := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
  have hjr := mem_range.mp hj
  have hlast := last_stride r hr hn
  have hb : j * r ≤ (r - 1) * r := Nat.mul_le_mul_right r (by omega)
  exact mem_range.mpr (by omega)

theorem linear_stride_intersection (r s : ℕ) (hr : 2 ≤ r) (hn : n + 1 = r * r)
    (hroom : s + r ≤ n) :
    Ico s (s + r) ∩ natStride r = {((s + r - 1) / r) * r} := by
  let q := (s + r - 1) / r
  have hrp : 0 < r := by omega
  have hq : q < r := (Nat.div_lt_iff_lt_mul hrp).mpr (by omega)
  have hlo : q * r ≤ s + r - 1 := by simpa [q, Nat.mul_comm] using Nat.mul_div_le (s + r - 1) r
  have hhi : s + r - 1 < (q + 1) * r :=
    (Nat.div_lt_iff_lt_mul hrp).mp (by omega)
  have hnext : (q + 1) * r = q * r + r := by ring
  rw [hnext] at hhi
  ext i
  constructor
  · intro hi
    obtain ⟨hiI, hiW⟩ := mem_inter.mp hi
    obtain ⟨j, hj, he⟩ := mem_image.mp hiW
    have hlow := (mem_Ico.mp hiI).1
    have hupp := (mem_Ico.mp hiI).2
    have hjnext : (j + 1) * r = j * r + r := by ring
    have hdiv : (s + r - 1) / r = j := Nat.div_eq_of_lt_le (by omega) (by rw [hjnext]; omega)
    apply mem_singleton.mpr
    rw [← he, hdiv]
  · intro hi
    have he : i = q * r := mem_singleton.mp hi
    rw [he]
    exact mem_inter.mpr ⟨mem_Ico.mpr ⟨by omega, by omega⟩,
      mem_image.mpr ⟨q, mem_range.mpr hq, rfl⟩⟩

theorem wrapping_stride_intersection (r s : ℕ) (hr : 2 ≤ r) (hn : n + 1 = r * r)
    (hs : s < n) (hwrap : n < s + r) :
    natArc n r s ∩ natStride r = if s = (r - 1) * r then {0, (r - 1) * r} else {0} := by
  have hlast := last_stride r hr hn
  have hrlast : r ≤ (r - 1) * r := by
    simpa using Nat.mul_le_mul_right r (show 1 ≤ r - 1 by omega)
  have harc := natArc_wrap n r s hs (by omega) hwrap
  have hchar : ∀ i, i ∈ natArc n r s ∩ natStride r ↔
      i = 0 ∨ (s = (r - 1) * r ∧ i = (r - 1) * r) := by
    intro i
    constructor
    · intro hi
      obtain ⟨hiA, hiW⟩ := mem_inter.mp hi
      obtain ⟨j, hj, he⟩ := mem_image.mp hiW
      have hjr := mem_range.mp hj
      have hjlast : j * r ≤ (r - 1) * r := Nat.mul_le_mul_right r (by omega)
      rw [harc] at hiA
      rcases mem_union.mp hiA with hiA | hiA
      · right
        have := mem_Ico.mp hiA
        omega
      · left
        have hupp := (mem_Ico.mp hiA).2
        by_cases hj0 : j = 0
        · rw [hj0] at he; simpa using he.symm
        · have hmin : r ≤ j * r := by
            simpa using Nat.mul_le_mul_right r (show 1 ≤ j by omega)
          omega
    · rintro (rfl | ⟨heS, rfl⟩)
      · apply mem_inter.mpr
        refine ⟨?_, mem_image.mpr ⟨0, mem_range.mpr (by omega), by simp⟩⟩
        rw [harc]
        exact mem_union_right _ (mem_Ico.mpr ⟨le_rfl, by omega⟩)
      · apply mem_inter.mpr
        refine ⟨?_, mem_image.mpr ⟨r - 1, mem_range.mpr (by omega), rfl⟩⟩
        rw [harc]
        exact mem_union_left _ (mem_Ico.mpr ⟨by omega, by omega⟩)
  ext i
  rw [hchar]
  by_cases he : s = (r - 1) * r <;> simp [he]

theorem nat_stride_count (r s : ℕ) (hr : 2 ≤ r) (hn : n + 1 = r * r) (hs : s < n) :
    (natArc n r s ∩ natStride r).card = if s = (r - 1) * r then 2 else 1 := by
  by_cases hroom : s + r ≤ n
  · rw [natArc_nowrap n r s hroom, linear_stride_intersection r s hr hn hroom, card_singleton]
    have hlast := last_stride r hr hn
    rw [ite_eq_right (by omega)]
  · rw [wrapping_stride_intersection r s hr hn hs (by omega)]
    have hlastpos : 0 < (r - 1) * r := Nat.mul_pos (by omega) (by omega)
    split_ifs <;> simp [ne_of_gt hlastpos, ne_of_lt hlastpos]

theorem cast_intersection (A B : Finset ℕ) (hA : A ⊆ range n) (hB : B ⊆ range n) :
    (A ∩ B).image (fun i : ℕ => (i : ZMod n)) =
      A.image (fun i : ℕ => (i : ZMod n)) ∩ B.image (fun i : ℕ => (i : ZMod n)) := by
  ext i
  simp only [mem_inter, cast_membership A hA i, cast_membership B hB i,
    cast_membership (A ∩ B) (inter_subset_left.trans hA) i]

theorem stride_count (r : ℕ) (hr : 2 ≤ r) (hn : n + 1 = r * r) (s : ZMod n) :
    (arc r s ∩ stride (n := n) r).card = if s.val = (r - 1) * r then 2 else 1 := by
  have hAr : natArc n r s.val ⊆ range n := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := mem_image.mp hi
    exact mem_range.mpr (Nat.mod_lt _ (NeZero.pos n))
  have hW := natStride_subset r hr hn
  have he := cast_intersection (natArc n r s.val) (natStride r) hAr hW
  rw [cast_natArc, ZMod.natCast_zmod_val] at he
  change (arc r s ∩ (natStride r).image (fun i : ℕ => (i : ZMod n))).card = _
  rw [← he, card_image_of_injOn]
  · exact nat_stride_count r s.val hr hn (ZMod.val_lt s)
  · intro a ha b hb hab
    exact cast_injective_below (mem_range.mp (hAr (mem_inter.mp ha).1))
      (mem_range.mp (hAr (mem_inter.mp hb).1)) hab

theorem stride_ranked (r : ℕ) (hr : 2 ≤ r) (hn : n + 1 = r * r) :
    stride (n := n) r ∈ rankedWrites n r r := by
  have hW := natStride_subset r hr hn
  have hcard : (stride (n := n) r).card = r := by
    unfold stride natStride
    rw [card_image_of_injOn, card_image_of_injOn, card_range]
    · intro a ha b hb hab
      exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < r) hab
    · intro a ha b hb hab
      exact cast_injective_below (mem_range.mp (hW ha)) (mem_range.mp (hW hb)) hab
  refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _), ?_⟩, hcard⟩
  intro s
  apply card_pos.mp
  rw [stride_count r hr hn s]
  split_ifs <;> omega

#print axioms stride_count
#print axioms stride_ranked

def rotatedStride (r : ℕ) (a : ZMod n) : Finset (ZMod n) :=
  (stride r).image (translateEquiv a)

theorem rotated_stride_count (r : ℕ) (hr : 2 ≤ r) (hn : n + 1 = r * r)
    (a s : ZMod n) :
    (arc r s ∩ rotatedStride r a).card =
      if s = a + (((r - 1) * r : ℕ) : ZMod n) then 2 else 1 := by
  have he := image_inter (arc r (s - a)) (stride (n := n) r) (translateEquiv a).injective
  rw [translate_arc] at he
  have heas : a + (s - a) = s := by ring
  rw [heas] at he
  unfold rotatedStride
  rw [← he, card_image_of_injective _ (translateEquiv a).injective, stride_count r hr hn]
  have hlast := last_stride r hr hn
  have hlastn : (r - 1) * r < n := by omega
  have hiff : (s - a).val = (r - 1) * r ↔
      s = a + (((r - 1) * r : ℕ) : ZMod n) := by
    constructor
    · intro hv
      have hs : s - a = (((r - 1) * r : ℕ) : ZMod n) := by
        calc s - a = ((s - a).val : ZMod n) := by simp
             _ = _ := by rw [hv]
      calc s = a + (s - a) := by ring
           _ = _ := by rw [hs]
    · intro hs
      rw [hs]
      have hsub : a + (((r - 1) * r : ℕ) : ZMod n) - a =
          (((r - 1) * r : ℕ) : ZMod n) := by ring
      rw [hsub, ZMod.val_natCast, Nat.mod_eq_of_lt hlastn]
  simp only [hiff]

theorem rotated_stride_ranked (r : ℕ) (hr : 2 ≤ r) (hn : n + 1 = r * r) (a : ZMod n) :
    rotatedStride r a ∈ rankedWrites n r r := by
  have hbase := stride_ranked r hr hn
  have hcard : (rotatedStride r a).card = r := by
    unfold rotatedStride
    rw [card_image_of_injective _ (translateEquiv a).injective]
    exact (mem_filter.mp hbase).2
  refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _), ?_⟩, hcard⟩
  intro s
  apply card_pos.mp
  rw [rotated_stride_count r hr hn]
  split_ifs <;> omega

theorem rotated_stride_points (r a : ℕ) (hr : 2 ≤ r) (hn : n + 1 = r * r)
    (hroom : a + (r - 1) * r < n) (i : ZMod n) (hi : i ∈ rotatedStride r (a : ZMod n)) :
    ∃ j < r, i.val = a + j * r := by
  unfold rotatedStride stride natStride at hi
  rw [image_image, image_image] at hi
  obtain ⟨j, hj, he⟩ := mem_image.mp hi
  have hjr := mem_range.mp hj
  have hbound : a + j * r < n := by
    have hh := Nat.mul_le_mul_right r (show j ≤ r - 1 by omega)
    omega
  refine ⟨j, hjr, ?_⟩
  have heq : ((a + j * r : ℕ) : ZMod n) = i := by simpa [translateEquiv] using he
  rw [← heq, ZMod.val_natCast, Nat.mod_eq_of_lt hbound]

theorem rotated_stride_mod (r a d : ℕ) (hr : 2 ≤ r) (hn : n + 1 = r * r)
    (ha : a < r) (hroom : a + (r - 1) * r < n) (hd : d < n)
    (hi : (d : ZMod n) ∈ rotatedStride r (a : ZMod n)) : d % r = a := by
  obtain ⟨j, _, he⟩ := rotated_stride_points r a hr hn hroom (d : ZMod n) hi
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hd] at he
  rw [he]
  simp [Nat.add_mod, Nat.mod_eq_of_lt ha]

#print axioms rotated_stride_count
#print axioms rotated_stride_ranked
end
end QuorumAudit.MixedCircle
