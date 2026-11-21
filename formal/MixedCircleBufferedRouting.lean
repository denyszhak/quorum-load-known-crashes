import MixedCircleBufferedGeometry
import MixedCircleRawAttainment

set_option maxHeartbeats 4000000

namespace QuorumAudit.MixedCircle
noncomputable section
open Finset Circle
open scoped BigOperators
variable {n : ℕ} [NeZero n]

namespace BufferedProfile
variable {r d : ℕ} (P : BufferedProfile n r d)

theorem read_route (hr : 5 ≤ r) :
    ∃ read : Routing (reads n r) univ {0, (d : ZMod n)},
      ∀ i, incidence read.quorums read.p i = P.value i.val := by
  have htA := Nat.div_le_self P.tA 2
  have htB := Nat.div_le_self P.tB 2
  have hF : ({0, d} : Finset ℕ) ⊆ range n := by
    intro i hi
    simp only [mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl <;> exact mem_range.mpr (by
      have := P.arcA; have := P.arcB
      have hp := Nat.mul_pos P.kB_pos (by omega : 0 < r)
      omega)
  let A := packedReadDistribution r P.kA (1 + P.tA / 2) (endReads P.kA P.tA) P.U P.V
  let B := packedReadDistribution r P.kB (d + 1 + P.tB / 2) (endReads P.kB P.tB) P.U P.V
  have hAv := packed_valid n r P.kA (1 + P.tA / 2) (endReads P.kA P.tA) P.U P.V
    (by omega) P.kA_pos (end_reads_subset _ _) P.low_pos P.high_pos {0, d}
    (by have := P.arcA; have := P.arcB; omega) (by
      intro i hi
      have := mem_Ico.mp hi
      have := P.arcA
      simp only [mem_insert, mem_singleton]
      omega)
  have hBv := packed_valid n r P.kB (d + 1 + P.tB / 2) (endReads P.kB P.tB) P.U P.V
    (by omega) P.kB_pos (end_reads_subset _ _) P.low_pos P.high_pos {0, d}
    (by have := P.arcB; omega) (by
      intro i hi
      have := mem_Ico.mp hi
      simp only [mem_insert, mem_singleton]
      omega)
  obtain ⟨oldRead, hread⟩ := read_distribution_route r (appendReadDistribution A B) {0, d}
    hF (append_read_valid r {0, d} A B hAv hBv)
  have hcast : ({0, d} : Finset ℕ).image (fun i : ℕ => (i : ZMod n)) = {0, (d : ZMod n)} := by simp
  let read : Routing (reads n r) univ {0, (d : ZMod n)} := {
    quorums := oldRead.quorums
    subset := oldRead.subset
    live := by intro q hq; rw [← hcast]; exact oldRead.live q hq
    p := oldRead.p
    nonnegative := oldRead.nonnegative
    normalized := oldRead.normalized }
  have hscale : (appendReadDistribution A B).scale = P.h := by
    change (endReads P.kA P.tA).card * P.U + (P.kA - (endReads P.kA P.tA).card) * P.V +
      ((endReads P.kB P.tB).card * P.U + (P.kB - (endReads P.kB P.tB).card) * P.V) = _
    have hEA : (endReads P.kA P.tA).card ≤ P.kA := by
      simpa using card_le_card (end_reads_subset P.kA P.tA)
    have hEB : (endReads P.kB P.tB).card ≤ P.kB := by
      simpa using card_le_card (end_reads_subset P.kB P.tB)
    have hsub : (P.kA - (endReads P.kA P.tA).card) +
      (P.kB - (endReads P.kB P.tB).card) =
      r - 1 - ((endReads P.kA P.tA).card + (endReads P.kB P.tB).card) := by
      have := P.blocks
      omega
    calc
      _ = ((endReads P.kA P.tA).card + (endReads P.kB P.tB).card) * P.U +
        ((P.kA - (endReads P.kA P.tA).card) + (P.kB - (endReads P.kB P.tB).card)) * P.V := by ring
      _ = P.h := by rw [hsub]; exact P.normalized
  refine ⟨read, ?_⟩
  intro i
  change incidence oldRead.quorums oldRead.p i = _
  rw [hread, hscale, append_read_degree, packed_degree, packed_degree]
  rfl

end BufferedProfile

theorem buffered_budgets (r : ℝ) (hr : 5 ≤ r) :
    (r^2 + 2) / den r + 1 = cap r * r ∧
    ordinary r / den r + 1 = cap r * (r - 1) ∧
    exceptional r / den r + 1 + mixture r = cap r * (r - 1) := by
  have hd := ne_of_gt (den_pos r hr)
  unfold cap mixture ordinary exceptional
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> unfold den <;> ring

theorem buffered_profile_attains (r d : ℕ) (hr : 10 ≤ r) (hn : n + 1 = r * r)
    (P : BufferedProfile n r d) :
    ∃ read : Routing (reads n r) univ {0, (d : ZMod n)},
    ∃ write : Routing (mixedWrites n r) univ {0, (d : ZMod n)},
      ∀ i ∈ univ \ {0, (d : ZMod n)}, combined read write (1 / 2) i = cap r / 2 := by
  have hrR : (5 : ℝ) ≤ r := by exact_mod_cast (show 5 ≤ r by omega)
  have hlast := last_stride (n := n) r (by omega) hn
  have hkrA : r ≤ P.kA * r := by simpa using Nat.mul_le_mul_right r P.kA_pos
  have hkrB : r ≤ P.kB * r := by simpa using Nat.mul_le_mul_right r P.kB_pos
  have hd : d < n := by have := P.arcB; omega
  let w := if d % r = 1 then r - 2 else 1
  have hw : w = 1 ∨ w = r - 2 := by dsimp [w]; split_ifs <;> omega
  have hwr : w < r := by omega
  have hwpos : 0 < w := by omega
  have hroom : w + (r - 1) * r < n := by omega
  have hwneq : d % r ≠ w := by dsimp [w]; split_ifs <;> omega
  have hd0 : (d : ZMod n) ≠ 0 := by
    intro he
    have hv := congrArg ZMod.val he
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hd] at hv
    simp only [ZMod.val_zero] at hv
    have := P.arcA
    omega
  have hF : ({0, (d : ZMod n)} : Finset (ZMod n)).card = 2 := by simp [Ne.symm hd0]
  let q := rotatedStride (n := n) r (w : ZMod n)
  have hq := rotated_stride_ranked (n := n) r (by omega) hn (w : ZMod n)
  have hqlive : q ⊆ univ \ {0, (d : ZMod n)} := by
    intro i hi
    refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
    simp only [mem_insert, mem_singleton]
    rintro (rfl | rfl)
    · have hm := rotated_stride_mod (n := n) r w 0 (by omega) hn hwr hroom
        (NeZero.pos n) (by simpa only [Nat.cast_zero] using hi)
      simp only [Nat.zero_mod] at hm
      omega
    · exact hwneq (rotated_stride_mod (n := n) r w d (by omega) hn hwr hroom hd hi)
  obtain ⟨read, hread⟩ := P.read_route (by omega)
  refine ⟨read, ?_⟩
  apply compensation_attains r (by omega) hn {0, (d : ZMod n)} hF read
    (fun i => P.mass i.val) P.h P.μ P.C P.scale_pos hread P.mixture_eq P.cap_eq q hq hqlive
  · intro i _
    rw [hread]
    exact (P.point i.val (by omega)).trans (high_point_bound r hrR)
  · intro s
    have hrn : r ≤ n := by nlinarith
    have hsum : (∑ i ∈ arc r s, incidence read.quorums read.p i) = cyclicSum n P.value s.val r := by
      simp_rw [hread]
      change (∑ i ∈ arc r s, (P.mass i.val : ℝ) / P.h) = _
      rw [← sum_div, ← Nat.cast_sum, raw_arc_sum P.mass r hrn s]
      exact (cyclicSum_div n P.mass P.h s.val r).symm
    rw [hsum]
    have hcount := rotated_stride_count (n := n) r (by omega) hn (w : ZMod n) s
    change (arc r s ∩ q).card = _ at hcount
    have hFe := cast_pair_count r d hd s
    have hcard := card_sdiff_add_card_inter (arc r s) {0, (d : ZMod n)}
    rw [arc_card r hrn s, hFe] at hcard
    have hclass := P.windows (by omega) s.val (ZMod.val_lt s)
    have hb := buffered_budgets (r : ℝ) hrR
    by_cases he : s = (w : ZMod n) + (((r - 1) * r : ℕ) : ZMod n)
    · have hval : s.val = w + (r - 1) * r := by
        rw [he, ← Nat.cast_add, ZMod.val_natCast, Nat.mod_eq_of_lt hroom]
      have hex : s.val = n - 1 ∨ s.val = n - r + 2 := by
        rw [hval]
        omega
      have hbound := P.exceptional_window hr s.val (ZMod.val_lt s) hex
      rw [hcount, if_pos he]
      norm_num only [Nat.cast_ofNat]
      rcases hclass with ⟨hc, _⟩ | ⟨hc, _⟩
      · have hlive : (arc r s \ {0, (d : ZMod n)}).card = r := by omega
        rw [hlive]
        have hμ := (parameters (r : ℝ) hrR).1
        have hc0 : 0 ≤ cap r := by unfold cap; exact div_nonneg (by linarith) (le_of_lt (den_pos r hrR))
        nlinarith only [hbound, hb.2.2, hc0]
      · have hlive : (arc r s \ {0, (d : ZMod n)}).card = r - 1 := by omega
        rw [hlive, Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
        linarith only [hbound, hb.2.2]
    · rw [hcount, if_neg he, Nat.cast_one]
      rcases hclass with ⟨hc, hbound⟩ | ⟨hc, hbound⟩
      · have hlive : (arc r s \ {0, (d : ZMod n)}).card = r := by omega
        rw [hlive]
        linarith only [hbound, hb.1]
      · have hlive : (arc r s \ {0, (d : ZMod n)}).card = r - 1 := by omega
        rw [hlive, Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
        linarith only [hbound, hb.2.1]

theorem buffered_attains (r d kA kB tA tB : ℕ) (hr : 10 ≤ r) (hn : n + 1 = r * r)
    (hkA : 0 < kA) (hkB : 0 < kB)
    (hA : 1 + kA * r + tA = d) (hB : d + 1 + kB * r + tB = n)
    (hK : kA + kB = r - 1) (hT : tA + tB = r - 3) :
    ∃ read : Routing (reads n r) univ {0, (d : ZMod n)},
    ∃ write : Routing (mixedWrites n r) univ {0, (d : ZMod n)},
      ∀ i ∈ univ \ {0, (d : ZMod n)}, combined read write (1 / 2) i = cap r / 2 := by
  obtain ⟨P⟩ := buffered_profile_exists n r d kA kB tA tB hr hkA hkB hA hB hK hT
  exact buffered_profile_attains r d hr hn P

#print axioms BufferedProfile.read_route
#print axioms buffered_attains
end
end QuorumAudit.MixedCircle
