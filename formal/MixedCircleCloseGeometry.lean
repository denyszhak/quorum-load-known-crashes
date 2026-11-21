import MixedCircleOverlapProfiles

set_option maxHeartbeats 4000000

namespace QuorumAudit.MixedCircle
open Finset
open scoped BigOperators

theorem inter_pair_card {ι : Type*} [DecidableEq ι] (S : Finset ι) (a b : ι) (hne : a ≠ b) :
    (S ∩ {a, b}).card = (if a ∈ S then 1 else 0) + (if b ∈ S then 1 else 0) := by
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
  · have he : S ∩ {a, b} = {a, b} := by ext i; simp_all
    simp [he, ha, hb, hne]
  · have he : S ∩ {a, b} = {a} := by ext i; simp_all
    simp [he, ha, hb]
  · have he : S ∩ {a, b} = {b} := by ext i; simp_all
    simp [he, ha, hb]
  · have he : S ∩ {a, b} = ∅ := by ext i; simp_all
    simp [he, ha, hb]

def closeMass (r i : ℕ) : ℕ := placedMass r (r - 1) 2 (r + 1) i

theorem close_prefix_window (n r s : ℕ) (hr : 5 ≤ r) (hn : n + 1 = r * r)
    (hs : 1 ≤ s) (hsr : s ≤ r) :
    cyclicSum n (closeMass r) s r = lineSum (pairedMass r (r - 1) 2) 0 (s - 1) := by
  have hlarge : 2 * r < n := by nlinarith
  rw [cyclicSum_nowrap n _ s r (by omega)]
  have hlen : (r + 1 - s) + (s - 1) = r := by omega
  have hsplit := lineSum_add (closeMass r) s (r + 1 - s) (s - 1)
  rw [hlen] at hsplit
  rw [hsplit]
  rw [show s + (r + 1 - s) = r + 1 by omega]
  change lineSum (placedMass r (r - 1) 2 (r + 1)) s (r + 1 - s) +
    lineSum (placedMass r (r - 1) 2 (r + 1)) (r + 1) (s - 1) = _
  rw [placed_line_before r (r - 1) 2 (r + 1) s (r + 1 - s) (by omega), zero_add]
  have he := placed_line r (r - 1) 2 (r + 1) 0 (s - 1)
  simpa using he

theorem close_suffix_window (n r s : ℕ) (hr : 5 ≤ r) (hn : n + 1 = r * r)
    (hs : s < n) (hwrap : n < s + r) :
    cyclicSum n (closeMass r) s r = lineSum (pairedMass r (r - 1) 2) 0 (n - s) := by
  have hlarge : 2 * r < n := by nlinarith
  have hp : (r - 1) * r + r = r * r := by nlinarith [show r - 1 + 1 = r by omega]
  have hL : r + 1 + ((r - 1) * r - 2) = n := by omega
  rw [cyclicSum_wrap n _ s r hs (by omega) hwrap]
  change lineSum (placedMass r (r - 1) 2 (r + 1)) s (n - s) +
    lineSum (placedMass r (r - 1) 2 (r + 1)) 0 (r - (n - s)) = _
  rw [placed_line_before r (r - 1) 2 (r + 1) 0 (r - (n - s)) (by omega), add_zero]
  have he : s = r + 1 + ((r - 1) * r - 2 - (n - s)) := by omega
  have hpLine := placed_line r (r - 1) 2 (r + 1) ((r - 1) * r - 2 - (n - s)) (n - s)
  have hsEq : r + 1 + ((r - 1) * r - 2 - (n - s)) = s := by omega
  rw [hsEq] at hpLine
  rw [hpLine]
  exact paired_suffix_eq_prefix r (r - 1) 2 (n - s) (by omega) (by omega) (by omega)
    (by omega) (by omega)

theorem close_raw_window (n r a d s : ℕ) (hr : 5 ≤ r) (hn : n + 1 = r * r)
    (hd : 1 ≤ d ∧ d ≤ r) (ha0 : 2 * a ≤ r - d) (ha1 : r - d ≤ 2 * a + 1)
    (hs : s < n) :
    cyclicSum n (closeMass r) s r +
      2 * (r - 5) * (if s = (r - 1) * r + (if d ≤ r - 2 then 0 else 1) then 2 else 1) +
      (2 * (r - 2) * (r + 1) - 2 * (r - 5)) ≤
    2 * (2 * r - 1) * (r - (natArc n r s ∩ {a, a + d}).card) := by
  have hr1 : r - 1 + 1 = r := by omega
  have hr2 : r - 2 + 2 = r := by omega
  have hr5 : r - 5 + 5 = r := by omega
  have h2r1 : 2 * r - 1 + 1 = 2 * r := by omega
  have hE : r + (r - 1) - 1 + 2 = 2 * r := by omega
  have hp : (r - 1) * r + r = r * r := by nlinarith
  have hlarge : 2 * r < n := by nlinarith
  have had : a + d ≤ r := by omega
  have hrd : r - d + d = r := by omega
  have hsub1 : s - 1 + 1 = s ∨ s = 0 := by omega
  have hns : n - s + s = n := by omega
  have hnear : lineSum (pairedMass r (r - 1) 2) 0 (r - 1) =
      (r - 2) * (r + (r - 1) - 1) + (2 * r + 2) := by
    simpa [lineSum] using paired_prefix_near r (r - 1) 2 (by omega) (by omega) (by omega) (by omega)
  have hDμ : 2 * (r - 5) ≤ 2 * (r - 2) * (r + 1) := by nlinarith
  have hsub : 2 * (r - 2) * (r + 1) - 2 * (r - 5) + 2 * (r - 5) =
      2 * (r - 2) * (r + 1) := Nat.sub_add_cancel hDμ
  rw [inter_pair_card _ a (a + d) (by omega)]
  by_cases hz : s = 0
  · subst s
    have hx : cyclicSum n (closeMass r) 0 r = 0 := by
      rw [cyclicSum_nowrap n _ 0 r (by omega)]
      exact placed_line_before r (r - 1) 2 (r + 1) 0 r (by omega)
    rw [hx, natArc_nowrap n r 0 (by omega)]
    simp only [mem_Ico, zero_add]
    split_ifs <;> (try omega) <;> (try simp only [Nat.add_zero, Nat.zero_add, Nat.sub_zero]) <;> nlinarith
  · by_cases hfront : s ≤ r
    · rw [close_prefix_window n r s hr hn (by omega) hfront,
        natArc_nowrap n r s (by omega)]
      simp only [mem_Ico]
      have hnex : s ≠ (r - 1) * r + (if d ≤ r - 2 then 0 else 1) := by
        split_ifs <;> omega
      rw [if_neg hnex]
      by_cases hnear : s = r
      · rw [hnear, ‹lineSum (pairedMass r (r - 1) 2) 0 (r - 1) = _›]
        split_ifs <;> (try omega) <;> (try simp only [Nat.add_zero, Nat.zero_add, Nat.sub_zero]) <;> nlinarith
      · rw [paired_short_endpoint r (r - 1) 2 (s - 1) hr (by omega) (by omega) (by omega) (by omega)]
        have hE : r + (r - 1) - 1 + 2 = 2 * r := by omega
        have hs1 : s - 1 + 1 = s := by omega
        split_ifs <;> (try omega) <;> (try simp only [Nat.add_zero, Nat.zero_add, Nat.sub_zero]) <;> nlinarith
    · by_cases hwrap : n < s + r
      · rw [close_suffix_window n r s hr hn hs hwrap, natArc_wrap n r s hs (by omega) hwrap]
        simp only [mem_union, mem_Ico, Nat.zero_le, true_and]
        have haIn : (s ≤ a ∧ a < n ∨ a < s + r - n) ↔ a < s + r - n := by omega
        have hadIn : (s ≤ a + d ∧ a + d < n ∨ a + d < s + r - n) ↔
            a + d < s + r - n := by omega
        simp only [haIn, hadIn]
        have hℓ : n - s ≤ r - 1 := by omega
        by_cases hnear : n - s = r - 1
        · rw [hnear, ‹lineSum (pairedMass r (r - 1) 2) 0 (r - 1) = _›]
          split_ifs <;> (try omega) <;> (try simp only [Nat.add_zero, Nat.zero_add, Nat.sub_zero]) <;>
            (try { have hbound : 2 * (n - s) ≤ r - 2 := by omega
                   have hm := Nat.mul_le_mul_right (r - 1) hbound
                   nlinarith }) <;> nlinarith
        · rw [paired_short_endpoint r (r - 1) 2 (n - s) hr (by omega) (by omega) (by omega) (by omega)]
          have hE : r + (r - 1) - 1 + 2 = 2 * r := by omega
          split_ifs <;> (try omega) <;> (try simp only [Nat.add_zero, Nat.zero_add, Nat.sub_zero]) <;>
            first
            | (have hbound : 2 * (n - s) ≤ r - 2 := by omega
               have hm := Nat.mul_le_mul_right (r - 1) hbound
               nlinarith only [hr, hr1, hr2, hr5, h2r1, hE, hsub, hbound, hm])
            | nlinarith
      · have hroom : s + r ≤ n := by omega
        have hx := placed_line_window r (r - 1) 2 (r + 1) s (by omega) (by omega)
          (by omega) (by omega) (by omega) (by
            have hL : r + 1 + ((r - 1) * r - 2) = n := by omega
            omega)
        change lineSum (closeMass r) s r ≤ _ at hx
        rw [cyclicSum_nowrap n _ s r hroom, natArc_nowrap n r s hroom]
        simp only [mem_Ico]
        have hnex : s ≠ (r - 1) * r + (if d ≤ r - 2 then 0 else 1) := by
          split_ifs <;> omega
        rw [if_neg hnex, if_neg (by omega), if_neg (by omega)]
        simp only [Nat.add_zero, Nat.zero_add, Nat.sub_zero]
        nlinarith

#print axioms close_raw_window
end QuorumAudit.MixedCircle
