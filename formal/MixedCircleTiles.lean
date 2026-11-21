import CircleExactCardinality

set_option maxHeartbeats 2000000

namespace QuorumAudit.MixedCircle
open Finset
open scoped BigOperators

def tileMass {α : Type*} [AddCommMonoid α] (b r k : ℕ) (w : ℕ → α) (i : ℕ) : α :=
  ∑ j ∈ range k, if b + j * r ≤ i ∧ i < b + (j + 1) * r then w j else 0

theorem tileMass_eval {α : Type*} [AddCommMonoid α] (b r k : ℕ) (w : ℕ → α)
    (hr : 0 < r) (i : ℕ) :
    tileMass b r k w i = if b ≤ i ∧ i < b + k * r then w ((i - b) / r) else 0 := by
  unfold tileMass
  by_cases hi : b ≤ i ∧ i < b + k * r
  · rw [if_pos hi]
    let q := (i - b) / r
    have hq : q < k := (Nat.div_lt_iff_lt_mul hr).mpr (by omega)
    have hqlo : q * r ≤ i - b := by simpa [q, Nat.mul_comm] using Nat.mul_div_le (i - b) r
    have hqhi : i - b < (q + 1) * r :=
      (Nat.div_lt_iff_lt_mul hr).mp (by dsimp [q]; omega)
    rw [sum_eq_single q]
    · rw [if_pos (by omega)]
    · intro j hj hjq
      apply if_neg
      intro hji
      have hdiv : (i - b) / r = j := Nat.div_eq_of_lt_le (by omega) (by omega)
      exact hjq (by simpa [q] using hdiv.symm)
    · intro hnot
      exact False.elim (hnot (mem_range.mpr hq))
  · rw [if_neg hi]
    apply sum_eq_zero
    intro j hj
    apply if_neg
    intro hji
    have hjk : j + 1 ≤ k := by have := mem_range.mp hj; omega
    have hm : (j + 1) * r ≤ k * r := Nat.mul_le_mul_right r hjk
    exact hi ⟨by omega, by omega⟩

theorem paired_tile_profile (r k δ i : ℕ) (hr : 3 ≤ r) (hk : 2 ≤ k)
    (hkr : k ≤ r) (hδ : 1 ≤ δ ∧ δ ≤ 2) (hi : i < k * r - δ) :
    tileMass 0 r (k - 1) (fun j => 2 * (k - 1 - j) + (r - k + 1)) i +
      tileMass (r - δ) r (k - 1) (fun j => 2 * (j + 1) + (r - k + 1)) i =
    if i < r - δ ∨ (k - 1) * r ≤ i then r + k - 1
    else if r - δ ≤ i % r then 2 * r + 2 else 2 * r := by
  have hrp : 0 < r := by omega
  have hdr : δ ≤ r := by omega
  have hik : i < k * r := by omega
  have hqk : i / r < k := (Nat.div_lt_iff_lt_mul hrp).mpr hik
  have hmod : i % r < r := Nat.mod_lt i hrp
  have hdecomp : i % r + r * (i / r) = i := Nat.mod_add_div i r
  rw [Nat.mul_comm r (i / r)] at hdecomp
  have hsucc : (i / r + 1) * r = (i / r) * r + r := by ring
  have hkprod : (k - 1) * r + r = k * r := by
    calc
      _ = (k - 1 + 1) * r := by ring
      _ = _ := by rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
  rw [tileMass_eval _ _ _ _ hrp, tileMass_eval _ _ _ _ hrp]
  simp only [zero_add, Nat.sub_zero]
  by_cases hfront : i < r - δ
  · have hq : i / r = 0 := Nat.div_eq_of_lt (by omega)
    have hfirst : i < (k - 1) * r := by
      have : r ≤ (k - 1) * r := by simpa using Nat.mul_le_mul_right r (show 1 ≤ k - 1 by omega)
      omega
    rw [if_pos ⟨Nat.zero_le _, hfirst⟩, if_neg (by omega), if_pos (Or.inl hfront), hq]
    omega
  · by_cases hlast : (k - 1) * r ≤ i
    · have hq : i / r = k - 1 := Nat.div_eq_of_lt_le hlast
        (by simpa [Nat.sub_add_cancel (by omega : 1 ≤ k)] using hik)
      have hsecond : r - δ ≤ i ∧ i < r - δ + (k - 1) * r := by
        have : r ≤ (k - 1) * r := by simpa using Nat.mul_le_mul_right r (show 1 ≤ k - 1 by omega)
        omega
      have hqprod : (k - 2) * r + r = (k - 1) * r := by
        have he : k - 2 + 1 = k - 1 := by omega
        calc
          _ = (k - 2 + 1) * r := by ring
          _ = _ := by rw [he]
      have hq2 : (i - (r - δ)) / r = k - 2 :=
        Nat.div_eq_of_lt_le (by omega) (by rw [show k - 2 + 1 = k - 1 by omega]; omega)
      rw [if_neg (by omega), if_pos hsecond, if_pos (Or.inr hlast), hq2]
      omega
    · have hfirst : i < (k - 1) * r := by omega
      have hsecond : r - δ ≤ i ∧ i < r - δ + (k - 1) * r := by omega
      rw [if_pos ⟨Nat.zero_le _, hfirst⟩, if_pos hsecond,
        if_neg (by omega : ¬ (i < r - δ ∨ (k - 1) * r ≤ i))]
      have hqsmall : i / r < k - 1 := (Nat.div_lt_iff_lt_mul hrp).mpr hfirst
      have hsplit : i - (r - δ) + (r - δ) = i := Nat.sub_add_cancel (by omega)
      by_cases ht : r - δ ≤ i % r
      · have hq2 : (i - (r - δ)) / r = i / r :=
          Nat.div_eq_of_lt_le (by omega) (by rw [hsucc]; omega)
        rw [if_pos ht, hq2]
        omega
      · have hqp : 1 ≤ i / r := by
          apply Nat.one_le_iff_ne_zero.mpr
          intro hq0
          rw [hq0] at hdecomp
          simp only [Nat.zero_mul, add_zero] at hdecomp
          omega
        have hqprod : (i / r - 1) * r + r = (i / r) * r := by
          calc
            _ = (i / r - 1 + 1) * r := by ring
            _ = _ := by rw [Nat.sub_add_cancel hqp]
        have hq2 : (i - (r - δ)) / r = i / r - 1 :=
          Nat.div_eq_of_lt_le (by omega)
            (by rw [Nat.sub_add_cancel hqp]; omega)
        rw [if_neg ht, hq2]
        omega

#print axioms tileMass_eval
#print axioms paired_tile_profile
end QuorumAudit.MixedCircle
