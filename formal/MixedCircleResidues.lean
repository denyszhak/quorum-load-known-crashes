import MixedCircleBufferedBounds

namespace QuorumAudit.MixedCircle

theorem live_arc_remainders (r kA kB tA tB : ℕ) (hr : 10 ≤ r)
    (htA : tA < r) (htB : tB < r)
    (hsum : (kA + kB) * r + (tA + tB) = (r - 1) * r + (r - 3)) :
    (tA + tB = r - 3 ∧ kA + kB = r - 1) ∨
    (tA + tB = 2 * r - 3 ∧ (kA + 1) + (kB + 1) = r ∧
      1 ≤ r - tA ∧ r - tA ≤ 2 ∧ 1 ≤ r - tB ∧ r - tB ≤ 2) := by
  have hmod : (tA + tB) % r = r - 3 := by
    have hh := congrArg (fun i : ℕ => i % r) hsum
    simpa only [Nat.mul_add_mod_self_right,
      Nat.mod_eq_of_lt (by omega : r - 3 < r)] using hh
  have hq : (tA + tB) / r < 2 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
  have hdecomp := Nat.mod_add_div (tA + tB) r
  rw [hmod] at hdecomp
  have hcases : (tA + tB) / r = 0 ∨ (tA + tB) / r = 1 := by
    have hf : ∀ q : ℕ, q < 2 → q = 0 ∨ q = 1 := by intro q hq; omega
    exact hf _ hq
  rcases hcases with hz | hq1
  · left
    rw [hz, Nat.mul_zero, add_zero] at hdecomp
    have ht : tA + tB = r - 3 := hdecomp.symm
    have hm : (kA + kB) * r = (r - 1) * r := by omega
    exact ⟨ht, Nat.eq_of_mul_eq_mul_right (by omega : 0 < r) hm⟩
  · right
    rw [hq1, Nat.mul_one] at hdecomp
    have ht : tA + tB = 2 * r - 3 := by omega
    have hr1 : r - 1 + 1 = r := by omega
    have hr3 : r - 3 + 3 = r := by omega
    have hr23 : 2 * r - 3 + 3 = 2 * r := by omega
    have hm : ((kA + 1) + (kB + 1)) * r = r * r := by nlinarith only [hsum, ht, hr1, hr3, hr23]
    exact ⟨ht, Nat.eq_of_mul_eq_mul_right (by omega : 0 < r) hm, by omega, by omega, by omega, by omega⟩


#print axioms live_arc_remainders
end QuorumAudit.MixedCircle
