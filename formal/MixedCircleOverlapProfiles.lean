import MixedCirclePlacedProfiles

set_option maxHeartbeats 3000000

namespace QuorumAudit.MixedCircle
open Finset
open scoped BigOperators

theorem paired_short_endpoint (r k δ ℓ : ℕ) (hr : 5 ≤ r) (hk : 2 ≤ k)
    (hkr : k ≤ r) (hδ : 1 ≤ δ ∧ δ ≤ 2) (hℓ : ℓ ≤ r - 2) :
    lineSum (pairedMass r k δ) 0 ℓ = ℓ * (r + k - 1) := by
  simpa [lineSum] using paired_prefix r k δ ℓ (by omega) hk hkr hδ (by omega)

theorem paired_near_endpoint_bound (r k δ : ℕ) (hr : 5 ≤ r) (hk : 2 ≤ k)
    (hkr : k ≤ r) (hδ : 1 ≤ δ ∧ δ ≤ 2) :
    lineSum (pairedMass r k δ) 0 (r - 1) ≤
      (r - 2) * (r + k - 1) + (2 * r + 2) := by
  have he := paired_prefix_near r k δ (by omega) hk hkr hδ
  simp only [lineSum, zero_add]
  rw [he]
  split_ifs
  · have hlen : r - 1 = r - 2 + 1 := by omega
    rw [hlen, Nat.add_mul]
    omega
  · exact le_rfl

theorem paired_cross_bound (r a b δA δB ℓ : ℕ) (hr : 5 ≤ r)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : a + b = r)
    (hδA : 1 ≤ δA ∧ δA ≤ 2) (hδB : 1 ≤ δB ∧ δB ≤ 2) (hℓ : ℓ ≤ r - 1) :
    lineSum (pairedMass r a δA) 0 ℓ +
      lineSum (pairedMass r b δB) 0 (r - 1 - ℓ) ≤ 2 * ((r - 1) ^ 2 + 2) := by
  have hEA : r + a - 1 ≤ 2 * r - 3 := by omega
  have hEB : r + b - 1 ≤ 2 * r - 3 := by omega
  have hr1 : r - 1 + 1 = r := by omega
  have hr2 : r - 2 + 2 = r := by omega
  have hr3 : 2 * r - 3 + 3 = 2 * r := by omega
  by_cases hleft : ℓ = r - 1
  · subst ℓ
    simp only [Nat.sub_self, lineSum, range_zero, sum_empty, add_zero]
    have he := paired_near_endpoint_bound r a δA hr ha (by omega) hδA
    have hm := Nat.mul_le_mul_left (r - 2) hEA
    simp only [lineSum, zero_add] at he
    simpa only [zero_add] using he.trans (show (r - 2) * (r + a - 1) + (2 * r + 2) ≤
      2 * ((r - 1) ^ 2 + 2) by nlinarith)
  · by_cases hright : ℓ = 0
    · subst ℓ
      simp only [Nat.sub_zero, lineSum, range_zero, sum_empty, zero_add]
      have he := paired_near_endpoint_bound r b δB hr hb (by omega) hδB
      have hm := Nat.mul_le_mul_left (r - 2) hEB
      simp only [lineSum, zero_add] at he
      simpa only [zero_add] using he.trans (show (r - 2) * (r + b - 1) + (2 * r + 2) ≤
        2 * ((r - 1) ^ 2 + 2) by nlinarith)
    · have hsmallA : ℓ ≤ r - 2 := by omega
      have hsmallB : r - 1 - ℓ ≤ r - 2 := by omega
      rw [paired_short_endpoint r a δA ℓ hr ha (by omega) hδA hsmallA,
        paired_short_endpoint r b δB (r - 1 - ℓ) hr hb (by omega) hδB hsmallB]
      have hmA := Nat.mul_le_mul_left ℓ hEA
      have hmB := Nat.mul_le_mul_left (r - 1 - ℓ) hEB
      have hlen : ℓ + (r - 1 - ℓ) = r - 1 := by omega
      nlinarith

theorem paired_exceptional_bound (r a b δA δB : ℕ) (hr : 5 ≤ r)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : a + b = r) (hle : a ≤ b)
    (hδA : 1 ≤ δA ∧ δA ≤ 2) (hδB : 1 ≤ δB ∧ δB ≤ 2) :
    lineSum (pairedMass r a δA) 0 (r - 2) +
      lineSum (pairedMass r b δB) 0 1 ≤ 2 * ((r - 2) * (r - 1) + 6) := by
  rw [paired_short_endpoint r a δA (r - 2) hr ha (by omega) hδA le_rfl,
    paired_short_endpoint r b δB 1 hr hb (by omega) hδB (by omega)]
  have h2a : 2 * a ≤ r := by omega
  have hm := Nat.mul_le_mul_right (r - 3) h2a
  have hr2 : r - 2 + 2 = r := by omega
  have hr1 : r - 1 + 1 = r := by omega
  have hr3 : r - 3 + 3 = r := by omega
  have hr5 : r - 5 + 5 = r := by omega
  have hEA : r + a - 1 + 1 = r + a := by omega
  have hEB : r + b - 1 + 1 = r + b := by omega
  nlinarith [sq_nonneg (r - 5)]

#print axioms paired_cross_bound
#print axioms paired_exceptional_bound
end QuorumAudit.MixedCircle
