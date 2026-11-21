import MixedCirclePairedReads

set_option maxHeartbeats 2000000

namespace QuorumAudit.MixedCircle
open Finset
open scoped BigOperators

theorem paired_zero (r k δ i : ℕ) (hr : 3 ≤ r) (hk : 2 ≤ k)
    (hδ : δ ≤ r) (hi : k * r - δ ≤ i) : pairedMass r k δ i = 0 := by
  have hp : (k - 1) * r + r = k * r := by
    calc _ = (k - 1 + 1) * r := by ring
         _ = _ := by rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
  rw [pairedMass, tileMass_eval _ _ _ _ (by omega),
    tileMass_eval _ _ _ _ (by omega), if_neg (by omega), if_neg (by omega)]
  rfl

theorem paired_point_bound (r k δ i : ℕ) (hr : 3 ≤ r) (hk : 2 ≤ k)
    (hkr : k ≤ r) (hδ : 1 ≤ δ ∧ δ ≤ 2) : pairedMass r k δ i ≤ 2 * r + 2 := by
  by_cases hi : i < k * r - δ
  · rw [pairedMass, paired_tile_profile r k δ i hr hk hkr hδ hi]
    split_ifs <;> omega
  · rw [paired_zero r k δ i hr hk (by omega) (by omega)]
    omega

theorem paired_suffix_eq_prefix (r k δ ℓ : ℕ) (hr : 3 ≤ r) (hk : 2 ≤ k)
    (hkr : k ≤ r) (hδ : 1 ≤ δ ∧ δ ≤ 2) (hℓ : ℓ ≤ k * r - δ) :
    lineSum (pairedMass r k δ) (k * r - δ - ℓ) ℓ =
      lineSum (pairedMass r k δ) 0 ℓ := by
  unfold lineSum
  conv_lhs => rw [← sum_range_reverse ℓ
    (fun j => pairedMass r k δ (k * r - δ - ℓ + j))]
  apply sum_congr rfl
  intro j hj
  have hjℓ := mem_range.mp hj
  have he : k * r - δ - ℓ + (ℓ - 1 - j) = k * r - δ - 1 - j := by omega
  rw [he, paired_reflect r k δ j hr hk hkr hδ (by omega), zero_add]

theorem placed_zero_left (r k δ b i : ℕ) (hi : i < b) :
    placedMass r k δ b i = 0 := by simp [placedMass, show ¬ b ≤ i by omega]

theorem placed_zero_right (r k δ b i : ℕ) (hr : 3 ≤ r) (hk : 2 ≤ k)
    (hδ : δ ≤ r) (hi : b + (k * r - δ) ≤ i) : placedMass r k δ b i = 0 := by
  rw [placedMass, if_pos (by omega)]
  exact paired_zero r k δ (i - b) hr hk hδ (by omega)

theorem placed_point_bound (r k δ b i : ℕ) (hr : 3 ≤ r) (hk : 2 ≤ k)
    (hkr : k ≤ r) (hδ : 1 ≤ δ ∧ δ ≤ 2) : placedMass r k δ b i ≤ 2 * r + 2 := by
  unfold placedMass
  split_ifs
  · exact paired_point_bound r k δ _ hr hk hkr hδ
  · omega

theorem placed_line (r k δ b s ℓ : ℕ) :
    lineSum (placedMass r k δ b) (b + s) ℓ =
      lineSum (pairedMass r k δ) s ℓ := by
  unfold lineSum
  apply sum_congr rfl
  intro j _
  simp [placedMass, Nat.add_assoc]

theorem placed_line_before (r k δ b s ℓ : ℕ) (hs : s + ℓ ≤ b) :
    lineSum (placedMass r k δ b) s ℓ = 0 := by
  apply sum_eq_zero
  intro j hj
  apply placed_zero_left
  have := mem_range.mp hj
  omega

theorem placed_line_after (r k δ b s ℓ : ℕ) (hr : 3 ≤ r) (hk : 2 ≤ k)
    (hδ : δ ≤ r) (hs : b + (k * r - δ) ≤ s) :
    lineSum (placedMass r k δ b) s ℓ = 0 := by
  apply sum_eq_zero
  intro j _
  exact placed_zero_right r k δ b (s + j) hr hk hδ (by omega)

theorem placed_line_window (r k δ b s : ℕ) (hr : 3 ≤ r) (hk : 2 ≤ k)
    (hkr : k ≤ r) (hδ : 1 ≤ δ ∧ δ ≤ 2)
    (hs : b ≤ s) (hroom : s + r ≤ b + (k * r - δ)) :
    lineSum (placedMass r k δ b) s r ≤ 2 * r * r + 2 * δ := by
  rw [show s = b + (s - b) by omega, placed_line]
  apply paired_window r k δ (s - b) hr hk hkr hδ
  omega

theorem placed_prefix (r k δ b ℓ : ℕ) (hr : 3 ≤ r) (hk : 2 ≤ k)
    (hkr : k ≤ r) (hδ : 1 ≤ δ ∧ δ ≤ 2) (hℓ : ℓ ≤ r - δ) :
    lineSum (placedMass r k δ b) b ℓ = ℓ * (r + k - 1) := by
  have he := placed_line r k δ b 0 ℓ
  simp only [Nat.add_zero] at he
  rw [he]
  simpa [lineSum] using paired_prefix r k δ ℓ hr hk hkr hδ hℓ

theorem placed_suffix (r k δ b ℓ : ℕ) (hr : 3 ≤ r) (hk : 2 ≤ k)
    (hkr : k ≤ r) (hδ : 1 ≤ δ ∧ δ ≤ 2) (hℓ : ℓ ≤ r - δ) :
    lineSum (placedMass r k δ b) (b + (k * r - δ) - ℓ) ℓ = ℓ * (r + k - 1) := by
  have hp : 2 * r ≤ k * r := Nat.mul_le_mul_right r hk
  rw [show b + (k * r - δ) - ℓ = b + (k * r - δ - ℓ) by omega,
    placed_line, paired_suffix_eq_prefix r k δ ℓ hr hk hkr hδ (by omega)]
  simpa [lineSum] using paired_prefix r k δ ℓ hr hk hkr hδ hℓ

theorem placed_prefix_near (r k δ b : ℕ) (hr : 3 ≤ r) (hk : 2 ≤ k)
    (hkr : k ≤ r) (hδ : 1 ≤ δ ∧ δ ≤ 2) :
    lineSum (placedMass r k δ b) b (r - 1) =
      if δ = 1 then (r - 1) * (r + k - 1)
      else (r - 2) * (r + k - 1) + (2 * r + 2) := by
  have he := placed_line r k δ b 0 (r - 1)
  simp only [Nat.add_zero] at he
  rw [he]
  simpa [lineSum] using paired_prefix_near r k δ hr hk hkr hδ

theorem placed_suffix_near (r k δ b : ℕ) (hr : 3 ≤ r) (hk : 2 ≤ k)
    (hkr : k ≤ r) (hδ : 1 ≤ δ ∧ δ ≤ 2) :
    lineSum (placedMass r k δ b) (b + (k * r - δ) - (r - 1)) (r - 1) =
      if δ = 1 then (r - 1) * (r + k - 1)
      else (r - 2) * (r + k - 1) + (2 * r + 2) := by
  have hp : 2 * r ≤ k * r := Nat.mul_le_mul_right r hk
  rw [show b + (k * r - δ) - (r - 1) = b + (k * r - δ - (r - 1)) by omega,
    placed_line, paired_suffix_eq_prefix r k δ (r - 1) hr hk hkr hδ (by omega)]
  simpa [lineSum] using paired_prefix_near r k δ hr hk hkr hδ

#print axioms paired_point_bound
#print axioms placed_line_window
#print axioms placed_suffix_near
end QuorumAudit.MixedCircle
