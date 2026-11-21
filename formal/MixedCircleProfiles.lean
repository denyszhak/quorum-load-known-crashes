import MixedCircleTiles

set_option maxHeartbeats 2000000

namespace QuorumAudit.MixedCircle
open Finset Circle
open scoped BigOperators

def pairedMass (r k δ i : ℕ) : ℕ :=
  tileMass 0 r (k - 1) (fun j => 2 * (k - 1 - j) + (r - k + 1)) i +
  tileMass (r - δ) r (k - 1) (fun j => 2 * (j + 1) + (r - k + 1)) i

theorem paired_weights_normalized (r k : ℕ) (hk : 2 ≤ k) (hkr : k ≤ r) :
    (range (k - 1)).sum (fun j => 2 * (k - 1 - j) + (r - k + 1)) +
    (range (k - 1)).sum (fun j => 2 * (j + 1) + (r - k + 1)) =
      2 * (k - 1) * (r + 1) := by
  have hsum : (range (k - 1)).sum (fun j =>
      (2 * (k - 1 - j) + (r - k + 1)) + (2 * (j + 1) + (r - k + 1))) =
      (range (k - 1)).sum (fun j => 2 * (k - 1 - j) + (r - k + 1)) +
      (range (k - 1)).sum (fun j => 2 * (j + 1) + (r - k + 1)) := by
    exact sum_add_distrib
  rw [← hsum]
  have he : ∀ j ∈ range (k - 1),
      (2 * (k - 1 - j) + (r - k + 1)) +
      (2 * (j + 1) + (r - k + 1)) = 2 * (r + 1) := by
    intro j hj
    have := mem_range.mp hj
    omega
  rw [sum_congr rfl he]
  simp
  ring

theorem paired_prefix (r k δ ℓ : ℕ) (hr : 3 ≤ r) (hk : 2 ≤ k)
    (hkr : k ≤ r) (hδ : 1 ≤ δ ∧ δ ≤ 2) (hℓ : ℓ ≤ r - δ) :
    (∑ i ∈ range ℓ, pairedMass r k δ i) = ℓ * (r + k - 1) := by
  have hprod : 2 * r ≤ k * r := Nat.mul_le_mul_right r hk
  have he : ∀ i ∈ range ℓ, pairedMass r k δ i = r + k - 1 := by
    intro i hi
    have hiℓ := mem_range.mp hi
    have hiL : i < k * r - δ := by omega
    rw [pairedMass, paired_tile_profile r k δ i hr hk hkr hδ hiL,
      ite_eq_left (Or.inl (by omega))]
  rw [sum_congr rfl he]
  simp

theorem sum_range_reverse {α : Type*} [AddCommMonoid α] (m : ℕ) (f : ℕ → α) :
    (∑ j ∈ range m, f (m - 1 - j)) = ∑ j ∈ range m, f j := by
  apply sum_bij (fun j _ => m - 1 - j)
  · intro j hj; apply mem_range.mpr; have := mem_range.mp hj; omega
  · intro i hi j hj hij
    have := mem_range.mp hi
    have := mem_range.mp hj
    omega
  · intro j hj
    refine ⟨m - 1 - j, mem_range.mpr (by have := mem_range.mp hj; omega), ?_⟩
    have := mem_range.mp hj
    omega
  · intros; rfl

theorem paired_prefix_near (r k δ : ℕ) (hr : 3 ≤ r) (hk : 2 ≤ k)
    (hkr : k ≤ r) (hδ : 1 ≤ δ ∧ δ ≤ 2) :
    (∑ i ∈ range (r - 1), pairedMass r k δ i) =
      if δ = 1 then (r - 1) * (r + k - 1)
      else (r - 2) * (r + k - 1) + (2 * r + 2) := by
  have hcases : δ = 1 ∨ δ = 2 := by omega
  rcases hcases with rfl | rfl
  · rw [ite_eq_left rfl]
    exact paired_prefix r k 1 (r - 1) hr hk hkr (by omega) le_rfl
  · rw [ite_eq_right (by decide : ¬ (2 : ℕ) = 1)]
    have hprod : 2 * r ≤ k * r := Nat.mul_le_mul_right r hk
    have hlast : r - 2 < (k - 1) * r := by
      have hlow : r ≤ (k - 1) * r := by
        simpa using Nat.mul_le_mul_right r (show 1 ≤ k - 1 by omega)
      omega
    have hp : pairedMass r k 2 (r - 2) = 2 * r + 2 := by
      rw [pairedMass, paired_tile_profile r k 2 (r - 2) hr hk hkr (by omega) (by omega)]
      rw [ite_eq_right (by omega), Nat.mod_eq_of_lt (by omega : r - 2 < r), ite_eq_left le_rfl]
    have hlen : r - 1 = (r - 2) + 1 := by omega
    conv_lhs => rw [hlen, sum_range_succ]
    rw [paired_prefix r k 2 (r - 2) hr hk hkr (by omega) le_rfl, hp]

theorem tileMass_reflect {α : Type*} [AddCommMonoid α]
    (b r m L i : ℕ) (w : ℕ → α) (hroom : b + m * r ≤ L) (hi : i < L) :
    tileMass b r m w (L - 1 - i) =
      tileMass (L - (b + m * r)) r m (fun j => w (m - 1 - j)) i := by
  unfold tileMass
  rw [← sum_range_reverse m (fun j =>
    if b + j * r ≤ L - 1 - i ∧ L - 1 - i < b + (j + 1) * r then w j else 0)]
  apply sum_congr rfl
  intro j hj
  have hjm := mem_range.mp hj
  have hjrev : m - 1 - j + j + 1 = m := by omega
  have hprod : (m - 1 - j) * r + j * r + r = m * r := by
    calc _ = (m - 1 - j + j + 1) * r := by ring
         _ = _ := by rw [hjrev]
  have hbase : L - (b + m * r) + (b + m * r) = L := Nat.sub_add_cancel hroom
  have hpoint : L - 1 - i + i + 1 = L := by omega
  have hnext : (j + 1) * r = j * r + r := by ring
  have hrevnext : (m - 1 - j + 1) * r = (m - 1 - j) * r + r := by ring
  have he : (b + (m - 1 - j) * r ≤ L - 1 - i ∧
      L - 1 - i < b + (m - 1 - j + 1) * r) ↔
      (L - (b + m * r) + j * r ≤ i ∧
       i < L - (b + m * r) + (j + 1) * r) := by
    rw [hnext, hrevnext]
    omega
  simp only [he]

theorem tileMass_congr {α : Type*} [AddCommMonoid α] (b r k i : ℕ) (w v : ℕ → α)
    (h : ∀ j < k, w j = v j) : tileMass b r k w i = tileMass b r k v i := by
  unfold tileMass
  apply sum_congr rfl
  intro j hj
  rw [h j (mem_range.mp hj)]

theorem paired_reflect (r k δ i : ℕ) (hr : 3 ≤ r) (hk : 2 ≤ k)
    (hkr : k ≤ r) (hδ : 1 ≤ δ ∧ δ ≤ 2) (hi : i < k * r - δ) :
    pairedMass r k δ (k * r - δ - 1 - i) = pairedMass r k δ i := by
  have hδr : δ ≤ r := by omega
  have hprod : (k - 1) * r + r = k * r := by
    calc _ = (k - 1 + 1) * r := by ring
         _ = _ := by rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
  have hbase1 : k * r - δ - (0 + (k - 1) * r) = r - δ := by omega
  have hbase2 : k * r - δ - (r - δ + (k - 1) * r) = 0 := by omega
  unfold pairedMass
  rw [tileMass_reflect _ _ _ _ _ _ (by omega) hi,
      tileMass_reflect _ _ _ _ _ _ (by omega) hi, hbase1, hbase2]
  have he1 : ∀ j < k - 1,
      2 * (k - 1 - (k - 1 - 1 - j)) + (r - k + 1) =
        2 * (j + 1) + (r - k + 1) := by intros; omega
  have he2 : ∀ j < k - 1,
      2 * (k - 1 - 1 - j + 1) + (r - k + 1) =
        2 * (k - 1 - j) + (r - k + 1) := by intros; omega
  rw [tileMass_congr _ _ _ _ _ _ he1, tileMass_congr _ _ _ _ _ _ he2, add_comm]

theorem paired_suffix (r k δ ℓ : ℕ) (hr : 3 ≤ r) (hk : 2 ≤ k)
    (hkr : k ≤ r) (hδ : 1 ≤ δ ∧ δ ≤ 2) (hℓ : ℓ ≤ r - δ) :
    (∑ i ∈ range ℓ, pairedMass r k δ (k * r - δ - 1 - i)) =
      ℓ * (r + k - 1) := by
  have hprod : 2 * r ≤ k * r := Nat.mul_le_mul_right r hk
  calc
    _ = ∑ i ∈ range ℓ, pairedMass r k δ i := by
      apply sum_congr rfl
      intro i hi
      apply paired_reflect r k δ i hr hk hkr hδ
      have := mem_range.mp hi
      omega
    _ = _ := paired_prefix r k δ ℓ hr hk hkr hδ hℓ

theorem sum_range_mod {α : Type*} [AddCommMonoid α] (r s : ℕ) (hr : 0 < r)
    (f : ℕ → α) : (∑ j ∈ range r, f ((s + j) % r)) = ∑ j ∈ range r, f j := by
  letI : NeZero r := ⟨ne_of_gt hr⟩
  apply sum_bij (fun j _ => (s + j) % r)
  · intro j _; exact mem_range.mpr (Nat.mod_lt _ hr)
  · intro i hi j hj hij
    have hc : ((s + i : ℕ) : ZMod r) = ((s + j : ℕ) : ZMod r) := by
      have := congrArg (fun v : ℕ => (v : ZMod r)) hij
      simpa using this
    simp only [Nat.cast_add] at hc
    exact cast_injective_below (mem_range.mp hi) (mem_range.mp hj) (add_left_cancel hc)
  · intro j hj
    let z : ZMod r := (j : ZMod r) - (s : ZMod r)
    refine ⟨z.val, mem_range.mpr (ZMod.val_lt z), ?_⟩
    have hc : ((s + z.val : ℕ) : ZMod r) = (j : ZMod r) := by simp [z]
    have hv := congrArg ZMod.val hc
    rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.mp hj)] at hv
    exact hv
  · intros; rfl

theorem high_residue_count (r δ s : ℕ) (hr : 0 < r) (hδ : δ ≤ r) :
    (∑ j ∈ range r, if r - δ ≤ (s + j) % r then (1 : ℕ) else 0) = δ := by
  rw [sum_range_mod r s hr (fun j => if r - δ ≤ j then (1 : ℕ) else 0)]
  rw [← sum_filter]
  have he : (range r).filter (fun j => r - δ ≤ j) = Ico (r - δ) r := by
    ext j
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [he]
  simp
  omega

theorem paired_window (r k δ s : ℕ) (hr : 3 ≤ r) (hk : 2 ≤ k)
    (hkr : k ≤ r) (hδ : 1 ≤ δ ∧ δ ≤ 2) (hs : s + r ≤ k * r - δ) :
    (∑ j ∈ range r, pairedMass r k δ (s + j)) ≤ 2 * r * r + 2 * δ := by
  have hpoint : ∀ j ∈ range r, pairedMass r k δ (s + j) ≤
      2 * r + 2 * (if r - δ ≤ (s + j) % r then 1 else 0) := by
    intro j hj
    have hjr := mem_range.mp hj
    rw [pairedMass, paired_tile_profile r k δ (s + j) hr hk hkr hδ (by omega)]
    split_ifs <;> omega
  have hb := sum_le_sum hpoint
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_range, smul_eq_mul] at hb
  rw [high_residue_count r δ s (by omega) (by omega)] at hb
  nlinarith

#print axioms paired_weights_normalized
#print axioms paired_prefix
#print axioms paired_reflect
#print axioms paired_suffix
#print axioms paired_window
end QuorumAudit.MixedCircle
