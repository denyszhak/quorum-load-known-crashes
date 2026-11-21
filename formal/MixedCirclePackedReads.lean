import MixedCirclePairedReads

set_option maxHeartbeats 1000000

namespace QuorumAudit.MixedCircle
noncomputable section
open Finset
open scoped BigOperators

def packedWeight (E : Finset ℕ) (U V j : ℕ) : ℕ := if j ∈ E then U else V

def packedReadDistribution (r k b : ℕ) (E : Finset ℕ) (U V : ℕ) : NatDistribution ℕ := {
  entries := (List.range k).map (fun j => (blockInterval b r j, packedWeight E U V j))
  scale := E.card * U + (k - E.card) * V }

theorem packed_weight_bound (E : Finset ℕ) (U V j : ℕ) (hUV : U ≤ V) :
    packedWeight E U V j ≤ V := by unfold packedWeight; split_ifs <;> omega

theorem packed_normalized (r k b : ℕ) (E : Finset ℕ) (U V : ℕ) (hE : E ⊆ range k) :
    ((packedReadDistribution r k b E U V).entries.map Prod.snd).sum =
      (packedReadDistribution r k b E U V).scale := by
  change (((List.range k).map (fun j => (blockInterval b r j, packedWeight E U V j))).map Prod.snd).sum = _
  rw [List.map_map, list_range_sum]
  simp only [Function.comp_def]
  unfold packedWeight
  rw [sum_ite]
  have hfilter : (range k).filter (fun j => j ∈ E) = E := by
    ext j
    simp only [mem_filter]
    constructor
    · exact And.right
    · intro hj; exact ⟨hE hj, hj⟩
  have hcount := card_filter_add_card_filter_not (s := range k) (p := fun j => j ∈ E)
  rw [hfilter, card_range] at hcount
  have hc : ((range k).filter (fun j => ¬ j ∈ E)).card = k - E.card := by omega
  simp only [sum_const, smul_eq_mul, hfilter, hc]
  rfl

theorem packed_degree (r k b i : ℕ) (E : Finset ℕ) (U V : ℕ) :
    (packedReadDistribution r k b E U V).degree i = tileMass b r k (packedWeight E U V) i := by
  unfold NatDistribution.degree packedReadDistribution
  rw [List.map_map, list_range_sum]
  simp only [Function.comp_def, blockInterval, mem_Ico]
  rfl

theorem packed_valid (n r k b : ℕ) (E : Finset ℕ) (U V : ℕ)
    (hr : 0 < r) (hk : 0 < k) (hE : E ⊆ range k) (hU : 0 < U) (hV : 0 < V)
    (F : Finset ℕ) (hroom : b + k * r ≤ n)
    (hlive : ∀ i ∈ Ico b (b + k * r), i ∉ F) :
    (packedReadDistribution r k b E U V).Valid (natReads n r) (range n) F := by
  have hnpos : 0 < n := by have hp := Nat.mul_pos hk hr; omega
  letI : NeZero n := ⟨ne_of_gt hnpos⟩
  have hEc : E.card ≤ k := by simpa using card_le_card hE
  refine ⟨?_, ?_, packed_normalized r k b E U V hE⟩
  · change 0 < E.card * U + (k - E.card) * V
    by_cases he : E.card = 0
    · rw [he]; simpa using Nat.mul_pos hk hV
    · have hp := Nat.mul_pos (show 0 < E.card by omega) hU
      omega
  · intro e he
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp he
    have hjk : j + 1 ≤ k := by have := List.mem_range.mp hj; omega
    have hm := Nat.mul_le_mul_right r hjk
    refine ⟨blockInterval_member (n := n) r b j hr (by omega), ?_⟩
    intro i hi
    have hip := mem_Ico.mp hi
    refine mem_sdiff.mpr ⟨mem_range.mpr (by omega), ?_⟩
    apply hlive i
    exact mem_Ico.mpr ⟨by omega, by omega⟩

theorem tile_point_bound (b r k : ℕ) (w : ℕ → ℕ) (V i : ℕ)
    (hr : 0 < r) (hw : ∀ j, w j ≤ V) : tileMass b r k w i ≤ V := by
  rw [tileMass_eval b r k w hr]
  split_ifs
  · exact hw _
  · exact Nat.zero_le _

theorem tile_margin_prefix_bound (r k b l ℓ : ℕ) (w : ℕ → ℕ) (V : ℕ)
    (hr : 0 < r) (hw : ∀ j, w j ≤ V) :
    lineSum (tileMass (b + l) r k w) b ℓ ≤ (ℓ - l) * V := by
  have hp : ∀ j ∈ range ℓ, tileMass (b + l) r k w (b + j) ≤ if l ≤ j then V else 0 := by
    intro j _
    by_cases hj : l ≤ j
    · rw [if_pos hj]; exact tile_point_bound _ _ _ _ _ _ hr hw
    · rw [if_neg hj, tileMass_eval _ _ _ _ hr, if_neg (by omega)]
  have hh := sum_le_sum hp
  rw [← sum_filter] at hh
  have he : (range ℓ).filter (fun j => l ≤ j) = Ico l ℓ := by
    ext j
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [he] at hh
  simpa [lineSum] using hh

theorem tile_low_prefix (r k b ℓ : ℕ) (w : ℕ → ℕ) (U : ℕ)
    (hr : 0 < r) (hk : 0 < k) (hℓ : ℓ ≤ r) (hw : w 0 = U) :
    lineSum (tileMass b r k w) b ℓ = ℓ * U := by
  have hkr : r ≤ k * r := by simpa using Nat.mul_le_mul_right r (show 1 ≤ k by omega)
  have hp : ∀ j ∈ range ℓ, tileMass b r k w (b + j) = U := by
    intro j hj
    have hjr : j < r := by have := mem_range.mp hj; omega
    rw [tileMass_eval _ _ _ _ hr, if_pos (by omega), Nat.add_sub_cancel_left,
      Nat.div_eq_of_lt hjr, hw]
  unfold lineSum
  rw [sum_congr rfl hp]
  simp

theorem tile_suffix_reflection (r k l t ℓ : ℕ) (w : ℕ → ℕ)
    (hl : l ≤ t) (hℓ : ℓ ≤ k * r + t) :
    lineSum (tileMass l r k w) (k * r + t - ℓ) ℓ =
      lineSum (tileMass (t - l) r k (fun j => w (k - 1 - j))) 0 ℓ := by
  unfold lineSum
  conv_lhs => rw [← sum_range_reverse ℓ (fun j => tileMass l r k w (k * r + t - ℓ + j))]
  apply sum_congr rfl
  intro j hj
  have hjℓ := mem_range.mp hj
  have he : k * r + t - ℓ + (ℓ - 1 - j) = k * r + t - 1 - j := by omega
  rw [he, tileMass_reflect l r k (k * r + t) j w (by omega) (by omega)]
  have hb : k * r + t - (l + k * r) = t - l := by omega
  rw [hb, zero_add]

#print axioms packed_normalized
#print axioms packed_valid
#print axioms tile_margin_prefix_bound
#print axioms tile_low_prefix
#print axioms tile_suffix_reflection
end
end QuorumAudit.MixedCircle
