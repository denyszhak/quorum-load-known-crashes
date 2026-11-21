import MixedCircleBufferedParameters

set_option maxHeartbeats 2000000

namespace QuorumAudit.MixedCircle
noncomputable section
open Finset
open scoped BigOperators

def endReads (k t : ℕ) : Finset ℕ :=
  (range k).filter (fun j => (j = 0 ∧ t / 2 = 0) ∨ (j + 1 = k ∧ t = t / 2))

theorem end_reads_subset (k t : ℕ) : endReads k t ⊆ range k := filter_subset _ _

theorem end_reads_card (k t : ℕ) : (endReads k t).card ≤ 2 := by
  have hs : endReads k t ⊆ {0, k - 1} := by
    intro j hj
    have hh := (mem_filter.mp hj).2
    simp only [mem_insert, mem_singleton]
    omega
  exact (card_le_card hs).trans (card_insert_le _ _ |>.trans (by simp))

theorem end_reads_empty (k t : ℕ) (ht : 4 ≤ t) : endReads k t = ∅ := by
  ext j
  simp only [endReads, mem_filter, Finset.notMem_empty, iff_false]
  omega

theorem end_reads_total (r kA kB tA tB : ℕ) (hr : 10 ≤ r)
    (ht : tA + tB = r - 3) : (endReads kA tA).card + (endReads kB tB).card ≤ 2 := by
  have hh := buffered_margin_dichotomy r tA tB hr ht
  rcases hh with hh | hh
  · rw [end_reads_empty kA tA (by omega), card_empty, zero_add]
    exact end_reads_card _ _
  · rw [end_reads_empty kB tB (by omega), card_empty, add_zero]
    exact end_reads_card _ _

def bufferedArc (r k t b U V : ℕ) : ℕ → ℕ :=
  tileMass (b + t / 2) r k (packedWeight (endReads k t) U V)

theorem buffered_arc_zero_left (r k t b U V i : ℕ) (hr : 0 < r) (hi : i < b) :
    bufferedArc r k t b U V i = 0 := by
  rw [bufferedArc, tileMass_eval _ _ _ _ hr, if_neg (by omega)]

theorem buffered_arc_zero_right (r k t b U V i : ℕ) (hr : 0 < r)
    (hi : b + k * r + t ≤ i) : bufferedArc r k t b U V i = 0 := by
  have ht : t / 2 ≤ t := Nat.div_le_self _ _
  rw [bufferedArc, tileMass_eval _ _ _ _ hr, if_neg (by omega)]

theorem buffered_arc_point (r k t b U V i : ℕ) (hr : 0 < r) (hUV : U ≤ V) :
    bufferedArc r k t b U V i ≤ V :=
  tile_point_bound _ _ _ _ _ _ hr (fun j => packed_weight_bound _ _ _ j hUV)

theorem tile_line_shift (r k b l s ℓ : ℕ) (w : ℕ → ℕ) :
    lineSum (tileMass (b + l) r k w) (b + s) ℓ = lineSum (tileMass l r k w) s ℓ := by
  unfold lineSum
  apply sum_congr rfl
  intro j _
  rw [Nat.add_assoc, tileMass_shift]
  simp

theorem buffered_arc_suffix (r k t b U V ℓ : ℕ) (hℓ : ℓ ≤ k * r + t) :
    lineSum (bufferedArc r k t b U V) (b + k * r + t - ℓ) ℓ =
      lineSum (tileMass (t - t / 2) r k
        (fun j => packedWeight (endReads k t) U V (k - 1 - j))) 0 ℓ := by
  have he : b + k * r + t - ℓ = b + (k * r + t - ℓ) := by omega
  rw [he, bufferedArc, tile_line_shift, tile_suffix_reflection _ _ _ _ _ _
    (Nat.div_le_self _ _) hℓ]

theorem lineSum_div (x : ℕ → ℕ) (h s ℓ : ℕ) :
    lineSum (fun i => (x i : ℝ) / h) s ℓ = ((lineSum x s ℓ : ℕ) : ℝ) / h := by
  simp only [lineSum, ← sum_div, Nat.cast_sum]

theorem cyclicSum_div (n : ℕ) (x : ℕ → ℕ) (h s ℓ : ℕ) :
    cyclicSum n (fun i => (x i : ℝ) / h) s ℓ = ((cyclicSum n x s ℓ : ℕ) : ℝ) / h := by
  simp only [cyclicSum, ← sum_div, Nat.cast_sum]

theorem scaled_tile_bound (r k b l ℓ U V h : ℕ) (w : ℕ → ℕ)
    (hr : 5 ≤ r) (hp : 0 < h) (hw : ∀ j, w j ≤ V)
    (hV : (V : ℝ) / h ≤ highBound r) :
    ((lineSum (tileMass (b + l) r k w) b ℓ : ℕ) : ℝ) / h ≤
      ((ℓ - l : ℕ) : ℝ) * highBound r := by
  have hh := tile_margin_prefix_bound r k b l ℓ w V (by omega) hw
  have hhR : ((lineSum (tileMass (b + l) r k w) b ℓ : ℕ) : ℝ) ≤
      ((ℓ - l : ℕ) : ℝ) * V := by exact_mod_cast hh
  have hpR : (0 : ℝ) < h := by exact_mod_cast hp
  calc
    _ ≤ (((ℓ - l : ℕ) : ℝ) * V) / h := div_le_div_of_nonneg_right hhR (le_of_lt hpR)
    _ = ((ℓ - l : ℕ) : ℝ) * ((V : ℝ) / h) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hV (Nat.cast_nonneg _)

theorem buffered_prefix_bounds (r k t b U V h ℓ : ℕ) (hr : 5 ≤ r) (hk : 0 < k)
    (hp : 0 < h) (hUV : U ≤ V) (hℓ : ℓ ≤ r - 1)
    (hU : (U : ℝ) / h = low r) (hV : (V : ℝ) / h ≤ highBound r) :
    ((lineSum (bufferedArc r k t b U V) b ℓ : ℕ) : ℝ) / h ≤
        ((ℓ - t / 2 : ℕ) : ℝ) * highBound r ∧
    (t / 2 = 0 ∨ ℓ = 0 →
      ((lineSum (bufferedArc r k t b U V) b ℓ : ℕ) : ℝ) / h ≤ (ℓ : ℝ) * low r) := by
  refine ⟨scaled_tile_bound r k b (t / 2) ℓ U V h _ hr hp
    (fun j => packed_weight_bound _ _ _ j hUV) hV, ?_⟩
  intro hm
  rcases hm with hm | rfl
  · have he : 0 ∈ endReads k t := by simp [endReads, hk, hm]
    have hw : packedWeight (endReads k t) U V 0 = U := by simp [packedWeight, he]
    rw [bufferedArc, hm, Nat.add_zero, tile_low_prefix _ _ _ _ _ _ (by omega) hk (by omega) hw]
    push_cast
    rw [mul_div_assoc, hU]
  · simp [lineSum]

theorem buffered_suffix_bounds (r k t b U V h ℓ : ℕ) (hr : 5 ≤ r) (hk : 0 < k)
    (hp : 0 < h) (hUV : U ≤ V) (hℓ : ℓ ≤ r - 1)
    (hU : (U : ℝ) / h = low r) (hV : (V : ℝ) / h ≤ highBound r) :
    ((lineSum (bufferedArc r k t b U V) (b + k * r + t - ℓ) ℓ : ℕ) : ℝ) / h ≤
        ((ℓ - (t - t / 2) : ℕ) : ℝ) * highBound r ∧
    (t - t / 2 = 0 ∨ ℓ = 0 →
      ((lineSum (bufferedArc r k t b U V) (b + k * r + t - ℓ) ℓ : ℕ) : ℝ) / h ≤
        (ℓ : ℝ) * low r) := by
  have hkr : r ≤ k * r := by simpa using Nat.mul_le_mul_right r (show 1 ≤ k by omega)
  rw [buffered_arc_suffix _ _ _ _ _ _ _ (by omega)]
  have hh := scaled_tile_bound r k 0 (t - t / 2) ℓ U V h
    (fun j => packedWeight (endReads k t) U V (k - 1 - j)) hr hp
    (fun j => packed_weight_bound _ _ _ _ hUV) hV
  simp only [zero_add] at hh
  refine ⟨hh, ?_⟩
  intro hm
  rcases hm with hm | rfl
  · have he : k - 1 ∈ endReads k t := by
      simp only [endReads, mem_filter, mem_range]
      exact ⟨by omega, Or.inr ⟨by omega, by have := Nat.div_le_self t 2; omega⟩⟩
    have hw : packedWeight (endReads k t) U V (k - 1 - 0) = U := by
      simp [packedWeight, he]
    rw [hm, tile_low_prefix _ _ _ _ _ _ (by omega) hk (by omega) hw]
    push_cast
    rw [mul_div_assoc, hU]
  · simp [lineSum]

#print axioms end_reads_total
#print axioms buffered_prefix_bounds
#print axioms buffered_suffix_bounds
end
end QuorumAudit.MixedCircle
