import MixedCircleBufferedReads

set_option maxHeartbeats 3000000

namespace QuorumAudit.MixedCircle
noncomputable section
open Finset
open scoped BigOperators

structure BufferedProfile (n r d : ℕ) where
  kA : ℕ
  kB : ℕ
  tA : ℕ
  tB : ℕ
  h : ℕ
  U : ℕ
  V : ℕ
  μ : ℕ
  C : ℕ
  kA_pos : 0 < kA
  kB_pos : 0 < kB
  arcA : 1 + kA * r + tA = d
  arcB : d + 1 + kB * r + tB = n
  blocks : kA + kB = r - 1
  margins : tA + tB = r - 3
  scale_pos : 0 < h
  low_pos : 0 < U
  high_pos : 0 < V
  ordered : U ≤ V
  normalized : ((endReads kA tA).card + (endReads kB tB).card) * U +
    (r - 1 - ((endReads kA tA).card + (endReads kB tB).card)) * V = h
  low_eq : (U : ℝ) / h = low r
  high_le : (V : ℝ) / h ≤ highBound r
  mixture_eq : (μ : ℝ) = mixture r * h
  cap_eq : (C : ℝ) = cap r * h

theorem buffered_profile_exists (n r d kA kB tA tB : ℕ) (hr : 10 ≤ r)
    (hkA : 0 < kA) (hkB : 0 < kB)
    (hA : 1 + kA * r + tA = d) (hB : d + 1 + kB * r + tB = n)
    (hK : kA + kB = r - 1) (hT : tA + tB = r - 3) :
    Nonempty (BufferedProfile n r d) := by
  let e := (endReads kA tA).card + (endReads kB tB).card
  have he : e ≤ 2 := end_reads_total r kA kB tA tB hr hT
  obtain ⟨h, U, V, μ, C, hp, hU, hV, hUV, hn, hu, hv, hm, hc⟩ :=
    buffered_integer_parameters r e (by omega) he
  have hrR : (5 : ℝ) ≤ r := by exact_mod_cast (show 5 ≤ r by omega)
  exact ⟨⟨kA, kB, tA, tB, h, U, V, μ, C, hkA, hkB, hA, hB, hK, hT,
    hp, hU, hV, hUV, hn, hu,
    hv.le.trans (buffered_real_parameters r e hrR ⟨Nat.cast_nonneg _, by exact_mod_cast he⟩).2.2.1,
    hm, hc⟩⟩

namespace BufferedProfile
variable {n r d : ℕ} (P : BufferedProfile n r d)

def mass (i : ℕ) : ℕ :=
  bufferedArc r P.kA P.tA 1 P.U P.V i +
  bufferedArc r P.kB P.tB (d + 1) P.U P.V i

def value (i : ℕ) : ℝ := (P.mass i : ℝ) / P.h

theorem value_line (s ℓ : ℕ) : lineSum P.value s ℓ = ((lineSum P.mass s ℓ : ℕ) : ℝ) / P.h :=
  lineSum_div P.mass P.h s ℓ

theorem lineA (s ℓ : ℕ) (hr : 5 ≤ r) (hs : 1 ≤ s) (hroom : s + ℓ ≤ d) :
    lineSum P.mass s ℓ = lineSum (bufferedArc r P.kA P.tA 1 P.U P.V) s ℓ := by
  unfold lineSum mass
  apply sum_congr rfl
  intro j hj
  have hjℓ := mem_range.mp hj
  rw [buffered_arc_zero_left r P.kB P.tB (d + 1) P.U P.V (s + j) (by omega) (by omega), add_zero]

theorem lineB (s ℓ : ℕ) (hr : 5 ≤ r) (hs : d + 1 ≤ s) :
    lineSum P.mass s ℓ = lineSum (bufferedArc r P.kB P.tB (d + 1) P.U P.V) s ℓ := by
  unfold lineSum mass
  apply sum_congr rfl
  intro j _
  rw [buffered_arc_zero_right _ _ _ _ _ _ _ (by omega) (by have := P.arcA; omega), zero_add]

theorem point (i : ℕ) (hr : 5 ≤ r) : P.value i ≤ highBound r := by
  have hnat : P.mass i ≤ P.V := by
    unfold mass
    by_cases hi : i < d
    · rw [buffered_arc_zero_left r P.kB P.tB (d + 1) P.U P.V i (by omega) (by omega), add_zero]
      exact buffered_arc_point _ _ _ _ _ _ _ (by omega) P.ordered
    · rw [buffered_arc_zero_right _ _ _ _ _ _ _ (by omega) (by have := P.arcA; omega), zero_add]
      exact buffered_arc_point _ _ _ _ _ _ _ (by omega) P.ordered
  have hh : (P.mass i : ℝ) ≤ P.V := by exact_mod_cast hnat
  exact (div_le_div_of_nonneg_right hh (Nat.cast_nonneg P.h)).trans P.high_le

theorem zero_failures (hr : 5 ≤ r) : P.value 0 = 0 ∧ P.value d = 0 := by
  have h0 : P.mass 0 = 0 := by
    unfold mass
    rw [buffered_arc_zero_left _ _ _ _ _ _ _ (by omega) (by omega),
      buffered_arc_zero_left _ _ _ _ _ _ _ (by omega) (by omega), zero_add]
  have hd : P.mass d = 0 := by
    unfold mass
    rw [buffered_arc_zero_right _ _ _ _ _ _ _ (by omega) (by have := P.arcA; omega),
      buffered_arc_zero_left _ _ _ _ _ _ _ (by omega) (by omega), zero_add]
  simp [value, h0, hd]

theorem prefixA (ℓ : ℕ) (hr : 5 ≤ r) (hℓ : ℓ ≤ r - 1) :
    lineSum P.value 1 ℓ ≤ ((ℓ - P.tA / 2 : ℕ) : ℝ) * highBound r ∧
    (P.tA / 2 = 0 ∨ ℓ = 0 → lineSum P.value 1 ℓ ≤ (ℓ : ℝ) * low r) := by
  have hkr : r ≤ P.kA * r := by simpa using Nat.mul_le_mul_right r P.kA_pos
  rw [P.value_line]
  rw [P.lineA 1 ℓ hr le_rfl (by have := P.arcA; omega)]
  exact buffered_prefix_bounds _ _ _ _ _ _ _ _ hr P.kA_pos P.scale_pos P.ordered hℓ P.low_eq P.high_le

theorem prefixB (ℓ : ℕ) (hr : 5 ≤ r) (hℓ : ℓ ≤ r - 1) :
    lineSum P.value (d + 1) ℓ ≤ ((ℓ - P.tB / 2 : ℕ) : ℝ) * highBound r ∧
    (P.tB / 2 = 0 ∨ ℓ = 0 → lineSum P.value (d + 1) ℓ ≤ (ℓ : ℝ) * low r) := by
  rw [P.value_line]
  rw [P.lineB (d + 1) ℓ hr le_rfl]
  exact buffered_prefix_bounds _ _ _ _ _ _ _ _ hr P.kB_pos P.scale_pos P.ordered hℓ P.low_eq P.high_le

theorem suffixA (ℓ : ℕ) (hr : 5 ≤ r) (hℓ : ℓ ≤ r - 1) :
    lineSum P.value (d - ℓ) ℓ ≤ ((ℓ - (P.tA - P.tA / 2) : ℕ) : ℝ) * highBound r ∧
    (P.tA - P.tA / 2 = 0 ∨ ℓ = 0 → lineSum P.value (d - ℓ) ℓ ≤ (ℓ : ℝ) * low r) := by
  have hkr : r ≤ P.kA * r := by simpa using Nat.mul_le_mul_right r P.kA_pos
  rw [P.value_line]
  rw [P.lineA (d - ℓ) ℓ hr (by have := P.arcA; omega) (by have := P.arcA; omega)]
  have hh := buffered_suffix_bounds r P.kA P.tA 1 P.U P.V P.h ℓ
    hr P.kA_pos P.scale_pos P.ordered hℓ P.low_eq P.high_le
  have he : 1 + P.kA * r + P.tA - ℓ = d - ℓ := by have := P.arcA; omega
  rwa [he] at hh

theorem suffixB (ℓ : ℕ) (hr : 5 ≤ r) (hℓ : ℓ ≤ r - 1) :
    lineSum P.value (n - ℓ) ℓ ≤ ((ℓ - (P.tB - P.tB / 2) : ℕ) : ℝ) * highBound r ∧
    (P.tB - P.tB / 2 = 0 ∨ ℓ = 0 → lineSum P.value (n - ℓ) ℓ ≤ (ℓ : ℝ) * low r) := by
  have hkr : r ≤ P.kB * r := by simpa using Nat.mul_le_mul_right r P.kB_pos
  rw [P.value_line]
  rw [P.lineB (n - ℓ) ℓ hr (by have := P.arcB; omega)]
  have hh := buffered_suffix_bounds r P.kB P.tB (d + 1) P.U P.V P.h ℓ
    hr P.kB_pos P.scale_pos P.ordered hℓ P.low_eq P.high_le
  have he : d + 1 + P.kB * r + P.tB - ℓ = n - ℓ := by have := P.arcB; omega
  rwa [he] at hh

theorem windows (hr : 5 ≤ r) (s : ℕ) (hs : s < n) :
    ((natArc n r s ∩ {0, d}).card = 0 ∧ cyclicSum n P.value s r ≤ ((r : ℝ)^2 + 2) / den r) ∨
    ((natArc n r s ∩ {0, d}).card = 1 ∧ cyclicSum n P.value s r ≤ ordinary r / den r) := by
  have hkrA : r ≤ P.kA * r := by simpa using Nat.mul_le_mul_right r P.kA_pos
  have hkrB : r ≤ P.kB * r := by simpa using Nat.mul_le_mul_right r P.kB_pos
  have hpoint : ∀ u, lineSum P.value u r ≤ (r : ℝ) * highBound r := by
    intro u
    have hh := sum_le_sum (fun j (_ : j ∈ range r) => P.point (u + j) hr)
    simpa [lineSum] using hh
  have hrR : (5 : ℝ) ≤ r := by exact_mod_cast hr
  apply far_windows_bound n r d P.value _ _ (by omega) (by have := P.arcA; omega)
    (by have := P.arcB; omega) (P.zero_failures hr).1 (P.zero_failures hr).2
  · intro u _ _
    exact (hpoint u).trans (buffered_window_bounds r hrR).1
  · intro u _ _
    exact (hpoint u).trans (buffered_window_bounds r hrR).1
  · intro ℓ hℓ
    have hA := P.suffixB ℓ hr hℓ
    have hB := P.prefixA (r - 1 - ℓ) hr (by omega)
    exact buffered_cross_bound r ℓ (P.tB - P.tB / 2) (P.tA / 2) _ _ hr hℓ hA.1 hB.1 hA.2 hB.2
  · intro ℓ hℓ
    have hA := P.suffixA ℓ hr hℓ
    have hB := P.prefixB (r - 1 - ℓ) hr (by omega)
    exact buffered_cross_bound r ℓ (P.tA - P.tA / 2) (P.tB / 2) _ _ hr hℓ hA.1 hB.1 hA.2 hB.2
  · exact hs

theorem exceptional_window (hr : 10 ≤ r) (s : ℕ) (hs : s < n)
    (he : s = n - 1 ∨ s = n - r + 2) :
    cyclicSum n P.value s r ≤ exceptional r / den r := by
  have hkrA : r ≤ P.kA * r := by simpa using Nat.mul_le_mul_right r P.kA_pos
  have hkrB : r ≤ P.kB * r := by simpa using Nat.mul_le_mul_right r P.kB_pos
  have hzero := (P.zero_failures (by omega)).1
  have htA := Nat.div_le_self P.tA 2
  have htB := Nat.div_le_self P.tB 2
  have hmargin := buffered_margin_dichotomy r P.tA P.tB hr P.margins
  have hmargin' : 2 ≤ P.tA / 2 ∨ 2 ≤ P.tB - P.tB / 2 := by omega
  have hA := P.prefixA (r - 2) (by omega) (by omega)
  have hB := P.suffixB 1 (by omega) (by omega)
  have hA' := P.suffixB (r - 2) (by omega) (by omega)
  have hstart : n - (r - 2) = n - r + 2 := by have := P.arcB; omega
  rw [hstart] at hA'
  have hB' := P.prefixA 1 (by omega) (by omega)
  rw [cyclicSum_wrap n P.value s r hs (by have := P.arcB; omega) (by rcases he with he | he <;> omega)]
  rw [lineSum_split_zero P.value 0 (r - (n - s)) 0 (by omega)
    (by rcases he with he | he <;> omega) hzero]
  simp only [lineSum, range_zero, sum_empty, zero_add, Nat.sub_zero]
  change lineSum P.value s (n - s) + lineSum P.value 1 (r - (n - s) - 1) ≤ _
  rcases he with rfl | rfl
  · have hns : n - (n - 1) = 1 := by have := P.arcB; omega
    have hrr : r - 1 - 1 = r - 2 := by omega
    rw [hns, hrr, add_comm]
    exact buffered_exceptional_bound r (P.tA / 2) (P.tB - P.tB / 2) _ _ (by omega)
      hmargin' hA.1 hB.1 (fun hm => hA.2 (Or.inl hm))
  · have hns : n - (n - r + 2) = r - 2 := by have := P.arcB; omega
    have hrr : r - (r - 2) - 1 = 1 := by omega
    rw [hns, hrr]
    exact buffered_exceptional_bound r (P.tB - P.tB / 2) (P.tA / 2) _ _ (by omega)
      (by omega) hA'.1 hB'.1 (fun hm => hA'.2 (Or.inl hm))

end BufferedProfile
#print axioms buffered_profile_exists
#print axioms BufferedProfile.windows
#print axioms BufferedProfile.exceptional_window
end
end QuorumAudit.MixedCircle
