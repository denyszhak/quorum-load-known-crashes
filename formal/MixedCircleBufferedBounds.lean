import MixedCirclePackedReads
import MixedCircleArithmetic

set_option maxHeartbeats 1500000

namespace QuorumAudit.MixedCircle
noncomputable section
open Finset
open scoped BigOperators

def bufferedHigh (r e : ℝ) : ℝ := (1 - e * low r) / (r - 1 - e)

theorem buffered_real_parameters (r e : ℝ) (hr : 5 ≤ r) (he : 0 ≤ e ∧ e ≤ 2) :
    0 < low r ∧ low r ≤ bufferedHigh r e ∧
    bufferedHigh r e ≤ highBound r ∧
    e * low r + (r - 1 - e) * bufferedHigh r e = 1 := by
  have hp : 0 < r - 1 := by linarith
  have hm : 0 < r - 1 - e := by linarith
  have h3 : 0 < r - 3 := by linarith
  obtain ⟨hm0, hm1, _⟩ := parameters r hr
  have hu : 0 < low r := div_pos (by linarith) hp
  have hdiff : bufferedHigh r e - low r = mixture r / (r - 1 - e) := by
    unfold bufferedHigh low
    field_simp
    ring
  have hupper : highBound r - bufferedHigh r e =
      mixture r * (2 - e) / ((r - 3) * (r - 1 - e)) := by
    rw [highBound_formula r hr]
    unfold bufferedHigh low
    field_simp
    ring
  refine ⟨hu, ?_, ?_, ?_⟩
  · have hh := div_nonneg hm0 (le_of_lt hm)
    linarith
  · have hh : 0 ≤ mixture r * (2 - e) / ((r - 3) * (r - 1 - e)) :=
      div_nonneg (mul_nonneg hm0 (by linarith)) (le_of_lt (mul_pos h3 hm))
    linarith
  · unfold bufferedHigh
    field_simp
    ring

theorem low_mass (r : ℝ) (hr : 5 ≤ r) :
    (r - 1) * low r = ordinary r / den r := by
  have hd := ne_of_gt (den_pos r hr)
  have hp : r - 1 ≠ 0 := by linarith
  unfold low mixture ordinary
  field_simp
  unfold den
  ring

theorem high_nonnegative (r : ℝ) (hr : 5 ≤ r) : 0 ≤ highBound r := by
  have hh := buffered_real_parameters r 0 hr (by norm_num)
  linarith [hh.1, hh.2.1, hh.2.2.1]

theorem high_point_bound (r : ℝ) (hr : 5 ≤ r) : highBound r ≤ (r + 1) / den r := by
  have hd := den_pos r hr
  have hw := (buffered_window_bounds r hr).1
  have hn : r ^ 2 + 2 ≤ r * (r + 1) := by nlinarith
  have hh := div_le_div_of_nonneg_right hn (le_of_lt hd)
  have he : r * (r + 1) / den r = r * ((r + 1) / den r) := by ring
  rw [he] at hh
  nlinarith

theorem buffered_cross_bound (r ℓ mA mB : ℕ) (A B : ℝ) (hr : 5 ≤ r) (hℓ : ℓ ≤ r - 1)
    (hA : A ≤ ((ℓ - mA : ℕ) : ℝ) * highBound r)
    (hB : B ≤ ((r - 1 - ℓ - mB : ℕ) : ℝ) * highBound r)
    (hlowA : mA = 0 ∨ ℓ = 0 → A ≤ (ℓ : ℝ) * low r)
    (hlowB : mB = 0 ∨ r - 1 - ℓ = 0 → B ≤ ((r - 1 - ℓ : ℕ) : ℝ) * low r) :
    A + B ≤ ordinary r / den r := by
  have hrR : (5 : ℝ) ≤ r := by exact_mod_cast hr
  have hV := high_nonnegative (r : ℝ) hrR
  by_cases hblank : (0 < ℓ ∧ 0 < mA) ∨ (0 < r - 1 - ℓ ∧ 0 < mB)
  · have hclip : (ℓ - mA) + (r - 1 - ℓ - mB) ≤ r - 2 := by omega
    have hc : (((ℓ - mA) + (r - 1 - ℓ - mB) : ℕ) : ℝ) ≤ (r : ℝ) - 2 := by
      have hh : (((ℓ - mA) + (r - 1 - ℓ - mB) : ℕ) : ℝ) ≤ ((r - 2 : ℕ) : ℝ) := by exact_mod_cast hclip
      simpa only [Nat.cast_sub (by omega : 2 ≤ r), Nat.cast_ofNat] using hh
    calc
      A + B ≤ (((ℓ - mA) + (r - 1 - ℓ - mB) : ℕ) : ℝ) * highBound r := by
        push_cast
        nlinarith only [hA, hB]
      _ ≤ ((r : ℝ) - 2) * highBound r := mul_le_mul_of_nonneg_right hc hV
      _ ≤ ordinary r / den r := (buffered_window_bounds (r : ℝ) hrR).2.1
  · have hlA := hlowA (by omega)
    have hlB := hlowB (by omega)
    have he : (ℓ : ℝ) + ((r - 1 - ℓ : ℕ) : ℝ) = (r : ℝ) - 1 := by
      have hh : ℓ + (r - 1 - ℓ) = r - 1 := by omega
      have hc := congrArg (fun j : ℕ => (j : ℝ)) hh
      simpa only [Nat.cast_add, Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one] using hc
    calc A + B ≤ (ℓ : ℝ) * low r + ((r - 1 - ℓ : ℕ) : ℝ) * low r := add_le_add hlA hlB
         _ = ((r : ℝ) - 1) * low r := by rw [← add_mul, he]
         _ = ordinary r / den r := low_mass (r : ℝ) hrR

theorem buffered_exceptional_bound (r mA mB : ℕ) (A B : ℝ) (hr : 5 ≤ r)
    (hm : 2 ≤ mA ∨ 2 ≤ mB)
    (hA : A ≤ ((r - 2 - mA : ℕ) : ℝ) * highBound r)
    (hB : B ≤ ((1 - mB : ℕ) : ℝ) * highBound r)
    (hlowA : mA = 0 → A ≤ ((r - 2 : ℕ) : ℝ) * low r) :
    A + B ≤ exceptional r / den r := by
  have hrR : (5 : ℝ) ≤ r := by exact_mod_cast hr
  have hV := high_nonnegative (r : ℝ) hrR
  by_cases hz : mA = 0
  · have hmb : 2 ≤ mB := by omega
    have hclip : 1 - mB = 0 := by omega
    rw [hclip, Nat.cast_zero, zero_mul] at hB
    have hl := hlowA hz
    have hr2 : ((r - 2 : ℕ) : ℝ) = (r : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ r), Nat.cast_ofNat]
    rw [hr2] at hl
    exact (show A + B ≤ ((r : ℝ) - 2) * low r by linarith).trans
      (low_exceptional_bound (r : ℝ) hrR)
  · have hclip : (r - 2 - mA) + (1 - mB) ≤ r - 3 := by omega
    have hc : (((r - 2 - mA) + (1 - mB) : ℕ) : ℝ) ≤ (r : ℝ) - 3 := by
      have hh : (((r - 2 - mA) + (1 - mB) : ℕ) : ℝ) ≤ ((r - 3 : ℕ) : ℝ) := by exact_mod_cast hclip
      simpa only [Nat.cast_sub (by omega : 3 ≤ r), Nat.cast_ofNat] using hh
    calc
      A + B ≤ (((r - 2 - mA) + (1 - mB) : ℕ) : ℝ) * highBound r := by
        push_cast
        nlinarith only [hA, hB]
      _ ≤ ((r : ℝ) - 3) * highBound r := mul_le_mul_of_nonneg_right hc hV
      _ ≤ exceptional r / den r := (buffered_window_bounds (r : ℝ) hrR).2.2

theorem buffered_margin_dichotomy (r tA tB : ℕ) (hr : 10 ≤ r)
    (ht : tA + tB = r - 3) : 2 ≤ tA / 2 ∨ 2 ≤ tB / 2 := by omega

#print axioms buffered_real_parameters
#print axioms buffered_cross_bound
#print axioms buffered_exceptional_bound
#print axioms buffered_margin_dichotomy
end
end QuorumAudit.MixedCircle
