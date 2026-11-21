import Arithmetic

namespace QuorumAudit.MixedCircle
noncomputable section

def den (r : ℝ) : ℝ := (r - 2) * (r + 1)
def cap (r : ℝ) : ℝ := (2 * r - 1) / den r
def mixture (r : ℝ) : ℝ := (r - 5) / den r
def low (r : ℝ) : ℝ := (1 - mixture r) / (r - 1)
def highBound (r : ℝ) : ℝ :=
  (den r * (r - 3) + 2 * (r - 5)) / (den r * (r - 1) * (r - 3))
def ordinary (r : ℝ) : ℝ := r ^ 2 - 2 * r + 3
def exceptional (r : ℝ) : ℝ := r ^ 2 - 3 * r + 8

theorem den_pos (r : ℝ) (hr : 5 ≤ r) : 0 < den r := by
  unfold den
  exact mul_pos (by linarith) (by linarith)

theorem parameters (r : ℝ) (hr : 5 ≤ r) :
    0 ≤ mixture r ∧ mixture r < 1 ∧ cap r ≤ 1 - mixture r := by
  have hd := den_pos r hr
  refine ⟨div_nonneg (by linarith) (le_of_lt hd), ?_, ?_⟩
  · unfold mixture
    apply (div_lt_one hd).mpr
    unfold den
    nlinarith [sq_nonneg (r - 2)]
  · unfold cap mixture
    apply (le_sub_iff_add_le).mpr
    rw [← add_div]
    apply (div_le_one hd).mpr
    unfold den
    nlinarith [sq_nonneg (r - 2)]

theorem residual_mass (r : ℝ) (hr : 5 ≤ r) :
    (r ^ 2 - 3) * cap r - r - r * mixture r = (r + 1) * (1 - mixture r) := by
  have hd := ne_of_gt (den_pos r hr)
  unfold cap mixture
  field_simp
  unfold den
  ring

theorem residual_positive (r x y : ℝ) (hr : 5 ≤ r)
    (hx : x ≤ (r + 1) / den r) (hy : y ≤ mixture r) :
    3 / den r ≤ cap r - x - y := by
  have hd := ne_of_gt (den_pos r hr)
  have heq : cap r - (r + 1) / den r - mixture r = 3 / den r := by
    unfold cap mixture
    field_simp
    ring
  linarith

theorem highBound_formula (r : ℝ) (hr : 5 ≤ r) :
    highBound r = 1 / (r - 1) +
      2 * mixture r / ((r - 1) * (r - 3)) := by
  have hd := ne_of_gt (den_pos r hr)
  have h1 : r - 1 ≠ 0 := by linarith
  have h3 : r - 3 ≠ 0 := by linarith
  unfold highBound mixture
  field_simp

theorem buffered_bound (r a B : ℝ) (hr : 5 ≤ r)
    (hdiff : 0 ≤ B * (r - 1) * (r - 3) -
      a * (den r * (r - 3) + 2 * (r - 5))) :
    a * highBound r ≤ B / den r := by
  have hd := den_pos r hr
  have hp : 0 < den r * (r - 1) * (r - 3) :=
    mul_pos (mul_pos hd (by linarith)) (by linarith)
  unfold highBound
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hp hd).mpr
  apply sub_nonneg.mp
  calc
    0 ≤ den r * (B * (r - 1) * (r - 3) -
      a * (den r * (r - 3) + 2 * (r - 5))) := mul_nonneg (le_of_lt hd) hdiff
    _ = B * (den r * (r - 1) * (r - 3)) -
      (a * (den r * (r - 3) + 2 * (r - 5))) * den r := by ring

theorem buffered_window_bounds (r : ℝ) (hr : 5 ≤ r) :
    r * highBound r ≤ (r ^ 2 + 2) / den r ∧
    (r - 2) * highBound r ≤ ordinary r / den r ∧
    (r - 3) * highBound r ≤ exceptional r / den r := by
  refine ⟨buffered_bound r r (r ^ 2 + 2) hr ?_,
    buffered_bound r (r - 2) (ordinary r) hr ?_,
    buffered_bound r (r - 3) (exceptional r) hr ?_⟩
  · have heq : (r ^ 2 + 2) * (r - 1) * (r - 3) -
        r * (den r * (r - 3) + 2 * (r - 5)) = 2 * (r - 1) ^ 2 + 4 := by
      unfold den
      ring
    rw [heq]
    positivity
  · have heq : ordinary r * (r - 1) * (r - 3) -
        (r - 2) * (den r * (r - 3) + 2 * (r - 5)) =
          3 * (r - 5) ^ 2 + 22 * (r - 5) + 36 := by
      unfold ordinary den
      ring
    rw [heq]
    have : 0 ≤ r - 5 := by linarith
    positivity
  · have heq : exceptional r * (r - 1) * (r - 3) -
        (r - 3) * (den r * (r - 3) + 2 * (r - 5)) = (r - 3) * (8 * r - 4) := by
      unfold exceptional den
      ring
    rw [heq]
    exact mul_nonneg (by linarith) (by linarith)

theorem low_exceptional_bound (r : ℝ) (hr : 5 ≤ r) :
    (r - 2) * low r ≤ exceptional r / den r := by
  have hd := den_pos r hr
  have h1 : 0 < r - 1 := by linarith
  have heq : low r = ordinary r / (den r * (r - 1)) := by
    unfold low mixture ordinary
    field_simp
    unfold den
    ring
  rw [heq, ← mul_div_assoc]
  apply (div_le_div_iff₀ (mul_pos hd h1) hd).mpr
  have heq : exceptional r * (den r * (r - 1)) -
      ((r - 2) * ordinary r) * den r = den r * (4 * r - 2) := by
    unfold ordinary exceptional
    ring
  apply sub_nonneg.mp
  rw [heq]
  exact mul_nonneg (le_of_lt hd) (by linarith)

theorem small_buffered_exception :
    (6 - 2 : ℝ) * highBound 6 ≤ exceptional 6 / den 6 ∧
    (7 - 2 : ℝ) * highBound 7 ≤ exceptional 7 / den 7 := by
  norm_num [highBound, exceptional, den]

theorem overlap_window_bounds (r E : ℝ) (hr : 5 ≤ r) (hE : E ≤ r - 3 / 2) :
    (r - 1) * E ≤ ordinary r ∧
    (r - 2) * E + r + 1 ≤ ordinary r := by
  unfold ordinary
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hE (by linarith : 0 ≤ r - 1)]
  · nlinarith [mul_le_mul_of_nonneg_left hE (by linarith : 0 ≤ r - 2)]

theorem overlap_exceptional_bound (r a b : ℝ) (hr : 5 ≤ r)
    (hab : a + b = r) (hle : a ≤ b) :
    (r - 2) * ((r + a - 1) / 2) + (r + b - 1) / 2 ≤ exceptional r := by
  have ha : 2 * a ≤ r := by linarith
  have hprod : a * (r - 3) ≤ (r / 2) * (r - 3) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  unfold exceptional
  nlinarith [sq_nonneg (r - 7 / 2)]

#print axioms parameters
#print axioms residual_mass
#print axioms residual_positive
#print axioms buffered_window_bounds
#print axioms low_exceptional_bound
#print axioms small_buffered_exception
#print axioms overlap_window_bounds
#print axioms overlap_exceptional_bound
end
end QuorumAudit.MixedCircle
