import FullRangeAttained
import PaperClaims

/-!
Consequences and controls for the printed forms: the read-heavy mirror
images of the exact theorems, and instances showing that the hypotheses
of the limit theorems can be met.
-/

set_option maxHeartbeats 2000000

namespace QuorumAudit.Paper
noncomputable section
open Finset Circle Filter Topology

/-- The mirror image of Theorem `thm:general-f` on the read-heavy
    interval, as stated after Proposition `prop:symmetry`. -/
theorem arbitrary_f_read_heavy (n f k : ℕ) [NeZero n]
    (hf : 1 ≤ f) (hk : f * f + 1 ≤ k) (hn : n = (f + 1) * k)
    (a L : ℝ) (ha : a ≤ 1) (hend : 1 - a ≤ 1 / (((k : ℝ) - 1) * (k + f) + 1)) :
    Feasible (univ : Finset (ZMod n)) f a L ↔
      ((f : ℝ) + 1 + ((k : ℝ) - 1) * (1 - a)) / ((n : ℝ) - f) ≤ L := by
  rw [feasible_symmetry]
  exact arbitrary_f_exact_in_paper_model n f k hf hk hn (1 - a) L (by linarith) hend

/-- The mirror image of the cyclic two-crash theorem. -/
theorem cyclic_read_heavy (k : ℕ) (hk : 3 ≤ k) (a L : ℝ)
    (ha : a ≤ 1) (hend : 1 - a ≤ 3 / ((k : ℝ) * k + k + 1)) :
    Feasible (range (3 * k + 2)) 2 a L ↔
      (3 + ((k : ℝ) - 1) * (1 - a)) / (3 * (k : ℝ)) ≤ L := by
  rw [feasible_symmetry]
  exact cyclic_exact_in_paper_model k hk (1 - a) L (by linarith) hend

/-- The hypothesis of the sharp-constant limit can be met: one crash,
    equal fractions, `k + 1` servers. -/
theorem example_sharp_limit :
    Tendsto (fun k : ℕ => optimum (k + 1) 1 (1 / 2) /
      (2 * √((1 / 2 : ℝ) * (1 - 1 / 2) / ((k + 1 : ℕ) : ℝ)))) atTop (𝓝 1) := by
  apply sharp_limit (fun k => k + 1) (fun _ => 1) (fun _ => 1 / 2) (fun _ => le_rfl)
  have h1 : Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have h2 := h1.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
  refine h2.congr fun k => ?_
  norm_num

/-- The hypothesis of the ratio corollary can be met: with one crash and
    equal fractions the ratio of the two optima tends to `sqrt 3`. -/
theorem example_price_limit :
    Tendsto (fun k : ℕ => proactiveOptimum (k + 1) 1 (1 / 2) / optimum (k + 1) 1 (1 / 2))
      atTop (𝓝 (√(2 * ((1 : ℕ) : ℝ) + 1))) := by
  apply price_limit_fixed 1 le_rfl (fun k => k + 1) (fun _ => 1 / 2)
  have h1 : Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have h2 := h1.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
  refine h2.congr fun k => ?_
  norm_num

/-- Endpoint values on seven servers with two crashes: `3/5` and `5/7`. -/
theorem example_endpoints :
    optimum 7 2 0 = 3 / 5 ∧ proactiveOptimum 7 2 0 = 5 / 7 := by
  obtain ⟨h1, h2, _⟩ := price_endpoints (n := 7) 2 (by norm_num)
  constructor
  · rw [h1]; norm_num
  · rw [h2]; norm_num

/-- The optimum is a minimum: on seven servers with two crashes and no
    reads, load `3/5` is feasible and nothing smaller is. -/
theorem example_minimum (L : ℝ) :
    Feasible (univ : Finset (ZMod 7)) 2 0 L ↔ 3 / 5 ≤ L := by
  rw [feasible_iff_optimum_le 2 (by norm_num) 0 le_rfl (by norm_num), example_endpoints.1]

/-- The remark after Theorem `thm:proactive`: the first lower bound
    `d/n` is at least `sqrt(d/(4 a n))` times the second,
    `2 sqrt(d a(1-a)/n)`. When `a n = o(f)` this factor is unbounded, so the
    hypothesis of part (4) cannot be weakened to `a n → ∞`. -/
theorem proactive_corner (d a n : ℝ) (hd : 0 < d) (ha0 : 0 < a) (ha1 : a < 1) (hn : 0 < n) :
    √(d / (4 * a * n)) * (2 * √(d * (a * (1 - a)) / n)) ≤ d / n := by
  have hb : 0 < 1 - a := by linarith
  have hX : 0 ≤ d / (4 * a * n) := by positivity
  have h : √(d / (4 * a * n)) * √(d * (a * (1 - a)) / n) =
      √(d / (4 * a * n) * (d * (a * (1 - a)) / n)) := (Real.sqrt_mul hX _).symm
  have e : d / (4 * a * n) * (d * (a * (1 - a)) / n) = (d / (2 * n)) ^ 2 * (1 - a) := by
    field_simp
    ring
  have h2 : √((d / (2 * n)) ^ 2 * (1 - a)) = d / (2 * n) * √(1 - a) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have h3 : √(1 - a) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have h4 : 0 ≤ d / (2 * n) := by positivity
  calc
    √(d / (4 * a * n)) * (2 * √(d * (a * (1 - a)) / n)) =
        2 * (√(d / (4 * a * n)) * √(d * (a * (1 - a)) / n)) := by ring
    _ = 2 * (d / (2 * n) * √(1 - a)) := by rw [h, e, h2]
    _ ≤ 2 * (d / (2 * n) * 1) := by
      have := mul_le_mul_of_nonneg_left h3 h4
      linarith
    _ = d / n := by ring

#print axioms proactive_corner
#print axioms arbitrary_f_read_heavy
#print axioms cyclic_read_heavy
#print axioms example_sharp_limit
#print axioms example_price_limit
#print axioms example_endpoints
#print axioms example_minimum
end
end QuorumAudit.Paper
