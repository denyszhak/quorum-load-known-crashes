import FullRangeSharp
import FullRangeComb

/-!
Theorem `thm:proactive`(4) and Corollary `cor:price`: the limit of the
proactive optimum, the ratio between the two optima, and the endpoint
values at read fraction 0 and 1.
-/

set_option maxHeartbeats 4000000

namespace QuorumAudit.Paper
noncomputable section
open Finset Circle Filter Topology
variable {n : ℕ} [NeZero n]

/-! ### Theorem `thm:proactive`(4) -/

/-- The explicit bound behind part (4): if `4 d ≤ min{a,1-a} n` with
    `d = 2f+1`, then
    `2 sqrt(d a(1-a)/n) ≤ L^pro ≤ 2 sqrt(d a(1-a)/n) + (a d + 1 - a)/n`. -/
theorem proactive_error (f : ℕ) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (hy : 4 * (2 * (f : ℝ) + 1) ≤ min a (1 - a) * n) :
    2 * √((2 * (f : ℝ) + 1) * (a * (1 - a)) / n) ≤ proactiveOptimum n f a ∧
      proactiveOptimum n f a ≤
        2 * √((2 * (f : ℝ) + 1) * (a * (1 - a)) / n) + (a * (2 * (f : ℝ) + 1) + (1 - a)) / n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hf0 : (0 : ℝ) ≤ f := Nat.cast_nonneg f
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 2 * (f : ℝ) + 1 := ⟨_, rfl⟩
  have hDcast : ((2 * f + 1 : ℕ) : ℝ) = D := by rw [hD]; push_cast; ring
  rw [← hD] at hy ⊢
  have hD1 : 1 ≤ D := by rw [hD]; linarith
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = 1 - a := ⟨_, rfl⟩
  rw [← hb] at hy ⊢
  have hb0 : 0 < b := by rw [hb]; linarith
  have hb1 : b < 1 := by rw [hb]; linarith
  have han : 4 * D ≤ a * n := hy.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hn.le)
  have hbn : 4 * D ≤ b * n := hy.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hn.le)
  have hn8 : 8 * D ≤ n := by nlinarith
  have hrad : 0 < a * D * n / b := by positivity
  obtain ⟨q₀, hq₀def⟩ : ∃ q₀ : ℝ, q₀ = √(a * D * n / b) := ⟨_, rfl⟩
  have hq₀ : 0 < q₀ := by rw [hq₀def]; exact Real.sqrt_pos.mpr hrad
  have hq₀sq : b * q₀ ^ 2 = a * D * n := by
    rw [hq₀def, Real.sq_sqrt hrad.le]
    field_simp
  have hq₀lo : 2 * D ≤ q₀ := by
    have h1 : (2 * D) ^ 2 ≤ q₀ ^ 2 := by
      have h2 : b * (2 * D) ^ 2 ≤ b * q₀ ^ 2 := by
        rw [hq₀sq]
        have h3 : 4 * D * D ≤ a * n * D := mul_le_mul_of_nonneg_right han (by linarith)
        have h4 : b * (2 * D) ^ 2 ≤ 1 * (2 * D) ^ 2 :=
          mul_le_mul_of_nonneg_right hb1.le (by positivity)
        nlinarith
      exact le_of_mul_le_mul_left h2 hb0
    exact (pow_le_pow_iff_left₀ (by linarith) hq₀.le (by norm_num)).mp h1
  -- the comb size and the gap
  have hqge : q₀ ≤ (⌈q₀⌉₊ : ℝ) := Nat.le_ceil q₀
  have hqlt : (⌈q₀⌉₊ : ℝ) < q₀ + 1 := Nat.ceil_lt_add_one hq₀.le
  have hqpos : (0 : ℝ) < (⌈q₀⌉₊ : ℝ) := lt_of_lt_of_le hq₀ hqge
  have hqnat : 2 * f + 1 ≤ ⌈q₀⌉₊ := by
    have : ((2 * f + 1 : ℕ) : ℝ) ≤ (⌈q₀⌉₊ : ℝ) := by rw [hDcast]; linarith
    exact_mod_cast this
  have hgpos : (0 : ℝ) ≤ (n : ℝ) / (⌈q₀⌉₊ : ℝ) := by positivity
  have hglt : (⌈(n : ℝ) / (⌈q₀⌉₊ : ℝ)⌉₊ : ℝ) < (n : ℝ) / (⌈q₀⌉₊ : ℝ) + 1 :=
    Nat.ceil_lt_add_one hgpos
  have hnq : (n : ℝ) / (⌈q₀⌉₊ : ℝ) ≤ (n : ℝ) / q₀ :=
    div_le_div_of_nonneg_left hn.le hq₀ hqge
  have hnq₀ : (n : ℝ) / q₀ ≤ n / (2 * D) :=
    div_le_div_of_nonneg_left hn.le (by linarith) hq₀lo
  have hgle : (⌈(n : ℝ) / (⌈q₀⌉₊ : ℝ)⌉₊ : ℝ) ≤ (n : ℝ) / q₀ + 1 := by linarith
  have hdg : (2 * f + 1) * ⌈(n : ℝ) / (⌈q₀⌉₊ : ℝ)⌉₊ ≤ n := by
    have h1 : D * (⌈(n : ℝ) / (⌈q₀⌉₊ : ℝ)⌉₊ : ℝ) ≤ D * (n / (2 * D) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h2 : D * ((n : ℝ) / (2 * D) + 1) = n / 2 + D := by field_simp
    have h3 : (((2 * f + 1) * ⌈(n : ℝ) / (⌈q₀⌉₊ : ℝ)⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by
      rw [Nat.cast_mul, hDcast]
      linarith
    exact_mod_cast h3
  have hup := proactive_upper_printed (n := n) f ⌈q₀⌉₊ hqnat hdg a ha0.le ha1.le
  rw [← hD, ← hb] at hup
  -- the leading term
  have hτ : √(D * (a * b) / n) = b * q₀ / n := by
    have h0 : 0 ≤ b * q₀ / n := by positivity
    have e : D * (a * b) / n = (b * q₀ / n) ^ 2 := by
      have : (b * q₀ / n) ^ 2 = b * (b * q₀ ^ 2) / (n : ℝ) ^ 2 := by ring
      rw [this, hq₀sq]
      field_simp
    rw [e, Real.sqrt_sq h0]
  have hadn : a * D * (n / q₀) = b * q₀ := by
    have : a * D * (n / q₀) = a * D * n / q₀ := by ring
    rw [this, ← hq₀sq]
    field_simp
  constructor
  · obtain ⟨𝒜, ℬ, _, _, hmeet, hroutes⟩ :=
      proactive_comb_design (n := n) f ⌈q₀⌉₊ hqnat hdg a ha0.le ha1.le
    apply le_proactiveOptimum f a
      ⟨_, 𝒜, ℬ, fun _ _ => subset_univ _, fun _ _ => subset_univ _, hmeet, hroutes⟩
    intro L hL
    have h := proactive_lower_sqrt (n := n) f a L ha0.le ha1.le hL
    rw [← hD, ← hb] at h
    exact (le_max_right _ _).trans h
  · apply hup.trans
    rw [hτ]
    have h1 : a * (D * (⌈(n : ℝ) / (⌈q₀⌉₊ : ℝ)⌉₊ : ℝ)) ≤ a * (D * ((n : ℝ) / q₀ + 1)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgle (by linarith)) ha0.le
    have h2 : b * (⌈q₀⌉₊ : ℝ) ≤ b * (q₀ + 1) := mul_le_mul_of_nonneg_left hqlt.le hb0.le
    have h3 : a * (D * ((n : ℝ) / q₀ + 1)) = b * q₀ + a * D := by
      have : a * (D * ((n : ℝ) / q₀ + 1)) = a * D * (n / q₀) + a * D := by ring
      rw [this, hadn]
    have e : 2 * (b * q₀ / n) + (a * D + b) / n = (b * q₀ + a * D + b * (q₀ + 1)) / n := by
      field_simp
      ring
    rw [e]
    apply div_le_div_of_nonneg_right _ hn.le
    linarith

/-- The lower-order term is small: it is at most the leading term times
    `sqrt(d / (min{a,1-a} n))`. -/
theorem proactive_error_term (f : ℕ) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    (a * (2 * (f : ℝ) + 1) + (1 - a)) / n ≤
      2 * √((2 * (f : ℝ) + 1) * (a * (1 - a)) / n) *
        √((2 * (f : ℝ) + 1) / (min a (1 - a) * n)) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hf0 : (0 : ℝ) ≤ f := Nat.cast_nonneg f
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 2 * (f : ℝ) + 1 := ⟨_, rfl⟩
  rw [← hD]
  have hD1 : 1 ≤ D := by rw [hD]; linarith
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = 1 - a := ⟨_, rfl⟩
  rw [← hb]
  have hb0 : 0 < b := by rw [hb]; linarith
  have hb1 : b < 1 := by rw [hb]; linarith
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ = min a b := ⟨_, rfl⟩
  rw [← hμ]
  have hμ0 : 0 < μ := by rw [hμ]; exact lt_min ha0 hb0
  have hμa : μ ≤ a := by rw [hμ]; exact min_le_left _ _
  have hμb : μ ≤ b := by rw [hμ]; exact min_le_right _ _
  have hX : 0 ≤ D * (a * b) / n := by positivity
  have hprod : √(D * (a * b) / n) * √(D / (μ * n)) = √(D * (a * b) / n * (D / (μ * n))) :=
    (Real.sqrt_mul hX _).symm
  have key : ∀ t : ℝ, 0 ≤ t → t ^ 2 ≤ D * (a * b) / n * (D / (μ * n)) →
      t ≤ √(D * (a * b) / n) * √(D / (μ * n)) := by
    intro t ht h
    rw [hprod]
    calc t = √(t ^ 2) := (Real.sqrt_sq ht).symm
      _ ≤ _ := Real.sqrt_le_sqrt h
  have h1 : a * D / n ≤ √(D * (a * b) / n) * √(D / (μ * n)) := by
    apply key _ (by positivity)
    have e : D * (a * b) / n * (D / (μ * n)) - (a * D / n) ^ 2 =
        D ^ 2 * a * (b - a * μ) / (μ * (n : ℝ) ^ 2) := by
      field_simp
    have hpos : 0 ≤ D ^ 2 * a * (b - a * μ) / (μ * (n : ℝ) ^ 2) := by
      have : 0 ≤ b - a * μ := by nlinarith
      positivity
    linarith
  have h2 : b / n ≤ √(D * (a * b) / n) * √(D / (μ * n)) := by
    apply key _ (by positivity)
    have e : D * (a * b) / n * (D / (μ * n)) - (b / n) ^ 2 =
        b * (D ^ 2 * a - b * μ) / (μ * (n : ℝ) ^ 2) := by
      field_simp
    have hpos : 0 ≤ b * (D ^ 2 * a - b * μ) / (μ * (n : ℝ) ^ 2) := by
      have h3 : b * μ ≤ a := by nlinarith
      have hD2 : 1 ≤ D ^ 2 := by nlinarith
      have h4 : a ≤ D ^ 2 * a := by
        have := mul_le_mul_of_nonneg_right hD2 ha0.le
        linarith
      have : 0 ≤ D ^ 2 * a - b * μ := by linarith
      positivity
    linarith
  have e : (a * D + b) / n = a * D / n + b / n := by ring
  rw [e]
  linarith

/-- The same as a ratio, in terms of `y = min{a,1-a} n / (2f+1)`. -/
theorem proactive_ratio (f : ℕ) (a : ℝ)
    (hy : 4 ≤ min a (1 - a) * n / (2 * (f : ℝ) + 1)) :
    0 < a ∧ a < 1 ∧
      1 ≤ proactiveOptimum n f a / (2 * √((2 * (f : ℝ) + 1) * (a * (1 - a)) / n)) ∧
      proactiveOptimum n f a / (2 * √((2 * (f : ℝ) + 1) * (a * (1 - a)) / n)) ≤
        1 + 1 / √(min a (1 - a) * n / (2 * (f : ℝ) + 1)) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hf0 : (0 : ℝ) ≤ f := Nat.cast_nonneg f
  have hD : (0 : ℝ) < 2 * (f : ℝ) + 1 := by positivity
  have hy' : 4 * (2 * (f : ℝ) + 1) ≤ min a (1 - a) * n := (le_div_iff₀ hD).mp hy
  have hmin : 0 < min a (1 - a) := by
    by_contra h
    have : min a (1 - a) * n ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) hn.le
    nlinarith
  have ha0 : 0 < a := lt_of_lt_of_le hmin (min_le_left _ _)
  have ha1 : a < 1 := by
    have := lt_of_lt_of_le hmin (min_le_right a (1 - a))
    linarith
  obtain ⟨hlow, hup⟩ := proactive_error (n := n) f a ha0 ha1 hy'
  have hterm := proactive_error_term (n := n) f a ha0 ha1
  have hτ : 0 < 2 * √((2 * (f : ℝ) + 1) * (a * (1 - a)) / n) := by
    have : 0 < (2 * (f : ℝ) + 1) * (a * (1 - a)) / n := by
      have : 0 < 1 - a := by linarith
      positivity
    have := Real.sqrt_pos.mpr this
    linarith
  have hw : √((2 * (f : ℝ) + 1) / (min a (1 - a) * n)) =
      1 / √(min a (1 - a) * n / (2 * (f : ℝ) + 1)) := by
    rw [one_div, ← Real.sqrt_inv, inv_div]
  refine ⟨ha0, ha1, (one_le_div hτ).mpr hlow, ?_⟩
  rw [div_le_iff₀ hτ, ← hw]
  nlinarith

/-- Theorem `thm:proactive`(4): along any sequence of parameters with
    `min{a,1-a} n / f → ∞`, the proactive optimum is
    `(1 + o(1)) 2 sqrt((2f+1) a(1-a)/n)`. -/
theorem proactive_limit (n : ℕ → ℕ) [∀ k, NeZero (n k)] (f : ℕ → ℕ) (a : ℕ → ℝ)
    (hf : ∀ k, 1 ≤ f k)
    (hx : Tendsto (fun k => min (a k) (1 - a k) * (n k : ℝ) / (f k : ℝ)) atTop atTop) :
    Tendsto (fun k => proactiveOptimum (n k) (f k) (a k) /
        (2 * √((2 * (f k : ℝ) + 1) * (a k * (1 - a k)) / (n k : ℝ)))) atTop (𝓝 1) := by
  have hy : Tendsto (fun k => min (a k) (1 - a k) * (n k : ℝ) / (2 * (f k : ℝ) + 1))
      atTop atTop := by
    apply tendsto_atTop_mono' atTop _ (hx.atTop_div_const (by norm_num : (0 : ℝ) < 3))
    filter_upwards [hx.eventually_ge_atTop 0] with k hk
    have hF : (1 : ℝ) ≤ f k := by exact_mod_cast hf k
    have hnum : 0 ≤ min (a k) (1 - a k) * (n k : ℝ) := by
      by_contra h
      have : min (a k) (1 - a k) * (n k : ℝ) / (f k : ℝ) < 0 :=
        div_neg_of_neg_of_pos (not_le.mp h) (by linarith)
      linarith
    rw [div_div]
    apply div_le_div_of_nonneg_left hnum (by positivity)
    linarith
  have h0 : Tendsto (fun k => 1 / √(min (a k) (1 - a k) * (n k : ℝ) / (2 * (f k : ℝ) + 1)))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hy)
  have hupper : Tendsto
      (fun k => 1 + 1 / √(min (a k) (1 - a k) * (n k : ℝ) / (2 * (f k : ℝ) + 1)))
      atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add h0
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [hy.eventually_ge_atTop 4] with k hk
    exact (proactive_ratio (n := n k) (f k) (a k) hk).2.2.1
  · filter_upwards [hy.eventually_ge_atTop 4] with k hk
    exact (proactive_ratio (n := n k) (f k) (a k) hk).2.2.2

/-! ### Corollary `cor:price`, the limit -/

/-- Corollary `cor:price`: along any sequence of parameters with
    `min{a,1-a} n / f² → ∞`, the ratio of the two optima divided by
    `sqrt(2f+1)` tends to one. The crash budget may vary with the index. -/
theorem price_limit (n : ℕ → ℕ) [∀ k, NeZero (n k)] (f : ℕ → ℕ) (a : ℕ → ℝ)
    (hf : ∀ k, 1 ≤ f k)
    (hx : Tendsto (fun k => min (a k) (1 - a k) * (n k : ℝ) / (f k : ℝ) ^ 2) atTop atTop) :
    Tendsto (fun k => proactiveOptimum (n k) (f k) (a k) /
        (optimum (n k) (f k) (a k) * √(2 * (f k : ℝ) + 1))) atTop (𝓝 1) := by
  have hx1 : Tendsto (fun k => min (a k) (1 - a k) * (n k : ℝ) / (f k : ℝ)) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hx
    filter_upwards [hx.eventually_ge_atTop 0] with k hk
    have hF : (1 : ℝ) ≤ f k := by exact_mod_cast hf k
    have hF2 : (f k : ℝ) ≤ (f k : ℝ) ^ 2 := by nlinarith
    have hnum : 0 ≤ min (a k) (1 - a k) * (n k : ℝ) := by
      by_contra h
      have : min (a k) (1 - a k) * (n k : ℝ) / (f k : ℝ) ^ 2 < 0 :=
        div_neg_of_neg_of_pos (not_le.mp h) (by positivity)
      linarith
    exact div_le_div_of_nonneg_left hnum (by linarith) hF2
  have hA := sharp_limit n f a hf hx
  have hB := proactive_limit n f a hf hx1
  have hBA := hB.div hA one_ne_zero
  rw [div_one] at hBA
  apply hBA.congr'
  filter_upwards [hx.eventually_ge_atTop 64] with k hk
  obtain ⟨ha0, ha1, _, _⟩ := sharp_ratio (n := n k) (f k) (hf k) (a k) hk
  have hn : (0 : ℝ) < n k := by exact_mod_cast NeZero.pos (n k)
  have hf0 : (0 : ℝ) ≤ f k := Nat.cast_nonneg _
  have hβ : 0 < a k * (1 - a k) / (n k : ℝ) := by
    have : 0 < 1 - a k := by linarith
    positivity
  have hσ : 0 < √(a k * (1 - a k) / (n k : ℝ)) := Real.sqrt_pos.mpr hβ
  have hD : 0 < √(2 * (f k : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hτ : √((2 * (f k : ℝ) + 1) * (a k * (1 - a k)) / (n k : ℝ)) =
      √(2 * (f k : ℝ) + 1) * √(a k * (1 - a k) / (n k : ℝ)) := by
    rw [mul_div_assoc, Real.sqrt_mul (by positivity)]
  simp only [Pi.div_apply]
  rw [hτ, div_div_div_eq]
  field_simp

/-- Corollary `cor:price` for a fixed crash budget: the ratio of the two
    optima tends to `sqrt(2f+1)`. -/
theorem price_limit_fixed (f : ℕ) (hf : 1 ≤ f) (n : ℕ → ℕ) [∀ k, NeZero (n k)] (a : ℕ → ℝ)
    (hx : Tendsto (fun k => min (a k) (1 - a k) * (n k : ℝ) / (f : ℝ) ^ 2) atTop atTop) :
    Tendsto (fun k => proactiveOptimum (n k) f (a k) / optimum (n k) f (a k))
      atTop (𝓝 (√(2 * (f : ℝ) + 1))) := by
  have h := price_limit n (fun _ => f) a (fun _ => hf) hx
  have hD : 0 < √(2 * (f : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have h2 := h.mul_const (√(2 * (f : ℝ) + 1))
  rw [one_mul] at h2
  apply h2.congr
  intro k
  rw [← div_div, div_mul_cancel₀ _ hD.ne']

/-! ### Corollary `cor:price`, the endpoints -/

omit [NeZero n] in
theorem proactive_swap {ι : Type*} [DecidableEq ι] {V : Finset ι} {f : ℕ} {a L : ℝ}
    (h : ProactiveFeasible V f a L) : ProactiveFeasible V f (1 - a) L := by
  obtain ⟨𝒜, ℬ, h𝒜, hℬ, hmeet, p, q, hp, hpn, hq, hqn, hload⟩ := h
  refine ⟨ℬ, 𝒜, hℬ, h𝒜, ?_, q, p, hq, hqn, hp, hpn, ?_⟩
  · intro B hB A hA
    rw [inter_comm]
    exact hmeet A hA B hB
  · intro i hi
    have e : (1 : ℝ) - (1 - a) = a := by ring
    rw [e]
    linarith [hload i hi]

theorem proactiveOptimum_symmetry (f : ℕ) (a : ℝ) :
    proactiveOptimum n f a = proactiveOptimum n f (1 - a) := by
  unfold proactiveOptimum
  congr 1
  ext L
  constructor
  · exact proactive_swap
  · intro h
    have h2 := proactive_swap h
    have e : (1 : ℝ) - (1 - a) = a := by ring
    rwa [e] at h2

/-- With no reads, the known-failure optimum is `(f+1)/(n-f)`: writes of
    `f+1` servers against reads of `n-f` servers. -/
theorem known_endpoint (f : ℕ) (hn : 2 * f + 1 ≤ n) (L : ℝ) :
    Feasible (univ : Finset (ZMod n)) f 0 L ↔ ((f : ℝ) + 1) / ((n : ℝ) - f) ≤ L := by
  constructor
  · intro h
    have := known_lower (univ : Finset (ZMod n)) f (by rw [card_zmod_univ]; omega) 0 L
      le_rfl (by norm_num) h
    rw [card_zmod_univ] at this
    exact this.2.1
  · intro hL
    rw [feasible_iff]
    refine ⟨powersetCard (n - f) univ, rankedWrites n n (f + 1),
      fun _ _ => subset_univ _, fun _ _ => subset_univ _, ?_, ?_⟩
    · intro r hr w hw
      have hrc : r.card = n - f := (mem_powersetCard.mp hr).2
      have hwc : w.card = f + 1 := (mem_filter.mp hw).2
      apply Finset.inter_nonempty_of_card_lt_card_add_card (subset_univ r) (subset_univ w)
      rw [card_zmod_univ, hrc, hwc]
      omega
    · intro F _ hF
      obtain ⟨G, hFG, _, hG⟩ := Finset.exists_subsuperset_card_eq (subset_univ F) hF
        (by rw [card_zmod_univ]; omega)
      let read : Routing (powersetCard (n - f) (univ : Finset (ZMod n))) univ F := {
        quorums := {univ \ G}
        subset := by
          intro q hq
          rw [mem_singleton.mp hq]
          refine mem_powersetCard.mpr ⟨sdiff_subset, ?_⟩
          rw [card_sdiff_of_subset (subset_univ _), card_zmod_univ, hG]
        live := by
          intro q hq
          rw [mem_singleton.mp hq]
          exact sdiff_subset_sdiff le_rfl hFG
        p := fun _ => 1
        nonnegative := by intros; norm_num
        normalized := by simp }
      obtain ⟨write, hwrite⟩ := tile_write_route G n (f + 1) le_rfl (by omega)
        (by rw [hG]; exact Nat.le_mul_of_pos_left _ (by omega)) (by omega)
      refine ⟨read, unpad_routing write hFG, ?_⟩
      intro i _
      change 0 * incidence read.quorums read.p i + (1 - 0) * incidence write.quorums write.p i ≤ L
      have h1 := hwrite i
      rw [hG] at h1
      have e : ((f + 1 : ℕ) : ℝ) = (f : ℝ) + 1 := by push_cast; ring
      rw [e] at h1
      linarith

/-- With no reads, the proactive optimum is `(2f+1)/n`: every server as
    the read contact set, intervals of `2f+1` servers as write contacts. -/
theorem proactive_endpoint (f : ℕ) (hn : 2 * f + 1 ≤ n) (L : ℝ) :
    ProactiveFeasible (univ : Finset (ZMod n)) f 0 L ↔ (2 * (f : ℝ) + 1) / n ≤ L := by
  constructor
  · intro h
    have := proactive_lower (univ : Finset (ZMod n)) f
      (by rw [card_zmod_univ]; exact NeZero.pos n) 0 L le_rfl (by norm_num) h
    rw [card_zmod_univ] at this
    exact this.2.1
  · intro hL
    obtain ⟨write, hwrite⟩ := uniform_interval_route (n := n) (2 * f + 1)
    refine ⟨{univ}, write.quorums, fun _ _ => subset_univ _, fun _ _ => subset_univ _, ?_,
      fun _ => 1, write.p, fun _ _ => by norm_num, by simp, write.nonnegative,
      write.normalized, ?_⟩
    · intro A hA B hB
      rw [mem_singleton.mp hA, univ_inter]
      obtain ⟨s, _, rfl⟩ := mem_image.mp (write.subset hB)
      rw [arc_card (2 * f + 1) hn s]
    · intro i _
      have h1 := hwrite i
      have e : ((2 * f + 1 : ℕ) : ℝ) = 2 * (f : ℝ) + 1 := by push_cast; ring
      rw [e] at h1
      linarith

/-- Corollary `cor:price`, endpoints: at read fraction 0 and at read
    fraction 1 the two optima are `(f+1)/(n-f)` and `(2f+1)/n`, so their
    ratio is `(2f+1)(n-f) / ((f+1) n)`. -/
theorem price_endpoints (f : ℕ) (hn : 2 * f + 1 ≤ n) :
    optimum n f 0 = ((f : ℝ) + 1) / ((n : ℝ) - f) ∧
    proactiveOptimum n f 0 = (2 * (f : ℝ) + 1) / n ∧
    optimum n f 1 = ((f : ℝ) + 1) / ((n : ℝ) - f) ∧
    proactiveOptimum n f 1 = (2 * (f : ℝ) + 1) / n ∧
    proactiveOptimum n f 0 / optimum n f 0 =
      (2 * (f : ℝ) + 1) * ((n : ℝ) - f) / (((f : ℝ) + 1) * n) := by
  have h0 : optimum n f 0 = ((f : ℝ) + 1) / ((n : ℝ) - f) := by
    unfold optimum
    have hset : {L : ℝ | Feasible (univ : Finset (ZMod n)) f 0 L} =
        Set.Ici (((f : ℝ) + 1) / ((n : ℝ) - f)) := by
      ext L
      exact known_endpoint f hn L
    rw [hset, csInf_Ici]
  have hp0 : proactiveOptimum n f 0 = (2 * (f : ℝ) + 1) / n := by
    unfold proactiveOptimum
    have hset : {L : ℝ | ProactiveFeasible (univ : Finset (ZMod n)) f 0 L} =
        Set.Ici ((2 * (f : ℝ) + 1) / n) := by
      ext L
      exact proactive_endpoint f hn L
    rw [hset, csInf_Ici]
  have h1 : optimum n f 1 = optimum n f 0 := by
    rw [optimum_symmetry f 1]
    norm_num
  have hp1 : proactiveOptimum n f 1 = proactiveOptimum n f 0 := by
    rw [proactiveOptimum_symmetry f 1]
    norm_num
  refine ⟨h0, hp0, by rw [h1, h0], by rw [hp1, hp0], ?_⟩
  rw [h0, hp0]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hm : (0 : ℝ) < (n : ℝ) - f := by
    have : ((2 * f + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at this
    have hf0 : (0 : ℝ) ≤ f := Nat.cast_nonneg f
    linarith
  have hf1 : (0 : ℝ) < (f : ℝ) + 1 := by positivity
  field_simp

#print axioms proactive_error
#print axioms proactive_error_term
#print axioms proactive_ratio
#print axioms proactive_limit
#print axioms price_limit
#print axioms price_limit_fixed
#print axioms known_endpoint
#print axioms proactive_endpoint
#print axioms price_endpoints
end
end QuorumAudit.Paper
