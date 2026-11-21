import FullRangeExact
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.Field

/-!
The limit statement of Theorem `thm:sharp`: an explicit relative error
bound, and the limit that follows from it.
-/

set_option maxHeartbeats 4000000

namespace QuorumAudit.Paper
noncomputable section
open Finset Circle Filter Topology
variable {n : ℕ} [NeZero n]

/-- Real arithmetic behind the error bound. Here `N = n`, `F = f`,
    `δ = f / sqrt(a n)`, `ρ₀ = sqrt(m(1-a)/a)`, `s = sqrt(a(1-a)/m)` and
    `σ = sqrt(a(1-a)/n)`, each given by its defining equation. -/
theorem sharp_error_arith (a F N δ ρ₀ s σ : ℝ)
    (ha0 : 0 < a) (ha : a ≤ 1 / 2) (hF : 1 ≤ F)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 8) (hδdef : δ ^ 2 * (a * N) = F ^ 2)
    (hρ₀ : 0 < ρ₀) (hρ : a * ρ₀ ^ 2 = (N - F) * (1 - a))
    (hs : s = a * ρ₀ / (N - F)) (hσ0 : 0 ≤ σ) (hσ : σ ^ 2 * N = a * (1 - a)) :
    F * (ρ₀ + F + 1) / (N - F) < 1 ∧
      s * (1 + (1 + (F + 1) / ρ₀) / (1 - F * (ρ₀ + F + 1) / (N - F)) + ρ₀ / (N - F)) ≤
        2 * σ * (1 + 4 * δ) := by
  have hb : 1 / 2 ≤ 1 - a := by linarith
  have hδ2 : δ ^ 2 ≤ 1 / 64 := by nlinarith
  have hδ2' : δ ^ 2 ≤ δ / 8 := by nlinarith
  have hN : 0 < N := by
    by_contra h
    have h1 : a * N ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha0.le (not_lt.mp h)
    have h2 : δ ^ 2 * (a * N) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg δ) h1
    nlinarith
  have haN0 : 0 ≤ a * N := by positivity
  have haN : a * N ≤ N / 2 := by nlinarith
  have hF2 : F ^ 2 ≤ N / 128 := by
    have h1 : δ ^ 2 * (a * N) ≤ 1 / 64 * (N / 2) := mul_le_mul hδ2 haN haN0 (by norm_num)
    linarith
  have hFle : F ≤ F ^ 2 := by nlinarith
  have hFF1 : 1 ≤ F ^ 2 := by nlinarith
  have hF2δ : F ^ 2 ≤ δ * N / 16 := by
    have h1 : δ ^ 2 * (a * N) ≤ δ / 8 * (N / 2) := mul_le_mul hδ2' haN haN0 (by positivity)
    linarith
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = N - F := ⟨_, rfl⟩
  rw [← hMdef] at hρ hs ⊢
  have hMN : 127 / 128 * N ≤ M := by linarith
  have hM : 0 < M := by linarith
  have hNM : N ≤ 128 / 127 * M := by linarith
  have hδN : δ * N ≤ δ * (128 / 127 * M) := mul_le_mul_of_nonneg_left hNM hδ0.le
  -- (i) F ≤ δ ρ₀
  have hFρ : F ≤ δ * ρ₀ := by
    have h1 : a * F ^ 2 ≤ a * (δ * ρ₀) ^ 2 := by
      have e1 : a * F ^ 2 = δ ^ 2 * (a ^ 2 * N) := by rw [← hδdef]; ring
      have e2 : a * (δ * ρ₀) ^ 2 = δ ^ 2 * (M * (1 - a)) := by rw [← hρ]; ring
      rw [e1, e2]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg δ)
      have ha2 : a ^ 2 ≤ 1 / 4 := by nlinarith
      have h3 : a ^ 2 * N ≤ 1 / 4 * N := mul_le_mul_of_nonneg_right ha2 hN.le
      have h4 : 127 / 128 * N * (1 / 2) ≤ M * (1 - a) :=
        mul_le_mul hMN hb (by norm_num) hM.le
      linarith
    have h2 : F ^ 2 ≤ (δ * ρ₀) ^ 2 := le_of_mul_le_mul_left h1 ha0
    exact (pow_le_pow_iff_left₀ (by linarith) (by positivity) (by norm_num)).mp h2
  have he1 : (F + 1) / ρ₀ ≤ 2 * δ := by
    rw [div_le_iff₀ hρ₀]
    linarith
  -- (iii) F ρ₀ ≤ (65/64) δ M
  have hFρM : F * ρ₀ ≤ 65 / 64 * δ * M := by
    have h1 : a * (F * ρ₀) ^ 2 ≤ a * (65 / 64 * δ * M) ^ 2 := by
      have e1 : a * (F * ρ₀) ^ 2 = δ ^ 2 * a * M * (N * (1 - a)) := by
        have : a * (F * ρ₀) ^ 2 = F ^ 2 * (a * ρ₀ ^ 2) := by ring
        rw [this, ← hδdef, hρ]
        ring
      have e2 : a * (65 / 64 * δ * M) ^ 2 = δ ^ 2 * a * M * (4225 / 4096 * M) := by ring
      rw [e1, e2]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have : N * (1 - a) ≤ N := by nlinarith
      linarith
    have h2 : (F * ρ₀) ^ 2 ≤ (65 / 64 * δ * M) ^ 2 := le_of_mul_le_mul_left h1 ha0
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp h2
  have hFF : F * (F + 1) ≤ δ * M / 7 := by nlinarith
  -- (v) ρ₀ ≤ (65/64) δ M
  have hρM : ρ₀ ≤ 65 / 64 * δ * M := by
    have h1 : a * ρ₀ ^ 2 * N ≤ a * (65 / 64 * δ * M) ^ 2 * N := by
      have e2 : a * (65 / 64 * δ * M) ^ 2 * N = 4225 / 4096 * M ^ 2 * (δ ^ 2 * (a * N)) := by
        ring
      rw [hρ, e2, hδdef]
      have h3 : M * (1 - a) * N ≤ M * 1 * (128 / 127 * M) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hM.le) hNM hN.le (by positivity)
      have h4 : 4225 / 4096 * M ^ 2 * 1 ≤ 4225 / 4096 * M ^ 2 * F ^ 2 :=
        mul_le_mul_of_nonneg_left hFF1 (by positivity)
      nlinarith [sq_nonneg M]
    have h2 : a * ρ₀ ^ 2 ≤ a * (65 / 64 * δ * M) ^ 2 := le_of_mul_le_mul_right h1 hN
    have h3 : ρ₀ ^ 2 ≤ (65 / 64 * δ * M) ^ 2 := le_of_mul_le_mul_left h2 ha0
    exact (pow_le_pow_iff_left₀ hρ₀.le (by positivity) (by norm_num)).mp h3
  -- (vi) s ≤ σ (1 + δ/16)
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have hsM : s * M = a * ρ₀ := by rw [hs]; field_simp
  have hs2 : s ^ 2 * M = a * (1 - a) := by
    have h1 : s ^ 2 * M * M = a * (1 - a) * M := by
      have : s ^ 2 * M * M = (s * M) ^ 2 := by ring
      rw [this, hsM]
      have : (a * ρ₀) ^ 2 = a * (a * ρ₀ ^ 2) := by ring
      rw [this, hρ]
      ring
    exact mul_right_cancel₀ hM.ne' h1
  have hNle : N ≤ (1 + δ / 8) * M := by
    have : N = M + F := by linarith
    nlinarith
  have hsσ : s ≤ σ * (1 + δ / 16) := by
    have h1 : s ^ 2 * M ≤ (σ * (1 + δ / 16)) ^ 2 * M := by
      have e : (σ * (1 + δ / 16)) ^ 2 * M =
          σ ^ 2 * ((1 + δ / 8) * M) + σ ^ 2 * M * (δ ^ 2 / 256) := by ring
      have h2 : σ ^ 2 * N ≤ σ ^ 2 * ((1 + δ / 8) * M) :=
        mul_le_mul_of_nonneg_left hNle (sq_nonneg σ)
      have h3 : 0 ≤ σ ^ 2 * M * (δ ^ 2 / 256) := by positivity
      rw [e, hs2, ← hσ]
      linarith
    have h2 : s ^ 2 ≤ (σ * (1 + δ / 16)) ^ 2 := le_of_mul_le_mul_right h1 hM
    exact (pow_le_pow_iff_left₀ hs0 (by positivity) (by norm_num)).mp h2
  -- (vii) the bracket
  have he2 : F * (ρ₀ + F + 1) / M ≤ 6 / 5 * δ := by
    rw [div_le_iff₀ hM]
    have : F * (ρ₀ + F + 1) = F * ρ₀ + F * (F + 1) := by ring
    rw [this]
    nlinarith
  have he2lt : F * (ρ₀ + F + 1) / M < 1 := by linarith
  refine ⟨he2lt, ?_⟩
  have he10 : 0 ≤ (F + 1) / ρ₀ := by positivity
  have he20 : 0 ≤ F * (ρ₀ + F + 1) / M := by positivity
  have hden : 0 < 1 - F * (ρ₀ + F + 1) / M := by linarith
  have hfrac : (1 + (F + 1) / ρ₀) / (1 - F * (ρ₀ + F + 1) / M) ≤ 1 + 4 * δ := by
    rw [div_le_iff₀ hden]
    have h1 : (1 + 4 * δ) * (1 - 6 / 5 * δ) ≤ (1 + 4 * δ) * (1 - F * (ρ₀ + F + 1) / M) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  have he3 : ρ₀ / M ≤ 65 / 64 * δ := by
    rw [div_le_iff₀ hM]
    linarith
  have hfrac0 : 0 ≤ (1 + (F + 1) / ρ₀) / (1 - F * (ρ₀ + F + 1) / M) :=
    div_nonneg (by linarith) hden.le
  have he30 : 0 ≤ ρ₀ / M := by positivity
  have hB : 1 + (1 + (F + 1) / ρ₀) / (1 - F * (ρ₀ + F + 1) / M) + ρ₀ / M ≤ 2 + 21 / 4 * δ := by
    linarith
  have hB0 : 0 ≤ 1 + (1 + (F + 1) / ρ₀) / (1 - F * (ρ₀ + F + 1) / M) + ρ₀ / M := by linarith
  have hσδ : σ * δ ^ 2 ≤ σ * (δ / 8) := mul_le_mul_of_nonneg_left hδ2' hσ0
  have hσδ0 : 0 ≤ σ * δ := by positivity
  calc
    s * (1 + (1 + (F + 1) / ρ₀) / (1 - F * (ρ₀ + F + 1) / M) + ρ₀ / M) ≤
        σ * (1 + δ / 16) * (2 + 21 / 4 * δ) := mul_le_mul hsσ hB hB0 (by positivity)
    _ = 2 * σ + 43 / 8 * (σ * δ) + 21 / 64 * (σ * δ ^ 2) := by ring
    _ ≤ 2 * σ * (1 + 4 * δ) := by nlinarith

/-- Theorem `thm:sharp` with an explicit relative error, for `a ≤ 1/2`:
    if `64 f² ≤ a n`, then
    `2 sqrt(a(1-a)/n) ≤ L* ≤ 2 sqrt(a(1-a)/n) (1 + 4 f / sqrt(a n))`. -/
theorem sharp_error_half (f : ℕ) (hf : 1 ≤ f) (a : ℝ) (ha0 : 0 < a) (ha : a ≤ 1 / 2)
    (hx : 64 * (f : ℝ) ^ 2 ≤ a * n) :
    2 * √(a * (1 - a) / n) ≤ optimum n f a ∧
      optimum n f a ≤ 2 * √(a * (1 - a) / n) * (1 + 4 * ((f : ℝ) / √(a * n))) := by
  have hF : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have han : 0 < a * n := by positivity
  have hfn : f < n := by
    have h1 : (f : ℝ) ≤ (f : ℝ) ^ 2 := by nlinarith
    have h2 : a * n ≤ n / 2 := by nlinarith
    have : (f : ℝ) < n := by nlinarith
    exact_mod_cast this
  have hM : (0 : ℝ) < (n : ℝ) - f := by
    have : (f : ℝ) < n := by exact_mod_cast hfn
    linarith
  have hsq : 0 < √(a * n) := Real.sqrt_pos.mpr han
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (f : ℝ) / √(a * n) := ⟨_, rfl⟩
  rw [← hδ]
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδdef : δ ^ 2 * (a * n) = (f : ℝ) ^ 2 := by
    rw [hδ, div_pow, Real.sq_sqrt han.le]
    field_simp
  have hδle : δ ≤ 1 / 8 := by
    have h1 : δ ^ 2 * (a * n) ≤ (1 / 8) ^ 2 * (a * n) := by
      rw [hδdef]
      nlinarith
    have h2 : δ ^ 2 ≤ (1 / 8) ^ 2 := le_of_mul_le_mul_right h1 han
    exact (pow_le_pow_iff_left₀ hδ0.le (by norm_num) (by norm_num)).mp h2
  have hb : 0 < 1 - a := by linarith
  have hrad : 0 < ((n : ℝ) - f) * (1 - a) / a := by positivity
  have hρ₀ : 0 < √(((n : ℝ) - f) * (1 - a) / a) := Real.sqrt_pos.mpr hrad
  have hρ : a * √(((n : ℝ) - f) * (1 - a) / a) ^ 2 = ((n : ℝ) - f) * (1 - a) := by
    rw [Real.sq_sqrt hrad.le]
    field_simp
  have hβ : 0 ≤ a * (1 - a) / n := by positivity
  have hσ : √(a * (1 - a) / n) ^ 2 * n = a * (1 - a) := by
    rw [Real.sq_sqrt hβ]
    field_simp
  obtain ⟨hε, hbound⟩ := sharp_error_arith a f n δ (√(((n : ℝ) - f) * (1 - a) / a))
    (a * √(((n : ℝ) - f) * (1 - a) / a) / ((n : ℝ) - f)) (√(a * (1 - a) / n))
    ha0 ha hF hδ0 hδle hδdef hρ₀ hρ rfl (Real.sqrt_nonneg _) hσ
  obtain ⟨hlow, hup⟩ := sharp_bracket (n := n) f hf hfn a ha0 ha hε
  have hsM : √(a * (1 - a) / ((n : ℝ) - f)) =
      a * √(((n : ℝ) - f) * (1 - a) / a) / ((n : ℝ) - f) := by
    have hs0 : 0 ≤ a * √(((n : ℝ) - f) * (1 - a) / a) / ((n : ℝ) - f) := by positivity
    have e : a * (1 - a) / ((n : ℝ) - f) =
        (a * √(((n : ℝ) - f) * (1 - a) / a) / ((n : ℝ) - f)) ^ 2 := by
      rw [div_pow, mul_pow, Real.sq_sqrt hrad.le]
      field_simp
    rw [e, Real.sqrt_sq hs0]
  have hmono : √(a * (1 - a) / n) ≤ √(a * (1 - a) / ((n : ℝ) - f)) := by
    apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_left (by positivity) hM
    have : (0 : ℝ) ≤ f := Nat.cast_nonneg f
    linarith
  rw [hsM] at hup
  exact ⟨by linarith, hup.trans hbound⟩

/-- Theorem `thm:sharp` with an explicit relative error, at every read
    fraction: if `64 f² ≤ min{a, 1-a} n`, then
    `2 sqrt(a(1-a)/n) ≤ L* ≤ 2 sqrt(a(1-a)/n) (1 + 4 f / sqrt(min{a,1-a} n))`. -/
theorem sharp_error (f : ℕ) (hf : 1 ≤ f) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (hx : 64 * (f : ℝ) ^ 2 ≤ min a (1 - a) * n) :
    2 * √(a * (1 - a) / n) ≤ optimum n f a ∧
      optimum n f a ≤
        2 * √(a * (1 - a) / n) * (1 + 4 * ((f : ℝ) / √(min a (1 - a) * n))) := by
  by_cases h : a ≤ 1 / 2
  · have hmin : min a (1 - a) = a := min_eq_left (by linarith)
    rw [hmin] at hx ⊢
    exact sharp_error_half f hf a ha0 h hx
  · have hmin : min a (1 - a) = 1 - a := min_eq_right (by linarith)
    rw [hmin] at hx ⊢
    have h' := sharp_error_half (n := n) f hf (1 - a) (by linarith) (by linarith) hx
    have e : (1 - a) * (1 - (1 - a)) = a * (1 - a) := by ring
    rw [e, ← optimum_symmetry] at h'
    exact h'

/-- The same bound as a ratio, in terms of `x = min{a,1-a} n / f²`. -/
theorem sharp_ratio (f : ℕ) (hf : 1 ≤ f) (a : ℝ)
    (hx : 64 ≤ min a (1 - a) * n / (f : ℝ) ^ 2) :
    0 < a ∧ a < 1 ∧ 1 ≤ optimum n f a / (2 * √(a * (1 - a) / n)) ∧
      optimum n f a / (2 * √(a * (1 - a) / n)) ≤
        1 + 4 / √(min a (1 - a) * n / (f : ℝ) ^ 2) := by
  have hF : (0 : ℝ) < f := by exact_mod_cast hf
  have hF2 : (0 : ℝ) < (f : ℝ) ^ 2 := by positivity
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hx' : 64 * (f : ℝ) ^ 2 ≤ min a (1 - a) * n := (le_div_iff₀ hF2).mp hx
  have hmin : 0 < min a (1 - a) := by
    by_contra h
    have : min a (1 - a) * n ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) hn.le
    nlinarith
  have ha0 : 0 < a := lt_of_lt_of_le hmin (min_le_left _ _)
  have ha1 : a < 1 := by
    have := lt_of_lt_of_le hmin (min_le_right a (1 - a))
    linarith
  obtain ⟨hlow, hup⟩ := sharp_error (n := n) f hf a ha0 ha1 hx'
  have hσ : 0 < 2 * √(a * (1 - a) / n) := by
    have : 0 < a * (1 - a) / n := by
      have : 0 < 1 - a := by linarith
      positivity
    have := Real.sqrt_pos.mpr this
    linarith
  have hroot : √(min a (1 - a) * n / (f : ℝ) ^ 2) = √(min a (1 - a) * n) / f := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_sq hF.le]
  have hfour : 4 / √(min a (1 - a) * n / (f : ℝ) ^ 2) = 4 * ((f : ℝ) / √(min a (1 - a) * n)) := by
    rw [hroot]
    have : 0 < √(min a (1 - a) * n) := Real.sqrt_pos.mpr (by positivity)
    field_simp
  refine ⟨ha0, ha1, (one_le_div hσ).mpr hlow, ?_⟩
  rw [hfour, div_le_iff₀ hσ]
  linarith

/-- Theorem `thm:sharp`, the limit: along any sequence of parameters with
    `min{a,1-a} n / f² → ∞`, the optimum is `(1 + o(1)) 2 sqrt(a(1-a)/n)`. -/
theorem sharp_limit (n : ℕ → ℕ) [∀ k, NeZero (n k)] (f : ℕ → ℕ) (a : ℕ → ℝ)
    (hf : ∀ k, 1 ≤ f k)
    (hx : Tendsto (fun k => min (a k) (1 - a k) * (n k : ℝ) / (f k : ℝ) ^ 2) atTop atTop) :
    Tendsto (fun k => optimum (n k) (f k) (a k) / (2 * √(a k * (1 - a k) / (n k : ℝ))))
      atTop (𝓝 1) := by
  have h0 : Tendsto (fun k => 4 / √(min (a k) (1 - a k) * (n k : ℝ) / (f k : ℝ) ^ 2))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hx)
  have hupper : Tendsto (fun k => 1 + 4 / √(min (a k) (1 - a k) * (n k : ℝ) / (f k : ℝ) ^ 2))
      atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add h0
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [hx.eventually_ge_atTop 64] with k hk
    exact (sharp_ratio (n := n k) (f k) (hf k) (a k) hk).2.2.1
  · filter_upwards [hx.eventually_ge_atTop 64] with k hk
    exact (sharp_ratio (n := n k) (f k) (hf k) (a k) hk).2.2.2

#print axioms sharp_error_arith
#print axioms sharp_error
#print axioms sharp_ratio
#print axioms sharp_limit
end
end QuorumAudit.Paper
