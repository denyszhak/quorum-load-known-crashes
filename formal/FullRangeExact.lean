import FullRangeOrder
import FullRangeProactive
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Floor.Semiring

/-!
The statements of the sections "Every read fraction" and "Unknown
failures" in the form printed in the manuscript: with square roots, real
ceilings, and the optimum as a number.
-/

set_option maxHeartbeats 1000000

namespace QuorumAudit.Paper
noncomputable section
open Finset Circle
variable {n : ℕ} [NeZero n]

/-! ### The two optima -/

/-- `L*_{n,f}(a)`: the least load attainable when the failed set is known
    before routing, as the infimum of the feasible loads. -/
def optimum (n : ℕ) [NeZero n] (f : ℕ) (a : ℝ) : ℝ :=
  sInf {L : ℝ | Feasible (univ : Finset (ZMod n)) f a L}

/-- `L^pro_{n,f}(a)`: the least load attainable by `f`-resilient contact
    sets chosen before the failures. -/
def proactiveOptimum (n : ℕ) [NeZero n] (f : ℕ) (a : ℝ) : ℝ :=
  sInf {L : ℝ | ProactiveFeasible (univ : Finset (ZMod n)) f a L}

theorem card_zmod_univ : (univ : Finset (ZMod n)).card = n := by rw [card_univ, ZMod.card]

theorem feasible_bddBelow (f : ℕ) (hfn : f < n) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    BddBelow {L : ℝ | Feasible (univ : Finset (ZMod n)) f a L} :=
  ⟨0, fun L hL => (known_lower univ f (by rw [card_zmod_univ]; exact hfn) a L ha ha1 hL).1.le⟩

theorem optimum_le (f : ℕ) (hfn : f < n) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) {L : ℝ}
    (h : Feasible (univ : Finset (ZMod n)) f a L) : optimum n f a ≤ L :=
  csInf_le (feasible_bddBelow f hfn a ha ha1) h

theorem le_optimum (f : ℕ) (a : ℝ) {c : ℝ}
    (hne : ∃ L, Feasible (univ : Finset (ZMod n)) f a L)
    (h : ∀ L, Feasible (univ : Finset (ZMod n)) f a L → c ≤ L) : c ≤ optimum n f a :=
  le_csInf hne h

/-- Proposition `prop:symmetry` for the optimum. -/
theorem optimum_symmetry (f : ℕ) (a : ℝ) : optimum n f a = optimum n f (1 - a) := by
  unfold optimum
  congr 1
  ext L
  exact feasible_symmetry _ f a L

theorem proactive_bddBelow (f : ℕ) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    BddBelow {L : ℝ | ProactiveFeasible (univ : Finset (ZMod n)) f a L} :=
  ⟨0, fun L hL => (proactive_lower univ f (by rw [card_zmod_univ]; exact NeZero.pos n)
    a L ha ha1 hL).1.le⟩

theorem proactiveOptimum_le (f : ℕ) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) {L : ℝ}
    (h : ProactiveFeasible (univ : Finset (ZMod n)) f a L) : proactiveOptimum n f a ≤ L :=
  csInf_le (proactive_bddBelow f a ha ha1) h

theorem le_proactiveOptimum (f : ℕ) (a : ℝ) {c : ℝ}
    (hne : ∃ L, ProactiveFeasible (univ : Finset (ZMod n)) f a L)
    (h : ∀ L, ProactiveFeasible (univ : Finset (ZMod n)) f a L → c ≤ L) :
    c ≤ proactiveOptimum n f a :=
  le_csInf hne h

/-! ### Square roots -/

/-- From the squared form to the printed form. -/
theorem two_sqrt_le {t L : ℝ} (hL : 0 ≤ L) (h : 4 * t ≤ L ^ 2) : 2 * √t ≤ L := by
  have h1 : √t ≤ L / 2 := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  linarith

/-- Proposition `prop:amgm` as printed. -/
theorem known_lower_sqrt (f : ℕ) (hfn : f < n) (a L : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (h : Feasible (univ : Finset (ZMod n)) f a L) :
    max (((f : ℝ) + 1) / ((n : ℝ) - f)) (2 * √(a * (1 - a) / ((n : ℝ) - f))) ≤ L := by
  obtain ⟨hL, h1, h2⟩ := known_lower univ f (by rw [card_zmod_univ]; exact hfn) a L ha ha1 h
  rw [card_zmod_univ] at h1 h2
  apply max_le h1
  apply two_sqrt_le hL.le
  have e : 4 * (a * (1 - a) / ((n : ℝ) - f)) = 4 * a * (1 - a) / ((n : ℝ) - f) := by ring
  rw [e]
  exact h2

/-- Theorem `thm:proactive`(1) as printed. -/
theorem proactive_lower_sqrt (f : ℕ) (a L : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (h : ProactiveFeasible (univ : Finset (ZMod n)) f a L) :
    max ((2 * (f : ℝ) + 1) / n) (2 * √((2 * (f : ℝ) + 1) * (a * (1 - a)) / n)) ≤ L := by
  obtain ⟨hL, h1, h2⟩ := proactive_lower univ f (by rw [card_zmod_univ]; exact NeZero.pos n)
    a L ha ha1 h
  rw [card_zmod_univ] at h1 h2
  apply max_le h1
  apply two_sqrt_le hL.le
  have e : 4 * ((2 * (f : ℝ) + 1) * (a * (1 - a)) / n) =
      4 * (2 * (f : ℝ) + 1) * (a * (1 - a)) / n := by ring
  rw [e]
  exact h2

/-! ### Ceilings -/

omit [NeZero n] in
theorem cdiv_eq_ceil (x y : ℕ) (hy : 0 < y) : cdiv x y = ⌈(x : ℝ) / (y : ℝ)⌉₊ := by
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  rcases Nat.eq_zero_or_pos x with hx | hx
  · subst hx
    have h0 : cdiv 0 y = 0 := by
      unfold cdiv
      rw [Nat.zero_add]
      exact Nat.div_eq_of_lt (by omega)
    simp [h0]
  · obtain ⟨h1, h2, h3⟩ := cdiv_spec x y hx hy
    symm
    rw [Nat.ceil_eq_iff (by omega)]
    constructor
    · rw [lt_div_iff₀ hy']
      have : ((y * (cdiv x y - 1) : ℕ) : ℝ) < (x : ℝ) := by exact_mod_cast h3
      rw [Nat.cast_mul] at this
      linarith [mul_comm ((cdiv x y - 1 : ℕ) : ℝ) (y : ℝ)]
    · rw [div_le_iff₀ hy']
      exact_mod_cast h2

/-- Proposition `prop:tiles` as printed, with real ceilings:
    `N = ⌈(m - f(ρ-1))/ρ⌉` and `q = ⌈m/(ρ-f)⌉` for `m = n - f`. -/
theorem prop_tiles_ceil (f ρ : ℕ) (hf : 1 ≤ f) (hρ : f + 1 ≤ ρ) (hroom : f * (ρ - 1) < n - f)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    Admissible (reads n ρ) (rankedWrites n ρ ⌈((n : ℝ) - f) / ((ρ : ℝ) - f)⌉₊) univ f ∧
      ∀ F ⊆ (univ : Finset (ZMod n)), F.card ≤ f →
        RoutesAt (reads n ρ) (rankedWrites n ρ ⌈((n : ℝ) - f) / ((ρ : ℝ) - f)⌉₊) univ F a
          (a / (⌈((n : ℝ) - f - f * ((ρ : ℝ) - 1)) / (ρ : ℝ)⌉₊ : ℕ) +
            (1 - a) * ((⌈((n : ℝ) - f) / ((ρ : ℝ) - f)⌉₊ : ℕ) / ((n : ℝ) - f))) := by
  have hfn : f ≤ n := by omega
  have e1 : (((n - f - f * (ρ - 1) : ℕ)) : ℝ) = (n : ℝ) - f - f * ((ρ : ℝ) - 1) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub hfn, Nat.cast_mul, Nat.cast_sub (by omega)]
    simp
  have e2 : ((n - f : ℕ) : ℝ) = (n : ℝ) - f := Nat.cast_sub hfn
  have e3 : ((ρ - f : ℕ) : ℝ) = (ρ : ℝ) - f := Nat.cast_sub (by omega)
  have hN : cdiv (n - f - f * (ρ - 1)) ρ = ⌈((n : ℝ) - f - f * ((ρ : ℝ) - 1)) / (ρ : ℝ)⌉₊ := by
    rw [cdiv_eq_ceil _ _ (by omega), e1]
  have hq : cdiv (n - f) (ρ - f) = ⌈((n : ℝ) - f) / ((ρ : ℝ) - f)⌉₊ := by
    rw [cdiv_eq_ceil _ _ (by omega), e2, e3]
  have h := prop_tiles (n := n) f ρ hf hρ hroom a ha ha1
  rw [hN, hq] at h
  exact h

/-! ### Theorems `thm:sharp` (bracket) and `thm:order` as printed -/

/-- Theorem `thm:sharp`, the displayed two-sided bound. For `0 < a ≤ 1/2`,
    `m = n - f`, `ρ₀ = sqrt(m(1-a)/a)`, `ε₁ = (f+1)/ρ₀` and
    `ε₂ = f(ρ₀+f+1)/m < 1`:
    `2 sqrt(a(1-a)/m) ≤ L* ≤ sqrt(a(1-a)/m) [1 + (1+ε₁)/(1-ε₂) + ρ₀/m]`. -/
theorem sharp_bracket (f : ℕ) (hf : 1 ≤ f) (hfn : f < n) (a : ℝ) (ha0 : 0 < a) (ha : a ≤ 1 / 2)
    (hε : (f : ℝ) * (√(((n : ℝ) - f) * (1 - a) / a) + f + 1) / ((n : ℝ) - f) < 1) :
    2 * √(a * (1 - a) / ((n : ℝ) - f)) ≤ optimum n f a ∧
      optimum n f a ≤ √(a * (1 - a) / ((n : ℝ) - f)) *
        (1 + (1 + ((f : ℝ) + 1) / √(((n : ℝ) - f) * (1 - a) / a)) /
              (1 - f * (√(((n : ℝ) - f) * (1 - a) / a) + f + 1) / ((n : ℝ) - f)) +
          √(((n : ℝ) - f) * (1 - a) / a) / ((n : ℝ) - f)) := by
  have hM : (0 : ℝ) < (n : ℝ) - f := by
    have : (f : ℝ) < n := by exact_mod_cast hfn
    linarith
  have hb : 0 < 1 - a := by linarith
  have hrad : 0 < ((n : ℝ) - f) * (1 - a) / a := by positivity
  obtain ⟨ρ₀, hρdef⟩ : ∃ ρ₀ : ℝ, ρ₀ = √(((n : ℝ) - f) * (1 - a) / a) := ⟨_, rfl⟩
  rw [← hρdef] at hε ⊢
  have hρ₀ : 0 < ρ₀ := by rw [hρdef]; exact Real.sqrt_pos.mpr hrad
  have hρsq : a * ρ₀ ^ 2 = ((n : ℝ) - f) * (1 - a) := by
    rw [hρdef, Real.sq_sqrt hrad.le]
    field_simp
  have hε' : (f : ℝ) * (ρ₀ + f + 1) < (n : ℝ) - f := by rwa [div_lt_one hM] at hε
  have hs0 : 0 ≤ a * ρ₀ / ((n : ℝ) - f) := by positivity
  obtain ⟨hs2, hfeas⟩ := sharp_upper_bracket (n := n) f ⌈ρ₀⌉₊ hf hfn.le ρ₀ (a * ρ₀ / ((n : ℝ) - f))
    hρ₀ (Nat.le_ceil ρ₀) (Nat.ceil_lt_add_one hρ₀.le).le hε' a ha0.le (by linarith) hρsq rfl
  have hsqrt : √(a * (1 - a) / ((n : ℝ) - f)) = a * ρ₀ / ((n : ℝ) - f) := by
    rw [← hs2, Real.sqrt_sq hs0]
  rw [hsqrt]
  constructor
  · apply le_optimum f a ⟨_, hfeas⟩
    intro L hL
    have h := known_lower_sqrt (n := n) f hfn a L ha0.le (by linarith) hL
    rw [hsqrt] at h
    exact (le_max_right _ _).trans h
  · exact optimum_le f hfn a ha0.le (by linarith) hfeas

/-- Theorem `thm:order` as printed: if `m = n - f ≥ 16 f²`, then
    `max{(f+1)/m, 2 sqrt(a(1-a)/m)} ≤ L* ≤ 20 max{(f+1)/m, sqrt(a(1-a)/m)}`,
    and the upper value is feasible. -/
theorem order_sqrt (f : ℕ) (hf : 1 ≤ f) (hfn : f < n) (hm : 16 * f * f ≤ n - f)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    max (((f : ℝ) + 1) / ((n : ℝ) - f)) (2 * √(a * (1 - a) / ((n : ℝ) - f))) ≤ optimum n f a ∧
      optimum n f a ≤
        20 * max (((f : ℝ) + 1) / ((n : ℝ) - f)) (√(a * (1 - a) / ((n : ℝ) - f))) ∧
      Feasible (univ : Finset (ZMod n)) f a
        (20 * max (((f : ℝ) + 1) / ((n : ℝ) - f)) (√(a * (1 - a) / ((n : ℝ) - f)))) := by
  have hM : (0 : ℝ) < (n : ℝ) - f := by
    have : (f : ℝ) < n := by exact_mod_cast hfn
    linarith
  have ht : 0 ≤ a * (1 - a) / ((n : ℝ) - f) :=
    div_nonneg (mul_nonneg ha (by linarith)) hM.le
  have hfeas : Feasible (univ : Finset (ZMod n)) f a
      (20 * max (((f : ℝ) + 1) / ((n : ℝ) - f)) (√(a * (1 - a) / ((n : ℝ) - f)))) := by
    apply order_upper f hf hfn.le hm a _ ha ha1
    · have h := le_max_left (((f : ℝ) + 1) / ((n : ℝ) - f)) (√(a * (1 - a) / ((n : ℝ) - f)))
      have e : 20 * ((f : ℝ) + 1) / ((n : ℝ) - f) = 20 * (((f : ℝ) + 1) / ((n : ℝ) - f)) := by
        ring
      rw [e]
      linarith
    · have h := le_max_right (((f : ℝ) + 1) / ((n : ℝ) - f)) (√(a * (1 - a) / ((n : ℝ) - f)))
      have hs0 : 0 ≤ √(a * (1 - a) / ((n : ℝ) - f)) := Real.sqrt_nonneg _
      have hsq : (20 * √(a * (1 - a) / ((n : ℝ) - f))) ^ 2 ≤
          (20 * max (((f : ℝ) + 1) / ((n : ℝ) - f)) (√(a * (1 - a) / ((n : ℝ) - f)))) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 2
      have e : (20 * √(a * (1 - a) / ((n : ℝ) - f))) ^ 2 =
          400 * (a * (1 - a)) / ((n : ℝ) - f) := by
        rw [mul_pow, Real.sq_sqrt ht]
        ring
      rw [e] at hsq
      exact hsq
  refine ⟨?_, optimum_le f hfn a ha ha1 hfeas, hfeas⟩
  apply le_optimum f a ⟨_, hfeas⟩
  intro L hL
  exact known_lower_sqrt (n := n) f hfn a L ha ha1 hL

/-! ### Theorem `thm:proactive`(3) as printed -/

/-- At `a_q = q² / (q² + d n)` with `q ∣ n`, `q ≥ d = 2f+1`:
    `L^pro = 2 d q / (q² + d n) = 2 sqrt(d a_q (1 - a_q) / n)`. -/
theorem proactive_exact_value (f q : ℕ) (hq : 2 * f + 1 ≤ q) (hdiv : q ∣ n) :
    proactiveOptimum n f ((q : ℝ) ^ 2 / ((q : ℝ) ^ 2 + (2 * (f : ℝ) + 1) * n)) =
        2 * (2 * (f : ℝ) + 1) * q / ((q : ℝ) ^ 2 + (2 * (f : ℝ) + 1) * n) ∧
      2 * (2 * (f : ℝ) + 1) * q / ((q : ℝ) ^ 2 + (2 * (f : ℝ) + 1) * n) =
        2 * √((2 * (f : ℝ) + 1) *
          ((q : ℝ) ^ 2 / ((q : ℝ) ^ 2 + (2 * (f : ℝ) + 1) * n) *
            (1 - (q : ℝ) ^ 2 / ((q : ℝ) ^ 2 + (2 * (f : ℝ) + 1) * n))) / n) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hd : (0 : ℝ) < 2 * (f : ℝ) + 1 := by positivity
  have hD : (0 : ℝ) < (q : ℝ) ^ 2 + (2 * (f : ℝ) + 1) * n := by positivity
  constructor
  · unfold proactiveOptimum
    have hset : {L : ℝ | ProactiveFeasible (univ : Finset (ZMod n)) f
          ((q : ℝ) ^ 2 / ((q : ℝ) ^ 2 + (2 * (f : ℝ) + 1) * n)) L} =
        Set.Ici (2 * (2 * (f : ℝ) + 1) * q / ((q : ℝ) ^ 2 + (2 * (f : ℝ) + 1) * n)) := by
      ext L
      exact proactive_exact (n := n) f q hq hdiv L
    rw [hset, csInf_Ici]
  · have hval : (0 : ℝ) ≤ (2 * (f : ℝ) + 1) * q / ((q : ℝ) ^ 2 + (2 * (f : ℝ) + 1) * n) := by
      positivity
    have e : (2 * (f : ℝ) + 1) *
          ((q : ℝ) ^ 2 / ((q : ℝ) ^ 2 + (2 * (f : ℝ) + 1) * n) *
            (1 - (q : ℝ) ^ 2 / ((q : ℝ) ^ 2 + (2 * (f : ℝ) + 1) * n))) / n =
        ((2 * (f : ℝ) + 1) * q / ((q : ℝ) ^ 2 + (2 * (f : ℝ) + 1) * n)) ^ 2 := by
      field_simp
      ring
    rw [e, Real.sqrt_sq hval]
    ring

/-- `L^pro_{n,f}(1/2) = sqrt(d/n)` when `n = d s²`, `d = 2f+1`. -/
theorem proactive_half (f s : ℕ) (hs : 1 ≤ s) (hn : n = (2 * f + 1) * s * s) :
    proactiveOptimum n f (1 / 2) = √((2 * (f : ℝ) + 1) / n) := by
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs
  have hd : (0 : ℝ) < 2 * (f : ℝ) + 1 := by positivity
  have hncast : (n : ℝ) = (2 * (f : ℝ) + 1) * s * s := by rw [hn]; push_cast; ring
  have hq : 2 * f + 1 ≤ (2 * f + 1) * s := Nat.le_mul_of_pos_right _ (by omega)
  have hdiv : (2 * f + 1) * s ∣ n := ⟨s, hn⟩
  obtain ⟨h1, _⟩ := proactive_exact_value (n := n) f ((2 * f + 1) * s) hq hdiv
  have ea : ((((2 * f + 1) * s : ℕ)) : ℝ) ^ 2 /
      ((((2 * f + 1) * s : ℕ) : ℝ) ^ 2 + (2 * (f : ℝ) + 1) * n) = 1 / 2 := by
    rw [hncast]
    push_cast
    field_simp
    ring
  rw [ea] at h1
  rw [h1, hncast]
  have e1 : 2 * (2 * (f : ℝ) + 1) * (((2 * f + 1) * s : ℕ) : ℝ) /
      ((((2 * f + 1) * s : ℕ) : ℝ) ^ 2 + (2 * (f : ℝ) + 1) * ((2 * (f : ℝ) + 1) * s * s)) =
      1 / s := by
    push_cast
    field_simp
    ring
  have e2 : (2 * (f : ℝ) + 1) / ((2 * (f : ℝ) + 1) * s * s) = (1 / (s : ℝ)) ^ 2 := by
    field_simp
  rw [e1, e2, Real.sqrt_sq (by positivity)]

#print axioms optimum_symmetry
#print axioms known_lower_sqrt
#print axioms proactive_lower_sqrt
#print axioms prop_tiles_ceil
#print axioms sharp_bracket
#print axioms order_sqrt
#print axioms proactive_exact_value
#print axioms proactive_half
end
end QuorumAudit.Paper
