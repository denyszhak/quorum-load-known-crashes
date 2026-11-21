import FullRangeTiles

/-!
Proposition `prop:tiles` in the form printed in the manuscript, and the
explicit constant-factor bound of Theorem `thm:order`.
-/

set_option maxHeartbeats 2000000

namespace QuorumAudit.Paper
noncomputable section
open Finset Circle
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- Ceiling of `x / y` for natural numbers. -/
def cdiv (x y : ℕ) : ℕ := (x + y - 1) / y

theorem cdiv_spec (x y : ℕ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    1 ≤ cdiv x y ∧ x ≤ cdiv x y * y ∧ y * (cdiv x y - 1) < x := by
  unfold cdiv
  have h1 := Nat.div_add_mod (x + y - 1) y
  have h2 := Nat.mod_lt (x + y - 1) (by omega : 0 < y)
  generalize (x + y - 1) / y = c at h1 ⊢
  generalize (x + y - 1) % y = r at h1 h2
  rcases Nat.eq_zero_or_pos c with hc | hc
  · rw [hc, Nat.mul_zero] at h1
    omega
  · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    rw [Nat.mul_succ] at h1
    refine ⟨by omega, ?_, ?_⟩
    · rw [Nat.mul_comm, Nat.mul_succ]
      omega
    · rw [Nat.add_sub_cancel]
      omega

/-- Proposition `prop:tiles` as printed: with `m = n - f`,
    `N = ⌈(m - f(ρ-1))/ρ⌉` and `q = ⌈m/(ρ-f)⌉`, the interval reads and the
    `q`-element hitting writes are admissible and have load at most
    `a/N + (1-a) q/m` after every allowed failed set. -/
theorem prop_tiles (f ρ : ℕ) (hf : 1 ≤ f) (hρ : f + 1 ≤ ρ) (hroom : f * (ρ - 1) < n - f)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    Admissible (reads n ρ) (rankedWrites n ρ (cdiv (n - f) (ρ - f))) univ f ∧
      ∀ F ⊆ (univ : Finset (ZMod n)), F.card ≤ f →
        RoutesAt (reads n ρ) (rankedWrites n ρ (cdiv (n - f) (ρ - f))) univ F a
          (a / (cdiv (n - f - f * (ρ - 1)) ρ : ℕ) +
            (1 - a) * ((cdiv (n - f) (ρ - f) : ℕ) / ((n : ℝ) - f))) := by
  obtain ⟨hN1, hN2, hN3⟩ := cdiv_spec (n - f - f * (ρ - 1)) ρ (by omega) (by omega)
  obtain ⟨hq1, hq2, hq3⟩ := cdiv_spec (n - f) (ρ - f) (by omega) (by omega)
  have hq4 : cdiv (n - f) (ρ - f) - 1 ≤ (ρ - f) * (cdiv (n - f) (ρ - f) - 1) :=
    Nat.le_mul_of_pos_left _ (by omega)
  exact tiles_feasible f ρ _ _ hf hρ hN1 (by omega) hq2 (by omega) a ha ha1

/-- A simpler bound without ceilings: for every interval length `ρ` with
    `f + 1 ≤ ρ` and `f(ρ-1) < m`, the load
    `a ρ / (m - f(ρ-1)) + (1-a)(1/(ρ-f) + 1/m)` is feasible. Theorem
    `thm:sharp` evaluates this at `ρ = ⌈ρ₀⌉ + f`. -/
theorem tiles_simple (f ρ : ℕ) (hf : 1 ≤ f) (hρ : f + 1 ≤ ρ) (hroom : f * (ρ - 1) < n - f)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    Feasible (univ : Finset (ZMod n)) f a
      (a * ρ / ((n : ℝ) - f - f * ((ρ : ℝ) - 1)) +
        (1 - a) * (1 / ((ρ : ℝ) - f) + 1 / ((n : ℝ) - f))) := by
  obtain ⟨hN1, hN2, hN3⟩ := cdiv_spec (n - f - f * (ρ - 1)) ρ (by omega) (by omega)
  obtain ⟨hq1, hq2, hq3⟩ := cdiv_spec (n - f) (ρ - f) (by omega) (by omega)
  obtain ⟨had, hroutes⟩ := prop_tiles (n := n) f ρ hf hρ hroom a ha ha1
  apply feasible_mono _ ⟨_, _, had, hroutes⟩
  set N := cdiv (n - f - f * (ρ - 1)) ρ
  set q := cdiv (n - f) (ρ - f)
  have hfn : f ≤ n := by omega
  have hmpos : (0 : ℝ) < (n : ℝ) - f := by
    have : ((n - f : ℕ) : ℝ) = (n : ℝ) - f := Nat.cast_sub hfn
    have h0 : (0 : ℝ) < ((n - f : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - f)
    linarith
  have hdpos : (0 : ℝ) < (ρ : ℝ) - f := by
    have : (f : ℝ) + 1 ≤ ρ := by exact_mod_cast hρ
    linarith
  have hxcast : (((n - f - f * (ρ - 1) : ℕ)) : ℝ) = (n : ℝ) - f - f * ((ρ : ℝ) - 1) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub hfn, Nat.cast_mul, Nat.cast_sub (by omega)]
    simp
  have hxpos : (0 : ℝ) < (n : ℝ) - f - f * ((ρ : ℝ) - 1) := by
    rw [← hxcast]
    exact_mod_cast (by omega : 0 < n - f - f * (ρ - 1))
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hρpos : (0 : ℝ) < ρ := by exact_mod_cast (by omega : 0 < ρ)
  have hNreal : (n : ℝ) - f - f * ((ρ : ℝ) - 1) ≤ N * ρ := by
    rw [← hxcast]
    exact_mod_cast hN2
  have hqreal : ((ρ : ℝ) - f) * ((q : ℝ) - 1) ≤ (n : ℝ) - f := by
    have h : ((ρ - f) * (q - 1) : ℕ) ≤ n - f := hq3.le
    have hc : (((ρ - f) * (q - 1) : ℕ) : ℝ) = ((ρ : ℝ) - f) * ((q : ℝ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_sub hq1]
      simp
    have hc2 : ((n - f : ℕ) : ℝ) = (n : ℝ) - f := Nat.cast_sub hfn
    rw [← hc, ← hc2]
    exact_mod_cast h
  have h1 : a / (N : ℝ) ≤ a * ρ / ((n : ℝ) - f - f * ((ρ : ℝ) - 1)) := by
    rw [div_le_div_iff₀ hNpos hxpos]
    nlinarith [mul_le_mul_of_nonneg_left hNreal ha]
  have h2 : (q : ℝ) / ((n : ℝ) - f) ≤ 1 / ((ρ : ℝ) - f) + 1 / ((n : ℝ) - f) := by
    have e : 1 / ((ρ : ℝ) - f) + 1 / ((n : ℝ) - f) =
        ((n : ℝ) - f + ((ρ : ℝ) - f)) / (((ρ : ℝ) - f) * ((n : ℝ) - f)) := by
      field_simp
    rw [e, div_le_div_iff₀ hmpos (mul_pos hdpos hmpos)]
    nlinarith
  have h3 := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 1 - a)
  linarith

/-! ### The constant-factor bound (Theorem `thm:order`) -/

/-- Real arithmetic for the case `a m < 16 f²`, with interval length
    `r = ⌊m / (2f)⌋`. -/
theorem order_corner_arith (a M F r : ℝ) (ha : 0 ≤ a) (hF : 1 ≤ F)
    (hM : 16 * F ^ 2 ≤ M) (hsmall : a * M < 16 * F ^ 2)
    (hr1 : 2 * F * r ≤ M) (hr2 : M < 2 * F * (r + 1)) :
    a * r / (M - F * (r - 1)) + (1 - a) * (1 / (r - F) + 1 / M) ≤ 20 * (F + 1) / M := by
  have hF0 : 0 < F := by linarith
  have hFF : F ≤ F ^ 2 := by nlinarith
  have hM0 : 0 < M := by nlinarith
  have hrF : 3 * M < 8 * F * (r - F) := by nlinarith
  have hrF0 : 0 < r - F := by
    by_contra h
    have h' : r - F ≤ 0 := not_lt.mp h
    have : 8 * F * (r - F) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h'
    linarith
  have hr0 : 0 ≤ r := by linarith
  have hD : M / 2 < M - F * (r - 1) := by nlinarith
  have hD0 : 0 < M - F * (r - 1) := by linarith
  have hA : a * r / (M - F * (r - 1)) ≤ 16 * F / M := by
    rw [div_le_div_iff₀ hD0 hM0]
    have h1 : a * M * r ≤ 16 * F ^ 2 * r := mul_le_mul_of_nonneg_right hsmall.le hr0
    have h2 : 8 * F * (2 * F * r) ≤ 8 * F * M := mul_le_mul_of_nonneg_left hr1 (by positivity)
    have h3 : 16 * F * (M / 2) < 16 * F * (M - F * (r - 1)) :=
      mul_lt_mul_of_pos_left hD (by positivity)
    nlinarith
  have hB1 : 1 / (r - F) ≤ 8 * F / (3 * M) := by
    rw [div_le_div_iff₀ hrF0 (by positivity)]
    linarith
  have hB0 : 0 ≤ 1 / (r - F) + 1 / M := by positivity
  have hB : (1 - a) * (1 / (r - F) + 1 / M) ≤ 8 * F / (3 * M) + 1 / M := by
    have h1 : (1 - a) * (1 / (r - F) + 1 / M) ≤ 1 * (1 / (r - F) + 1 / M) :=
      mul_le_mul_of_nonneg_right (by linarith) hB0
    linarith
  have hsum : 16 * F / M + (8 * F / (3 * M) + 1 / M) = (56 * F / 3 + 1) / M := by
    field_simp
    ring
  have hfinal : (56 * F / 3 + 1) / M ≤ 20 * (F + 1) / M :=
    div_le_div_of_nonneg_right (by linarith) hM0.le
  linarith

/-- Real arithmetic for the case `a m ≥ 16 f²`. Here `T` is the least
    integer with `m(1-a) ≤ a T²` and the interval length is `R = T + F`. -/
theorem order_bulk_arith (a M F R T L : ℝ) (hR : R = T + F) (ha0 : 0 < a) (ha : a ≤ 1 / 2)
    (hF : 1 ≤ F) (hbig : 16 * F ^ 2 ≤ a * M) (hT1 : M * (1 - a) ≤ a * T ^ 2)
    (hT2 : a * (T - 1) ^ 2 < M * (1 - a)) (hT : 1 ≤ T) (hL0 : 0 ≤ L)
    (hL : 400 * (a * (1 - a)) ≤ M * L ^ 2) :
    F * (R - 1) < M ∧
      a * R / (M - F * (R - 1)) + (1 - a) * (1 / (R - F) + 1 / M) ≤ L := by
  subst hR
  have hTF : T + F - F = T := by ring
  rw [hTF]
  have hb : 0 < 1 - a := by linarith
  have hF0 : 0 < F := by linarith
  have hT0 : 0 < T := by linarith
  have hFF : 1 ≤ F ^ 2 := by nlinarith
  have hM0 : 0 < M := by
    by_contra h
    have : a * M ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha0.le (not_lt.mp h)
    linarith
  have haM : a * M ≤ M / 2 := by nlinarith
  have hF2 : 16 * F ^ 2 ≤ M / 2 := by linarith
  have hM32 : 32 ≤ M := by linarith
  have hTM : M ≤ T ^ 2 := by
    have h1 : a * M ≤ a * T ^ 2 := by nlinarith
    exact le_of_mul_le_mul_left h1 ha0
  have hT4 : 4 * F ≤ T := by
    by_contra h
    have h' : T < 4 * F := not_le.mp h
    have h2 : T ^ 2 < (4 * F) ^ 2 := pow_lt_pow_left₀ h' hT0.le (by norm_num)
    nlinarith
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = T - 1 := ⟨_, rfl⟩
  rw [← hu] at hT2
  have hTu : T = u + 1 := by linarith
  have hu3 : 3 ≤ u := by linarith
  have hu0 : 0 ≤ u := by linarith
  have hFu : F * u < M / 4 := by
    by_contra h
    have h' : M / 4 ≤ F * u := not_lt.mp h
    have h1 : (M / 4) ^ 2 ≤ (F * u) ^ 2 := pow_le_pow_left₀ (by positivity) h' 2
    have h3 : F ^ 2 * u ^ 2 ≤ a * M / 16 * u ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg u)
    have h5 : M / 16 * (a * u ^ 2) < M / 16 * (M * (1 - a)) :=
      mul_lt_mul_of_pos_left hT2 (by positivity)
    have h6 : M / 16 * (M * (1 - a)) ≤ M ^ 2 / 16 := by nlinarith
    have h7 : (M / 4) ^ 2 = M ^ 2 / 16 := by ring
    have h8 : (F * u) ^ 2 = F ^ 2 * u ^ 2 := by ring
    have h9 : a * M / 16 * u ^ 2 = M / 16 * (a * u ^ 2) := by ring
    linarith
  have hsplit : F * (T + F - 1) = F * u + F ^ 2 := by rw [hTu]; ring
  have hD : 23 * M / 32 < M - F * (T + F - 1) := by rw [hsplit]; linarith
  have hD0 : 0 < M - F * (T + F - 1) := by linarith
  refine ⟨by linarith, ?_⟩
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = a * T / M := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have hsM : s * M = a * T := by rw [hs]; field_simp
  have hA : a * (T + F) / (M - F * (T + F - 1)) ≤ 40 / 23 * s := by
    rw [div_le_iff₀ hD0]
    have h1 : 40 / 23 * s * (23 * M / 32) ≤ 40 / 23 * s * (M - F * (T + F - 1)) :=
      mul_le_mul_of_nonneg_left hD.le (by positivity)
    have h2 : 40 / 23 * s * (23 * M / 32) = 5 / 4 * (s * M) := by ring
    have h3 : a * F ≤ a * T / 4 := by nlinarith
    linarith
  have huM : u < M / 4 := by
    have : u ≤ F * u := by nlinarith
    linarith
  have hB : (1 - a) * (1 / T + 1 / M) ≤ 41 / 32 * s := by
    have h1 : 1 / M ≤ 9 / 32 / T := by
      rw [div_le_div_iff₀ hM0 hT0]
      linarith
    have h2 : (1 - a) / T ≤ s := by
      rw [hs, div_le_div_iff₀ hT0 hM0]
      nlinarith
    have h3 : (1 - a) * (1 / T + 1 / M) ≤ (1 - a) * (1 / T + 9 / 32 / T) :=
      mul_le_mul_of_nonneg_left (by linarith) hb.le
    have h4 : (1 - a) * (1 / T + 9 / 32 / T) = 41 / 32 * ((1 - a) / T) := by
      field_simp
      ring
    linarith
  have hX : a * (T + F) / (M - F * (T + F - 1)) + (1 - a) * (1 / T + 1 / M) ≤ 7 / 2 * s := by
    linarith
  have hs2 : (7 / 2 * s) ^ 2 * M ≤ M * L ^ 2 := by
    have h1 : T ≤ 4 / 3 * u := by linarith
    have h2 : T ^ 2 ≤ (4 / 3 * u) ^ 2 := pow_le_pow_left₀ hT0.le h1 2
    have h3 : a * T ^ 2 ≤ 16 / 9 * (a * u ^ 2) := by nlinarith
    have h4 : a * T ^ 2 ≤ 16 / 9 * (M * (1 - a)) := by linarith
    have h5 : (7 / 2 * s) ^ 2 * M = 49 / 4 * (a * (a * T ^ 2)) / M := by
      rw [hs]
      field_simp
      norm_num
    rw [h5, div_le_iff₀ hM0]
    have h6 : a * (a * T ^ 2) ≤ a * (16 / 9 * (M * (1 - a))) :=
      mul_le_mul_of_nonneg_left h4 ha0.le
    have h7 : 400 * (a * (1 - a)) * M ≤ M * L ^ 2 * M :=
      mul_le_mul_of_nonneg_right hL hM0.le
    have h8 : 0 ≤ a * (1 - a) * M := by positivity
    nlinarith
  have hsL : 7 / 2 * s ≤ L := by
    by_contra h
    have h' : L < 7 / 2 * s := not_le.mp h
    have h2 : L ^ 2 < (7 / 2 * s) ^ 2 := pow_lt_pow_left₀ h' hL0 (by norm_num)
    have h3 : M * L ^ 2 < M * (7 / 2 * s) ^ 2 := mul_lt_mul_of_pos_left h2 hM0
    linarith
  linarith

/-- Theorem `thm:order`, upper bound. If `m = n - f ≥ 16 f²`, every load
    `L` with `L ≥ 20 (f+1)/m` and `L² ≥ 400 a(1-a)/m`, that is,
    `L ≥ 20 max{(f+1)/m, sqrt(a(1-a)/m)}`, is feasible. -/
theorem order_upper (f : ℕ) (hf : 1 ≤ f) (hfn : f ≤ n) (hm : 16 * f * f ≤ n - f)
    (a L : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (h1 : 20 * ((f : ℝ) + 1) / ((n : ℝ) - f) ≤ L)
    (h2 : 400 * (a * (1 - a)) / ((n : ℝ) - f) ≤ L ^ 2) :
    Feasible (univ : Finset (ZMod n)) f a L := by
  have hF : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hMcast : ((n - f : ℕ) : ℝ) = (n : ℝ) - f := Nat.cast_sub hfn
  have hM : 16 * (f : ℝ) ^ 2 ≤ (n : ℝ) - f := by
    rw [← hMcast]
    have : ((16 * f * f : ℕ) : ℝ) ≤ ((n - f : ℕ) : ℝ) := by exact_mod_cast hm
    push_cast at this
    nlinarith
  have hM0 : (0 : ℝ) < (n : ℝ) - f := by nlinarith
  have hL0 : 0 ≤ L := by
    have : (0 : ℝ) ≤ 20 * ((f : ℝ) + 1) / ((n : ℝ) - f) := by positivity
    linarith
  have key : ∀ b : ℝ, 0 ≤ b → b ≤ 1 / 2 → 400 * (b * (1 - b)) / ((n : ℝ) - f) ≤ L ^ 2 →
      Feasible (univ : Finset (ZMod n)) f b L := by
    intro b hb0 hb hb2
    have hb2' : 400 * (b * (1 - b)) ≤ ((n : ℝ) - f) * L ^ 2 := by
      rw [div_le_iff₀ hM0] at hb2
      linarith
    by_cases hcase : 16 * (f : ℝ) ^ 2 ≤ b * ((n : ℝ) - f)
    · -- the bulk: least `t` with `m (1-b) ≤ b t²`
      have hbpos : 0 < b := by
        by_contra h
        have hb00 : b = 0 := le_antisymm (not_lt.mp h) hb0
        rw [hb00, zero_mul] at hcase
        nlinarith
      have hex : ∃ t : ℕ, ((n : ℝ) - f) * (1 - b) ≤ b * (t : ℝ) ^ 2 := by
        refine ⟨n - f, ?_⟩
        rw [hMcast]
        have h16 : (16 : ℝ) ≤ b * ((n : ℝ) - f) := by nlinarith
        nlinarith
      classical
      obtain ⟨t, ht, hmin⟩ : ∃ t : ℕ, ((n : ℝ) - f) * (1 - b) ≤ b * (t : ℝ) ^ 2 ∧
          ∀ t' < t, ¬ (((n : ℝ) - f) * (1 - b) ≤ b * (t' : ℝ) ^ 2) :=
        ⟨Nat.find hex, Nat.find_spec hex, fun t' ht' => Nat.find_min hex ht'⟩
      have ht1 : 1 ≤ t := by
        rcases Nat.eq_zero_or_pos t with h0 | h0
        · rw [h0] at ht
          norm_num at ht
          nlinarith
        · exact h0
      have hTcast : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
        rw [Nat.cast_sub ht1]
        simp
      have hT2 : b * ((t : ℝ) - 1) ^ 2 < ((n : ℝ) - f) * (1 - b) := by
        have := hmin (t - 1) (by omega)
        rw [hTcast] at this
        exact not_le.mp this
      have hR : ((t + f : ℕ) : ℝ) = (t : ℝ) + f := by push_cast; ring
      obtain ⟨hroomR, hloadR⟩ := order_bulk_arith b ((n : ℝ) - f) f ((t + f : ℕ) : ℝ) t L hR
        hbpos hb hF hcase ht hT2 (by exact_mod_cast ht1) hL0 hb2'
      have hroom : f * (t + f - 1) < n - f := by
        have hc : ((f * (t + f - 1) : ℕ) : ℝ) = (f : ℝ) * (((t + f : ℕ) : ℝ) - 1) := by
          rw [Nat.cast_mul, Nat.cast_sub (by omega)]
          simp
        have : ((f * (t + f - 1) : ℕ) : ℝ) < ((n - f : ℕ) : ℝ) := by
          rw [hc, hMcast]
          exact hroomR
        exact_mod_cast this
      exact feasible_mono hloadR
        (tiles_simple (n := n) f (t + f) hf (by omega) hroom b hb0 (by linarith))
    · -- the corner: interval length `⌊m / (2f)⌋`
      have hsmall : b * ((n : ℝ) - f) < 16 * (f : ℝ) ^ 2 := not_le.mp hcase
      have h2f : 0 < 2 * f := by omega
      have hρ8 : 8 * f ≤ (n - f) / (2 * f) := by
        rw [Nat.le_div_iff_mul_le h2f]
        calc 8 * f * (2 * f) = 16 * f * f := by ring
          _ ≤ n - f := hm
      have hρ1 : (n - f) / (2 * f) * (2 * f) ≤ n - f := Nat.div_mul_le_self _ _
      have hρ2 : n - f < 2 * f * ((n - f) / (2 * f) + 1) := Nat.lt_mul_div_succ _ h2f
      generalize (n - f) / (2 * f) = ρ at hρ8 hρ1 hρ2
      have hr1 : 2 * (f : ℝ) * ρ ≤ (n : ℝ) - f := by
        rw [← hMcast]
        have : ((ρ * (2 * f) : ℕ) : ℝ) ≤ ((n - f : ℕ) : ℝ) := by exact_mod_cast hρ1
        push_cast at this
        linarith
      have hr2 : (n : ℝ) - f < 2 * (f : ℝ) * ((ρ : ℝ) + 1) := by
        rw [← hMcast]
        have : ((n - f : ℕ) : ℝ) < ((2 * f * (ρ + 1) : ℕ) : ℝ) := by exact_mod_cast hρ2
        push_cast at this
        linarith
      have hroom : f * (ρ - 1) < n - f := by
        have h3 : f * (ρ - 1) ≤ f * ρ := Nat.mul_le_mul_left f (Nat.sub_le ρ 1)
        have h4 : ρ * (2 * f) = 2 * (f * ρ) := by ring
        have h5 : 0 < n - f := by
          have : 0 < 16 * f * f := by positivity
          omega
        omega
      have harith := order_corner_arith b ((n : ℝ) - f) f ρ hb0 hF hM hsmall hr1 hr2
      exact feasible_mono (harith.trans h1)
        (tiles_simple (n := n) f ρ hf (by omega) hroom b hb0 (by linarith))
  by_cases hhalf : a ≤ 1 / 2
  · exact key a ha hhalf h2
  · have hhalf' : 1 - a ≤ 1 / 2 := by linarith
    have e : (1 - a) * (1 - (1 - a)) = a * (1 - a) := by ring
    exact (feasible_symmetry _ f a L).mpr (key (1 - a) (by linarith) hhalf' (by rw [e]; exact h2))

/-- Theorem `thm:order`: for `m = n - f ≥ 16 f²` the optimum lies between
    `max{(f+1)/m, 2 sqrt(a(1-a)/m)}` and `20 max{(f+1)/m, sqrt(a(1-a)/m)}`.
    Both sides are stated without square roots. -/
theorem order_theorem (f : ℕ) (hf : 1 ≤ f) (hfn : f < n) (hm : 16 * f * f ≤ n - f)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (∀ L : ℝ, Feasible (univ : Finset (ZMod n)) f a L →
        0 < L ∧ ((f : ℝ) + 1) / ((n : ℝ) - f) ≤ L ∧ 4 * a * (1 - a) / ((n : ℝ) - f) ≤ L ^ 2) ∧
      (∀ L : ℝ, 20 * ((f : ℝ) + 1) / ((n : ℝ) - f) ≤ L →
        400 * (a * (1 - a)) / ((n : ℝ) - f) ≤ L ^ 2 →
        Feasible (univ : Finset (ZMod n)) f a L) := by
  constructor
  · intro L h
    have := known_lower (univ : Finset (ZMod n)) f (by rw [card_univ, ZMod.card]; exact hfn)
      a L ha ha1 h
    rwa [card_univ, ZMod.card] at this
  · intro L h1 h2
    exact order_upper f hf hfn.le hm a L ha ha1 h1 h2

/-! ### The upper bound of Theorem `thm:sharp` -/

/-- The two displayed inequalities in the proof of Theorem `thm:sharp`,
    for any real `ρ₀ > 0` and an integer `t` with `ρ₀ ≤ t ≤ ρ₀ + 1`
    (the manuscript takes `t = ⌈ρ₀⌉`): if `f (ρ₀ + f + 1) < m`, the load
    `a (ρ₀+f+1) / (m - f (ρ₀+f+1)) + (1-a) (1/ρ₀ + 1/m)` is feasible. -/
theorem sharp_upper (f t : ℕ) (hf : 1 ≤ f) (hfn : f ≤ n) (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀)
    (ht1 : ρ₀ ≤ t) (ht2 : (t : ℝ) ≤ ρ₀ + 1)
    (hε : (f : ℝ) * (ρ₀ + f + 1) < (n : ℝ) - f) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    Feasible (univ : Finset (ZMod n)) f a
      (a * (ρ₀ + f + 1) / ((n : ℝ) - f - f * (ρ₀ + f + 1)) +
        (1 - a) * (1 / ρ₀ + 1 / ((n : ℝ) - f))) := by
  have hF : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hMcast : ((n - f : ℕ) : ℝ) = (n : ℝ) - f := Nat.cast_sub hfn
  have htpos : 1 ≤ t := by
    have : (0 : ℝ) < t := lt_of_lt_of_le hρ₀ ht1
    exact_mod_cast this
  have hR : ((t + f : ℕ) : ℝ) = (t : ℝ) + f := by push_cast; ring
  have hD2 : 0 < (n : ℝ) - f - f * (ρ₀ + f + 1) := by linarith
  have hden : (n : ℝ) - f - f * (ρ₀ + f + 1) ≤ (n : ℝ) - f - f * (((t + f : ℕ) : ℝ) - 1) := by
    rw [hR]
    nlinarith
  have hD1 : 0 < (n : ℝ) - f - f * (((t + f : ℕ) : ℝ) - 1) := lt_of_lt_of_le hD2 hden
  have hroom : f * (t + f - 1) < n - f := by
    have hc : ((f * (t + f - 1) : ℕ) : ℝ) = (f : ℝ) * (((t + f : ℕ) : ℝ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega)]
      simp
    have : ((f * (t + f - 1) : ℕ) : ℝ) < ((n - f : ℕ) : ℝ) := by
      rw [hc, hMcast]
      linarith
    exact_mod_cast this
  apply feasible_mono _ (tiles_simple (n := n) f (t + f) hf (by omega) hroom a ha ha1)
  have hnum : ((t + f : ℕ) : ℝ) ≤ ρ₀ + f + 1 := by rw [hR]; linarith
  have hnum0 : (0 : ℝ) ≤ ρ₀ + f + 1 := by positivity
  have hA : a * ((t + f : ℕ) : ℝ) / ((n : ℝ) - f - f * (((t + f : ℕ) : ℝ) - 1)) ≤
      a * (ρ₀ + f + 1) / ((n : ℝ) - f - f * (ρ₀ + f + 1)) := by
    rw [div_le_div_iff₀ hD1 hD2]
    have hmul : ((t + f : ℕ) : ℝ) * ((n : ℝ) - f - f * (ρ₀ + f + 1)) ≤
        (ρ₀ + f + 1) * ((n : ℝ) - f - f * (((t + f : ℕ) : ℝ) - 1)) :=
      mul_le_mul hnum hden hD2.le hnum0
    have := mul_le_mul_of_nonneg_left hmul ha
    linarith
  have hsub : ((t + f : ℕ) : ℝ) - f = t := by rw [hR]; ring
  have hB : (1 : ℝ) / (((t + f : ℕ) : ℝ) - f) ≤ 1 / ρ₀ := by
    rw [hsub]
    exact one_div_le_one_div_of_le hρ₀ ht1
  have hB' := mul_le_mul_of_nonneg_left
    (add_le_add_right hB (1 / ((n : ℝ) - f))) (by linarith : (0 : ℝ) ≤ 1 - a)
  linarith

/-- The same bound in the bracket form of Theorem `thm:sharp`. The number
    `s` stands for `sqrt(a(1-a)/m)`: it is `a ρ₀ / m` with
    `a ρ₀² = m (1-a)`, so `s² = a(1-a)/m`. With `ε₁ = (f+1)/ρ₀` and
    `ε₂ = f(ρ₀+f+1)/m < 1`, the load `s [1 + (1+ε₁)/(1-ε₂) + ρ₀/m]` is
    feasible. -/
theorem sharp_upper_bracket (f t : ℕ) (hf : 1 ≤ f) (hfn : f ≤ n) (ρ₀ s : ℝ) (hρ₀ : 0 < ρ₀)
    (ht1 : ρ₀ ≤ t) (ht2 : (t : ℝ) ≤ ρ₀ + 1)
    (hε : (f : ℝ) * (ρ₀ + f + 1) < (n : ℝ) - f) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hρ : a * ρ₀ ^ 2 = ((n : ℝ) - f) * (1 - a)) (hs : s = a * ρ₀ / ((n : ℝ) - f)) :
    s ^ 2 = a * (1 - a) / ((n : ℝ) - f) ∧
    Feasible (univ : Finset (ZMod n)) f a
      (s * (1 + (1 + ((f : ℝ) + 1) / ρ₀) / (1 - f * (ρ₀ + f + 1) / ((n : ℝ) - f)) +
        ρ₀ / ((n : ℝ) - f))) := by
  have hF0 : (0 : ℝ) ≤ f := Nat.cast_nonneg f
  have hM0 : (0 : ℝ) < (n : ℝ) - f := by
    have : (0 : ℝ) ≤ (f : ℝ) * (ρ₀ + f + 1) := by positivity
    linarith
  have hD : (n : ℝ) - f - f * (ρ₀ + f + 1) ≠ 0 := by
    have : 0 < (n : ℝ) - f - f * (ρ₀ + f + 1) := by linarith
    exact ne_of_gt this
  have hs2 : s ^ 2 = a * (1 - a) / ((n : ℝ) - f) := by
    rw [hs, div_pow, eq_div_iff hM0.ne']
    have e : (a * ρ₀) ^ 2 / ((n : ℝ) - f) ^ 2 * ((n : ℝ) - f) =
        a * (a * ρ₀ ^ 2) / ((n : ℝ) - f) := by
      field_simp
    rw [e, hρ]
    field_simp
  refine ⟨hs2, ?_⟩
  have h := sharp_upper (n := n) f t hf hfn ρ₀ hρ₀ ht1 ht2 hε a ha ha1
  have e1 : (1 + ((f : ℝ) + 1) / ρ₀) = (ρ₀ + f + 1) / ρ₀ := by
    field_simp
    ring
  have e2 : (1 - f * (ρ₀ + f + 1) / ((n : ℝ) - f)) =
      ((n : ℝ) - f - f * (ρ₀ + f + 1)) / ((n : ℝ) - f) := by
    field_simp
  have e3 : (1 - a) / ρ₀ = a * ρ₀ / ((n : ℝ) - f) := by
    rw [div_eq_div_iff hρ₀.ne' hM0.ne']
    linarith [hρ]
  have e4 : (1 - a) / ((n : ℝ) - f) = a * ρ₀ / ((n : ℝ) - f) * (ρ₀ / ((n : ℝ) - f)) := by
    rw [← e3]
    field_simp
  have etotal : s * (1 + (1 + ((f : ℝ) + 1) / ρ₀) / (1 - f * (ρ₀ + f + 1) / ((n : ℝ) - f)) +
        ρ₀ / ((n : ℝ) - f)) =
      a * (ρ₀ + f + 1) / ((n : ℝ) - f - f * (ρ₀ + f + 1)) +
        (1 - a) * (1 / ρ₀ + 1 / ((n : ℝ) - f)) := by
    have e5 : (1 - a) * (1 / ρ₀ + 1 / ((n : ℝ) - f)) =
        (1 - a) / ρ₀ + (1 - a) / ((n : ℝ) - f) := by ring
    rw [e5, e3, e4, e1, e2, hs]
    field_simp
    ring
  rw [etotal]
  exact h

#print axioms prop_tiles
#print axioms tiles_simple
#print axioms order_upper
#print axioms order_theorem
#print axioms sharp_upper
#print axioms sharp_upper_bracket
end
end QuorumAudit.Paper
