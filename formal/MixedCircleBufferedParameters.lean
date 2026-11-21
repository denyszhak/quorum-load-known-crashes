import MixedCircleBufferedBounds

set_option maxHeartbeats 2000000

namespace QuorumAudit.MixedCircle
noncomputable section

theorem buffered_integer_parameters (r e : ℕ) (hr : 5 ≤ r) (he : e ≤ 2) :
    ∃ h U V μ C : ℕ,
      0 < h ∧ 0 < U ∧ 0 < V ∧ U ≤ V ∧
      e * U + (r - 1 - e) * V = h ∧
      (U : ℝ) / h = low r ∧ (V : ℝ) / h = bufferedHigh r e ∧
      (μ : ℝ) = mixture r * h ∧ (C : ℝ) = cap r * h := by
  let D := (r - 2) * (r + 1)
  let K := (r - 1) ^ 2 + 2
  let p := r - 1
  let m := p - e
  let h := D * p * m
  let U := K * m
  let V := D * p - e * K
  let μ := (r - 5) * p * m
  let C := (2 * r - 1) * p * m
  have hr1 : r - 1 + 1 = r := by omega
  have hr2 : r - 2 + 2 = r := by omega
  have hr5 : r - 5 + 5 = r := by omega
  have hD : 0 < D := Nat.mul_pos (by omega) (by omega)
  have hK : 0 < K := by dsimp [K]; omega
  have hp : 4 ≤ p := by dsimp [p]; omega
  have hm : 0 < m := by dsimp [m]; omega
  have hKD : K ≤ D := by dsimp [K, D]; nlinarith only [hr1, hr2, hr5, Nat.zero_le (r - 5)]
  have heK : e * K ≤ e * D := Nat.mul_le_mul_left e hKD
  have hDP : e * D < D * p := by
    calc e * D = D * e := by ring
         _ < D * p := Nat.mul_lt_mul_of_pos_left (by omega) hD
  have hEK : e * K < D * p := lt_of_le_of_lt heK hDP
  have hV : 0 < V := Nat.sub_pos_of_lt hEK
  have hVsum : V + e * K = D * p := Nat.sub_add_cancel (le_of_lt hEK)
  have hmsum : m + e = p := by dsimp [m]; omega
  have hUsum : U + e * K = K * p := by
    dsimp [U]
    calc K * m + e * K = K * (m + e) := by ring
         _ = K * p := by rw [hmsum]
  have hUV : U ≤ V := by
    have hh := Nat.mul_le_mul_right p hKD
    omega
  have hnorm : e * U + m * V = h := by
    dsimp [U, h]
    calc e * (K * m) + m * V = (V + e * K) * m := by ring
         _ = D * p * m := by rw [hVsum]
  have hh : 0 < h := Nat.mul_pos (Nat.mul_pos hD (by omega)) hm
  have hU : 0 < U := Nat.mul_pos hK hm
  have hrR : (5 : ℝ) ≤ r := by exact_mod_cast hr
  have heR : (0 : ℝ) ≤ e ∧ (e : ℝ) ≤ 2 := ⟨Nat.cast_nonneg _, by exact_mod_cast he⟩
  have hDR : (D : ℝ) = den r := by
    dsimp [D]
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 2 ≤ r)]
    simp [den]
  have hKR : (K : ℝ) = ordinary r := by
    dsimp [K]
    rw [Nat.cast_add, Nat.cast_pow, Nat.cast_sub (by omega : 1 ≤ r)]
    norm_num only [Nat.cast_one, Nat.cast_ofNat]
    unfold ordinary
    ring
  have hpR : (p : ℝ) = (r : ℝ) - 1 := by
    dsimp [p]
    rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
  have hmR : (m : ℝ) = (r : ℝ) - 1 - e := by
    dsimp [m]
    rw [Nat.cast_sub (by omega : e ≤ p), hpR]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  have hD0 := ne_of_gt (den_pos (r : ℝ) hrR)
  have hp0 : (r : ℝ) - 1 ≠ 0 := by linarith
  have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hh)
  have hUr : (U : ℝ) / h = low r := by
    change ((K * m : ℕ) : ℝ) / ((D * p * m : ℕ) : ℝ) = _
    push_cast
    rw [hDR, hKR, hpR]
    unfold low mixture ordinary
    field_simp
    unfold den
    ring
  have hVr : (V : ℝ) / h = bufferedHigh r e := by
    have hnR : (e : ℝ) * (U : ℝ) + (m : ℝ) * (V : ℝ) = h := by exact_mod_cast hnorm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    unfold bufferedHigh
    rw [← hmR, ← hUr]
    field_simp
    nlinarith only [hnR]
  refine ⟨h, U, V, μ, C, hh, hU, hV, hUV, ?_, hUr, hVr, ?_, ?_⟩
  · simpa only [m, p] using hnorm
  · change (((r - 5) * p * m : ℕ) : ℝ) = mixture r * ((D * p * m : ℕ) : ℝ)
    push_cast [Nat.cast_sub (by omega : 5 ≤ r)]
    rw [hDR]
    unfold mixture
    field_simp
  · change (((2 * r - 1) * p * m : ℕ) : ℝ) = cap r * ((D * p * m : ℕ) : ℝ)
    push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * r)]
    rw [hDR]
    unfold cap
    field_simp

#print axioms buffered_integer_parameters
end
end QuorumAudit.MixedCircle
