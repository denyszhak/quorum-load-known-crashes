import FullRangeTiles

/-!
Contact sets chosen before the failures: the construction and the exact
points of Theorem `thm:proactive`, parts (2) and (3).
-/

set_option maxHeartbeats 1000000

namespace QuorumAudit.Paper
noncomputable section
open Finset Circle
open scoped BigOperators
variable {n : ℕ} [NeZero n]

omit [NeZero n] in
theorem proactive_mono {ι : Type*} [DecidableEq ι] {V : Finset ι} {f : ℕ} {a L L' : ℝ}
    (hL : L ≤ L') (h : ProactiveFeasible V f a L) : ProactiveFeasible V f a L' := by
  obtain ⟨𝒜, ℬ, h𝒜, hℬ, hmeet, p, q, hp, hpn, hq, hqn, hload⟩ := h
  exact ⟨𝒜, ℬ, h𝒜, hℬ, hmeet, p, q, hp, hpn, hq, hqn, fun i hi => (hload i hi).trans hL⟩

omit [NeZero n] in
/-- A set that meets every interval of `g` servers meets every interval of
    `d * g` servers at least `d` times. -/
theorem long_interval_hits (d g : ℕ) (hdg : d * g ≤ n) (B : Finset (ZMod n))
    (hB : ∀ s : ZMod n, (arc g s ∩ B).Nonempty) (s : ZMod n) :
    d ≤ (arc (d * g) s ∩ B).card := by
  have hex : ∀ k : ℕ, ∃ j : ℕ, j < g ∧ s + ((k * g + j : ℕ) : ZMod n) ∈ B := by
    intro k
    obtain ⟨z, hz⟩ := hB (s + ((k * g : ℕ) : ZMod n))
    obtain ⟨hzarc, hzB⟩ := mem_inter.mp hz
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hzarc
    refine ⟨j, mem_range.mp hj, ?_⟩
    have e : s + ((k * g + j : ℕ) : ZMod n) = s + ((k * g : ℕ) : ZMod n) + (j : ZMod n) := by
      push_cast; ring
    rw [e]
    exact hzB
  choose j hj hjB using hex
  have hoff : ∀ k < d, k * g + j k < d * g := by
    intro k hk
    have h1 := Nat.mul_le_mul_right g (Nat.succ_le_of_lt hk)
    rw [Nat.succ_mul] at h1
    have := hj k
    omega
  have hcard : (range d).card ≤ (arc (d * g) s ∩ B).card := by
    apply Finset.card_le_card_of_injOn (fun k => s + ((k * g + j k : ℕ) : ZMod n))
    · intro k hk
      have hk' := mem_range.mp hk
      exact mem_inter.mpr ⟨mem_image.mpr ⟨k * g + j k, mem_range.mpr (hoff k hk'), rfl⟩, hjB k⟩
    · intro k hk k' hk' heq
      have hk1 := mem_range.mp hk
      have hk2 := mem_range.mp hk'
      have hnat : k * g + j k = k' * g + j k' :=
        cast_injective_below (lt_of_lt_of_le (hoff k hk1) hdg)
          (lt_of_lt_of_le (hoff k' hk2) hdg) (add_left_cancel heq)
      have hjk := hj k
      have hjk' := hj k'
      rcases Nat.lt_trichotomy k k' with h | h | h
      · have h1 := Nat.mul_le_mul_right g (Nat.succ_le_of_lt h)
        rw [Nat.succ_mul] at h1
        omega
      · exact h
      · have h1 := Nat.mul_le_mul_right g (Nat.succ_le_of_lt h)
        rw [Nat.succ_mul] at h1
        omega
  rwa [card_range] at hcard

/-- Uniformly rotated intervals of `ρ` servers contact each server with
    probability at most `ρ / n`. -/
theorem uniform_interval_route (ρ : ℕ) :
    ∃ route : Routing (reads n ρ) (univ : Finset (ZMod n)) ∅,
      ∀ i, incidence route.quorums route.p i ≤ (ρ : ℝ) / n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  let route := routing_from_indexed (univ : Finset (ZMod n)) (fun s => arc ρ s)
    (fun _ => 1 / (n : ℝ)) (reads n ρ) univ ∅
    (fun s _ => mem_image_of_mem _ (mem_univ _))
    (fun s _ z _ => by simp)
    (fun _ _ => by positivity)
    (by rw [sum_const, nsmul_eq_mul, card_univ, ZMod.card]; field_simp)
  refine ⟨route, ?_⟩
  intro i
  change incidence ((univ : Finset (ZMod n)).image (fun s => arc ρ s))
    (mergedProbability univ (fun s => arc ρ s) (fun _ => 1 / (n : ℝ))) i ≤ _
  rw [merged_incidence, ← sum_filter, sum_const, nsmul_eq_mul]
  have hsub : (univ : Finset (ZMod n)).filter (fun s => i ∈ arc ρ s) ⊆
      (range ρ).image (fun j : ℕ => i - (j : ZMod n)) := by
    intro s hs
    obtain ⟨j, hj, hji⟩ := mem_image.mp (mem_filter.mp hs).2
    exact mem_image.mpr ⟨j, hj, by rw [← hji]; ring⟩
  have hcard : (((univ : Finset (ZMod n)).filter (fun s => i ∈ arc ρ s)).card : ℝ) ≤ ρ := by
    have := (card_le_card hsub).trans card_image_le
    rw [card_range] at this
    exact_mod_cast this
  calc
    (((univ : Finset (ZMod n)).filter (fun s => i ∈ arc ρ s)).card : ℝ) * (1 / (n : ℝ)) ≤
        (ρ : ℝ) * (1 / (n : ℝ)) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (ρ : ℝ) / n := by ring

/-- Theorem `thm:proactive`(2). With `d = 2f+1`, a write size `q` and a gap
    bound `g` such that `n ≤ g q` and `d g ≤ n`, the load
    `(a d g + (1-a) q) / n` is attainable. The manuscript takes
    `g = ⌈n/q⌉`; the two conditions imply its hypothesis `d ≤ q`. Write contacts come from the sampling lemma with equal
    weights; read contacts are all intervals of `d g` servers. -/
theorem proactive_upper (f q g : ℕ) (hqn : q ≤ n) (hg : n ≤ g * q)
    (hdg : (2 * f + 1) * g ≤ n) (a : ℝ) (ha : 0 ≤ a) :
    ProactiveFeasible (univ : Finset (ZMod n)) f a
      ((a * ((2 * (f : ℝ) + 1) * g) + (1 - a) * q) / n) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hgn : g ≤ n := (Nat.le_mul_of_pos_left g (by omega : 0 < 2 * f + 1)).trans hdg
  obtain ⟨read, hread⟩ := uniform_interval_route (n := n) ((2 * f + 1) * g)
  obtain ⟨write, hwrite⟩ := exact_ranked_sampled_routing (h := n) (fun _ : ZMod n => q) ∅ g q hgn
    (by rw [sum_const, smul_eq_mul, card_univ, ZMod.card, mul_comm])
    (fun _ => hqn) (by simp)
    (fun s => by rw [sum_const, smul_eq_mul, arc_card g hgn s]; exact hg)
  refine ⟨read.quorums, write.quorums, fun _ _ => subset_univ _, fun _ _ => subset_univ _, ?_,
    read.p, write.p, read.nonnegative, read.normalized, write.nonnegative, write.normalized, ?_⟩
  · intro A hA B hB
    obtain ⟨s, _, rfl⟩ := mem_image.mp (read.subset hA)
    have hBw : B ∈ writes n g := (mem_filter.mp (write.subset hB)).1
    exact long_interval_hits (2 * f + 1) g hdg B (mem_filter.mp hBw).2 s
  · intro i _
    have h1 := mul_le_mul_of_nonneg_left (hread i) ha
    have h2 : (1 - a) * incidence write.quorums write.p i = (1 - a) * ((q : ℝ) / n) := by
      rw [hwrite i]
    rw [h2]
    have e : (a * ((2 * (f : ℝ) + 1) * g) + (1 - a) * q) / n =
        a * ((((2 * f + 1) * g : ℕ) : ℝ) / n) + (1 - a) * ((q : ℝ) / n) := by
      push_cast
      ring
    rw [e]
    linarith

/-- Theorem `thm:proactive`(3): when `q` divides `n` and `q ≥ d = 2f+1`,
    the optimum at `a = q² / (q² + d n)` is exactly `2 d q / (q² + d n)`. -/
theorem proactive_exact (f q : ℕ) (hq : 2 * f + 1 ≤ q) (hdiv : q ∣ n) (L : ℝ) :
    ProactiveFeasible (univ : Finset (ZMod n)) f
        ((q : ℝ) ^ 2 / ((q : ℝ) ^ 2 + (2 * (f : ℝ) + 1) * n)) L ↔
      2 * (2 * (f : ℝ) + 1) * q / ((q : ℝ) ^ 2 + (2 * (f : ℝ) + 1) * n) ≤ L := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hd : (0 : ℝ) < 2 * (f : ℝ) + 1 := by positivity
  have hD : (0 : ℝ) < (q : ℝ) ^ 2 + (2 * (f : ℝ) + 1) * n := by positivity
  set d : ℝ := 2 * (f : ℝ) + 1 with hd_def
  set D : ℝ := (q : ℝ) ^ 2 + d * n with hD_def
  have ha0 : 0 ≤ (q : ℝ) ^ 2 / D := by positivity
  have ha1 : (q : ℝ) ^ 2 / D ≤ 1 := by
    rw [div_le_one hD]
    have : 0 ≤ d * n := by positivity
    linarith
  have hone : 1 - (q : ℝ) ^ 2 / D = d * n / D := by
    field_simp
    ring
  constructor
  · intro h
    obtain ⟨hL, _, h2⟩ := proactive_lower (univ : Finset (ZMod n)) f
      (by rw [card_univ, ZMod.card]; exact NeZero.pos n) _ L ha0 ha1 h
    rw [card_univ, ZMod.card, hone] at h2
    have hsq : (2 * d * q / D) ^ 2 ≤ L ^ 2 := by
      have e : 4 * d * ((q : ℝ) ^ 2 / D * (d * n / D)) / n = (2 * d * q / D) ^ 2 := by
        field_simp
        ring
      rw [← e]
      exact h2
    exact (pow_le_pow_iff_left₀ (by positivity) hL.le (by norm_num)).mp hsq
  · intro hL
    obtain ⟨g, hg⟩ := hdiv
    have hgpos : 0 < g := by
      rcases Nat.eq_zero_or_pos g with h0 | h0
      · rw [h0, mul_zero] at hg
        exact absurd hg (NeZero.ne n)
      · exact h0
    have hqn : q ≤ n := by rw [hg]; exact Nat.le_mul_of_pos_right q hgpos
    have hdg : (2 * f + 1) * g ≤ n := by rw [hg]; exact Nat.mul_le_mul_right g hq
    have hup := proactive_upper (n := n) f q g hqn (by rw [hg, mul_comm]) hdg
      ((q : ℝ) ^ 2 / D) ha0
    apply proactive_mono _ hup
    have hncast : (n : ℝ) = q * g := by rw [hg]; push_cast; ring
    have hgq : (g : ℝ) = n / q := by rw [hncast]; field_simp
    rw [hone, hgq]
    apply le_of_eq_of_le _ hL
    field_simp
    ring

#print axioms long_interval_hits
#print axioms proactive_upper
#print axioms proactive_exact
end
end QuorumAudit.Paper
