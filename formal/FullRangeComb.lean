import FullRangeExact

/-!
Theorem `thm:proactive`(2) with the construction printed in the
manuscript: write contacts are the rotations of the comb
`{⌊j n / q⌋ : 0 ≤ j < q}` and read contacts are all cyclic intervals of
`d ⌈n/q⌉` servers.
-/

set_option maxHeartbeats 1000000

namespace QuorumAudit.Paper
noncomputable section
open Finset Circle
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- The comb `{⌊j n / q⌋ : 0 ≤ j < q}` rotated by `r`. -/
def comb (n q : ℕ) [NeZero n] (r : ZMod n) : Finset (ZMod n) :=
  (range q).image (fun j : ℕ => r + ((j * n / q : ℕ) : ZMod n))

omit [NeZero n] in
/-- Consecutive comb points are at most `⌈n/q⌉` apart. -/
theorem comb_gap (q : ℕ) (hq : 1 ≤ q) (j : ℕ) : (j + 1) * n / q ≤ j * n / q + cdiv n q := by
  have hsplit : (j + 1) * n = j * n + n := by ring
  rw [hsplit, Nat.add_div (by omega : 0 < q)]
  unfold cdiv
  split_ifs with h
  · have hmod : 0 < n % q := by
      have := Nat.mod_lt (j * n) (by omega : 0 < q)
      omega
    have h1 : n / q + 1 ≤ (n + q - 1) / q := by
      rw [Nat.le_div_iff_mul_le (by omega : 0 < q)]
      have h2 := Nat.div_add_mod n q
      have h3 : (n / q + 1) * q = q * (n / q) + q := by ring
      omega
    omega
  · have h1 : n / q ≤ (n + q - 1) / q := Nat.div_le_div_right (by omega)
    omega

/-- Every offset `x < n` is followed within `⌈n/q⌉` by a comb value
    `⌊j n / q⌋` with `j ≤ q`. -/
theorem comb_next (q : ℕ) (hq : 1 ≤ q) (x : ℕ) (hx : x < n) :
    ∃ j : ℕ, j ≤ q ∧ x ≤ j * n / q ∧ j * n / q < x + cdiv n q := by
  have hn : 1 ≤ n := NeZero.pos n
  have hg : 1 ≤ cdiv n q := (cdiv_spec n q hn hq).1
  have hex : ∃ j : ℕ, x ≤ j * n / q := ⟨q, by
    rw [Nat.mul_div_cancel_left n (by omega : 0 < q)]
    exact hx.le⟩
  classical
  have hlast : x ≤ q * n / q := by
    rw [Nat.mul_div_cancel_left n (by omega : 0 < q)]
    exact hx.le
  refine ⟨Nat.find hex, Nat.find_min' hex hlast, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h0
  · rw [h0]
    simp only [Nat.zero_mul, Nat.zero_div]
    omega
  · obtain ⟨j', hj'⟩ : ∃ j', Nat.find hex = j' + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hmin : ¬ (x ≤ j' * n / q) := Nat.find_min hex (by omega)
    have hgap := comb_gap (n := n) q hq j'
    rw [hj']
    omega

/-- A rotated comb meets every interval of at least `⌈n/q⌉` servers. -/
theorem comb_hits (q g : ℕ) (hq : 1 ≤ q) (hg : cdiv n q ≤ g) (r s : ZMod n) :
    (arc g s ∩ comb n q r).Nonempty := by
  obtain ⟨j, hjq, hlo, hhi⟩ := comb_next (n := n) q hq (s - r).val (ZMod.val_lt _)
  have hs : s = r + (((s - r).val : ℕ) : ZMod n) := by simp
  obtain ⟨i, hi⟩ : ∃ i : ℕ, j * n / q = (s - r).val + i := ⟨j * n / q - (s - r).val, by omega⟩
  have hig : i < g := by omega
  rcases Nat.lt_or_ge j q with hlt | hge
  · refine ⟨r + ((j * n / q : ℕ) : ZMod n), mem_inter.mpr ⟨?_, ?_⟩⟩
    · refine mem_image.mpr ⟨i, mem_range.mpr hig, ?_⟩
      rw [hi]
      push_cast
      conv_lhs => rw [hs]
      ring
    · exact mem_image.mpr ⟨j, mem_range.mpr hlt, rfl⟩
  · have hjeq : j = q := le_antisymm hjq hge
    have hval : j * n / q = n := by
      rw [hjeq, Nat.mul_div_cancel_left n (by omega : 0 < q)]
    refine ⟨r, mem_inter.mpr ⟨?_, ?_⟩⟩
    · refine mem_image.mpr ⟨i, mem_range.mpr hig, ?_⟩
      have hni : (((s - r).val + i : ℕ) : ZMod n) = 0 := by
        rw [← hi, hval]
        exact ZMod.natCast_self n
      conv_lhs => rw [hs]
      rw [add_assoc, ← Nat.cast_add, hni, add_zero]
    · refine mem_image.mpr ⟨0, mem_range.mpr (by omega), ?_⟩
      simp

/-- Uniformly rotated combs contact each server with probability at most
    `q / n`. -/
theorem uniform_comb_route (q : ℕ) :
    ∃ route : Routing ((univ : Finset (ZMod n)).image (comb n q)) (univ : Finset (ZMod n)) ∅,
      ∀ i, incidence route.quorums route.p i ≤ (q : ℝ) / n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  let route := routing_from_indexed (univ : Finset (ZMod n)) (comb n q)
    (fun _ => 1 / (n : ℝ)) ((univ : Finset (ZMod n)).image (comb n q)) univ ∅
    (fun r _ => mem_image_of_mem _ (mem_univ _))
    (fun r _ z _ => by simp)
    (fun _ _ => by positivity)
    (by rw [sum_const, nsmul_eq_mul, card_univ, ZMod.card]; field_simp)
  refine ⟨route, ?_⟩
  intro i
  change incidence ((univ : Finset (ZMod n)).image (comb n q))
    (mergedProbability univ (comb n q) (fun _ => 1 / (n : ℝ))) i ≤ _
  rw [merged_incidence, ← sum_filter, sum_const, nsmul_eq_mul]
  have hsub : (univ : Finset (ZMod n)).filter (fun r => i ∈ comb n q r) ⊆
      (range q).image (fun j : ℕ => i - ((j * n / q : ℕ) : ZMod n)) := by
    intro r hr
    obtain ⟨j, hj, hji⟩ := mem_image.mp (mem_filter.mp hr).2
    exact mem_image.mpr ⟨j, hj, by rw [← hji]; ring⟩
  have hcard : (((univ : Finset (ZMod n)).filter (fun r => i ∈ comb n q r)).card : ℝ) ≤ q := by
    have := (card_le_card hsub).trans card_image_le
    rw [card_range] at this
    exact_mod_cast this
  calc
    (((univ : Finset (ZMod n)).filter (fun r => i ∈ comb n q r)).card : ℝ) * (1 / (n : ℝ)) ≤
        (q : ℝ) * (1 / (n : ℝ)) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (q : ℝ) / n := by ring

/-- Theorem `thm:proactive`(2) with the printed families. For
    `d = 2f+1 ≤ q ≤ n`, `g = ⌈n/q⌉` and `d g ≤ n`: read contacts taken
    among the cyclic intervals of `d g` servers and write contacts among
    the rotations of the comb intersect in at least `d` servers, and
    uniform rotations give load at most `(a d g + (1-a) q) / n`. -/
theorem proactive_comb_design (f q : ℕ) (hq : 2 * f + 1 ≤ q)
    (hdg : (2 * f + 1) * ⌈(n : ℝ) / (q : ℝ)⌉₊ ≤ n) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    ∃ 𝒜 ℬ : Finset (Finset (ZMod n)),
      𝒜 ⊆ reads n ((2 * f + 1) * ⌈(n : ℝ) / (q : ℝ)⌉₊) ∧
      ℬ ⊆ (univ : Finset (ZMod n)).image (comb n q) ∧
      (∀ A ∈ 𝒜, ∀ B ∈ ℬ, 2 * f + 1 ≤ (A ∩ B).card) ∧
      ProactiveRoutes 𝒜 ℬ univ a
        ((a * ((2 * (f : ℝ) + 1) * (⌈(n : ℝ) / (q : ℝ)⌉₊ : ℕ)) + (1 - a) * q) / n) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hq1 : 1 ≤ q := by omega
  have hg : cdiv n q = ⌈(n : ℝ) / (q : ℝ)⌉₊ := cdiv_eq_ceil n q (by omega)
  rw [← hg] at hdg ⊢
  obtain ⟨read, hread⟩ := uniform_interval_route (n := n) ((2 * f + 1) * cdiv n q)
  obtain ⟨write, hwrite⟩ := uniform_comb_route (n := n) q
  refine ⟨read.quorums, write.quorums, read.subset, write.subset, ?_,
    read.p, write.p, read.nonnegative, read.normalized, write.nonnegative, write.normalized, ?_⟩
  · intro A hA B hB
    obtain ⟨s, _, rfl⟩ := mem_image.mp (read.subset hA)
    obtain ⟨r, _, rfl⟩ := mem_image.mp (write.subset hB)
    exact long_interval_hits (2 * f + 1) (cdiv n q) hdg (comb n q r)
      (fun s' => comb_hits q (cdiv n q) hq1 le_rfl r s') s
  · intro i _
    have h1 := mul_le_mul_of_nonneg_left (hread i) ha
    have h2 := mul_le_mul_of_nonneg_left (hwrite i) (by linarith : (0 : ℝ) ≤ 1 - a)
    have e : (a * ((2 * (f : ℝ) + 1) * (cdiv n q : ℕ)) + (1 - a) * q) / n =
        a * ((((2 * f + 1) * cdiv n q : ℕ) : ℝ) / n) + (1 - a) * ((q : ℝ) / n) := by
      push_cast
      ring
    rw [e]
    linarith

/-- Theorem `thm:proactive`(2) as printed. -/
theorem proactive_upper_printed (f q : ℕ) (hq : 2 * f + 1 ≤ q)
    (hdg : (2 * f + 1) * ⌈(n : ℝ) / (q : ℝ)⌉₊ ≤ n) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    proactiveOptimum n f a ≤
      (a * ((2 * (f : ℝ) + 1) * (⌈(n : ℝ) / (q : ℝ)⌉₊ : ℕ)) + (1 - a) * q) / n := by
  obtain ⟨𝒜, ℬ, _, _, hmeet, hroutes⟩ := proactive_comb_design (n := n) f q hq hdg a ha ha1
  exact proactiveOptimum_le f a ha ha1
    ⟨𝒜, ℬ, fun _ _ => subset_univ _, fun _ _ => subset_univ _, hmeet, hroutes⟩

#print axioms comb_hits
#print axioms proactive_comb_design
#print axioms proactive_upper_printed
end
end QuorumAudit.Paper
