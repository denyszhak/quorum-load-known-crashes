import CircleExactCardinality
import FullRangeBounds
import Mathlib.Data.Nat.Count

/-!
The tiled-interval construction of the section "Every read fraction"
(Proposition `prop:tiles`).
-/

set_option maxHeartbeats 1000000

namespace QuorumAudit.Tiles
open Finset

/-! ### Counting complete tiles on a line -/

section Streak
variable (dead : ℕ → Prop) [DecidablePred dead]

/-- Number of consecutive live positions ending at `j`. -/
def streak : ℕ → ℕ
  | 0 => 0
  | j + 1 => if dead (j + 1) then 0 else streak j + 1

theorem streak_zero : streak dead 0 = 0 := rfl

theorem streak_succ (j : ℕ) :
    streak dead (j + 1) = if dead (j + 1) then 0 else streak dead j + 1 := rfl

theorem streak_le (j : ℕ) : streak dead j ≤ j := by
  induction j with
  | zero => simp [streak_zero]
  | succ j ih =>
    rw [streak_succ]
    split_ifs <;> omega

theorem streak_pos_live {j : ℕ} (h : 0 < streak dead j) : ¬ dead j := by
  cases j with
  | zero => simp [streak_zero] at h
  | succ j =>
    intro hd
    rw [streak_succ, ite_eq_left hd] at h
    omega

theorem streak_back : ∀ k j : ℕ, k < streak dead j →
    k ≤ j ∧ streak dead (j - k) = streak dead j - k := by
  intro k
  induction k with
  | zero => intro j _; simp
  | succ k ih =>
    intro j hk
    cases j with
    | zero => simp [streak_zero] at hk
    | succ j =>
      have hd : ¬ dead (j + 1) := streak_pos_live dead (by omega)
      have hs : streak dead (j + 1) = streak dead j + 1 := by rw [streak_succ, ite_eq_right hd]
      obtain ⟨h1, h2⟩ := ih j (by omega)
      refine ⟨by omega, ?_⟩
      rw [show j + 1 - (k + 1) = j - k by omega, h2, hs]
      omega

/-- Position `j` ends a complete tile of length `ρ`. -/
def IsEnd (ρ j : ℕ) : Prop := 0 < streak dead j ∧ streak dead j % ρ = 0

instance (ρ : ℕ) : DecidablePred (IsEnd dead ρ) := fun _ => by unfold IsEnd; infer_instance

theorem mod_succ_cases (s ρ : ℕ) (hρ : 1 ≤ ρ) :
    ((s + 1) % ρ = 0 ∧ s % ρ = ρ - 1) ∨ ((s + 1) % ρ = s % ρ + 1 ∧ s % ρ + 1 < ρ) := by
  have hlt : s % ρ < ρ := Nat.mod_lt _ (by omega)
  have key : (s + 1) % ρ = (s % ρ + 1) % ρ := by
    conv_lhs => rw [← Nat.div_add_mod s ρ]
    rw [Nat.add_assoc, Nat.mul_add_mod]
  by_cases h : s % ρ + 1 < ρ
  · right
    exact ⟨by rw [key, Nat.mod_eq_of_lt h], h⟩
  · left
    have he : s % ρ + 1 = ρ := by omega
    exact ⟨by rw [key, he, Nat.mod_self], by omega⟩

/-- Among the first `k+1` positions, live positions are paid for by `ρ`
    per complete tile and `ρ-1` per dead position. -/
theorem tile_invariant (ρ : ℕ) (hρ : 1 ≤ ρ) (h0 : dead 0) (k : ℕ) :
    Nat.count (fun j => ¬ dead j) (k + 1) + (ρ - 1 - streak dead k % ρ) ≤
      ρ * Nat.count (IsEnd dead ρ) (k + 1) + (ρ - 1) * Nat.count dead (k + 1) := by
  induction k with
  | zero =>
    have e : ¬ IsEnd dead ρ 0 := by simp [IsEnd, streak_zero]
    simp [Nat.count_succ, h0, e, streak_zero]
  | succ k ih =>
    rw [Nat.count_succ (fun j => ¬ dead j) (k + 1), Nat.count_succ (IsEnd dead ρ) (k + 1),
      Nat.count_succ dead (k + 1)]
    generalize Nat.count (fun j => ¬ dead j) (k + 1) = lv at ih ⊢
    generalize Nat.count (IsEnd dead ρ) (k + 1) = e at ih ⊢
    generalize Nat.count dead (k + 1) = d at ih ⊢
    by_cases hd : dead (k + 1)
    · have hs : streak dead (k + 1) = 0 := by rw [streak_succ, ite_eq_left hd]
      have he : ¬ IsEnd dead ρ (k + 1) := by simp [IsEnd, hs]
      have h1 : (if (fun j => ¬ dead j) (k + 1) then 1 else 0) = 0 := ite_eq_right (not_not.mpr hd)
      rw [h1, ite_eq_right he, ite_eq_left hd, hs, Nat.zero_mod, Nat.mul_add, Nat.mul_add]
      omega
    · have hs : streak dead (k + 1) = streak dead k + 1 := by rw [streak_succ, ite_eq_right hd]
      have h1 : (if (fun j => ¬ dead j) (k + 1) then 1 else 0) = 1 := ite_eq_left hd
      rw [h1, ite_eq_right hd, hs]
      rcases mod_succ_cases (streak dead k) ρ hρ with ⟨hm, hprev⟩ | ⟨hm, hlt⟩
      · have he : IsEnd dead ρ (k + 1) := ⟨by rw [hs]; omega, by rw [hs]; exact hm⟩
        rw [ite_eq_left he, hm, Nat.mul_add]
        rw [hprev] at ih
        simp only [Nat.add_zero, Nat.mul_one, Nat.sub_zero] at ih ⊢
        omega
      · have he : ¬ IsEnd dead ρ (k + 1) := by
          rintro ⟨_, h⟩
          rw [hs, hm] at h
          omega
        rw [ite_eq_right he, hm]
        simp only [Nat.add_zero] at ih ⊢
        omega

end Streak
end QuorumAudit.Tiles

namespace QuorumAudit.Circle
noncomputable section
open Finset QuorumAudit.Tiles
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- Offset `j` from the server `x0` is failed. -/
def deadAt (F : Finset (ZMod n)) (x0 : ZMod n) (j : ℕ) : Prop := x0 + (j : ZMod n) ∈ F

instance (F : Finset (ZMod n)) (x0 : ZMod n) : DecidablePred (deadAt F x0) :=
  fun _ => by unfold deadAt; infer_instance

/-- First server of the tile that ends at offset `e`. -/
def tileStart (x0 : ZMod n) (ρ e : ℕ) : ZMod n := x0 + ((e + 1 - ρ : ℕ) : ZMod n)

omit [NeZero n] in
theorem mem_tile {x0 z : ZMod n} {ρ e : ℕ} :
    z ∈ arc ρ (tileStart x0 ρ e) ↔ ∃ t < ρ, z = x0 + ((e + 1 - ρ + t : ℕ) : ZMod n) := by
  unfold arc tileStart
  simp only [mem_image, mem_range]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, by push_cast; ring⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, by push_cast; ring⟩

omit [NeZero n] in
theorem end_facts {F : Finset (ZMod n)} {x0 : ZMod n} {ρ e : ℕ}
    (he : IsEnd (deadAt F x0) ρ e) (t : ℕ) (ht : t < ρ) :
    e + 1 - ρ + t ≤ e ∧ ρ ≤ e ∧ 0 < streak (deadAt F x0) (e + 1 - ρ + t) ∧
      streak (deadAt F x0) (e + 1 - ρ + t) + (ρ - 1 - t) = streak (deadAt F x0) e := by
  obtain ⟨hpos, hmod⟩ := he
  have hle : ρ ≤ streak (deadAt F x0) e := Nat.le_of_dvd hpos (Nat.dvd_of_mod_eq_zero hmod)
  have hse := streak_le (deadAt F x0) e
  obtain ⟨h1, h2⟩ := streak_back (deadAt F x0) (ρ - 1 - t) e (by omega)
  have hidx : e - (ρ - 1 - t) = e + 1 - ρ + t := by omega
  rw [hidx] at h2
  exact ⟨by omega, by omega, by omega, by omega⟩

omit [NeZero n] in
theorem tile_live {F : Finset (ZMod n)} {x0 : ZMod n} {ρ e : ℕ}
    (he : IsEnd (deadAt F x0) ρ e) : Disjoint (arc ρ (tileStart x0 ρ e)) F := by
  apply disjoint_left.mpr
  intro z hz hzF
  obtain ⟨t, ht, rfl⟩ := mem_tile.mp hz
  obtain ⟨_, _, hpos, _⟩ := end_facts he t ht
  exact streak_pos_live _ hpos hzF

omit [NeZero n] in
theorem tile_disjoint {F : Finset (ZMod n)} {x0 z : ZMod n} {ρ e e' : ℕ}
    (he : IsEnd (deadAt F x0) ρ e) (he' : IsEnd (deadAt F x0) ρ e') (hen : e < n) (hen' : e' < n)
    (hz : z ∈ arc ρ (tileStart x0 ρ e)) (hz' : z ∈ arc ρ (tileStart x0 ρ e')) : e = e' := by
  obtain ⟨t, ht, rfl⟩ := mem_tile.mp hz
  obtain ⟨t', ht', heq⟩ := mem_tile.mp hz'
  obtain ⟨h1, h2, _, h3⟩ := end_facts he t ht
  obtain ⟨h1', h2', _, h3'⟩ := end_facts he' t' ht'
  have hj : e + 1 - ρ + t = e' + 1 - ρ + t' :=
    cast_injective_below (by omega) (by omega) (add_left_cancel heq)
  rw [hj] at h3
  obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero he.2
  obtain ⟨c', hc'⟩ := Nat.dvd_of_mod_eq_zero he'.2
  have hcc : c = c' := by
    rcases Nat.lt_trichotomy c c' with h | h | h
    · have := Nat.mul_le_mul_left ρ (Nat.succ_le_of_lt h)
      rw [Nat.mul_succ] at this
      omega
    · exact h
    · have := Nat.mul_le_mul_left ρ (Nat.succ_le_of_lt h)
      rw [Nat.mul_succ] at this
      omega
  rw [hcc] at hc
  omega

/-- After a nonempty failed set, there are pairwise disjoint live intervals
    of length `ρ`, and `ρ` per interval plus `ρ-1` per failure covers all
    survivors. -/
theorem tiles_exist (F : Finset (ZMod n)) (ρ : ℕ) (hρ : 1 ≤ ρ) (hF : F.Nonempty) :
    ∃ (I : Finset ℕ) (S : ℕ → ZMod n),
      (∀ e ∈ I, Disjoint (arc ρ (S e)) F) ∧
      (∀ e ∈ I, ∀ e' ∈ I, ∀ z, z ∈ arc ρ (S e) → z ∈ arc ρ (S e') → e = e') ∧
      n - F.card ≤ ρ * I.card + (ρ - 1) * F.card := by
  obtain ⟨x0, hx0⟩ := hF
  have hn : 1 ≤ n := NeZero.pos n
  refine ⟨(range n).filter (IsEnd (deadAt F x0) ρ), tileStart x0 ρ, ?_, ?_, ?_⟩
  · intro e he
    exact tile_live (mem_filter.mp he).2
  · intro e he e' he' z hz hz'
    exact tile_disjoint (mem_filter.mp he).2 (mem_filter.mp he').2
      (mem_range.mp (mem_filter.mp he).1) (mem_range.mp (mem_filter.mp he').1) hz hz'
  · have h0 : deadAt F x0 0 := by simpa [deadAt] using hx0
    have hinv := tile_invariant (deadAt F x0) ρ hρ h0 (n - 1)
    rw [show n - 1 + 1 = n by omega] at hinv
    rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range,
      Nat.count_eq_card_filter_range] at hinv
    have hdead : ((range n).filter (deadAt F x0)).card = F.card := by
      apply Finset.card_bij (fun (j : ℕ) _ => x0 + (j : ZMod n))
      · intro j hj
        exact (mem_filter.mp hj).2
      · intro a ha b hb hab
        exact cast_injective_below (mem_range.mp (mem_filter.mp ha).1)
          (mem_range.mp (mem_filter.mp hb).1) (add_left_cancel hab)
      · intro z hz
        refine ⟨(z - x0).val, mem_filter.mpr ⟨mem_range.mpr (ZMod.val_lt _), ?_⟩, ?_⟩
        · simpa [deadAt] using hz
        · simp
    have hsplit := Finset.card_filter_add_card_filter_not (s := range n) (deadAt F x0)
    rw [card_range, hdead] at hsplit
    rw [hdead] at hinv
    have hE : ((range n).filter (IsEnd (deadAt F x0) ρ)).card =
        (Finset.card {x ∈ range n | IsEnd (deadAt F x0) ρ x}) := rfl
    rw [hE]
    omega

#print axioms tiles_exist
end
end QuorumAudit.Circle

namespace QuorumAudit.Paper
noncomputable section
open Finset Circle
open scoped BigOperators
variable {n : ℕ} [NeZero n]

omit [NeZero n] in
theorem feasible_mono {ι : Type*} [DecidableEq ι] {V : Finset ι} {f : ℕ} {a L L' : ℝ}
    (hL : L ≤ L') (h : Feasible V f a L) : Feasible V f a L' := by
  obtain ⟨R, W, had, hroutes⟩ := h
  refine ⟨R, W, had, fun F hF hc => ?_⟩
  obtain ⟨p, q, hp, hq, hload⟩ := hroutes F hF hc
  exact ⟨p, q, hp, hq, fun i hi => (hload i hi).trans hL⟩

/-- Uniform choice among the disjoint live intervals. -/
theorem tile_read_route (F : Finset (ZMod n)) (ρ N : ℕ) (hρ : 1 ≤ ρ) (hF : F.Nonempty)
    (hN : 1 ≤ N) (hcount : ρ * (N - 1) + (ρ - 1) * F.card < n - F.card) :
    ∃ route : Routing (reads n ρ) univ F,
      ∀ i, incidence route.quorums route.p i ≤ 1 / (N : ℝ) := by
  obtain ⟨I, S, hlive, hdis, hcard⟩ := tiles_exist F ρ hρ hF
  have hT : N ≤ I.card := by
    by_contra hlt
    have h1 : I.card ≤ N - 1 := by omega
    have h2 := Nat.mul_le_mul_left ρ h1
    omega
  have hTpos : (0 : ℝ) < I.card := by exact_mod_cast (by omega : 0 < I.card)
  let route := routing_from_indexed I (fun e => arc ρ (S e)) (fun _ => 1 / (I.card : ℝ))
    (reads n ρ) univ F
    (fun e _ => mem_image_of_mem _ (mem_univ _))
    (fun e he z hz => mem_sdiff.mpr
      ⟨mem_univ _, fun hzF => disjoint_left.mp (hlive e he) hz hzF⟩)
    (fun _ _ => by positivity)
    (by rw [sum_const, nsmul_eq_mul]; field_simp)
  refine ⟨route, ?_⟩
  intro i
  change incidence (I.image (fun e => arc ρ (S e)))
    (mergedProbability I (fun e => arc ρ (S e)) (fun _ => 1 / (I.card : ℝ))) i ≤ _
  rw [merged_incidence, ← sum_filter, sum_const, nsmul_eq_mul]
  have hone : (I.filter (fun e => i ∈ arc ρ (S e))).card ≤ 1 := by
    apply card_le_one.mpr
    intro e he e' he'
    exact hdis e (mem_filter.mp he).1 e' (mem_filter.mp he').1 i
      (mem_filter.mp he).2 (mem_filter.mp he').2
  have hone' : ((I.filter (fun e => i ∈ arc ρ (S e))).card : ℝ) ≤ 1 := by exact_mod_cast hone
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNT : (N : ℝ) ≤ I.card := by exact_mod_cast hT
  calc
    ((I.filter (fun e => i ∈ arc ρ (S e))).card : ℝ) * (1 / (I.card : ℝ)) ≤
        1 * (1 / (I.card : ℝ)) :=
      mul_le_mul_of_nonneg_right hone' (by positivity)
    _ = 1 / (I.card : ℝ) := one_mul _
    _ ≤ 1 / (N : ℝ) := one_div_le_one_div_of_le hNpos hNT

/-- Sampled writes with equal weight on every survivor. -/
theorem tile_write_route (F : Finset (ZMod n)) (ρ q : ℕ) (hρn : ρ ≤ n) (hFn : F.card < n)
    (hq : n - F.card ≤ q * (ρ - F.card)) (hqm : q ≤ n - F.card) :
    ∃ route : Routing (rankedWrites n ρ q) univ F,
      ∀ i, incidence route.quorums route.p i ≤ (q : ℝ) / ((n : ℝ) - F.card) := by
  haveI : NeZero (n - F.card) := ⟨by omega⟩
  let w : ZMod n → ℕ := fun i => if i ∈ F then 0 else q
  have hwF : ∀ i ∈ F, w i = 0 := fun i hi => by simp [w, hi]
  have hwL : ∀ i, i ∉ F → w i = q := fun i hi => by simp [w, hi]
  have htotal : ∑ i : ZMod n, w i = q * (n - F.card) := by
    rw [← Finset.sum_sdiff (subset_univ F), Finset.sum_eq_zero hwF, add_zero,
      Finset.sum_congr rfl (fun i hi => hwL i (mem_sdiff.mp hi).2), sum_const, smul_eq_mul,
      card_sdiff_of_subset (subset_univ _), card_univ, ZMod.card, mul_comm]
  have hw : ∀ i, w i ≤ n - F.card := by
    intro i
    by_cases hi : i ∈ F
    · rw [hwF i hi]; omega
    · rw [hwL i hi]; exact hqm
  have hwindow : ∀ s : ZMod n, n - F.card ≤ ∑ i ∈ arc ρ s, w i := by
    intro s
    have h1 : ∑ i ∈ arc ρ s \ F, w i ≤ ∑ i ∈ arc ρ s, w i :=
      Finset.sum_le_sum_of_subset sdiff_subset
    have h2 : ∑ i ∈ arc ρ s \ F, w i = (arc ρ s \ F).card * q := by
      rw [Finset.sum_congr rfl (fun i hi => hwL i (mem_sdiff.mp hi).2), sum_const, smul_eq_mul]
    have h3 : ρ - F.card ≤ (arc ρ s \ F).card := by
      have := Finset.le_card_sdiff F (arc ρ s)
      rw [arc_card ρ hρn s] at this
      exact this
    have h4 := Nat.mul_le_mul_right q h3
    rw [mul_comm] at hq
    omega
  obtain ⟨route, hm⟩ := exact_ranked_sampled_routing (h := n - F.card) w F ρ q hρn
    htotal hw hwF hwindow
  refine ⟨route, ?_⟩
  intro i
  rw [hm i, Nat.cast_sub hFn.le]
  have hpos : (0 : ℝ) < (n : ℝ) - F.card := by
    have : (F.card : ℝ) < n := by exact_mod_cast hFn
    linarith
  apply div_le_div_of_nonneg_right _ hpos.le
  by_cases hi : i ∈ F
  · rw [hwF i hi]; simp
  · rw [hwL i hi]

/-- Proposition `prop:tiles`, routes: after at most `f` failures, uniform
    disjoint live intervals and sampled writes have load at most
    `a/N + (1-a) q/m` at every server. -/
theorem tiles_routes (f ρ N q : ℕ) (hf : 1 ≤ f) (hρ : f + 1 ≤ ρ) (hN : 1 ≤ N)
    (hNt : ρ * (N - 1) + f * (ρ - 1) < n - f) (hq : n - f ≤ q * (ρ - f)) (hqm : q ≤ n - f)
    (F : Finset (ZMod n)) (hF : F.card ≤ f) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    ∃ read : Routing (reads n ρ) univ F, ∃ write : Routing (rankedWrites n ρ q) univ F,
      ∀ i, combined read write a i ≤ a / N + (1 - a) * (q / ((n : ℝ) - f)) := by
  have hfn : f < n := by omega
  have hρ1 : ρ - 1 ≤ f * (ρ - 1) := Nat.le_mul_of_pos_left _ hf
  have hρn : ρ ≤ n := by omega
  obtain ⟨G, hFG, _, hG⟩ := Finset.exists_subsuperset_card_eq (subset_univ F) hF
    (by rw [card_univ, ZMod.card]; exact hfn.le)
  have hGne : G.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨read, hread⟩ := tile_read_route G ρ N (by omega) hGne hN
    (by rw [hG, mul_comm (ρ - 1) f]; exact hNt)
  obtain ⟨write, hwrite⟩ := tile_write_route G ρ q hρn (by omega)
    (by rw [hG]; exact hq) (by rw [hG]; exact hqm)
  refine ⟨unpad_routing read hFG, unpad_routing write hFG, ?_⟩
  intro i
  change a * incidence read.quorums read.p i + (1 - a) * incidence write.quorums write.p i ≤ _
  have h1 := mul_le_mul_of_nonneg_left (hread i) ha
  have h2 := mul_le_mul_of_nonneg_left (hwrite i) (by linarith : (0 : ℝ) ≤ 1 - a)
  rw [hG] at h2
  have e : a * (1 / (N : ℝ)) = a / N := by ring
  rw [e] at h1
  linarith

/-- Proposition `prop:tiles` for general admissible parameters `N`, `q`. -/
theorem tiles_feasible (f ρ N q : ℕ) (hf : 1 ≤ f) (hρ : f + 1 ≤ ρ) (hN : 1 ≤ N)
    (hNt : ρ * (N - 1) + f * (ρ - 1) < n - f) (hq : n - f ≤ q * (ρ - f)) (hqm : q ≤ n - f)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    Admissible (reads n ρ) (rankedWrites n ρ q) univ f ∧
      ∀ F ⊆ (univ : Finset (ZMod n)), F.card ≤ f →
        RoutesAt (reads n ρ) (rankedWrites n ρ q) univ F a
          (a / N + (1 - a) * (q / ((n : ℝ) - f))) := by
  have hroutes : ∀ F ⊆ (univ : Finset (ZMod n)), F.card ≤ f →
      ∃ read : Routing (reads n ρ) univ F, ∃ write : Routing (rankedWrites n ρ q) univ F,
        ∀ i ∈ univ \ F, combined read write a i ≤ a / N + (1 - a) * (q / ((n : ℝ) - f)) := by
    intro F _ hc
    obtain ⟨read, write, h⟩ := tiles_routes f ρ N q hf hρ hN hNt hq hqm F hc a ha ha1
    exact ⟨read, write, fun i _ => h i⟩
  exact ⟨admissible_of_routes _ _ _ f a _ (fun _ _ => subset_univ _) (fun _ _ => subset_univ _)
    (ranked_safe ρ q) hroutes,
    fun F hF hc => (routes_iff _ _ _ _ _ _).mpr (hroutes F hF hc)⟩

#print axioms tiles_routes
#print axioms tiles_feasible
end
end QuorumAudit.Paper
