import CircleRanked

namespace QuorumAudit.Circle
noncomputable section
open Finset
open scoped BigOperators
variable {n h : ℕ} [NeZero n] [NeZero h]

def residueCount (P a : ℕ) (t : ZMod h) : ℕ :=
  ∑ j ∈ range a, if ((P + j : ℕ) : ZMod h) = t then 1 else 0

omit [NeZero h] in
theorem residueCount_small (P a : ℕ) (ha : a ≤ h) (t : ZMod h) :
    residueCount P a t = if t ∈ colors h P a then 1 else 0 := by
  have hinj : Set.InjOn (fun j : ℕ => ((P + j : ℕ) : ZMod h)) (range a) := by
    intro x hx y hy hxy
    simp only [Nat.cast_add] at hxy
    exact cast_injective_below (lt_of_lt_of_le (mem_range.mp hx) ha)
      (lt_of_lt_of_le (mem_range.mp hy) ha) (add_left_cancel hxy)
  unfold residueCount
  change (∑ j ∈ range a, (fun u : ZMod h => if u = t then (1 : ℕ) else 0)
    ((P + j : ℕ) : ZMod h)) = _
  calc
    _ = ∑ u ∈ (range a).image (fun j : ℕ => ((P + j : ℕ) : ZMod h)),
        if u = t then (1 : ℕ) else 0 := (sum_image hinj).symm
    _ = _ := by simp [colors]

omit [NeZero h] in
theorem residueCount_add (P a b : ℕ) (t : ZMod h) :
    residueCount P (a + b) t = residueCount P a t + residueCount (P + a) b t := by
  unfold residueCount
  rw [sum_range_add]
  congr 1
  apply sum_congr rfl
  intro j _
  rw [Nat.add_assoc]

theorem residueCount_total (q : ℕ) (t : ZMod h) : residueCount 0 (q * h) t = q := by
  induction q with
  | zero => simp [residueCount]
  | succ q ih =>
    rw [Nat.succ_mul, residueCount_add, ih, residueCount_small _ _ le_rfl,
      colors_full _ _ le_rfl]
    simp

omit [NeZero n] in
theorem prefix_block_count (w : ZMod n → ℕ) (hw : ∀ i, w i ≤ h)
    (hp : (partialSum w n : ZMod h) = 0) (l : ℕ) (t : ZMod h) :
    (∑ j ∈ range l, if t ∈ block w (j : ZMod n) then (1 : ℕ) else 0) =
      residueCount 0 (partialSum w l) t := by
  induction l with
  | zero => simp [partialSum, residueCount]
  | succ l ih =>
    rw [sum_range_succ, ih]
    have hs : partialSum w (l + 1) = partialSum w l + w (l : ZMod n) := by
      exact sum_range_succ _ l
    rw [hs, residueCount_add]
    simp only [zero_add]
    rw [residueCount_small _ _ (hw _), block_lift w hp]

theorem sample_card_exact (w : ZMod n → ℕ) (q : ℕ)
    (htotal : ∑ i : ZMod n, w i = q * h) (hw : ∀ i, w i ≤ h) :
    ∀ t : ZMod h, (sample w t).card = q := by
  have hp : (partialSum w n : ZMod h) = 0 := by rw [sum_cast, htotal]; simp
  intro t
  calc
    (sample w t).card = ∑ i : ZMod n, if t ∈ block w i then (1 : ℕ) else 0 := by
      simp [sample]
    _ = ∑ j ∈ range n, if t ∈ block w (j : ZMod n) then (1 : ℕ) else 0 := by
      symm
      exact sum_cast (fun i => if t ∈ block w i then 1 else 0)
    _ = residueCount 0 (partialSum w n) t := prefix_block_count w hw hp n t
    _ = q := by rw [sum_cast, htotal]; exact residueCount_total q t

theorem exact_ranked_sampled_routing (w : ZMod n → ℕ) (F : Finset (ZMod n))
    (r q : ℕ) (hr : r ≤ n) (htotal : ∑ i : ZMod n, w i = q * h)
    (hw : ∀ i, w i ≤ h) (hzero : ∀ i ∈ F, w i = 0)
    (hwindow : ∀ s, h ≤ ∑ i ∈ arc r s, w i) :
    ∃ route : Routing (rankedWrites n r q) univ F,
      ∀ i, incidence route.quorums route.p i = (w i : ℝ) / h := by
  have hp : (partialSum w n : ZMod h) = 0 := by rw [sum_cast, htotal]; simp
  have hfamily : ∀ t ∈ (univ : Finset (ZMod h)), sample w t ∈ rankedWrites n r q := by
    intro t _
    apply mem_filter.mpr
    refine ⟨mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _), ?_⟩,
      sample_card_exact w q htotal hw t⟩
    intro s
    exact sample_hits w hp r s t (by rw [← sum_arc w r hr]; exact hwindow s)
  let route := routing_from_indexed univ (sample w) (fun _ => (1 / (h : ℝ)))
    (rankedWrites n r q) univ F hfamily (fun t _ => sample_live w F hzero t)
    (by intros; positivity)
    (by simp [ZMod.card, ne_of_gt (Nat.cast_pos.mpr (NeZero.pos h) : (0 : ℝ) < h)])
  refine ⟨route, ?_⟩
  intro i
  change incidence (univ.image (sample w))
    (mergedProbability univ (sample w) (fun _ => (1 / (h : ℝ)))) i = _
  rw [merged_incidence]
  exact sample_marginal w hw i

#print axioms sample_card_exact
#print axioms exact_ranked_sampled_routing
end
end QuorumAudit.Circle
