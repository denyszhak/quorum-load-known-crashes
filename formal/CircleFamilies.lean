import CircleSampling
import ConstructiveRouting

namespace QuorumAudit.Circle
noncomputable section
open Finset
open scoped BigOperators
variable {n h : ℕ} [NeZero n] [NeZero h]

def reads (n r : ℕ) [NeZero n] : Finset (Finset (ZMod n)) :=
  univ.image (arc r)

def writes (n r : ℕ) [NeZero n] : Finset (Finset (ZMod n)) :=
  univ.powerset.filter (fun w => ∀ s : ZMod n, (arc r s ∩ w).Nonempty)

theorem safe (r : ℕ) : ∀ R ∈ reads n r, ∀ W ∈ writes n r, (R ∩ W).Nonempty := by
  intro R hR W hW
  obtain ⟨s, _, rfl⟩ := mem_image.mp hR
  exact (mem_filter.mp hW).2 s

theorem live_arc (r : ℕ) (F : Finset (ZMod n)) (hroom : F.card * r < n) :
    ∃ s : ZMod n, Disjoint (arc r s) F := by
  let bad := F.biUnion (fun z => (range r).image (fun j : ℕ => z - (j : ZMod n)))
  have hc : bad.card ≤ F.card * r := by
    apply le_trans card_biUnion_le
    calc
      (∑ z ∈ F, ((range r).image (fun j : ℕ => z - (j : ZMod n))).card) ≤
          ∑ _z ∈ F, r := sum_le_sum (fun _ _ => le_trans card_image_le (le_of_eq (card_range r)))
      _ = F.card * r := by simp
  have hex : ∃ s : ZMod n, s ∉ bad := by
    by_contra hn
    push Not at hn
    have hh : (univ : Finset (ZMod n)).card ≤ bad.card := card_le_card (by intro s _; exact hn s)
    simp only [card_univ, ZMod.card] at hh
    omega
  obtain ⟨s, hs⟩ := hex
  refine ⟨s, disjoint_left.mpr ?_⟩
  intro z hz hF
  obtain ⟨j, hj, hsz⟩ := mem_image.mp hz
  apply hs
  apply mem_biUnion.mpr
  refine ⟨z, hF, mem_image.mpr ⟨j, hj, ?_⟩⟩
  rw [← hsz]
  simp

theorem sum_cast (w : ZMod n → ℕ) : partialSum w n = ∑ i : ZMod n, w i := by
  unfold partialSum
  apply sum_bij (fun (j : ℕ) _ => (j : ZMod n))
  · intros; exact mem_univ _
  · intro a ha b hb hab
    exact cast_injective_below (mem_range.mp ha) (mem_range.mp hb) hab
  · intro i _
    exact ⟨i.val, mem_range.mpr (ZMod.val_lt i), by simp⟩
  · intros; rfl

omit [NeZero n] in
theorem sum_arc (w : ZMod n → ℕ) (r : ℕ) (hr : r ≤ n) (s : ZMod n) :
    ∑ i ∈ arc r s, w i = ∑ j ∈ range r, w (s + (j : ZMod n)) := by
  apply sum_image
  intro a ha b hb hab
  exact cast_injective_below (lt_of_lt_of_le (mem_range.mp ha) hr)
    (lt_of_lt_of_le (mem_range.mp hb) hr) (add_left_cancel hab)

omit [NeZero h] in
theorem sample_live (w : ZMod n → ℕ) (F : Finset (ZMod n))
    (hzero : ∀ i ∈ F, w i = 0) (t : ZMod h) : sample w t ⊆ univ \ F := by
  intro i hi
  refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
  intro hiF
  have ht := (mem_filter.mp hi).2
  simp [block, colors, hzero i hiF] at ht

theorem sampled_routing (w : ZMod n → ℕ) (F : Finset (ZMod n))
    (r q : ℕ) (hr : r ≤ n)
    (htotal : ∑ i : ZMod n, w i = q * h)
    (hw : ∀ i, w i ≤ h) (hzero : ∀ i ∈ F, w i = 0)
    (hwindow : ∀ s, h ≤ ∑ i ∈ arc r s, w i) :
    ∃ route : Routing (writes n r) univ F,
      ∀ i, incidence route.quorums route.p i = (w i : ℝ) / h := by
  have hp : (partialSum w n : ZMod h) = 0 := by
    rw [sum_cast, htotal]
    simp
  have hfamily : ∀ t ∈ (univ : Finset (ZMod h)), sample w t ∈ writes n r := by
    intro t _
    apply mem_filter.mpr
    refine ⟨mem_powerset.mpr (subset_univ _), ?_⟩
    intro s
    exact sample_hits w hp r s t (by rw [← sum_arc w r hr]; exact hwindow s)
  let route := routing_from_indexed univ (sample w) (fun _ => (1 / (h : ℝ)))
    (writes n r) univ F hfamily (fun t _ => sample_live w F hzero t)
    (by intros; positivity) (by simp [ZMod.card, ne_of_gt (Nat.cast_pos.mpr (NeZero.pos h) : (0 : ℝ) < h)])
  refine ⟨route, ?_⟩
  intro i
  change incidence (univ.image (sample w)) (mergedProbability univ (sample w) (fun _ => (1 / (h : ℝ)))) i = _
  rw [merged_incidence]
  exact sample_marginal w hw i

#print axioms live_arc
#print axioms sampled_routing
end
end QuorumAudit.Circle
