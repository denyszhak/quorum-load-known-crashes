import CircleFamilies

namespace QuorumAudit.Circle
noncomputable section
open Finset
open scoped BigOperators
variable {n h : ℕ} [NeZero n] [NeZero h]

def rankedWrites (n r q : ℕ) [NeZero n] : Finset (Finset (ZMod n)) :=
  (writes n r).filter (fun w => w.card = q)

theorem ranked_safe (r q : ℕ) :
    ∀ R ∈ reads n r, ∀ W ∈ rankedWrites n r q, (R ∩ W).Nonempty := by
  intro R hR W hW
  exact safe r R hR W (mem_filter.mp hW).1

theorem sum_sample_cards (w : ZMod n → ℕ) (hw : ∀ i, w i ≤ h) :
    (∑ t : ZMod h, (sample w t).card) = ∑ i : ZMod n, w i := by
  calc
    (∑ t : ZMod h, (sample w t).card) =
        ∑ t : ZMod h, ∑ i : ZMod n, if t ∈ block w i then (1 : ℕ) else 0 := by
      apply sum_congr rfl
      intro t _
      simp [sample]
    _ = ∑ i : ZMod n, ∑ t : ZMod h, if t ∈ block w i then (1 : ℕ) else 0 := sum_comm
    _ = ∑ i : ZMod n, w i := by
      apply sum_congr rfl
      intro i _
      have hc : (block (h := h) w i).card = w i := colors_card _ _ (hw i)
      rw [← sum_filter]
      simpa using hc

theorem sample_card (w : ZMod n → ℕ) (r q : ℕ) (hr : r ≤ n)
    (hroom : (q - 1) * r < n) (htotal : ∑ i : ZMod n, w i = q * h)
    (hw : ∀ i, w i ≤ h) (hwindow : ∀ s, h ≤ ∑ i ∈ arc r s, w i) :
    ∀ t : ZMod h, (sample w t).card = q := by
  have hp : (partialSum w n : ZMod h) = 0 := by rw [sum_cast, htotal]; simp
  have hmin : ∀ t : ZMod h, q ≤ (sample w t).card := by
    intro t
    by_contra hn
    have hsmall : (sample w t).card ≤ q - 1 := by omega
    obtain ⟨s, hs⟩ := live_arc r (sample w t)
      (lt_of_le_of_lt (Nat.mul_le_mul_right r hsmall) hroom)
    obtain ⟨i, hi⟩ := sample_hits w hp r s t (by rw [← sum_arc w r hr]; exact hwindow s)
    exact disjoint_left.mp hs (mem_inter.mp hi).1 (mem_inter.mp hi).2
  have hsum : (∑ _t : ZMod h, q) = ∑ t : ZMod h, (sample w t).card := by
    rw [sum_sample_cards w hw, htotal]
    simp [ZMod.card, mul_comm]
  intro t
  exact ((sum_eq_sum_iff_of_le (fun j _ => hmin j)).mp hsum t (mem_univ _)).symm

theorem ranked_sampled_routing (w : ZMod n → ℕ) (F : Finset (ZMod n))
    (r q : ℕ) (hr : r ≤ n) (hroom : (q - 1) * r < n)
    (htotal : ∑ i : ZMod n, w i = q * h)
    (hw : ∀ i, w i ≤ h) (hzero : ∀ i ∈ F, w i = 0)
    (hwindow : ∀ s, h ≤ ∑ i ∈ arc r s, w i) :
    ∃ route : Routing (rankedWrites n r q) univ F,
      ∀ i, incidence route.quorums route.p i = (w i : ℝ) / h := by
  have hp : (partialSum w n : ZMod h) = 0 := by rw [sum_cast, htotal]; simp
  have hfamily : ∀ t ∈ (univ : Finset (ZMod h)), sample w t ∈ rankedWrites n r q := by
    intro t _
    apply mem_filter.mpr
    refine ⟨mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _), ?_⟩,
      sample_card w r q hr hroom htotal hw hwindow t⟩
    intro s
    exact sample_hits w hp r s t (by rw [← sum_arc w r hr]; exact hwindow s)
  let route := routing_from_indexed univ (sample w) (fun _ => (1 / (h : ℝ)))
    (rankedWrites n r q) univ F hfamily (fun t _ => sample_live w F hzero t)
    (by intros; positivity) (by simp [ZMod.card, ne_of_gt (Nat.cast_pos.mpr (NeZero.pos h) : (0 : ℝ) < h)])
  refine ⟨route, ?_⟩
  intro i
  change incidence (univ.image (sample w)) (mergedProbability univ (sample w) (fun _ => (1 / (h : ℝ)))) i = _
  rw [merged_incidence]
  exact sample_marginal w hw i

#print axioms sample_card
#print axioms ranked_sampled_routing
end
end QuorumAudit.Circle
