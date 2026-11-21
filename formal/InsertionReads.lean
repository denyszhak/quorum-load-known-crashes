import InsertionCyclic

namespace QuorumAudit
set_option maxHeartbeats 1000000

theorem outgoing_old_node {α : Type*} (r : ℤ → α) (p t i d : ℤ)
    (ht : 0 ≤ t) (hd : 0 ≤ d) (hd4 : d ≤ 4)
    (hperiod : ∀ j, p - 4 ≤ j → j ≤ p + 3 → r j = r (p + (j - p) % 3))
    (hold : i < p ∨ p + 3 * t ≤ i) :
    r (spliceIndex p t (i + d)) = r (spliceIndex p t i + d) := by
  rcases hold with hi | hi
  · have hsi : spliceIndex p t i = i := by simp [spliceIndex, hi]
    rw [hsi]
    unfold spliceIndex
    split_ifs with h h2
    · rfl
    · exact (hperiod _ (by omega) (by omega)).symm
    · calc
        r (i + d - 3 * t) = r (p + (i + d - 3 * t - p) % 3) :=
          hperiod _ (by omega) (by omega)
        _ = r (p + (i + d - p) % 3) := by congr 1; omega
        _ = r (i + d) := (hperiod _ (by omega) (by omega)).symm
  · have hsi : spliceIndex p t i = i - 3 * t := by
      unfold spliceIndex
      split_ifs <;> omega
    have hsd : spliceIndex p t (i + d) = i + d - 3 * t := by
      unfold spliceIndex
      split_ifs <;> omega
    rw [hsi, hsd]
    congr 1
    omega

theorem outgoing_inserted_node {α : Type*} (r : ℤ → α) (p t i d : ℤ)
    (hd : 0 ≤ d) (hd4 : d ≤ 4) (hi : p ≤ i) (hi2 : i < p + 3 * t)
    (hperiod : ∀ j, p - 4 ≤ j → j ≤ p + 3 → r j = r (p + (j - p) % 3)) :
    r (spliceIndex p t (i + d)) = r (p + (i + d - p) % 3) := by
  unfold spliceIndex
  split_ifs with h h2
  · omega
  · rfl
  · calc
      r (i + d - 3 * t) = r (p + (i + d - 3 * t - p) % 3) :=
        hperiod _ (by omega) (by omega)
      _ = r (p + (i + d - p) % 3) := by congr 1; omega

theorem cyclic_outgoing_eq {α : Type*} (r : ℤ → α) (n p t i d : ℤ)
    (hn : 11 ≤ n) (hp : 5 ≤ p) (hp2 : p + 7 ≤ n) (ht : 0 ≤ t)
    (hi : 0 ≤ i) (hi2 : i < n + 3 * t) (hd : 0 ≤ d) (hd4 : d ≤ 4)
    (hcycle : ∀ j, r (j + n) = r j) :
    cyclicLift n p t r (i + d) = r (spliceIndex p t (i + d)) := by
  unfold cyclicLift
  by_cases hlt : i + d < n + 3 * t
  · rw [Int.emod_eq_of_lt (by omega) hlt]
  · have hm : (i + d) % (n + 3 * t) = i + d - (n + 3 * t) := by
      have hs : (i + d - (n + 3 * t)) % (n + 3 * t) = (i + d) % (n + 3 * t) := by
        simp [Int.sub_emod]
      rw [← hs]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    have hnew : spliceIndex p t (i + d - (n + 3 * t)) = i + d - (n + 3 * t) := by
      unfold spliceIndex
      split_ifs <;> omega
    have hold : spliceIndex p t (i + d) = i + d - 3 * t := by
      unfold spliceIndex
      split_ifs <;> omega
    rw [hm, hnew, hold]
    exact (hcycle (i + d - (n + 3 * t))).symm.trans (by congr 1; omega)

/-- A locally periodic read extends to a hitting set of EVERY cyclic write,
    including writes containing failed nodes. No availability-only shortcut. -/
theorem cyclic_read_hits_after_insertion (r : ℤ → Prop) (n p t : ℤ)
    (hn : 11 ≤ n) (hp : 5 ≤ p) (hp2 : p + 7 ≤ n) (ht : 0 ≤ t)
    (hcycle : ∀ j, r (j + n) = r j)
    (hperiod : ∀ j, p - 4 ≤ j → j ≤ p + 3 → r j = r (p + (j - p) % 3))
    (hcolor : r p ∨ r (p + 1) ∨ r (p + 2))
    (hhit : ∀ i e, 0 ≤ i → i < n → (e = 1 ∨ e = 2) →
      r i ∨ r (i + e) ∨ r (i + 2 * e)) :
    ∀ i e, 0 ≤ i → i < n + 3 * t → (e = 1 ∨ e = 2) →
      cyclicLift n p t r i ∨ cyclicLift n p t r (i + e) ∨
        cyclicLift n p t r (i + 2 * e) := by
  intro i e hi hi2 he
  have he0 : 0 ≤ e := by omega
  have he4 : e ≤ 4 := by omega
  have he20 : 0 ≤ 2 * e := by omega
  have he24 : 2 * e ≤ 4 := by omega
  have h0 := cyclic_outgoing_eq r n p t i 0 hn hp hp2 ht hi hi2 (by omega) (by omega) hcycle
  have h1 := cyclic_outgoing_eq r n p t i e hn hp hp2 ht hi hi2 he0 he4 hcycle
  have h2 := cyclic_outgoing_eq r n p t i (2 * e) hn hp hp2 ht hi hi2 he20 he24 hcycle
  simp only [add_zero] at h0
  rw [h0, h1, h2]
  by_cases hold : i < p ∨ p + 3 * t ≤ i
  · rw [outgoing_old_node r p t i e ht he0 he4 hperiod hold,
      outgoing_old_node r p t i (2 * e) ht he20 he24 hperiod hold]
    have hbounds : 0 ≤ spliceIndex p t i ∧ spliceIndex p t i < n := by
      unfold spliceIndex
      split_ifs <;> omega
    exact hhit _ _ hbounds.1 hbounds.2 he
  · have hii : p ≤ i := by omega
    have hii2 : i < p + 3 * t := by omega
    have h00 := outgoing_inserted_node r p t i 0 (by omega) (by omega) hii hii2 hperiod
    simp only [add_zero] at h00
    rw [h00, outgoing_inserted_node r p t i e he0 he4 hii hii2 hperiod,
      outgoing_inserted_node r p t i (2 * e) he20 he24 hii hii2 hperiod]
    have hr : (i - p) % 3 = 0 ∨ (i - p) % 3 = 1 ∨ (i - p) % 3 = 2 := by omega
    rcases hr with hr | hr | hr <;> rcases he with he | he
    all_goals
      have hm1 : (i + e - p) % 3 = ((i - p) % 3 + e) % 3 := by omega
      have hm2 : (i + 2 * e - p) % 3 = ((i - p) % 3 + 2 * e) % 3 := by omega
      rw [hm1, hm2, hr, he]
      norm_num
      rcases hcolor with h | h | h <;>
        first | exact Or.inl h | exact Or.inr (Or.inl h) | exact Or.inr (Or.inr h)

#print axioms cyclic_read_hits_after_insertion
end QuorumAudit
