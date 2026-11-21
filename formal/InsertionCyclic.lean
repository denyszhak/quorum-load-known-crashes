import InsertionLocal

namespace QuorumAudit

def cyclicLift (n p t : ℤ) {α : Type*} (w : ℤ → α) (j : ℤ) : α :=
  w (spliceIndex p t (j % (n + 3 * t)))

/-- Negative incoming indices wrap at the original boundary. The cut's
    distance from that boundary prevents interaction with inserted blocks. -/
theorem cyclic_incoming_eq {α : Type*} (w : ℤ → α) (n p t i d : ℤ)
    (hn : 11 ≤ n) (hp : 5 ≤ p) (hp2 : p + 7 ≤ n) (ht : 0 ≤ t)
    (hi : 0 ≤ i) (hi2 : i < n + 3 * t) (hd : 0 ≤ d) (hd4 : d ≤ 4)
    (hcycle : ∀ j, w (j + n) = w j) :
    cyclicLift n p t w (i - d) = w (spliceIndex p t (i - d)) := by
  unfold cyclicLift
  by_cases hnonneg : 0 ≤ i - d
  · rw [Int.emod_eq_of_lt hnonneg (by omega)]
  · have hm : (i - d) % (n + 3 * t) = i - d + (n + 3 * t) := by
      rw [Int.emod_eq_add_self_emod]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    have hnew : spliceIndex p t (i - d + (n + 3 * t)) = i - d + n := by
      unfold spliceIndex
      split_ifs <;> omega
    have hold : spliceIndex p t (i - d) = i - d := by
      unfold spliceIndex
      split_ifs <;> omega
    rw [hm, hnew, hold]
    exact hcycle _

theorem cyclic_degree_eq_local (w1 w2 : ℤ → ℝ) (n p t i : ℤ)
    (hn : 11 ≤ n) (hp : 5 ≤ p) (hp2 : p + 7 ≤ n) (ht : 0 ≤ t)
    (hi : 0 ≤ i) (hi2 : i < n + 3 * t)
    (hc1 : ∀ j, w1 (j + n) = w1 j) (hc2 : ∀ j, w2 (j + n) = w2 j) :
    localDegree (cyclicLift n p t w1) (cyclicLift n p t w2) i =
      localDegree (fun j => w1 (spliceIndex p t j)) (fun j => w2 (spliceIndex p t j)) i := by
  unfold localDegree
  dsimp only
  have h10 := cyclic_incoming_eq w1 n p t i 0 hn hp hp2 ht hi hi2 (by omega) (by omega) hc1
  have h11 := cyclic_incoming_eq w1 n p t i 1 hn hp hp2 ht hi hi2 (by omega) (by omega) hc1
  have h12 := cyclic_incoming_eq w1 n p t i 2 hn hp hp2 ht hi hi2 (by omega) (by omega) hc1
  have h20 := cyclic_incoming_eq w2 n p t i 0 hn hp hp2 ht hi hi2 (by omega) (by omega) hc2
  have h22 := cyclic_incoming_eq w2 n p t i 2 hn hp hp2 ht hi hi2 (by omega) (by omega) hc2
  have h24 := cyclic_incoming_eq w2 n p t i 4 hn hp hp2 ht hi hi2 (by omega) (by omega) hc2
  simp only [sub_zero] at h10 h20
  rw [h10, h11, h12, h20, h22, h24]

/-- Full cyclic flow-degree insertion lemma: old nodes retain their degree;
    inserted nodes have the sum of the three residue coefficients. -/
theorem cyclic_degree_insertion (w1 w2 : ℤ → ℝ) (n p t i : ℤ)
    (hn : 11 ≤ n) (hp : 5 ≤ p) (hp2 : p + 7 ≤ n) (ht : 0 ≤ t)
    (hi : 0 ≤ i) (hi2 : i < n + 3 * t)
    (hc1 : ∀ j, w1 (j + n) = w1 j) (hc2 : ∀ j, w2 (j + n) = w2 j)
    (h1 : ∀ s, p - 4 ≤ s → s < p → w1 s = w1 (s + 3))
    (h2 : ∀ s, p - 4 ≤ s → s < p → w2 s = w2 (s + 3)) :
    localDegree (cyclicLift n p t w1) (cyclicLift n p t w2) i =
      if i < p ∨ p + 3 * t ≤ i then localDegree w1 w2 (spliceIndex p t i)
      else w1 p + w1 (p + 1) + w1 (p + 2) + w2 p + w2 (p + 1) + w2 (p + 2) := by
  rw [cyclic_degree_eq_local w1 w2 n p t i hn hp hp2 ht hi hi2 hc1 hc2]
  have hp1 := periodic_window_of_four_equalities w1 p h1
  have hp2' := periodic_window_of_four_equalities w2 p h2
  split_ifs with h
  · exact degree_old_node w1 w2 p t i ht hp1 hp2' h
  · exact degree_inserted_node w1 w2 p t i hp1 hp2' (by omega) (by omega)

#print axioms cyclic_degree_insertion
end QuorumAudit
