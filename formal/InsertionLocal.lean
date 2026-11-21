import Arithmetic

/-! Local insertion geometry on integer coordinates.
The cyclic boundary and finite support are composed separately.
-/
namespace QuorumAudit

def spliceIndex (p t i : ℤ) : ℤ :=
  if i < p then i else if i < p + 3 * t then p + (i - p) % 3 else i - 3 * t

theorem splice_residue (p t i : ℤ) :
    (spliceIndex p t i - p) % 3 = (i - p) % 3 := by
  unfold spliceIndex
  split_ifs <;> omega

theorem splice_zero (p i : ℤ) : spliceIndex p 0 i = i := by
  unfold spliceIndex
  split_ifs <;> omega

/-- The four equalities actually checked in each base certificate imply the
    seven-start local periodicity used by the general degree proof. -/
theorem periodic_window_of_four_equalities {α : Type*} (w : ℤ → α) (p : ℤ)
    (h : ∀ s, p - 4 ≤ s → s < p → w s = w (s + 3)) :
    ∀ j, p - 4 ≤ j → j ≤ p + 2 → w j = w (p + (j - p) % 3) := by
  have h4 : w (p - 4) = w (p - 1) := by
    simpa [show p - 4 + 3 = p - 1 by omega] using h (p - 4) (by omega) (by omega)
  have h3 : w (p - 3) = w p := by
    simpa [show p - 3 + 3 = p by omega] using h (p - 3) (by omega) (by omega)
  have h2 : w (p - 2) = w (p + 1) := by
    simpa [show p - 2 + 3 = p + 1 by omega] using h (p - 2) (by omega) (by omega)
  have h1 : w (p - 1) = w (p + 2) := by
    simpa [show p - 1 + 3 = p + 2 by omega] using h (p - 1) (by omega) (by omega)
  intro j hj hj2
  have heq : j = p - 4 ∨ j = p - 3 ∨ j = p - 2 ∨ j = p - 1 ∨ j = p ∨ j = p + 1 ∨ j = p + 2 := by omega
  rcases heq with heq | heq | heq | heq | heq | heq | heq
  · have hr : (j - p) % 3 = 2 := by omega
    rw [hr, heq]
    exact h4.trans h1
  · have hr : (j - p) % 3 = 0 := by omega
    rw [hr, heq, add_zero]
    exact h3
  · have hr : (j - p) % 3 = 1 := by omega
    rw [hr, heq]
    exact h2
  · have hr : (j - p) % 3 = 2 := by omega
    rw [hr, heq]
    exact h1
  · have hr : (j - p) % 3 = 0 := by omega
    rw [hr, heq, add_zero]
  · have hr : (j - p) % 3 = 1 := by omega
    rw [hr, heq]
  · have hr : (j - p) % 3 = 2 := by omega
    rw [hr, heq]

/-- Copying a coefficient through insertion preserves every incoming
    coefficient at an old node. Only seven locally periodic starts are needed. -/
theorem incoming_old_node {α : Type*} (w : ℤ → α) (p t i d : ℤ)
    (ht : 0 ≤ t) (hd : 0 ≤ d) (hd4 : d ≤ 4)
    (hperiod : ∀ j, p - 4 ≤ j → j ≤ p + 2 → w j = w (p + (j - p) % 3))
    (hold : i < p ∨ p + 3 * t ≤ i) :
    w (spliceIndex p t (i - d)) = w (spliceIndex p t i - d) := by
  rcases hold with hi | hi
  · have hs : i - d < p := by omega
    simp [spliceIndex, hi, hs]
  · have hn : ¬i < p := by omega
    have hn2 : ¬i < p + 3 * t := by omega
    simp only [spliceIndex, ite_eq_right hn, ite_eq_right hn2]
    by_cases hs : i - d < p
    · rw [ite_eq_left hs]
      have hj : p - 4 ≤ i - d - 3 * t ∧ i - d - 3 * t ≤ p + 2 := by omega
      have hj2 : p - 4 ≤ i - d ∧ i - d ≤ p + 2 := by omega
      calc
        w (i - d) = w (p + (i - d - p) % 3) := hperiod _ hj2.1 hj2.2
        _ = w (p + (i - 3 * t - d - p) % 3) := by congr 1; omega
        _ = w (i - 3 * t - d) := (hperiod _ (by omega) (by omega)).symm
    · rw [ite_eq_right hs]
      by_cases hs2 : i - d < p + 3 * t
      · rw [ite_eq_left hs2]
        calc
          w (p + (i - d - p) % 3) = w (p + (i - 3 * t - d - p) % 3) := by congr 1; omega
          _ = w (i - 3 * t - d) := (hperiod _ (by omega) (by omega)).symm
      · rw [ite_eq_right hs2]
        congr 1
        omega

/-- Inside the inserted interval, each incoming coefficient is its residue
    class representative, regardless of the number of inserted blocks. -/
theorem incoming_inserted_node {α : Type*} (w : ℤ → α) (p t i d : ℤ)
    (hd : 0 ≤ d) (hd4 : d ≤ 4) (hi : p ≤ i) (hi2 : i < p + 3 * t)
    (hperiod : ∀ j, p - 4 ≤ j → j ≤ p + 2 → w j = w (p + (j - p) % 3)) :
    w (spliceIndex p t (i - d)) = w (p + (i - d - p) % 3) := by
  unfold spliceIndex
  split_ifs with h h2
  · exact hperiod _ (by omega) (by omega)
  · rfl
  · omega

def localDegree (w1 w2 : ℤ → ℝ) (i : ℤ) : ℝ :=
  w1 i + w1 (i - 1) + w1 (i - 2) + w2 i + w2 (i - 2) + w2 (i - 4)

theorem degree_old_node (w1 w2 : ℤ → ℝ) (p t i : ℤ) (ht : 0 ≤ t)
    (h1 : ∀ j, p - 4 ≤ j → j ≤ p + 2 → w1 j = w1 (p + (j - p) % 3))
    (h2 : ∀ j, p - 4 ≤ j → j ≤ p + 2 → w2 j = w2 (p + (j - p) % 3))
    (hi : i < p ∨ p + 3 * t ≤ i) :
    localDegree (fun j => w1 (spliceIndex p t j)) (fun j => w2 (spliceIndex p t j)) i =
      localDegree w1 w2 (spliceIndex p t i) := by
  unfold localDegree
  dsimp only
  have h11 := incoming_old_node w1 p t i 1 ht (by omega) (by omega) h1 hi
  have h12 := incoming_old_node w1 p t i 2 ht (by omega) (by omega) h1 hi
  have h22 := incoming_old_node w2 p t i 2 ht (by omega) (by omega) h2 hi
  have h24 := incoming_old_node w2 p t i 4 ht (by omega) (by omega) h2 hi
  rw [h11, h12, h22, h24]

/-- Degree in the inserted region is the sum of all three residue coefficients
    for each step, hence constant even for arbitrarily many inserted blocks. -/
theorem degree_inserted_node (w1 w2 : ℤ → ℝ) (p t i : ℤ)
    (h1 : ∀ j, p - 4 ≤ j → j ≤ p + 2 → w1 j = w1 (p + (j - p) % 3))
    (h2 : ∀ j, p - 4 ≤ j → j ≤ p + 2 → w2 j = w2 (p + (j - p) % 3))
    (hi : p ≤ i) (hi2 : i < p + 3 * t) :
    localDegree (fun j => w1 (spliceIndex p t j)) (fun j => w2 (spliceIndex p t j)) i =
      w1 p + w1 (p + 1) + w1 (p + 2) + w2 p + w2 (p + 1) + w2 (p + 2) := by
  unfold localDegree
  dsimp only
  have h10 := incoming_inserted_node w1 p t i 0 (by omega) (by omega) hi hi2 h1
  have h11 := incoming_inserted_node w1 p t i 1 (by omega) (by omega) hi hi2 h1
  have h12 := incoming_inserted_node w1 p t i 2 (by omega) (by omega) hi hi2 h1
  have h20 := incoming_inserted_node w2 p t i 0 (by omega) (by omega) hi hi2 h2
  have h22 := incoming_inserted_node w2 p t i 2 (by omega) (by omega) hi hi2 h2
  have h24 := incoming_inserted_node w2 p t i 4 (by omega) (by omega) hi hi2 h2
  simp only [sub_zero] at h10 h20
  rw [h10, h11, h12, h20, h22, h24]
  have hr : (i - p) % 3 = 0 ∨ (i - p) % 3 = 1 ∨ (i - p) % 3 = 2 := by omega
  rcases hr with hr | hr | hr
  all_goals
    have hmod1 : (i - 1 - p) % 3 = ((i - p) % 3 + 2) % 3 := by omega
    have hmod2 : (i - 2 - p) % 3 = ((i - p) % 3 + 1) % 3 := by omega
    have hmod4 : (i - 4 - p) % 3 = ((i - p) % 3 + 2) % 3 := by omega
    rw [hmod1, hmod2, hmod4, hr]
    norm_num
    ring

#print axioms incoming_old_node
#print axioms incoming_inserted_node
#print axioms degree_old_node
#print axioms degree_inserted_node
end QuorumAudit
