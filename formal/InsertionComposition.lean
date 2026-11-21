import InsertionReads
import InsertionMass

namespace QuorumAudit

theorem splice_bounds (n p t i : ℤ) (hp : 0 ≤ p) (hp2 : p + 3 ≤ n)
    (ht : 0 ≤ t) (hi : 0 ≤ i) (hi2 : i < n + 3 * t) :
    0 ≤ spliceIndex p t i ∧ spliceIndex p t i < n := by
  unfold spliceIndex
  split_ifs <;> omega

theorem splice_old_image (p t i : ℤ) (ht : 0 ≤ t) :
    spliceIndex p t (if i < p then i else i + 3 * t) = i := by
  split_ifs with hi
  · simp [spliceIndex, hi]
  · unfold spliceIndex
    split_ifs <;> omega

theorem cyclicLift_periodic {α : Type*} (w : ℤ → α) (n p t j : ℤ) :
    cyclicLift n p t w (j + (n + 3 * t)) = cyclicLift n p t w j := by
  simp [cyclicLift]

/-- A second cut at least twelve nodes later keeps its entire local signature
    after the first insertion, with coordinates shifted by three times t. -/
theorem later_cut_signature_preserved {α : Type*} (w : ℤ → α) (n p q t j : ℤ)
    (hpq : p + 12 ≤ q) (hq : q + 7 ≤ n) (hp : 0 ≤ p) (ht : 0 ≤ t)
    (hj : q + 3 * t - 4 ≤ j) (hj2 : j ≤ q + 3 * t + 6) :
    cyclicLift n p t w j = w (j - 3 * t) := by
  have hi : 0 ≤ j := by omega
  have hi2 : j < n + 3 * t := by omega
  unfold cyclicLift
  rw [Int.emod_eq_of_lt hi hi2]
  unfold spliceIndex
  split_ifs <;> first | rfl | omega

theorem later_cut_four_equalities {α : Type*} (w : ℤ → α) (n p q t : ℤ)
    (hpq : p + 12 ≤ q) (hq : q + 7 ≤ n) (hp : 0 ≤ p) (ht : 0 ≤ t)
    (h : ∀ s, q - 4 ≤ s → s < q → w s = w (s + 3)) :
    ∀ s, q + 3 * t - 4 ≤ s → s < q + 3 * t →
      cyclicLift n p t w s = cyclicLift n p t w (s + 3) := by
  intro s hs hs2
  rw [later_cut_signature_preserved w n p q t s hpq hq hp ht hs (by omega),
    later_cut_signature_preserved w n p q t (s + 3) hpq hq hp ht (by omega) (by omega)]
  simpa [show s + 3 - 3 * t = s - 3 * t + 3 by omega] using
    h (s - 3 * t) (by omega) (by omega)

theorem later_cut_read_periodicity {α : Type*} (r : ℤ → α) (n p q t : ℤ)
    (hpq : p + 12 ≤ q) (hq : q + 7 ≤ n) (hp : 0 ≤ p) (ht : 0 ≤ t)
    (h : ∀ j, q - 4 ≤ j → j ≤ q + 3 → r j = r (q + (j - q) % 3)) :
    ∀ j, q + 3 * t - 4 ≤ j → j ≤ q + 3 * t + 3 →
      cyclicLift n p t r j =
        cyclicLift n p t r (q + 3 * t + (j - (q + 3 * t)) % 3) := by
  intro j hj hj2
  rw [later_cut_signature_preserved r n p q t j hpq hq hp ht hj (by omega),
    later_cut_signature_preserved r n p q t
      (q + 3 * t + (j - (q + 3 * t)) % 3) hpq hq hp ht (by omega) (by omega)]
  have heq : q + 3 * t + (j - (q + 3 * t)) % 3 - 3 * t =
      q + (j - 3 * t - q) % 3 := by omega
  rw [heq]
  exact h _ (by omega) (by omega)

/-- All failed old nodes remain excluded from a read when their shifted
    images are excluded. The image is an old node, never a copied new node. -/
theorem read_excludes_old_image (r : ℤ → Prop) (n p t i : ℤ)
    (hn : 0 ≤ i) (hn2 : i < n) (hp : 0 ≤ p) (hp2 : p ≤ n)
    (ht : 0 ≤ t) (hr : ¬r i) :
    ¬cyclicLift n p t r (if i < p then i else i + 3 * t) := by
  have hi : 0 ≤ (if i < p then i else i + 3 * t) := by split_ifs <;> omega
  have hi2 : (if i < p then i else i + 3 * t) < n + 3 * t := by split_ifs <;> omega
  unfold cyclicLift
  rw [Int.emod_eq_of_lt hi hi2, splice_old_image p t i ht]
  exact hr

theorem degree_at_old_image (w1 w2 : ℤ → ℝ) (n p t i : ℤ)
    (hn : 11 ≤ n) (hp : 5 ≤ p) (hp2 : p + 7 ≤ n) (ht : 0 ≤ t)
    (hi : 0 ≤ i) (hi2 : i < n)
    (hc1 : ∀ j, w1 (j + n) = w1 j) (hc2 : ∀ j, w2 (j + n) = w2 j)
    (h1 : ∀ s, p - 4 ≤ s → s < p → w1 s = w1 (s + 3))
    (h2 : ∀ s, p - 4 ≤ s → s < p → w2 s = w2 (s + 3)) :
    localDegree (cyclicLift n p t w1) (cyclicLift n p t w2)
      (if i < p then i else i + 3 * t) = localDegree w1 w2 i := by
  have hb0 : 0 ≤ (if i < p then i else i + 3 * t) := by split_ifs <;> omega
  have hb1 : (if i < p then i else i + 3 * t) < n + 3 * t := by split_ifs <;> omega
  rw [cyclic_degree_insertion w1 w2 n p t _ hn hp hp2 ht hb0 hb1 hc1 hc2 h1 h2]
  have hold : (if i < p then i else i + 3 * t) < p ∨
      p + 3 * t ≤ (if i < p then i else i + 3 * t) := by split_ifs <;> omega
  rw [if_pos hold, splice_old_image p t i ht]

/-- Nonnegative flows cannot place positive mass on any write incident to
    a node with zero degree. This is the availability check for failed nodes. -/
theorem zero_degree_coefficients (w1 w2 : ℤ → ℝ) (i : ℤ)
    (h1 : ∀ j, 0 ≤ w1 j) (h2 : ∀ j, 0 ≤ w2 j)
    (hz : localDegree w1 w2 i = 0) :
    w1 i = 0 ∧ w1 (i - 1) = 0 ∧ w1 (i - 2) = 0 ∧
      w2 i = 0 ∧ w2 (i - 2) = 0 ∧ w2 (i - 4) = 0 := by
  have h10 := h1 i
  have h11 := h1 (i - 1)
  have h12 := h1 (i - 2)
  have h20 := h2 i
  have h22 := h2 (i - 2)
  have h24 := h2 (i - 4)
  unfold localDegree at hz
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

def residueTotal (w1 w2 : ℤ → ℝ) (p : ℤ) : ℝ :=
  w1 p + w1 (p + 1) + w1 (p + 2) + w2 p + w2 (p + 1) + w2 (p + 2)

theorem localDegree_add_scaled (c1 c2 u1 u2 : ℤ → ℝ) (d : ℝ) (i : ℤ) :
    localDegree (fun j => c1 j + d * u1 j) (fun j => c2 j + d * u2 j) i =
      localDegree c1 c2 i + d * localDegree u1 u2 i := by
  unfold localDegree
  ring

/-- The extra critical-flow correction restores the target parameter.
    Applies to old and inserted survivors, for any real correction amount. -/
theorem corrected_degree (c1 c2 u1 u2 : ℤ → ℝ) (k d count : ℝ)
    (node : ℤ) (hu : localDegree u1 u2 node = 1)
    (hc : localDegree c1 c2 node = k + 2 - count) :
    localDegree (fun j => c1 j + d * u1 j) (fun j => c2 j + d * u2 j) node =
      (k + d) + 2 - count := by
  rw [localDegree_add_scaled, hu, hc]
  ring

/-- Whole-flow mass after expansion and the correction, not just node load. -/
theorem corrected_mass (k d oldC oldU : ℝ)
    (hc : oldC = (k - 1) * (k + 2) + d * (k + 1))
    (hu : oldU = k + d) :
    oldC + d * oldU = ((k + d) - 1) * ((k + d) + 2) := by
  rw [hc, hu]
  ring

#print axioms later_cut_signature_preserved
#print axioms later_cut_four_equalities
#print axioms later_cut_read_periodicity
#print axioms read_excludes_old_image
#print axioms degree_at_old_image
#print axioms zero_degree_coefficients
#print axioms corrected_mass
end QuorumAudit
