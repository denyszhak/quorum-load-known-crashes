import InsertionLocal

namespace QuorumAudit
open Finset

def spliceNat (p t i : Nat) : Nat :=
  if i < p then i else if i < p + 3 * t then p + (i - p) % 3 else i - 3 * t

theorem spliceNat_cast (p t i : Nat) :
    (spliceNat p t i : ℤ) = spliceIndex p t i := by
  by_cases h : i < p
  · have h' : (i : ℤ) < p := by exact_mod_cast h
    simp [spliceNat, spliceIndex, h, h']
  · have h' : ¬(i : ℤ) < p := by exact_mod_cast h
    by_cases h2 : i < p + 3 * t
    · have h2' : (i : ℤ) < p + 3 * t := by exact_mod_cast h2
      simp only [spliceNat, spliceIndex, ite_eq_right h, ite_eq_right h',
        ite_eq_left h2, ite_eq_left h2', Nat.cast_add, Int.natCast_emod]
      rw [Nat.cast_sub (by omega)]
      norm_num
    · have h2' : ¬(i : ℤ) < p + 3 * t := by exact_mod_cast h2
      simp only [spliceNat, spliceIndex, ite_eq_right h, ite_eq_right h',
        ite_eq_right h2, ite_eq_right h2']
      rw [Nat.cast_sub (by omega)]
      push_cast
      rfl

theorem residue_sum (f : Nat → ℝ) (p t : Nat) :
    (∑ j ∈ range (3 * t), f (p + j % 3)) =
      t * (f p + f (p + 1) + f (p + 2)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show 3 * (t + 1) = 3 * t + 3 by omega, sum_range_add, ih]
    have hh : (∑ j ∈ range 3, f (p + (3 * t + j) % 3)) =
        f p + f (p + 1) + f (p + 2) := by
      simp [sum_range_succ, Nat.add_mod]
    rw [hh]
    push_cast
    ring

/-- Exact finite mass formula, with the number of inserted blocks unbounded.
    This also proves read cardinality when f is a membership indicator. -/
theorem splice_mass (f : Nat → ℝ) (n p t : Nat) (hp : p ≤ n) :
    (∑ i ∈ range (n + 3 * t), f (spliceNat p t i)) =
      (∑ i ∈ range n, f i) + t * (f p + f (p + 1) + f (p + 2)) := by
  have hnew : n + 3 * t = p + (3 * t + (n - p)) := by omega
  have hold : n = p + (n - p) := by omega
  rw [hnew, sum_range_add]
  have hpre : (∑ i ∈ range p, f (spliceNat p t i)) = ∑ i ∈ range p, f i := by
    apply sum_congr rfl
    intro i hi
    simp only [mem_range] at hi
    simp [spliceNat, hi]
  have hmiddle : (∑ j ∈ range (3 * t), f (spliceNat p t (p + j))) =
      t * (f p + f (p + 1) + f (p + 2)) := by
    rw [← residue_sum f p t]
    apply sum_congr rfl
    intro j hj
    simp only [mem_range] at hj
    have h1 : ¬p + j < p := by omega
    have h2 : p + j < p + 3 * t := by omega
    simp [spliceNat, h1, h2]
  have hpost : (∑ j ∈ range (n - p), f (spliceNat p t (p + (3 * t + j)))) =
      ∑ j ∈ range (n - p), f (p + j) := by
    apply sum_congr rfl
    intro j hj
    have h1 : ¬p + (3 * t + j) < p := by omega
    have h2 : ¬p + (3 * t + j) < p + 3 * t := by omega
    simp only [spliceNat, ite_eq_right h1, ite_eq_right h2]
    congr 1
    omega
  rw [hpre, sum_range_add, hmiddle, hpost]
  have hsum : (∑ i ∈ range n, f i) =
      (∑ i ∈ range p, f i) + ∑ j ∈ range (n - p), f (p + j) := by
    conv_lhs => rw [hold]
    exact sum_range_add f p (n - p)
  rw [hsum]
  ring

#print axioms splice_mass
end QuorumAudit
