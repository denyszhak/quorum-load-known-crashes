import IndexedRouting
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin

namespace QuorumAudit
noncomputable section
open scoped BigOperators
variable {ι : Type*} [DecidableEq ι]

/-- An integer-scaled distribution. Repeated quorum entries are merged by
    `routing_from_indexed`; the scale is checked, never assumed. -/
structure NatDistribution (ι : Type*) where
  entries : List (Finset ι × Nat)
  scale : Nat

namespace NatDistribution
def quorum (d : NatDistribution ι) (j : Fin d.entries.length) : Finset ι := d.entries[j].1
def weight (d : NatDistribution ι) (j : Fin d.entries.length) : Nat := d.entries[j].2
def degree (d : NatDistribution ι) (i : ι) : Nat :=
  (d.entries.map (fun e => if i ∈ e.1 then e.2 else 0)).sum

def Valid (d : NatDistribution ι) (family : Finset (Finset ι)) (U F : Finset ι) : Prop :=
  0 < d.scale ∧ (∀ e ∈ d.entries, e.1 ∈ family ∧ e.1 ⊆ U \ F) ∧
    (d.entries.map Prod.snd).sum = d.scale

instance (d : NatDistribution ι) (family : Finset (Finset ι)) (U F : Finset ι) :
    Decidable (d.Valid family U F) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem indexed_sum {α : Type*} (l : List α) (f : α → Nat) :
    (∑ j : Fin l.length, f l[j]) = (l.map f).sum := by
  rw [← List.sum_ofFn]
  exact congrArg List.sum (List.ofFn_getElem_eq_map l f)

def toRouting (d : NatDistribution ι) (family : Finset (Finset ι)) (U F : Finset ι)
    (h : d.Valid family U F) : Routing family U F :=
  routing_from_indexed Finset.univ d.quorum (fun j => (d.weight j : ℝ) / d.scale)
    family U F (by intro j _; exact (h.2.1 d.entries[j] (List.getElem_mem _)).1)
    (by intro j _; exact (h.2.1 d.entries[j] (List.getElem_mem _)).2)
    (by intro j _; positivity) (by
      rw [← Finset.sum_div]
      have heq : (∑ j : Fin d.entries.length, (d.weight j : ℝ)) = (d.scale : ℝ) := by
        have hn : (∑ j : Fin d.entries.length, d.weight j) = d.scale := by
          change (∑ j : Fin d.entries.length, d.entries[j].2) = d.scale
          rw [indexed_sum]
          exact h.2.2
        exact_mod_cast hn
      rw [heq, div_self (by exact_mod_cast (Nat.ne_of_gt h.1) : (d.scale : ℝ) ≠ 0)])

theorem toRouting_incidence (d : NatDistribution ι) (family : Finset (Finset ι)) (U F : Finset ι)
    (h : d.Valid family U F) (i : ι) :
    incidence (d.toRouting family U F h).quorums (d.toRouting family U F h).p i =
      (d.degree i : ℝ) / d.scale := by
  change incidence (Finset.univ.image d.quorum)
    (mergedProbability Finset.univ d.quorum (fun j => (d.weight j : ℝ) / d.scale)) i = _
  rw [merged_incidence]
  have hd : d.degree i = ∑ j : Fin d.entries.length,
      if i ∈ d.quorum j then d.weight j else 0 := by
    symm
    exact indexed_sum d.entries (fun e => if i ∈ e.1 then e.2 else 0)
  rw [hd]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp
end NatDistribution

theorem sum_zero_extend {α : Type*} [DecidableEq α] (S T : Finset α)
    (hST : S ⊆ T) (p : α → ℝ) :
    (∑ x ∈ T, if x ∈ S then p x else 0) = ∑ x ∈ S, p x := by
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hST]

/-- Convexly mixing two legal routings preserves normalization, liveness
    and every node's affine inclusion probability. -/
def mixRouting {family : Finset (Finset ι)} {U F : Finset ι}
    (r s : Routing family U F) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    Routing family U F where
  quorums := r.quorums ∪ s.quorums
  subset := Finset.union_subset r.subset s.subset
  live := by
    intro q hq
    rcases Finset.mem_union.mp hq with h | h
    · exact r.live q h
    · exact s.live q h
  p := fun q => (1-t) * (if q ∈ r.quorums then r.p q else 0) +
    t * (if q ∈ s.quorums then s.p q else 0)
  nonnegative := by
    intro q _
    apply add_nonneg
    · apply mul_nonneg (by linarith)
      split_ifs with h
      · exact r.nonnegative q h
      · rfl
    · apply mul_nonneg ht
      split_ifs with h
      · exact s.nonnegative q h
      · rfl
  normalized := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      sum_zero_extend _ _ Finset.subset_union_left,
      sum_zero_extend _ _ Finset.subset_union_right, r.normalized, s.normalized]
    ring

theorem mixRouting_incidence {family : Finset (Finset ι)} {U F : Finset ι}
    (r s : Routing family U F) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (i : ι) :
    incidence (mixRouting r s t ht ht1).quorums (mixRouting r s t ht ht1).p i =
      (1-t) * incidence r.quorums r.p i + t * incidence s.quorums s.p i := by
  unfold incidence mixRouting
  simp only
  have heq : ∀ q : Finset ι,
      (if i ∈ q then (1-t) * (if q ∈ r.quorums then r.p q else 0) +
        t * (if q ∈ s.quorums then s.p q else 0) else 0) =
      (1-t) * (if q ∈ r.quorums then (if i ∈ q then r.p q else 0) else 0) +
        t * (if q ∈ s.quorums then (if i ∈ q then s.p q else 0) else 0) := by
    intro q
    split_ifs <;> ring
  simp_rw [heq]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_zero_extend _ _ Finset.subset_union_left,
    sum_zero_extend _ _ Finset.subset_union_right]

/-- Two endpoint strategies yield the whole real workload interval.
    The read routing at the positive endpoint is also available at zero. -/
theorem interpolate_twenty_three {R W : Finset (Finset ι)} {U F : Finset ι}
    (r : Routing R U F) (w0 w1 : Routing W U F)
    (h0 : ∀ i ∈ U, incidence w0.quorums w0.p i ≤ 1 / 5)
    (h1 : ∀ i ∈ U, combined r w1 (1 / 9) i ≤ 2 / 9)
    (a : ℝ) (ha : 0 ≤ a) (ha9 : a ≤ 1 / 9) :
    ∃ w : Routing W U F, ∀ i ∈ U, combined r w a i ≤ (1 + a) / 5 := by
  have hd : 0 < 1-a := by linarith
  let t := 8*a/(1-a)
  have ht : 0 ≤ t := div_nonneg (by linarith) (le_of_lt hd)
  have ht1 : t ≤ 1 := by
    dsimp [t]
    apply (div_le_one hd).mpr
    linarith
  refine ⟨mixRouting w0 w1 t ht ht1, ?_⟩
  intro i hi
  have hEq : combined r (mixRouting w0 w1 t ht ht1) a i =
      (1-9*a) * incidence w0.quorums w0.p i + 9*a * combined r w1 (1/9) i := by
    unfold combined
    rw [mixRouting_incidence]
    dsimp [t]
    field_simp
    <;> ring
  rw [hEq]
  have hleft := mul_le_mul_of_nonneg_left (h0 i hi) (by linarith : 0 ≤ 1-9*a)
  have hright := mul_le_mul_of_nonneg_left (h1 i hi) (by linarith : 0 ≤ 9*a)
  linarith

#print axioms NatDistribution.toRouting
#print axioms interpolate_twenty_three
end
end QuorumAudit
