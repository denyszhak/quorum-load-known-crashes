import SemanticBounds

namespace QuorumAudit
noncomputable section
open scoped BigOperators
variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

def mergedProbability (I : Finset κ) (Q : κ → Finset ι) (p : κ → ℝ)
    (q : Finset ι) : ℝ := ∑ j ∈ I.filter (fun j => Q j = q), p j

theorem merged_normalization (I : Finset κ) (Q : κ → Finset ι) (p : κ → ℝ)
    (hp : ∑ j ∈ I, p j = 1) :
    ∑ q ∈ I.image Q, mergedProbability I Q p q = 1 := by
  unfold mergedProbability
  rw [Finset.sum_fiberwise_of_maps_to (fun j hj => Finset.mem_image_of_mem Q hj)]
  exact hp

/-- Indexed choices may repeat the same quorum. Adding their probabilities
    creates an actual Routing without changing their normalized mass. -/
def routing_from_indexed (I : Finset κ) (Q : κ → Finset ι) (p : κ → ℝ)
    (family : Finset (Finset ι)) (U F : Finset ι)
    (hfamily : ∀ j ∈ I, Q j ∈ family)
    (hlive : ∀ j ∈ I, Q j ⊆ U \ F)
    (hpos : ∀ j ∈ I, 0 ≤ p j) (hnorm : ∑ j ∈ I, p j = 1) :
    Routing family U F where
  quorums := I.image Q
  subset := by
    intro q hq
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
    exact hfamily j hj
  live := by
    intro q hq
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
    exact hlive j hj
  p := mergedProbability I Q p
  nonnegative := by
    intro q hq
    apply Finset.sum_nonneg
    intro j hj
    exact hpos j (Finset.mem_filter.mp hj).1
  normalized := merged_normalization I Q p hnorm

/-- Merging repeated choices preserves every node's exact inclusion load. -/
theorem merged_incidence (I : Finset κ) (Q : κ → Finset ι) (p : κ → ℝ) (i : ι) :
    incidence (I.image Q) (mergedProbability I Q p) i =
      ∑ j ∈ I, if i ∈ Q j then p j else 0 := by
  unfold incidence mergedProbability
  calc
    (∑ q ∈ I.image Q, if i ∈ q then ∑ j ∈ I.filter (fun j => Q j = q), p j else 0) =
        ∑ q ∈ I.image Q, ∑ j ∈ I.filter (fun j => Q j = q),
          if i ∈ Q j then p j else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hi : i ∈ q
      · rw [ite_eq_left hi]
        apply Finset.sum_congr rfl
        intro j hj
        rw [(Finset.mem_filter.mp hj).2, ite_eq_left hi]
      · rw [ite_eq_right hi]
        symm
        apply Finset.sum_eq_zero
        intro j hj
        rw [(Finset.mem_filter.mp hj).2, ite_eq_right hi]
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun j hj => Finset.mem_image_of_mem Q hj) _

#print axioms routing_from_indexed
#print axioms merged_incidence
end
end QuorumAudit
