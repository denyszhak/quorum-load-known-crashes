import BaseCertificates

namespace QuorumAudit

def compressArc (x : Nat) : Nat := if x < 15 then x else 15 + x % 3

/-- Any arc is its compressed arc plus a whole number of three-node blocks. -/
theorem compress_properties (x : Nat) :
    compressArc x ≤ 17 ∧ compressArc x ≤ x ∧
    compressArc x % 3 = x % 3 ∧
    (15 ≤ x → 15 ≤ compressArc x) ∧
    ∃ t : Nat, x = compressArc x + 3 * t := by
  have h := Nat.mod_add_div x 3
  have hmod := Nat.mod_lt x (by decide : 0 < 3)
  unfold compressArc
  split
  · refine ⟨by omega, by omega, rfl, by omega, 0, by omega⟩
  · refine ⟨by omega, by omega, by omega, by omega, x / 3 - 5, by omega⟩

/-- Sorting the compressed pair lands in the finite table for every size
    and every pair of surviving arc lengths. -/
theorem compressed_pair_covered (A B k : Nat) (hk : 3 ≤ k) (hs : A + B = 3 * k) :
    (min (compressArc A) (compressArc B), max (compressArc A) (compressArc B))
      ∈ expectedPairs := by
  obtain ⟨ha17, ha, hamod, halong, ta, hat⟩ := compress_properties A
  obtain ⟨hb17, hb, hbmod, hblong, tb, hbt⟩ := compress_properties B
  have hsum : 9 ≤ compressArc A + compressArc B := by
    by_cases hA : A < 15
    · by_cases hB : B < 15
      · simp only [compressArc, ite_eq_left hA, ite_eq_left hB]
        omega
      · have := hblong (by omega)
        omega
    · have := halong (by omega)
      omega
  have hmod : (compressArc A + compressArc B) % 3 = 0 := by omega
  have hsort : min (compressArc A) (compressArc B) + max (compressArc A) (compressArc B) =
      compressArc A + compressArc B := by omega
  simp only [expectedPairs, List.mem_flatMap, List.mem_range, List.mem_map,
    List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨min (compressArc A) (compressArc B), by omega,
    max (compressArc A) (compressArc B), ?_, rfl⟩
  exact ⟨by omega, ⟨by omega, by omega⟩, by omega⟩

#print axioms compress_properties
#print axioms compressed_pair_covered

/-- Every compressed pair selects an actually kernel-checked base witness. -/
theorem checked_base_for_every_pair (A B k : Nat) (hk : 3 ≤ k) (hs : A + B = 3 * k) :
    ∃ g ∈ bases,
      g.a = min (compressArc A) (compressArc B) ∧
      g.b = max (compressArc A) (compressArc B) ∧ checkGadget g = true := by
  have hpair := compressed_pair_covered A B k hk hs
  rw [← base_table_complete] at hpair
  obtain ⟨g, hg, heq⟩ := List.mem_map.mp hpair
  have hvalid : checkGadget g = true := (List.all_eq_true.mp all_bases_checked) g hg
  exact ⟨g, hg, congrArg Prod.fst heq, congrArg Prod.snd heq, hvalid⟩

#print axioms checked_base_for_every_pair
end QuorumAudit
