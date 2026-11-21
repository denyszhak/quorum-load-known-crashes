import Arithmetic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace QuorumAudit
noncomputable section
open scoped BigOperators
variable {ι : Type*} [DecidableEq ι]

def incidence (Q : Finset (Finset ι)) (p : Finset ι → ℝ) (i : ι) : ℝ :=
  ∑ q ∈ Q, if i ∈ q then p q else 0

/-- Double counting: node inclusion mass is expected intersection size. -/
theorem sum_incidence (Q : Finset (Finset ι)) (p : Finset ι → ℝ) (S : Finset ι) :
    ∑ i ∈ S, incidence Q p i = ∑ q ∈ Q, (S ∩ q).card * p q := by
  unfold incidence
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter]
  simp

theorem incidence_nonnegative (Q : Finset (Finset ι)) (p : Finset ι → ℝ)
    (hp : ∀ q ∈ Q, 0 ≤ p q) (i : ι) : 0 ≤ incidence Q p i := by
  apply Finset.sum_nonneg
  intro q hq
  split_ifs
  · exact hp q hq
  · rfl

/-- A normalized nonnegative quorum distribution must spend at least r
    total inclusion mass on S when every supported quorum meets S r times. -/
theorem intersection_mass_bound (Q : Finset (Finset ι)) (p : Finset ι → ℝ)
    (S : Finset ι) (r : ℝ) (hp : ∀ q ∈ Q, 0 ≤ p q)
    (hnorm : ∑ q ∈ Q, p q = 1)
    (hcard : ∀ q ∈ Q, r ≤ ((S ∩ q).card : ℝ)) :
    r ≤ ∑ i ∈ S, incidence Q p i := by
  rw [sum_incidence]
  calc
    r = ∑ q ∈ Q, r * p q := by rw [← Finset.mul_sum, hnorm]; ring
    _ ≤ ∑ q ∈ Q, (S ∩ q).card * p q := by
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_right (hcard q hq) (hp q hq)

/-- Availability after f crashes and global cross-intersection force every
    quorum in the opposite family to have more than f nodes. -/
theorem quorum_minimum_rank (R W : Finset (Finset ι)) (U : Finset ι) (f : Nat)
    (hsub : ∀ r ∈ R, r ⊆ U)
    (hsafe : ∀ r ∈ R, ∀ w ∈ W, (r ∩ w).Nonempty)
    (havailable : ∀ F ⊆ U, F.card ≤ f → ∃ w ∈ W, Disjoint w F) :
    ∀ r ∈ R, f + 1 ≤ r.card := by
  intro r hr
  by_contra h
  have hsmall : r.card ≤ f := by omega
  obtain ⟨w, hw, hdisj⟩ := havailable r (hsub r hr) hsmall
  obtain ⟨i, hi⟩ := hsafe r hr w hw
  have hmem := Finset.mem_inter.mp hi
  exact Finset.disjoint_left.mp hdisj hmem.2 hmem.1

/-- After crashing a subset F of a global read r, all available writes
    must still hit the remaining read nodes. -/
theorem surviving_write_hits_read (r w F : Finset ι)
    (hsafe : (r ∩ w).Nonempty) (halive : Disjoint w F) :
    ((r \ F) ∩ w).Nonempty := by
  obtain ⟨i, hi⟩ := hsafe
  obtain ⟨hir, hiw⟩ := Finset.mem_inter.mp hi
  have hnot : i ∉ F := fun h => Finset.disjoint_left.mp halive hiw h
  exact ⟨i, Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨hir, hnot⟩, hiw⟩⟩

/-- These premises describe one legal routing after a failure set. -/
structure Routing (family : Finset (Finset ι)) (U F : Finset ι) where
  quorums : Finset (Finset ι)
  subset : quorums ⊆ family
  live : ∀ q ∈ quorums, q ⊆ U \ F
  p : Finset ι → ℝ
  nonnegative : ∀ q ∈ quorums, 0 ≤ p q
  normalized : ∑ q ∈ quorums, p q = 1

def combined {R W : Finset (Finset ι)} {U F : Finset ι}
    (read : Routing R U F) (write : Routing W U F) (a : ℝ) (i : ι) : ℝ :=
  a * incidence read.quorums read.p i + (1 - a) * incidence write.quorums write.p i

omit [DecidableEq ι] in
/-- Zero or one crash can be padded to two when there are at least two nodes. -/
theorem pad_failures (U F : Finset ι) (hFU : F ⊆ U) (hF : F.card ≤ 2) (hU : 2 ≤ U.card) :
    ∃ G, F ⊆ G ∧ G ⊆ U ∧ G.card = 2 :=
  Finset.exists_subsuperset_card_eq hFU hF hU

/-- A routing that avoids a padded failure set also avoids the actual set. -/
def unpad_routing {R : Finset (Finset ι)} {U F G : Finset ι}
    (route : Routing R U G) (hFG : F ⊆ G) : Routing R U F where
  quorums := route.quorums
  subset := route.subset
  live := by
    intro q hq i hi
    have h := Finset.mem_sdiff.mp (route.live q hq hi)
    exact Finset.mem_sdiff.mpr ⟨h.1, fun hiF => h.2 (hFG hiF)⟩
  p := route.p
  nonnegative := route.nonnegative
  normalized := route.normalized

theorem routing_mass_bound {R : Finset (Finset ι)} {U F : Finset ι}
    (route : Routing R U F) (r : ℝ)
    (hr : ∀ q ∈ R, r ≤ (q.card : ℝ)) :
    r ≤ ∑ i ∈ U \ F, incidence route.quorums route.p i := by
  apply intersection_mass_bound _ _ _ _ route.nonnegative route.normalized
  intro q hq
  have hsub := route.live q hq
  rw [Finset.inter_eq_right.mpr hsub]
  exact hr q (route.subset hq)

/-- The large-read branch, including normalized routing probabilities. -/
theorem survivor_average_branch {R W : Finset (Finset ι)} {U F : Finset ι}
    (read : Routing R U F) (write : Routing W U F) (a r w L : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hr : ∀ q ∈ R, r ≤ (q.card : ℝ)) (hw : ∀ q ∈ W, w ≤ (q.card : ℝ))
    (hL : ∀ i ∈ U \ F, combined read write a i ≤ L) :
    r * a + w * (1 - a) ≤ ((U \ F).card : ℝ) * L := by
  have hR := routing_mass_bound read r hr
  have hW := routing_mass_bound write w hw
  apply average_bound (U \ F) (combined read write a) L _ hL
  unfold combined
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h1 := mul_le_mul_of_nonneg_left hR ha
  have h2 := mul_le_mul_of_nonneg_left hW (by linarith : 0 ≤ 1 - a)
  nlinarith

/-- The small-read branch: available writes spend at least unit mass on
    the surviving nodes of the chosen global read. -/
theorem small_read_mass_branch {R W : Finset (Finset ι)} {U F : Finset ι}
    (read : Routing R U F) (write : Routing W U F) (r : Finset ι) (a L : ℝ)
    (hrU : r ⊆ U) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hsafe : ∀ w ∈ W, (r ∩ w).Nonempty)
    (hL : ∀ i ∈ U \ F, combined read write a i ≤ L) :
    1 - a ≤ ((r \ F).card : ℝ) * L := by
  have hW : (1 : ℝ) ≤ ∑ i ∈ r \ F, incidence write.quorums write.p i := by
    apply intersection_mass_bound _ _ _ _ write.nonnegative write.normalized
    intro w hw
    have hdisj : Disjoint w F := by
      apply Finset.disjoint_left.mpr
      intro i hiw hiF
      exact (Finset.mem_sdiff.mp (write.live w hw hiw)).2 hiF
    have hhit := surviving_write_hits_read r w F (hsafe w (write.subset hw)) hdisj
    have hcard : 1 ≤ ((r \ F) ∩ w).card := Finset.card_pos.mpr hhit
    exact_mod_cast hcard
  have hR : 0 ≤ ∑ i ∈ r \ F, incidence read.quorums read.p i :=
    Finset.sum_nonneg fun i _ => incidence_nonnegative _ _ read.nonnegative i
  apply average_bound (r \ F) (combined read write a) L _
  · intro i hi
    apply hL
    exact Finset.mem_sdiff.mpr ⟨hrU (Finset.mem_sdiff.mp hi).1, (Finset.mem_sdiff.mp hi).2⟩
  · unfold combined
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h1 := mul_nonneg ha hR
    have h2 := mul_le_mul_of_nonneg_left hW (by linarith : 0 ≤ 1 - a)
    nlinarith

#print axioms quorum_minimum_rank
#print axioms sum_incidence
#print axioms intersection_mass_bound
#print axioms survivor_average_branch
#print axioms small_read_mass_branch
#print axioms pad_failures
end
end QuorumAudit
