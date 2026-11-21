import TwoCrashAllSizes
import TwoCrashCycleRouting
import UniversalLowerBound

namespace QuorumAudit.TwoCrash
open Finset
noncomputable section

theorem rotation_nat_add (n : Nat) [NeZero n] (x y : Nat) :
    rotation n (x:ZMod n) y=(y+x)%n := by
  unfold rotation
  rw [← Nat.cast_add,ZMod.val_natCast]

theorem two_failures_routes (k : Nat) (hk : 3≤k) (a : ℝ)
    (ha : 0≤a) (haReg : a≤critical k) (x y : Nat)
    (hx : x<3*k+2) (hy : y<3*k+2) (hxy : x<y) :
    ∃ r : Routing (reads (3*k+2) k) (range (3*k+2)) {x,y},
    ∃ w : Routing (writes (3*k+2)) (range (3*k+2)) {x,y},
      ∀ i∈range (3*k+2),combined r w a i≤target k a := by
  let n := 3*k+2
  let A := y-x-1
  let B := n-(y-x)-1
  have hs : A+B=3*k := by dsimp [A,B,n]; omega
  have hnn : A+B+2=n := by omega
  let _ : NeZero n := ⟨by dsimp [n]; omega⟩
  by_cases ho : compressArc A≤compressArc B
  · obtain ⟨z⟩ := ordered_arcs_witness A B k hk hs ho
    have z' : CycleWitness n k (A+1) := by simpa only [hnn] using z
    obtain ⟨r,w,hl⟩ := cycle_witness_routes z' a ha haReg
    have hf : ({0,A+1}:Finset Nat)⊆range (A+B+2) := by
      intro i hi
      simp only [mem_insert,mem_singleton] at hi
      rcases hi with rfl | rfl <;> apply mem_range.mpr <;> omega
    rw [hnn] at hf
    have heq : ({0,A+1}:Finset Nat).image (rotation n (x:ZMod n))={x,y} := by
      rw [image_insert,image_singleton,rotation_nat_add,rotation_nat_add]
      have hA : A+1+x=y := by dsimp [A]; omega
      rw [zero_add,hA,Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt hy]
    let P := fun F : Finset Nat =>
      ∃ r : Routing (reads n k) (range n) F,
      ∃ w : Routing (writes n) (range n) F,
        ∀i∈range n,combined r w a i≤target k a
    exact Eq.mp (congrArg P heq) (rotation_routes n k (x:ZMod n) {0,A+1} hf r w a (target k a) hl)
  · obtain ⟨z⟩ := ordered_arcs_witness B A k hk (by omega) (by omega)
    have hnn' : B+A+2=n := by omega
    have z' : CycleWitness n k (B+1) := by simpa only [hnn'] using z
    obtain ⟨r,w,hl⟩ := cycle_witness_routes z' a ha haReg
    have hf : ({0,B+1}:Finset Nat)⊆range (B+A+2) := by
      intro i hi
      simp only [mem_insert,mem_singleton] at hi
      rcases hi with rfl | rfl <;> apply mem_range.mpr <;> omega
    rw [hnn'] at hf
    have heq : ({0,B+1}:Finset Nat).image (rotation n (y:ZMod n))={x,y} := by
      rw [image_insert,image_singleton,rotation_nat_add,rotation_nat_add]
      have hB : B+1+y=n+x := by dsimp [B,n]; omega
      rw [zero_add,hB,Nat.mod_eq_of_lt hy,Nat.add_mod_left,Nat.mod_eq_of_lt hx]
      exact pair_comm y x
    let P := fun F : Finset Nat =>
      ∃ r : Routing (reads n k) (range n) F,
      ∃ w : Routing (writes n) (range n) F,
        ∀i∈range n,combined r w a i≤target k a
    exact Eq.mp (congrArg P heq) (rotation_routes n k (y:ZMod n) {0,B+1} hf r w a (target k a) hl)

/-- One fixed pair of quorum families attains the bound for every allowed
    cluster size, workload and set of at most two known failures. -/
theorem fixed_construction_attains (k : Nat) (hk : 3≤k) (a : ℝ)
    (ha : 0≤a) (haReg : a≤critical k) (F : Finset Nat)
    (hF : F⊆range (3*k+2)) (hcard : F.card≤2) :
    ∃ r : Routing (reads (3*k+2) k) (range (3*k+2)) F,
    ∃ w : Routing (writes (3*k+2)) (range (3*k+2)) F,
      ∀ i∈range (3*k+2),combined r w a i≤target k a := by
  obtain ⟨G,hFG,hG,hGc⟩ := pad_failures (range (3*k+2)) F hF hcard (by simp)
  obtain ⟨x,y,hxy,hGeq⟩ := card_eq_two.mp hGc
  have hx : x<3*k+2 := mem_range.mp (hG (by rw [hGeq]; simp))
  have hy : y<3*k+2 := mem_range.mp (hG (by rw [hGeq]; simp))
  have hroutes : ∃ r : Routing (reads (3*k+2) k) (range (3*k+2)) G,
      ∃ w : Routing (writes (3*k+2)) (range (3*k+2)) G,
        ∀ i∈range (3*k+2),combined r w a i≤target k a := by
    rw [hGeq]
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · exact two_failures_routes k hk a ha haReg x y hx hy hlt
    · rw [pair_comm x y]
      exact two_failures_routes k hk a ha haReg y x hy hx hgt
  obtain ⟨r,w,hl⟩ := hroutes
  exact ⟨unpad_routing r hFG,unpad_routing w hFG,hl⟩

#print axioms fixed_construction_attains

theorem routing_has_live_quorum {R : Finset (Finset Nat)} {V F : Finset Nat}
    (r : Routing R V F) : ∃q∈R,Disjoint q F := by
  rcases eq_empty_or_nonempty r.quorums with he | ⟨q,hq⟩
  · have hm := r.normalized
    simp only [he,sum_empty] at hm
    norm_num at hm
  · refine ⟨q,r.subset hq,disjoint_left.mpr ?_⟩
    intro i hi hF
    exact (mem_sdiff.mp (r.live q hq hi)).2 hF

/-- Feasibility in the manuscript's model: globally fixed families, cross
    intersection, and normalized failure-dependent routing for both phases. -/
def LoadFeasible (n : Nat) (a L : ℝ) : Prop :=
  ∃ R W : Finset (Finset Nat),
    (∀r∈R,r⊆range n) ∧ (∀w∈W,w⊆range n) ∧
    (∀r∈R,∀w∈W,(r∩w).Nonempty) ∧
    ∀F⊆range n,F.card≤2 →
      ∃r : Routing R (range n) F, ∃w : Routing W (range n) F,
        ∀i∈range n \ F,combined r w a i≤L

/-- Unconditional exact optimum. The reverse implication constructs routing
    for the specified fixed cyclic design, including the endpoint alpha=0. -/
theorem two_crash_exact_optimum (k : Nat) (hk : 3≤k) (a L : ℝ)
    (ha : 0≤a) (haReg : a≤critical k) :
    LoadFeasible (3*k+2) a L ↔ target k a≤L := by
  constructor
  · rintro ⟨R,W,hR,hW,hsafe,hroutes⟩
    let rF := fun F (hF:F⊆range (3*k+2)) (hc:F.card=2) =>
      Classical.choose (hroutes F hF (le_of_eq hc))
    let wF := fun F (hF:F⊆range (3*k+2)) (hc:F.card=2) =>
      Classical.choose (Classical.choose_spec (hroutes F hF (le_of_eq hc)))
    have hRA : ∀ F⊆range (3*k+2), F.card≤2 → ∃r∈R,Disjoint r F := by
      intro F hF hc
      obtain ⟨r,_,_⟩ := hroutes F hF hc
      exact routing_has_live_quorum r
    have hWA : ∀ F⊆range (3*k+2), F.card≤2 → ∃w∈W,Disjoint w F := by
      intro F hF hc
      obtain ⟨_,w,_⟩ := hroutes F hF hc
      exact routing_has_live_quorum w
    apply universal_two_crash_lower_bound k hk (range (3*k+2)) (by simp)
      R W hR hW hsafe hRA hWA rF wF a L ha haReg
    intro F hF hc i hi
    exact Classical.choose_spec (Classical.choose_spec (hroutes F hF (le_of_eq hc))) i hi
  · intro hL
    refine ⟨reads (3*k+2) k,writes (3*k+2),reads_subset _ _,
      writes_subset _ (by omega),read_family_safe _ _,?_⟩
    intro F hF hc
    obtain ⟨r,w,hl⟩ := fixed_construction_attains k hk a ha haReg F hF hc
    exact ⟨r,w,fun i hi => le_trans (hl i (mem_sdiff.mp hi).1) hL⟩

#print axioms two_crash_exact_optimum
end
end QuorumAudit.TwoCrash
