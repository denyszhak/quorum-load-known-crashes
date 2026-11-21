import FullRangePrice
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Maps.Proper.Basic

/-!
The two optima are attained. The feasible loads form a closed set, so the
infimum used in `optimum` and `proactiveOptimum` is a minimum, as in the
manuscript's definition of `L*`.
-/

set_option maxHeartbeats 2000000

namespace QuorumAudit.Paper
noncomputable section
open Finset Circle Topology
open scoped BigOperators

section Closed
variable {ι : Type*} [DecidableEq ι]

/-- Distributions on a family, extended by zero outside it. -/
def simplexOn (P : Finset (Finset ι)) : Set (Finset ι → ℝ) :=
  {p | (∀ q ∈ P, 0 ≤ p q) ∧ ∑ q ∈ P, p q = 1 ∧ ∀ q, q ∉ P → p q = 0}

theorem simplexOn_compact (P : Finset (Finset ι)) : IsCompact (simplexOn P) := by
  have hbox : IsCompact (Set.pi Set.univ (fun _ : Finset ι => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  apply hbox.of_isClosed_subset
  · have h1 : IsClosed {p : Finset ι → ℝ | ∀ q ∈ P, 0 ≤ p q} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun q => isClosed_iInter fun _ =>
        isClosed_le continuous_const (continuous_apply q)
    have h2 : IsClosed {p : Finset ι → ℝ | ∑ q ∈ P, p q = 1} :=
      isClosed_eq (continuous_finsetSum _ fun q _ => continuous_apply q) continuous_const
    have h3 : IsClosed {p : Finset ι → ℝ | ∀ q, q ∉ P → p q = 0} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun q => isClosed_iInter fun _ =>
        isClosed_eq (continuous_apply q) continuous_const
    exact h1.inter (h2.inter h3)
  · rintro p ⟨hp, hsum, hzero⟩ q _
    by_cases hq : q ∈ P
    · exact ⟨hp q hq, by rw [← hsum]; exact Finset.single_le_sum (fun r hr => hp r hr) hq⟩
    · rw [hzero q hq]
      exact ⟨le_rfl, zero_le_one⟩

def restrictTo (P : Finset (Finset ι)) (p : Finset ι → ℝ) : Finset ι → ℝ :=
  fun q => if q ∈ P then p q else 0

theorem restrictTo_mem {P : Finset (Finset ι)} {p : Finset ι → ℝ}
    (hp : ∀ q ∈ P, 0 ≤ p q) (hs : ∑ q ∈ P, p q = 1) : restrictTo P p ∈ simplexOn P := by
  refine ⟨fun q hq => by simp [restrictTo, hq, hp q hq], ?_, fun q hq => by simp [restrictTo, hq]⟩
  rw [← hs]
  exact Finset.sum_congr rfl (fun q hq => by simp [restrictTo, hq])

theorem incidence_restrictTo (P : Finset (Finset ι)) (p : Finset ι → ℝ) (i : ι) :
    incidence P (restrictTo P p) i = incidence P p i := by
  unfold incidence
  exact Finset.sum_congr rfl (fun q hq => by simp [restrictTo, hq])

/-- For fixed families and a fixed set of servers, the loads attainable by
    some pair of distributions form a closed set. -/
theorem routes_closed (P Q : Finset (Finset ι)) (S : Finset ι) (a : ℝ) :
    IsClosed {L : ℝ | ∃ p q : Finset ι → ℝ,
      (∀ r ∈ P, 0 ≤ p r) ∧ ∑ r ∈ P, p r = 1 ∧ (∀ w ∈ Q, 0 ≤ q w) ∧ ∑ w ∈ Q, q w = 1 ∧
      ∀ i ∈ S, a * incidence P p i + (1 - a) * incidence Q q i ≤ L} := by
  have : CompactSpace (simplexOn P) := isCompact_iff_compactSpace.mp (simplexOn_compact P)
  have : CompactSpace (simplexOn Q) := isCompact_iff_compactSpace.mp (simplexOn_compact Q)
  let A : Set ((simplexOn P × simplexOn Q) × ℝ) :=
    {x | ∀ i ∈ S, a * incidence P (x.1.1 : Finset ι → ℝ) i +
      (1 - a) * incidence Q (x.1.2 : Finset ι → ℝ) i ≤ x.2}
  have hA : IsClosed A := by
    have hcont : ∀ (R : Finset (Finset ι)) (g : (simplexOn P × simplexOn Q) × ℝ → (Finset ι → ℝ)),
        Continuous g → ∀ i : ι, Continuous fun x => incidence R (g x) i := by
      intro R g hg i
      unfold incidence
      refine continuous_finsetSum _ fun r _ => ?_
      by_cases hi : i ∈ r
      · simp only [hi, ite_true]
        exact (continuous_apply r).comp hg
      · simp only [hi, ite_false]
        exact continuous_const
    have hg1 : Continuous fun x : (simplexOn P × simplexOn Q) × ℝ => (x.1.1 : Finset ι → ℝ) :=
      continuous_subtype_val.comp (continuous_fst.comp continuous_fst)
    have hg2 : Continuous fun x : (simplexOn P × simplexOn Q) × ℝ => (x.1.2 : Finset ι → ℝ) :=
      continuous_subtype_val.comp (continuous_snd.comp continuous_fst)
    simp only [A, Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun _ =>
      isClosed_le ((continuous_const.mul (hcont P _ hg1 i)).add
        (continuous_const.mul (hcont Q _ hg2 i))) continuous_snd
  have himg : IsClosed (Prod.snd '' A) := isClosedMap_snd_of_compactSpace A hA
  convert himg using 1
  ext L
  constructor
  · rintro ⟨p, q, hp, hpn, hq, hqn, hload⟩
    refine ⟨((⟨restrictTo P p, restrictTo_mem hp hpn⟩, ⟨restrictTo Q q, restrictTo_mem hq hqn⟩), L),
      ?_, rfl⟩
    intro i hi
    change a * incidence P (restrictTo P p) i + (1 - a) * incidence Q (restrictTo Q q) i ≤ L
    rw [incidence_restrictTo, incidence_restrictTo]
    exact hload i hi
  · rintro ⟨⟨⟨p, q⟩, L'⟩, hx, rfl⟩
    exact ⟨p.1, q.1, p.2.1, p.2.2.1, q.2.1, q.2.2.1, hx⟩

variable [Fintype ι]

theorem feasible_closed (V : Finset ι) (f : ℕ) (a : ℝ) : IsClosed {L : ℝ | Feasible V f a L} := by
  have hset : {L : ℝ | Feasible V f a L} =
      ⋃ (RW : Finset (Finset ι) × Finset (Finset ι)), ⋃ (_ : Admissible RW.1 RW.2 V f),
        ⋂ (F : Finset ι), ⋂ (_ : F ⊆ V), ⋂ (_ : F.card ≤ f),
          {L : ℝ | RoutesAt RW.1 RW.2 V F a L} := by
    ext L
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter]
    constructor
    · rintro ⟨R, W, had, h⟩
      exact ⟨(R, W), had, h⟩
    · rintro ⟨⟨R, W⟩, had, h⟩
      exact ⟨R, W, had, h⟩
  rw [hset]
  refine isClosed_iUnion_of_finite fun RW => isClosed_iUnion_of_finite fun _ =>
    isClosed_iInter fun F => isClosed_iInter fun _ => isClosed_iInter fun _ => ?_
  convert routes_closed (liveQuorums RW.1 V F) (liveQuorums RW.2 V F) (V \ F) a using 1
  ext L
  constructor
  · rintro ⟨p, q, ⟨hp, hpn⟩, ⟨hq, hqn⟩, hload⟩
    exact ⟨p, q, hp, hpn, hq, hqn, hload⟩
  · rintro ⟨p, q, hp, hpn, hq, hqn, hload⟩
    exact ⟨p, q, ⟨hp, hpn⟩, ⟨hq, hqn⟩, hload⟩

theorem proactive_closed (V : Finset ι) (f : ℕ) (a : ℝ) :
    IsClosed {L : ℝ | ProactiveFeasible V f a L} := by
  have hset : {L : ℝ | ProactiveFeasible V f a L} =
      ⋃ (AB : Finset (Finset ι) × Finset (Finset ι)),
        ⋃ (_ : (∀ A ∈ AB.1, A ⊆ V) ∧ (∀ B ∈ AB.2, B ⊆ V) ∧
          ∀ A ∈ AB.1, ∀ B ∈ AB.2, 2 * f + 1 ≤ (A ∩ B).card),
          {L : ℝ | ProactiveRoutes AB.1 AB.2 V a L} := by
    ext L
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨𝒜, ℬ, h1, h2, h3, h⟩
      exact ⟨(𝒜, ℬ), ⟨h1, h2, h3⟩, h⟩
    · rintro ⟨⟨𝒜, ℬ⟩, ⟨h1, h2, h3⟩, h⟩
      exact ⟨𝒜, ℬ, h1, h2, h3, h⟩
  rw [hset]
  exact isClosed_iUnion_of_finite fun AB => isClosed_iUnion_of_finite fun _ =>
    routes_closed AB.1 AB.2 V a

omit [Fintype ι] in
/-- Every contact probability is at most one. -/
theorem incidence_le_one (P : Finset (Finset ι)) (p : Finset ι → ℝ) (hp : ∀ q ∈ P, 0 ≤ p q)
    (hs : ∑ q ∈ P, p q = 1) (i : ι) : incidence P p i ≤ 1 := by
  unfold incidence
  rw [← hs]
  apply Finset.sum_le_sum
  intro q hq
  split_ifs
  · exact le_rfl
  · exact hp q hq

omit [Fintype ι] in
/-- An admissible pair that routes at one read fraction routes, with load
    at most one, at every read fraction. -/
theorem feasible_one {V : Finset ι} {f : ℕ} {a L : ℝ} (h : Feasible V f a L)
    (b : ℝ) (hb : 0 ≤ b) (hb1 : b ≤ 1) : Feasible V f b 1 := by
  obtain ⟨R, W, had, hroutes⟩ := h
  refine ⟨R, W, had, fun F hF hc => ?_⟩
  obtain ⟨p, q, hp, hq, _⟩ := hroutes F hF hc
  refine ⟨p, q, hp, hq, fun i _ => ?_⟩
  have h1 : contact R V F p i ≤ 1 := incidence_le_one _ p hp.1 hp.2 i
  have h2 : contact W V F q i ≤ 1 := incidence_le_one _ q hq.1 hq.2 i
  nlinarith

end Closed

variable {n : ℕ} [NeZero n]

/-- The known-failure optimum is attained (`n ≥ 2f+1`). -/
theorem optimum_attained (f : ℕ) (hn : 2 * f + 1 ≤ n) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    Feasible (univ : Finset (ZMod n)) f a (optimum n f a) := by
  have h0 : Feasible (univ : Finset (ZMod n)) f 0 (((f : ℝ) + 1) / ((n : ℝ) - f)) :=
    (known_endpoint f hn _).mpr le_rfl
  exact (feasible_closed (univ : Finset (ZMod n)) f a).csInf_mem ⟨1, feasible_one h0 a ha ha1⟩
    (feasible_bddBelow f (by omega) a ha ha1)

/-- The feasible loads are exactly those at least `L*`, so `L*` is the
    minimum of the manuscript's definition. -/
theorem feasible_iff_optimum_le (f : ℕ) (hn : 2 * f + 1 ≤ n) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (L : ℝ) : Feasible (univ : Finset (ZMod n)) f a L ↔ optimum n f a ≤ L :=
  ⟨fun h => optimum_le f (by omega) a ha ha1 h,
    fun h => feasible_mono h (optimum_attained f hn a ha ha1)⟩

/-- The proactive optimum is attained (`n ≥ 2f+1`). -/
theorem proactive_attained (f : ℕ) (hn : 2 * f + 1 ≤ n) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    ProactiveFeasible (univ : Finset (ZMod n)) f a (proactiveOptimum n f a) := by
  have hne : ProactiveFeasible (univ : Finset (ZMod n)) f a 1 := by
    refine ⟨{univ}, {univ}, fun _ _ => subset_univ _, fun _ _ => subset_univ _, ?_,
      fun _ => 1, fun _ => 1, fun _ _ => by norm_num, by simp, fun _ _ => by norm_num, by simp, ?_⟩
    · intro A hA B hB
      rw [mem_singleton.mp hA, mem_singleton.mp hB, inter_self, card_zmod_univ]
      exact hn
    · intro i _
      have h1 : incidence ({univ} : Finset (Finset (ZMod n))) (fun _ => (1 : ℝ)) i = 1 := by
        unfold incidence
        rw [Finset.sum_singleton]
        simp
      rw [h1]
      linarith
  exact (proactive_closed (univ : Finset (ZMod n)) f a).csInf_mem ⟨1, hne⟩
    (proactive_bddBelow f a ha ha1)

theorem proactive_iff_optimum_le (f : ℕ) (hn : 2 * f + 1 ≤ n) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (L : ℝ) : ProactiveFeasible (univ : Finset (ZMod n)) f a L ↔ proactiveOptimum n f a ≤ L :=
  ⟨fun h => proactiveOptimum_le f a ha ha1 h,
    fun h => proactive_mono h (proactive_attained f hn a ha ha1)⟩

#print axioms feasible_closed
#print axioms optimum_attained
#print axioms feasible_iff_optimum_le
#print axioms proactive_attained
#print axioms proactive_iff_optimum_le
end
end QuorumAudit.Paper
