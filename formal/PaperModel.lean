import SemanticBounds

set_option maxHeartbeats 1000000

namespace QuorumAudit.Paper
noncomputable section
open Finset
open scoped BigOperators
variable {ι : Type*} [DecidableEq ι]

def liveQuorums (A : Finset (Finset ι)) (V F : Finset ι) : Finset (Finset ι) :=
  A.filter (fun q => q ⊆ V \ F)

def Distribution (A : Finset (Finset ι)) (V F : Finset ι) (p : Finset ι → ℝ) : Prop :=
  (∀ q ∈ liveQuorums A V F, 0 ≤ p q) ∧
  ∑ q ∈ liveQuorums A V F, p q = 1

def contact (A : Finset (Finset ι)) (V F : Finset ι) (p : Finset ι → ℝ) (i : ι) : ℝ :=
  ∑ q ∈ liveQuorums A V F, if i ∈ q then p q else 0

def RoutesAt (R W : Finset (Finset ι)) (V F : Finset ι) (a L : ℝ) : Prop :=
  ∃ p q : Finset ι → ℝ,
    Distribution R V F p ∧ Distribution W V F q ∧
    ∀ i ∈ V \ F, a * contact R V F p i + (1 - a) * contact W V F q i ≤ L

def Admissible (R W : Finset (Finset ι)) (V : Finset ι) (f : ℕ) : Prop :=
  (∀ r ∈ R, r ⊆ V) ∧ (∀ w ∈ W, w ⊆ V) ∧ R.Nonempty ∧ W.Nonempty ∧
  (∀ r ∈ R, ∀ w ∈ W, (r ∩ w).Nonempty) ∧
  ∀ F ⊆ V, F.card ≤ f →
    (liveQuorums R V F).Nonempty ∧ (liveQuorums W V F).Nonempty

def Feasible (V : Finset ι) (f : ℕ) (a L : ℝ) : Prop :=
  ∃ R W : Finset (Finset ι), Admissible R W V f ∧
    ∀ F ⊆ V, F.card ≤ f → RoutesAt R W V F a L

def FixedReadsFeasible (V : Finset ι) (f : ℕ) (R : Finset (Finset ι)) (a L : ℝ) : Prop :=
  ∃ W : Finset (Finset ι), Admissible R W V f ∧
    ∀ F ⊆ V, F.card ≤ f → RoutesAt R W V F a L

theorem live_membership (A : Finset (Finset ι)) (V F q : Finset ι)
    (hA : ∀ r ∈ A, r ⊆ V) :
    q ∈ liveQuorums A V F ↔ q ∈ A ∧ Disjoint q F := by
  constructor
  · intro h
    obtain ⟨hq, hlive⟩ := mem_filter.mp h
    exact ⟨hq, disjoint_left.mpr (fun i hi hF => (mem_sdiff.mp (hlive hi)).2 hF)⟩
  · rintro ⟨hq, hd⟩
    exact mem_filter.mpr ⟨hq, fun i hi => mem_sdiff.mpr
      ⟨hA q hq hi, fun hF => disjoint_left.mp hd hi hF⟩⟩

def extendProbability {A : Finset (Finset ι)} {V F : Finset ι}
    (route : Routing A V F) (q : Finset ι) : ℝ :=
  if q ∈ route.quorums then route.p q else 0

theorem route_support_live {A : Finset (Finset ι)} {V F : Finset ι}
    (route : Routing A V F) : route.quorums ⊆ liveQuorums A V F := by
  intro q hq
  exact mem_filter.mpr ⟨route.subset hq, route.live q hq⟩

theorem extended_distribution {A : Finset (Finset ι)} {V F : Finset ι}
    (route : Routing A V F) : Distribution A V F (extendProbability route) := by
  constructor
  · intro q _
    unfold extendProbability
    split_ifs with hq
    · exact route.nonnegative q hq
    · rfl
  · calc
      _ = ∑ q ∈ route.quorums, extendProbability route q :=
        (sum_subset (route_support_live route) (by intro q _ hq; simp [extendProbability, hq])).symm
      _ = ∑ q ∈ route.quorums, route.p q := sum_congr rfl (by intro q hq; simp [extendProbability, hq])
      _ = 1 := route.normalized

theorem extended_contact {A : Finset (Finset ι)} {V F : Finset ι}
    (route : Routing A V F) (i : ι) :
    contact A V F (extendProbability route) i = incidence route.quorums route.p i := by
  unfold contact incidence
  calc
    _ = ∑ q ∈ route.quorums, if i ∈ q then extendProbability route q else 0 :=
      (sum_subset (route_support_live route) (by intro q _ hq; simp [extendProbability, hq])).symm
    _ = _ := sum_congr rfl (by intro q hq; simp [extendProbability, hq])

def distributionRoute {A : Finset (Finset ι)} {V F : Finset ι}
    (p : Finset ι → ℝ) (hp : Distribution A V F p) : Routing A V F where
  quorums := liveQuorums A V F
  subset := filter_subset _ _
  live := fun q hq => (mem_filter.mp hq).2
  p := p
  nonnegative := hp.1
  normalized := hp.2

theorem routes_iff (R W : Finset (Finset ι)) (V F : Finset ι) (a L : ℝ) :
    RoutesAt R W V F a L ↔
      ∃ read : Routing R V F, ∃ write : Routing W V F,
        ∀ i ∈ V \ F, combined read write a i ≤ L := by
  constructor
  · rintro ⟨p, q, hp, hq, hload⟩
    exact ⟨distributionRoute p hp, distributionRoute q hq, hload⟩
  · rintro ⟨read, write, hload⟩
    refine ⟨extendProbability read, extendProbability write,
      extended_distribution read, extended_distribution write, ?_⟩
    intro i hi
    rw [extended_contact, extended_contact]
    exact hload i hi

theorem route_nonempty {A : Finset (Finset ι)} {V F : Finset ι} (route : Routing A V F) :
    (liveQuorums A V F).Nonempty := by
  by_contra h
  have he : route.quorums = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro q hq
    exact h ⟨q, route_support_live route hq⟩
  have hn := route.normalized
  simp only [he, sum_empty] at hn
  norm_num at hn

theorem admissible_of_routes (R W : Finset (Finset ι)) (V : Finset ι) (f : ℕ) (a L : ℝ)
    (hR : ∀ r ∈ R, r ⊆ V) (hW : ∀ w ∈ W, w ⊆ V)
    (hsafe : ∀ r ∈ R, ∀ w ∈ W, (r ∩ w).Nonempty)
    (hroutes : ∀ F ⊆ V, F.card ≤ f →
      ∃ read : Routing R V F, ∃ write : Routing W V F,
        ∀ i ∈ V \ F, combined read write a i ≤ L) : Admissible R W V f := by
  have hav : ∀ F ⊆ V, F.card ≤ f →
      (liveQuorums R V F).Nonempty ∧ (liveQuorums W V F).Nonempty := by
    intro F hF hc
    obtain ⟨read, write, _⟩ := hroutes F hF hc
    exact ⟨route_nonempty read, route_nonempty write⟩
  obtain ⟨hR0, hW0⟩ := hav ∅ (empty_subset _) (by simp)
  exact ⟨hR, hW, hR0.mono (filter_subset _ _), hW0.mono (filter_subset _ _), hsafe, hav⟩

theorem feasible_iff (V : Finset ι) (f : ℕ) (a L : ℝ) :
    Feasible V f a L ↔
      ∃ R W : Finset (Finset ι), (∀ r ∈ R, r ⊆ V) ∧ (∀ w ∈ W, w ⊆ V) ∧
        (∀ r ∈ R, ∀ w ∈ W, (r ∩ w).Nonempty) ∧
        ∀ F ⊆ V, F.card ≤ f →
          ∃ read : Routing R V F, ∃ write : Routing W V F,
            ∀ i ∈ V \ F, combined read write a i ≤ L := by
  constructor
  · rintro ⟨R, W, had, hroutes⟩
    exact ⟨R, W, had.1, had.2.1, had.2.2.2.2.1,
      fun F hF hc => (routes_iff R W V F a L).mp (hroutes F hF hc)⟩
  · rintro ⟨R, W, hR, hW, hs, hroutes⟩
    exact ⟨R, W, admissible_of_routes R W V f a L hR hW hs hroutes,
      fun F hF hc => (routes_iff R W V F a L).mpr (hroutes F hF hc)⟩

#print axioms routes_iff
#print axioms feasible_iff
end
end QuorumAudit.Paper
