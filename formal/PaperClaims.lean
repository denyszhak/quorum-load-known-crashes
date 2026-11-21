import PaperModel
import TwoCrashOptimal
import GeneralFOptimal
import GeneralCrashLower
import MixedCircleAssembly

set_option maxHeartbeats 1500000

namespace QuorumAudit.Paper
noncomputable section
open Finset Circle
open scoped BigOperators

theorem cyclic_model_is_paper (n : ℕ) (a L : ℝ) :
    TwoCrash.LoadFeasible n a L ↔ Feasible (range n) 2 a L :=
  (feasible_iff (range n) 2 a L).symm

theorem cyclic_exact_in_paper_model (k : ℕ) (hk : 3 ≤ k) (a L : ℝ)
    (ha : 0 ≤ a) (hend : a ≤ 3 / ((k : ℝ) * k + k + 1)) :
    Feasible (range (3 * k + 2)) 2 a L ↔
      (3 + ((k : ℝ) - 1) * a) / (3 * (k : ℝ)) ≤ L := by
  rw [← cyclic_model_is_paper]
  exact TwoCrash.two_crash_exact_optimum k hk a L ha hend

theorem cyclic_fixed_design (k : ℕ) (hk : 3 ≤ k) (a : ℝ)
    (ha : 0 ≤ a) (hend : a ≤ 3 / ((k : ℝ) * k + k + 1))
    (F : Finset ℕ) (hF : F ⊆ range (3 * k + 2)) (hc : F.card ≤ 2) :
    RoutesAt (TwoCrash.reads (3 * k + 2) k) (TwoCrash.writes (3 * k + 2))
      (range (3 * k + 2)) F a ((3 + ((k : ℝ) - 1) * a) / (3 * (k : ℝ))) := by
  apply (routes_iff _ _ _ _ _ _).mpr
  obtain ⟨read, write, h⟩ := TwoCrash.fixed_construction_attains k hk a ha hend F hF hc
  exact ⟨read, write, fun i hi => h i (mem_sdiff.mp hi).1⟩

theorem general_model_is_paper (n f : ℕ) [NeZero n] (a L : ℝ) :
    GeneralF.LoadFeasible f n a L ↔ Feasible (univ : Finset (ZMod n)) f a L := by
  rw [feasible_iff]
  constructor
  · rintro ⟨R, W, hs, hroutes⟩
    exact ⟨R, W, fun _ _ => subset_univ _, fun _ _ => subset_univ _, hs,
      fun F _ hc => hroutes F hc⟩
  · rintro ⟨R, W, _, _, hs, hroutes⟩
    exact ⟨R, W, hs, fun F hc => hroutes F (subset_univ _) hc⟩

theorem arbitrary_f_exact_in_paper_model (n f k : ℕ) [NeZero n]
    (hf : 1 ≤ f) (hk : f * f + 1 ≤ k) (hn : n = (f + 1) * k)
    (a L : ℝ) (ha : 0 ≤ a) (hend : a ≤ 1 / (((k : ℝ) - 1) * (k + f) + 1)) :
    Feasible (univ : Finset (ZMod n)) f a L ↔
      ((f : ℝ) + 1 + ((k : ℝ) - 1) * a) / ((n : ℝ) - f) ≤ L := by
  rw [← general_model_is_paper]
  have hv : GeneralF.value f k a =
      ((f : ℝ) + 1 + ((k : ℝ) - 1) * a) / ((n : ℝ) - f) := by
    unfold GeneralF.value
    rw [hn]
    push_cast
    rfl
  rw [← hv]
  exact GeneralF.arbitrary_f_exact_optimum f k hf hk n hn a L ha hend

theorem arbitrary_f_fixed_design (n f k : ℕ) [NeZero n]
    (hf : 1 ≤ f) (hk : f * f + 1 ≤ k) (hn : n = (f + 1) * k)
    (a : ℝ) (ha : 0 ≤ a) (hend : a ≤ 1 / (((k : ℝ) - 1) * (k + f) + 1))
    (F : Finset (ZMod n)) (hc : F.card ≤ f) :
    RoutesAt (reads n (k + f)) (rankedWrites n (k + f) (f + 1)) univ F a
      (((f : ℝ) + 1 + ((k : ℝ) - 1) * a) / ((n : ℝ) - f)) := by
  apply (routes_iff _ _ _ _ _ _).mpr
  obtain ⟨read, write, h⟩ := GeneralF.interval_construction_attains f k hf hk n hn F hc a ha hend
  refine ⟨read, write, ?_⟩
  intro i hi
  have hv := h i hi
  unfold GeneralF.value at hv
  simpa only [hn, Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hv

theorem interval_reads_membership (n r : ℕ) [NeZero n] (q : Finset (ZMod n)) :
    q ∈ reads n r ↔ ∃ s : ZMod n, q = (range r).image (fun j : ℕ => s + (j : ZMod n)) := by
  simp only [reads, arc, mem_image, mem_univ, true_and]
  constructor <;> rintro ⟨s, hs⟩ <;> exact ⟨s, hs.symm⟩

theorem mixed_writes_membership (n r : ℕ) [NeZero n] (w : Finset (ZMod n)) :
    w ∈ MixedCircle.mixedWrites n r ↔
      (w.card = r ∨ w.card = r + 1) ∧
      ∀ s : ZMod n, ((range r).image (fun j : ℕ => s + (j : ZMod n)) ∩ w).Nonempty := by
  have hbase : w ∈ Circle.writes n r ↔
      ∀ s : ZMod n, ((range r).image (fun j : ℕ => s + (j : ZMod n)) ∩ w).Nonempty := by
    simp [Circle.writes, arc]
  simp only [MixedCircle.mixedWrites, mem_union, rankedWrites, mem_filter, hbase]
  tauto

theorem balanced_fixed_reads_exact_in_paper_model (n r : ℕ) [NeZero n]
    (hr : 5 ≤ r) (hn : n + 1 = r * r) (L : ℝ) :
    FixedReadsFeasible (univ : Finset (ZMod n)) 2 (reads n r) (1 / 2) L ↔
      (2 * (r : ℝ) - 1) / (2 * ((r : ℝ) - 2) * ((r : ℝ) + 1)) ≤ L := by
  have hv : MixedCircle.cap r / 2 =
      (2 * (r : ℝ) - 1) / (2 * ((r : ℝ) - 2) * ((r : ℝ) + 1)) := by
    unfold MixedCircle.cap MixedCircle.den
    rw [div_div]
    congr 1
    ring
  rw [← hv]
  constructor
  · rintro ⟨W, had, hroutes⟩
    apply MixedCircle.balanced_fixed_read_lower r hr hn W L had.2.2.2.2.1
    intro F hc
    exact (routes_iff _ _ _ _ _ _).mp (hroutes F (subset_univ _) hc)
  · intro hL
    have hroutes : ∀ F ⊆ (univ : Finset (ZMod n)), F.card ≤ 2 →
        ∃ read : Routing (reads n r) univ F,
        ∃ write : Routing (MixedCircle.mixedWrites n r) univ F,
          ∀ i ∈ univ \ F, combined read write (1 / 2) i ≤ L := by
      intro F _ hc
      obtain ⟨read, write, h⟩ := MixedCircle.balanced_interval_upper r hr hn F hc
      exact ⟨read, write, fun i _ => (h i).trans hL⟩
    exact ⟨MixedCircle.mixedWrites n r,
      admissible_of_routes _ _ _ 2 (1 / 2) L (fun _ _ => subset_univ _)
        (fun _ _ => subset_univ _) (MixedCircle.mixed_safe r) hroutes,
      fun F hF hc => (routes_iff _ _ _ _ _ _).mpr (hroutes F hF hc)⟩

theorem weighted_sampling_in_paper_model (n q h ρ : ℕ) [NeZero n]
    (hq : 1 ≤ q) (hh : 1 ≤ h) (hρ : 1 ≤ ρ ∧ ρ ≤ n)
    (weights : ZMod n → ℕ) (htotal : ∑ i : ZMod n, weights i = q * h)
    (hw : ∀ i, weights i ≤ h) (hwindow : ∀ s, h ≤ ∑ i ∈ arc ρ s, weights i) :
    ∃ p : Finset (ZMod n) → ℝ,
      Distribution (rankedWrites n ρ q) univ ∅ p ∧
      ∀ i, contact (rankedWrites n ρ q) univ ∅ p i = (weights i : ℝ) / h := by
  letI : NeZero h := ⟨by omega⟩
  obtain ⟨route, hm⟩ := exact_ranked_sampled_routing (h := h) weights ∅ ρ q hρ.2
    htotal hw (by simp) hwindow
  refine ⟨extendProbability route, extended_distribution route, ?_⟩
  intro i
  rw [extended_contact]
  exact hm i

theorem universal_lower_in_paper_model {ι : Type*} [DecidableEq ι]
    (f ρ : ℕ) (hf : 1 ≤ f) (V : Finset ι) (hV : 2 * f + 1 ≤ V.card)
    (hρ : f + 2 ≤ ρ ∧ ρ ≤ V.card) (R W : Finset (Finset ι))
    (had : Admissible R W V f) (a L : ℝ) (ha : 0 ≤ a ∧ a ≤ 1)
    (hroutes : ∀ F ⊆ V, F.card ≤ f → RoutesAt R W V F a L) :
    min ((1 - a) / ((ρ : ℝ) - 1 - f))
      (((ρ : ℝ) * a + ((f : ℝ) + 1) * (1 - a)) / ((V.card : ℝ) - f)) ≤ L := by
  have hroute : ∀ F ⊆ V, F.card ≤ f →
      ∃ read : Routing R V F, ∃ write : Routing W V F,
        ∀ i ∈ V \ F, combined read write a i ≤ L := by
    intro F hF hc
    exact (routes_iff _ _ _ _ _ _).mp (hroutes F hF hc)
  have hRav : ∀ F ⊆ V, F.card ≤ f → ∃ r ∈ R, Disjoint r F := by
    intro F hF hc
    obtain ⟨read, _, _⟩ := hroute F hF hc
    exact GeneralF.routing_has_live_quorum read
  have hWav : ∀ F ⊆ V, F.card ≤ f → ∃ w ∈ W, Disjoint w F := by
    intro F hF hc
    obtain ⟨_, write, _⟩ := hroute F hF hc
    exact GeneralF.routing_has_live_quorum write
  let rr := fun F (hF : F ⊆ V) (hc : F.card = f) => (hroute F hF hc.le).choose
  let wr := fun F (hF : F ⊆ V) (hc : F.card = f) => (hroute F hF hc.le).choose_spec.choose
  have h := GeneralCrash.universal_dichotomy f ρ hf hρ.1 V hV R W
    had.1 had.2.1 had.2.2.2.2.1 hRav hWav rr wr a L ha.1 ha.2 (by
      intro F hF hc i hi
      exact (hroute F hF hc.le).choose_spec.choose_spec i hi)
  exact h.elim (fun h => (min_le_left _ _).trans h) (fun h => (min_le_right _ _).trans h)

theorem all_n_lower_in_paper_model {ι : Type*} [DecidableEq ι]
    (k r : ℕ) (hk : 3 ≤ k) (hr : r ≤ 2) (V : Finset ι) (hV : V.card = 3 * k + r)
    (R W : Finset (Finset ι)) (had : Admissible R W V 2) (a L : ℝ)
    (ha : 0 ≤ a) (hend : a ≤ ((r : ℝ) + 1) / ((k : ℝ) * k + k + r - 1))
    (hroutes : ∀ F ⊆ V, F.card ≤ 2 → RoutesAt R W V F a L) :
    (3 + ((k : ℝ) - 1) * a) / ((V.card : ℝ) - 2) ≤ L := by
  have hroute : ∀ F ⊆ V, F.card ≤ 2 →
      ∃ read : Routing R V F, ∃ write : Routing W V F,
        ∀ i ∈ V \ F, combined read write a i ≤ L := by
    intro F hF hc
    exact (routes_iff _ _ _ _ _ _).mp (hroutes F hF hc)
  have hRav : ∀ F ⊆ V, F.card ≤ 2 → ∃ r ∈ R, Disjoint r F := by
    intro F hF hc
    obtain ⟨read, _, _⟩ := hroute F hF hc
    exact GeneralF.routing_has_live_quorum read
  have hWav : ∀ F ⊆ V, F.card ≤ 2 → ∃ w ∈ W, Disjoint w F := by
    intro F hF hc
    obtain ⟨_, write, _⟩ := hroute F hF hc
    exact GeneralF.routing_has_live_quorum write
  let rr := fun F (hF : F ⊆ V) (hc : F.card = 2) => (hroute F hF hc.le).choose
  let wr := fun F (hF : F ⊆ V) (hc : F.card = 2) => (hroute F hF hc.le).choose_spec.choose
  have h := GeneralCrash.universal_two_crash_all_n k r hk hr V hV R W
    had.1 had.2.1 had.2.2.2.2.1 hRav hWav rr wr a L ha hend (by
      intro F hF hc i hi
      exact (hroute F hF hc.le).choose_spec.choose_spec i hi)
  simpa only [GeneralCrash.twoCrashValue, hV, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using h

#check cyclic_exact_in_paper_model
#check arbitrary_f_exact_in_paper_model
#check balanced_fixed_reads_exact_in_paper_model
#print axioms cyclic_exact_in_paper_model
#print axioms cyclic_fixed_design
#print axioms arbitrary_f_exact_in_paper_model
#print axioms arbitrary_f_fixed_design
#print axioms interval_reads_membership
#print axioms mixed_writes_membership
#print axioms balanced_fixed_reads_exact_in_paper_model
#print axioms weighted_sampling_in_paper_model
#print axioms universal_lower_in_paper_model
#print axioms all_n_lower_in_paper_model
end
end QuorumAudit.Paper
