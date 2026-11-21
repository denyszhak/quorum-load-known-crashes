import TwoCrashExpansion

namespace QuorumAudit.TwoCrash
open Finset
noncomputable section

theorem residueTotal_add_scaled (c₁ c₂ u₁ u₂ : ℤ → ℝ) (t : ℝ)
    (q : ℤ) :
    residueTotal (fun i => c₁ i+t*u₁ i) (fun i => c₂ i+t*u₂ i) q =
      residueTotal c₁ c₂ q+t*residueTotal u₁ u₂ q := by
  unfold residueTotal
  ring

theorem later_residue {α : Type*} (f : ℤ → α) (n p q t : Nat)
    (hpq : p+12 ≤ q) (hq : q+7 ≤ n) (a : ℤ) (ha : 0 ≤ a) (ha2 : a ≤ 2) :
    cyclicLift n p t f ((q+3*t:Nat)+a) = f ((q:ℤ)+a) := by
  have h := later_cut_signature_preserved f n p q t ((q+3*t:Nat)+a)
    (by exact_mod_cast hpq) (by exact_mod_cast hq) (by omega) (by omega)
    (by push_cast; omega) (by push_cast; omega)
  have he : ((q+3*t:Nat):ℤ)+a-3*t=(q:ℤ)+a := by push_cast; omega
  rw [he] at h
  exact h

/-- A distant second cut remains valid after both the splice and the critical
    flow correction. It can therefore be used by `expand` again. -/
theorem second_cut {n k d : Nat} (w : CycleWitness n k d) (p q t : Nat)
    (hp : Cut w p) (hq : Cut w q) (hpq : p+12 ≤ q) :
    Cut (expand w p t hp) (q+3*t) := by
  have hs (f : ℤ → ℝ) (a : ℤ) (ha : 0 ≤ a) (ha2 : a ≤ 2) :=
    later_residue f n p q t hpq hq.right a ha ha2
  have hr (j : Nat) (a : ℤ) (ha : 0 ≤ a) (ha2 : a ≤ 2) :=
    later_residue (w.read j) n p q t hpq hq.right a ha ha2
  have res (f g : ℤ → ℝ) :
      residueTotal (cyclicLift n p t f) (cyclicLift n p t g) (q+3*t:Nat) =
        residueTotal f g q := by
    unfold residueTotal
    have hf0 := hs f 0 (by omega) (by omega)
    have hg0 := hs g 0 (by omega) (by omega)
    simp only [add_zero] at hf0 hg0
    rw [hf0, hs f 1 (by omega) (by omega), hs f 2 (by omega) (by omega),
      hg0, hs g 1 (by omega) (by omega), hs g 2 (by omega) (by omega)]
  refine ⟨by have := hq.left; omega, by have := hq.right; omega, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold shiftedFailure
    split_ifs <;> rcases hq.away with hd | hd <;> omega
  · intro j hj i hi hi2
    change cyclicLift n p t (w.read j) i =
      cyclicLift n p t (w.read j) ((q+3*t:Nat)+(i-(q+3*t:Nat))%3)
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      later_cut_read_periodicity (w.read j) n p q t
        (by exact_mod_cast hpq) (by exact_mod_cast hq.right) (by omega) (by omega)
        (hq.read_period j hj) i (by simpa using hi) (by simpa using hi2)
  · intro j hj
    change indicator (cyclicLift n p t (w.read j) (q+3*t:Nat)) +
      indicator (cyclicLift n p t (w.read j) ((q+3*t:Nat)+1)) +
      indicator (cyclicLift n p t (w.read j) ((q+3*t:Nat)+2)) = 1
    have hr0 := hr j 0 (by omega) (by omega)
    simp only [add_zero] at hr0
    rw [hr0, hr j 1 (by omega) (by omega), hr j 2 (by omega) (by omega)]
    exact hq.read_color j hj
  · intro i hi hi2
    change readCountReal (expandedRead w p t) i=1
    unfold readCountReal expandedRead
    have he : ∀ j ∈ range 3, cyclicLift n p t (w.read j) i=w.read j (i-3*t) := by
      intro j _
      apply later_cut_signature_preserved (w.read j) n p q t i
        (by exact_mod_cast hpq) (by exact_mod_cast hq.right) (by omega) (by omega)
        (by push_cast at hi; omega) (by push_cast at hi2; omega)
    rw [sum_congr rfl (fun j hj => congrArg indicator (he j hj))]
    exact hq.count_one (i-3*t) (by push_cast at hi; omega) (by push_cast at hi2; omega)
  · simpa only [expand, expandedU₁, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      later_cut_four_equalities w.u₁ n p q t (by exact_mod_cast hpq)
        (by exact_mod_cast hq.right) (by omega) (by omega) hq.u₁_period
  · simpa only [expand, expandedU₂, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      later_cut_four_equalities w.u₂ n p q t (by exact_mod_cast hpq)
        (by exact_mod_cast hq.right) (by omega) (by omega) hq.u₂_period
  · intro i hi hi2
    change cyclicLift n p t w.c₁ i+(t:ℝ)*cyclicLift n p t w.u₁ i = _
    have hc := later_cut_four_equalities w.c₁ n p q t (by exact_mod_cast hpq)
      (by exact_mod_cast hq.right) (by omega) (by omega) hq.c₁_period i
      (by simpa using hi) (by simpa using hi2)
    have hu := later_cut_four_equalities w.u₁ n p q t (by exact_mod_cast hpq)
      (by exact_mod_cast hq.right) (by omega) (by omega) hq.u₁_period i
      (by simpa using hi) (by simpa using hi2)
    rw [hc, hu]
    rfl
  · intro i hi hi2
    change cyclicLift n p t w.c₂ i+(t:ℝ)*cyclicLift n p t w.u₂ i = _
    have hc := later_cut_four_equalities w.c₂ n p q t (by exact_mod_cast hpq)
      (by exact_mod_cast hq.right) (by omega) (by omega) hq.c₂_period i
      (by simpa using hi) (by simpa using hi2)
    have hu := later_cut_four_equalities w.u₂ n p q t (by exact_mod_cast hpq)
      (by exact_mod_cast hq.right) (by omega) (by omega) hq.u₂_period i
      (by simpa using hi) (by simpa using hi2)
    rw [hc, hu]
    rfl
  · change residueTotal (cyclicLift n p t w.u₁) (cyclicLift n p t w.u₂) (q+3*t:Nat)=1
    rw [res, hq.u_residue]
  · change residueTotal (fun i => cyclicLift n p t w.c₁ i+(t:ℝ)*cyclicLift n p t w.u₁ i)
      (fun i => cyclicLift n p t w.c₂ i+(t:ℝ)*cyclicLift n p t w.u₂ i) (q+3*t:Nat)=_
    rw [residueTotal_add_scaled, res, res, hq.c_residue, hq.u_residue]
    push_cast
    ring

#print axioms second_cut
end
end QuorumAudit.TwoCrash
