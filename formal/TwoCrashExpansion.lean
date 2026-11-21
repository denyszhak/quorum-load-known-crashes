import InsertionComposition
import TwoCrashWitness

namespace QuorumAudit.TwoCrash
open Finset
noncomputable section

def indicator (b : Bool) : ℝ := if b then 1 else 0
def readCountReal (r : Nat → ℤ → Bool) (i : ℤ) : ℝ :=
  ∑ j ∈ range 3, indicator (r j i)
def cycleMass (n : Nat) (w : ℤ → ℝ) : ℝ := ∑ i ∈ range n, w i
def flowTotal (n : Nat) (w₁ w₂ : ℤ → ℝ) : ℝ := cycleMass n w₁ + cycleMass n w₂

/-- Periodic functions with all the finite witness obligations stated explicitly. -/
structure CycleWitness (n k d : Nat) where
  read : Nat → ℤ → Bool
  u₁ : ℤ → ℝ
  u₂ : ℤ → ℝ
  c₁ : ℤ → ℝ
  c₂ : ℤ → ℝ
  size : n = 3*k+2
  rank : 3 ≤ k
  failure_pos : 0 < d
  failure_lt : d < n
  read_period : ∀ j i, read j (i+n) = read j i
  u₁_period : ∀ i, u₁ (i+n) = u₁ i
  u₂_period : ∀ i, u₂ (i+n) = u₂ i
  c₁_period : ∀ i, c₁ (i+n) = c₁ i
  c₂_period : ∀ i, c₂ (i+n) = c₂ i
  u₁_nonneg : ∀ i, 0 ≤ u₁ i
  u₂_nonneg : ∀ i, 0 ≤ u₂ i
  c₁_nonneg : ∀ i, 0 ≤ c₁ i
  c₂_nonneg : ∀ i, 0 ≤ c₂ i
  read_mass : ∀ j ∈ range 3, cycleMass n (fun i => indicator (read j i)) = k+2
  read_dead : ∀ j ∈ range 3, read j 0 = false ∧ read j d = false
  read_hit : ∀ j ∈ range 3, ∀ i e : ℤ, 0 ≤ i → i < n →
    (e=1 ∨ e=2) → read j i = true ∨ read j (i+e) = true ∨ read j (i+2*e) = true
  u_degree : ∀ i : ℤ, 0 ≤ i → i < n →
    localDegree u₁ u₂ i = if i=0 ∨ i=d then 0 else 1
  c_degree : ∀ i : ℤ, 0 ≤ i → i < n →
    localDegree c₁ c₂ i = if i=0 ∨ i=d then 0 else k+2-readCountReal read i
  u_mass : flowTotal n u₁ u₂ = k
  c_mass : flowTotal n c₁ c₂ = (k-1:ℝ)*(k+2)

structure Cut {n k d : Nat} (w : CycleWitness n k d) (p : Nat) : Prop where
  left : 5 ≤ p
  right : p+7 ≤ n
  away : p+3 ≤ d ∨ d < p
  read_period : ∀ j ∈ range 3, ∀ i : ℤ, p-4 ≤ i → i ≤ p+3 →
    w.read j i = w.read j (p+(i-p)%3)
  read_color : ∀ j ∈ range 3,
    indicator (w.read j p)+indicator (w.read j (p+1))+indicator (w.read j (p+2))=1
  count_one : ∀ i : ℤ, p ≤ i → i ≤ p+2 → readCountReal w.read i=1
  u₁_period : ∀ i : ℤ, p-4 ≤ i → i < p → w.u₁ i=w.u₁ (i+3)
  u₂_period : ∀ i : ℤ, p-4 ≤ i → i < p → w.u₂ i=w.u₂ (i+3)
  c₁_period : ∀ i : ℤ, p-4 ≤ i → i < p → w.c₁ i=w.c₁ (i+3)
  c₂_period : ∀ i : ℤ, p-4 ≤ i → i < p → w.c₂ i=w.c₂ (i+3)
  u_residue : residueTotal w.u₁ w.u₂ p=1
  c_residue : residueTotal w.c₁ w.c₂ p=k+1

def shiftedFailure (p t d : Nat) : Nat := if d < p then d else d+3*t

theorem lift_mass {α : Type*} (f : α → ℝ) (w : ℤ → α) (n p t : Nat)
    (hp : p ≤ n) :
    cycleMass (n+3*t) (fun i => f (cyclicLift n p t w i)) =
      cycleMass n (fun i => f (w i)) +
        t*(f (w p)+f (w (p+1))+f (w (p+2))) := by
  unfold cycleMass
  have heq : ∀ i ∈ range (n+3*t),
      f (cyclicLift n p t w i) = f (w (spliceNat p t i)) := by
    intro i hi
    unfold cyclicLift
    rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast mem_range.mp hi)]
    rw [spliceNat_cast]
  rw [sum_congr rfl heq]
  simpa only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using
    splice_mass (fun i => f (w i)) n p t hp

theorem lift_flow_total (w₁ w₂ : ℤ → ℝ) (n p t : Nat) (hp : p ≤ n) :
    flowTotal (n+3*t) (cyclicLift n p t w₁) (cyclicLift n p t w₂) =
      flowTotal n w₁ w₂ + t*residueTotal w₁ w₂ p := by
  unfold flowTotal
  have h₁ := lift_mass id w₁ n p t hp
  have h₂ := lift_mass id w₂ n p t hp
  simp only [id_eq] at h₁ h₂
  rw [h₁, h₂]
  unfold residueTotal
  ring

theorem splice_failure (n p t d : Nat) (hp : 5 ≤ p) (_hp2 : p+7 ≤ n)
    (hd : 0 < d) (haway : p+3 ≤ d ∨ d < p) (i : ℤ)
    (hi : 0 ≤ i) (_hi2 : i < (n:ℤ)+3*t) :
    (spliceIndex p t i=0 ∨ spliceIndex p t i=d) ↔
      (i=0 ∨ i=(shiftedFailure p t d:Nat)) := by
  unfold shiftedFailure spliceIndex
  split_ifs <;> rcases haway with haway | haway <;> omega

theorem lift_count (r : Nat → ℤ → Bool) (n p t i : ℤ) :
    readCountReal (fun j => cyclicLift n p t (r j)) i =
      readCountReal r (spliceIndex p t (i%(n+3*t))) := rfl

def expandedRead {n k d : Nat} (w : CycleWitness n k d) (p t : Nat) : Nat → ℤ → Bool :=
  fun j => cyclicLift n p t (w.read j)
def expandedU₁ {n k d : Nat} (w : CycleWitness n k d) (p t : Nat) : ℤ → ℝ :=
  cyclicLift n p t w.u₁
def expandedU₂ {n k d : Nat} (w : CycleWitness n k d) (p t : Nat) : ℤ → ℝ :=
  cyclicLift n p t w.u₂
def expandedC₁ {n k d : Nat} (w : CycleWitness n k d) (p t : Nat) : ℤ → ℝ :=
  fun i => cyclicLift n p t w.c₁ i+t*cyclicLift n p t w.u₁ i
def expandedC₂ {n k d : Nat} (w : CycleWitness n k d) (p t : Nat) : ℤ → ℝ :=
  fun i => cyclicLift n p t w.c₂ i+t*cyclicLift n p t w.u₂ i

theorem flowTotal_add_scaled (c₁ c₂ u₁ u₂ : ℤ → ℝ) (n : Nat) (t : ℝ) :
    flowTotal n (fun i => c₁ i+t*u₁ i) (fun i => c₂ i+t*u₂ i) =
      flowTotal n c₁ c₂+t*flowTotal n u₁ u₂ := by
  simp only [flowTotal, cycleMass, sum_add_distrib, ← mul_sum]
  ring

theorem expanded_u_degree {n k d : Nat} (w : CycleWitness n k d)
    (p t : Nat) (h : Cut w p) (i : ℤ) (hi : 0 ≤ i) (hi2 : i < (n:ℤ)+3*t) :
    localDegree (expandedU₁ w p t) (expandedU₂ w p t) i =
      if i=0 ∨ i=(shiftedFailure p t d:Nat) then 0 else 1 := by
  have hn : (11:ℤ) ≤ n := by have := w.size; have := w.rank; omega
  have hp : (5:ℤ) ≤ p := by exact_mod_cast h.left
  have hp2 : (p:ℤ)+7 ≤ n := by exact_mod_cast h.right
  rw [expandedU₁, expandedU₂, cyclic_degree_insertion w.u₁ w.u₂ n p t i
    hn hp hp2 (by omega) hi hi2 w.u₁_period w.u₂_period h.u₁_period h.u₂_period]
  have hb := splice_bounds n p t i (by omega) (by omega) (by omega) hi hi2
  have hf := splice_failure n p t d h.left h.right w.failure_pos h.away i hi hi2
  by_cases hold : i < p ∨ (p:ℤ)+3*t ≤ i
  · rw [ite_eq_left hold, w.u_degree _ hb.1 hb.2]
    simp only [hf]
  · have hnot : ¬(i=0 ∨ i=(shiftedFailure p t d:Nat)) := by
      unfold shiftedFailure
      split_ifs <;> push_cast <;> rcases h.away with ha | ha <;> omega
    rw [ite_eq_right hold, ite_eq_right hnot]
    exact h.u_residue

theorem expanded_c_degree {n k d : Nat} (w : CycleWitness n k d)
    (p t : Nat) (h : Cut w p) (i : ℤ) (hi : 0 ≤ i) (hi2 : i < (n:ℤ)+3*t) :
    localDegree (expandedC₁ w p t) (expandedC₂ w p t) i =
      if i=0 ∨ i=(shiftedFailure p t d:Nat) then 0
      else (k+t:Nat)+2-readCountReal (expandedRead w p t) i := by
  have hn : (11:ℤ) ≤ n := by have := w.size; have := w.rank; omega
  have hp : (5:ℤ) ≤ p := by exact_mod_cast h.left
  have hp2 : (p:ℤ)+7 ≤ n := by exact_mod_cast h.right
  have hb := splice_bounds n p t i (by omega) (by omega) (by omega) hi hi2
  have hf := splice_failure n p t d h.left h.right w.failure_pos h.away i hi hi2
  have hcount : readCountReal (expandedRead w p t) i =
      readCountReal w.read (spliceIndex p t i) := by
    unfold expandedRead
    rw [lift_count, Int.emod_eq_of_lt hi hi2]
  have hu := expanded_u_degree w p t h i hi hi2
  unfold expandedC₁ expandedC₂
  rw [localDegree_add_scaled, cyclic_degree_insertion w.c₁ w.c₂ n p t i
    hn hp hp2 (by omega) hi hi2 w.c₁_period w.c₂_period h.c₁_period h.c₂_period]
  change _ + (t:ℝ)*localDegree (expandedU₁ w p t) (expandedU₂ w p t) i = _
  rw [hu]
  by_cases hold : i < p ∨ (p:ℤ)+3*t ≤ i
  · rw [ite_eq_left hold, w.c_degree _ hb.1 hb.2, hcount]
    simp only [hf]
    split_ifs <;> push_cast <;> ring
  · have hnot : ¬(i=0 ∨ i=(shiftedFailure p t d:Nat)) := by
      unfold shiftedFailure
      split_ifs <;> push_cast <;> rcases h.away with ha | ha <;> omega
    rw [ite_eq_right hold]
    simp only [hnot]
    change residueTotal w.c₁ w.c₂ p + (t:ℝ)*1 = _
    rw [h.c_residue, hcount]
    have hsp : spliceIndex p t i = (p:ℤ)+(i-p)%3 := by
      unfold spliceIndex
      split_ifs <;> omega
    rw [hsp, h.count_one _ (by omega) (by omega)]
    push_cast
    ring

/-- One insertion preserves a complete witness, including read sizes and both
    total flow masses. The number of inserted blocks is arbitrary. -/
def expand {n k d : Nat} (w : CycleWitness n k d) (p t : Nat) (h : Cut w p) :
    CycleWitness (n+3*t) (k+t) (shiftedFailure p t d) where
  read := expandedRead w p t
  u₁ := expandedU₁ w p t
  u₂ := expandedU₂ w p t
  c₁ := expandedC₁ w p t
  c₂ := expandedC₂ w p t
  size := by have := w.size; omega
  rank := by have := w.rank; omega
  failure_pos := by unfold shiftedFailure; split_ifs <;> have := w.failure_pos <;> omega
  failure_lt := by
    unfold shiftedFailure
    split_ifs <;> have := w.failure_lt <;> omega
  read_period := by
    intro j i
    simpa only [expandedRead, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      cyclicLift_periodic (w.read j) n p t i
  u₁_period := by
    intro i
    simpa only [expandedU₁, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      cyclicLift_periodic w.u₁ n p t i
  u₂_period := by
    intro i
    simpa only [expandedU₂, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      cyclicLift_periodic w.u₂ n p t i
  c₁_period := by
    intro i
    simp only [expandedC₁, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, cyclicLift_periodic]
  c₂_period := by
    intro i
    simp only [expandedC₂, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, cyclicLift_periodic]
  u₁_nonneg := by intro i; exact w.u₁_nonneg _
  u₂_nonneg := by intro i; exact w.u₂_nonneg _
  c₁_nonneg := by
    intro i
    exact add_nonneg (w.c₁_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (w.u₁_nonneg _))
  c₂_nonneg := by
    intro i
    exact add_nonneg (w.c₂_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (w.u₂_nonneg _))
  read_mass := by
    intro j hj
    rw [expandedRead, lift_mass indicator (w.read j) n p t (by have := h.right; omega),
      w.read_mass j hj, h.read_color j hj]
    push_cast
    ring
  read_dead := by
    intro j hj
    have h0 : spliceIndex (p:ℤ) t 0=0 := by
      unfold spliceIndex
      exact ite_eq_left (by have := h.left; omega)
    have hd : (if (d:ℤ)<p then (d:ℤ) else d+3*t) = (shiftedFailure p t d:Nat) := by
      unfold shiftedFailure
      split_ifs <;> push_cast <;> omega
    constructor
    · unfold expandedRead cyclicLift
      rw [Int.zero_emod, h0]
      exact (w.read_dead j hj).1
    · have himg0 : (0:ℤ) ≤ if (d:ℤ)<p then (d:ℤ) else d+3*t := by split_ifs <;> omega
      have himglt : (if (d:ℤ)<p then (d:ℤ) else d+3*t) < (n:ℤ)+3*t := by
        have := w.failure_lt
        split_ifs <;> omega
      unfold expandedRead cyclicLift
      rw [← hd, Int.emod_eq_of_lt himg0 himglt, splice_old_image _ _ _ (by omega)]
      exact (w.read_dead j hj).2
  read_hit := by
    intro j hj i e hi hi2 he
    have hn : (11:ℤ) ≤ n := by have := w.size; have := w.rank; omega
    have hc : w.read j p=true ∨ w.read j (p+1)=true ∨ w.read j (p+2)=true := by
      have hcolor := h.read_color j hj
      cases h₀ : w.read j p <;> cases h₁ : w.read j (p+1) <;>
        cases h₂ : w.read j (p+2) <;> simp_all [indicator]
    exact cyclic_read_hits_after_insertion (fun i => w.read j i=true) n p t hn
      (by exact_mod_cast h.left) (by exact_mod_cast h.right) (by omega)
      (fun i => congrArg (fun b => b=true) (w.read_period j i))
      (fun i hi hi2 => congrArg (fun b => b=true) (h.read_period j hj i hi hi2))
      hc (w.read_hit j hj) i e hi (by simpa using hi2) he
  u_degree := by
    intro i hi hi2
    exact expanded_u_degree w p t h i hi (by simpa using hi2)
  c_degree := by
    intro i hi hi2
    exact expanded_c_degree w p t h i hi (by simpa using hi2)
  u_mass := by
    rw [expandedU₁, expandedU₂, lift_flow_total _ _ n p t (by have := h.right; omega),
      w.u_mass, h.u_residue]
    push_cast
    ring
  c_mass := by
    change flowTotal (n+3*t) (fun i => cyclicLift n p t w.c₁ i+(t:ℝ)*cyclicLift n p t w.u₁ i)
      (fun i => cyclicLift n p t w.c₂ i+(t:ℝ)*cyclicLift n p t w.u₂ i) = _
    rw [flowTotal_add_scaled,
      lift_flow_total _ _ n p t (by have := h.right; omega),
      lift_flow_total _ _ n p t (by have := h.right; omega),
      w.c_mass, w.u_mass, h.c_residue, h.u_residue]
    push_cast
    ring

#print axioms expand

end
end QuorumAudit.TwoCrash
