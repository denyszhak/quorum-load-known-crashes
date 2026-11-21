import TwoCrashExpansion
import TwoCrashSymmetry
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Algebra.BigOperators.Fin

namespace QuorumAudit.TwoCrash
open Finset
noncomputable section

theorem periodic_emod {α : Type*} (f : ℤ → α) (n : ℤ)
    (hf : ∀ i, f (i+n)=f i) (i : ℤ) : f (i%n)=f i := by
  have hp : Function.Periodic f n := hf
  have h := hp.int_mul (i/n) (i%n)
  have he : i%n+(i/n)*n=i := by simpa only [mul_comm] using Int.emod_add_mul_ediv i n
  simpa only [Int.cast_id, he] using h.symm

def circleWrite (n : Nat) [NeZero n] (s : ZMod n) (e : Nat) : Finset Nat :=
  {s.val, (s+e).val, (s+2*e).val}

theorem circleWrite_family (n : Nat) [NeZero n] (s : ZMod n) (e : Nat)
    (he : e=1 ∨ e=2) : circleWrite n s e∈writes n := by
  have hr : e-1<2 := by omega
  have hd : (2*s.val+(e-1))/2=s.val := by omega
  have hm : (2*s.val+(e-1))%2=e-1 := by omega
  have he' : e-1+1=e := by omega
  have hq : circleWrite n s e=writeSet n (2*s.val+(e-1)) := by
    rw [writeSet_explicit, hd, hm, he']
    unfold circleWrite
    have h0 : s.val%n=s.val := Nat.mod_eq_of_lt (ZMod.val_lt s)
    have h1 : (s+e).val=(s.val+e)%n := by
      rw [← ZMod.val_natCast n (s.val+e)]
      simp only [Nat.cast_add, ZMod.natCast_zmod_val]
    have h2 : (s+2*e).val=(s.val+2*e)%n := by
      rw [← ZMod.val_natCast n (s.val+2*e)]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]
    rw [h0, h1, h2]
  rw [hq]
  apply mem_image_of_mem
  exact mem_range.mpr (by have := ZMod.val_lt s; omega)

theorem three_indicator (a b c s : α) [DecidableEq α]
    (hab : a≠b) (hac : a≠c) (hbc : b≠c) (f : α → ℝ) :
    (if s=a ∨ s=b ∨ s=c then f s else 0) =
      (if s=a then f s else 0)+(if s=b then f s else 0)+(if s=c then f s else 0) := by
  by_cases ha : s=a <;> by_cases hb : s=b <;> by_cases hc : s=c <;> simp_all

theorem circleWrite_mem (n : Nat) [NeZero n] (s : ZMod n) (e i : Nat) (hi : i<n) :
    i∈circleWrite n s e ↔
      s=(i:ZMod n) ∨ s=(i:ZMod n)-e ∨ s=(i:ZMod n)-2*e := by
  have eqv (z : ZMod n) : i=z.val ↔ z=(i:ZMod n) := by
    constructor
    · intro h; rw [h]; exact (ZMod.natCast_zmod_val z).symm
    · intro h; rw [h, ZMod.val_natCast_of_lt hi]
  simp only [circleWrite, mem_insert, mem_singleton, eqv]
  constructor
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl ((eq_sub_iff_add_eq).mpr h))
    · exact Or.inr (Or.inr ((eq_sub_iff_add_eq).mpr h))
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl ((eq_sub_iff_add_eq).mp h))
    · exact Or.inr (Or.inr ((eq_sub_iff_add_eq).mp h))

theorem circle_incidence (n : Nat) [NeZero n] (hn : 11≤n) (e i : Nat)
    (he : e=1 ∨ e=2) (hi : i<n) (f : ZMod n → ℝ) :
    (∑ s : ZMod n, if i∈circleWrite n s e then f s else 0) =
      f (i:ZMod n)+f ((i:ZMod n)-e)+f ((i:ZMod n)-2*e) := by
  have en : (e:ZMod n)≠0 := by
    intro hz
    have hv := congrArg ZMod.val hz
    rw [ZMod.val_natCast_of_lt (by omega : e<n)] at hv
    simp only [ZMod.val_zero] at hv
    omega
  have e2n : (2*(e:ZMod n))≠0 := by
    intro hz
    have hv := congrArg ZMod.val hz
    have hc : (2*(e:ZMod n))=((2*e:Nat):ZMod n) := by push_cast; rfl
    rw [hc, ZMod.val_natCast_of_lt (by omega : 2*e<n)] at hv
    simp only [ZMod.val_zero] at hv
    omega
  have hab : (i:ZMod n)≠(i:ZMod n)-e := by
    intro h
    apply en
    exact sub_eq_self.mp h.symm
  have hac : (i:ZMod n)≠(i:ZMod n)-2*e := by
    intro h
    apply e2n
    exact sub_eq_self.mp h.symm
  have hbc : (i:ZMod n)-e≠(i:ZMod n)-2*e := by
    intro h
    apply en
    have hh : (i:ZMod n)-e=((i:ZMod n)-e)-e := by
      calc
        _ = (i:ZMod n)-2*e := h
        _ = _ := by ring
    exact sub_eq_self.mp hh.symm
  simp only [circleWrite_mem n _ e i hi]
  simp_rw [three_indicator _ _ _ _ hab hac hbc f]
  simp [sum_add_distrib]

#print axioms circle_incidence

def circleIndices (n : Nat) [NeZero n] : Finset (ZMod n × Nat) := univ ×ˢ {1,2}
def circleWeight (n : Nat) [NeZero n] (f g : ℤ → ℝ) (j : ZMod n × Nat) : ℝ :=
  if j.2=1 then f j.1.val else g j.1.val

theorem circle_sum (n : Nat) [NeZero n] (f : ℤ → ℝ) :
    (∑ s : ZMod n, f s.val)=cycleMass n f := by
  unfold cycleMass
  apply sum_bij (fun s _ => s.val)
  · intro s _; exact mem_range.mpr (ZMod.val_lt s)
  · intro a _ b _ hab; exact ZMod.val_injective n hab
  · intro i hi
    exact ⟨(i:ZMod n),mem_univ _,ZMod.val_natCast_of_lt (mem_range.mp hi)⟩
  · intro s _; rfl

theorem circle_weight_mass (n : Nat) [NeZero n] (f g : ℤ → ℝ) :
    (∑ j ∈ circleIndices n, circleWeight n f g j)=flowTotal n f g := by
  simp only [circleIndices, sum_product]
  simp only [sum_insert (by decide : (1:Nat)∉({2}:Finset Nat)),sum_singleton,
    circleWeight,show ¬(2:Nat)=1 by decide,
    ite_true,ite_false,sum_add_distrib]
  rw [circle_sum, circle_sum]
  rfl

theorem circle_weight_degree (n : Nat) [NeZero n] (hn : 11≤n)
    (f g : ℤ → ℝ) (hf : ∀ i,f (i+n)=f i) (hg : ∀ i,g (i+n)=g i)
    (i : Nat) (hi : i<n) :
    (∑ j ∈ circleIndices n, if i∈circleWrite n j.1 j.2 then circleWeight n f g j else 0)=
      localDegree f g i := by
  simp only [circleIndices, sum_product]
  simp only [sum_insert (by decide : (1:Nat)∉({2}:Finset Nat)),sum_singleton,
    circleWeight,show ¬(2:Nat)=1 by decide,
    ite_true,ite_false,sum_add_distrib]
  rw [circle_incidence n hn 1 i (by simp) hi,
    circle_incidence n hn 2 i (by simp) hi]
  have wrap (w : ℤ → ℝ) (hw : ∀ i,w (i+n)=w i) (a : ℤ) :
      w ((a:ZMod n).val)=w a := by
    rw [ZMod.val_intCast, periodic_emod w n hw]
  have cv : ((i:ZMod n).val:ℤ)=i := by rw [ZMod.val_natCast_of_lt hi]
  have c₁ : (i:ZMod n)-1=(((i:ℤ)-1:ℤ):ZMod n) := by push_cast; rfl
  have c₃ : (i:ZMod n)-2=(((i:ℤ)-2:ℤ):ZMod n) := by push_cast; rfl
  have c₄ : (i:ZMod n)-2*2=(((i:ℤ)-4:ℤ):ZMod n) := by push_cast; ring
  simp only [Nat.cast_one,Nat.cast_ofNat,mul_one]
  rw [cv,c₁,c₃,c₄,wrap f hf,wrap f hf,wrap g hg,wrap g hg]
  unfold localDegree
  ring

#print axioms circle_weight_degree
end
end QuorumAudit.TwoCrash
