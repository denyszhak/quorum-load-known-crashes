import TwoCrashIncidence

namespace QuorumAudit.TwoCrash
open Finset
noncomputable section

def cycleRead {n k d : Nat} (w : CycleWitness n k d) (j : Nat) : Finset Nat :=
  (range n).filter fun i => w.read j i

theorem nat_wrap_read {n k d : Nat} (w : CycleWitness n k d) (j m : Nat) :
    w.read j (m%n:Nat)=w.read j m := by
  simpa only [Int.natCast_emod] using periodic_emod (w.read j) n (w.read_period j) m

theorem cycle_read_valid {n k d : Nat} (w : CycleWitness n k d) (j : Nat)
    (hj : j∈range 3) : ReadValid n k (cycleRead w j) := by
  have hn : 0<n := by have := w.size; omega
  refine ⟨filter_subset _ _,?_,?_⟩
  · apply Nat.cast_injective (R:=ℝ)
    calc
      ((cycleRead w j).card:ℝ) = ∑ i ∈ cycleRead w j, (1:ℝ) := by simp
      _ = cycleMass n (fun i => indicator (w.read j i)) := by
        simp [cycleRead,cycleMass,indicator]
      _ = (k:ℝ)+2 := w.read_mass j hj
      _ = ((k+2:Nat):ℝ) := by push_cast; rfl
  · intro v hv
    let s := v/2
    let e := v%2+1
    have hs : s<n := by dsimp [s]; have := mem_range.mp hv; omega
    have he : e=1 ∨ e=2 := by dsimp [e]; omega
    have hit := w.read_hit j hj (s:ℤ) (e:ℤ) (by omega) (by exact_mod_cast hs)
      (by exact_mod_cast he)
    have hit' : w.read j (s%n:Nat)=true ∨ w.read j ((s+e)%n:Nat)=true ∨
        w.read j ((s+2*e)%n:Nat)=true := by
      simpa only [nat_wrap_read, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hit
    rw [writeSet_explicit]
    change ((cycleRead w j) ∩ {s%n,(s+e)%n,(s+2*e)%n}).Nonempty
    rcases hit' with h | h | h
    · exact ⟨s%n,mem_inter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ hn),h⟩,
        mem_insert_self _ _⟩⟩
    · exact ⟨(s+e)%n,mem_inter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ hn),h⟩,
        by simp⟩⟩
    · exact ⟨(s+2*e)%n,mem_inter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ hn),h⟩,
        by simp⟩⟩

theorem cycle_read_live {n k d : Nat} (w : CycleWitness n k d) (j : Nat)
    (hj : j∈range 3) : cycleRead w j ⊆ range n \ {0,d} := by
  intro i hi
  obtain ⟨hin,hread⟩ := mem_filter.mp hi
  refine mem_sdiff.mpr ⟨hin,?_⟩
  intro hdead
  simp only [mem_insert,mem_singleton] at hdead
  rcases hdead with rfl | rfl
  · simp only [Nat.cast_zero,(w.read_dead j hj).1,Bool.false_eq_true] at hread
  · simp only [(w.read_dead j hj).2,Bool.false_eq_true] at hread

theorem cycle_read_multiplicity {n k d : Nat} (w : CycleWitness n k d) (i : Nat)
    (hi : i<n) : readMultiplicity (cycleRead w) i=readCountReal w.read i := by
  simp [readMultiplicity,readCountReal,cycleRead,indicator,hi]

theorem positive_support_sum {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (U C f : ι → ℝ) (hU : ∀j∈I,0≤U j) (hC : ∀j∈I,0≤C j)
    (hz : ∀j∈I,U j=0 → C j=0 → f j=0) :
    (∑ j ∈ I.filter (fun j => 0<U j+C j), f j)=∑ j∈I,f j := by
  apply sum_subset (filter_subset _ _)
  intro j hj hnot
  have hnon : ¬0<U j+C j := by
    intro hp; exact hnot (mem_filter.mpr ⟨hj,hp⟩)
  exact hz j hj (by have := hU j hj; have := hC j hj; linarith)
    (by have := hU j hj; have := hC j hj; linarith)

theorem circleWeight_nonneg (n : Nat) [NeZero n] (f g : ℤ → ℝ)
    (hf : ∀i,0≤f i) (hg : ∀i,0≤g i) (j : ZMod n×Nat) :
    0≤circleWeight n f g j := by
  unfold circleWeight
  split_ifs <;> first | exact hf _ | exact hg _

/-- The periodic witness gives actual finite quorum routings; in particular,
    zero-weight writes incident to a failed node are removed from the support. -/
theorem cycle_witness_routes {n k d : Nat} (w : CycleWitness n k d)
    (a : ℝ) (ha : 0≤a) (haReg : a≤critical k) :
    ∃ r : Routing (reads n k) (range n) {0,d},
    ∃ v : Routing (writes n) (range n) {0,d},
      ∀ i∈range n,combined r v a i≤target k a := by
  have hn : 11≤n := by have := w.size; have := w.rank; omega
  let _ : NeZero n := ⟨by omega⟩
  let U := circleWeight n w.u₁ w.u₂
  let C := circleWeight n w.c₁ w.c₂
  let I := (circleIndices n).filter fun j => 0<U j+C j
  let Q := fun j : ZMod n×Nat => circleWrite n j.1 j.2
  have hu (j : ZMod n×Nat) : 0≤U j :=
    circleWeight_nonneg n w.u₁ w.u₂ w.u₁_nonneg w.u₂_nonneg j
  have hc (j : ZMod n×Nat) : 0≤C j :=
    circleWeight_nonneg n w.c₁ w.c₂ w.c₁_nonneg w.c₂_nonneg j
  have su : (∑j∈I,U j)=flowTotal n w.u₁ w.u₂ := by
    rw [positive_support_sum _ U C U (fun j _ => hu j) (fun j _ => hc j)
      (fun j _ h _ => h),circle_weight_mass]
  have sc : (∑j∈I,C j)=flowTotal n w.c₁ w.c₂ := by
    rw [positive_support_sum _ U C C (fun j _ => hu j) (fun j _ => hc j)
      (fun j _ _ h => h),circle_weight_mass]
  have du (i : Nat) (hi : i<n) :
      (∑j∈I,if i∈Q j then U j else 0)=localDegree w.u₁ w.u₂ i := by
    rw [positive_support_sum _ U C _ (fun j _ => hu j) (fun j _ => hc j)
      (fun j _ hz _ => by simp only [hz,ite_self])]
    exact circle_weight_degree n hn w.u₁ w.u₂ w.u₁_period w.u₂_period i hi
  have dc (i : Nat) (hi : i<n) :
      (∑j∈I,if i∈Q j then C j else 0)=localDegree w.c₁ w.c₂ i := by
    rw [positive_support_sum _ U C _ (fun j _ => hu j) (fun j _ => hc j)
      (fun j _ _ hz => by simp only [hz,ite_self])]
    exact circle_weight_degree n hn w.c₁ w.c₂ w.c₁_period w.c₂_period i hi
  apply upper_routing_from_witnesses (reads n k) (writes n) (range n) {0,d}
    (cycleRead w) I Q C U k a (by exact_mod_cast w.rank) ha haReg
  · intro j hj; exact (cycle_read_valid w j hj).mem
  · exact cycle_read_live w
  · intro j hj
    have hj2 := (mem_product.mp (mem_filter.mp hj).1).2
    exact circleWrite_family n j.1 j.2 (by simpa only [mem_insert,mem_singleton] using hj2)
  · intro j hj
    have hj2 := (mem_product.mp (mem_filter.mp hj).1).2
    have hfamily := circleWrite_family n j.1 j.2
      (by simpa only [mem_insert,mem_singleton] using hj2)
    have hsub := writes_subset n (by omega) (Q j) hfamily
    intro i hi
    refine mem_sdiff.mpr ⟨hsub hi,?_⟩
    intro hdead
    have hin := mem_range.mp (hsub hi)
    have hdead' : (i:ℤ)=0 ∨ (i:ℤ)=d := by
      simpa only [mem_insert,mem_singleton,Nat.cast_eq_zero,Nat.cast_inj] using hdead
    have hzU : (∑l∈I,if i∈Q l then U l else 0)=0 := by
      rw [du i hin,w.u_degree i (by omega) (by exact_mod_cast hin),ite_eq_left hdead']
    have hzC : (∑l∈I,if i∈Q l then C l else 0)=0 := by
      rw [dc i hin,w.c_degree i (by omega) (by exact_mod_cast hin),ite_eq_left hdead']
    have hleU := single_le_sum (s:=I) (f:=fun l => if i∈Q l then U l else 0)
      (fun l _ => by split_ifs; exact hu l; rfl) hj
    have hleC := single_le_sum (s:=I) (f:=fun l => if i∈Q l then C l else 0)
      (fun l _ => by split_ifs; exact hc l; rfl) hj
    rw [ite_eq_left hi,hzU] at hleU
    rw [ite_eq_left hi,hzC] at hleC
    have hpos := (mem_filter.mp hj).2
    linarith
  · intro j _; exact hc j
  · intro j _; exact hu j
  · rw [sc,w.c_mass]
  · rw [su,w.u_mass]
  · intro i hi
    obtain ⟨hin,hdead⟩ := mem_sdiff.mp hi
    have hilt := mem_range.mp hin
    have hn' : ¬((i:ℤ)=0 ∨ (i:ℤ)=d) := by
      simpa only [mem_insert,mem_singleton,Nat.cast_eq_zero,Nat.cast_inj] using hdead
    rw [dc i hilt,w.c_degree i (by omega) (by exact_mod_cast hilt),ite_eq_right hn',
      cycle_read_multiplicity w i hilt]
  · intro i hi
    obtain ⟨hin,hdead⟩ := mem_sdiff.mp hi
    have hilt := mem_range.mp hin
    have hn' : ¬((i:ℤ)=0 ∨ (i:ℤ)=d) := by
      simpa only [mem_insert,mem_singleton,Nat.cast_eq_zero,Nat.cast_inj] using hdead
    rw [du i hilt,w.u_degree i (by omega) (by exact_mod_cast hilt),ite_eq_right hn']

#print axioms cycle_witness_routes
end
end QuorumAudit.TwoCrash
