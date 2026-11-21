import TwoCrashSecondCut
import TwoCrashExpansionBases

namespace QuorumAudit.TwoCrash
open Finset
noncomputable section

theorem ordered_arcs_witness (A B k : Nat) (hk : 3≤k) (hs : A+B=3*k)
    (ho : compressArc A≤compressArc B) :
    Nonempty (CycleWitness (A+B+2) k (A+1)) := by
  obtain ⟨g,hg,hga,hgb,_⟩ := semantic_base_for_every_pair A B k hk hs
  rw [min_eq_left ho] at hga
  rw [max_eq_right ho] at hgb
  have hready := all_bases_expansion_ready g hg
  let w := rationalWitness g hready.1
  obtain ⟨_,_,_,haLong,ta,hta⟩ := compress_properties A
  obtain ⟨_,_,_,hbLong,tb,htb⟩ := compress_properties B
  have hA : A=g.a+3*ta := by omega
  have hB : B=g.b+3*tb := by omega
  have hsize := w.size
  have hn : nodes g=g.a+g.b+2 := rfl
  by_cases hta0 : ta=0
  · subst ta
    by_cases htb0 : tb=0
    · subst tb
      have hnk : rankParameter g=k := by omega
      have hnn : nodes g=A+B+2 := by omega
      have hdd : g.a+1=A+1 := by omega
      simpa only [hnk,hnn,hdd] using (show Nonempty (CycleWitness (nodes g)
        (rankParameter g) (g.a+1)) from ⟨w⟩)
    · have hlong : 15≤g.b := by
        have hB15 : 15≤B := by
          by_contra h
          have hb : compressArc B=B := by simp [compressArc, show B<15 by omega]
          omega
        have := hbLong hB15
        omega
      obtain ⟨q,_,hq,hqd⟩ := hready.2.2.2.1 hlong
      have hcut : Cut w q := rational_cut_sound g hready.1 q (hready.2.1 q hq)
      have hdd : shiftedFailure q tb (g.a+1)=A+1 := by
        unfold shiftedFailure
        rw [ite_eq_left (by omega)]
        omega
      have hnk : rankParameter g+tb=k := by omega
      have hnn : nodes g+3*tb=A+B+2 := by omega
      simpa only [hnk,hnn,hdd] using
        (show Nonempty (CycleWitness (nodes g+3*tb) (rankParameter g+tb)
          (shiftedFailure q tb (g.a+1))) from ⟨expand w q tb hcut⟩)
  · have hlongA : 15≤g.a := by
      have hA15 : 15≤A := by
        by_contra h
        have ha : compressArc A=A := by simp [compressArc, show A<15 by omega]
        omega
      have := haLong hA15
      omega
    obtain ⟨p,_,hp,hpd⟩ := hready.2.2.1 hlongA
    have hcut : Cut w p := rational_cut_sound g hready.1 p (hready.2.1 p hp)
    let w' := expand w p ta hcut
    have hd' : shiftedFailure p ta (g.a+1)=A+1 := by
      unfold shiftedFailure
      rw [ite_eq_right (by omega)]
      omega
    by_cases htb0 : tb=0
    · subst tb
      have hnk : rankParameter g+ta=k := by omega
      have hnn : nodes g+3*ta=A+B+2 := by omega
      simpa only [hnk,hnn,hd'] using
        (show Nonempty (CycleWitness (nodes g+3*ta) (rankParameter g+ta)
          (shiftedFailure p ta (g.a+1))) from ⟨w'⟩)
    · have hlongB : 15≤g.b := by omega
      obtain ⟨q,_,hq,hqd⟩ := hready.2.2.2.1 hlongB
      have hcutq : Cut w q := rational_cut_sound g hready.1 q (hready.2.1 q hq)
      have hpq := hready.2.2.2.2 p hp q hq hpd hqd
      have hsecond : Cut w' (q+3*ta) := second_cut w p q ta hcut hcutq hpq
      have hdd : shiftedFailure (q+3*ta) tb (shiftedFailure p ta (g.a+1))=A+1 := by
        rw [hd']
        unfold shiftedFailure
        rw [ite_eq_left (by omega)]
      have hnk : rankParameter g+ta+tb=k := by omega
      have hnn : nodes g+3*ta+3*tb=A+B+2 := by omega
      simpa only [hnk,hnn,hdd] using
        (show Nonempty (CycleWitness (nodes g+3*ta+3*tb) (rankParameter g+ta+tb)
          (shiftedFailure (q+3*ta) tb (shiftedFailure p ta (g.a+1))))
          from ⟨expand w' (q+3*ta) tb hsecond⟩)

#print axioms ordered_arcs_witness
end
end QuorumAudit.TwoCrash
