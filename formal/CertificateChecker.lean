import Std

/-! Direct integer checks of rational finite base witnesses.
Weights are numerators with a common positive denominator `scale`.
Reads are three explicit node lists, including multiplicities by repetition.
No solver, floating-point calculation, or native_decide is used in proofs.
-/
namespace QuorumAudit

structure Gadget where
  a : Nat
  b : Nat
  reads : List (List Nat)
  scale : Nat
  uniform : List Nat
  criticalFlow : List Nat
  cuts : List Nat
  deriving Repr

def nodes (g : Gadget) : Nat := g.a + g.b + 2
def rankParameter (g : Gadget) : Nat := (g.a + g.b) / 3
def failed (g : Gadget) (i : Nat) : Bool := i == 0 || i == g.a + 1
def triple (n t : Nat) : List Nat :=
  (List.range 3).map fun j => (t / 2 + (t % 2 + 1) * j) % n
def readCount (g : Gadget) (i : Nat) : Nat :=
  (g.reads.map fun r => if r.contains i then 1 else 0).sum
def degree (g : Gadget) (flow : List Nat) (i : Nat) : Nat :=
  ((List.range (2 * nodes g)).map fun t =>
    if (triple (nodes g) t).contains i then flow.getD t 0 else 0).sum

def eligibleArcs (g : Gadget) : List (Nat × Nat) :=
  (if 15 ≤ g.a then [(1, g.a + 1)] else []) ++
  (if 15 ≤ g.b then [(g.a + 2, nodes g)] else [])

/-- Exact translation of the mathematical base-certificate conditions.
    Every read is checked against EVERY global allowed write, even failed ones. -/
def checkGadget (g : Gadget) : Bool :=
  let n := nodes g
  let k := rankParameter g
  let ts := List.range (2 * n)
  decide (g.a ≤ g.b ∧ g.b ≤ 17 ∧ 9 ≤ g.a + g.b ∧ (g.a + g.b) % 3 = 0) &&
  (g.scale > 0) && (g.reads.length == 3) &&
  (g.uniform.length == 2 * n) && (g.criticalFlow.length == 2 * n) &&
  g.reads.all (fun r =>
    (r.length == k + 2) && (r.eraseDups.length == r.length) &&
    r.all (fun i => (i < n) && !(failed g i)) &&
    ts.all (fun t => (triple n t).any (fun i => r.contains i))) &&
  ts.all (fun t => if g.uniform.getD t 0 + g.criticalFlow.getD t 0 > 0
    then (triple n t).all (fun i => !(failed g i)) else true) &&
  (g.uniform.sum == k * g.scale) &&
  (g.criticalFlow.sum == (k - 1) * (k + 2) * g.scale) &&
  (List.range n).all (fun i =>
    (degree g g.uniform i == if failed g i then 0 else g.scale) &&
    (degree g g.criticalFlow i == if failed g i then 0 else (k + 2 - readCount g i) * g.scale)) &&
  (g.cuts.length == (eligibleArcs g).length) &&
  (g.cuts.zip (eligibleArcs g)).all (fun (p, lo, hi) =>
    decide (lo + 4 ≤ p ∧ p + 7 ≤ hi) &&
    g.reads.all (fun r => (List.range 3).any (fun color =>
      (List.range 8).all (fun j => r.contains (p - 4 + j) == ((p - 4 + j) % 3 == color)))) &&
    (List.range 8).all (fun j => readCount g (p - 4 + j) == 1) &&
    [g.uniform, g.criticalFlow].all (fun flow =>
      (List.range 4).all (fun j => [1, 2].all (fun e =>
        flow.getD (2 * (p - 4 + j) + e - 1) 0 ==
          flow.getD (2 * (p - 4 + j + 3) + e - 1) 0))))

def expectedPairs : List (Nat × Nat) :=
  (List.range 18).flatMap fun a =>
    ((List.range 18).filter fun b => a ≤ b && 9 ≤ a + b && (a + b) % 3 == 0).map fun b => (a, b)

end QuorumAudit
