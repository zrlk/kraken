/-
The resource specification and the per-thread invariants of message passing
(MP, `SLR/MpTrees.lean`) for the SLR rules (`ThreadRuleRX` for the writer,
`ThreadRuleR` for the reader).

## Resources

Locations: the flag `Fl = ⟨f, 4⟩`, the data word `Dt = ⟨d, 4⟩`, and a ghost
token `W` that no instruction accesses.

- The writer holds all of `Dt` (write set: the initial message), all of `Fl`
  and all of `W`. Its `str` adds `(1, tw)` to the write set of `Dt`; its
  `stlr` releases all of `Dt` into the slots of the flag message. It keeps
  `W` forever (its postcondition).
- The reader holds one **acquire id** `ι` of `Fl`, with acquire predicate
  `φ` (the flag's release predicate). It never gains or loses anything:
  in this model a load does not move slots into the thread (reads transfer
  in the assertion layer, `SLR/ReachRules.lean`). Holding `ι` keeps a slot
  for `ι` on every release message of `Fl` (`Erase.slotsDom`), and nobody
  else can acquire it, so the slot's full `Dt` permission pins down every
  later read of `Dt`.
- `φ` (`flagPred`): at a value with a non-zero low word, the message's slot
  holds all of `Dt`, whose maximal write is `(1, ts)` with `ts` at or below
  the message's timestamp (`Good`). At a zero low word it is pure (the
  initial flag message).

## Postcondition

`MpPost P rd`: `1 ≤ W` (the writer's) or the reader `rd` has `W4 = 1`, has
seen a non-zero flag message, and holds an acquire id of `Fl` with predicate
`φ`. `NPSafe`'s postcondition is shared by all threads; at a final
configuration validity allows only one thread to hold all of `W`, so the
other gives the reader's disjunct (`SLR/MpAdequacy.lean`).
-/
import Kraken.Promising.SLR.MpTrees
import Kraken.Promising.SLR.Adequacy

namespace Kraken.Promising.SLR.Mp

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.MpTrees

/-! ## Parameters and the flag's predicate -/

/-- The parameters of an MP instance: the flag and data addresses and the
writer's ghost token. -/
structure Params where
  f : BitVec 64
  d : BitVec 64
  W : Loc

namespace Params

/-- The flag word. -/
abbrev Fl (P : Params) : Loc := ⟨P.f, 4⟩

/-- The data word. -/
abbrev Dt (P : Params) : Loc := ⟨P.d, 4⟩

end Params

/-- The locations are distinct. -/
structure MpLocs (P : Params) : Prop where
  fd : P.f ≠ P.d
  wf : P.W ≠ P.Fl
  wd : P.W ≠ P.Dt

theorem MpLocs.fl_dt {P : Params} (h : MpLocs P) : P.Fl ≠ P.Dt := fun he => h.fd (congrArg Loc.addr he)

/-- The published state: all of `Dt`, whose maximal write is `(1, ts)` with
`ts ≤ V`. -/
def Good (Dt : Loc) (V : View) (r : Res) : Prop :=
  (r.wr Dt).q = 1 ∧ ∃ ts, (r.wr Dt).X (1#128, ts) ∧ (∀ p, (r.wr Dt).X p → p.2 ≤ ts) ∧ ts ≤ V

/-- **The flag's release and acquire predicate**: `Good` at a non-zero low
word (the reader tests the 32-bit value it loaded). -/
def flagPred (Dt : Loc) : Pred where
  P v _ V r := BitVec.setWidth 32 v ≠ 0 → Good Dt V r
  mono _ _ _ _ _ _ h := h

/-- The flag's predicate for these parameters. -/
abbrev Params.φ (P : Params) : Pred := flagPred P.Dt

theorem flagPred_pure {Dt : Loc} {v : Val} (hv : BitVec.setWidth 32 v = 0) : Pred.Pure (flagPred Dt) v :=
  fun _ _ h => absurd hv h

theorem flagPred_impure {Dt : Loc} {v : Val} (hv : BitVec.setWidth 32 v ≠ 0) : ¬ Pred.Pure (flagPred Dt) v :=
  fun h => by
    have := (h default 0 hv).1
    simp [Res.unit, Perm.unit] at this

/-! ## The writer -/

variable [layout : _root_.Layout]

/-- The thread is at position `i` of the laid-out program `p`. -/
def AtPos (p : Program) (st : State) (i : Nat) : Prop := st.st.2 = (layout p).addrOf i

/-- The writer's frame: the laid-out writer, no declarations, the end
address, `X0 = f`, `X1 = d`, both words outside the private memory. -/
structure FrameW (P : Params) (st : State) : Prop where
  exe : st.exe = layout mpWriter
  decls : st.decls = {}
  endPc : st.endPc = (layout mpWriter).addrOf 5
  x0 : st.st.1.regs.X0.toBitVec = P.f
  x1 : st.st.1.regs.X1.toBitVec = P.d
  df : Mem.loadInt st.st.1.dmem P.f 4 = none
  dd : Mem.loadInt st.st.1.dmem P.d 4 = none

/-- Before the data store: all of `Dt` (only the initial write), all of `W`,
a share of `Fl`. -/
def Own0 (P : Params) (r : Res) : Prop :=
  (r.wr P.Dt).q = 1 ∧ (∀ p, (r.wr P.Dt).X p → p.2 = 0) ∧ 1 ≤ (r.wr P.W).q ∧ 0 < (r.wr P.Fl).q

/-- After the data store: all of `Dt` with maximal write `(1, ts)`, `ts` at
or below `vwOld` (which the release's timestamp exceeds), all of `W`, a share
of `Fl`. -/
def Own1 (P : Params) (vs : Views) (r : Res) : Prop :=
  (r.wr P.Dt).q = 1 ∧ (∃ ts, (r.wr P.Dt).X (1#128, ts) ∧ (∀ p, (r.wr P.Dt).X p → p.2 ≤ ts) ∧ ts ≤ vs.vwOld) ∧
    1 ≤ (r.wr P.W).q ∧ 0 < (r.wr P.Fl).q

/-- After prepaying the release: `Dt` is in the slots of the pending flag
promise; the writer keeps `W` and a share of `Fl`. -/
def Prepaid (P : Params) (r : Res) : Prop :=
  (r.wr P.Dt).q = 0 ∧ 1 ≤ (r.wr P.W).q ∧ 0 < (r.wr P.Fl).q

/-- The writer's phase at each position (`x2`, `x3`: the low words of `X2`,
`X3`). Position 4 is the end (the label `done_w`, at the end address). -/
def PhaseW (P : Params) (i : Nat) (x2 x3 : BitVec 32) (vs : Views) (r : Res) : Prop :=
  match i with
  | 0 => Own0 P r
  | 1 => Own0 P r ∧ x2 = 1
  | 2 => Own1 P vs r
  | 3 => (Own1 P vs r ∨ Prepaid P r) ∧ x3 = 1
  | 4 => 1 ≤ (r.wr P.W).q
  | _ => False

/-- The writer's world facts: the flag's release predicate is `φ`, the
data's is pure. Stable under `Ghost.Le`. -/
def WorldW (P : Params) (g : Ghost) : Prop := g.rel P.Fl = P.φ ∧ ∀ v, Pred.Pure (g.rel P.Dt) v

/-- A prepaid writer (position 3 without `Dt`) has the flag promise
outstanding. -/
def PrepaidProm (P : Params) (tid : Nat) (i : Nat) (t : Thread isa) (m : Memory) (r : Res) : Prop :=
  i = 3 → (r.wr P.Dt).q = 0 → ∃ ts ∈ t.prom, m.get? ts = some ⟨P.Fl, 1#128, tid⟩

/-- **The writer's invariant** at clean flag `cl` (the writer's facts do not
depend on it: it reads nothing). -/
def InvW (P : Params) (tid : Nat) (_cl : Prop) (c : Config isa) (r : Res) (g : Ghost) : Prop :=
  WorldW P g ∧ ∃ t, c.threads[tid]? = some t ∧ FrameW P t.st ∧
    ∃ i, AtPos mpWriter t.st i ∧
      PhaseW P i (BitVec.setWidth 32 t.st.st.1.regs.X2.toBitVec)
        (BitVec.setWidth 32 t.st.st.1.regs.X3.toBitVec) t.views r ∧
      PrepaidProm P tid i t c.mem r

/-- Every pending mark is a message of the memory. -/
def PendIn (g : Ghost) (m : Memory) : Prop := ∀ ts ∈ g.pend, ts ≤ m.last

/-- An own pending promise is the prepaid flag release: the writer is at
position 3, has given `Dt` away, and it is the only own pending promise. -/
def OwnPendW (P : Params) (tid : Nat) (c : Config isa) (r : Res) (g : Ghost) : Prop :=
  ∀ t, c.threads[tid]? = some t → ∀ ts ∈ t.prom, ts ∈ g.pend → AtPos mpWriter t.st 3 ∧ (r.wr P.Dt).q = 0 ∧
    ∀ ts' ∈ t.prom, ts' ∈ g.pend → ts' = ts

/-- **The writer's instance invariant** for `ThreadRuleRX`. -/
def InvXW (P : Params) (tid : Nat) (cl : Prop) (c : Config isa) (r : Res) (g : Ghost) : Prop :=
  InvW P tid cl c r g ∧ PendIn g c.mem ∧ OwnPendW P tid c r g

/-! ## The reader -/

/-- The reader's frame. -/
structure FrameR (P : Params) (st : State) : Prop where
  exe : st.exe = layout mpReader
  decls : st.decls = {}
  endPc : st.endPc = (layout mpReader).addrOf 5
  x0 : st.st.1.regs.X0.toBitVec = P.f
  x1 : st.st.1.regs.X1.toBitVec = P.d
  df : Mem.loadInt st.st.1.dmem P.f 4 = none
  dd : Mem.loadInt st.st.1.dmem P.d 4 = none

/-- The memory has a flag message with a non-zero low word at a timestamp
`≤ V`. -/
def Seen (P : Params) (m : Memory) (V : View) : Prop :=
  ∃ ts v, m.read? P.Fl ts = some v ∧ BitVec.setWidth 32 v ≠ 0 ∧ ts ≤ V

/-- The reader has no forwarding item for the flag: the reader never writes,
so its acquire load is not forwarded. -/
def FlFwd (P : Params) (vs : Views) : Prop := vs.getFwd P.Fl = none

/-- The reader's phase at each position (`x3`, `x4`: the low words of `X3`,
`X4`). Position 4 is the end (the label `done_r`). Under the clean flag, the
data load returned `1`. -/
def PhaseR (P : Params) (cl : Prop) (i : Nat) (x3 x4 : BitVec 32) (m : Memory) (vs : Views) : Prop :=
  match i with
  | 1 => FlFwd P vs
  | 2 => FlFwd P vs ∧ (x3 ≠ 0 → Seen P m vs.vrNew)
  | 3 => FlFwd P vs ∧ Seen P m vs.vrNew
  | 4 => (∃ V, Seen P m V) ∧ (cl → x4 = 1)
  | _ => False

/-- The reader's world facts: the flag's release predicate is `φ`, and the
reader holds an acquire id of `Fl` with predicate `φ`. -/
def WorldR (P : Params) (r : Res) (g : Ghost) : Prop :=
  g.rel P.Fl = P.φ ∧ ∃ ι, ι < g.acqTab.length ∧ g.acqPred ι = P.φ ∧ r.acq P.Fl ι = 1

/-- **The reader's invariant** at clean flag `cl`. -/
def InvR (P : Params) (tid : Nat) (cl : Prop) (c : Config isa) (r : Res) (g : Ghost) : Prop :=
  WorldR P r g ∧ ∃ t, c.threads[tid]? = some t ∧ FrameR P t.st ∧
    ∃ i, AtPos mpReader t.st i ∧
      PhaseR P cl i (BitVec.setWidth 32 t.st.st.1.regs.X3.toBitVec)
        (BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec) c.mem t.views

/-! ## The postcondition -/

/-- The reader `rd` has loaded `1` into `W4`, and the memory has a flag
message with a non-zero low word. -/
def ReaderDone (P : Params) (rd : Nat) (c : Config isa) : Prop :=
  (∃ t, c.threads[rd]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 1) ∧
    ∃ ts v, c.mem.read? P.Fl ts = some v ∧ BitVec.setWidth 32 v ≠ 0

/-- **The shared postcondition** (`NPSafe`'s `B`): the writer's token, or the
reader's result with its acquire id. -/
def MpPost (P : Params) (rd : Nat) (c : Config isa) (r : Res) (g : Ghost) : Prop :=
  1 ≤ (r.wr P.W).q ∨
    (ReaderDone P rd c ∧ ∃ ι, ι < g.acqTab.length ∧ g.acqPred ι = P.φ ∧ r.acq P.Fl ι = 1)

end Kraken.Promising.SLR.Mp
