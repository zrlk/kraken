/-
**The one-thread consumer at any call depth with buffer allocation** on the
canonical AArch64 target: the twin of `Spike/Lib/A64ConsumerS.lean` (whose
statements are unchanged) for a source thread that allocates buffers
(`let x = newBuf a τ in e`), over the allocator's arena (`Arena`: the arena
at `heap` of `cells` 16-byte cells, the heap counter word `ctr`, the
allocator's `units` and base offsets `off`).

- `Arena`, `Arena.OK` (ISA-neutral, `Spike/Lib/Arena.lean`): the arena's
  parameters and their facts (the counter off the arena, the units and
  offsets of an object of `k · nWords us` words with its header).
- `msOfA`: `msOfS` with the arena, and the allocation fragment (`xa`): the
  pair lands in the fragment with the new label placed, the arena fitting
  the object (`HeapLand.AllocLand`); box rows where the arena admits them
  (`Arena.newOk`). `msOfA0`: the same with no box rows.
- `WeAb`, `msOfAB`: the write abort's justification tied to the phase `Ab`,
  and `msOfA` with `print`'s byte step (`ByteOut`) and it (properties in
  `Spike/Lib/A64ConsumerAB.lean`); `msOfAX`: `msOfA` or `msOfAB`, the rows'
  memory side `NodesA`'s `ab` picks (`none`: `msOfA`).
- `PendA`: `PendN` without its "not at a buffer allocation".
- `CtrRow`: the premises of `Out.ctrRmw` at a pair (the counter's add).
- `Writes`: an instruction's outcome writes a location (appended or
  fulfilling a promise, as `ExtRows.out_memP` gives it).
- `NodesA`: `NodesS` without `noAlloc`, its rows under `msOfAX … ab`, plus `ctrRow` (an outcome that
  writes the counter word is the counter's add), `arena` (no outcome writes
  into the arena outside the placed labels, but the header of a pending
  allocation below its base, or the box's initialising store, `NewStM`) and
  `zero` (the zero words of an allocated type represent 0).
- `HoldInvA`: the hold an exchange's (`HoldInv`) or the counter's.
- `PreJA`, `PreSA`, `RSA`: `PreJ`, `PreS`, `RS` with the hold `HoldInvA`,
  the counter off every placed label (`CtrOff`), and the heap clause
  `HeapCtr` replaced by the allocation invariant at the source's heap use
  (`AllocInvAt … (heapUse s)`, `Spike/Lib/HeapObl.lean`), which gives it
  (`heapCtr_of_allocInvAt`).
- Frame runs keep the allocation invariant (`allocInvAt_frameRun`); the
  header store may fulfil a promise (`AllocInvAt.header_fulfil`); the rows
  and pending landings of `NodesS` restated (`NodesA.row`, `pend_runA`,
  `pre_localJA`, `pend_landA`); `NodesA.rowX`: the row under `msOfA` off the
  output `write`, for rows under any `msOfAX … ab`.
-/
import Spike.Lib.A64ConsumerS
import Spike.Lib.A64PlacedSE
import Spike.Lib.HeapLand
import Spike.Lib.Arena
import Spike.Lib.ByteOut
import Spike.Lib.MemSideBW
import Spike.Lib.AllocLo
import Spike.Lib.FrameNew
import Spike.Lib.OutNew

namespace Spike.Lib.A64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Sem.SrcSem (mainExit)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS
open Spike.Lib.AllocRow (freeR)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.ByteOut (ByteOut)

variable {P : SrcSem.SrcParams} {p : Prog} {E : Entry}

/-! ## Over the arena (`Spike.Lib.Arena`) -/

/-- **The counter word is off every placed label** (the source's objects:
the layout's static labels and the arena's buffers; the runtime's words,
the counter among them, are not labels). The hold of an exchange is at a
placed word, so never the counter's. -/
def CtrOff (ar : Arena) (lbl : Lbl) (lsize : Lsize) : Prop :=
  ∀ l b, lbl l = some b → ¬ (lrange lsize l b).contains ar.ctr

/-- **The memory side at the frames `fs` with the arena and no box rows**
(`msOfS` with the arena): an allocation lands in the fragment `I` with the
label placed and the arena fitting the object (`AllocLand`); the counter
floor is the placement's (`AllocLo.LoOf`: the arena above the cursor free of
every placed label). -/
def msOfA0 (Λ : Scc.Sem.Layout) (μ : Marks) (rd : TermRun.Word → Prop) (G : Loc → Val → Prop) (own : OwnS)
    (ar : Arena) (I : InvS) (lbl : Lbl) (lsize : Lsize) (fs : List TermRun.Frame) : MemSide isaLSE2 :=
  MemSide.ofLabels rd lbl lsize (some abi) G ar.heap ar.ctr ar.units ar.off ar.cells (own := (own · fs))
    (mp := fun L w => Kernel.mapped (K0 Λ) w L = true ∧ (w = true → LocIn Λ.shared L))
    (abortAt := fun s => ∃ k a, μ.abortAt k = some a ∧ pcOf s = a) (pl := fun s c => fs = [] ∧ Placed Λ lbl s c)
    (xa := fun l b n s c => AllocLand ar.heap ar.cells b n ∧
      I (fun l' => if l' = l then some b else lbl l') (fun l' => if l' = l then n else lsize l') s c fs)
    (lo := Spike.Lib.AllocLo.LoOf ar.heap ar.cells lbl lsize)

/-- **The memory side at the frames `fs` with the arena** (`msOfA0`), box
rows admitted where the arena admits them (`Arena.newOk`), and the source's
publication at a fence where it admits it (`Arena.pub`). -/
def msOfA (Λ : Scc.Sem.Layout) (μ : Marks) (rd : TermRun.Word → Prop) (G : Loc → Val → Prop) (own : OwnS)
    (ar : Arena) (I : InvS) (lbl : Lbl) (lsize : Lsize) (fs : List TermRun.Frame) : MemSide isaLSE2 :=
  { msOfA0 Λ μ rd G own ar I lbl lsize fs with newOk := ar.newOk, pub := ar.pub }

/-- **The write abort's justification at `s`, tied to the phase `Ab`**: every
result `r` the kernel may refuse the call with (`Kernel.writeRefused`)
resumes the thread (`K.ret s r`) in `Ab`. -/
def WeAb {I : ISA} (K : Kernel.Abi I) (Ab : I.State → Prop) : I.State → Ctl → Prop :=
  fun s _ => ∀ r, Kernel.writeRefused r = true → Ab (K.ret s r)

/-- **The memory side at the frames `fs` with the arena, `print`'s byte step
and the write abort phase `Ab`**: `msOfA` with `bo := ByteOut p lbl` and
`we := WeAb abi Ab`. -/
def msOfAB (Λ : Scc.Sem.Layout) (μ : Marks) (p : Prog) (rd : TermRun.Word → Prop) (G : Loc → Val → Prop)
    (own : OwnS) (ar : Arena) (I : InvS) (Ab : State → Prop) (lbl : Lbl) (lsize : Lsize)
    (fs : List TermRun.Frame) : MemSide isaLSE2 :=
  (msOfA Λ μ rd G own ar I lbl lsize fs).withBW (ByteOut p lbl) (WeAb abi Ab)

/-- **The memory side of the rows**: `msOfA`, or, given the write abort
phase `Ab`, `msOfAB` (`print`'s byte step and the write abort's
justification). `NodesA`'s `ab` picks it; at `none` it is `msOfA`
definitionally. -/
def msOfAX (Λ : Scc.Sem.Layout) (μ : Marks) (p : Prog) (rd : TermRun.Word → Prop) (G : Loc → Val → Prop)
    (own : OwnS) (ar : Arena) (I : InvS) :
    Option (State → Prop) → Lbl → Lsize → List TermRun.Frame → MemSide isaLSE2
  | none => msOfA Λ μ rd G own ar I
  | some Ab => msOfAB Λ μ p rd G own ar I Ab

/-- **A pair whose source has a pending frame run into the fragment**, not at
`main`'s return (`PendN` without its "not at a buffer allocation"). -/
def PendA (p : Prog) (I : InvS) : InvS := fun lbl lsize s c fs =>
  (fs = [] → ∀ a, c.term ≠ .ret a) ∧ Pend p (I lbl lsize) s c fs

/-- **The counter's add at a pair** (`Out.ctrRmw`'s premises under `ms`,
landing in `X`): the instruction is the read-modify-write of the counter
word adding the allocation's units, at an allocation site (`AllocSite
ms.newOk`: a buffer, or where `ms` admits it a box) with no hold; for every old value runtime memory may hold there, owned, within the
cells, above the counter floor, the new value may be held there too and the control, holding the old
count, lands in `X`. -/
def CtrRow (ms : MemSide isaLSE2) (X : Frag isaLSE2) (s : State) (c : Ctl) : Prop :=
  ∃ (k : Kraken.RmwKind) (op : Val → Option Val) (g : Val → State) (x : String) (τ : Ty) (e : Expr) (n : Nat),
    isaLSE2.exec s = some (.rmw k false ⟨BitVec.ofNat 64 ms.ctr, 8⟩ op fun v => .done (g v)) ∧
    ms.rt (BitVec.ofNat 64 ms.ctr).toNat ∧ ms.mp ⟨BitVec.ofNat 64 ms.ctr, 8⟩ true ∧
    AllocSite ms.newOk c x n τ e ∧
    c.hold = none ∧
    (∀ old, op old = some ((old.setWidth 64 + BitVec.ofNat 64 (ms.units n τ)).setWidth 128)) ∧
    (∀ old, ms.G ⟨BitVec.ofNat 64 ms.ctr, 8⟩ old → (∀ w, (⟨BitVec.ofNat 64 ms.ctr, 8⟩, w) ∈ ms.own s → old = w) →
      (old.setWidth 64).toNat ≤ ms.cells → ms.lo (old.setWidth 64).toNat →
      ms.G ⟨BitVec.ofNat 64 ms.ctr, 8⟩ ((old.setWidth 64 + BitVec.ofNat 64 (ms.units n τ)).setWidth 128) ∧
      X (g old) { c with hold := some (ms.ctr, TermRun.cst (.num (old.setWidth 64).toNat)) })

/-- **A write the arena allows from the control `c`**: to the counter word
(`ctrRow` says how), off the arena, into a placed label, or, the counter
held at the old count `old` at `let x = newBuf a τ in e` of `k` elements,
below the object's base (the header); or, where the arena admits box rows
(`Arena.newOk`), the counter held at `old` at `let x = new a in e` of one
object of `a`'s type `ty`, below the box's base (the box's header). -/
def ArenaW (ar : Arena) (lbl : Lbl) (lsize : Lsize) (c : Ctl) (L : Loc) : Prop :=
  L = ar.ctrLoc ∨ ¬ (ar.heap ≤ L.addr.toNat ∧ L.addr.toNat < ar.heap + 16 * ar.cells) ∨
    (∃ l b, lbl l = some b ∧ (lrange lsize l b).contains L.addr.toNat) ∨
    (∃ old x a τ e ta ws k, c.hold = some (ar.ctr, TermRun.cst (.num old)) ∧ c.term = .let_ x (.newBuf a τ) e ∧
      TermRun.evalAt c.env a = some (ta, ws) ∧ TermRun.numOf ws = some k ∧
      L.addr.toNat < ar.heap + 16 * old + ar.off k τ) ∨
    (ar.newOk ∧ ∃ old x a e ty ws, c.hold = some (ar.ctr, TermRun.cst (.num old)) ∧ c.term = .let_ x (.new a) e ∧
      TermRun.evalAt c.env a = some (ty, ws) ∧ L.addr.toNat < ar.heap + 16 * old + ar.off 1 ty)

/-- **An outcome writes the location `L`**: one message of thread 0 at `L`,
appended (the promises unchanged) or fulfilling an outstanding promise (the
memory unchanged), as `ExtRows.out_memP` gives an `Out` row's write. -/
def Writes (t : Thread isaLSE2) (mem : Memory) (o : Outcome isaLSE2) (L : Loc) : Prop :=
  ∃ V : Val, (o.mem = (mem.append ⟨L, V, 0⟩).1 ∧ o.thread.prom = t.prom) ∨
    ∃ q ∈ t.prom, mem.get? q = some ⟨L, V, 0⟩ ∧ o.mem = mem ∧ o.thread.prom = t.prom.erase q

/-- **The node obligations at any depth with allocation** (`NodesS` without
`noAlloc`, the rows under `msOfAX … ab` (`msOfA` at the default `none`,
`msOfAB` with the write abort phase `Ab` at `some Ab`) landing with a pending frame run, `Pend`,
as `NodesS.out`'s; the pending landings `PendA`): `ctrRow`,
an outcome of the instruction of a pair a frame run reaches that writes the
counter word (`Writes`) is the counter's add (`CtrRow`, landing in `PendA`);
`arena`, every location such an outcome writes is one the arena allows
(`ArenaW`), or the box's initialising store from the pair (`NewStM`, at
`msOfA`'s own fields); `zero`, at a buffer allocation the zero
words of the type represent 0 under every placement. The rest as in
`NodesS`. At the system calls `Cl` marks (a `clone`, `ClonePathS`; none at
the default) no row is asked for (`out`'s last premise). -/
structure NodesA (Λ : Scc.Sem.Layout) (p : Prog) (μ : Marks) (rd : TermRun.Word → Prop) (G : Loc → Val → Prop)
    (own : OwnS) (ar : Arena) (I : InvS) (ab : Option (State → Prop) := none)
    (Cl : State → Prop := fun _ => False) : Prop where
  out : ∀ lbl lsize s c fs, I lbl lsize s c fs → (∀ a, μ.site .take = some a → pcOf s ≠ a) →
    (abi.atSys s = true → ¬ Cl s) → OutS p lbl (msOfAX Λ μ p rd G own ar I ab lbl lsize) (Pend p (I lbl lsize)) s c fs
  noRet : ∀ lbl lsize s c, I lbl lsize s c [] → ∀ a, c.term ≠ .ret a
  cell : ∀ lbl lsize s c fs, IRun p I lbl lsize s c fs → ∀ x a e ty w,
    (c.term = .let_ x (.load true a) e ∨ ∃ b, c.term = .let_ x (.store true a b none) e) →
    TermRun.evalAt c.env a = some (ty, [w]) → OneCellTy ty
  noSite : ∀ lbl lsize s c fs, I lbl lsize s c fs → ∀ a, μ.site .release = some a → pcOf s ≠ a
  mapped : ∀ lbl lsize s c fs, I lbl lsize s c fs → abi.atSys s = false → ∀ e, isaLSE2.exec s = some e →
    ¬ Kernel.Touches (fun l w => Kernel.mapped (K0 Λ) w l = false) e
  place : ∀ lbl lsize s c fs, I lbl lsize s c fs → PlacedSE Λ lbl s c fs
  svc : ∀ lbl lsize s c fs, I lbl lsize s c fs → abi.atSys s = true →
    ∃ imm sz, Kraken.Promising.Lower.A64.CellAt s (.instr ⟨.W64, .SVC imm⟩) sz
  ownRun : ∀ lbl lsize s c fs c' fs', FrameRun p (c, fs) (c', fs') →
    (I lbl lsize s c fs ∨ I lbl lsize s c' fs') → own s fs' = own s fs
  ownInstr : ∀ lbl lsize s c fs, IRun p I lbl lsize s c fs → abi.atSys s = false → ∀ tree,
    isaLSE2.exec s = some tree → OwnTree (own · fs) (own s fs) tree
  ownSys : ∀ lbl lsize s c fs, IRun p I lbl lsize s c fs → abi.atSys s = true → ∀ call,
    Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call → ∀ s' ∈ Kernel.certSuccs abi s call,
      own s' fs = own s fs
  ownTake : ∀ lbl lsize s c fs, I lbl lsize s c fs → ∀ a, μ.site .take = some a → pcOf s = a →
    ∀ m, own (abi.skip (abi.setDmem s m)) fs = own s fs
  ctrRow : ∀ lbl lsize s c fs, IRun p I lbl lsize s c fs → abi.atSys s = false → ∀ (t : Thread isaLSE2) mem outs o,
    t.st = s → stepOne Arch.armv8 t 0 mem = some outs → .ok o ∈ outs → Writes t mem o ar.ctrLoc →
    CtrRow (msOfA Λ μ rd G own ar I lbl lsize fs) (fun s' c' => PendA p I lbl lsize s' c' fs) s c
  arena : ∀ lbl lsize s c fs, IRun p I lbl lsize s c fs → abi.atSys s = false → ∀ (t : Thread isaLSE2) mem outs o L,
    t.st = s → stepOne Arch.armv8 t 0 mem = some outs → .ok o ∈ outs → Writes t mem o L →
    ArenaW ar lbl lsize c L ∨ NewStM p lbl (msOfA Λ μ rd G own ar I lbl lsize fs) s c
  zero : ∀ lbl lsize s c fs, IRun p I lbl lsize s c fs → ∀ x a τ e, c.term = .let_ x (.newBuf a τ) e →
    ∀ vs, TermRun.zeroWords (TermRun.close [] τ) = some vs → ∀ v ∈ vs, ∀ lbl' : WeakMem.AllocLabel → Option Nat,
      ValRep lbl' v 0

/-! ## The relation -/

/-- **The hold with the arena**: an exchange's (`HoldInv`), or the
counter's (between the counter's add and the allocation's landing, its
count `AllocInvAt`'s). -/
def HoldInvA (ar : Arena) (lbl : Lbl) (lsize : Lsize) (sm : WeakMem.Memory) (hd : Option (Nat × TermRun.Word)) :
    Prop :=
  HoldInv lbl lsize sm hd ∨ ∃ w, hd = some (ar.ctr, w)

/-- **Before the exit, over a fragment `J`, with the arena, the ranges held
by `H`** (`PreJ` with the heap clause the allocation invariant at the
source's heap use, the hold an exchange's or the counter's, `HoldInvA`, and
the counter off every placed label, `CtrOff`; the held list by a predicate
`H` of the thread state, `HeldPathS`). -/
def PreJAH (Λ : Scc.Sem.Layout) (P : SrcSem.SrcParams) (p : Prog) (G : Loc → Val → Prop) (own : OwnS) (J : InvS)
    (H : State → List (Nat × Range) → Prop) (μ : Marks) (ar : Arena) (t : T.M.Cfg) (s : TermRun.Cfg) : Prop :=
  ∃ (th : Thread isaLSE2) (th0 : TermRun.TTh) (j : Nat) (lbl : Lbl) (lsize : Lsize) (ts : Nat → Option Nat)
    (hl : List (Nat × Range)) (pm : _root_.Mem 64) (hd : Option (Nat × TermRun.Word)),
    t.1.threads = #[th] ∧ (∃ E : Entry, t.2 = KS E Λ j hl pm) ∧ (∀ a, Kernel.byte pm a = 0) ∧ H th.st hl ∧
    WrOk th j ∧
    CertOkC Arch.armv8 (Kernel.certSem abi Arch.armv8 μ t.2 0) 0 th t.1.mem ∧
    s.ths = #[th0] ∧ th0.σs = [] ∧ th0.promises = [] ∧
    J lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack ∧ HoldInvA ar lbl lsize s.mem hd ∧ WideSt th.st ∧
    th.Bnd t.1.mem.last ∧ Inv1 Λ lbl lsize ts th t.1.mem s.mem ∧
    OwnMsgs t.1.mem ∧ MemIn Λ t.1.mem ∧ MemFits t.1.mem ∧ MemInv G t.1.mem ∧
    ExtRows.OwnOk (own th.st th0.stack) t.1.mem th.prom ∧
    AllocInvAt Λ lbl lsize th t.1.mem ar.heap ar.cells ar.ctr ar.units ar.off (heapUse s) ⟨th0.term, th0.env, hd⟩ ∧
    AllocInv.FreshInv lbl s.lbase s.n 0 th0.nalloc ∧ CtrOff ar lbl lsize ∧ ∃ tr, (SrcSem.source P p).Reach tr s

/-- **Before the exit**, the ranges held by `H` (`PreSA` over `H`):
`PreJAH` over the fragment. -/
abbrev PreSAH (Λ : Scc.Sem.Layout) (P : SrcSem.SrcParams) (p : Prog) (G : Loc → Val → Prop) (own : OwnS) (I : InvS)
    (H : State → List (Nat × Range) → Prop) (μ : Marks) (ar : Arena) (t : T.M.Cfg) (s : TermRun.Cfg) : Prop :=
  PreJAH Λ P p G own I H μ ar t s

/-- **The relation**, the ranges held by `H` (`RSA` over `H`). -/
def RSAH (Λ : Scc.Sem.Layout) (P : SrcSem.SrcParams) (p : Prog) (G : Loc → Val → Prop) (own : OwnS) (I : InvS)
    (H : State → List (Nat × Range) → Prop) (μ : Marks) (ar : Arena) (t : T.M.Cfg) (s : TermRun.Cfg) : Prop :=
  PreSAH Λ P p G own I H μ ar t s ∨ PostSAH Λ P p H t s

/-- **Before the exit, over a fragment `J`, with the arena** (`PreJ` with
the heap clause the allocation invariant at the source's heap use, the hold
an exchange's or the counter's, `HoldInvA`, and the counter off every placed
label, `CtrOff`): `PreJAH` at `HeldOk` (definitionally, `PreJA_eq`). -/
def PreJA (Λ : Scc.Sem.Layout) (P : SrcSem.SrcParams) (p : Prog) (G : Loc → Val → Prop) (own : OwnS) (J : InvS)
    (rS : Range) (Tk : State → Prop) (μ : Marks) (ar : Arena) (t : T.M.Cfg) (s : TermRun.Cfg) : Prop :=
  ∃ (th : Thread isaLSE2) (th0 : TermRun.TTh) (j : Nat) (lbl : Lbl) (lsize : Lsize) (ts : Nat → Option Nat)
    (hl : List (Nat × Range)) (pm : _root_.Mem 64) (hd : Option (Nat × TermRun.Word)),
    t.1.threads = #[th] ∧ (∃ E : Entry, t.2 = KS E Λ j hl pm) ∧ (∀ a, Kernel.byte pm a = 0) ∧ HeldOk Λ rS Tk th.st hl ∧
    WrOk th j ∧
    CertOkC Arch.armv8 (Kernel.certSem abi Arch.armv8 μ t.2 0) 0 th t.1.mem ∧
    s.ths = #[th0] ∧ th0.σs = [] ∧ th0.promises = [] ∧
    J lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack ∧ HoldInvA ar lbl lsize s.mem hd ∧ WideSt th.st ∧
    th.Bnd t.1.mem.last ∧ Inv1 Λ lbl lsize ts th t.1.mem s.mem ∧
    OwnMsgs t.1.mem ∧ MemIn Λ t.1.mem ∧ MemFits t.1.mem ∧ MemInv G t.1.mem ∧
    ExtRows.OwnOk (own th.st th0.stack) t.1.mem th.prom ∧
    AllocInvAt Λ lbl lsize th t.1.mem ar.heap ar.cells ar.ctr ar.units ar.off (heapUse s) ⟨th0.term, th0.env, hd⟩ ∧
    AllocInv.FreshInv lbl s.lbase s.n 0 th0.nalloc ∧ CtrOff ar lbl lsize ∧ ∃ tr, (SrcSem.source P p).Reach tr s

/-- **Before the exit** at any depth with the arena: `PreJA` over the
fragment. -/
abbrev PreSA (Λ : Scc.Sem.Layout) (P : SrcSem.SrcParams) (p : Prog) (G : Loc → Val → Prop) (own : OwnS) (I : InvS)
    (rS : Range) (Tk : State → Prop) (μ : Marks) (ar : Arena) (t : T.M.Cfg) (s : TermRun.Cfg) : Prop :=
  PreJA Λ P p G own I rS Tk μ ar t s

/-- **The relation** at any depth with the arena. -/
def RSA (Λ : Scc.Sem.Layout) (P : SrcSem.SrcParams) (p : Prog) (G : Loc → Val → Prop) (own : OwnS) (I : InvS)
    (rS : Range) (Tk : State → Prop) (μ : Marks) (ar : Arena) (t : T.M.Cfg) (s : TermRun.Cfg) : Prop :=
  PreSA Λ P p G own I rS Tk μ ar t s ∨ PostSA Λ P p rS Tk t s

/-- `PreJA` is `PreJAH` at `HeldOk`. -/
theorem PreJA_eq {Λ : Scc.Sem.Layout} {P : SrcSem.SrcParams} {p : Prog} {G : Loc → Val → Prop} {own : OwnS}
    {J : InvS} {rS : Range} {Tk : State → Prop} {μ : Marks} {ar : Arena} {t : T.M.Cfg} {s : TermRun.Cfg} :
    PreJA Λ P p G own J rS Tk μ ar t s = PreJAH Λ P p G own J (HeldOk Λ rS Tk) μ ar t s := rfl

/-- `RSA` is `RSAH` at `HeldOk`. -/
theorem RSA_eq {Λ : Scc.Sem.Layout} {P : SrcSem.SrcParams} {p : Prog} {G : Loc → Val → Prop} {own : OwnS}
    {I : InvS} {rS : Range} {Tk : State → Prop} {μ : Marks} {ar : Arena} {t : T.M.Cfg} {s : TermRun.Cfg} :
    RSA Λ P p G own I rS Tk μ ar t s = RSAH Λ P p G own I (HeldOk Λ rS Tk) μ ar t s := rfl

/-- **`PreJA`'s allocation invariant gives `PreJ`'s heap clause.** -/
theorem heapCtr_of_allocInvAt {Λ : Scc.Sem.Layout} {lbl : Lbl} {lsize : Lsize} {th : Thread isaLSE2}
    {tm : Memory} {ar : Arena} {s : TermRun.Cfg} {c : Ctl}
    (h : AllocInvAt Λ lbl lsize th tm ar.heap ar.cells ar.ctr ar.units ar.off (heapUse s) c) :
    HeapCtr ar.cells ar.ctr (heapUse s) c :=
  h.heapCtr

/-! ## Frame runs and the allocation invariant -/

/-- **No local step at a buffer allocation** whose count evaluates (the
source's allocation step changes the allocation count). -/
theorem localStepS_not_newBuf {c c' : Ctl} (h : LocalStepS p c c') {x : String} {a : At} {τ : Ty} {e : Expr}
    {ta : Ty} {ws : List TermRun.Word} {k : Nat} (ht : c.term = .let_ x (.newBuf a τ) e)
    (hea : TermRun.evalAt c.env a = some (ta, ws)) (hk : TermRun.numOf ws = some k) : False := by
  obtain ⟨-, h2⟩ := h
  let g : TermRun.G := { p := p, k := default, arch := default, lbase := 0, n := 1, i := 0 }
  let th : TermRun.TTh := { term := c.term, env := c.env }
  have hs := h2 g (#[] : WeakMem.Memory) [] th rfl rfl rfl rfl
  cases hus : TermRun.accs (TermRun.close th.σs τ) with
  | some us =>
    obtain ⟨z, ini, th', hm, -, -, -, -, -, hn⟩ :=
      SrcMem.src_newBuf_step g (#[] : WeakMem.Memory) [] th ht hea hk hus
    rw [hs] at hm
    simp only [List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨-, -, rfl⟩ := hm
    simp [th] at hn
  | none =>
    simp only [TermRun.tstep, th, ht, TermRun.evalOp, hea, TermRun.ol] at hs
    have hus0 : TermRun.accs (TermRun.close [] τ) = none := hus
    simp [hus0] at hs

/-- **A frame run from a buffer allocation whose count evaluates is
empty.** -/
theorem FrameRun.eq_of_newBuf {c : Ctl} {fs : List TermRun.Frame} {q' : Ctl × List TermRun.Frame}
    (hr : FrameRun p (c, fs) q') {x : String} {a : At} {τ : Ty} {e : Expr} {ta : Ty} {ws : List TermRun.Word}
    {k : Nat} (ht : c.term = .let_ x (.newBuf a τ) e) (hea : TermRun.evalAt c.env a = some (ta, ws))
    (hk : TermRun.numOf ws = some k) : q' = (c, fs) := by
  cases hr with
  | refl => rfl
  | step hs _ =>
    cases hs with
    | loc hl => exact (localStepS_not_newBuf hl ht hea hk).elim
    | call hc => rw [ht] at hc; cases hc
    | ret hc => rw [ht] at hc; cases hc

/-- **A frame run ends where it started or with no hold.** -/
theorem FrameRun.hold_of {q q' : Ctl × List TermRun.Frame} (hr : FrameRun p q q') :
    q' = q ∨ q'.1.hold = none := by
  induction hr with
  | refl => exact .inl rfl
  | step hs _ ih =>
    refine .inr (ih.elim (fun h => ?_) id)
    subst h
    cases hs with
    | loc hl => exact hl.1
    | call => rfl
    | ret => rfl

/-- A frame run keeps `HoldInvA`: it holds the same or nothing
(`FrameRun.hold_of`). -/
theorem holdInvA_frameRun {p : Prog} {ar : Arena} {lbl : Lbl} {lsize : Lsize} {sm : WeakMem.Memory}
    {q q' : Ctl × List TermRun.Frame} (hr : FrameRun p q q') (h : HoldInvA ar lbl lsize sm q.1.hold) :
    HoldInvA ar lbl lsize sm q'.1.hold := by
  rcases FrameRun.hold_of hr with rfl | hn
  · exact h
  · rw [hn]; exact .inl trivial

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {lsize : Lsize} {th : Thread isaLSE2} {tm : Memory} {ar : Arena}
  {hu : Nat}

/-- **A frame run keeps `AllocInvAt`**: pending, the control is at the
allocation and the run is empty; idle, the run holds nothing. -/
theorem allocInvAt_frameRun {c c' : Ctl} {fs fs' : List TermRun.Frame}
    (h : AllocInvAt Λ lbl lsize th tm ar.heap ar.cells ar.ctr ar.units ar.off hu c)
    (hr : FrameRun p (c, fs) (c', fs')) :
    AllocInvAt Λ lbl lsize th tm ar.heap ar.cells ar.ctr ar.units ar.off hu c' := by
  rcases h with ⟨hh, ex, hpd, ha⟩ | ⟨hn, hctr, ha⟩
  · obtain ⟨x, n, τ, e, ⟨a, ta, ws, ht, hea, hk⟩ | ⟨-, a, ws, ht, -⟩, -⟩ := id hpd
    · obtain ⟨rfl, -⟩ := Prod.mk.inj (FrameRun.eq_of_newBuf hr ht hea hk)
      exact .inl ⟨hh, ex, hpd, ha⟩
    · obtain ⟨rfl, -⟩ := Prod.mk.inj (FrameNew.FrameRun.eq_of_new hr ht)
      exact .inl ⟨hh, ex, hpd, ha⟩
  · rcases FrameRun.hold_of hr with he | hn'
    · obtain ⟨rfl, -⟩ := Prod.mk.inj he
      exact .inr ⟨hn, hctr, ha⟩
    · exact .inr ⟨fun w h => (by simp only at hn'; rw [hn'] at h; cases h), hctr, ha⟩

/-- **The heap use of the one-thread configuration** with its thread
replaced by one of the same allocation count and box label. -/
theorem heapUse_one {s : TermRun.Cfg} {th0 th' : TermRun.TTh} (hs0 : s.ths = #[th0])
    (hn : th'.nalloc = th0.nalloc) (ht : th'.tidLbl = th0.tidLbl) : heapUse { s with ths := #[th'] } = heapUse s := by
  have h0 : s.ths[0]? = some th0 := by rw [hs0]; rfl
  exact Spike.Lib.HeapPres.heapUse_set (s' := { s with ths := #[th'] }) h0 rfl (set_one hs0).symm hn ht

/-- **The header store fulfilling a promise while pending** at `hu` (the
fulfilment twin of `AllocInvAt.header`): the promised message `q`, off the
counter, below the pending buffer's base, is recorded as an exception, the
memory unchanged and `q` no longer outstanding. -/
theorem _root_.Spike.Lib.AllocInvAt.header_fulfil {c : Ctl}
    (h : AllocInvAt Λ lbl lsize th tm ar.heap ar.cells ar.ctr ar.units ar.off hu c)
    (hh : c.hold = some (ar.ctr, TermRun.cst (.num hu))) {x : String} {a : At} {τ : Ty} {e : Expr} {ta : Ty}
    {ws : List TermRun.Word} {k : Nat} (ht : c.term = .let_ x (.newBuf a τ) e)
    (hea : TermRun.evalAt c.env a = some (ta, ws)) (hk : TermRun.numOf ws = some k) {q : Time} {w : Msg}
    (hq : tm.get? q = some w) (hw : w.loc ≠ wordLoc ar.ctr)
    (hlt : w.loc.addr.toNat < ar.heap + 16 * hu + ar.off k τ) (hnd : th.prom.Nodup) {t' : Thread isaLSE2}
    (hp : t'.prom = th.prom.erase q) :
    AllocInvAt Λ lbl lsize t' tm ar.heap ar.cells ar.ctr ar.units ar.off hu c := by
  have hmem : ∀ k', k' ≠ q → (k' ∈ t'.prom ↔ k' ∈ th.prom) := fun k' hne => by
    rw [hp]; exact List.Nodup.mem_erase_iff hnd |>.trans (and_iff_right hne)
  rcases h with ⟨-, ex, hpd, ha⟩ | ⟨hn, -⟩
  · obtain ⟨hctr, hex⟩ := hpd.newBuf ht hea hk
    refine .inl ⟨hh, fun a' => ex a' ∨ a' = w.loc.addr.toNat,
      AllocInv.Pending.of_newBuf ht hea hk (hctr.prom_congr fun k'' w' hg hl => hmem k'' fun he => ?_) ?_,
      ⟨ha.hu_le, ha.sub, ha.align, ha.disj, ha.base, ha.zero, fun k'' w' hg hfr hx => ?_⟩⟩
    · subst he; rw [hq] at hg; cases hg; exact hw hl
    · rintro a' (h | rfl)
      · exact hex a' h
      · exact hlt
    · by_cases he : k'' = q
      · subst he; rw [hq] at hg; cases hg
        exact absurd (.inr rfl) hx
      · exact (hmem k'' he).mpr (ha.fresh k'' w' hg hfr fun h' => hx (.inl h'))
  · exact absurd hh (hn _)

/-- **The box header store fulfilling a promise while pending** at `hu`
(`AllocInvAt.header_fulfil` at `let x = new a in e`): below the pending
box's base. -/
theorem _root_.Spike.Lib.AllocInvAt.header_fulfilBox {c : Ctl}
    (h : AllocInvAt Λ lbl lsize th tm ar.heap ar.cells ar.ctr ar.units ar.off hu c)
    (hh : c.hold = some (ar.ctr, TermRun.cst (.num hu))) {x : String} {a : At} {e : Expr} {ty : Ty}
    {ws : List TermRun.Word} (ht : c.term = .let_ x (.new a) e)
    (hea : TermRun.evalAt c.env a = some (ty, ws)) {q : Time} {w : Msg}
    (hq : tm.get? q = some w) (hw : w.loc ≠ wordLoc ar.ctr)
    (hlt : w.loc.addr.toNat < ar.heap + 16 * hu + ar.off 1 ty) (hnd : th.prom.Nodup) {t' : Thread isaLSE2}
    (hp : t'.prom = th.prom.erase q) :
    AllocInvAt Λ lbl lsize t' tm ar.heap ar.cells ar.ctr ar.units ar.off hu c := by
  have hmem : ∀ k', k' ≠ q → (k' ∈ t'.prom ↔ k' ∈ th.prom) := fun k' hne => by
    rw [hp]; exact List.Nodup.mem_erase_iff hnd |>.trans (and_iff_right hne)
  rcases h with ⟨-, ex, hpd, ha⟩ | ⟨hn, -⟩
  · obtain ⟨hctr, hex⟩ := hpd.box ht hea
    refine .inl ⟨hh, fun a' => ex a' ∨ a' = w.loc.addr.toNat,
      AllocInv.Pending.of_box ht hea (hctr.prom_congr fun k'' w' hg hl => hmem k'' fun he => ?_) ?_,
      ⟨ha.hu_le, ha.sub, ha.align, ha.disj, ha.base, ha.zero, fun k'' w' hg hfr hx => ?_⟩⟩
    · subst he; rw [hq] at hg; cases hg; exact hw hl
    · rintro a' (h | rfl)
      · exact hex a' h
      · exact hlt
    · by_cases he : k'' = q
      · subst he; rw [hq] at hg; cases hg
        exact absurd (.inr rfl) hx
      · exact (hmem k'' he).mpr (ha.fresh k'' w' hg hfr fun h' => hx (.inl h'))
  · exact absurd hh (hn _)

/-! ## Rows and landings -/

variable {I : InvS} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {own : OwnS}
  {ab : Option (State → Prop)} {Cl : State → Prop}

/-- **The row of a pair of the fragment** (`NodesS.row` with the arena):
the source takes a frame run to `(c₁, fs₁)`, from which the instruction is
an `Out` row under `msOfA` landing in `PendA` at `fs₁`. -/
theorem NodesA.row (hN : NodesA Λ p μ rd G own ar I) {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (hI : I lbl lsize s c fs) (hnt : ∀ a, μ.site .take = some a → pcOf s ≠ a) :
    ∃ c₁ fs₁, FrameRun p (c, fs) (c₁, fs₁) ∧ own s fs₁ = own s fs ∧
      Out p lbl (msOfA Λ μ rd G own ar I lbl lsize fs₁) (fun s' c' => PendA p I lbl lsize s' c' fs₁) s c₁ := by
  cases hN.out _ _ _ _ _ hI hnt (fun _ h => h) with
  | pre c₁ fs₁ hr h =>
    refine ⟨c₁, fs₁, hr, hN.ownRun _ _ _ _ _ _ _ hr (.inl hI), h.mono fun s' c' h' => ⟨?_, h'⟩⟩
    rintro h0 a hc
    obtain ⟨c'', fs'', hr', h''⟩ := h'
    cases hr'.eq_of_stuck (.inr ⟨h0, a, hc⟩)
    exact hN.noRet _ _ _ _ (h0 ▸ h'') a hc
  | frame s' c' fs' he hr hx =>
    obtain ⟨c'', fs'', hr', hx⟩ := hx
    refine ⟨c, fs, .refl _, rfl, .silent s' c he (.refl c) ⟨?_, c'', fs'', hr.trans hr', hx⟩⟩
    exact fun h0 => hN.noRet _ _ _ _ (h0 ▸ hI)

/-- **The row of a pair of the fragment off the output `write` and off
`Cl`**, for rows under any `msOfAX … ab`: `NodesA.row`, the row under `msOfA`
(an `Out.emit` row is at a `write(1, …)`, which `hne` excludes; `Out.unBW`). -/
theorem NodesA.rowXC (hN : NodesA Λ p μ rd G own ar I ab Cl) {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (hI : I lbl lsize s c fs) (hnt : ∀ a, μ.site .take = some a → pcOf s ≠ a)
    (hne : abi.atSys s = true → ∀ buf n, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) ≠ some (.write 1 buf n))
    (hcl : abi.atSys s = true → ¬ Cl s) :
    ∃ c₁ fs₁, FrameRun p (c, fs) (c₁, fs₁) ∧ own s fs₁ = own s fs ∧
      Out p lbl (msOfA Λ μ rd G own ar I lbl lsize fs₁) (fun s' c' => PendA p I lbl lsize s' c' fs₁) s c₁ := by
  have hun : ∀ {fs₁ : List TermRun.Frame} {X : Frag isaLSE2} {c₁ : Ctl},
      Out p lbl (msOfAX Λ μ p rd G own ar I ab lbl lsize fs₁) X s c₁ →
        Out p lbl (msOfA Λ μ rd G own ar I lbl lsize fs₁) X s c₁ := by
    intro fs₁ X c₁ h
    cases ab with
    | none => exact h
    | some Ab =>
      exact Out.unBW h fun K hK ha => by
        cases hK
        exact hne ha
  cases hN.out _ _ _ _ _ hI hnt hcl with
  | pre c₁ fs₁ hr h =>
    refine ⟨c₁, fs₁, hr, hN.ownRun _ _ _ _ _ _ _ hr (.inl hI), (hun h).mono fun s' c' h' => ⟨?_, h'⟩⟩
    rintro h0 a hc
    obtain ⟨c'', fs'', hr', h''⟩ := h'
    cases hr'.eq_of_stuck (.inr ⟨h0, a, hc⟩)
    exact hN.noRet _ _ _ _ (h0 ▸ h'') a hc
  | frame s' c' fs' he hr hx =>
    obtain ⟨c'', fs'', hr', hx⟩ := hx
    refine ⟨c, fs, .refl _, rfl, .silent s' c he (.refl c) ⟨?_, c'', fs'', hr.trans hr', hx⟩⟩
    exact fun h0 => hN.noRet _ _ _ _ (h0 ▸ hI)

/-- **The row of a pair of the fragment off the output `write`**, for rows
under any `msOfAX … ab` (`NodesA.rowXC`, no `Cl` at the default). -/
theorem NodesA.rowX (hN : NodesA Λ p μ rd G own ar I ab) {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (hI : I lbl lsize s c fs) (hnt : ∀ a, μ.site .take = some a → pcOf s ≠ a)
    (hne : abi.atSys s = true → ∀ buf n, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) ≠ some (.write 1 buf n)) :
    ∃ c₁ fs₁, FrameRun p (c, fs) (c₁, fs₁) ∧ own s fs₁ = own s fs ∧
      Out p lbl (msOfA Λ μ rd G own ar I lbl lsize fs₁) (fun s' c' => PendA p I lbl lsize s' c' fs₁) s c₁ :=
  hN.rowXC hI hnt hne fun _ h => h

/-- **The row of a pair of the fragment off a system call**, any `Cl`
(`NodesA.rowXC`: `out`'s premise is about system calls only). -/
theorem NodesA.rowNS (hN : NodesA Λ p μ rd G own ar I ab Cl) {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (hI : I lbl lsize s c fs) (hnt : ∀ a, μ.site .take = some a → pcOf s ≠ a) (hns : abi.atSys s = false) :
    ∃ c₁ fs₁, FrameRun p (c, fs) (c₁, fs₁) ∧ own s fs₁ = own s fs ∧
      Out p lbl (msOfA Λ μ rd G own ar I lbl lsize fs₁) (fun s' c' => PendA p I lbl lsize s' c' fs₁) s c₁ :=
  hN.rowXC hI hnt (fun h => absurd (hns.symm.trans h) Bool.false_ne_true)
    fun h => absurd (hns.symm.trans h) Bool.false_ne_true

/-- `PendA`'s state is one of the fragment's. -/
theorem PendA.inv {s : State} {c : Ctl} {fs : List TermRun.Frame} (h : PendA p I lbl lsize s c fs) :
    ∃ c' fs', I lbl lsize s c' fs' := by
  obtain ⟨-, c', fs', -, h⟩ := h; exact ⟨c', fs', h⟩

/-- `PendA`'s pair is off `main`'s return. -/
theorem PendA.noRet {s : State} {c : Ctl} {fs : List TermRun.Frame} (h : PendA p I lbl lsize s c fs) :
    fs = [] → ∀ a, c.term ≠ .ret a := h.1

/-- A pair of the fragment is a `PendA` one (with the empty run). -/
theorem PendA.of (hN : NodesA Λ p μ rd G own ar I ab Cl) {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (h : I lbl lsize s c fs) : PendA p I lbl lsize s c fs :=
  ⟨fun h0 => hN.noRet _ _ _ _ (h0 ▸ h), c, fs, .refl _, h⟩

/-- **A pending frame run is taken** (`pend_run` with the arena): the
allocation invariant moves along the run (`allocInvAt_frameRun`) at the same
heap use (`heapUse_one`). -/
theorem pend_runA (hP : HookOK P p) (hN : NodesA Λ p μ rd G own ar I ab Cl) {rS : Range}
    {Tk : State → Prop} {t : T.M.Cfg} {s : TermRun.Cfg}
    (h : PreJA Λ P p G own (PendA p I) rS Tk μ ar t s) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ PreSA Λ P p G own I rS Tk μ ar t s' := by
  obtain ⟨th, th0, j, lbl, lsize, ts, hl, pm, hd, hth, hk, hz, hh, hwr, hcert, hs0, hσ, hp,
    ⟨hnr, c₂, fs₂, hr, hI⟩, hhi, hw, hb, hinv, hown, hmi, hfi, hgi, hoo, hai, hfr, hco, tr, hreach⟩ := h
  have hrun := frun_one (q := (⟨th0.term, th0.env, hd⟩, th0.stack)) hP hr hs0 rfl rfl hσ rfl hp hnr
    (fun h0 => hN.noRet _ _ _ _ (by simp only at h0; subst h0; exact hI))
  refine ⟨_, hrun, th, { th0 with term := c₂.term, env := c₂.env, stack := fs₂ }, j, lbl, lsize, ts, hl, pm, c₂.hold,
    hth, hk, hz, hh, hwr, hcert, rfl, hσ, hp, hI, holdInvA_frameRun hr hhi, hw, hb, hinv, hown, hmi, hfi, hgi, ?_,
    ?_, (by rw [TermRun.Cfg.n, hs0] at hfr; exact hfr), hco, _, reach_run hreach hrun⟩
  · show ExtRows.OwnOk (own th.st fs₂) _ _
    rw [hN.ownRun _ _ _ _ _ _ _ hr (.inr hI)]; exact hoo
  · rw [heapUse_one (th' := { th0 with term := c₂.term, env := c₂.env, stack := fs₂ }) hs0 rfl rfl]
    exact allocInvAt_frameRun hai hr

/-- **A frame run lands in `PreJA`** over any fragment `J` (`pre_localJ`
with the arena): the allocation invariant given at the run's end, at the
heap use the run keeps. -/
theorem pre_localJA (hP : HookOK P p) {J : InvS} {t' : T.M.Cfg} {s : TermRun.Cfg}
    {u : Thread isaLSE2} {th0 : TermRun.TTh} {ts : Nat → Option Nat} {c' : Ctl}
    {fs' : List TermRun.Frame} {rS : Range} {Tk : State → Prop} {hl : List (Nat × Range)} {pm : _root_.Mem 64}
    {hd : Option (Nat × TermRun.Word)}
    (hth : t'.1.threads = #[u]) (hk : t'.2 = KS E Λ 0 hl pm) (hz : ∀ a, Kernel.byte pm a = 0)
    (hh : HeldOk Λ rS Tk u.st hl)
    (hc : CertOkC Arch.armv8 (Kernel.certSem abi Arch.armv8 μ t'.2 0) 0 u t'.1.mem) (hs0 : s.ths = #[th0])
    (hσ : th0.σs = []) (hp : th0.promises = []) (hJ : J lbl lsize u.st c' fs') (hw : WideSt u.st)
    (hb : u.Bnd t'.1.mem.last) (hinv : Inv1 Λ lbl lsize ts u t'.1.mem s.mem) (hown : OwnMsgs t'.1.mem)
    (hmi : MemIn Λ t'.1.mem) (hfi : MemFits t'.1.mem) (hgi : MemInv G t'.1.mem)
    (hoo : ExtRows.OwnOk (own u.st fs') t'.1.mem u.prom)
    (hai : AllocInvAt Λ lbl lsize u t'.1.mem ar.heap ar.cells ar.ctr ar.units ar.off (heapUse s) c')
    (hfr : AllocInv.FreshInv lbl s.lbase s.n 0 th0.nalloc) (hco : CtrOff ar lbl lsize)
    (hre : ∃ tr, (SrcSem.source P p).Reach tr s)
    (hhi : HoldInvA ar lbl lsize s.mem hd) (hcr : th0.stack = [] → ∀ a, th0.term ≠ .ret a)
    (hcr' : fs' = [] → ∀ a, c'.term ≠ .ret a) (hr : FrameRun p (⟨th0.term, th0.env, hd⟩, th0.stack) (c', fs')) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ PreJA Λ P p G own J rS Tk μ ar t' s' := by
  have hrun := frun_one hP hr hs0 rfl rfl hσ rfl hp hcr hcr'
  obtain ⟨tr, hre⟩ := hre
  exact ⟨_, hrun, u, { th0 with term := c'.term, env := c'.env, stack := fs' }, 0, lbl, lsize, ts, hl, pm, c'.hold,
    hth, ⟨E, hk⟩, hz, hh, .inl rfl, hc, rfl, hσ, hp, hJ, holdInvA_frameRun hr hhi, hw, hb, hinv, hown, hmi, hfi, hgi,
    hoo, by rw [heapUse_one (th' := { th0 with term := c'.term, env := c'.env, stack := fs' }) hs0 rfl rfl]; exact hai,
    by rw [TermRun.Cfg.n, hs0] at hfr; exact hfr, hco, _, reach_run hre hrun⟩

/-- **A landing over `PendA` is a step of the relation**: the pending frame
run taken (`pend_runA`). -/
theorem pend_landA (hP : HookOK P p) (hN : NodesA Λ p μ rd G own ar I ab Cl) {rS : Range}
    {Tk : State → Prop} {t : T.M.Cfg} {s s₂ : TermRun.Cfg} (hrun : (SrcSem.source P p).Run s [] s₂)
    (h : PreJA Λ P p G own (PendA p I) rS Tk μ ar t s₂) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ RSA Λ P p G own I rS Tk μ ar t s' := by
  obtain ⟨s', hr, hpre⟩ := pend_runA hP hN h
  exact ⟨s', run_trans0 hrun hr, .inl hpre⟩

/-- **A pending frame run is taken**, the ranges held by `H` (`pend_runA`
over `H`). -/
theorem pend_runAH (hP : HookOK P p) (hN : NodesA Λ p μ rd G own ar I ab Cl)
    {H : State → List (Nat × Range) → Prop} {t : T.M.Cfg} {s : TermRun.Cfg}
    (h : PreJAH Λ P p G own (PendA p I) H μ ar t s) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ PreSAH Λ P p G own I H μ ar t s' := by
  obtain ⟨th, th0, j, lbl, lsize, ts, hl, pm, hd, hth, hk, hz, hh, hwr, hcert, hs0, hσ, hp,
    ⟨hnr, c₂, fs₂, hr, hI⟩, hhi, hw, hb, hinv, hown, hmi, hfi, hgi, hoo, hai, hfr, hco, tr, hreach⟩ := h
  have hrun := frun_one (q := (⟨th0.term, th0.env, hd⟩, th0.stack)) hP hr hs0 rfl rfl hσ rfl hp hnr
    (fun h0 => hN.noRet _ _ _ _ (by simp only at h0; subst h0; exact hI))
  refine ⟨_, hrun, th, { th0 with term := c₂.term, env := c₂.env, stack := fs₂ }, j, lbl, lsize, ts, hl, pm, c₂.hold,
    hth, hk, hz, hh, hwr, hcert, rfl, hσ, hp, hI, holdInvA_frameRun hr hhi, hw, hb, hinv, hown, hmi, hfi, hgi, ?_,
    ?_, (by rw [TermRun.Cfg.n, hs0] at hfr; exact hfr), hco, _, reach_run hreach hrun⟩
  · show ExtRows.OwnOk (own th.st fs₂) _ _
    rw [hN.ownRun _ _ _ _ _ _ _ hr (.inr hI)]; exact hoo
  · rw [heapUse_one (th' := { th0 with term := c₂.term, env := c₂.env, stack := fs₂ }) hs0 rfl rfl]
    exact allocInvAt_frameRun hai hr

/-- **A frame run lands in `PreJAH`** over any fragment `J` (`pre_localJA`
over `H`). -/
theorem pre_localJAH (hP : HookOK P p) {J : InvS} {H : State → List (Nat × Range) → Prop} {t' : T.M.Cfg}
    {s : TermRun.Cfg} {u : Thread isaLSE2} {th0 : TermRun.TTh} {ts : Nat → Option Nat} {c' : Ctl}
    {fs' : List TermRun.Frame} {hl : List (Nat × Range)} {pm : _root_.Mem 64}
    {hd : Option (Nat × TermRun.Word)}
    (hth : t'.1.threads = #[u]) (hk : t'.2 = KS E Λ 0 hl pm) (hz : ∀ a, Kernel.byte pm a = 0)
    (hh : H u.st hl)
    (hc : CertOkC Arch.armv8 (Kernel.certSem abi Arch.armv8 μ t'.2 0) 0 u t'.1.mem) (hs0 : s.ths = #[th0])
    (hσ : th0.σs = []) (hp : th0.promises = []) (hJ : J lbl lsize u.st c' fs') (hw : WideSt u.st)
    (hb : u.Bnd t'.1.mem.last) (hinv : Inv1 Λ lbl lsize ts u t'.1.mem s.mem) (hown : OwnMsgs t'.1.mem)
    (hmi : MemIn Λ t'.1.mem) (hfi : MemFits t'.1.mem) (hgi : MemInv G t'.1.mem)
    (hoo : ExtRows.OwnOk (own u.st fs') t'.1.mem u.prom)
    (hai : AllocInvAt Λ lbl lsize u t'.1.mem ar.heap ar.cells ar.ctr ar.units ar.off (heapUse s) c')
    (hfr : AllocInv.FreshInv lbl s.lbase s.n 0 th0.nalloc) (hco : CtrOff ar lbl lsize)
    (hre : ∃ tr, (SrcSem.source P p).Reach tr s)
    (hhi : HoldInvA ar lbl lsize s.mem hd) (hcr : th0.stack = [] → ∀ a, th0.term ≠ .ret a)
    (hcr' : fs' = [] → ∀ a, c'.term ≠ .ret a) (hr : FrameRun p (⟨th0.term, th0.env, hd⟩, th0.stack) (c', fs')) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ PreJAH Λ P p G own J H μ ar t' s' := by
  have hrun := frun_one hP hr hs0 rfl rfl hσ rfl hp hcr hcr'
  obtain ⟨tr, hre⟩ := hre
  exact ⟨_, hrun, u, { th0 with term := c'.term, env := c'.env, stack := fs' }, 0, lbl, lsize, ts, hl, pm, c'.hold,
    hth, ⟨E, hk⟩, hz, hh, .inl rfl, hc, rfl, hσ, hp, hJ, holdInvA_frameRun hr hhi, hw, hb, hinv, hown, hmi, hfi, hgi,
    hoo, by rw [heapUse_one (th' := { th0 with term := c'.term, env := c'.env, stack := fs' }) hs0 rfl rfl]; exact hai,
    by rw [TermRun.Cfg.n, hs0] at hfr; exact hfr, hco, _, reach_run hre hrun⟩

/-- **A landing over `PendA` is a step of the relation**, the ranges held by
`H` (`pend_landA` over `H`). -/
theorem pend_landAH (hP : HookOK P p) (hN : NodesA Λ p μ rd G own ar I ab Cl)
    {H : State → List (Nat × Range) → Prop} {t : T.M.Cfg} {s s₂ : TermRun.Cfg}
    (hrun : (SrcSem.source P p).Run s [] s₂) (h : PreJAH Λ P p G own (PendA p I) H μ ar t s₂) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ RSAH Λ P p G own I H μ ar t s' := by
  obtain ⟨s', hr, hpre⟩ := pend_runAH hP hN h
  exact ⟨s', run_trans0 hrun hr, .inl hpre⟩

end Spike.Lib.A64ConsumerA
