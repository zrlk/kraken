/-
**The allocation-capable consumer through `print`'s `write(1, buf, n)`** on
the canonical x86-64 target: the relation `RSA`
(`Spike/Lib/X64ConsumerA.lean`) with a third disjunct for the pairs in the
middle of the output `write`, and the rows under `msOfAB` (`NodesA … (some
Ab)`, `Spike/Lib/X64ConsumerAB.lean`).

During the kernel's `write(1, buf, n)` the thread's state is constant: the
progress is the kernel state's count `wr` alone. The source runs `print`'s
loop, one `emit` per byte, so its control changes at every byte. `EmitSA`
relates the two: the source at `Pw j`, `j = wr`, of the `Out.emit` row of the
`syscall` (`EmitJ`), over `PreJA`.

- `EmitBody`: an `Out.emit` row's byte and return clauses, the byte step
  `print`'s (`ByteOut`), its landing `X`.
- `EmitA`: the emit rows: from a pair of the fragment at a `write(1, buf,
  n)`, a frame run to the row's control, inside a call (the frames not
  empty, placed: `FramesPlaced`, `Spike/Lib/X64PlacedS.lean`), the row's
  local run to `Pw 0`, its clauses, and every `Pw j` control at no hold and
  in `Top`.
- `EmitJ j`: the source at `Pw j` of such a row, `j ≤ n`.
- `EmitSA`, `Wr1Zero`, `RSAE`: `PreJA` over `EmitJ (wr)`; no byte of the
  output out; the relation `PreSA` (with `Wr1Zero`) `∨ EmitSA`, with the
  private-memory invariant (`PrivInv`), or `PostS`.
-/
import Spike.Lib.X64ConsumerAB
import Spike.Lib.X64ConsumerASys
import Spike.Lib.X64PlacedS
import Spike.Lib.X64DmemPriv
import Spike.Lib.Src.SrcNum2

namespace Spike.Lib.X64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS
open Spike.Lib.ByteOut (ByteOut)
open Spike.Lib.DmemPriv (PrivInv)

/-- **An `Out.emit` row's clauses** at the `syscall` state `st` of a `write(1,
buf, n)`, over the controls `Pw j`: each byte `j < n` is `print`'s byte step
(`ByteOut`) from `Pw j` into `Pw (j + 1)`; every result `r` the kernel may
return after `j ≤ n` bytes (`WriteRetOk`) resumes the thread (`abi.ret st r`)
in `X` with the source at `Pw j`. -/
def EmitBody (p : Prog) (lbl : Lbl) (X : Frag isa) (st : State) (buf n : Nat) (Pw : Nat → Ctl → Prop) :
    Prop :=
  (∀ j < n, ∀ c1, Pw j c1 → ByteOut (I := isa) p lbl st (buf + j) c1 (Pw (j + 1))) ∧
    ∀ j ≤ n, ∀ c1, Pw j c1 → ∀ r ∈ Kernel.results (.write 1 buf n), WriteRetOk j r → X (abi.ret st r) c1

/-- **The emit rows of the fragment**, over the top-frame property `Top`:
from a pair of `I` at a `write(1, buf, n)`, the source takes a frame run to
`(c₁, fs₁)`, inside a call (`fs₁ ≠ []`) whose suspended frames are placed
(`FramesPlaced`); from `c₁` it runs locally to `Pw 0`; the row's clauses
hold (`EmitBody`, landing in `Pend` at `fs₁`); every `Pw j`, `j ≤ n`, has no
hold and is in `Top`. -/
structure EmitA (Λ : Scc.Sem.Layout) (p : Prog) (I : InvS) (Top : Ctl → Prop) : Prop where
  row : ∀ lbl lsize s c fs, I lbl lsize s c fs → abi.atSys s = true → ∀ buf n,
    Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.write 1 buf n) →
    ∃ (c₁ : Ctl) (fs₁ : List TermRun.Frame) (Pw : Nat → Ctl → Prop),
      FrameRun p (c, fs) (c₁, fs₁) ∧ fs₁ ≠ [] ∧ FramesPlaced Λ lbl s fs₁ ∧
      (∃ c', LocalRun p c₁ c' ∧ Pw 0 c') ∧ EmitBody p lbl (fun s' c' => Pend p (I lbl lsize) s' c' fs₁) s buf n Pw ∧
      ∀ j ≤ n, ∀ c', Pw j c' → c'.hold = none ∧ Top c'

/-- **The source `j` bytes into an emit row** at the `syscall` state `st`: a
pair `(c₀, fs₀)` of `I` at `st` with a frame run to `(c₁, fs)`, the
`write(1, buf, n)` decoded, the row's clauses over `Pw`, the suspended
frames placed, and the source at `Pw j`, `j ≤ n`, with no hold and in
`Top`. -/
def EmitJ (Λ : Scc.Sem.Layout) (p : Prog) (I : InvS) (Top : Ctl → Prop) (j : Nat) : InvS :=
  fun lbl lsize st c fs =>
    c.hold = none ∧ Top c ∧ fs ≠ [] ∧ FramesPlaced Λ lbl st fs ∧ abi.atSys st = true ∧
      ∃ (c₀ : Ctl) (fs₀ : List TermRun.Frame) (c₁ : Ctl) (buf n : Nat) (Pw : Nat → Ctl → Prop),
        I lbl lsize st c₀ fs₀ ∧ FrameRun p (c₀, fs₀) (c₁, fs) ∧
        Kernel.decode abi.nrs (abi.nr st) (abi.arg st) = some (.write 1 buf n) ∧
        EmitBody p lbl (fun s' c' => Pend p (I lbl lsize) s' c' fs) st buf n Pw ∧
        (∀ i ≤ n, ∀ c', Pw i c' → c'.hold = none ∧ Top c') ∧ j ≤ n ∧ Pw j c

/-- **In the middle of the output `write`**: `PreJA` over `EmitJ` at the
kernel's count of thread 0 (`wr 0`). -/
def EmitSA (Λ : Scc.Sem.Layout) (P : SrcSem.SrcParams) (p : Prog) (G : Loc → Val → Prop) (own : OwnS) (I : InvS)
    (Top : Ctl → Prop) (rS : Range) (Tk : State → Prop) (μ : Marks) (ar : Arena) (t : T.M.Cfg)
    (s : TermRun.Cfg) : Prop :=
  PreJA Λ P p G own (EmitJ Λ p I Top (t.2.wr 0)) rS Tk μ ar t s

/-- **No byte of the output out** at a pair of the fragment: thread 0 at a
`write(1, …)` has the kernel's count 0 (the bytes of the output are in
`EmitSA`; `PreSA`'s count is a `write` to another descriptor's). -/
def Wr1Zero (t : T.M.Cfg) : Prop :=
  ∀ th buf n, t.1.threads = #[th] → Kernel.callOf abi th = some (.write 1 buf n) → t.2.wr 0 = 0

/-- **The relation through the output `write`**: before the exit, at a
pair of the fragment with no byte of the output out (`PreSA`, `Wr1Zero`)
or in the middle of the output `write` (`EmitSA`), with the private-memory
invariant from the entry `Ent` (`PrivInv`, which gives the byte step's
`hpriv`); or after the exit (`PostSA`). -/
def RSAE (Λ : Scc.Sem.Layout) (P : SrcSem.SrcParams) (p : Prog) (G : Loc → Val → Prop) (own : OwnS) (I : InvS)
    (Top : Ctl → Prop) (rS : Range) (Tk : State → Prop) (μ : Marks) (ar : Arena) (Ent : Entry) (t : T.M.Cfg)
    (s : TermRun.Cfg) : Prop :=
  ((PreSA Λ P p G own I rS Tk μ ar t s ∧ Wr1Zero t ∨ EmitSA Λ P p G own I Top rS Tk μ ar t s) ∧
      PrivInv abi WideSt Λ Ent t) ∨
    PostSA Λ P p rS Tk t s

/-- **Promises are to shared regions** in the middle of the output `write`
(`PromSharedA` over `EmitSA`). With `write` a certification dead end
(`Kernel.prom_nil_of_write`) no promise certifies there and this holds
vacuously. -/
def PromSharedAE (Λ : Scc.Sem.Layout) (P : SrcSem.SrcParams) (p : Prog) (G : Loc → Val → Prop) (own : OwnS)
    (I : InvS) (Top : Ctl → Prop) (rS : Range) (Tk : State → Prop) (μ : Marks) (ar : Arena) : Prop :=
  ∀ t s th w, EmitSA Λ P p G own I Top rS Tk μ ar t s → t.1.threads = #[th] → w.tid = 0 →
    CertOkC Arch.tso (Kernel.certSem abi Arch.tso μ t.2 0) 0 (Live.Sem.promThread th t.1.mem w)
      (t.1.mem.append w).1 →
    LocIn Λ.shared w.loc ∧ G w.loc w.val

end Spike.Lib.X64ConsumerA
