/-
**The runtime's own states inside `W2`** (x86-64; the twin of
`Spike/Lib/LowerA64/RtW2.lean`): `W2Part` (`Spike/Lib/LowerX64/W2Blk.lean`)
at a runtime state from facts of the state alone, so that the runtime's
blocks (`_start`'s, `scc_rt_start`'s, `scc_rt_main`'s before its setup
call) are inside `W2` from the phase table's `SFacts` at the source start's
control and three per-state facts.

The runtime writes shared memory (the TCB, the pin, the stack's lock, next
and free words) but never the arena's heap nor its counter (`WrOff`): every
location it writes is allowed by the arena at every control (`ArenaW`'s
off-heap case), and the counter's row is vacuous (`wrOkA_of_wrOff`). The
`print` output fact is vacuous at `SFacts` with no write tail (no `write`).

- `WrOff`: every location the instruction writes is off the arena's heap
  and not its counter;
- `wrOkA_of_wrOff`: `WrOkA` from `WrOff`;
- `w2Part_of_wrOff`: `W2Part` from the abort phase, the placement, `WrOff`
  and `SFacts` at the state (any control);
- `BlkW.w2_rt`, `NodeW.w2_rt`: a block's / a node's states inside `W2` from
  `SFacts` at the source start's control (`dumN`) and a block / node
  obligation of the abort phase, the placement and `WrOff`.
-/
import Spike.Lib.LowerX64.W2Blk

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region FrameRun)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW BlkW ND At)
open Spike.Lib.X64.AllocG (dumN)
open Spike.Lib.LowerNode (FrOk2 ZBad)

variable {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : Own} {rS : Range} {Tk : State → Prop} {ar : Arena} {J : InvS} {Dt Ab : State → Prop} {lbl lbl0 : Lbl}
  {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame}

/-- **The instruction writes neither the arena's heap nor its counter**:
every location it writes (`WrAt`) is off `[heap, heap + 16 · cells)` and
not the counter's word. -/
def WrOff (ar : Arena) (s : State) : Prop :=
  ∀ L, WrAt s L → L ≠ ar.ctrLoc ∧ ¬ (ar.heap ≤ L.addr.toNat ∧ L.addr.toNat < ar.heap + 16 * ar.cells)

/-- **The arena's write obligation off its heap and counter**: every
location is allowed (`ArenaW`'s off-heap case), the counter is not
written. -/
theorem wrOkA_of_wrOff {ms : MemSide isa} {X : Frag isa} (h : WrOff ar s) :
    WrOkA ar lbl lsize ms X s c :=
  ⟨fun L hL => .inr (.inl (h L hL).2), fun hL => absurd rfl (h _ hL).1⟩

/-- **`W2Part` at a state off the arena**: the abort phase, the frames
placed, `WrOff`, and `SFacts` at the state with no write tail (at any
control), so no `write`. -/
theorem w2Part_of_wrOff {c' : Ctl} (hab : AbSt μ Ab s) (hpl : PlacedS Λ lbl s c fs) (hwr : WrOff ar s)
    (hS : SFacts Λ μ own rS Tk lbl0 s c') : W2Part Λ μ p rd G own ar J Ab lbl lsize fs s c :=
  ⟨hab, hpl, fun _ _ _ _ => wrOkA_of_wrOff hwr, fun hs _ _ hd => (hS.wrTail hs 1 _ _ hd).elim⟩

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {K : State → State → Prop}

/-- **A runtime block's states inside `W2`** at the frames `fs`: `SFacts`
at the source start's control (`dumN`, as the phase table's producers give
it) not moved by `K`, the abort phase, the placement and `WrOff` at the
block's states, and at every control of the node's invariant `main`'s `ret`
excluded and `FrOk2`. -/
theorem BlkW.w2_rt (hp : ProgNoS ZBad p) {n : ND} {blk : List (Directive × Nat)}
    (hS : BlkW (fun s c => SFacts Λ μ own rS Tk lbl0 s c) K exe endPc R F (dumN n) blk)
    (hX : BlkW (fun s c => AbSt μ Ab s ∧ PlacedS Λ lbl s c fs ∧ WrOff ar s) (fun _ _ => False) exe endPc R F n
      blk)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F n blk :=
  BlkW.w2 hp hS (fun s σ c he hn hd hpc hA hF hJn k hk m hA' hD =>
    let h1 := hS s σ _ he hn hd hpc hA hF ⟨rfl, c, hJn⟩ k hk m hA' hD
    let h2 := hX s σ c he hn hd hpc hA hF hJn k hk m hA' hD
    ⟨w2Part_of_wrOff h2.1.1 h2.1.2.1 h2.1.2.2 h1.1, fun _ h => h⟩) hJ

/-- **A runtime node's states inside `W2`** at the frames `fs` (as
`BlkW.w2_rt`). -/
theorem NodeW.w2_rt (hp : ProgNoS ZBad p) {n : ND}
    (hS : NodeW (fun s c => SFacts Λ μ own rS Tk lbl0 s c) K exe endPc R F (dumN n))
    (hX : NodeW (fun s c => AbSt μ Ab s ∧ PlacedS Λ lbl s c fs ∧ WrOff ar s) (fun _ _ => False) exe endPc R F n)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    NodeW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F n :=
  NodeW.w2 hp hS (fun s c hA => by
    obtain ⟨h1, h2, h3, h4, σ, hAb, hF, hJn⟩ := hA
    have hS' := hS s _ ⟨h1, h2, h3, h4, σ, hAb, hF, rfl, c, hJn⟩
    have hX' := hX s c ⟨h1, h2, h3, h4, σ, hAb, hF, hJn⟩
    exact ⟨w2Part_of_wrOff hX'.1.1 hX'.1.2.1 hX'.1.2.2 hS'.1, fun _ h => h⟩) hJ

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.BlkW.w2_rt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BlkW.w2_rt

/-- info: 'Spike.Lib.LowerX64.NodeW.w2_rt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NodeW.w2_rt

end Spike.Lib.LowerX64
