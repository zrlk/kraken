/-
**The public statement of the x64 spinlock counter**
(`X64SpinTrees.spinWorker`, register-addressed variant of `spinlock2.kl`): a
wrapper of `X64SpinInv.x64_counter_spin` (`SLR/X64SpinFinalX.lean`) whose
hypotheses mention only the layout, the number of threads `N`, the lock and
counter addresses `l`, `c`, the thread states and the initial values of the
two words. The x64 twin of `SLR/SwpPublic.lean` (a separate file: the two
ISA syntaxes cannot be imported together).

- The ghost token locations `K`, `F` of `Params`, and the seven ghost fields
  of `SpinLocs`, are chosen here (`ghostParams`): `K j = ⟨0, 2j + 5⟩`,
  `F j = ⟨0, 2j + 6⟩`. They never occur in the program's accesses or in the
  conclusion; no lemma needs them well-sized or address-disjoint from the
  lock and the counter (they differ from `⟨l, 4⟩`, `⟨c, 4⟩` by `bytes`).
- `0 < N` is dropped: for `N = 0` there are no threads, the initial
  configuration is the only reachable one, and the counter is its initial
  value `0`.
- The thread-state hypothesis is `StartState l c`: `Frame` and `AtPos 0`
  without the ghost parameters.

`x64_counter_2'` re-derives the concrete instance
`X64SpinConcrete.x64_counter_2` through the wrapper.
-/
import Kraken.Promising.SLR.X64SpinFinalX
import Kraken.Promising.SLR.X64SpinConcrete

namespace Kraken.Promising.SLR.X64SpinPublic

open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.SLR.Spinlock
open Kraken.Promising.SLR.SpinCommon
open Kraken.Promising.SLR.X64SpinTrees
open Kraken.Promising.SLR.X64SpinInv

section General

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout spinWorker)]

/-- A worker thread at its start, with lock address `l` and counter address
`c`: it runs the laid-out `spinWorker` from its first cell (the label
`worker`) to the end of the text, without declarations (so its accesses are
the 4-byte words `⟨l, 4⟩`, `⟨c, 4⟩`), with `%rdi = l`, `%rsi = c`, and
neither word in its private data memory. -/
structure StartState (l c : BitVec 64) (s : State) : Prop where
  exe : s.exe = layout spinWorker
  decls : s.decls = {}
  endPc : s.endPc = (layout spinWorker).addrOf 14
  pc : s.st.2 = (layout spinWorker).addrOf 0
  rdi : s.st.1.regs.get64 .rdi = l
  rsi : s.st.1.regs.get64 .rsi = c
  dl : Mem.loadInt s.st.1.dmem l 4 = none
  dc : Mem.loadInt s.st.1.dmem c 4 = none

/-- The parameters with the ghost locations chosen: `K j = ⟨0, 2j + 5⟩`,
`F j = ⟨0, 2j + 6⟩` (never 4 bytes wide, odd and even widths). -/
def ghostParams (N : Nat) (l c : BitVec 64) : Params where
  N := N
  l := l
  c := c
  K j := ⟨0, 2 * j + 5⟩
  F j := ⟨0, 2 * j + 6⟩

omit layout hv in
/-- The ghost fields of `SpinLocs` hold for `ghostParams`; only `l ≠ c` is
needed. -/
theorem ghostParams_spinLocs {N : Nat} {l c : BitVec 64} (hlc : l ≠ c) :
    SpinLocs (ghostParams N l c).N (ghostParams N l c).Lk (ghostParams N l c).C
      (ghostParams N l c).K (ghostParams N l c).F where
  lk_c h := hlc (congrArg Loc.addr h)
  k_lk j _ h := by have := congrArg Loc.bytes h; simp [ghostParams] at this
  k_c j _ h := by have := congrArg Loc.bytes h; simp [ghostParams] at this
  f_lk j _ h := by have := congrArg Loc.bytes h; simp [ghostParams] at this
  f_c j _ h := by have := congrArg Loc.bytes h; simp [ghostParams] at this
  k_f i _ j _ h := by have := congrArg Loc.bytes h; simp [ghostParams] at this; omega
  k_inj i _ j _ h := by have := congrArg Loc.bytes h; simp [ghostParams] at this; omega
  f_inj i _ j _ h := by have := congrArg Loc.bytes h; simp [ghostParams] at this; omega

omit hv in
/-- A start state is a `Frame` at position 0 for any ghost parameters. -/
theorem StartState.frame {N : Nat} {l c : BitVec 64} {s : State} (h : StartState l c s) :
    Frame (ghostParams N l c) s ∧ AtPos s 0 :=
  ⟨⟨h.exe, h.decls, h.endPc, h.rdi, h.rsi, h.dl, h.dc⟩, h.pc⟩

omit layout hv in
/-- With no threads, nothing steps: the initial configuration is the only
reachable one. -/
private theorem reachable_nil {A : Arch} {fuel : Nat} {initMem : List (Loc × Val)} {cfg : Config isa}
    (h : Reachable A fuel (Config.init [] initMem) cfg) : cfg = Config.init [] initMem :=
  Reachable.eq_of_init_nil h

/-- **`counter = N` for the x64 spinlock workers**, public form.

For every valid layout of `spinWorker`, every number of threads `N < 2 ^ 32`
and all addresses `l`, `c` whose 4-byte words are disjoint: if `states` consists of `N` threads, each at the
start of the worker with `%rdi = l`, `%rsi = c` (`StartState`), and the
initial memory has the 4-byte words `⟨l, 4⟩` (lock) and `⟨c, 4⟩` (counter)
at `0` (an absent entry counts as `0`), then every configuration `Reachable`
under `Arch.tso` that is final has the counter word at `N`.

What is and is not covered:
- The worker is `spinWorker`, which addresses the lock and the counter
  register-indirectly, `(%rdi)`/`(%rsi)`. The code of `spinlock2.kl`
  addresses them absolutely, `(lock)`/`(counter)`, through data labels the
  runner appends to the text; that program is not covered (it is
  `spinWorker` only after the textual substitution, see
  `SLR/X64SpinConcrete.lean`, "Provenance").
  The literal `spinlock2.kl` program is a separate theorem, to be done after
  the x64 cell files are refactored to depend on the worker only through a
  cell-tree interface.
- The locations are the undeclared 4-byte footprints `⟨l, 4⟩`, `⟨c, 4⟩`
  (`decls = {}`). The `.kl` runner instead declares `lock` and `counter` as
  unsized locations (`⟨l, 0⟩`, `⟨c, 0⟩`, legacy mode); that configuration is
  not covered.
  Known limitation / provenance: apart from `decls` the
  runner's threads are the start states here, but no theorem bridges the
  two, since every cell lemma goes through `exec_eq_of_codeAt`'s
  `decls = {}` (`SLR/AArch64Bridge.lean`, `SLR/X64Bridge.lean`). The
  planned generalisation: `Frame.decls` becomes "`decls.resolve a 4 = .ok
  ⟨a, 4⟩` for `a ∈ {l, c}`", with a lemma `toEv D t = toEv {} t` for trees
  whose accesses resolve identically under `D` and `{}`; declaring the `.kl`
  locations sized (`int lock = 0; int counter = 0;`) then puts the runner's
  configuration under the theorem. The legacy unsized mode would need a
  renaming simulation `⟨a, 0⟩ ↦ ⟨a, 4⟩` of `Reachable` instead.
- `hdisj : Decls.overlaps l 4 c 4 = false`: the two 4-byte words are
  disjoint (which implies `l ≠ c`). The proof does not use it beyond
  `l ≠ c`. It is there because the model (`succs`, hence `Reachable`) treats
  distinct `Loc`s as independent locations even when their byte ranges
  overlap (e.g. `l = c + 2`), where real hardware would not: for overlapping
  words the model is laxer than the hardware, and a conclusion there would
  say nothing about real executions. The hypothesis keeps the theorem inside
  the region where the model matches the hardware (see
  `Kraken/Litmus/KNOWN_GAPS.md`, mixed-size accesses).
- Conclusions are about final configurations only (every thread halted, no
  outstanding promise). A faulting step has no successor, so a run that
  faults never becomes final and is not constrained; a thread whose pc
  leaves the text counts as halted. (For this worker no access faults.)
  The observable predicates (`Config.FaultFree`, `Config.WildFree`,
  `Promising/Faults.lean`) are not concluded here; the N = 2 instance is
  checked against them by the explorer only (`SLR/X64SpinFaults.lean`).
- Faults: faults are not covered by this theorem. What exists:
  `NoFaultRule` is proved for this program's rule (`spinRuleX_noFault`,
  `SLR/X64SpinNoFault.lean`); fault-freedom of the whole program reduces to the open
  statement `ErasedWitness` (`noFaultTheorem_of_erasedWitness`,
  `SLR/Sim/CertExtOpen.lean`), which is not proved; the explorer check finds
  no faults for N = 2 (`SLR/X64SpinFaults.lean`), which is evidence, not proof.
- `N < 2 ^ 32`: the counter is a 32-bit word. -/
theorem x64_counter_public {fuel : Nat} (N : Nat) (l c : BitVec 64)
    (hdisj : Decls.overlaps l 4 c 4 = false) (hN32 : N < 2 ^ 32)
    {states : List isa.State} {initMem : List (Loc × Val)}
    (hst : ∀ s ∈ states, StartState l c s) (hN : states.length = N)
    (hC0 : (Config.init states initMem).mem.initVal ⟨c, 4⟩ = 0)
    (hLk0 : (Config.init states initMem).mem.initVal ⟨l, 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init states initMem) cfg)
    (hf : cfg.final = true) :
    cfg.mem.finalVal ⟨c, 4⟩ = BitVec.ofNat 128 N := by
  have hlc : l ≠ c := by rintro rfl; simp [Decls.overlaps] at hdisj
  rcases Nat.eq_zero_or_pos N with rfl | hN0
  · obtain rfl : states = [] := List.length_eq_zero_iff.mp hN
    obtain rfl := reachable_nil hc
    simpa [Memory.finalVal, Config.init] using hC0
  · exact x64_counter_spin (ghostParams N l c) (ghostParams_spinLocs hlc) hN32
      (fun _ s h => (hst s (List.mem_of_getElem? h)).frame) hN hN0 hC0 hLk0 hc hf

end General

/-! ## The concrete instance through the public theorem -/

section Concrete

open Kraken.Promising.SLR.X64SpinConcrete

attribute [local instance] spinLayout

/-- The thread `worker0` is a start state. -/
theorem worker0_start : StartState P2.l P2.c worker0 :=
  let h := worker0_frame.1
  ⟨h.exe, h.decls, h.endPc, worker0_frame.2, h.rdi, h.rsi, h.dl, h.dc⟩

/-- **`counter = 2`** for two register-addressed workers of `spinlock2.kl`
under `Arch.tso`, derived from `x64_counter_public` (the statement of
`X64SpinConcrete.x64_counter_2`). -/
theorem x64_counter_2' {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init states2 initMem2) c) (hf : c.final = true) :
    c.mem.finalVal P2.C = 2 :=
  x64_counter_public 2 P2.l P2.c (by decide) (by decide)
    (fun s hs => by
      have : s = worker0 := by
        rcases List.mem_cons.mp hs with h | h
        · exact h
        · exact List.mem_singleton.mp h
      subst this; exact worker0_start)
    rfl (by decide) (by decide) hc hf

end Concrete

end Kraken.Promising.SLR.X64SpinPublic
