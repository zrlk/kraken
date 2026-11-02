/-
**hello.w's worker segment's control fact with `RelWS`, x86-64** (the twin of `Spike/Lib/A64HelloZR.lean`): the
fragment `ZHR exe kp` (`ZH` and `RelWS`, `Spike/Lib/X64RelWS.lean`), so that `helloDR`'s invariant at
`Z := fun _ => ZHR exe kp` gives the worker's `hW1` (every instruction's tree writes at most once, a release write),
and the segments' premises at `Z0 ∧ RelWS` (`ZR`): `Z0`'s (`Spike/Lib/X64HelloZ.lean`) and `RelWS`'s
(`Spike/Lib/X64HelloRelZ.lean`, `Spike/Lib/X64HelloRelZP.lean`) combined per node.

- `ZR`, `ZHR`, `ZR.toZHR`.
- `relW1_of_pend`: `RelWS` reads no control, so a pending frame run into a fragment inside `RelWS` gives the
  state's `RelW1 tso`.
- `wcR_hz`, `wcR_hZE`, `wcR_hZC`, `wcR_hZP`, `wcR_hZA`, `wcR_hZu`, `wcR_hZW`, `wcR_hZU`: the worker segment's
  premises at `Z := ZR exe kp`.
- `thrR_hz`, `thrR_hZE`, `thrR_hZT`, `childR_hZc`: the thread worker's and the child's at
  `Z := fun s c => ZR exe kp s c []`.

Unlike AArch64: the release-write part is the per-state `RelWS s` under `Arch.tso` (AArch64: `RelZ`, the trees
only, under `armv8`), as x86-64 wake's (`X64WakeZX`); the prologues are `XProW`s combined by `XProW.and`
(AArch64: `ProW`, `Wake.ZX.ProW.and`); `NodeZA` needs no alignment premise and `NodeZ.toA` no length; the tails'
nodes are at their executing offsets (`HelloTail.NA`, `HThrTail.NA`); `print`'s nodes are stated with their
invariant left free (`Print.N`'s pc and offsets), and the abort path with its runs left free (as `wc_hZA`). The
consumers' premises `passZ_ZHR` and `zStoreOk_ZHR` (over `HelloPassH`, `HelloW1StoreZ`) and the entry's
non-vacuity `wcR_entry` are not stated here.
-/
import Spike.Lib.X64HelloZ
import Spike.Lib.X64HelloRelZ
import Spike.Lib.X64HelloRelZP

namespace Spike.Lib.X64.Flow.Worker.Hello.Z

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.PcRuns (PcIn runsOk inRuns)
open Spike.Lib.X64.Flow.Worker Spike.Lib.X64.Flow.Worker.Hello
open Spike.Lib.X64.Flow.Worker.Hello.Child (cN CN cBlk)
open Spike.Lib.X64.Flow.Worker.Hello.Pass (HPassC helloPassT)
open Spike.Lib.X64WakeMainR (XProW.and)
open SccCode (helloCells)

/-- **`Z0` and `RelWS`**: the segments' control fact. -/
def ZR (exe : _root_.Executable) (kp : Nat) : FragS isa := fun s c fs => Z0 exe kp s c fs ∧ RelWS s

/-- **The worker segment's control fact with `RelWS`**: `ZH` and `RelWS`. -/
def ZHR (exe : _root_.Executable) (kp : Nat) : FragS isa := fun s c fs => ZH exe kp s c fs ∧ RelWS s

/-- The segment's fragment (at `ZR`) is inside `ZHR`. -/
theorem ZR.toZHR {exe : _root_.Executable} {kp : Nat} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (h : ZR exe kp s c fs) (hs : fs = [] → SysSafe s) : ZHR exe kp s c fs :=
  ⟨⟨h.1, hs⟩, h.2⟩

/-- **`hW1` from a pending run**: `RelWS` reads no control, so a pending frame run into a fragment inside `RelWS`
gives the state's `RelW1 tso`. -/
theorem relW1_of_pend {p : Prog} {Zf : FragS isa} (hZ : ∀ s c fs, Zf s c fs → RelWS s) {s : State}
    {c : Ctl} {fs : List TermRun.Frame} (h : Pend p Zf s c fs) :
    ∀ e, isa.exec s = some e → EvTree.RelW1 Arch.tso e :=
  let ⟨_, _, _, h⟩ := h; (hZ _ _ _ h).2

section Inst

variable {exe : _root_.Executable} [hv : Kraken.Executable.ValidLayout exe] {kp : Nat} {endPc : Int64}
  (hp : Lays exe helloCells kp)
include hp

/-- **The abort path** (`hZA`): on a frame at a pc of runs `A` of the cells none of whose bytes is past the store,
the abort's controls at no `unpark` binding, the state in `RelWS`. -/
theorem wcR_hZA {A : List (Label × Nat × Nat)} (hok : runsOk helloCells A = true)
    (hdis : A.all (fun q => (List.range q.2.2).all fun j => !inRuns helloCells Pass.helloPostRuns q.1 j) = true)
    {fr : TermRun.Frame} {c' : Ctl} (hu : NotUnpk c') {s : State} (he : s.exe = exe) (h : PcIn A s)
    (hr : RelWS s) : ZR exe kp s c' [fr] :=
  ⟨wc_hZA hp hok hdis hu he h, hr⟩

omit hv hp in
/-- **On a frame no `unpark` binding** (`hZu`). -/
theorem wcR_hZu : ∀ (fr : TermRun.Frame) s c, ZR exe kp s c [fr] → ∀ x a e, c.term ≠ .let_ x (.ext .unpark a) e :=
  fun _ _ _ h => h.1.2.2.1 (List.cons_ne_nil _ _)

variable (hend : endPc = endOf exe helloCells kp)
include hend

/-- **`wc_worker`'s prologue** (`hz`). -/
theorem wcR_hz {R : Region} {F : MachineData → Prop} {ms : MemSide isa} (hR : R.OK) (hlo : R.lo ≤ -88)
    (hhi : 0 ≤ R.hi) {J : AS → Ctl → Prop} (hb : ∀ σ c, J σ c → ¬ HPassC c) :
    XProW (fun s c => ZR exe kp s c []) (fun _ _ => False) exe endPc R F ms
      ((_root_.Executable.labels exe).label "wc_worker") 80 8 ".Lwc_worker.stk" 5 9 3 6 4 Wk.wcPs J :=
  XProW.and (XProW.ofPcs fun s σ c k hk he hs hJ =>
      wc_hz hp hb s σ c k (Nat.lt_of_le_of_lt hk (by decide)) he hs hJ)
    (RelZH.wcPro_relH hp hend hR hlo hhi)

/-- **`wc_worker`'s `.entry` nodes** (`hZE`). -/
theorem wcR_hZE {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -144) (hhi : 8 ≤ R.hi)
    {J : AS → Ctl → Prop} {Pr : AS → Nat → Ctl → Prop} (hb : ∀ σ c, J σ c → ¬ HPassC c) :
    NodeZA (fun s c => ZR exe kp s c []) exe endPc R F (Body.wN (_root_.Executable.labels exe).label J Pr .e)
        Body.wkE1 ∧
      NodeZA (fun s c => ZR exe kp s c []) exe endPc R F (Body.wN (_root_.Executable.labels exe).label J Pr .mul)
        [(Body.wkMul.toDir, 4)] ∧
      NodeZA (fun s c => ZR exe kp s c []) exe endPc R F (Body.wN (_root_.Executable.labels exe).label J Pr .e2)
        Body.wkE2 :=
  have hz := wc_hZE hp (Pr := Pr) hb
  have hr := RelZH.wE_relH hp hend hR hlo hhi (J := J) (Pr := Pr)
  ⟨NodeZA.and hz.1.toA hr.1, NodeZA.and hz.2.1.toA hr.2.1, NodeZA.and hz.2.2.toA hr.2.2⟩

/-- **`wc_worker`'s call node** (`hZC`). -/
theorem wcR_hZC {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -144) (hhi : 8 ≤ R.hi)
    {J Kc : AS → Ctl → Prop} (hK : ∀ σ c, Kc σ c → ¬ HPassC c) :
    NodeZA (fun s c => ZR exe kp s c []) exe endPc R F (Body.wCall (_root_.Executable.labels exe).label J Kc)
      Spike.Lib.X64.Print.x0 :=
  NodeZA.and (wc_hZC hp (J := J) hK).toA (RelZH.wCall_relH hp hend hR hlo hhi)

/-- **`print`'s nodes** (`hZP`), at a node with `Print.N`'s pc and offsets and any invariant `J` whose controls
are at no `unpark` binding. -/
theorem wcR_hZP {fr : TermRun.Frame} {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -40)
    (hhi : 16 ≤ R.hi) {c0 : Ctl} {rbp0 ra : BitVec 64} {J : AS → Ctl → Prop} (hu : ∀ σ c, J σ c → NotUnpk c)
    (i : Print.PN) :
    NodeZA (fun s c => ZR exe kp s c [fr]) exe endPc R F
      ⟨(Print.N (_root_.Executable.labels exe).label c0 rbp0 ra i).pc,
        (Print.N (_root_.Executable.labels exe).label c0 rbp0 ra i).o, J⟩ (PrintF.FA.blkN i) :=
  NodeZA.and (wc_hZP hp hu i).toA (RelZH.print_relH hp hend hR hlo hhi i)

/-- **`wc_worker`'s tail** (`hZW`), at its executing offsets. -/
theorem wcR_hZW {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -96) (hhi : 8 ≤ R.hi)
    {cw c1 c2 : Ctl} {A B rbp0 ra tp sp : BitVec 64} (hw : ¬ HPassC cw) (h1 : HPassC c1) (h2 : HPassC c2)
    (i : HelloTail.PN) :
    NodeZA (fun s c => ZR exe kp s c []) exe endPc R F
      (HelloTail.NA (_root_.Executable.labels exe).label cw c1 c2 A B rbp0 ra tp sp i) (HelloTail.blkN i) :=
  NodeZA.and (wc_hZW hp hw h1 h2 i).toA (RelZH.tail_relH hp hend hR hlo hhi i)

/-- **`scc_rt_unpark`'s nodes** (`hZU`). -/
theorem wcR_hZU {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 8 ≤ R.hi)
    {c1 c2 : Ctl} {B rbp1 ra1 tp : BitVec 64} (h1 : HPassC c1) (h2 : HPassC c2) (i : Unpark.PN) :
    NodeZA (fun s c => ZR exe kp s c []) exe endPc R F
      (Unpark.N (_root_.Executable.labels exe).label c1 c2 B rbp1 ra1 tp i) (Unpark.blkN i) :=
  NodeZA.and (wc_hZU hp h1 h2 i).toA (RelZH.unpk_relH hp hend hR hlo hhi i)

/-- **`scc_rt_thr_worker`'s prologue** (`hz`). -/
theorem thrR_hz {R : Region} {F : MachineData → Prop} {ms : MemSide isa} (hR : R.OK) (hlo : R.lo ≤ -72)
    (hhi : 0 ≤ R.hi) {J : AS → Ctl → Prop} (hb : ∀ σ c, J σ c → ¬ HPassC c) :
    XProW (fun s c => ZR exe kp s c []) (fun _ _ => False) exe endPc R F ms
      ((_root_.Executable.labels exe).label "scc_rt_thr_worker") 64 8 ".Lscc_rt_thr_worker.stk" 5 9 3 2 4 thrPs J :=
  XProW.and (XProW.ofPcs fun s σ c k hk he hs hJ =>
      thr_hz hp hb s σ c k (Nat.lt_of_le_of_lt hk (by decide)) he hs hJ)
    (RelZH.thrPro_relH hp hend hR hlo hhi)

/-- **`scc_rt_thr_worker`'s head** (`hZE`). -/
theorem thrR_hZE {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -80) (hhi : 8 ≤ R.hi)
    {J : AS → Ctl → Prop} {L : Ctl → Ctl → Prop} (hb : ∀ σ c, J σ c → ¬ HPassC c) :
    NodeZA (fun s c => ZR exe kp s c []) exe endPc R F (HThrHead.tN (_root_.Executable.labels exe).label J L .e)
      (HThrHead.blkN .e) :=
  NodeZA.and (thr_hZE hp (L := L) hb).toA (RelZH.thrHead_relH hp hend hR hlo hhi .e)

/-- **`scc_rt_thr_worker`'s tail** (`hZT`), at its executing offsets. -/
theorem thrR_hZT {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -72) (hhi : 8 ≤ R.hi)
    {c3 : Ctl} {tp sp0 : BitVec 64} (h3 : HPassC c3) (i : HThrTail.PN) :
    NodeZA (fun s c => ZR exe kp s c []) exe endPc R F (HThrTail.NA (_root_.Executable.labels exe).label c3 tp sp0 i)
      (HThrTail.blkN i) :=
  NodeZA.and (thr_hZT hp h3 i).toA (RelZH.thrTail_relH hp hend hR hlo hhi i)

/-- **The child's stub** (`hZc`). -/
theorem childR_hZc {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -128) (hhi : 0 ≤ R.hi)
    {cW : Ctl} {w : Child.Words} {tp sp0 : BitVec 64} (h0 : ¬ HPassC cW) (i : CN) :
    NodeZA (fun s c => ZR exe kp s c []) exe endPc R F (cN (_root_.Executable.labels exe).label cW w tp sp0 i)
      (cBlk i) :=
  NodeZA.and (child_hZc hp h0 i).toA (RelZH.child_relH hp hend hR hlo hhi i)

end Inst

/-- `ZR` is inhabited: `Z0` (on a frame, off the store, at a control at no `unpark` binding, off the end) at a
state in `RelWS`. -/
example (exe : _root_.Executable) (kp : Nat) (s : State) (h : ¬ helloPassT s)
    (hend : s.st.2 ≠ endOf exe helloCells kp) (fr : TermRun.Frame) (hr : RelWS s) :
    ZR exe kp s ⟨.ret .unit, [], none⟩ [fr] :=
  ⟨⟨⟨fun h' => absurd h' h, fun ⟨h1, _⟩ => absurd h1 (List.cons_ne_nil _ _)⟩,
    fun h => absurd h (List.cons_ne_nil _ _), fun _ _ _ _ h => (by cases h), hend⟩, hr⟩

end Spike.Lib.X64.Flow.Worker.Hello.Z

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.Z.wcR_hZE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.Z.wcR_hZE
