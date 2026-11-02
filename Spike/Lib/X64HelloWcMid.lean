/-
**hello.w's `wc_main` from the box's store to its `clone`'s `syscall`: the ghosts and the pieces' states**
(x86-64; the twin of `Spike/Lib/A64HelloWcMid.lean`). The segments past the box's store,

    .x22+18 .. .x23     hello_wc_res_segW        (the reserve; X64HelloWcSp0)
    .x23 .. .x25        WcSp3WH, WcSp4WH         (the second TCB, the tid word, thread_init; X64HelloWcSp3)
    .x25 .. syscall     hello_wc_sp6_pub_segW    (the packet, the publication, the clone's arguments; X64HelloWcPub)

meet at `.x23`. There the frame's words (the slice's registers `sl`, main's word `me`, the cell `cA`, the caller's
saved `%rbp` and return address `fr`) and the source `c0` become the later pieces' ghosts (`rXH_wcN3H`). The exit
keeps what the source's `Q l A c0` and the cell's word `cA = A` say (wake's `MidG`), and that `fr`, `sl` and `me` are
one entry state's `%rbp`, return address and `%rdi .. %r8` (`FrMGH`).

- `FrMGH`: the saved pair, the slice and main's word are one entry's `%rbp`, `[%rsp]`, `%rdi .. %r8`;
- `rXH_wcN3H`: `.x23`'s exit of the reserve is `wcN3H` at the frame's words;
- `WcMidWH`: the pieces' states inside `W`, at every ghost; `.x25`'s with the source published past the `mfence`
  (`WcSp6PW` at `boxPubCtlH c0 ty l`, under `MidPGH`).

## Differences from the AArch64 version

- There is no fence past the box's store: x86-64's listing has no instruction for the box's `publish` there (see
  `X64HelloWcSp0`), so the source stays at `Q l A` up to `.x23` and the ghosts' guard is `MidG Q c0 cA` (AArch64:
  `MidG S c0 cA`, `S` past the `dmb`). `WcMidWH` has no `S` parameter, and `res` is x86-64's
  `WcResWH W K exe endPc R F ms J1 Q`. The publication is taken at `.x25`'s `mfence` (`X64HelloWcPub`, wake's
  x86-64 `X64WakeWcPub`), so `sp6` is `WcSp6PW` at the published control `boxPubCtlH c0 ty l`, guarded by
  `MidPGH Q c0 ty l cA` (AArch64: `WcSp6W` at `c0`, guarded by `MidG S c0 cA`).
- `FrMGH` reads the caller's `%rbp` and return address (`[%rsp]`), and the five words from `%rdi .. %r8`
  (AArch64: `x29`, `x30`, `x0 .. x4`).
- The reserve's exit is stated at `⟨-128, []⟩` with `%rbp` in its invariant; `rXH_wcN3H` restores `oWH`
  (`Hello1.At.rbp_addr`), as wake's x86-64 `rX_wcN3`.
- Only the live constants are twinned: `WcMidWH.triv` and the composite `hello_wc_mid_segW` are not.
-/
import Spike.Lib.X64HelloWcSp0
import Spike.Lib.X64HelloWcSp3
import Spike.Lib.X64HelloWcSp6Seg
import Spike.Lib.X64HelloWcPub

namespace Spike.Lib.X64.Flow.HelloWc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.HelloPh.WcSp6 (oWH FrWH wcNSH WcSp6PW MidPGH)
open Spike.Lib.X64HelloMainPreSrc (boxPubCtlH)
open Spike.Lib.X64.Flow.WakeWc (MidG kOf)

/-- **The saved pair, the slice and main's word are the caller's**: `fr`, `sl` and `me` are the `%rbp`, the
return address (`[%rsp]`) and `%rdi .. %r8` of one entry state of `J1` (the prologue's saves and spills,
`wcJFH`). -/
def FrMGH (J1 : AS → Ctl → Prop) (fr : BitVec 64 × BitVec 64) (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64)
    (me : BitVec 64) : Prop :=
  ∃ σe c, J1 σe c ∧ fr = (σe.regs.rbp.toBitVec, σe.slot 0) ∧
    sl = (σe.regs.rdi.toBitVec, σe.regs.rsi.toBitVec, σe.regs.rdx.toBitVec, σe.regs.rcx.toBitVec) ∧
    me = σe.regs.r8.toBitVec

/-- **`wc_main`'s states past the box's store inside `W`**: the reserve's segment's, and at every ghost (`c0`,
`sl`, `me`, `cA`, `fr`) with `MidG Q c0 cA` and `FrMGH J1 fr sl me` (as `rXH_wcN3H` exits) the second TCB's,
`.x24`'s, and with `MidPGH Q c0 ty l cA` `.x25`'s, publishing at the `mfence` (at the frame condition `F₂`). -/
structure WcMidWH (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F F₂ : MachineData → Prop) (ms : MemSide isa) (J1 : AS → Ctl → Prop)
    (Q : WeakMem.AllocLabel → Nat → Ctl → Prop) : Prop where
  res : WcResWH W K exe endPc R F ms J1 Q
  sp3 : ∀ c0 sl me cA fr, MidG Q c0 cA ∧ FrMGH J1 fr sl me → WcSp3WH W K exe endPc R F c0 sl me cA fr
  sp4 : ∀ c0 sl me cA fr, MidG Q c0 cA ∧ FrMGH J1 fr sl me →
    WcSp4WH W K exe endPc R F c0 (tH (_root_.Executable.labels exe).label) sl me cA fr
  sp6 : ∀ c0 ty l sl me cA fr, MidPGH Q c0 ty l cA ∧ FrMGH J1 fr sl me →
    WcSp6PW W K exe endPc R F₂ c0 (boxPubCtlH c0 ty l) (tH (_root_.Executable.labels exe).label)
      (kOf (_root_.Executable.labels exe).label) sl me cA fr

/-- `WcMidWH` is inhabited: the trivial predicate, with no outside moves (`FrMGH` and `MidG` are produced at
`.x23` by `rXH_wcN3H`). -/
example {exe : _root_.Executable} {endPc : Int64} {R : Region} {F F₂ : MachineData → Prop} {ms : MemSide isa}
    {J1 : AS → Ctl → Prop} {Q : WeakMem.AllocLabel → Nat → Ctl → Prop} :
    WcMidWH (fun _ _ => True) (fun _ _ => False) exe endPc R F F₂ ms J1 Q :=
  ⟨WcResWH.triv, fun _ _ _ _ _ _ => WcSp3WH.triv, fun _ _ _ _ _ _ => WcSp4WH.triv,
    fun _ _ _ _ _ _ _ _ => WcSp6PW.triv⟩

/-- **The reserve's exit at `.x23` is `wcN3H`** at the frame's words (the slice `sl` at `-8 .. -32`, main's word
`me` at `-40`, the cell `cA` at `-48`, the caller's saved `%rbp` and return address `fr` at `0`, `8`), the source
`c` its ghost, `MidG` and `FrMGH` holding. -/
theorem rXH_wcN3H {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isa} {J1 : AS → Ctl → Prop} {Q : WeakMem.AllocLabel → Nat → Ctl → Prop} {s : State} {c : Ctl}
    {x : Unit} (h : At exe endPc R F (rXH ms (_root_.Executable.labels exe).label R J1 Q x) s c) :
    ∃ (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) (me cA : BitVec 64) (fr : BitVec 64 × BitVec 64),
      MidG Q c cA ∧ FrMGH J1 fr sl me ∧
      At exe endPc R F (wcN3H (_root_.Executable.labels exe).label c sl me cA fr) s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, ⟨l, A, ⟨q, ⟨σe, hJ1, h8, h0, h1, h2, h3, h4, h5⟩, h48, -, -⟩, hQ⟩,
    hb, hax⟩ := h
  refine ⟨(σ.slot (-8), σ.slot (-16), σ.slot (-24), σ.slot (-32)), σ.slot (-40), σ.slot (-48),
    (σ.slot 0, σ.slot 8), ⟨l, A, hQ, h48⟩, ⟨σe, _, hJ1, ?_, ?_, h5⟩, ?_⟩
  · rw [h0, h8]
  · rw [h1, h2, h3, h4]
  have h1' : At exe endPc R F ⟨(_root_.Executable.labels exe).label x23L, ⟨-128, []⟩, fun σ' c' =>
      (wcN3H (_root_.Executable.labels exe).label c (σ.slot (-8), σ.slot (-16), σ.slot (-24), σ.slot (-32))
        (σ.slot (-40)) (σ.slot (-48)) (σ.slot 0, σ.slot 8)).J σ' c' ∧ σ'.regs.get64 .rbp = R.addr 0⟩ s c :=
    ⟨he, hn, hdc, hpc, σ, hA, hD, ⟨rfl, j3H_self hax⟩, hb⟩
  exact Ret0.At.imp (Hello1.At.rbp_addr h1' fun _ _ h => h.2) fun _ _ h => h.1

end Spike.Lib.X64.Flow.HelloWc

/-- info: 'Spike.Lib.X64.Flow.HelloWc.rXH_wcN3H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.rXH_wcN3H
