/-
**hello.w on AArch64: `ClonePreH` from the pre-spawn segment's end**
(the producer): `clonePreH_of`. This is the core of
wake's `WakeHClW.hCl_of`, without the instance plumbing (`R1O`, `SpawnPrem`,
`NodesA`, which come with hello's `W` at B8).

- `ClonePostH L endPc t s c`: the state the pre-spawn segment leaves at the
  clone's `svc` (wake's `WakeWc.ClonePost` at hello's frame). It is
  `A64HelloWcSp6.wcNSH` in `wc_main`'s region `R`, whose base is 144 above
  `sp`, and `sp` is 224 below stack 0's top. The thread pointer `t` is
  `pinA + 8`, in `TPIDR_EL0`.
- `CloneInvH L endPc lbl s c fs`: wake's `WakeWc.CloneInv` at hello:
  - the source stack empty, `ClonePostH`;
  - the source at `SpawnSrcH l ws` (`HelloMainPreSrc`);
  - `c`'s label `l` placed at `x13`, main's id label at `x14`;
  - the slice's words at `x9 .. x12` (`SlRep`).

  This is what the pre-spawn invariant says at the clone (its `h1` twin:
  item 7, `A64HelloWcMid`).
- `BufAtSpawn s lb`: rodata's buffer words' latest source messages at the
  clone, `ClonePreH`'s buffer conjunct.
- `clone_argsH`: a `clone` call's stack and thread pointer are `x1`, `x3`.
- `clonePreH_of`: `ClonePreH` with `X` main's state.

**Open hypothesis (burn-down).** `hbuf`, the buffer fact at the clone
(`BufAtSpawn s lb` for the slice's label `lb`), is **discharged by
`helloSrc_frzL` + `pre1T_vbuf` at the instance** (B8; source-run
invariant `VBuf`, wake's `SpawnFlag.VFlag` template). Its shape is exactly
`helloSrc_frzL`'s conclusion. The other premises are the pre-spawn
relation's (one thread, the certificate's empty promises, the held list
and ownership, main's source id from its run), as in `hCl_of`.
-/
import Spike.Lib.A64HelloClonePreH
import Spike.Lib.A64HelloWcSp6
import Spike.Lib.SegS

namespace Spike.Lib.HelloPreA

open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.WakeA64 Spike.Lib.WakeT1
open Spike.Lib.A64Consumer (Owned)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Scc.Sem.MemRel (SLatest)
open Spike.Lib.HelloMainPreSrc (SpawnSrcH SlRep)
open Spike.Lib.A64.HelloPh.WcSp6 (wcNSH)

/-- `wc_main`'s label prefix in hello.w's listing. -/
abbrev pfxM : String := ".L22_wc_main"

/-- **The state at main's `clone`** that the pre-spawn segment leaves:
`wcNSH` in `wc_main`'s region `R` (its base 144 above `sp`), with the child's
stack top `k`, the TCB `tc`, the slice's registers `sl`, main's word `me`,
the cell `cA` and the caller's pair `fr`; `sp` 224 below stack 0's top; the
thread pointer `t = pinA + 8` in `TPIDR_EL0`. -/
def ClonePostH (L : RuntimeLayout) (endPc : Int64) (t : UInt64) (s : State) (c : Ctl) : Prop :=
  ∃ (R : Region) (F₂ : MachineData → Prop) (tc k : BitVec 64) (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64)
    (me cA : BitVec 64) (fr : BitVec 64 × BitVec 64),
    R.base.toNat % 16 = 0 ∧
    At L.exe endPc R F₂ (wcNSH (_root_.Executable.labels L.exe).label c tc k sl me cA fr) s c ∧
    (R.base.toNat : Int) = s.st.1.regs.SP.toNat + 144 ∧
    s.st.1.regs.SP.toNat + 224 = L.stacksA.toNat + 16384 ∧
    s.st.1.regs.TPIDR_EL0.toBitVec = t.toBitVec ∧ t.toBitVec = L.pinA + 0#64 + 8#64

/-- **The pair at main's `clone`** at the placement `lbl` (wake's
`CloneInv`): the source stack empty, `ClonePostH`, the source at
`SpawnSrcH l ws`, `c`'s label placed at `x13`, main's id label at `x14`,
the slice's words at `x9 .. x12`. -/
def CloneInvH (L : RuntimeLayout) (endPc : Int64) (lbl : WeakMem.AllocLabel → Option Nat) : FragS isaLSE2 :=
  fun s c fs =>
    fs = [] ∧ ∃ (t : UInt64) (l : WeakMem.AllocLabel) (ws : List TermRun.Word), ClonePostH L endPc t s c ∧
      SpawnSrcH l ws c ∧ lbl l = some (s.st.1.regs.getXReg .X13).toNat ∧
      lbl (mainTidLbl 2) = some (s.st.1.regs.getXReg .X14).toNat ∧
      SlRep lbl ws (s.st.1.regs.getXReg .X9).toNat (s.st.1.regs.getXReg .X10).toNat
        (s.st.1.regs.getXReg .X11).toNat (s.st.1.regs.getXReg .X12).toNat

/-- **Rodata's buffer at the clone** (`ClonePreH`'s buffer conjunct, the
shape of `helloSrc_frzL`'s conclusion): the latest source messages to
`⟨lb, 0⟩`, `⟨lb, 1⟩` hold `bufW 0`, `bufW 1`, neither the last message. -/
def BufAtSpawn (s : TermRun.Cfg) (lb : WeakMem.AllocLabel) : Prop :=
  ∀ i < 2, ∃ j m, SLatest s.mem ⟨lb, i⟩ j ∧ s.mem[j]? = some m ∧ m.val = .num (bufW i) ∧ j + 1 < s.mem.size

/-- **A `clone` call's arguments**: the stack in `x1`, the thread pointer
in `x3` (wake's `WakeHClW.clone_args`). -/
theorem clone_argsH {s : State} {st tl : Nat}
    (h : Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl)) :
    st = (s.st.1.regs.getXReg .X1).toNat ∧ tl = (s.st.1.regs.getXReg .X3).toNat := by
  unfold Kernel.decode at h
  repeat' split at h
  all_goals first
    | (cases h; exact ⟨by simp [abi, xRegs, Reg64s.getXReg], by simp [abi, xRegs, Reg64s.getXReg, Kernel.Nrs.a64]; rfl⟩)
    | cases h

/-- **`ClonePreH` from the segment's end** (`hCl_of`'s core), with `X` main's
state:
- main's thread `th` at a `clone` call (`hsys`, `hcall`), its promises
  empty (`hprom`: the certificate, `Handover.prom_nil_of_clone`);
- `CloneInvH` at its source thread's control (`hci`);
- the held list `[(0, r1), (0, r0)]`, disjoint, both owned;
- `r0` stack 0 (`hr0`), the child's stack top `x1` the top of `r1` (`hk`);
- main's source id label (`htid`: `MainTidLbl.mainTidLbl_of_reach`);
- `hbuf`, the buffer fact (the open hypothesis; see the module docstring). -/
theorem clonePreH_of {L : RuntimeLayout} {endPc : Int64} {lbl : WeakMem.AllocLabel → Option Nat}
    {r0 r1 : Range} {d : Cfg} {s : TermRun.Cfg} {th : Thread isaLSE2} {th0 : TermRun.TTh}
    {hd : Option (Nat × TermRun.Word)} (hth : d.1.threads = #[th]) (hs : s.ths = #[th0])
    (hsys : abi.atSys th.st = true) {st tl : Nat} (hcall : callOf abi th = some (.clone st tl))
    (hprom : th.prom = [])
    (hci : CloneInvH L endPc lbl th.st ⟨th0.term, th0.env, hd⟩ th0.stack)
    (hheld : d.2.held = [(0, r1), (0, r0)]) (hdisj : r1.Disjoint r0) (hO0 : Owned L.Λ r0 th.st)
    (hO1 : Owned L.Λ r1 th.st) (hr0 : r0.lo = L.stacksA.toNat ∧ r0.size = 16384)
    (hk : (th.st.st.1.regs.getXReg .X1).toNat = r1.lo + r1.size)
    (htid : th0.tidLbl = some (mainTidLbl 2))
    (hbuf : ∀ l ws lb, SpawnSrcH l ws ⟨th0.term, th0.env, hd⟩ →
      ws.head? = some (TermRun.cst (.loc ⟨lb, 0⟩ 0)) → BufAtSpawn s lb) :
    ClonePreH pfxM L.Λ r0 r1 (· = th.st) lbl d s := by
  obtain ⟨-, t, l, ws, hcp, hS, h13, h14, hR⟩ := hci
  obtain ⟨R, F₂, tc, k, sl, me, cA, fr, -, hat, -, hsp, -, -⟩ := hcp
  obtain ⟨hexe, -, -, hpcS, -⟩ := hat
  obtain ⟨hst1, htl3⟩ := clone_argsH hcall
  have hcall' : callOf abi th = some (.clone (r1.lo + r1.size) (th.st.st.1.regs.getXReg .X3).toNat) := by
    rw [← hk, ← hst1, ← htl3]; exact hcall
  refine ⟨th, th0, hd, (th.st.st.1.regs.getXReg .X3).toNat, (th.st.st.1.regs.getXReg .X13).toNat,
    (th.st.st.1.regs.getXReg .X14).toNat, (th.st.st.1.regs.getXReg .X9).toNat,
    (th.st.st.1.regs.getXReg .X10).toNat, (th.st.st.1.regs.getXReg .X11).toNat,
    (th.st.st.1.regs.getXReg .X12).toNat, l, ws, hth, hs, ?_, hsys, hprom, hcall', hk, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, hheld, hdisj, hO0, hO1, rfl, by omega, by omega, by omega, hr0.2, hS, htid, hR,
    ⟨by decide, _, by simp [Scc.Sem.wordAddr, h13], rfl⟩, ⟨by decide, _, by simp [Scc.Sem.wordAddr, h14], rfl⟩,
    fun lb hh => hbuf l ws lb hS hh⟩
  rw [hpcS, hexe]; rfl

/-- info: 'Spike.Lib.HelloPreA.clonePreH_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms clonePreH_of

end Spike.Lib.HelloPreA
