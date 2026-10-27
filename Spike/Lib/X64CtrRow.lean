/-
**The counter's add at a node gives the consumer's `CtrRow`** (x86-64):
the premises of `ctr_ndW` (`Spike/Lib/X64AllocNodes.lean`) at a state of
the node give `CtrRow` (`Spike/Lib/X64ConsumerA.lean`) landing in the
node's successors (`Next`), the obligation `WrOkA.ctr` of the consumer at
the allocator's counter add. The twin of `Spike/Lib/A64CtrRow.lean`.

- `ctrRow_nd`: the rule.
- `Alloc.ctrRow_alloc`: at `scc_rt_alloc`'s counter add (`Alloc.N .rmw`),
  landing in the allocator's nodes and exits (`seg_allocW_at`'s).
-/
import Spike.Lib.X64Alloc
import Spike.Lib.X64ConsumerA

namespace Spike.Lib.X64.Flow

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Spike.Lib.X64ConsumerA (CtrRow)

variable {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

/-- **`CtrRow` at a state of the counter's add node** `lock xaddq %r,
k(%b)`, from `ctr_ndW`'s premises (`hcode`, `hedge`): the row lands in the
node's successors. -/
theorem ctrRow_nd {n : ND} {b r : Reg64} {k : Int64} {z : Nat} (hr : r ≠ .rsp) (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(xaddDir b k r, z)])
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      bAddr σ.regs b k = BitVec.ofNat 64 ms.ctr ∧ ms.rt (BitVec.ofNat 64 ms.ctr).toNat ∧
      ms.mp (ctrLoc ms) true ∧ Mem.loadInt m.dmem (BitVec.ofNat 64 ms.ctr) 8 = none ∧
      ∃ (x : String) (a : CoreTerm.At) (τ : Ty) (e : Expr) (ta : Ty) (ws : List TermRun.Word) (nn : Nat),
        c.term = .let_ x (.newBuf a τ) e ∧ TermRun.evalAt c.env a = some (ta, ws) ∧ TermRun.numOf ws = some nn ∧
        c.hold = none ∧ σ.regs.get64 r = BitVec.ofNat 64 (ms.units nn τ) ∧
        ∀ old : Val, ms.G (ctrLoc ms) old → (old.setWidth 64).toNat ≤ ms.cells →
          ms.G (ctrLoc ms) ((old.setWidth 64 + BitVec.ofNat 64 (ms.units nn τ)).setWidth 128) ∧
          ∀ fl, Lands N E ⟨n.pc + Int64.ofNat z, n.o.kill r, { ownStep r (old.setWidth 64) σ with status := fl }⟩
            (holdCtr ms c (old.setWidth 64)))
    {s : State} {c : Ctl} (hAt : At exe endPc R F n s c) :
    CtrRow ms (Next exe endPc R F N E) s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := hAt
  have hc : CellAt s (xaddDir b k r) z := (hcode s he hn).cell0 rfl rfl hpc
  obtain ⟨ha, hrt, hmp, hdm, x, a, τ, e, ta, ws, nn, ht, hev, hnn, hh, hru, hX⟩ := hedge _ σ c hA hD hJ
  have ha' : eaddr s z (mB b k) = BitVec.ofNat 64 ms.ctr :=
    (eaddr_mB s z b k).trans (by rw [hA.regs]; exact ha)
  have hex := exec_xaddG_agrees (w := .W64) hc ha' hdm (agrees_of_decls hdc _ _)
  rw [Reg64s.get_low64] at hex
  refine ⟨.acqRel, _, _, x, a, τ, e, ta, ws, nn, hex, hrt, hmp, ht, hev, hnn, hh, fun old => ?_,
    fun old hG _ hle => ?_⟩
  · simp only [hA.regs, hru]
  obtain ⟨hG', hL⟩ := hX old hG hle
  exact ⟨hG', land_own rfl hr hF he hn hdc hpc hA hD (hL _)⟩

end Spike.Lib.X64.Flow

namespace Spike.Lib.X64.Alloc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Scc.Cert.Rt.X64 (Lays endOf code_field)
open Spike.Lib.X64.Flow
open Spike.Lib.X64ConsumerA (CtrRow)

/-- **`CtrRow` at `scc_rt_alloc`'s counter add** for the call `q` (its
premises `hq`, its code from `allocIn` in a valid layout, the counter
unmapped under `F`): the row lands in the allocator's nodes and exits. -/
theorem ctrRow_alloc {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa} {exe : _root_.Executable}
    [Executable.ValidLayout exe] {endPc : Int64} {R : Region} {F : MachineData → Prop} {q : Call}
    {cells : List (Directive × Nat)} {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hin : allocIn cells = true) (hF : FStable R F) (hq : q.OK ms (_root_.Executable.labels exe).label)
    (hmem : ∀ m, F m → Mem.loadInt m.dmem (BitVec.ofNat 64 ms.ctr) 8 = none)
    {s : State} {c : Ctl} (hAt : At exe endPc R F (N (_root_.Executable.labels exe).label ms q .rmw) s c) :
    CtrRow ms (Next exe endPc R F (N (_root_.Executable.labels exe).label ms q)
      (E (_root_.Executable.labels exe).label ms q lbl)) s c := by
  have hin' := hin
  simp only [allocIn, fiAt, iCtr, iHeap, iRmw, iHdr, iRet, Bool.and_eq_true] at hin'
  refine ctrRow_nd (b := .rcx) (k := 0) (r := .rax) (z := 5) (by decide) hF
    (code_field hp hend (by simp only [hin']) (l := cntL) (off := 19) rfl) (fun m σ c _ hD hJ => ?_) hAt
  obtain ⟨⟨rfl, hFr, hn28⟩, hcx, hax⟩ := hJ
  have hb : bAddr σ.regs .rcx 0 = BitVec.ofNat 64 ms.ctr := by
    rw [← hq.ctr, ← hcx]; simp [bAddr, Reg64s.get64]
  rw [hb]
  refine ⟨rfl, hq.rt, hq.mp, hmem _ hD, q.x, q.a, q.τ, q.e, q.ta, q.ws, q.n, hq.term, hq.ev,
    hq.num, hq.hold, by exact hax, fun old hG hle => ⟨hq.grow old hG hle, fun fl =>
      .inl ⟨AN.c2, ofNat_add' _ 19 5, rfl, _, rfl, hle, hFr, hn28, ?_⟩⟩⟩
  simp [ownStep, Reg64s.set64]

end Spike.Lib.X64.Alloc
