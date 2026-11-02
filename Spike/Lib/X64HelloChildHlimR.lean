/-
**The child's limit-word premises at the root's clone data on x86-64** (the twin of
`Spike/Lib/HelloChildHlimR.lean`): both prologues' stack-limit facts (the thread worker's below `stack - 8`,
frame 64; `wc_worker`'s at `stack - 88`, frame 80) at the worker's memory side
`X64HelloMsW.msWH (LH hp i) (GH hp i (G0H hp i)) (SRH hp i) w`, the frame
`DFrame (childR stack lo) (childAfter abi x tid th stack tls).st.st.1`, the thread pointer `ofNat tls` and the
stack `ofNat stack`.

The chain: `X64HelloTcbArea.tlsTcb_H` (`TcbArea` at main's second `scc_rt_alloc_tcb`, `TlsTcb` at the second take
`r1Of`) at `msH`; `TlsTcb` is read only through `rt`, `mp`, `G`, which `msWH` (`msH.withBW`) keeps; then
`X64.HelloChildTls.TlsTcb.hlim_stack` at the clone's held list and top, the second take not wrapping
(`X64.HelloChildTcb.hbd_of`).

- `tlsTcb_msWH`: `TlsTcb` at `msH` is `TlsTcb` at `msWH`.
- `hlim_cloneH`: both limit facts at the root's data. Premises, all at the root's clone:
  - `hpin3` (`X64HelloTcbArea.hpin3_H`), `hinit2` (the second limit word's initial value, a loader fact),
    `hsub1` (the second take in the stack pool);
  - `hm`: the memory relation at the record's placement;
  - `hheld`, `htop`: the clone's held list and the second take's top;
  - `htls`: the clone's thread pointer the second TCB `tH` (`X64HelloTcbArea.r8_of_cloneMidH` gives
    `%r8 = tH` at `CloneMidH`);
  - `hlo`: the frame's depth fits the second take.

## Differences from the AArch64 version

- The thread pointer is `%fs` base (`Reg64s.fsBase`), the limit word `fsBase + 8` (AArch64: `TPIDR_EL0`,
  `tcbA r 8`); the conclusion is `X64.HelloChildTls.TlsTcb.hlim_stack`'s, whose first part also takes the entry
  stack pointer `%rsp = stack - 8` and whose second part is at `wcJE … rbp0 ra` with `%rsp = stack - 88` and the
  bound `%rsp - 8 - 80` (AArch64: `SP = stack - 80`, bound `SP - 96`).
- The frame region's depth `lo` is a parameter (`hlo : -lo ≤ 16384`) rather than AArch64's literal `-272`.
- The witness request is `tcb2QH ⟨0, 0, 0⟩ c0` at x86-64's `AllocTcb.G` (`sp`, `fp`, `ra`) and
  `X64HelloMainPreSrc.newTerm`.
-/
import Spike.Lib.X64HelloTcbArea
import Spike.Lib.X64HelloChildTcb
import Spike.Lib.X64HelloMsW
import Spike.Lib.X64WakeChildAt

namespace Spike.Lib.X64HelloChildHlimR

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (MemRelP Range)
open Scc.Sem.Kernel (KState)
open Spike.Lib.Handover (childAfter)
open Spike.Lib.X64.Rt.PreChild (r1Of)
open Spike.Lib.X64 (DFrame)
open Spike.Lib.X64.WakePh.Child (childR)
open Spike.Lib.X64.Flow.Worker.Hello.Child (wcJE Words)
open Spike.Lib.X64.PhRec (m0Of)
open Spike.Lib.X64HelloGOf2H (lim2AH)
open Spike.Lib.X64HelloMs (msH)
open Spike.Lib.X64HelloMsW (msWH)
open Spike.Lib.X64HelloAssemblyI (LH ιH SRH GH)
open Spike.Lib.X64HelloAssemblyIM (G0H)
open Spike.Lib.X64.Flow.HelloWc (tcb2QH tH)
open Spike.Lib.X64.HelloChildTls (TlsTcb)
open Spike.Lib

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **`TlsTcb` at `msH` is `TlsTcb` at `msWH`** (`msWH` is `msH` with `bo`, `we` set; `TlsTcb` reads `rt`, `mp`,
`G`). -/
theorem tlsTcb_msWH {G : ιH hp i → Loc → Val → Prop} {w : ιH hp i} {q : Spike.Lib.X64.Rt.TcbGG} {tls : Nat}
    {r1 : Range} (h : TlsTcb (msH (LH hp i) G (SRH hp i) w) (LH hp i).lab q tls r1) :
    TlsTcb (msWH (LH hp i) G (SRH hp i) w) (LH hp i).lab q tls r1 :=
  have ⟨⟨a, b, c, d, e, f, g⟩, h2, h3, h4, h5⟩ := h
  ⟨⟨a, b, c, d, e, f, g⟩, h2, h3, h4, h5⟩

/-- **Both prologues' limit facts at the root's clone data** (module doc): the worker's memory side `msWH`, the
thread pointer the second TCB `tH`, the stack the second take's top, held first for `tid`. -/
theorem hlim_cloneH
    (hpin3 : (LH hp i).pinA.toNat + 176 ≤ (LH hp i).Λ.pinned.lo + (LH hp i).Λ.pinned.size)
    (hinit2 : (m0Of (LH hp i).Λ o.prog o.secs).initVal ⟨lim2AH (LH hp i), 8⟩ = 0)
    (hsub1 : (r1Of (LH hp i).lab).Sub (LH hp i).Λ.stackPool)
    (w : ιH hp i) {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
    (hm : MemRelP (LH hp i).Λ (SRH hp i w).lbl (SRH hp i w).lsize ts tm sm tp tq sp)
    {x : KState} {tid : Nat} {th : Thread isa} {stack tls : Nat} {r0 : Range} {lo : Int}
    (hheld : x.held = [(tid, r1Of (LH hp i).lab), (tid, r0)])
    (htop : (r1Of (LH hp i).lab).lo + (r1Of (LH hp i).lab).size = stack)
    (htls : tls = (tH (LH hp i).lab).toNat) (hlo : -lo ≤ 16384) :
    (∀ r : Reg64s, r.fsBase.toBitVec = BitVec.ofNat 64 tls →
      r.rsp.toBitVec = BitVec.ofNat 64 stack - 8#64 →
      (msWH (LH hp i) (GH hp i (G0H hp i)) (SRH hp i) w).rt (r.fsBase.toBitVec + (8 : Int64).toBitVec).toNat ∧
      (msWH (LH hp i) (GH hp i (G0H hp i)) (SRH hp i) w).mp ⟨r.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ false ∧
      (∀ m, DFrame (childR stack lo) (childAfter Scc.Sem.X64.abi x tid th stack tls).st.st.1 m →
        Mem.loadInt m.dmem (r.fsBase.toBitVec + (8 : Int64).toBitVec) 8 = none) ∧
      ∀ v : Val, (msWH (LH hp i) (GH hp i (G0H hp i)) (SRH hp i) w).G
          ⟨r.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ v →
        (v.setWidth 64).toNat ≤ (r.rsp.toBitVec - 8#64 - (64 : Int64).toBitVec).toNat) ∧
    ∀ {c0 : Spike.Lib.Ctl} {w' : Words} rbp0 ra σ c, wcJE c0 w' rbp0 ra (BitVec.ofNat 64 tls) σ c →
      σ.regs.rsp.toBitVec = BitVec.ofNat 64 stack - 88#64 →
      (msWH (LH hp i) (GH hp i (G0H hp i)) (SRH hp i) w).rt (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec).toNat ∧
      (msWH (LH hp i) (GH hp i (G0H hp i)) (SRH hp i) w).mp
        ⟨σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ false ∧
      (∀ m, DFrame (childR stack lo) (childAfter Scc.Sem.X64.abi x tid th stack tls).st.st.1 m →
        Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec) 8 = none) ∧
      ∀ v : Val, (msWH (LH hp i) (GH hp i (G0H hp i)) (SRH hp i) w).G
          ⟨σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.rsp.toBitVec - 8#64 - (80 : Int64).toBitVec).toNat := by
  have hT := tlsTcb_msWH hp i (Spike.Lib.X64HelloTcbArea.tlsTcb_H hp i hpin3 hinit2 hsub1 w hm
    ⟨0#64, 0#64, 0#64⟩ ⟨Spike.Lib.X64HelloMainPreSrc.newTerm, [], none⟩ htls)
  have hbd := Spike.Lib.X64.HelloChildTcb.hbd_of (LH hp i) hsub1
  have hlo1 : (r1Of (LH hp i).lab).lo = (Spike.Lib.X64.Flow.Ret0.stacksA (LH hp i).lab).toNat + 16384 := by
    show (Spike.Lib.X64.Flow.Ret0.stacksA (LH hp i).lab + 16384#64).toNat = _
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by simp only [BitVec.toNat_ofNat]; omega)]; rfl
  have hsz : (r1Of (LH hp i).lab).size = 16384 := rfl
  exact hT.hlim_stack (t := th) htop hheld (by omega) (by omega) (by omega)

/-- `hlim_cloneH`'s thread-pointer premise is met by the second TCB itself, and its held list and top by the
clone's: the premises are jointly satisfiable. -/
example (lab : Label → Int64) (r0 : Range) :
    ∃ (x : KState) (stack tls : Nat), x.held = [(0, r1Of lab), (0, r0)] ∧
      (r1Of lab).lo + (r1Of lab).size = stack ∧ tls = (tH lab).toNat :=
  ⟨{ slots := #[], held := [(0, r1Of lab), (0, r0)] }, _, _, rfl, rfl, rfl⟩

end Spike.Lib.X64HelloChildHlimR

/-- info: 'Spike.Lib.X64HelloChildHlimR.tlsTcb_msWH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloChildHlimR.tlsTcb_msWH

/-- info: 'Spike.Lib.X64HelloChildHlimR.hlim_cloneH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloChildHlimR.hlim_cloneH
