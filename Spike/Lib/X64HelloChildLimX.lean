/-
**The child's thread-pointer premises at the worker's self-word memory side on x86-64** (x86-64 only): the
shapes `X64.Flow.Worker.Hello.SegR.ChildPrem` asks for its `hlimT`, `hlimW` (`LimOk` at the limit word
`tp + 8`) and `hT` (`LdOk` at the TCB's self word `tp`), at `X64HelloOwnLift.msWHX (LH hp i) (GH hp i (G0H hp i))
(SRH hp i) w`, the frame `DFrame (childR stack lo) (childAfter abi x tid th stack tls).st.st.1`, the thread pointer
`ofNat tls` (the second TCB `tH`) and the stack `ofNat stack` (the second take's top).

- `limT_cloneHX`, `limW_cloneHX`: `X64HelloChildHlimR.hlim_cloneH`'s two parts as `LimOk` at `msWH`, lifted to
  `msWHX` (`X64HelloOwnLift.limOk_msXW`); the thread worker's at its entry `%rsp = stack - 8`, `wc_worker`'s at
  `%rsp = stack - 8 - 80` (`wcJE` fixing `%fs` base).
- `ldT_cloneHX`: the TCB's self word `pinA + 144` is a runtime load in the child's frame: in `pinned`
  (`X64HelloTcbArea.pin3_word`), off the copied second take (in the stack pool, disjoint from `pinned`); lifted by
  `X64HelloOwnLift.ldOk_msXW`.
- `tls_tcbWH`: the thread pointer is `X64HelloOwnLift.tcbWH`, the word `msWHX` owns (`ownAt_msWHX`, `hown`).

## Differences from the AArch64 version

There is no AArch64 counterpart: AArch64's `ChildPrem` takes `hlimT`/`hlimW` in `HelloChildHlimR.hlim_cloneH`'s
unfolded form and has no `hT` (its thread worker reads the thread pointer from `TPIDR_EL0`); x86-64's reads the
TCB's self word through `%fs`, so its memory side is `msWHX` (owning that word) and the facts are `LimOk`/`LdOk`.
-/
import Spike.Lib.X64HelloChildHlimR
import Spike.Lib.X64HelloOwnLift

namespace Spike.Lib.X64HelloChildLimX

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (MemRelP Range)
open Scc.Sem.Kernel (KState)
open Spike.Lib.Handover (childAfter handed)
open Spike.Lib.X64.Rt.PreChild (r1Of)
open Spike.Lib.X64 (DFrame)
open Spike.Lib.X64.WakePh.Child (childR)
open Spike.Lib.X64.Flow.Worker.Hello.Child (wcJE Words)
open Spike.Lib.X64.Flow.Ret0 (LimOk LdOk)
open Spike.Lib.X64.PhRec (m0Of)
open Spike.Lib.X64HelloGOf2H (lim2AH)
open Spike.Lib.X64HelloMsW (msWH)
open Spike.Lib.X64HelloOwnLift (msWHX tcbWH)
open Spike.Lib.X64HelloAssemblyI (LH ιH SRH GH)
open Spike.Lib.X64HelloAssemblyIM (G0H)
open Spike.Lib.X64.Flow.HelloWc (tH)
open Spike.Lib

/-- **The thread pointer is `tcbWH`**, the self word `msWHX` owns. -/
theorem tls_tcbWH {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) {tls : Nat}
    (htls : tls = (tH (LH hp i).lab).toNat) : BitVec.ofNat 64 tls = tcbWH (LH hp i) := by
  rw [htls, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  show Spike.Lib.X64.Flow.Ret0.pinA (LH hp i).lab + 144#64 = _
  rw [(LH hp i).lab_pin]

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
    (hpin3 : (LH hp i).pinA.toNat + 208 ≤ (LH hp i).Λ.pinned.lo + (LH hp i).Λ.pinned.size)
    (hinit2 : (m0Of (LH hp i).Λ o.prog o.secs).initVal ⟨lim2AH (LH hp i), 8⟩ = 0)
    (hsub1 : (r1Of (LH hp i).lab).Sub (LH hp i).Λ.stackPool)
    (w : ιH hp i) {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
    (hm : MemRelP (LH hp i).Λ (SRH hp i w).lbl (SRH hp i w).lsize ts tm sm tp tq sp)
    {x : KState} {tid : Nat} {th : Thread isa} {stack tls : Nat} {r0 : Range} {lo : Int}
    (hheld : x.held = [(tid, r1Of (LH hp i).lab), (tid, r0)])
    (htop : (r1Of (LH hp i).lab).lo + (r1Of (LH hp i).lab).size = stack)
    (htls : tls = (tH (LH hp i).lab).toNat) (hlo : -lo ≤ 16384)
include hp hpin3 hinit2 hsub1 hm hheld htop htls hlo

/-- **`ChildPrem.hlimT` at `msWHX`**: the thread worker's limit load at its entry `%rsp = stack - 8`. -/
theorem limT_cloneHX :
    LimOk (msWHX (LH hp i) (GH hp i (G0H hp i)) (SRH hp i) w)
      (DFrame (childR stack lo) (childAfter Scc.Sem.X64.abi x tid th stack tls).st.st.1)
      (BitVec.ofNat 64 tls + (8 : Int64).toBitVec)
      (BitVec.ofNat 64 stack - 8#64 - 8#64 - (64 : Int64).toBitVec) := by
  have h := (Spike.Lib.X64HelloChildHlimR.hlim_cloneH hp i hpin3 hinit2 hsub1 w hm (th := th) hheld htop htls
    hlo).1 ({ fsBase := ⟨BitVec.ofNat 64 tls⟩, rsp := ⟨BitVec.ofNat 64 stack - 8#64⟩ } : Reg64s) rfl rfl
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact Spike.Lib.X64HelloOwnLift.limOk_msXW ⟨h1, h2, h3, h4⟩

/-- **`ChildPrem.hlimW` at `msWHX`**: `wc_worker`'s limit load at `%rsp = stack - 8 - 80`. -/
theorem limW_cloneHX : ∀ {c0 : Ctl} {w' : Words} rbp ra σ c, wcJE c0 w' rbp ra (BitVec.ofNat 64 tls) σ c →
    σ.regs.rsp.toBitVec = BitVec.ofNat 64 stack - 8#64 - 80#64 →
    LimOk (msWHX (LH hp i) (GH hp i (G0H hp i)) (SRH hp i) w)
      (DFrame (childR stack lo) (childAfter Scc.Sem.X64.abi x tid th stack tls).st.st.1)
      (BitVec.ofNat 64 tls + (8 : Int64).toBitVec) (σ.regs.rsp.toBitVec - 8#64 - (80 : Int64).toBitVec) := by
  intro c0 w' rbp ra σ c hJ hsp
  have hsp' : σ.regs.rsp.toBitVec = BitVec.ofNat 64 stack - 88#64 := by rw [hsp, BitVec.sub_sub]; rfl
  obtain ⟨h1, h2, h3, h4⟩ := (Spike.Lib.X64HelloChildHlimR.hlim_cloneH hp i hpin3 hinit2 hsub1 w hm (th := th)
    hheld htop htls hlo).2 rbp ra σ c hJ hsp'
  have hfs : σ.regs.fsBase.toBitVec = BitVec.ofNat 64 tls := hJ.2.2.2.2.2.2.2.2.2
  rw [hfs] at h1 h2 h3 h4
  exact Spike.Lib.X64HelloOwnLift.limOk_msXW ⟨h1, h2, h3, h4⟩

omit hinit2 in
/-- **`ChildPrem.hT` at `msWHX`**: the TCB's self word `pinA + 144` is a runtime load in the child's frame. -/
theorem ldT_cloneHX :
    LdOk (msWHX (LH hp i) (GH hp i (G0H hp i)) (SRH hp i) w)
      (DFrame (childR stack lo) (childAfter Scc.Sem.X64.abi x tid th stack tls).st.st.1)
      (BitVec.ofNat 64 tls) := by
  have hT : BitVec.ofNat 64 tls = (LH hp i).pinA + BitVec.ofNat 64 144 :=
    tls_tcbWH hp i htls
  have ht : ((LH hp i).pinA + 144#64).toNat = (LH hp i).pinA.toNat + 144 :=
    Spike.Lib.X64HelloTcbArea.pin3_toNat hp i (c := 144) (by decide)
  have hsm := (LH hp i).words_small _ (LH hp i).pin_mem
  obtain ⟨hrt, -, hmp⟩ := Spike.Lib.X64HelloTcbArea.pin3_word hp i hpin3 (GH hp i (G0H hp i)) w hm
    (c := 144) (by decide)
  have hp0 : (LH hp i).pinA.toNat = (LH hp i).Λ.pinned.lo := PlaceWX.pinA_toNat_ofPlaceWX hp i
  obtain ⟨-, -, -, -, -, -, -, -, -, hsp⟩ := (PlaceWX.wf_link_of_placeWX i hp).disjoint
  have hsp' : (LH hp i).Λ.stackPool.Disjoint (LH hp i).Λ.pinned := hsp
  have hbd := Spike.Lib.X64.HelloChildTcb.hbd_of (LH hp i) hsub1
  have hlo1 : (r1Of (LH hp i).lab).lo = (Spike.Lib.X64.Flow.Ret0.stacksA (LH hp i).lab).toNat + 16384 := by
    show (Spike.Lib.X64.Flow.Ret0.stacksA (LH hp i).lab + 16384#64).toNat = _
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by simp only [BitVec.toNat_ofNat]; omega)]; rfl
  have hsz : (r1Of (LH hp i).lab).size = 16384 := rfl
  have hh : handed x tid stack = some (tid, r1Of (LH hp i).lab) := by
    rw [← htop]; simp [handed, hheld]
  have hsub := hsub1
  simp only [Range.Sub, Range.Disjoint] at hsp' hsub
  have hstk : (BitVec.ofNat 64 stack).toNat = stack := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine Spike.Lib.X64HelloOwnLift.ldOk_msXW ⟨?_, ?_, ?_⟩
  · rw [hT]; exact hrt
  · rw [hT]; exact hmp
  · intro m hF
    rw [hT]
    rw [hF _ (by omega) (by simp only [childR, hstk]; omega), Spike.Lib.X64.Rt.childAfter_dmem hh]
    exact Spike.Lib.X64.Rt.loadInt_copyRange_none (by omega) (by simp only [Range.contains]; omega) (by decide)

end Place

end Spike.Lib.X64HelloChildLimX

/-- info: 'Spike.Lib.X64HelloChildLimX.limT_cloneHX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloChildLimX.limT_cloneHX

/-- info: 'Spike.Lib.X64HelloChildLimX.limW_cloneHX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloChildLimX.limW_cloneHX

/-- info: 'Spike.Lib.X64HelloChildLimX.ldT_cloneHX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloChildLimX.ldT_cloneHX
