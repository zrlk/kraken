/-
**wake.w's worker rows off the transfer sites on x86-64** (the x64 twin of
`Spike/Lib/A64WakeWorkerNN.lean`, `WCompat.noSite`): `Unpark.seg_unpark`
and the worker segments of `Spike/Lib/X64WakeWorker.lean` over
`SegTC (NNZ exe endPc Z)`, every state of their hidden invariants at a cell
other than a `nop`. The listing is wake.w's (`SccCode.wakeText`,
`Spike/Lib/X64WakeCode.lean`).

The proofs are the originals' with the leaves of `Spike/Lib/X64WakeNN.lean`
(`seg_ndNN` with each block's decided no-`nop` check, `relStore_ndNN`,
`unpkXchg_ndNN`, `syscall_ndNN`, `ownFsld_ndNN`, `rtst_ndNN`,
`texit_ndNN`, `call_ndTS`, `fn_segTS`) and `SegTC`'s combinators
(`Spike/Lib/SegThrS.lean`). Each segment also keeps a fragment `Z` at its
nodes, given per node as `NodeZ Z exe (N i) (blkN i)` (`hZ`; `hZU` for the
unpark callee at every ghost return frame).

- `Unpark.seg_unparkNN`: `Unpark.seg_unpark`.
- `Wake.WkTailW.seg_wkTailWNN`, `seg_unparkCallWNN`, `seg_wkTailWUNN`: the
  `WkTailW` segments (the call's callee given over `SegTC`).
- `Wake.ThrTailW.seg_thrTailWNN`: `ThrTailW.seg_thrTailW`.
- `Wake.ThrHeadW.seg_thrHeadWNN`: `ThrHeadW.seg_thrHeadW` (`hwk` over
  `SegTC`).

**Unlike AArch64** (forced by the x64 shape):

- `NodeZ` is indexed by a node's block (`blkN`, the cells with their sizes;
  `[(d, z)]` at a single instruction, `[]` at a call node), not by a count
  of 4-byte instructions (AArch64's `lenN`).
- the futex wake is a `syscall` (`syscall_ndNN`, with its safety: neither
  `write` nor `exit_group`), the permit's exchange `xchgq`
  (`unpkXchg_ndNN`), the `exited` release a plain `movq` (`rtst_ndNN`), and
  the thread pointer is read through `%fs` (`ownFsld_ndNN`).
- no alignment premise (`hal`); the regions end at `8` and the epilogue
  nodes claim `%rbp`'s offset back (`WaitLoop.At.rbpOf`) as in the
  originals.
-/
import Spike.Lib.X64WakeWorker
import Spike.Lib.X64WakeNN

namespace Spike.Lib.X64.Flow.Worker

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64
open Scc.Sem (ValRep)
open Spike.Lib Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (StOk LdOk)

set_option linter.unusedSimpArgs false

namespace Unpark

/-- Each node's block (the single instruction at the exchange and the
`syscall`), the block of its `NodeZ` obligation. -/
def blkN : PN → List (Directive × Nat)
  | .e => b0 | .n1 => b1 | .xchg => [(xchgDir .rcx 16 .rax, 4)] | .n2 => b2 | .n3 => b3
  | .wake => b4 | .sys => [(op64 .syscall, 2)] | .n5 => b5 | .done => b6

section ProofNN

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 c1 : Ctl}
  {B rbp0 ra tp : BitVec 64} {Z : Frag isa}

set_option hygiene false in
/-- A block node off the transfer sites: the block, its `okBlk`, its code;
the edge is left. -/
local macro "unode " b:ident ok:ident f:ident : tactic =>
  `(tactic| refine seg_ndNN (by simp [$b:ident]) $ok (by decide) hF hR hlo hhi
    (fun s he hn => hcode.$f s he hn) (fun σ c hJ => ⟨c, .refl c, ?_⟩) (hZ _))

/-- Hitting node `j`. -/
local macro "uhit " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;>
    simp_all [N, JI, JS, JE, JR, Int64.add_assoc, upd_apply, Reg64s.get64_set64_self,
      Reg64s.get64_set64_ne, KeepTP.set64_tp, ownStep, syscallStep, syscallRegs]))

/-- Hitting exit `x`. -/
local macro "uexit " x:term : tactic =>
  `(tactic| (refine .inr ⟨$x, ?_, rfl, ?_⟩ <;>
    simp_all [N, E, JI, JS, JE, JR, Int64.add_assoc, upd_apply, Reg64s.get64_set64_self,
      Reg64s.get64_set64_ne, KeepTP.set64_tp]))

/-- **`seg_unpark` off the transfer sites**: the same segment over
`SegTC (NNZ exe endPc Z)`. -/
theorem seg_unparkNN (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 8 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hS : StOk ms F (B + 16#64) 1#64) (htp4 : (B + 16#64).toNat % 4 = 0)
    {x : String} {a : CoreTerm.At} {e : Expr} {ty : Ty} {jw : TermRun.Word}
    (ht : c0.term = .let_ x (.ext .unpark a) e) (hh : c0.hold = none)
    (hev : TermRun.evalAt c0.env a = some (ty, [jw])) (hv : ValRep lbl jw.val B.toNat)
    (hc1 : c1 = ⟨e, (x, ExtName.unpark.sig.2, []) :: c0.env, none⟩)
    (hcode : Code c0 c1 B rbp0 ra tp exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".Lscc_rt_unpark.entry" =
      (_root_.Executable.labels exe).label "scc_rt_unpark" + 12)
    (hZ : ∀ i, NodeZ Z exe (N (_root_.Executable.labels exe).label c0 c1 B rbp0 ra tp i) (blkN i)) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 B rbp0 ra tp .e))
      (fun s c => ∃ x, At exe endPc R F (E c1 rbp0 ra tp x) s c) := by
  refine fn_segTS (N := N _ c0 c1 B rbp0 ra tp) (E := E c1 rbp0 ra tp) (fun i => ?_) PN.e
  cases i
  case e => unode b0 b0_ok e; rw [N, b0_run]; uhit PN.n1
  case n1 => unode b1 b1_ok n1; rw [N, b1_run]; uhit PN.xchg
  case xchg =>
    refine unpkXchg_ndNN (A := B + 16#64) (B := B) (by decide) hF (fun s he hn => hcode.xchg s he hn)
      (fun m σ c _ _ hJ => ?_) (hZ _)
    obtain ⟨⟨rfl, hJ⟩, hc, ha⟩ := hJ
    refine ⟨by rw [bAddr, hc]; rfl, ha, hS, rfl, x, a, e, ty, jw, ht, hh, hev, hv, fun v => ?_⟩
    rw [← hc1]
    uhit PN.n2
  case n2 =>
    unode b2 b2_ok n2; rw [N, b2_run]
    split
    · uhit PN.wake
    · uhit PN.n3
  case n3 => unode b3 b3_ok n3; rw [N, b3_run]; uhit PN.done
  case wake =>
    unode b4 b4_ok wake; rw [N, b4_run]
    have hc : (16#64 : BitVec 64) + B = B + 16#64 := BitVec.add_comm _ _
    uhit PN.sys
  case sys =>
    have hcall : ∀ σ c, (N (_root_.Executable.labels exe).label c0 c1 B rbp0 ra tp .sys).J σ c →
        syscallCall σ.regs = some (.futexWake 1) := by
      rintro σ c ⟨-, h0, h1, h2, h8⟩
      have hw := syscallCall_futexWake (r := σ.regs) ?_ ?_ ?_
      · rw [hw]
        have := congrArg BitVec.toNat h2; simp [Reg64s.get64] at this; rw [this]
      · have := congrArg BitVec.toNat h8; simpa [Reg64s.get64] using this
      · have := congrArg BitVec.toNat h1; simpa [Reg64s.get64] using this
      · have := congrArg BitVec.toNat h0; rw [← htp4, ← this]; simp [Reg64s.get64]
    refine syscall_ndNN hK hF (fun s he hn => hcode.sys s he hn) (fun σ c hJ => ?_) ?_ ?_ (hZ _)
    · refine ⟨.futexWake 1, hcall σ c hJ, nofun, fun v _ => ⟨c, .refl c, ?_⟩⟩
      obtain ⟨hT, -⟩ := hJ
      uhit PN.n5
    · rintro s c σ call - hJ hc
      rw [hcall σ c hJ] at hc
      cases hc
      exact ⟨nofun, nofun, nofun, nofun⟩
    · rintro σ c hJ call hc
      rw [hcall σ c hJ] at hc
      cases hc
      exact .inr ⟨nofun, nofun⟩
  case n5 => unode b5 b5_ok n5; rw [N, b5_run]; uexit PX.ret
  case done => unode b6 b6_ok done; rw [N, b6_run]; uexit PX.ret

end ProofNN

end Unpark

namespace Wake

namespace WkTailW

/-- Each node's block (the store's cell; `[]` at the call node), the block
of its `NodeZ` obligation. -/
def blkN : PN → List (Directive × Nat)
  | .e => b0 | .st => [(stDir .rcx 0 .rax, 3)] | .n3 => b1 | .unpk => [] | .x14 => b2

section ProofNN

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 c1 c2 : Ctl}
  {A B rbp0 ra tp sp : BitVec 64} {Z : Frag isa}

set_option hygiene false in
/-- A block node off the transfer sites: the block, its `okBlk`, its code;
the edge is left. -/
local macro "wnode " b:ident ok:ident f:ident : tactic =>
  `(tactic| refine seg_ndNN (by simp [$b:ident]) $ok (by decide) hF hR hlo hhi
    (fun s he hn => hcode.$f s he hn) (fun σ c hJ => ⟨c, .refl c, ?_⟩) (hZ _))

/-- Hitting node `j`. -/
local macro "whit " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;>
    simp_all [N, JI, Int64.add_assoc, upd_apply, Reg64s.get64_set64_self,
      Reg64s.get64_set64_ne, KeepTP.set64_tp, Reg64s.set64, Reg64s.get64]))

/-- **`seg_wkTailW` off the transfer sites** (`hunpk` over `SegTC`). -/
theorem seg_wkTailWNN (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -32) (hhi : 8 ≤ R.hi)
    (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    {d : String} {a b : CoreTerm.At} {e1 : Expr} {ty tb : Ty} {w wb : TermRun.Word}
    (ht : c0.term = .let_ d (.store true a b none) e1) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hv : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hevb : TermRun.evalAt c0.env b = some (tb, [wb])) (hvb : ValRep lbl wb.val 1)
    (hc1 : c1 = ⟨e1, (d, .unit, []) :: c0.env, none⟩)
    (hcode : Code c0 c1 c2 A B rbp0 ra tp (R.addr 0) exe endPc)
    (hunpk : SegTC (NNZ exe endPc Z) p lbl ms
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp (R.addr 0) .unpk))
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp (R.addr 0) .x14)))
    (hZ : ∀ i, NodeZ Z exe (N (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp (R.addr 0) i)
      (blkN i)) :
    SegTC (NNZ exe endPc Z) p lbl ms
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp (R.addr 0) .e))
      (fun s c => ∃ x, At exe endPc R F (E c2 rbp0 ra tp x) s c) := by
  refine fn_segTS (N := N _ c0 c1 c2 A B rbp0 ra tp (R.addr 0)) (E := E c2 rbp0 ra tp) (fun i => ?_) PN.e
  cases i
  case e => wnode b0 b0_ok e; rw [N, b0_run]; whit PN.st
  case st =>
    refine relStore_ndNN (A := A) (fun s he hn => hcode.st s he hn) hdm (fun m σ c _ _ hJ => ?_) (hZ _)
    obtain ⟨⟨rfl, hJ⟩, hc, ha⟩ := hJ
    refine ⟨by rw [bAddr, hc]; simp, d, a, b, e1, ty, tb, w, wb, ht, hev, hv, htag, hevb,
      by rw [ha]; exact hvb, ?_⟩
    rw [← hc1]
    whit PN.n3
  case n3 => wnode b1 b1_ok n3; rw [N, b1_run]; whit PN.unpk
  case unpk => exact hunpk.mono_post fun s c h => .inl ⟨PN.x14, h⟩
  case x14 =>
    let n := N (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp (R.addr 0) .x14
    refine (seg_ndNN (n := ⟨n.pc, oI, n.J⟩) (by simp [b2]) b2_ok (by decide) hF hR hlo hhi
      (fun s he hn => hcode.x14 s he hn) (fun σ c hJ => ⟨c, .refl c, ?_⟩) (hZ .x14)).mono_pre
      fun _ _ h => WaitLoop.At.rbpOf h fun σ c hJ => by
        show σ.regs.rbp.toBitVec = _; rw [hJ.2.2.2.2.2.2, WaitLoop.addr0_sub8]
    rw [b2_run]
    refine .inr ⟨PX.ret, ?_, rfl, ?_⟩ <;>
      simp_all [n, N, E, JI, Int64.add_assoc, upd_apply, Reg64s.get64_set64_self, Reg64s.get64_set64_ne,
        KeepTP.set64_tp]

/-- **`seg_unparkCallW` off the transfer sites** (`call_ndTS` with
`Unpark.seg_unparkNN`). -/
theorem seg_unparkCallWNN (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -72) (hhi : 8 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hS : StOk ms F (B + 16#64) 1#64) (htp4 : (B + 16#64).toNat % 4 = 0)
    {x : String} {a : CoreTerm.At} {e : Expr} {ty : Ty} {jw : TermRun.Word}
    (ht : c1.term = .let_ x (.ext .unpark a) e) (hh : c1.hold = none)
    (hev : TermRun.evalAt c1.env a = some (ty, [jw])) (hv : ValRep lbl jw.val B.toNat)
    (hc2 : c2 = ⟨e, (x, ExtName.unpark.sig.2, []) :: c1.env, none⟩)
    {c0' c1' : Ctl} {B' rbp0' ra' tp' : BitVec 64} (hpcode : Unpark.Code c0' c1' B' rbp0' ra' tp' exe endPc)
    (hpentry : (_root_.Executable.labels exe).label ".Lscc_rt_unpark.entry" =
      (_root_.Executable.labels exe).label "scc_rt_unpark" + 12)
    (hx14 : (_root_.Executable.labels exe).label ".Lwc_worker.x14" =
      (_root_.Executable.labels exe).label ".Lwc_worker.entry" + 14 + 9)
    (hZU : ∀ rbp1 ra1, ∀ i, NodeZ Z exe (Unpark.N (_root_.Executable.labels exe).label c1 c2 B rbp1 ra1 tp i)
      (Unpark.blkN i)) :
    SegTC (NNZ exe endPc Z) p lbl ms
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp sp .unpk))
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp sp .x14)) := by
  refine (call_ndTS (e0 := 0) (lo' := -40) (hi' := 8)
    (N := fun _ : Unit => N (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp sp .x14)
    (E := fun e : Empty => e.elim)
    (Ne := fun g : BitVec 64 × BitVec 64 =>
      Unpark.N (_root_.Executable.labels exe).label c1 c2 B g.1 g.2 tp .e)
    (Ex := fun g y => Unpark.E c2 g.1 g.2 tp y)
    hR hF (by show R.lo ≤ -32 - 0 + -40; omega) (by decide) (by show (-32 : Int) - 0 < R.hi; omega)
    (by show (-32 : Int) - 0 + 8 ≤ R.hi; omega) (by show ((-32 : Int) - 0) % 8 = 0; decide) (by decide)
    (by decide)
    (fun R' F' hR' hlo' hhi' hF' hFF g =>
      Unpark.seg_unparkNN hF' hR' hlo' hhi' hK (hS.mono hFF) htp4 ht hh hev hv hc2 hpcode.ghost hpentry
        (hZU g.1 g.2))
    (fun _ => rfl) ?_ ?_).mono_post fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
  · rintro σC c ⟨⟨rfl, -, -, -, -, htp, -⟩, hdi, -⟩
    exact ⟨(σC.regs.rbp.toBitVec, σC.slot (-32 - 0 + 0)), rfl, rfl, hdi, rfl, rfl, htp⟩
  · rintro ⟨rbp1, ra1⟩ ⟨⟩ σC c σx c' σR ⟨⟨rfl, h8, h0, h16, h24, -, hbp⟩, -, h32⟩ ⟨hc, -, hrb, hra, -⟩
      ⟨hc', hrb', htp'⟩ hreg - - hslot
    have hout : ∀ k : Int, -24 ≤ k → k % 8 = 0 → k ≤ 0 → σR.slot k = σC.slot k := fun k h1 h2 h3 =>
      hslot k ⟨h2, by omega, by omega⟩ fun ⟨_, _, h⟩ => by
        simp only [Region.callee, N] at h; omega
    refine .inl ⟨(), ?_, by show SO.le oP ⟨-32 - 0 + 8, []⟩ = true; decide, hc',
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · subst hra
      show (_root_.Executable.labels exe).label ".Lwc_worker.x14" = Int64.ofBitVec (σC.slot (-32))
      rw [h32, hx14]; rfl
    · rw [hout (-8) (by decide) (by decide) (by decide)]; exact h8
    · rw [hout 0 (by decide) (by decide) (by decide)]; exact h0
    · rw [hout (-16) (by decide) (by decide) (by decide)]; exact h16
    · rw [hout (-24) (by decide) (by decide) (by decide)]; exact h24
    · show σR.regs.fsBase.toBitVec = tp
      rw [hreg]; exact htp'
    · show σR.regs.rbp.toBitVec = _
      have : σx.regs.get64 .rbp = rbp1 := hrb'
      rw [hreg]; simp only [Reg64s.get64] at this; rw [this]
      exact (show σC.regs.rbp.toBitVec = rbp1 from hrb).symm.trans hbp

/-- **`seg_wkTailWU` off the transfer sites** (`seg_wkTailWNN` with
`seg_unparkCallWNN`). -/
theorem seg_wkTailWUNN (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -72) (hhi : 8 ≤ R.hi)
    (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    {d : String} {a b : CoreTerm.At} {e1 : Expr} {ty tb : Ty} {w wb : TermRun.Word}
    (ht : c0.term = .let_ d (.store true a b none) e1) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hv : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hevb : TermRun.evalAt c0.env b = some (tb, [wb])) (hvb : ValRep lbl wb.val 1)
    (hc1 : c1 = ⟨e1, (d, .unit, []) :: c0.env, none⟩)
    (hcode : Code c0 c1 c2 A B rbp0 ra tp (R.addr 0) exe endPc)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hS : StOk ms F (B + 16#64) 1#64) (htp4 : (B + 16#64).toNat % 4 = 0)
    {x : String} {au : CoreTerm.At} {e : Expr} {tu : Ty} {jw : TermRun.Word}
    (htu : c1.term = .let_ x (.ext .unpark au) e) (hhu : c1.hold = none)
    (hevu : TermRun.evalAt c1.env au = some (tu, [jw])) (hvu : ValRep lbl jw.val B.toNat)
    (hc2 : c2 = ⟨e, (x, ExtName.unpark.sig.2, []) :: c1.env, none⟩)
    {c0' c1' : Ctl} {B' rbp0' ra' tp' : BitVec 64} (hpcode : Unpark.Code c0' c1' B' rbp0' ra' tp' exe endPc)
    (hpentry : (_root_.Executable.labels exe).label ".Lscc_rt_unpark.entry" =
      (_root_.Executable.labels exe).label "scc_rt_unpark" + 12)
    (hx14 : (_root_.Executable.labels exe).label ".Lwc_worker.x14" =
      (_root_.Executable.labels exe).label ".Lwc_worker.entry" + 14 + 9)
    (hZ : ∀ i, NodeZ Z exe (N (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp (R.addr 0) i)
      (blkN i))
    (hZU : ∀ rbp1 ra1, ∀ i, NodeZ Z exe (Unpark.N (_root_.Executable.labels exe).label c1 c2 B rbp1 ra1 tp i)
      (Unpark.blkN i)) :
    SegTC (NNZ exe endPc Z) p lbl ms
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp (R.addr 0) .e))
      (fun s c => ∃ x, At exe endPc R F (E c2 rbp0 ra tp x) s c) :=
  seg_wkTailWNN hF hR (Int.le_trans hlo (by decide)) hhi hdm ht hev hv htag hevb hvb hc1 hcode
    (seg_unparkCallWNN hF hR hlo hhi hK hS htp4 htu hhu hevu hvu hc2 hpcode hpentry hx14 hZU) hZ

end ProofNN

end WkTailW

namespace ThrTailW

/-- Each node's block (the single instruction at the load, the store and
the `syscall`), the block of its `NodeZ` obligation. -/
def blkN : PN → List (Directive × Nat)
  | .x12 => [(fsDir .rax 0, 9)] | .n1 => b0 | .ex => [(stDir .rcx 24 .rax, 4)] | .n2 => b1
  | .sys => [(op64 .syscall, 2)]

section ProofNN

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {tp : BitVec 64}
  {Z : Frag isa}

set_option hygiene false in
/-- A block node off the transfer sites: the block, its `okBlk`, its code;
the edge is left. -/
local macro "tnode " b:ident ok:ident f:ident : tactic =>
  `(tactic| refine seg_ndNN (by simp [$b:ident]) $ok (by decide) hF hR hlo hhi
    (fun s he hn => hcode.$f s he hn) (fun σ c hJ => ⟨c, .refl c, ?_⟩) (hZ _))

/-- Hitting node `j`. -/
local macro "thit " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;>
    simp_all [N, Int64.add_assoc, upd_apply, Reg64s.get64_set64_self,
      Reg64s.get64_set64_ne, KeepTP.set64_tp, fsStep, Reg64s.set64, Reg64s.get64]))

/-- **`seg_thrTailW` off the transfer sites.** -/
theorem seg_thrTailWNN {Q : Frag isa} (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 8 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.X64.abi) (hT : LdOk ms F tp)
    (hown : OwnAt ms exe endPc ((_root_.Executable.labels exe).label ".Lscc_rt_thr_worker.x12") tp tp)
    (hS : StOk ms F (tp + 24#64) 1#64) {a : CoreTerm.At} (ht : c0.term = .ret a)
    (hcode : Code c0 tp (R.addr 0) exe endPc)
    (hZ : ∀ i, NodeZ Z exe (N (_root_.Executable.labels exe).label c0 tp (R.addr 0) i) (blkN i)) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label c0 tp (R.addr 0) .x12))
      Q := by
  refine (fn_segTS (N := N _ c0 tp (R.addr 0)) (E := (nofun : Empty → ND)) (fun i => ?_) PN.x12).mono_post
    fun _ _ ⟨x, _⟩ => x.elim
  cases i
  case x12 =>
    refine ownFsld_ndNN (by decide) hF (fun s he hn => hcode.x12 s he hn) hown
      (fun m σ c _ hm hJ => ?_) (hZ _)
    obtain ⟨hc0, hfs, hbp⟩ := hJ
    have ha : σ.regs.fsBase.toBitVec + (0 : Int64).toBitVec = tp := by rw [hfs]; exact BitVec.add_zero tp
    refine ⟨ha, hT.rt, hT.mp, hT.unmapped m hm, c, .refl c, ?_⟩
    thit PN.n1
  case n1 =>
    refine (seg_ndNN (n := ⟨(N (_root_.Executable.labels exe).label c0 tp (R.addr 0) .n1).pc, oI,
        (N (_root_.Executable.labels exe).label c0 tp (R.addr 0) .n1).J⟩) (by simp [b0]) b0_ok (by decide) hF hR hlo hhi
      (fun s he hn => hcode.n1 s he hn) (fun σ c hJ => ⟨c, .refl c, ?_⟩) (hZ .n1)).mono_pre
      fun _ _ h => WaitLoop.At.rbpOf h fun σ c hJ => by
        show σ.regs.rbp.toBitVec = _; rw [hJ.2.2, WaitLoop.addr0_sub8]
    rw [b0_run]; thit PN.ex
  case ex =>
    refine rtst_ndNN (fun s he hn => hcode.ex s he hn) (fun m σ c _ hm hJ => ?_) (hZ _)
    obtain ⟨rfl, hc, ha⟩ := hJ
    have hA : bAddr σ.regs .rcx 24 = tp + 24#64 := by rw [bAddr, hc]; rfl
    rw [hA, ha]
    exact ⟨hS.rt, hS.mp, hS.G, hS.unmapped m hm, c, .refl c, by thit PN.n2⟩
  case n2 => tnode b1 b1_ok n2; rw [N, b1_run]; thit PN.sys
  case sys =>
    refine texit_ndNN hK (fun s he hn => hcode.sys s he hn)
      (fun σ c ⟨hc, h60⟩ => ⟨?_, a, by rw [hc]; exact ht⟩) (hZ _)
    have := congrArg BitVec.toNat h60; simpa [Reg64s.get64] using this

end ProofNN

end ThrTailW

namespace ThrHeadW

/-- Each node's block (`[]` at the call), the block of its `NodeZ`
obligation. -/
def blkN : TN → List (Directive × Nat)
  | .e => thE | .call => []

section ProofNN

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {Z : Frag isa}

/-- **`seg_thrHeadW` off the transfer sites** (`hwk` over `SegTC`). -/
theorem seg_thrHeadWNN {ι κ : Sort _} {N : ι → ND} {E : κ → ND} (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -120) (hhi : 8 ≤ R.hi) {J : AS → Ctl → Prop}
    {L : Ctl → Ctl → Prop} (hL : ∀ σ c, J σ c → ∃ c', LocalRun p c c' ∧ L c c')
    (hcodeE : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s ((_root_.Executable.labels exe).label ".Lscc_rt_thr_worker.entry") thE)
    {γ : Type _} {κ' : Sort _} {Ne : γ → ND} {Ex : γ → κ' → ND}
    (hwk : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ -72 → 8 ≤ R'.hi →
      FStable R' F' → (∀ m, F' m → F m) → ∀ g,
        SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R' F' (Ne g))
          (fun s c => ∃ x, At exe endPc R' F' (Ex g x) s c))
    (hNe : ∀ g, (Ne g).o = ⟨0, []⟩)
    (hent : ∀ σC c, (tN (_root_.Executable.labels exe).label J L .call).J σC c →
      ∃ g, (Ne g).pc = (_root_.Executable.labels exe).label "wc_worker" ∧ (Ne g).J (enter (-48 - 0) σC) c)
    (hret : ∀ g x σC c σx c' (σR : AS), (tN (_root_.Executable.labels exe).label J L .call).J σC c →
      (Ne g).J (enter (-48 - 0) σC) c → (Ex g x).J σx c' →
      σR.regs = σx.regs → σR.zmms = σx.zmms → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee (-48 - 0) (-72) 8).Off (k - (-48 - 0)) → σR.slot k = σC.slot k) →
      Lands N E ⟨(Ex g x).pc, ⟨-48 - 0 + (Ex g x).o.sp, []⟩, σR⟩ c')
    (hZ : ∀ i, NodeZ Z exe (tN (_root_.Executable.labels exe).label J L i) (blkN i)) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F (tN (_root_.Executable.labels exe).label J L .e))
      (Next exe endPc R F N E) := by
  let lab := (_root_.Executable.labels exe).label
  refine SegTC.seq (Q := At exe endPc R F (tN lab J L .call))
    ((seg_ndNN (N := fun _ : Unit => tN lab J L .call) (E := (nofun : Empty → ND)) (blk := thE) (by simp [thE])
      thE_ok (by decide) hF hR hlo hhi hcodeE (fun σ c hJ => ?_) (hZ .e)) |>.mono_post ?_) ?_
  · obtain ⟨c', hr, hl⟩ := hL σ c hJ
    refine ⟨c', hr, .inl ⟨(), ?_, ?_, σ, c, hJ, hl, rfl⟩⟩
    · simp only [tN]; rw [thE_run]
    · simp only [tN]; rw [thE_run]; rfl
  · rintro s c (⟨_, h⟩ | ⟨y, _⟩)
    · exact h
    · exact y.elim
  · exact call_ndTS (e0 := 0) (lo' := -72) (hi' := 8) hR hF (by show R.lo ≤ -48 - 0 + -72; omega) (by decide)
      (by show (-48 : Int) - 0 < R.hi; omega) (by show (-48 : Int) - 0 + 8 ≤ R.hi; omega)
      (by show ((-48 : Int) - 0) % 8 = 0; decide) (by decide) (by decide) hwk hNe hent hret

end ProofNN

end ThrHeadW

end Wake

/-- info: 'Spike.Lib.X64.Flow.Worker.Wake.WkTailW.seg_wkTailWUNN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Wake.WkTailW.seg_wkTailWUNN

/-- info: 'Spike.Lib.X64.Flow.Worker.Wake.ThrTailW.seg_thrTailWNN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Wake.ThrTailW.seg_thrTailWNN

/-- info: 'Spike.Lib.X64.Flow.Worker.Wake.ThrHeadW.seg_thrHeadWNN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Wake.ThrHeadW.seg_thrHeadWNN

end Spike.Lib.X64.Flow.Worker
