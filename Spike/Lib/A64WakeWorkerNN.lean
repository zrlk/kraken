/-
**wake.w's worker rows off the transfer sites** (`WCompat.noSite`, AArch64): `Unpark.seg_unpark` and the worker segments of
`Spike/Lib/A64WakeWorker.lean` over `SegTC (NNZ exe endPc Z)`, every state of
their hidden invariants at a cell other than a `nop`. The listing is wake.w's
certificate (`Spike/Test/Cert/A64WakeCert.s`).

The proofs are the originals' with the leaves of `Spike/Lib/A64WakeNN.lean`
(`seg_ndNN` with each block's decided no-`nop` check, `relStore_ndNN`,
`unpkSwp_ndNN`, `svc_ndNN`, `ownStlr_ndNN`, `texit_ndNN`, `call_ndTS`,
`fn_segTS`) and `SegTC`'s combinators (`Spike/Lib/SegThrS.lean`). Each
segment also keeps a fragment `Z` at its nodes, given per node as
`NodeZ Z exe (N i) (lenN i)` (`hZ`; `hZU` for the unpark callee at every
ghost return frame).

- `Unpark.seg_unparkNN`: `Unpark.seg_unpark`.
- `Wake.WkTailW.seg_wkTailWNN`, `seg_unparkCallWNN`, `seg_wkTailWUNN`: the
  `WkTailW` segments (the call's callee given over `SegTC`).
- `Wake.ThrTailW.seg_thrTailWNN`: `ThrTailW.seg_thrTailW`.
- `Wake.ThrHeadW.seg_thrHeadWNN`: `ThrHeadW.seg_thrHeadW` (`hwk` over
  `SegTC`).
-/
import Spike.Lib.A64WakeWorker
import Spike.Lib.A64WakeNN

namespace Spike.Lib.A64.Flow.Worker

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (ValRep)
open Spike.Lib.A64.Flow.Ret0 (StOk land_ldStep)
open Spike.Lib.A64.Flow.Park (swpDir)

namespace Unpark

/-- Each node's block length (`1` at the single-instruction leaves), the
`len` of its `NodeZ` obligation. -/
def lenN : PN → Nat
  | .e => b0.length | .n1 => b1.length | .swp => 1 | .n2 => b2.length | .n3 => b3.length
  | .wake => b4.length | .svc => 1 | .n5 => b5.length | .done => b6.length

section ProofNN

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 c1 : Ctl}
  {B x29 ra tp : BitVec 64} {Z : Frag isaLSE2}

set_option hygiene false in
/-- A block node off the transfer sites: the block, its `okBlk`, its code;
the edge is left. -/
local macro "unode " b:ident ok:ident f:ident : tactic =>
  `(tactic| refine seg_ndNN (by simp [$b:ident]) $ok (by simp [$b:ident, notNop]) hF hR hal hlo hhi
    (fun s he hn => hcode.$f s he hn) (fun σ c hJ => ⟨c, .refl c, ?_⟩) (hZ _))

/-- Hitting node `j`. -/
local macro "uhit " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;> simp_all [N, JI, JS, JE, JX, Spike.Lib.upd_apply, Reg64s.getSysReg, svcStep, ldStep, KeepTP.setRegOrZr_tp, KeepTP.setXReg_tp]))

/-- Hitting exit `x`. -/
local macro "uexit " x:term : tactic =>
  `(tactic| (refine .inr ⟨$x, ?_, rfl, ?_⟩ <;> simp_all [N, E, JI, JS, JE, JX, Spike.Lib.upd_apply, Reg64s.getSysReg, svcStep, ldStep, KeepTP.setRegOrZr_tp, KeepTP.setXReg_tp]))

/-- **`seg_unpark` off the transfer sites**: the same segment over
`SegTC (NNZ exe endPc Z)`. -/
theorem seg_unparkNN (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48)
    (hhi : 0 ≤ R.hi) (hK : ms.K = some Scc.Sem.A64.abi)
    (hS : StOk ms F exe endPc (B + 16#64) 1#64) (htp4 : (B + 16#64).toNat % 4 = 0)
    {x : String} {a : CoreTerm.At} {e : Expr} {ty : Ty} {jw : TermRun.Word}
    (ht : c0.term = .let_ x (.ext .unpark a) e) (hh : c0.hold = none)
    (hev : TermRun.evalAt c0.env a = some (ty, [jw])) (hv : ValRep lbl jw.val B.toNat)
    (hc1 : c1 = ⟨e, (x, ExtName.unpark.sig.2, []) :: c0.env, none⟩)
    (hcode : Code c0 c1 B x29 ra tp exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".L11_scc_rt_unpark.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_unpark" + 4 + 4 + 4 + 4 + 4)
    (hZ : ∀ i, NodeZ Z exe (N (_root_.Executable.labels exe).label c0 c1 B x29 ra tp i) (lenN i)) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 B x29 ra tp .e))
      (fun s c => ∃ x, At exe endPc R F (E c1 x29 ra tp x) s c) := by
  refine fn_segTS (N := N _ c0 c1 B x29 ra tp) (E := E c1 x29 ra tp) (fun i => ?_) PN.e
  cases i
  case e => unode b0 b0_ok e; rw [N, b0_run]; uhit PN.n1
  case n1 => unode b1 b1_ok n1; rw [N, b1_run]; uhit PN.swp
  case swp =>
    refine unpkSwp_ndNN (A := B + 16#64) (B := B) hF (fun s he hn => hcode.swp s he hn) (fun m σ c _ _ hJ => ?_) (hZ _)
    obtain ⟨⟨rfl, hJ⟩, h10, h9⟩ := hJ
    refine ⟨h10, by rw [Spike.Lib.A64.Flow.Ret0.getRegOrZr_x9, h9], hS, rfl, x, a, e, ty, jw, ht, hh, hev, hv,
      fun v => ?_⟩
    rw [← hc1]
    uhit PN.n2
  case n2 =>
    unode b2 b2_ok n2; rw [N, b2_run]
    split
    · uhit PN.wake
    · uhit PN.n3
  case n3 => unode b3 b3_ok n3; rw [N, b3_run]; uhit PN.done
  case wake => unode b4 b4_ok wake; rw [N, b4_run]; uhit PN.svc
  case svc =>
    refine svc_ndNN hK hF (fun s he hn => hcode.svc s he hn) (fun σ c hJ => ?_) ?_ ?_ (hZ _)
    · obtain ⟨hT, h0, h1, h2, h8⟩ := hJ
      refine ⟨_, svcCall_futexWake (by rw [h8]; rfl) (by rw [h1]; rfl) (by rw [← htp4, ← h0]; rfl),
        fun v _ => ⟨c, .refl c, ?_⟩⟩
      uhit PN.n5
    · rintro s c σ call - ⟨-, h0, h1, h2, h8⟩ hcall
      rw [svcCall_futexWake (by rw [h8]; rfl) (by rw [h1]; rfl) (by rw [← htp4, ← h0]; rfl)] at hcall
      cases hcall
      exact ⟨nofun, nofun, nofun, nofun⟩
    · rintro σ c ⟨-, h0, h1, h2, h8⟩ call hcall
      rw [svcCall_futexWake (by rw [h8]; rfl) (by rw [h1]; rfl) (by rw [← htp4, ← h0]; rfl)] at hcall
      cases hcall
      exact .inr ⟨nofun, nofun⟩
  case n5 => unode b5 b5_ok n5; rw [N, b5_run]; uexit PX.ret
  case done => unode b6 b6_ok done; rw [N, b6_run]; uexit PX.ret

end ProofNN

end Unpark

namespace Wake

open Spike.Lib Spike.Lib.A64.Flow

namespace WkTailW

/-- Each node's block length (`1` at the store, `0` at the call), the `len`
of its `NodeZ` obligation. -/
def lenN : PN → Nat
  | .e => b0.length | .st => 1 | .n3 => b1.length | .bl => b2.length | .unpk => 0 | .sp1 => b3.length

section ProofNN

variable {pfx : String} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 c1 c2 : Ctl}
  {A B x29 ra tp : BitVec 64} {Z : Frag isaLSE2}

set_option hygiene false in
/-- A block node off the transfer sites: the block, its `okBlk`, its code;
the edge is left. -/
local macro "wnode " b:ident ok:ident f:ident : tactic =>
  `(tactic| refine seg_ndNN (by simp [$b:ident]) $ok (by simp [$b:ident, notNop]) hF hR hal hlo hhi
    (fun s he hn => hcode.$f s he hn) (fun σ c hJ => ⟨c, .refl c, ?_⟩) (hZ _))

/-- Hitting node `j`. -/
local macro "whit " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;> simp_all [N, JI, Spike.Lib.upd_apply, Reg64s.getSysReg, KeepTP.setRegOrZr_tp, KeepTP.setXReg_tp]))

/-- **`seg_wkTailW` off the transfer sites** (`hunpk` over `SegTC`). -/
theorem seg_wkTailWNN (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -32)
    (hhi : 0 ≤ R.hi) (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    {d : String} {a b : CoreTerm.At} {e1 : Expr} {ty tb : Ty} {w wb : TermRun.Word}
    (ht : c0.term = .let_ d (.store true a b none) e1) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hv : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hevb : TermRun.evalAt c0.env b = some (tb, [wb])) (hvb : ValRep lbl wb.val 1)
    (hc1 : c1 = ⟨e1, (d, .unit, []) :: c0.env, none⟩)
    (hcode : Code pfx c0 c1 c2 A B x29 ra tp exe endPc)
    (hunpk : SegTC (NNZ exe endPc Z) p lbl ms
      (At exe endPc R F (N pfx (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .unpk))
      (At exe endPc R F (N pfx (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .sp1)))
    (hZ : ∀ i, NodeZ Z exe (N pfx (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp i) (lenN i)) :
    SegTC (NNZ exe endPc Z) p lbl ms
      (At exe endPc R F (N pfx (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .e))
      (fun s c => ∃ x, At exe endPc R F (E c2 x29 ra tp x) s c) := by
  refine fn_segTS (N := N pfx _ c0 c1 c2 A B x29 ra tp) (E := E c2 x29 ra tp) (fun i => ?_) PN.e
  cases i
  case e => wnode b0 b0_ok e; rw [N, b0_run]; whit PN.st
  case st =>
    refine relStore_ndNN (A := A) (fun s he hn => hcode.st s he hn) hdm (fun m σ c _ _ hJ => ?_) (hZ _)
    obtain ⟨⟨rfl, hJ⟩, h10, h9⟩ := hJ
    refine ⟨h10, d, a, b, e1, ty, tb, w, wb, ht, hev, hv, htag, hevb,
      by rw [Spike.Lib.A64.Flow.Ret0.getRegOrZr_x9, h9]; exact hvb, ?_⟩
    rw [← hc1]
    whit PN.n3
  case n3 => wnode b1 b1_ok n3; rw [N, b1_run]; whit PN.bl
  case bl => wnode b2 b2_ok bl; rw [N, b2_run]; whit PN.unpk
  case unpk => exact hunpk.mono_post fun s c h => .inl ⟨PN.sp1, h⟩
  case sp1 =>
    wnode b3 b3_ok sp1; rw [N, b3_run]
    refine .inr ⟨PX.ret, ?_, rfl, ?_⟩ <;> simp_all [N, E, JI]

/-- **`seg_unparkCallW` off the transfer sites** (`call_ndTS` with
`Unpark.seg_unparkNN`). -/
theorem seg_unparkCallWNN (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -80)
    (hhi : 0 ≤ R.hi) (hK : ms.K = some Scc.Sem.A64.abi)
    (hS : StOk ms F exe endPc (B + 16#64) 1#64) (htp4 : (B + 16#64).toNat % 4 = 0)
    {x : String} {a : CoreTerm.At} {e : Expr} {ty : Ty} {jw : TermRun.Word}
    (ht : c1.term = .let_ x (.ext .unpark a) e) (hh : c1.hold = none)
    (hev : TermRun.evalAt c1.env a = some (ty, [jw])) (hv : ValRep lbl jw.val B.toNat)
    (hc2 : c2 = ⟨e, (x, ExtName.unpark.sig.2, []) :: c1.env, none⟩)
    {c0' c1' : Ctl} {B' x29' ra' tp' : BitVec 64} (hpcode : Unpark.Code c0' c1' B' x29' ra' tp' exe endPc)
    (hpentry : (_root_.Executable.labels exe).label ".L11_scc_rt_unpark.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_unpark" + 4 + 4 + 4 + 4 + 4)
    (hsp1 : (_root_.Executable.labels exe).label (pfx ++ ".sp1") =
      pcBl pfx (_root_.Executable.labels exe).label + 4)
    (hZU : ∀ x29' ra', ∀ i, NodeZ Z exe (Unpark.N (_root_.Executable.labels exe).label c1 c2 B x29' ra' tp i)
      (Unpark.lenN i)) :
    SegTC (NNZ exe endPc Z) p lbl ms
      (At exe endPc R F (N pfx (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .unpk))
      (At exe endPc R F (N pfx (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .sp1)) := by
  refine (call_ndTS (lo' := -48) (hi' := 0)
    (N := fun _ : Unit => N pfx (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .sp1)
    (E := fun e : Empty => e.elim)
    (Ne := fun g : BitVec 64 × BitVec 64 => Unpark.N (_root_.Executable.labels exe).label c1 c2 B g.1 g.2 tp .e)
    (Ex := fun g y => Unpark.E c2 g.1 g.2 tp y)
    hR hal hF (by show R.lo ≤ -32 + -48; omega) (by decide) (by show (-32 : Int) < R.hi; omega) (by decide)
    (by show (-32 : Int) % 16 = 0; decide) (by decide) (by decide)
    (fun R' F' hR' hal' hlo' hhi' hF' hFF g =>
      Unpark.seg_unparkNN hF' hR' hal' hlo' hhi' hK (hS.mono hFF) htp4 ht hh hev hv hc2 hpcode.ghost hpentry
        (hZU g.1 g.2))
    (fun _ => rfl) ?_ ?_).mono_post fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
  · rintro σC c ⟨⟨rfl, -, -, -, -, htp⟩, h0, -⟩
    exact ⟨(σC.regs.X29.toBitVec, σC.regs.X30.toBitVec), rfl, rfl, h0, rfl, rfl, htp⟩
  · rintro ⟨x29', ra'⟩ ⟨⟩ σC c σx c' σR ⟨⟨rfl, h16, h8, h32, h24, -⟩, -, h30⟩ ⟨-, -, -, hra, -⟩ ⟨hc', -, -, htp'⟩ hreg -
      hslot
    have hout : ∀ k : Int, -32 ≤ k → k % 8 = 0 → k + 8 ≤ 0 → σR.slot k = σC.slot k := fun k h1 h2 h3 =>
      hslot k ⟨h2, by omega, by omega⟩ fun ⟨_, _, h⟩ => by
        simp only [Region.callee, N] at h; omega
    refine .inl ⟨(), ?_, rfl, hc', ?_, ?_, ?_, ?_, ?_⟩
    · subst hra
      show (_root_.Executable.labels exe).label (pfx ++ ".sp1") = Int64.ofBitVec σC.regs.X30.toBitVec
      rw [h30, hsp1, Ret0.ofInt_bmod, BitVec.ofInt_add, Spike.Lib.int64_ofInt_toInt]; rfl
    · rw [hout (-16) (by decide) (by decide) (by decide)]; exact h16
    · rw [hout (-8) (by decide) (by decide) (by decide)]; exact h8
    · rw [hout (-32) (by decide) (by decide) (by decide)]; exact h32
    · rw [hout (-24) (by decide) (by decide) (by decide)]; exact h24
    · show σR.regs.TPIDR_EL0.toBitVec = tp
      rw [hreg]; exact htp'

/-- **`seg_wkTailWU` off the transfer sites** (`seg_wkTailWNN` with
`seg_unparkCallWNN`). -/
theorem seg_wkTailWUNN (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -80)
    (hhi : 0 ≤ R.hi) (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    {d : String} {a b : CoreTerm.At} {e1 : Expr} {ty tb : Ty} {w wb : TermRun.Word}
    (ht : c0.term = .let_ d (.store true a b none) e1) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hv : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hevb : TermRun.evalAt c0.env b = some (tb, [wb])) (hvb : ValRep lbl wb.val 1)
    (hc1 : c1 = ⟨e1, (d, .unit, []) :: c0.env, none⟩)
    (hcode : Code pfx c0 c1 c2 A B x29 ra tp exe endPc)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hS : StOk ms F exe endPc (B + 16#64) 1#64) (htp4 : (B + 16#64).toNat % 4 = 0)
    {x : String} {au : CoreTerm.At} {e : Expr} {tu : Ty} {jw : TermRun.Word}
    (htu : c1.term = .let_ x (.ext .unpark au) e) (hhu : c1.hold = none)
    (hevu : TermRun.evalAt c1.env au = some (tu, [jw])) (hvu : ValRep lbl jw.val B.toNat)
    (hc2 : c2 = ⟨e, (x, ExtName.unpark.sig.2, []) :: c1.env, none⟩)
    {c0' c1' : Ctl} {B' x29' ra' tp' : BitVec 64} (hpcode : Unpark.Code c0' c1' B' x29' ra' tp' exe endPc)
    (hpentry : (_root_.Executable.labels exe).label ".L11_scc_rt_unpark.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_unpark" + 4 + 4 + 4 + 4 + 4)
    (hsp1 : (_root_.Executable.labels exe).label (pfx ++ ".sp1") =
      pcBl pfx (_root_.Executable.labels exe).label + 4)
    (hZ : ∀ i, NodeZ Z exe (N pfx (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp i) (lenN i))
    (hZU : ∀ x29' ra', ∀ i, NodeZ Z exe (Unpark.N (_root_.Executable.labels exe).label c1 c2 B x29' ra' tp i)
      (Unpark.lenN i)) :
    SegTC (NNZ exe endPc Z) p lbl ms
      (At exe endPc R F (N pfx (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .e))
      (fun s c => ∃ x, At exe endPc R F (E c2 x29 ra tp x) s c) :=
  seg_wkTailWNN hF hR hal (Int.le_trans hlo (by decide)) hhi hdm ht hev hv htag hevb hvb hc1 hcode
    (seg_unparkCallWNN hF hR hal hlo hhi hK hS htp4 htu hhu hevu hvu hc2 hpcode hpentry hsp1 hZU) hZ

end ProofNN

end WkTailW

namespace ThrTailW

/-- Each node's block length (`1` at the store and the `svc`), the `len` of
its `NodeZ` obligation. -/
def lenN : PN → Nat
  | .sp0 => b0.length | .ex => 1 | .n2 => b1.length | .svc => 1

section ProofNN

variable {pfx : String} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {tp : BitVec 64}
  {Z : Frag isaLSE2}

set_option hygiene false in
/-- A block node off the transfer sites: the block, its `okBlk`, its code;
the edge is left. -/
local macro "tnode " b:ident ok:ident f:ident : tactic =>
  `(tactic| refine seg_ndNN (by simp [$b:ident]) $ok (by simp [$b:ident, notNop]) hF hR hal hlo hhi
    (fun s he hn => hcode.$f s he hn) (fun σ c hJ => ⟨c, .refl c, ?_⟩) (hZ _))

/-- Hitting node `j`. -/
local macro "thit " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;> simp_all [N, Spike.Lib.upd_apply, Reg64s.getSysReg, KeepTP.setRegOrZr_tp, KeepTP.setXReg_tp]))

/-- **`seg_thrTailW` off the transfer sites.** -/
theorem seg_thrTailWNN {Q : Frag isaLSE2} (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) (hK : ms.K = some Scc.Sem.A64.abi)
    (hS : StOk ms F exe endPc (tp + 24#64) 1#64) {a : CoreTerm.At} (ht : c0.term = .ret a)
    (hcode : Code pfx c0 tp exe endPc)
    (hZ : ∀ i, NodeZ Z exe (N pfx (_root_.Executable.labels exe).label c0 tp i) (lenN i)) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F (N pfx (_root_.Executable.labels exe).label c0 tp .sp0)) Q := by
  refine (fn_segTS (N := N pfx _ c0 tp) (E := (nofun : Empty → ND)) (fun i => ?_) PN.sp0).mono_post
    fun _ _ ⟨x, _⟩ => x.elim
  cases i
  case sp0 => tnode b0 b0_ok sp0; rw [N, b0_run]; thit PN.ex
  case ex =>
    refine ownStlr_ndNN (A := tp + 24#64) (fun s he hn => hcode.ex s he hn) (fun m σ c _ _ hJ => ?_) (hZ _)
    obtain ⟨rfl, h10, h9⟩ := hJ
    refine ⟨h10, by rw [Spike.Lib.A64.Flow.Ret0.getRegOrZr_x9, h9]; exact hS, ?_⟩
    thit PN.n2
  case n2 => tnode b1 b1_ok n2; rw [N, b1_run]; thit PN.svc
  case svc =>
    refine texit_ndNN hK (fun s he hn => hcode.svc s he hn) (fun σ c ⟨hc, h8⟩ => ⟨by rw [h8]; rfl, a, ?_⟩) (hZ _)
    rw [hc]; exact ht

end ProofNN

end ThrTailW

namespace ThrHeadW

/-- Each node's block length (`0` at the call), the `len` of its `NodeZ`
obligation. -/
def lenN : TN → Nat
  | .e => thE.length | .call => 0

section ProofNN

variable {pfx : String} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {Z : Frag isaLSE2}

/-- **`seg_thrHeadW` off the transfer sites** (`hwk` over `SegTC`). -/
theorem seg_thrHeadWNN {ι κ : Sort _} {N : ι → ND} {E : κ → ND} (hF : FStable R F) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -128) (hhi : 0 ≤ R.hi) {J : AS → Ctl → Prop}
    {L : Ctl → Ctl → Prop} (hL : ∀ σ c, J σ c → ∃ c', LocalRun p c c' ∧ L c c')
    (hcodeE : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s ((_root_.Executable.labels exe).label (pfx ++ ".0_entry")) thE)
    {γ : Type _} {κ' : Sort _} {Ne : γ → ND} {Ex : γ → κ' → ND}
    (hwk : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -80 →
      0 ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → ∀ g,
        SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R' F' (Ne g)) (fun s c => ∃ x, At exe endPc R' F' (Ex g x) s c))
    (hNe : ∀ g, (Ne g).o = ⟨0, []⟩)
    (hent : ∀ σC c, (tN pfx (_root_.Executable.labels exe).label J L .call).J σC c →
      ∃ g, (Ne g).pc = (_root_.Executable.labels exe).label "wc_worker" ∧ (Ne g).J (enter (-48) σC) c)
    (hret : ∀ g x σC c σx c' (σR : AS), (tN pfx (_root_.Executable.labels exe).label J L .call).J σC c →
      (Ne g).J (enter (-48) σC) c → (Ex g x).J σx c' →
      σR.regs = σx.regs → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee (-48) (-80) 0).Off (k - (-48)) → σR.slot k = σC.slot k) →
      Lands N E ⟨(Ex g x).pc, ⟨-48 + (Ex g x).o.sp, []⟩, σR⟩ c')
    (hZ : ∀ i, NodeZ Z exe (tN pfx (_root_.Executable.labels exe).label J L i) (lenN i)) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F (tN pfx (_root_.Executable.labels exe).label J L .e))
      (Next exe endPc R F N E) := by
  let lab := (_root_.Executable.labels exe).label
  refine SegTC.seq (Q := At exe endPc R F (tN pfx lab J L .call))
    ((seg_ndNN (N := fun _ : Unit => tN pfx lab J L .call) (E := (nofun : Empty → ND)) (by simp [thE]) thE_ok
      (by simp [thE, notNop]) hF hR hal hlo hhi hcodeE (fun σ c hJ => ?_) (hZ .e)) |>.mono_post ?_) ?_
  · obtain ⟨c', hr, hl⟩ := hL σ c hJ
    refine ⟨c', hr, .inl ⟨(), ?_, ?_, σ, c, hJ, hl, rfl⟩⟩
    · simp only [tN]; rw [thE_run]
    · simp only [tN]; rw [thE_run]; rfl
  · rintro s c (⟨_, h⟩ | ⟨y, _⟩)
    · exact h
    · exact y.elim
  · exact call_ndTS (lo' := -80) (hi' := 0) hR hal hF (by show R.lo ≤ -48 + -80; omega) (by decide)
      (by show (-48 : Int) < R.hi; omega) (by decide) (by show (-48 : Int) % 16 = 0; decide) (by decide)
      (by decide) hwk hNe hent hret

end ProofNN

end ThrHeadW

end Wake

end Spike.Lib.A64.Flow.Worker
