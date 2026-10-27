/-
**`hello1.w`'s `wc_rodata` from the allocator's return, with the source's
local steps, on x64**: `hello1_rodata_post_segW`
(`Spike/Lib/X64Hello1Rodata.lean`) with the source advanced by a local run
before each exchange's load, for a source that builds each stored word in a
`let` before its exchange (`hello1`'s `rodata`,
`Spike/Lib/Hello1RodataSrc.lean`). The x64 twin of
`Spike/Lib/A64Hello1RodataPostS.lean`.

- `pNL`: `.x13`'s nodes, each exchange's load at the source's control after
  the run (`Jp'`, `J2'`);
- `RdPostLW`, `RdPostLW.triv`: their states inside `W`;
- `hello1_rodata_post_runW`: the segment, the first block taking a local run
  from `Jp`'s controls to `Jp'`'s (`hr0`), the third from `J2`'s to `J2'`'s
  (`hr2`).
-/
import Spike.Lib.X64Hello1RodataS

namespace Spike.Lib.X64.Flow.Hello1

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)

set_option linter.unusedSimpArgs false

/-! ## `wc_rodata` from the allocator's return, the source advanced -/

/-- **`.x13`'s nodes, the source advanced before each load**: as `pN`,
the first load at `Jp'` (the control after the first block's run) and the
second at `J2'` (after the third block's run). -/
def pNL (lab : Label → Int64) (Jp Jp' J1 J2 J2' J3 J4 : AS → Ctl → Prop) : PN → ND
  | .l1 => ⟨lab ".Lwc_rodata.x13" + 8, oR, fun σ c => ∃ σ0, (∃ c0, Jp σ0 c0) ∧
      Jp' σ0 c ∧ rdFr σ0 σ ∧ σ.regs.get64 .rcx = σ0.regs.get64 .rax⟩
  | .l2 => pN lab Jp J1 J2' J3 J4 .l2
  | i => pN lab Jp J1 J2 J3 J4 i

/-- **`wc_rodata`'s states from the allocator's return inside `W`**, the
source advanced (`pNL`), none moved by `K`: one obligation per node. -/
structure RdPostLW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (Jp Jp' J1 J2 J2' J3 J4 : AS → Ctl → Prop) : Prop where
  s0 : BlkW W K exe endPc R F (pNL (_root_.Executable.labels exe).label Jp Jp' J1 J2 J2' J3 J4 .s0) rpB0
  l1 : NodeW W K exe endPc R F (pNL (_root_.Executable.labels exe).label Jp Jp' J1 J2 J2' J3 J4 .l1)
  s1 : BlkW W K exe endPc R F (pNL (_root_.Executable.labels exe).label Jp Jp' J1 J2 J2' J3 J4 .s1) rpB1
  x1 : NodeW W K exe endPc R F (pNL (_root_.Executable.labels exe).label Jp Jp' J1 J2 J2' J3 J4 .x1)
  s2 : BlkW W K exe endPc R F (pNL (_root_.Executable.labels exe).label Jp Jp' J1 J2 J2' J3 J4 .s2) rpB2
  l2 : NodeW W K exe endPc R F (pNL (_root_.Executable.labels exe).label Jp Jp' J1 J2 J2' J3 J4 .l2)
  s3 : BlkW W K exe endPc R F (pNL (_root_.Executable.labels exe).label Jp Jp' J1 J2 J2' J3 J4 .s3) rpB3
  x2 : NodeW W K exe endPc R F (pNL (_root_.Executable.labels exe).label Jp Jp' J1 J2 J2' J3 J4 .x2)
  s4 : BlkW W K exe endPc R F (pNL (_root_.Executable.labels exe).label Jp Jp' J1 J2 J2' J3 J4 .s4) rpB4

/-- The trivial predicate, with no outside moves. -/
theorem RdPostLW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {Jp Jp' J1 J2 J2' J3 J4 : AS → Ctl → Prop} :
    RdPostLW (fun _ _ => True) (fun _ _ => False) exe endPc R F Jp Jp' J1 J2 J2' J3 J4 :=
  ⟨BlkW.triv, NodeW.triv, BlkW.triv, NodeW.triv, BlkW.triv, NodeW.triv, BlkW.triv, NodeW.triv, BlkW.triv⟩

section RpFn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_rodata` from the allocator's return, the source advanced, is one
segment inside `W`**: `hello1_rodata_post_segW` where the first block takes
a local run from each control of `Jp` to one of `Jp'` (`hr0`) and the third
from each of `J2` to one of `J2'` (`hr2`), the loads' facts asked at `Jp'`
and `J2'` (`h1`, `h3`). -/
theorem hello1_rodata_post_runW {W : Frag isa} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Cells) (hend : endPc = endOf exe SccCode.hello1Cells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 8 ≤ R.hi)
    {Jp Jp' J1 J2 J2' J3 J4 : AS → Ctl → Prop} {x : ND} (ho : SO.le x.o ⟨8, []⟩ = true)
    (hW : RdPostLW W K exe endPc R F Jp Jp' J1 J2 J2' J3 J4)
    (hbp : ∀ σ0 c, Jp σ0 c → σ0.regs.get64 .rbp = R.addr (-8))
    (hra : ∀ σ0 c, Jp σ0 c → x.pc = Int64.ofBitVec (σ0.slot 0))
    (hmem : ∀ σ0 c, Jp σ0 c → ∀ i : Int64, (i = 0 ∨ i = 8) →
      ∀ m, F m → Mem.loadInt m.dmem (bAddr σ0.regs .rax i) 8 = none)
    (hr0 : ∀ σ0 c, Jp σ0 c → ∃ c', LocalRun p c c' ∧ Jp' σ0 c')
    (h1 : ∀ σ0 c, Jp' σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 0).toNat ∧ c.hold = none ∧
      ∀ (r : Val) (w' : TermRun.Word), ms.rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
        J1 σ0 { c with hold := some ((bAddr σ0.regs .rax 0).toNat, w') })
    (h2 : ∀ σ0 c, J1 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
      (wv wold : TermRun.Word),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 0).toNat ∧
      c.hold = some ((bAddr σ0.regs .rax 0).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
      Scc.Sem.ValRep lbl wv.val (rpK1.setWidth 128).toNat ∧ J2 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩)
    (hr2 : ∀ σ0 c, J2 σ0 c → ∃ c', LocalRun p c c' ∧ J2' σ0 c')
    (h3 : ∀ σ0 c, J2' σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 8).toNat ∧ c.hold = none ∧
      ∀ (r : Val) (w' : TermRun.Word), ms.rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
        J3 σ0 { c with hold := some ((bAddr σ0.regs .rax 8).toNat, w') })
    (h4 : ∀ σ0 c, J3 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
      (wv wold : TermRun.Word),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 8).toNat ∧
      c.hold = some ((bAddr σ0.regs .rax 8).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
      Scc.Sem.ValRep lbl wv.val (rpK2.setWidth 128).toNat ∧ J4 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩)
    (hedge : ∀ σ0 c, J4 σ0 c → ∀ σ' : AS, σ'.regs.rax.toBitVec = σ0.regs.rax.toBitVec →
      σ'.regs.rdx.toBitVec = 0#64 → σ'.regs.rcx.toBitVec = 2#64 → σ'.regs.rsi.toBitVec = 13#64 →
      σ'.regs.rbp.toBitVec = σ0.slot (-8) → σ'.regs.rsp.toBitVec = σ0.regs.rbp.toBitVec + 8#64 + 8#64 →
      ∃ c', LocalRun p c c' ∧ x.J σ' c') :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label ".Lwc_rodata.x13", ⟨-40, []⟩, Jp⟩)
      (At exe endPc R F x) := by
  have hin := hello1_rpIn
  simp only [rpIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨c0, c1⟩, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  refine ((fn_segW (N := pNL lab Jp Jp' J1 J2 J2' J3 J4) (E := fun _ : Unit => x) (fun i => ?_) PN.s0).mono_post
    fun _ _ ⟨_, h⟩ => h).mono_pre fun _ _ h => At.rbp_addr h hbp
  cases i
  case s0 =>
    refine seg_ndW (by simp [rpB0]) rpB0_ok hF hR hlo hhi (code_field hp hend c0 (ofNat_zero' _)) hW.s0
      fun σ c hJ => ?_
    obtain ⟨c', hr, hJ'⟩ := hr0 σ c hJ
    refine ⟨c', hr, .inl ⟨PN.l1, ?_, ?_, σ, ⟨c, hJ⟩, hJ', ?_⟩⟩
    · simp only [pNL, pN]; rw [rpB0_run]
    · simp only [pNL, pN]; rw [rpB0_run]; rfl
    · simp only [pNL, pN]; rw [rpB0_run]
      refine ⟨⟨?_, ?_, ?_, rfl⟩, by dsimp only; rw [Reg64s.get64_set64_self]; try rfl⟩ <;> simp [Spike.Lib.upd_apply]
  case l1 =>
    refine holdLd_ndW (r := .rax) (b := .rcx) (k := 0) (by decide) hF (code_field hp hend c1 rfl) hW.l1
      fun m σ c hA hD ⟨σ0, ⟨c0', hJp⟩, hJ, hfr, hcx⟩ => ?_
    have hr := bAddr_rcx_rax hcx 0
    have hm := hmem σ0 c0' hJp 0 (.inl rfl)
    obtain ⟨x, sa, u, v, e, hx, hv, hh, hk⟩ := h1 σ0 c hJ
    refine ⟨hr ▸ hm m hD, x, sa, u, v, e, hx, hr ▸ hv, hh, fun r w' hrd hrep =>
      .inl ⟨PN.s1, ?_, rfl, σ0, ⟨c0', hJp⟩, hr ▸ hk r w' hrd hrep, hfr⟩⟩
    show lab ".Lwc_rodata.x13" + 11 = lab ".Lwc_rodata.x13" + 8 + Int64.ofNat 3
    rw [Int64.add_assoc]; rfl
  case s1 =>
    refine seg_ndW (by simp [rpB1]) rpB1_ok hF hR hlo hhi (code_field hp hend c2 rfl) hW.s1
      fun σ c ⟨σ0, hJp, hJ, hfr⟩ => ⟨c, .refl c, .inl ⟨PN.x1, ?_, ?_, σ0, hJp, hJ, ?_⟩⟩
    · simp only [pNL, pN]; rw [rpB1_run, Int64.add_assoc]; rfl
    · simp only [pNL, pN]; rw [rpB1_run]; rfl
    · simp only [pNL, pN]; rw [rpB1_run]
      refine ⟨⟨?_, ?_, ?_, ?_⟩, by dsimp only; rw [Reg64s.get64_set64_self]; try rfl, ?_⟩
      · simp only [Spike.Lib.upd_apply]; exact hfr.1
      · simp only [Spike.Lib.upd_apply]; exact hfr.2.1
      · simp only [Spike.Lib.upd_apply]; exact hfr.2.2.1
      · simp only [Reg64s.set64]; exact hfr.2.2.2
      · rw [Reg64s.get64_set64_ne _ (by decide), Reg64s.get64_set64_self]; exact hfr.1
  case x1 =>
    refine xchgSt_ndW (r := .rax) (b := .rcx) (k := 0) (code_field hp hend c3 rfl) hW.x1
      fun m σ c hA hD ⟨σ0, ⟨c0', hJp⟩, hJ, hfr, hax, hcx⟩ => ?_
    have hr := bAddr_rcx_rax hcx 0
    have hm := hmem σ0 c0' hJp 0 (.inl rfl)
    obtain ⟨x, sa, u, v, e, tv, wv, wold, hx, hv, hh, hev, hV, hk⟩ := h2 σ0 c hJ
    refine ⟨hr ▸ hm m hD, x, sa, u, v, e, tv, wv, wold, hx, hr ▸ hv, hr ▸ hh, hev,
      by rw [hax]; exact hV, .inl ⟨PN.s2, ?_, rfl, σ0, ⟨c0', hJp⟩, hk, hfr⟩⟩
    show lab ".Lwc_rodata.x13" + 32 = lab ".Lwc_rodata.x13" + 29 + Int64.ofNat 3
    rw [Int64.add_assoc]; rfl
  case s2 =>
    refine seg_ndW (by simp [rpB2]) rpB2_ok hF hR hlo hhi (code_field hp hend c4 rfl) hW.s2
      fun σ c ⟨σ0, hJp, hJ, hfr⟩ => ?_
    obtain ⟨c', hr, hJ'⟩ := hr2 σ0 c hJ
    refine ⟨c', hr, .inl ⟨PN.l2, ?_, ?_, σ0, hJp, hJ', ?_⟩⟩
    · simp only [pNL, pN]; rw [rpB2_run, Int64.add_assoc]; rfl
    · simp only [pNL, pN]; rw [rpB2_run]; rfl
    · simp only [pNL, pN]; rw [rpB2_run]
      exact ⟨⟨hfr.1, hfr.2.1, hfr.2.2.1, hfr.2.2.2⟩, by rw [Reg64s.get64_set64_self]; exact hfr.1⟩
  case l2 =>
    refine holdLd_ndW (r := .rax) (b := .rcx) (k := 8) (by decide) hF (code_field hp hend c5 rfl) hW.l2
      fun m σ c hA hD ⟨σ0, ⟨c0', hJp⟩, hJ, hfr, hcx⟩ => ?_
    have hr := bAddr_rcx_rax hcx 8
    have hm := hmem σ0 c0' hJp 8 (.inr rfl)
    obtain ⟨x, sa, u, v, e, hx, hv, hh, hk⟩ := h3 σ0 c hJ
    refine ⟨hr ▸ hm m hD, x, sa, u, v, e, hx, hr ▸ hv, hh, fun r w' hrd hrep =>
      .inl ⟨PN.s3, ?_, rfl, σ0, ⟨c0', hJp⟩, hr ▸ hk r w' hrd hrep, hfr⟩⟩
    show lab ".Lwc_rodata.x13" + 40 = lab ".Lwc_rodata.x13" + 36 + Int64.ofNat 4
    rw [Int64.add_assoc]; rfl
  case s3 =>
    refine seg_ndW (by simp [rpB3]) rpB3_ok hF hR hlo hhi (code_field hp hend c6 rfl) hW.s3
      fun σ c ⟨σ0, hJp, hJ, hfr⟩ => ⟨c, .refl c, .inl ⟨PN.x2, ?_, ?_, σ0, hJp, hJ, ?_⟩⟩
    · simp only [pNL, pN]; rw [rpB3_run, Int64.add_assoc]; rfl
    · simp only [pNL, pN]; rw [rpB3_run]; rfl
    · simp only [pNL, pN]; rw [rpB3_run]
      refine ⟨⟨?_, ?_, ?_, ?_⟩, by dsimp only; rw [Reg64s.get64_set64_self]; try rfl, ?_⟩
      · simp only [Spike.Lib.upd_apply]; exact hfr.1
      · simp only [Spike.Lib.upd_apply]; exact hfr.2.1
      · simp only [Spike.Lib.upd_apply]; exact hfr.2.2.1
      · simp only [Reg64s.set64]; exact hfr.2.2.2
      · rw [Reg64s.get64_set64_ne _ (by decide), Reg64s.get64_set64_self]; exact hfr.1
  case x2 =>
    refine xchgSt_ndW (r := .rax) (b := .rcx) (k := 8) (code_field hp hend c7 rfl) hW.x2
      fun m σ c hA hD ⟨σ0, ⟨c0', hJp⟩, hJ, hfr, hax, hcx⟩ => ?_
    have hr := bAddr_rcx_rax hcx 8
    have hm := hmem σ0 c0' hJp 8 (.inr rfl)
    obtain ⟨x, sa, u, v, e, tv, wv, wold, hx, hv, hh, hev, hV, hk⟩ := h4 σ0 c hJ
    refine ⟨hr ▸ hm m hD, x, sa, u, v, e, tv, wv, wold, hx, hr ▸ hv, hr ▸ hh, hev,
      by rw [hax]; exact hV, .inl ⟨PN.s4, ?_, rfl, σ0, ⟨c0', hJp⟩, hk, hfr⟩⟩
    show lab ".Lwc_rodata.x13" + 62 = lab ".Lwc_rodata.x13" + 58 + Int64.ofNat 4
    rw [Int64.add_assoc]; rfl
  case s4 =>
    refine seg_ndW (by simp [rpB4]) rpB4_ok hF hR hlo hhi (code_field hp hend c8 rfl) hW.s4
      fun σ c ⟨σ0, ⟨c0', hJp⟩, hJ, hfr⟩ => ?_
    obtain ⟨h16, h8, h0, hbp'⟩ := hfr
    obtain ⟨c', hr, hx⟩ := hedge σ0 c hJ
      (arun lab rpB4 ⟨lab ".Lwc_rodata.x13" + 62, oR, σ⟩).σ
      (by rw [rpB4_run]; simp [Reg64s.set64, h16]) (by rw [rpB4_run]; simp [Reg64s.set64])
      (by rw [rpB4_run]; simp [Reg64s.set64]) (by rw [rpB4_run]; simp [Reg64s.set64])
      (by rw [rpB4_run]; simp [Reg64s.set64, h8]) (by rw [rpB4_run]; simp [Reg64s.set64, hbp'])
    refine ⟨c', hr, .inr ⟨(), ?_, ?_, hx⟩⟩
    · show x.pc = (arun lab rpB4 ⟨lab ".Lwc_rodata.x13" + 62, oR, σ⟩).pc
      rw [rpB4_run, hra σ0 c0' hJp, h0]
    · show x.o.le (arun lab rpB4 ⟨lab ".Lwc_rodata.x13" + 62, oR, σ⟩).so = true
      rw [rpB4_run]; exact ho

end RpFn

end Spike.Lib.X64.Flow.Hello1
