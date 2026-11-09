/-
**hello.w's `scc_rt_main` from `wc_rodata`'s `.x15` with the thread pointer kept** (x86-64; twin of
`Spike/Lib/A64HelloMainPostT.lean`).

`hello_rodata_post_runW`'s `hedge` hands the return node's invariant every state agreeing with `.x15`'s on
`%rax`, `%rdx`, `%rcx`, `%rsi`, `%rbp`, `%rsp` only, so no thread pointer can be asked of `wc_rodata`'s return
invariant `Jr` itself. Here it is read off the state instead, as `Hello1.hello1_rodata_setupW` does: `wc_rodata`'s
rest runs inside `NoSetFsW` (`rdPostW_noMsr`) under `tpXa`, so `SegW.keepTPN` carries `TP t` from `.x15` (where
`Jp`'s states have `%fs` base `t`, `hJpT`) to the return; leaving `wc_rodata`'s region (`at_leave`) the returned
state is `Jr`'s at `%fs` base `t`, `%rsp = R.addr (-72)` and `%rbp = R.addr (-8)` (`JrT`), and `scc_rt_main`'s
rest runs from `JrT`. The source's publication is taken as a stutter before `wc_rodata`'s last block
(`hello_rodata_post_runW`, a `SegWP`), so the segment is a `SegWSP` (`Spike/Lib/X64SegWPub.lean`).

- `rdPostW_noMsr`: `HelloRd.RdPostW` inside `NoSetFsW W K` in any valid layout of `helloCells`.
- `JrT Jr t R`: `Jr` at `%fs` base `t`, `scc_rt_main`'s `%rsp` past the return and its `%rbp`.
- `hello_main_post_segWST`: `scc_rt_main` from `wc_rodata`'s `.x15` (at `[fr]`) into `wc_main` (at `[]`), with
  `hW.sp0` and `hWc` at `JrT Jr t R`, from `Jp`'s thread pointer (`hJpT`) and the memory side's kernel (`hK'`).

## Differences from the AArch64 version

- The thread pointer is `%fs`'s base (`fsBase`, AArch64 `TPIDR_EL0`); a segment keeps it inside `NoSetFsW`
  (no `syscall` in the code, so no `arch_prctl(ARCH_SET_FS)`; AArch64 `NoMsrW`, no `msr`). The name
  `rdPostW_noMsr` is kept for the twin.
- `ret` pops the return address, so past the return `%rsp` is `R.addr (-72)` (AArch64 `sp = R.addr (-80)`).
- `RdPostW` has no fence node (scc's `# fence st` emits no code under TSO): the source's run at the fence
  (`hfen`, from `J4` into `J5`) is taken as a stutter before the last block's row, whose source invariant is
  `HelloRd.J4P J4 J4x` (the publication's targets in `J4x`, `hpubx`, each running locally into `J5`, `hlocx`);
  `hedge` is at `J5`, on `%rax`, `%rdx`, `%rcx`, `%rsi`, `%rbp`, `%rsp`. The segment is
  a `SegWSP` (AArch64: a `SegWS`, the publication on the `dmb ishst` row).
- `JrT` also pins `%rbp` at `R.addr (-8)`: the return restores `%rbp` from `.x15`'s `slot (-8)`, which `Jp`
  has at `R.addr (-8)` (`hsl`); `hello_rodata_post_runW`'s `hedge` sees `Jp`, so the return node's invariant is
  `retJH fr Jr` with that `%rbp` (`Jr` itself, the source's return, need not know it).
- `hello_rodata_post_runW` asks `.x15`'s `%rbp` of `Jp` (`hbp`), and `.x2`'s node knows `%rbp` at the saved
  `%rbp` (`Hello1.mO`); `hra` is about the stack top `σ0.slot 0` and `.Lscc_rt_main.x0` (AArch64: the saved
  `x30` at `-8`, `.L1_scc_rt_main.sp0`).
- No 16-alignment (`hD8 : D % 8 = 0`, no `hal`), `8 ≤ R.hi`; the buffer's words are at `%rax` (`bAddr`).
- Not twinned (unreachable from the AArch64 root, so twins only live constants): none.
-/
import Spike.Lib.X64HelloMainPostS
import Spike.Lib.X64Hello1RodataTP
import Spike.Lib.X64SegWPubTP

namespace Spike.Lib.X64.Flow.HelloM

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Hello1 (mR mF mR_ok mS0 mWC rpK1 rpK2)
open Spike.Lib.X64.Flow.HelloRd (RdPostW pN hello_rodata_post_runW hello_rpIn rpIn J4P)
open Spike.Lib.X64SegWPub (SegWP SegWSP)
open Spike.Lib.X64.KeepTP (TP tpXa)
open Spike.Lib.X64HelloRdCf (retJH)
open Scc.Cert.Rt.X64 (Lays endOf code_field)

/-- **`wc_rodata` from the allocator's return is inside `NoSetFsW W K`** in any valid layout of `helloCells`
(`Hello1.RdPostLW.noSetFs`'s twin). -/
theorem rdPostW_noMsr {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe]
    {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {W : Frag isa} {K : State → State → Prop} {kp : Nat} (hp : Lays exe SccCode.helloCells kp)
    (hend : endPc = endOf exe SccCode.helloCells kp) {Jp Jp' J1 J2 J2' J3 J4 : AS → Ctl → Prop}
    (h : RdPostW W K exe endPc R F Jp Jp' J1 J2 J2' J3 J4) :
    RdPostW (NoSetFsW W K) K exe endPc R F Jp Jp' J1 J2 J2' J3 J4 := by
  have hin := hello_rpIn
  simp only [rpIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨c0, c1⟩, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩ := hin
  exact ⟨BlkW.noSetFs h.s0 (code_field hp hend c0 (ofNat_zero' _)) (by decide),
    NodeW.noSetFs h.l1 (code_field hp hend c1 rfl) (by simp) (by decide),
    BlkW.noSetFs h.s1 (code_field hp hend c2 rfl) (by decide),
    NodeW.noSetFs h.x1 (code_field hp hend c3 rfl) (by simp) (by decide),
    BlkW.noSetFs h.s2 (code_field hp hend c4 rfl) (by decide),
    NodeW.noSetFs h.l2 (code_field hp hend c5 rfl) (by simp) (by decide),
    BlkW.noSetFs h.s3 (code_field hp hend c6 rfl) (by decide),
    NodeW.noSetFs h.x2 (code_field hp hend c7 rfl) (by simp) (by decide),
    BlkW.noSetFs h.s4 (Spike.Lib.X64.code_field_blockAcrossB hp hend c8 (List.take_append_drop _ _) rfl) (by decide)⟩

/-- **`wc_rodata`'s return invariant at the `%fs` base `t`, `scc_rt_main`'s `%rsp`** (`R.addr (-72)`, past
the popped return address, in `scc_rt_main`'s region `R`) **and its `%rbp`** (`R.addr (-8)`, `wc_rodata`'s
epilogue restoring the saved `%rbp`). -/
def JrT (Jr : AS → Ctl → Prop) (t : UInt64) (R : Region) (σ : AS) (c : Ctl) : Prop :=
  Jr σ c ∧ σ.regs.fsBase = t ∧ σ.regs.rsp.toBitVec = R.addr (-72) ∧ σ.regs.get64 .rbp = R.addr (-8)

section MainPostT

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`scc_rt_main` from `wc_rodata`'s `.x15` into `wc_main` at depth, the thread pointer kept**:
`wc_rodata`'s rest under `tpXa` inside `NoSetFsW` (`SegW.keepTPN`, from `Jp`'s `%fs` base `t`, `hJpT`), its
return popping the frame `fr`, then `scc_rt_main`'s rest (`hW.sp0`, `hWc`) from `JrT Jr t R`
(`hello_main_sp0_segW`). -/
theorem hello_main_post_segWST {W : FragS isa} {K : State → State → Prop} {fr : TermRun.Frame}
    {kp : Nat} (hp : Lays exe SccCode.helloCells kp) (hend : endPc = endOf exe SccCode.helloCells kp)
    (hK' : (ms [fr]).K = some Scc.Sem.X64.abi)
    {D : Int} (hD : 0 ≤ D) (hD8 : D % 8 = 0)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -288) (hloD : R.lo ≤ -80 - D)
    (hhi : 8 ≤ R.hi) (hfr : fr.σs = []) {m0 : MachineData} {σC : AS} {t : UInt64}
    {Jp Jp' J1 J2 J2' J3 J4 J4x J5 Jr : AS → Ctl → Prop}
    (hJpT : ∀ σ0 c, Jp σ0 c → σ0.regs.fsBase = t)
    (hW : MainPostSWH W K exe endPc R F fr m0 σC Jp Jp' J1 J2 J2' J3 (J4P J4 J4x) (JrT Jr t R))
    (hbp : ∀ σ0 c, Jp σ0 c → σ0.regs.get64 .rbp = (mR R).addr (-8))
    (hra : ∀ σ0 c, Jp σ0 c → (_root_.Executable.labels exe).label ".Lscc_rt_main.x0" = Int64.ofBitVec (σ0.slot 0))
    (hmem : ∀ σ0 c, Jp σ0 c → ∀ i : Int64, (i = 0 ∨ i = 8) →
      ∀ m, mF R F m0 σC m → Mem.loadInt m.dmem (bAddr σ0.regs .rax i) 8 = none)
    (hr0 : ∀ σ0 c, Jp σ0 c → ∃ c', LocalRun p c c' ∧ Jp' σ0 c')
    (h1 : ∀ σ0 c, Jp' σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 0).toNat ∧ c.hold = none ∧
      ∀ (r : Val) (w' : TermRun.Word), (ms [fr]).rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
        J1 σ0 { c with hold := some ((bAddr σ0.regs .rax 0).toNat, w') })
    (h2 : ∀ σ0 c, J1 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
      (wv wold : TermRun.Word),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 0).toNat ∧
      c.hold = some ((bAddr σ0.regs .rax 0).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
      Scc.Sem.ValRep lbl wv.val (rpK1.setWidth 128).toNat ∧ J2 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩)
    (hr2 : ∀ σ0 c, J2 σ0 c → ∃ c', LocalRun p c c' ∧ J2' σ0 c')
    (h3 : ∀ σ0 c, J2' σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 8).toNat ∧ c.hold = none ∧
      ∀ (r : Val) (w' : TermRun.Word), (ms [fr]).rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
        J3 σ0 { c with hold := some ((bAddr σ0.regs .rax 8).toNat, w') })
    (h4 : ∀ σ0 c, J3 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
      (wv wold : TermRun.Word),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 8).toNat ∧
      c.hold = some ((bAddr σ0.regs .rax 8).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
      Scc.Sem.ValRep lbl wv.val (rpK2.setWidth 128).toNat ∧ J4 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩)
    (hfen : ∀ σ0 c, J4 σ0 c → ∃ c', FenceRun p (ms [fr]).pub .st c c' ∧ J5 σ0 c')
    (hpubx : ∀ σ0 c c₁, J4 σ0 c → PubStep .st c c₁ → J4x σ0 c₁)
    (hlocx : ∀ σ0 c, J4x σ0 c → ∃ c', LocalRun p c c' ∧ J5 σ0 c')
    (hedge : ∀ σ0 c, J5 σ0 c → ∀ σ' : AS, σ'.regs.rax.toBitVec = σ0.regs.rax.toBitVec →
      σ'.regs.rdx.toBitVec = 0#64 → σ'.regs.rcx.toBitVec = 2#64 → σ'.regs.rsi.toBitVec = 13#64 →
      σ'.regs.rbp.toBitVec = σ0.slot (-8) → σ'.regs.rsp.toBitVec = σ0.regs.rbp.toBitVec + 8#64 + 8#64 →
      ∃ c', LocalRun p c c' ∧ retJH fr Jr σ' c')
    (hsl : ∀ σ0 c, Jp σ0 c → σ0.slot (-8) = R.addr (-8))
    {Q : MachineData → AS → Frag isa}
    (hWc : ∀ m1 σ1, (wcR R D).OK → FStable (wcR R D) (wcF R D F m1 σ1) →
      SegW (fun s c => W s c []) K p lbl (ms []) (At exe endPc (wcR R D) (wcF R D F m1 σ1)
        ⟨(_root_.Executable.labels exe).label "wc_main", ⟨0, []⟩,
          wcJ0 (mWC (_root_.Executable.labels exe).label σC (JrT Jr t R)).J σ1⟩) (Q m1 σ1)) :
    SegWSP W K p lbl ms
      ((At exe endPc (mR R) (mF R F m0 σC)
        (pN (_root_.Executable.labels exe).label Jp Jp' J1 J2 J2' J3 J4 .s0)).at [fr])
      (Frag.at (fun s c => ∃ m1 σ1, Q m1 σ1 s c) []) := by
  let lab := (_root_.Executable.labels exe).label
  obtain ⟨hR', hF'⟩ := mR_ok hR hF hlo hhi m0 σC
  -- `wc_rodata`'s rest under `tpXa` inside `NoSetFsW`, the thread pointer kept
  have hpost := SegWP.keepTPN (W := fun s c => W s c [fr]) (K := K) (t := t) hK'
    (hello_rodata_post_runW (W := NoSetFsW (fun s c => W s c [fr]) K) (ms := tpXa (ms [fr]) t) hp hend hF' hR'
      (by show (-208 : Int) ≤ -40; decide) (by show (8 : Int) ≤ 8; decide)
      (x := ⟨lab ".Lscc_rt_main.x0", ⟨8, []⟩, retJH fr fun σ c => Jr σ c ∧ σ.regs.get64 .rbp = R.addr (-8)⟩)
      (show SO.le ⟨8, []⟩ ⟨8, []⟩ = true by decide) (rdPostW_noMsr hp hend hW.rd) hbp hra
      hmem hr0 h1 h2 hr2 h3 h4 hfen hpubx hlocx fun σ0 c ⟨c0, hJp⟩ hJ5 σ' h0 h1 h2 h3 hbp' hsp' => by
        obtain ⟨c', hr, a, ty, ws, hc, ha, hJr⟩ := hedge σ0 c hJ5 σ' h0 h1 h2 h3 hbp' hsp'
        refine ⟨c', hr, a, ty, ws, hc, ha, hJr, ?_⟩
        show σ'.regs.rbp.toBitVec = R.addr (-8)
        rw [hbp', hsl σ0 c0 hJp])
  refine SegWSP.seq (Q := (At exe endPc R F (mS0 lab R σC (JrT Jr t R))).at []) (SegWSP.post_run ?_)
    (SegWS.liftS [] (hello_main_sp0_segW hp hend hD hD8 hF hR hlo hloD hhi hW.sp0 hWc) fun _ _ h => h).toP
  refine ((SegWSP.liftS [fr] hpost fun _ _ h => h).mono_pre ?_).mono_post ?_
  · rintro s c fs ⟨h, rfl⟩
    obtain ⟨he, hn, hdc, hpc, σ, hA, hD', hJ⟩ := h
    refine ⟨⟨⟨he, hn, hdc, hpc, σ, hA.weaken (show SO.le ⟨-40, []⟩ Hello1.oR = true by decide), hD', hJ⟩, ?_⟩, rfl⟩
    show s.st.1.regs.fsBase = t
    rw [hA.regs]; exact hJpT σ c hJ
  · rintro s c fs ⟨⟨h, ht⟩, rfl⟩
    obtain ⟨he, hn, hdc, hpc, σ, hA, hD', σx, σC', ⟨a, ty, ws, hc, ha, hJ⟩, rfl, hσ⟩ :=
      at_leave (P := fun σ => σ = σC) rfl (fun m hm => ⟨hm.1, m0, σC, ⟨-80, []⟩, hm.2.1, hm.2.2, rfl⟩) h
    have hreg : σ.regs = σx.regs := by rw [hσ]; rfl
    have htp : σx.regs.fsBase = t := by
      rw [← hreg, ← hA.regs]; exact ht
    have hsp : σx.regs.rsp.toBitVec = R.addr (-72) := by
      have := hA.so .rsp (-80 + 8) rfl
      rw [hreg] at this; exact this
    refine ⟨_, [], .single (FrameStep.ret hc hfr ha), ?_, rfl⟩
    refine Hello1.At.rbp_addr (J := (mS0 lab R _ (JrT Jr t R)).J)
      ⟨he, hn, hdc, hpc, σ, hA, hD', σx, ⟨hJ.1, htp, hsp, hJ.2⟩, hσ⟩ ?_
    rintro σ c ⟨σx, hJ, rfl⟩
    exact hJ.2.2.2

end MainPostT

end Spike.Lib.X64.Flow.HelloM

/-- info: 'Spike.Lib.X64.Flow.HelloM.rdPostW_noMsr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloM.rdPostW_noMsr

/--
info: 'Spike.Lib.X64.Flow.HelloM.hello_main_post_segWST' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloM.hello_main_post_segWST
