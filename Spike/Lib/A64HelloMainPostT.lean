/-
**hello.w's `scc_rt_main` from `wc_rodata`'s `.sp0` with the thread pointer kept** (AArch64; the fix of
`MainGlueS.MainWcPS`'s vacuity, witnessed by the since-deleted
`A64HelloPwVac`).

`hello_rodata_post_runW`'s `hedge` hands the return node's invariant every state agreeing with `.sp0`'s on
`x0`–`x3`, `x29`, `x30` only, so no thread pointer or `sp` can be asked of `wc_rodata`'s return invariant `Jr`
itself. Here they are read off the state instead, as `Hello1.hello1_rodata_setupW` does: `wc_rodata`'s rest runs
inside `NoMsrW` (`rdPostW_noMsr`) under `tpXa`, so `SegW.keepTPN` carries `TP t` from `.sp0` (where `Jp`'s states
have thread pointer `t`, `hJpT`) to the return; leaving `wc_rodata`'s region (`at_leave`) the returned state is
`Jr`'s at thread pointer `t` and `sp = R.addr (-80)` (`JrT`), and `scc_rt_main`'s rest runs from `JrT`.

- `rdPostW_noMsr`: `HelloRd.RdPostW` inside `NoMsrW W K` in any valid layout of `helloProg`.
- `JrT Jr t R`: `Jr` at thread pointer `t` and `scc_rt_main`'s `sp`.
- `hello_main_post_segWST`: `HelloM.hello_main_post_segWS` with `hW.sp0` and `hWc` at `JrT Jr t R`, from `Jp`'s
  thread pointer (`hJpT`) and the memory side's kernel (`hK'`); `hedge` as there.
-/
import Spike.Lib.A64HelloMainPostS
import Spike.Lib.A64Hello1RodataTP

namespace Spike.Lib.A64.Flow.HelloM

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Hello1 (mR mF mR_ok mS0 mWC rpK1 rpK2)
open Spike.Lib.A64.Flow.HelloRd (RdPostW pN hello_rodata_post_runW hello_rpIn rpIn)
open Spike.Lib.A64.KeepTP (TP tpXa)
open Spike.Lib.HelloRdCf (retJH)
open Scc.Cert.Rt.A64 (Lays endOf)

/-- **`wc_rodata` from the allocator's return is inside `NoMsrW W K`** in any valid layout of `helloProg`
(`Hello1.RdPostLW.noMsr`'s twin, with the publish fence). -/
theorem rdPostW_noMsr {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe]
    {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {W : Frag isaLSE2} {K : State → State → Prop} {kp : Nat} (hp : Lays exe SccCode.helloProg kp)
    (hend : endPc = endOf exe SccCode.helloProg kp) {Jp Jp' J1 J2 J2' J3 J4 J5 : AS → Ctl → Prop}
    (h : RdPostW W K exe endPc R F Jp Jp' J1 J2 J2' J3 J4 J5) :
    RdPostW (NoMsrW W K) K exe endPc R F Jp Jp' J1 J2 J2' J3 J4 J5 := by
  have hin := hello_rpIn
  simp only [rpIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨c0, c1⟩, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, cf⟩, c8⟩ := hin
  exact ⟨BlkW.noMsr h.s0 (code_of hp hend c0 (ofNat4_zero _)) (by decide),
    NodeW.noMsr h.l1 (code_of hp hend c1 rfl) (by simp) (by decide),
    BlkW.noMsr h.s1 (code_of hp hend c2 rfl) (by decide),
    NodeW.noMsr h.x1 (code_of hp hend c3 rfl) (by simp) (by decide),
    BlkW.noMsr h.s2 (code_of hp hend c4 rfl) (by decide),
    NodeW.noMsr h.l2 (code_of hp hend c5 rfl) (by simp) (by decide),
    BlkW.noMsr h.s3 (code_of hp hend c6 rfl) (by decide),
    NodeW.noMsr h.x2 (code_of hp hend c7 rfl) (by simp) (by decide),
    NodeW.noMsr h.f (code_of hp hend (WakeWc.pubF_eq ▸ cf) rfl) (by simp) (by decide),
    BlkW.noMsr h.s4 (Spike.Lib.A64.code_field_blockAcross hp hend c8 (List.take_append_drop _ _) rfl) (by decide)⟩

/-- **`wc_rodata`'s return invariant at the thread pointer `t` and `scc_rt_main`'s `sp`** (`R.addr (-80)`, the
call's `sp` in `scc_rt_main`'s region `R`). -/
def JrT (Jr : AS → Ctl → Prop) (t : UInt64) (R : Region) (σ : AS) (c : Ctl) : Prop :=
  Jr σ c ∧ σ.regs.TPIDR_EL0 = t ∧ σ.regs.SP.toBitVec = R.addr (-80)

section MainPostT

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`scc_rt_main` from `wc_rodata`'s `.sp0` into `wc_main` at depth, the thread pointer kept**:
`hello_main_post_segWS` with `wc_rodata`'s rest under `tpXa` inside `NoMsrW` (`SegW.keepTPN`, from `Jp`'s
thread pointer `t`, `hJpT`), so that `scc_rt_main`'s rest (`hW.sp0`, `hWc`) runs from `JrT Jr t R`. -/
theorem hello_main_post_segWST {W : FragS isaLSE2} {K : State → State → Prop} {fr : TermRun.Frame}
    {kp : Nat} (hp : Lays exe SccCode.helloProg kp) (hend : endPc = endOf exe SccCode.helloProg kp)
    (hK' : (ms [fr]).K = some Scc.Sem.A64.abi)
    {D : Int} (hD : 0 ≤ D) (hD16 : D % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -288) (hloD : R.lo ≤ -80 - D)
    (hhi : 0 ≤ R.hi) (hfr : fr.σs = []) {m0 : MachineData} {σC : AS} {t : UInt64}
    {Jp Jp' J1 J2 J2' J3 J4 J5 Jr : AS → Ctl → Prop}
    (hJpT : ∀ σ0 c, Jp σ0 c → σ0.regs.TPIDR_EL0 = t)
    (hW : MainPostSWH W K exe endPc R F fr m0 σC Jp Jp' J1 J2 J2' J3 J4 J5 (JrT Jr t R))
    (hra : ∀ σ0 c, Jp σ0 c → (_root_.Executable.labels exe).label ".L1_scc_rt_main.sp0" = Int64.ofBitVec (σ0.slot (-8)))
    (hmem : ∀ σ0 c, Jp σ0 c → ∀ i : Int64, (i = 0 ∨ i = 8) →
      ∀ m, mF R F m0 σC m → Mem.loadInt m.dmem (rAddr σ0.regs .X0 i) 8 = none)
    (hr0 : ∀ σ0 c, Jp σ0 c → ∃ c', LocalRun p c c' ∧ Jp' σ0 c')
    (h1 : ∀ σ0 c, Jp' σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 0).toNat ∧ c.hold = none ∧
      ∀ (r : Val) (w' : TermRun.Word), (ms [fr]).rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
        J1 σ0 { c with hold := some ((rAddr σ0.regs .X0 0).toNat, w') })
    (h2 : ∀ σ0 c, J1 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
      (wv wold : TermRun.Word),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 0).toNat ∧
      c.hold = some ((rAddr σ0.regs .X0 0).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
      Scc.Sem.ValRep lbl wv.val (rpK1.setWidth 128).toNat ∧ J2 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩)
    (hr2 : ∀ σ0 c, J2 σ0 c → ∃ c', LocalRun p c c' ∧ J2' σ0 c')
    (h3 : ∀ σ0 c, J2' σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 8).toNat ∧ c.hold = none ∧
      ∀ (r : Val) (w' : TermRun.Word), (ms [fr]).rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
        J3 σ0 { c with hold := some ((rAddr σ0.regs .X0 8).toNat, w') })
    (h4 : ∀ σ0 c, J3 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
      (wv wold : TermRun.Word),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 8).toNat ∧
      c.hold = some ((rAddr σ0.regs .X0 8).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
      Scc.Sem.ValRep lbl wv.val (rpK2.setWidth 128).toNat ∧ J4 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩)
    (hfen : ∀ σ0 c, J4 σ0 c → ∃ c', FenceRun p (ms [fr]).pub .st c c' ∧ J5 σ0 c')
    (hedge : ∀ σ0 c, J5 σ0 c → ∀ σ' : AS, σ'.regs.X0.toBitVec = σ0.regs.X0.toBitVec →
      σ'.regs.X1.toBitVec = 0#64 → σ'.regs.X2.toBitVec = 2#64 → σ'.regs.X3.toBitVec = 13#64 →
      σ'.regs.X29.toBitVec = σ0.slot (-16) → σ'.regs.X30.toBitVec = σ0.slot (-8) →
      ∃ c', LocalRun p c c' ∧ retJH fr Jr σ' c')
    {Q : MachineData → AS → Frag isaLSE2}
    (hWc : ∀ m1 σ1, (wcR R D).OK → (wcR R D).base.toNat % 16 = 0 → FStable (wcR R D) (wcF R D F m1 σ1) →
      SegW (fun s c => W s c []) K p lbl (ms []) (At exe endPc (wcR R D) (wcF R D F m1 σ1)
        ⟨(_root_.Executable.labels exe).label "wc_main", ⟨0, []⟩,
          wcJ0 (mWC (_root_.Executable.labels exe).label σC (JrT Jr t R)).J σ1⟩) (Q m1 σ1)) :
    SegWS W K p lbl ms
      ((At exe endPc (mR R) (mF R F m0 σC)
        (pN (_root_.Executable.labels exe).label Jp Jp' J1 J2 J2' J3 J4 J5 .s0)).at [fr])
      (Frag.at (fun s c => ∃ m1 σ1, Q m1 σ1 s c) []) := by
  let lab := (_root_.Executable.labels exe).label
  obtain ⟨hR', hal', hF'⟩ := mR_ok hR hal hF hlo hhi m0 σC
  -- `wc_rodata`'s rest under `tpXa` inside `NoMsrW`, the thread pointer kept
  have hpost := Spike.Lib.A64.Flow.SegW.keepTPN (W := fun s c => W s c [fr]) (K := K) (t := t) hK'
    (hello_rodata_post_runW (W := NoMsrW (fun s c => W s c [fr]) K) (ms := tpXa (ms [fr]) t) hp hend hF' hR'
      hal' (by show (-208 : Int) ≤ -48; decide) (by show (0 : Int) ≤ 0; decide)
      (x := ⟨lab ".L1_scc_rt_main.sp0", ⟨0, []⟩, retJH fr Jr⟩) rfl (rdPostW_noMsr hp hend hW.rd) hra hmem
      hr0 h1 h2 hr2 h3 h4 hfen hedge)
  refine SegWS.seq (Q := (At exe endPc R F (mS0 lab R σC (JrT Jr t R))).at []) (SegWS.post_run ?_)
    (SegWS.liftS [] (hello_main_sp0_segW hp hend hD hD16 hF hR hal hlo hloD hhi hW.sp0 hWc) fun _ _ h => h)
  refine ((SegWS.liftS [fr] hpost fun _ _ h => h).mono_pre ?_).mono_post ?_
  · rintro s c fs ⟨h, rfl⟩
    refine ⟨⟨h, ?_⟩, rfl⟩
    obtain ⟨-, -, -, -, σ, hA, -, hJ⟩ := h
    show s.st.1.regs.TPIDR_EL0 = t
    rw [hA.regs]; exact hJpT σ c hJ
  · rintro s c fs ⟨⟨h, ht⟩, rfl⟩
    obtain ⟨he, hn, hdc, hpc, σ, hA, hD', σx, σC', ⟨a, ty, ws, hc, ha, hJ⟩, rfl, hσ⟩ :=
      at_leave (P := fun σ => σ = σC) rfl (fun m hm => ⟨hm.1, m0, σC, ⟨-80, []⟩, hm.2.1, hm.2.2, rfl⟩) h
    have hreg : σ.regs = σx.regs := by rw [hσ]; rfl
    have htp : σx.regs.TPIDR_EL0 = t := by
      rw [← hreg, ← hA.regs]; exact ht
    have hsp : σx.regs.SP.toBitVec = R.addr (-80) := by
      have := hA.so .SP (-80) rfl
      rw [hreg] at this; exact this
    exact ⟨_, [], .single (FrameStep.ret hc hfr ha), ⟨he, hn, hdc, hpc, σ, hA, hD', σx, ⟨hJ, htp, hsp⟩, hσ⟩,
      rfl⟩

end MainPostT

end Spike.Lib.A64.Flow.HelloM

/-- info: 'Spike.Lib.A64.Flow.HelloM.rdPostW_noMsr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloM.rdPostW_noMsr

/--
info: 'Spike.Lib.A64.Flow.HelloM.hello_main_post_segWST' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloM.hello_main_post_segWST
