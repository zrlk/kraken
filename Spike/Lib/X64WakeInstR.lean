/-
**main's state predicate with its write, label, system call and flag
facts** (x86-64): the x64 twin of `WakeInst.mainWR` and of
`Spike/Lib/A64WakeMainClosedW.lean`'s `seg_mainPostW`/`main_closed_wakeW`
over it.

- `mainWR lab exe Λ lbl lsize`: `X64WakeInst.mainW` with the state's writes
  released (`X64.RelWS`), the source's label words mapped in `K0`
  (`X64WakeMappedRow.LabMapped`), its system calls `futex`/`exit_group`
  (`X64WakeMainS.MainSys`) and the flag load's facts (`X64WakeMainF.FlagW`
  at `q = lab ".Lwc_waitLoop.entry" + 7`). The conjuncts are in
  `WakeInst.mainWR`'s order, so the projections are the same.
- `RtOff lbl lsize ms`: the memory side's runtime words are outside every
  placed label (`MemSide.ofLabels`'s `rt`); `rtOff_msOf`: so for every
  placement's memory side `X64Consumer.msOf` (by definition).
- `ne_of_rt`: a word outside every placed label is not the flag's word
  (the generalisation of `X64WakeMainF.tp8_ne`); `htp_of_ldOk`,
  `htp8_of_limOk`: the park's thread pointer `tp` and the prologue's limit
  word `tp + 8` are not the flag's word, from `LdOk`/`LimOk`'s runtime fact
  under `RtOff` (the x64 `WakeInst.hrt8_of_limOk`).
- `seg_mainPostWR`: `X64WakeMainClosedW.seg_mainPostW` inside `mainWR`;
  each segment's obligations are `mainW`'s, `relW`'s, `ctl`'s, `sys`'s and
  `flag`'s combined with the `.and` lemmas.
- `main_closed_wakeWR`: the whole, at wake's cells, inside `mainWR`.

**Deviations from A64.** The file is separate from the (not yet written)
x64 `WakeInst` remainder (`wakeMs`, `wakeM`, `wakeQI`, `mainInv`), which
will import it; `mainW` stays in `X64WakeMainWDef`. `seg_mainPostWR` keeps
`X64WakeMainClosedW.seg_mainPostW`'s shape (one region `R`, the loop on
`R.fp 8`, no ghost family `Rg`/`Fg`, no `htls` premise: the x64 limit load
is inside `seg_waitLoopW`), with no alignment premise. The flag's listing
fact is discharged here (`wake_flagRuns`), not carried (`hflag`). The
thread pointer facts `tp ≠ A`, `tp + 8 ≠ A` (x64 only: the park reads
`%fs:0`, the prologue `%fs:8`) are discharged from `hT.rt`/`hlim.rt` under
`RtOff` (`hms`), which holds for every `msOf` (`rtOff_msOf`). The final
statement is `mainInv`'s body (no x64 `mainInv` yet).
-/
import Spike.Lib.X64WakeMainF
import Spike.Lib.X64WakeMainClosedW

namespace Spike.Lib.X64WakeInst

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel Spike.Lib.Handover
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.X64.WakePh (wake_parentIn)
open Spike.Lib.X64.WakePh.WcClone (oW)
open Spike.Lib.X64.WakePh.Parent (pN JS)
open Spike.Lib.X64.WakePh.MainPost (mainX2 wake_exitIn pE_rebase)
open Spike.Lib.X64.WaitLoop (RdOne Past wake_waitIn seg_waitLoopW seg_parkCallW)
open Spike.Lib.X64.Flow.Ret0 (LimOk StOk LdOk)
open Spike.Lib.X64WakePreA (ClonePre cloneAt)
open Spike.Lib.X64.WideKeep (WideX)
open Spike.Lib.X64.WakeRunsOff (wake_waitRuns_offA wake_parkRuns_offA wake_parentRuns_offA wake_exitRuns_offA)
open Spike.Lib.X64WakeMainW (loopW_main parkGW_main)
open Spike.Lib.X64WakeMainSegW (seg_parentW parentW_main seg_waitExitW exitW0_main exitW1_main)
open Spike.Lib.X64WakeMainClosedW (main_closed_of_cloneW)
open Spike.Lib.X64WakeMainR (ParentW.and LoopW.and ParkGW.and)

/-- **main's state predicate after the spawn, with its write, label, system
call and flag facts**: `mainW` with the state's writes released (`RelWS`),
the source's label words mapped in `K0` (`LabMapped`), its system calls
`futex`/`exit_group` (`MainSys`) and the flag load's facts (`FlagW`, `q`
the pc after `wc_waitLoop`'s flag load). -/
def mainWR (lab : String → Int64) (exe : _root_.Executable) (Λ : Scc.Sem.Layout)
    (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) : Frag isa :=
  fun s c => mainW lab exe Λ lbl s c ∧ Spike.Lib.X64.RelWS s ∧
    Spike.Lib.X64WakeMappedRow.LabMapped lbl (Spike.Lib.X64Consumer.K0 Λ) c ∧
    Spike.Lib.X64WakeMainS.MainSys s ∧
    -- `.Lwc_waitLoop.entry`, plus `b4`'s 4 bytes and the load's 3
    Spike.Lib.X64WakeMainF.FlagW lbl lsize (lab ".Lwc_waitLoop.entry" + Int64.ofNat 7) s c

/-! ## The thread pointer's words are not the flag's -/

/-- **The memory side's runtime words are outside every placed label**
(`MemSide.ofLabels`'s `rt`). -/
def RtOff (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (ms : MemSide isa) : Prop :=
  ∀ a, ms.rt a → ¬ ∃ l b, lbl l = some b ∧ (Scc.Sem.lrange lsize l b).contains a

/-- **Every placement's memory side has its runtime words outside its
labels** (by definition of `MemSide.ofLabels`). -/
theorem rtOff_msOf {Λ : Scc.Sem.Layout} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
    {own : Spike.Lib.X64Consumer.Own} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {bo : State → Nat → Ctl → (Ctl → Prop) → Prop} :
    RtOff lbl lsize (Spike.Lib.X64Consumer.msOf Λ μ rd G own lbl lsize bo) :=
  fun _ h => h

/-- **A word outside every placed label is not the flag's word** `A`, the
base of the label of `w`, which has a word (`hin`). -/
theorem ne_of_rt {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {a A : BitVec 64} {w : TermRun.Word}
    (hrt : ¬ ∃ l b, lbl l = some b ∧ (Scc.Sem.lrange lsize l b).contains a.toNat)
    (hloc : LocRep lbl w.val A.toNat 0) (hin : ∃ sa, w.val = .loc sa 0 ∧ sa.offset < lsize sa.label) :
    a ≠ A := by
  intro h
  obtain ⟨sa, hw, hsz⟩ := hin
  rw [hw] at hloc
  obtain ⟨-, hb, -⟩ := hloc
  have h1 : @LT.lt Nat _ sa.offset (lsize sa.label) := hsz
  refine hrt ⟨sa.label, A.toNat, hb, ?_⟩
  show A.toNat ≤ a.toNat ∧ a.toNat < A.toNat + 8 * lsize sa.label
  rw [h]; omega

/-- **The park's thread pointer is not the flag's word**: `LdOk`'s runtime
fact under `RtOff`. -/
theorem htp_of_ldOk {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ms : MemSide isa} {F : MachineData → Prop} {tp A : BitVec 64} {w : TermRun.Word}
    (hms : RtOff lbl lsize ms) (hT : LdOk ms F tp)
    (hloc : LocRep lbl w.val A.toNat 0) (hin : ∃ sa, w.val = .loc sa 0 ∧ sa.offset < lsize sa.label) :
    tp ≠ A :=
  ne_of_rt (hms _ hT.rt) hloc hin

/-- **The prologue's limit word is not the flag's word**: `LimOk`'s runtime
fact under `RtOff` (the x64 `WakeInst.hrt8_of_limOk`). -/
theorem htp8_of_limOk {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ms : MemSide isa} {F : MachineData → Prop} {tp Z A : BitVec 64} {w : TermRun.Word}
    (hms : RtOff lbl lsize ms) (hlim : LimOk ms F (tp + (8 : Int64).toBitVec) Z)
    (hloc : LocRep lbl w.val A.toNat 0) (hin : ∃ sa, w.val = .loc sa 0 ∧ sa.offset < lsize sa.label) :
    tp + 8#64 ≠ A :=
  ne_of_rt (hms _ hlim.rt) hloc hin

/-! ## main after its `clone`, inside `mainWR` -/

section Post

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ms : MemSide isa} {Λ : Scc.Sem.Layout}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {c0 : Ctl} {x : String} {a : CoreTerm.At} {e : Expr} {ty : Ty} {w : TermRun.Word} {A fp ra tp : BitVec 64}

/-- **main after its `clone` inside `mainWR`**: `seg_mainPostW`'s segments,
each with `mainW`'s, `RelWS`'s, `LabMapped`'s (`hmA`: the flag's word mapped;
`hmP`, `hmE`: the parent's and the post-load controls' label words), `MainSys`'s
and `FlagW`'s obligations (`hwb`, `hin`: the loop at `wlBody`, its flag word
inside its label; `hcPf`: the parent at neither `wlBody` nor `wlIf`; `hms`:
the runtime words outside the labels, so neither `tp` nor `tp + 8` is the
flag's word). -/
theorem seg_mainPostWR (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
    {R : Region} {F : MachineData → Prop} {cP : Ctl} {cv : String} {tyP tyv : Ty}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -80) (hhi : 40 ≤ R.hi)
    (hrun : LocalRun p cP c0)
    (hlim : LimOk ms F (tp + (8 : Int64).toBitVec) ((R.fp 8).addr 0 - 8#64 - (16 : Int64).toBitVec))
    (hterm : c0.term = .let_ x (.load true a) e) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hval : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    (hK : ms.K = some Scc.Sem.X64.abi) (hT : LdOk ms F tp)
    (hown : OwnAt ms exe endPc ((_root_.Executable.labels exe).label ".Lscc_rt_park.entry") tp tp)
    (hS : StOk ms F (tp + 16#64) 0#64) (htp4 : (tp + 16#64).toNat % 4 = 0)
    {c0' : Ctl} {rbp0' ra' tp' : BitVec 64} (hpcode : Park.Code c0' rbp0' ra' tp' exe endPc)
    (hpentry : (_root_.Executable.labels exe).label ".Lscc_rt_park.entry" =
      (_root_.Executable.labels exe).label "scc_rt_park" + 8)
    (hfp : fp = R.addr 48)
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainX2)
    (hexit : ∀ s c, Past c0 x e ty (RdOne (ms := ms) lbl) c →
      At exe endPc (R.fp 8) F ⟨(_root_.Executable.labels exe).label mainX2 + 4 + 4 + 5, ⟨8, [(.rbp, 40)]⟩,
        fun σ _ => σ.regs.rdi.toBitVec = 0#64⟩ s c → ¬ ms.abortAt s → MainExit p ms s c 0)
    (hwide : ∀ s : State, s.exe = exe → s.decls = {} → WideX exe s)
    (hcP : cP.term ≠ WakeMLive.wlRet) (hfvP : ∀ y ∈ Scc.Sem.exprFv cP.term, y = cv)
    (hlP : TermRun.lookupE cP.env cv = some (tyP, [w]))
    (hc0 : c0.term ≠ WakeMLive.wlRet) (hfv0 : ∀ y ∈ Scc.Sem.exprFv c0.term, y = cv)
    (hl : TermRun.lookupE c0.env cv = some (tyv, [w])) (hloc : LocRep lbl w.val A.toNat 0)
    (hE : e ≠ WakeMLive.wlRet) (hfvE : ∀ y ∈ Scc.Sem.exprFv e, y = x ∨ y = cv) (hxc : x ≠ cv)
    (hmA : ∀ wr, Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) wr ⟨A, 8⟩ = true)
    (hmP : Spike.Lib.X64WakeMappedRow.LabMapped lbl (Spike.Lib.X64Consumer.K0 Λ) cP)
    (hmE : ∀ c, Past c0 x e ty (RdOne (ms := ms) lbl) c →
      Spike.Lib.X64WakeMappedRow.LabMapped lbl (Spike.Lib.X64Consumer.K0 Λ) c)
    (hwb : c0.term = Spike.Lib.X64WakeM0.wlBody) (hin : ∃ sa, w.val = .loc sa 0 ∧ sa.offset < lsize sa.label)
    (hcPf : cP.term ≠ Spike.Lib.X64WakeM0.wlBody ∧ cP.term ≠ Spike.Lib.X64WakeM0.wlIf)
    (hms : RtOff lbl lsize ms) :
    SegLW (mainWR (_root_.Executable.labels exe).label exe Λ lbl lsize) p lbl ms
      (At exe endPc R F (pN (_root_.Executable.labels exe).label cP A fp ra tp .ts))
      (fun _ _ => False) := by
  have h1 : R.lo ≤ 8 := by omega
  have h2 : (8 : Int) < R.hi := by omega
  have hF' := FStable.fp hR h1 h2 hF
  have hR' := Region.fp_ok hR h1 h2
  have hlo' : (R.fp 8).lo ≤ -88 := by show R.lo - 8 ≤ -88; omega
  have hhi' : (8 : Int) ≤ (R.fp 8).hi := by show 8 ≤ R.hi - 8; omega
  have hfp' : fp = (R.fp 8).addr 40 := by rw [Region.fp_addr]; exact hfp
  have h16 : R.Off (-16) := ⟨by decide, by omega, by omega⟩
  have h16' : (R.fp 8).Off (-16) := ⟨by decide, by show R.lo - 8 ≤ -16; omega, by show -16 + 8 ≤ R.hi - 8; omega⟩
  have h24' : (R.fp 8).Off (-24) := ⟨by decide, by show R.lo - 8 ≤ -24; omega, by show -24 + 8 ≤ R.hi - 8; omega⟩
  have hm0 := Spike.Lib.X64WakeMainL.labMapped_c0 hterm hev hval htag hmA
  have h0 := Spike.Lib.X64WakeMainF.flag0_of (lsize := lsize) hwb hterm hev hloc hin
  have hflag := Spike.Lib.X64WakeMainF.wake_flagRuns hp
  have htp := htp_of_ldOk hms hT hloc hin
  have htp8 := htp8_of_limOk hms hlim hloc hin
  -- the parent on `R`, then the loop on `R.fp 8` (`pE_rebase`: `At.rebase` at `d = 8`), then the tail
  refine ((SegLW.ofSegW (seg_parentW hp hend wake_parentIn (c0 := c0) hF hR (by omega) (by omega) hrun
      (ParentW.and (parentW_main (wake_parentRuns_offA hp) hwide h16 hcP hfvP hlP hloc)
        (ParentW.and (Spike.Lib.X64WakeMainR.parentW_relW hp hend wake_parentIn hR (by omega) (by omega))
          (ParentW.and (Spike.Lib.X64WakeMainL.parentW_ctl hmP)
            (ParentW.and (Spike.Lib.X64WakeMainS.parentW_sys hp hend wake_parentIn hR (by omega) (by omega))
              (Spike.Lib.X64WakeMainF.parentW_flag hcPf))))))).seq
    ((seg_waitLoopW hp hend wake_waitIn hF' hR' hlo' hhi' hlim hterm hev hval htag hdm
      (LoopW.and (loopW_main (wake_waitRuns_offA hp) hwide hlo' hhi' hc0 hE hfv0 hfvE hxc hl hloc)
        (LoopW.and (Spike.Lib.X64WakeMainR.loopW_relW hp hend wake_waitIn hR' hlo' hhi')
          (LoopW.and (Spike.Lib.X64WakeMainL.loopW_ctl hm0 hmE)
            (LoopW.and (Spike.Lib.X64WakeMainS.loopW_sys hp hend wake_waitIn hR' hlo' hhi')
              (Spike.Lib.X64WakeMainF.loopW_flag hp hend wake_waitIn hR' hlo' hhi' rfl hflag hwb hterm hev
                hloc hin htp8)))))
      (seg_parkCallW hp wake_waitIn hF' hR' hlo' hhi' hK hT hown hS htp4 hpcode hpentry
        (fun R' F' hR'e hR'' hFF hm g' hg' => ParkGW.and
          (parkGW_main (wake_parkRuns_offA hp) hwide hR' hlo' hhi' hc0 hfv0 hl hloc R' F' hR'e hR'' hFF hm g' hg')
          (ParkGW.and
            (Spike.Lib.X64WakeMainR.parkGW_relW hR'' (by rw [hR'e]; exact Int.le_refl _)
              (by rw [hR'e]; exact Int.le_refl _) hpcode.ghost)
            (ParkGW.and (by obtain rfl := hg'; exact Spike.Lib.X64WakeMainL.parkGW_ctl hm0)
              (ParkGW.and
                (Spike.Lib.X64WakeMainS.parkGW_sys hR'' (by rw [hR'e]; exact Int.le_refl _)
                  (by rw [hR'e]; exact Int.le_refl _) hpcode.ghost)
                (by
                  obtain rfl := hg'
                  exact Spike.Lib.X64WakeMainF.parkGW_flag hR'' (by rw [hR'e]; exact Int.le_refl _)
                    (by rw [hR'e]; exact Int.le_refl _) hpcode.ghost hflag h0 htp))))))).mono_pre
      fun _ _ h => pE_rebase h)).seq
    (SegLW.exists_pre fun y => ?_)
  cases y
  exact SegLW.ofSegW (seg_waitExitW hp hend wake_exitIn hF' hR' (by show R.lo - 8 ≤ 0; omega)
    (by show 32 ≤ R.hi - 8; omega) hK hfp' hra hexit
    ((exitW0_main (wake_exitRuns_offA hp) hra hwide h16' h24' hE hfvE hxc hl hloc).and
      ((Spike.Lib.X64WakeMainR.exitW0_relW hp hend wake_exitIn hR' (by show R.lo - 8 ≤ 0; omega)
          (by show 32 ≤ R.hi - 8; omega) hra).and
        ((Spike.Lib.X64WakeMainL.exitW0_ctl hmE).and
          ((Spike.Lib.X64WakeMainS.exitW0_sys hp hend wake_exitIn hR' (by show R.lo - 8 ≤ 0; omega)
              (by show 32 ≤ R.hi - 8; omega) hra).and
            (Spike.Lib.X64WakeMainF.exitW0_flag hwb hterm)))))
    ((exitW1_main (wake_exitRuns_offA hp) hra hwide h16' h24' hE hfvE hxc hl hloc).and
      ((Spike.Lib.X64WakeMainR.exitW1_relW hp hend wake_exitIn hra).and
        ((Spike.Lib.X64WakeMainL.exitW1_ctl hmE).and
          (Spike.Lib.X64WakeMainS.exitW1_sys.and (Spike.Lib.X64WakeMainF.exitW1_flag hwb hterm))))))

end Post

/-- **main's invariant after its `clone` in wake's cells, inside
`mainWR`**: `main_closed_of_cloneW` with `seg_mainPostWR` on main's region
`R` and a frame condition `F` stable on it containing the parent's memory
outside `R` (`hFR`): an invariant closed under the rows inside `mainWR`
holds at the parent (the body of `WakeInst.mainInv`). -/
theorem main_closed_wakeWR {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {kp : Nat} (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
    {Λ Λ' : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {ms : MemSide isa}
    {t : Spike.Lib.X64WakeA64.Cfg} {s : TermRun.Cfg} (h : ClonePre Λ r0 r1 X lbl t s)
    {R : Region} {F F0 : MachineData → Prop} {cP : Ctl} {A fp ra tp : BitVec 64}
    (hat : ∀ th, t.1.threads = #[th] → At exe endPc R F0 ⟨cloneAt exe, oW, JS cP A fp ra tp⟩ th.st cP)
    (hRb : ∀ th : Thread isa, t.1.threads = #[th] →
      (R.base.toNat : Int) = (th.st.st.1.regs.get64 .rsp).toNat + 64)
    (hRlo : R.lo = -80) (hRhi : R.hi = 40) (hR : R.OK)
    (htop : r1.lo + r1.size ≤ 2 ^ 64) {r : BitVec 64} (hr0 : 0 < r.toNat) (hrm : r.toNat < Scc.Sem.Kernel.pidMax)
    (hFR : ∀ th : Thread isa, t.1.threads = #[th] → ∀ m,
      DFrame R (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st.st.1 m → F m)
    (hF : FStable R F)
    {c0 : Ctl} {x : String} {a : CoreTerm.At} {e : Expr} {ty : Ty} {w : TermRun.Word}
    (hrun : LocalRun Spike.Lib.X64WakeT1.wakeSrc cP c0)
    (hlim : LimOk ms F (tp + (8 : Int64).toBitVec) ((R.fp 8).addr 0 - 8#64 - (16 : Int64).toBitVec))
    (hterm : c0.term = .let_ x (.load true a) e) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hval : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    (hK : ms.K = some Scc.Sem.X64.abi) (hT : LdOk ms F tp)
    (hown : OwnAt ms exe endPc ((_root_.Executable.labels exe).label ".Lscc_rt_park.entry") tp tp)
    (hS : StOk ms F (tp + 16#64) 0#64) (htp4 : (tp + 16#64).toNat % 4 = 0)
    {c0' : Ctl} {rbp0' ra' tp' : BitVec 64} (hpcode : Park.Code c0' rbp0' ra' tp' exe endPc)
    (hpentry : (_root_.Executable.labels exe).label ".Lscc_rt_park.entry" =
      (_root_.Executable.labels exe).label "scc_rt_park" + 8)
    (hfp : fp = R.addr 48)
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainX2)
    (hexit : ∀ s c, Past c0 x e ty (RdOne (ms := ms) lbl) c →
      At exe endPc (R.fp 8) F ⟨(_root_.Executable.labels exe).label mainX2 + 4 + 4 + 5, ⟨8, [(.rbp, 40)]⟩,
        fun σ _ => σ.regs.rdi.toBitVec = 0#64⟩ s c → ¬ ms.abortAt s →
        MainExit Spike.Lib.X64WakeT1.wakeSrc ms s c 0)
    (hwide : ∀ s : State, s.exe = exe → s.decls = {} → WideX exe s)
    {cv : String} {tyP tyv : Ty}
    (hcP : cP.term ≠ WakeMLive.wlRet) (hfvP : ∀ y ∈ Scc.Sem.exprFv cP.term, y = cv)
    (hlP : TermRun.lookupE cP.env cv = some (tyP, [w]))
    (hc0 : c0.term ≠ WakeMLive.wlRet) (hfv0 : ∀ y ∈ Scc.Sem.exprFv c0.term, y = cv)
    (hl : TermRun.lookupE c0.env cv = some (tyv, [w])) (hloc : LocRep lbl w.val A.toNat 0)
    (hE : e ≠ WakeMLive.wlRet) (hfvE : ∀ y ∈ Scc.Sem.exprFv e, y = x ∨ y = cv) (hxc : x ≠ cv)
    (hmA : ∀ wr, Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ') wr ⟨A, 8⟩ = true)
    (hmP : Spike.Lib.X64WakeMappedRow.LabMapped lbl (Spike.Lib.X64Consumer.K0 Λ') cP)
    (hmE : ∀ c, Past c0 x e ty (RdOne (ms := ms) lbl) c →
      Spike.Lib.X64WakeMappedRow.LabMapped lbl (Spike.Lib.X64Consumer.K0 Λ') c)
    (hwb : c0.term = Spike.Lib.X64WakeM0.wlBody) (hin : ∃ sa, w.val = .loc sa 0 ∧ sa.offset < lsize sa.label)
    (hcPf : cP.term ≠ Spike.Lib.X64WakeM0.wlBody ∧ cP.term ≠ Spike.Lib.X64WakeM0.wlIf)
    (hms : RtOff lbl lsize ms) :
    ∃ th : Thread isa, t.1.threads = #[th] ∧ ∃ inv : Frag isa,
      (∀ s c, inv s c → OutL Spike.Lib.X64WakeT1.wakeSrc lbl ms inv s c) ∧
      (∀ s c, inv s c → mainWR (_root_.Executable.labels exe).label exe Λ' lbl lsize s c) ∧
      inv (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st cP :=
  main_closed_of_cloneW hp hend h hat hRb hRlo hRhi hR htop hr0 hrm hFR
    (seg_mainPostWR (Λ := Λ') hp hend hF hR (by omega) (by omega) hrun hlim hterm hev hval htag hdm hK hT hown hS
      htp4 hpcode hpentry hfp hra hexit hwide hcP hfvP hlP hc0 hfv0 hl hloc hE hfvE hxc hmA hmP hmE hwb hin hcPf
      hms)

end Spike.Lib.X64WakeInst

/-- info: 'Spike.Lib.X64WakeInst.rtOff_msOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeInst.rtOff_msOf

/-- info: 'Spike.Lib.X64WakeInst.htp8_of_limOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeInst.htp8_of_limOk

/-- info: 'Spike.Lib.X64WakeInst.seg_mainPostWR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeInst.seg_mainPostWR

/-- info: 'Spike.Lib.X64WakeInst.main_closed_wakeWR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeInst.main_closed_wakeWR
