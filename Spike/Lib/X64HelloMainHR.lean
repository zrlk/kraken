/-
**hello.w on x86-64: main's invariant past the clone at hello's relation** (the twin of
`Spike/Lib/HelloMainHR.lean`): `X64HelloSpawnR.HMainRH` from `MainWSH`, the hypotheses of
`X64HelloMainClosedWS.main_closed_wsH` past the clone.

- `MainWSH`: `main_closed_wsH`'s hypotheses but the listing's `hp`/`hend`, the clone `h`, the child's id bounds,
  the memory side's kernel `hK` and its runtime words `hms`, at main's control `cP`, the clone's configuration
  `t`, the handed range `r1` and the child's id `r` (x86-64 wake's `X64WakeSpawnR.MainWS` at hello's frame: 128
  bytes below the parent's region base, the region `[-128, 40)`, the clone at `cloneAtH`, the exit at
  `mainX3`, the invariant's state predicate `mainWRH` at `helloSrc`).
- `hMainRH_of`: `HMainRH` at any main side whose `Mi` is `mainInvP helloSrc` inside `mainWRH` at the record's
  placement (`hMi`; `X64HelloMainInv.helloM`'s by `rfl` at `lbl w := (SR w).lbl`), given `MainWSH` at every
  clone (`hMR`). The clone is `PreRH.clone` at the record's ranges, the child's stack top `stack` its handed
  range's (`SpawnPreH.top`), the placement the record's (`SpawnPreH.SR`) and the id bounds `SpawnPrem`'s.

## Differences from the AArch64 version

- `MainWSH` follows the x86-64 `main_closed_wsH`: one region `R` with frame condition `F` (no ghost family
  `Rg`/`Fg`/`fp`/`g0`, no `hal`, no `htls`), and x86-64 wake's park facts `hlim`, `hT`, `hown`, `hfp`.
- `hMainRH_of` takes the memory side's runtime words off the record's labels (`hms`, `X64WakeInst.RtOff`) next
  to `hK`; it holds of every `X64Consumer.msOf` (`X64WakeInst.rtOff_msOf`).
- Not twinned (unreachable from the AArch64 root, so twins only live constants): `hMainRH_helloM`.
-/
import Spike.Lib.X64HelloSpawnR
import Spike.Lib.X64HelloMainClosedWS

namespace Spike.Lib.X64HelloMainHR

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.Handover Spike.Lib.X64WakeA64 Spike.Lib.Inv2Core Spike.Lib.X64WakeT1
open Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Worker.Hello.Parent (JS oP)
open Spike.Lib.X64.Flow.Worker.Hello.MainPost (mainX3)
open Spike.Lib.X64HelloPreA (cloneAtH)
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.X64HelloSrc (helloSrc helloS)
open Spike.Lib.X64HelloMainInv (mainInvP mainWRH)
open Spike.Lib.X64.WideKeep (WideX)
open Spike.Lib.X64.WaitLoop (RdOne Past)
open Spike.Lib.X64.Flow.Ret0 (LimOk StOk LdOk)
open Spike.Lib.X64WakeInst (RtOff)
open Spike.Lib.X64WakeMainSrc (waitC)
open Spike.Lib.X64WakeM0 (mTail wlIf)
open Spike.Lib.X64HelloW1 (WSideH)
open Spike.Lib.X64HelloQ (helloQ)
open Spike.Lib.X64WakeSpawn (SpawnPrem)
open Spike.Lib.X64HelloSpawnR (PreRH HMainRH)

/-- **`main_closed_wsH`'s hypotheses past the clone** (all but the listing's
`hp`/`hend`, the clone `h`, the child's id bounds `hr0`/`hrm`, `hK` and
`hms`), at main's control `cP`, the clone's configuration `t`, the handed
range `r1` and the child's id `r`. -/
structure MainWSH (exe : _root_.Executable) (endPc : Int64) (Λ' : Scc.Sem.Layout)
    (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (ms : MemSide isa)
    (t : Cfg) (r1 : Range) (r : BitVec 64) (cP : Ctl) (R : Region) (F0 F : MachineData → Prop)
    (A fp ra tp : BitVec 64) (w : TermRun.Word) (tyP : Ty) : Prop where
  hat : ∀ th, t.1.threads = #[th] → At exe endPc R F0 ⟨cloneAtH exe, oP, JS cP A fp ra tp⟩ th.st cP
  hRb : ∀ th : Thread isa, t.1.threads = #[th] →
    (R.base.toNat : Int) = (th.st.st.1.regs.get64 .rsp).toNat + 128
  hRlo : R.lo = -128
  hRhi : R.hi = 40
  hR : R.OK
  htop : r1.lo + r1.size ≤ 2 ^ 64
  htP : cP.term = mTail
  hlP : TermRun.lookupE cP.env "c" = some (tyP, [w])
  hval : ValRep lbl w.val A.toNat
  hloc : LocRep lbl w.val A.toNat 0
  hin : ∃ sa, w.val = .loc sa 0 ∧ sa.offset < lsize sa.label
  hFR : ∀ th : Thread isa, t.1.threads = #[th] → ∀ m,
    DFrame R (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st.st.1 m → F m
  hF : FStable R F
  hlim : LimOk ms F (tp + (8 : Int64).toBitVec) ((R.fp 8).addr 0 - 8#64 - (16 : Int64).toBitVec)
  hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none
  hT : LdOk ms F tp
  hown : OwnAt ms exe endPc ((_root_.Executable.labels exe).label ".Lscc_rt_park.entry") tp tp
  hS : StOk ms F (tp + 16#64) 0#64
  htp4 : (tp + 16#64).toNat % 4 = 0
  hfp : fp = R.addr 80
  hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainX3
  hexit : ∀ s c, Past (waitC w) "d" wlIf (.ptr .pub .int) (RdOne (ms := ms) lbl) c →
    At exe endPc (R.fp 8) F ⟨(_root_.Executable.labels exe).label mainX3 + 4 + 4 + 5, ⟨8, [(.rbp, 72)]⟩,
      fun σ _ => σ.regs.rdi.toBitVec = 0#64⟩ s c → ¬ ms.abortAt s → MainExit helloSrc ms s c 0
  hwide : ∀ s : State, s.exe = exe → s.decls = {} → WideX exe s
  hmA : ∀ wr, Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ') wr ⟨A, 8⟩ = true
  hmP : Spike.Lib.X64WakeMappedRow.LabMapped lbl (Spike.Lib.X64Consumer.K0 Λ') cP
  hmE : ∀ c, Past (waitC w) "d" wlIf (.ptr .pub .int) (RdOne (ms := ms) lbl) c →
    Spike.Lib.X64WakeMappedRow.LabMapped lbl (Spike.Lib.X64Consumer.K0 Λ') c

section Inst

variable {ι : Type} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {SR : ι → SpawnRec}
  {cT : ι → Loc} {cS : ι → WeakMem.Address} {pT : ι → Loc} {Pa : ι → Inv2Params isa}
  {G : ι → Loc → Val → Prop} {passT : State → Prop} {M : X64WakeM0.MSide ι} {D : WSideH ι} {r0 r1 : ι → Range}
  {Λ : Scc.Sem.Layout} {asm : Scc.Sem.X64.Asm} {E : Entry}

/-- **`HMainRH` from `MainWSH` at every clone** (see the module doc). -/
theorem hMainRH_of {Fr : X64HelloSpawnR.FrP}
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    (hp : Lays exe SccCode.helloCells kp) (hend : endPc = endOf exe SccCode.helloCells kp) {Λ' : Scc.Sem.Layout}
    {ms : ι → MemSide isa} (hK : ∀ w, (ms w).K = some Scc.Sem.X64.abi)
    (hms : ∀ w, RtOff (SR w).lbl (SR w).lsize (ms w))
    /- main's invariant is `mainInvP helloSrc` inside `mainWRH` at the record's placement -/
    (hMi : ∀ w, M.Mi w = mainInvP helloSrc (SR w).lbl (ms w)
      (mainWRH (_root_.Executable.labels exe).label exe Λ' (SR w).lbl (SR w).lsize))
    /- `MainWSH` at main's source control past the clone -/
    (hMR : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l,
      SpawnPrem (helloQ arch R1 ι SR cT cS pT Pa G passT M D r0 r1) Λ asm E 0 d s th stack tls r →
      (helloS arch).Run s [] s' →
      PreRH arch R1 SR cT cS pT Pa G passT M D r0 r1 Λ w d th stack s s' s0 s1 lbl lsize ts j own₀ l →
      Fr lbl lsize th s →
      ∃ (cP : Ctl) (R : Region) (F0 F : MachineData → Prop) (A fp ra tp : BitVec 64)
        (cw : TermRun.Word) (tyP : Ty), Ctl.of s0 = cP ∧
        MainWSH exe endPc Λ' lbl lsize (ms w) d (r1 w) r cP R F0 F A fp ra tp cw tyP) :
    HMainRH arch R1 SR cT cS pT Pa G passT M D r0 r1 Λ asm E Fr := by
  intro d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l hP hrun hR hFr
  obtain ⟨cP, R, F0, F, A, fp, ra, tp, cw, tyP, hcP, hM⟩ :=
    hMR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP hrun hR hFr
  obtain ⟨X, hcl⟩ := hR.clone
  have h8 : 0 < r.toNat := hP.2.2.2.2.2.2.2.1
  have h9 : r.toNat < pidMax := hP.2.2.2.2.2.2.2.2.1
  have hSR : SR w = ⟨d.1.mem.last, s'.mem.size, lbl, lsize⟩ := hR.pre.SR
  have hms' : RtOff lbl lsize (ms w) := by have := hms w; rw [hSR] at this; exact this
  obtain ⟨th', hth', hmi⟩ := X64HelloMainClosedWS.main_closed_wsH hp hend hcl hM.hat hM.hRb hM.hRlo hM.hRhi
    hM.hR hM.htop h8 h9 hM.htP hM.hlP hM.hval hM.hloc hM.hin hM.hFR hM.hF hM.hlim hM.hdm (hK w) hM.hT hM.hown
    hM.hS hM.htp4 hM.hfp hM.hra hM.hexit hM.hwide hM.hmA hM.hmP hM.hmE hms'
  have e' : th' = th := by
    rw [hR.pre.threads] at hth'; exact (List.singleton_inj.mp (congrArg Array.toList hth')).symm
  subst th'
  rw [hR.pre.top] at hmi
  rw [hMi, hSR, hcP]
  exact hmi

end Inst

end Spike.Lib.X64HelloMainHR

/-- info: 'Spike.Lib.X64HelloMainHR.hMainRH_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloMainHR.hMainRH_of
