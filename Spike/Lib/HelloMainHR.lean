/-
**hello.w on AArch64: main's invariant past the clone at hello's relation**
(the twin of `Spike.Lib.WakeSpawnR`'s `MainWS` and of `spawn_R`'s
`main_closed_ws` step): `HelloSpawnR.HMainRH` from `MainWSH`, the hypotheses
of `A64HelloMainClosedWS.main_closed_wsH` past the clone.

- `MainWSH`: `main_closed_wsH`'s hypotheses but the listing's `hp`/`hend`,
  the clone `h`, the child's id bounds and the memory side's kernel `hK`,
  at main's control `cP`, the clone's configuration `t`, the handed range
  `r1` and the child's id `r` (wake's `MainWS` at hello's frame: 144 bytes
  below the parent's region base, the region `[-144, 48)`, the clone at
  `cloneAtH`, the exit at `mainSp1`, the invariant's state predicate
  `mainWRH` at `helloSrc`).
- `hMainRH_of`: `HMainRH` at any main side whose `Mi` is `mainInvP helloSrc`
  inside `mainWRH` at the record's placement (`hMi`; `HelloMainInv.helloM`'s
  by `rfl` at `lbl w := (SR w).lbl`), given `MainWSH` at every clone
  (`hMR`). The clone is `PreRH.clone` at the record's ranges, the child's
  stack top `stack` its handed range's (`SpawnPreH.top`), the placement the
  record's (`SpawnPreH.SR`) and the id bounds `SpawnPrem`'s.
-/
import Spike.Lib.HelloSpawnR
import Spike.Lib.A64HelloMainClosedWS
import Spike.Lib.HelloMainInv

namespace Spike.Lib.HelloMainHR

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.Handover Spike.Lib.WakeA64 Spike.Lib.Inv2Core Spike.Lib.WakeT1
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Worker.Hello.Child (pfxM)
open Spike.Lib.A64.Flow.Worker.Hello.Parent (JS oP)
open Spike.Lib.A64.Flow.Worker.Hello.MainPost (mainSp1)
open Spike.Lib.HelloPreA (cloneAtH)
open Scc.Cert.Rt.A64 (Lays endOf)
open SccCode (helloProg)
open Spike.Lib.HelloSrc (helloSrc helloS)
open Spike.Lib.HelloMainInv (mainInvP mainWRH)
open Spike.Lib.A64.WideKeep (WideX)
open Spike.Lib.WakeMainSrc (waitC)
open Spike.Lib.WakeM0 (mTail wlIf)
open Spike.Lib.A64.HelloLabels (pfx)
open Spike.Lib.HelloW1 (WSideH)
open Spike.Lib.HelloQ (helloQ)
open Spike.Lib.WakeSpawn (SpawnPrem)
open Spike.Lib.HelloSpawnR (PreRH HMainRH)

/-- **`main_closed_wsH`'s hypotheses past the clone** (all but the listing's
`hp`/`hend`, the clone `h`, the child's id bounds `hr0`/`hrm` and `hK`),
at main's control `cP`, the clone's configuration `t`, the handed range `r1`
and the child's id `r`. -/
structure MainWSH (exe : _root_.Executable) (endPc : Int64) (Λ' : Scc.Sem.Layout)
    (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (ms : MemSide isaLSE2)
    (t : Cfg) (r1 : Range) (r : BitVec 64) (cP : Ctl) (R : Spike.Lib.Region) (F0 : MachineData → Prop)
    (A x29 ra tp : BitVec 64) (w : TermRun.Word) (tyP : Ty) {γ : Type} (Rg : γ → Spike.Lib.Region)
    (Fg : γ → MachineData → Prop) (fp : γ → BitVec 64) (g0 : γ) : Prop where
  hat : ∀ th, t.1.threads = #[th] → At exe endPc R F0 ⟨cloneAtH pfxM exe, oP, JS cP A x29 ra tp⟩ th.st cP
  hRb : ∀ th : Thread isaLSE2, t.1.threads = #[th] → (R.base.toNat : Int) = th.st.st.1.regs.SP.toNat + 144
  hRlo : R.lo = -144
  hRhi : R.hi = 48
  hR : R.OK
  htop : r1.lo + r1.size ≤ 2 ^ 64
  htP : cP.term = mTail
  hlP : TermRun.lookupE cP.env "c" = some (tyP, [w])
  hval : ValRep lbl w.val A.toNat
  hloc : LocRep lbl w.val A.toNat 0
  hin : ∃ sa, w.val = .loc sa 0 ∧ sa.offset < lsize sa.label
  hRg : Rg g0 = R
  hfp : fp g0 = x29
  hFg : ∀ th : Thread isaLSE2, t.1.threads = #[th] → ∀ m,
    DFrame R (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st.st.1 m → Fg g0 m
  hF : ∀ g, FStable (Rg g) (Fg g)
  hRo : ∀ g, (Rg g).OK
  hal : ∀ g, (Rg g).base.toNat % 16 = 0
  hlo : ∀ g, (Rg g).lo ≤ -144
  hhi : ∀ g, 48 ≤ (Rg g).hi
  hdm : ∀ g m, Fg g m → Mem.loadInt m.dmem A 8 = none
  hS : ∀ g, Ret0.StOk ms (Fg g) exe endPc (tp + 16#64) 0#64
  htp4 : (tp + 16#64).toNat % 4 = 0
  htls : ∀ g,
    SegW (mainWRH (_root_.Executable.labels exe).label exe Λ' lbl lsize) (fun _ _ => False) helloSrc lbl ms
      (At exe endPc (Rg g) (Fg g)
        (Spike.Lib.A64.WaitLoop.N (_root_.Executable.labels exe).label pfx (waitC w) "d" wlIf (.ptr .pub .int)
          (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra tp .tls))
      (At exe endPc (Rg g) (Fg g)
        (Spike.Lib.A64.WaitLoop.N (_root_.Executable.labels exe).label pfx (waitC w) "d" wlIf (.ptr .pub .int)
          (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra tp .n1))
  hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainSp1
  hexit : ∀ g s c, Spike.Lib.A64.WaitLoop.Past (waitC w) "d" wlIf (.ptr .pub .int)
    (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) c →
    At exe endPc (Rg g) (Fg g) ⟨(_root_.Executable.labels exe).label mainSp1 + 4 + 4 + 4, ⟨0, []⟩,
      fun σ _ => σ.regs.X0.toBitVec = 0#64⟩ s c → ¬ ms.abortAt s → MainExit helloSrc ms s c 0
  hwide : ∀ s : State, s.exe = exe → s.decls = {} → WideX exe s
  hmA : ∀ wr, Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ') wr ⟨A, 8⟩ = true
  hmP : Spike.Lib.WakeMappedRow.LabMapped lbl (Spike.Lib.A64Consumer.K0 Λ') cP
  hmE : ∀ c, Spike.Lib.A64.WaitLoop.Past (waitC w) "d" wlIf (.ptr .pub .int)
    (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) c →
    Spike.Lib.WakeMappedRow.LabMapped lbl (Spike.Lib.A64Consumer.K0 Λ') c

section Inst

variable {ι : Type} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {SR : ι → SpawnRec}
  {cT : ι → Loc} {cS : ι → WeakMem.Address} {pT : ι → Loc} {Pa : ι → Inv2Params isaLSE2}
  {G : ι → Loc → Val → Prop} {passT : State → Prop} {M : WakeM0.MSide ι} {D : WSideH ι} {r0 r1 : ι → Range}
  {Λ : Scc.Sem.Layout} {asm : String} {E : Entry}

/-- **`HMainRH` from `MainWSH` at every clone** (see the module doc). -/
theorem hMainRH_of {Fr : HelloSpawnR.FrP}
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp) {Λ' : Scc.Sem.Layout}
    {ms : ι → MemSide isaLSE2} (hK : ∀ w, (ms w).K = some Scc.Sem.A64.abi)
    /- main's invariant is `mainInvP helloSrc` inside `mainWRH` at the record's placement -/
    (hMi : ∀ w, M.Mi w = mainInvP helloSrc (SR w).lbl (ms w)
      (mainWRH (_root_.Executable.labels exe).label exe Λ' (SR w).lbl (SR w).lsize))
    /- OPEN: `MainWSH` at main's source control past the clone -/
    (hMR : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l,
      SpawnPrem (helloQ arch R1 ι SR cT cS pT Pa G passT M D r0 r1) Λ asm E 0 d s th stack tls r →
      (helloS arch).Run s [] s' →
      PreRH arch R1 SR cT cS pT Pa G passT M D r0 r1 Λ w d th stack s s' s0 s1 lbl lsize ts j own₀ l →
      Fr lbl lsize th s →
      ∃ (cP : Ctl) (R : Spike.Lib.Region) (F0 : MachineData → Prop) (A x29 ra tp : BitVec 64)
        (cw : TermRun.Word) (tyP : Ty) (γ : Type) (Rg : γ → Spike.Lib.Region) (Fg : γ → MachineData → Prop)
        (fp : γ → BitVec 64) (g0 : γ), Ctl.of s0 = cP ∧
        MainWSH exe endPc Λ' lbl lsize (ms w) d (r1 w) r cP R F0 A x29 ra tp cw tyP Rg Fg fp g0) :
    HMainRH arch R1 SR cT cS pT Pa G passT M D r0 r1 Λ asm E Fr := by
  intro d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l hP hrun hR hFr
  obtain ⟨cP, R, F0, A, x29, ra, tp, cw, tyP, γ, Rg, Fg, fp, g0, hcP, hM⟩ :=
    hMR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP hrun hR hFr
  obtain ⟨X, hcl⟩ := hR.clone
  have h8 : 0 < r.toNat := hP.2.2.2.2.2.2.2.1
  have h9 : r.toNat < pidMax := hP.2.2.2.2.2.2.2.2.1
  obtain ⟨th', hth', hmi⟩ := A64HelloMainClosedWS.main_closed_wsH hp hend hcl hM.hat hM.hRb hM.hRlo hM.hRhi
    hM.hR hM.htop h8 h9 hM.htP hM.hlP hM.hval hM.hloc hM.hin g0 hM.hRg hM.hfp hM.hFg hM.hF hM.hRo hM.hal
    hM.hlo hM.hhi hM.hdm (hK w) hM.hS hM.htp4 hM.htls hM.hra hM.hexit hM.hwide hM.hmA hM.hmP hM.hmE
  have e' : th' = th := by
    rw [hR.pre.threads] at hth'; exact (List.singleton_inj.mp (congrArg Array.toList hth')).symm
  subst th'
  have hSR : SR w = ⟨d.1.mem.last, s'.mem.size, lbl, lsize⟩ := hR.pre.SR
  rw [hR.pre.top] at hmi
  rw [hMi, hSR, hcP]
  exact hmi

/-- **`hMainRH_of` at `HelloMainInv.helloM`** over the records' placement
(`hMi` by `rfl`). -/
theorem hMainRH_helloM {Fr : HelloSpawnR.FrP}
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp) {Λ' : Scc.Sem.Layout}
    {ms : ι → MemSide isaLSE2} (hK : ∀ w, (ms w).K = some Scc.Sem.A64.abi) {cw : ι → TermRun.Word}
    {μT : Marks}
    {hoff : ∀ s c, Spike.Lib.A64WakeOff.AbOffA (_root_.Executable.labels exe).label s c →
      ∀ k a, μT.abortAt k = some a → pcOf s ≠ a}
    (hMR : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l,
      SpawnPrem (helloQ arch R1 ι SR cT cS pT Pa G passT
        (HelloMainInv.helloM (fun w => (SR w).lbl) (fun w => (SR w).lsize) ms cw
          (_root_.Executable.labels exe).label exe Λ' μT hoff) D r0 r1) Λ asm E 0 d s th stack tls r →
      (helloS arch).Run s [] s' →
      PreRH arch R1 SR cT cS pT Pa G passT
        (HelloMainInv.helloM (fun w => (SR w).lbl) (fun w => (SR w).lsize) ms cw
          (_root_.Executable.labels exe).label exe Λ' μT hoff) D r0 r1 Λ w d th stack s s' s0 s1 lbl lsize ts
        j own₀ l →
      Fr lbl lsize th s →
      ∃ (cP : Ctl) (R : Spike.Lib.Region) (F0 : MachineData → Prop) (A x29 ra tp : BitVec 64)
        (fw : TermRun.Word) (tyP : Ty) (γ : Type) (Rg : γ → Spike.Lib.Region) (Fg : γ → MachineData → Prop)
        (fp : γ → BitVec 64) (g0 : γ), Ctl.of s0 = cP ∧
        MainWSH exe endPc Λ' lbl lsize (ms w) d (r1 w) r cP R F0 A x29 ra tp fw tyP Rg Fg fp g0) :
    HMainRH arch R1 SR cT cS pT Pa G passT
      (HelloMainInv.helloM (fun w => (SR w).lbl) (fun w => (SR w).lsize) ms cw
        (_root_.Executable.labels exe).label exe Λ' μT hoff) D r0 r1 Λ asm E Fr :=
  hMainRH_of hp hend hK (fun _ => rfl) hMR

end Inst

end Spike.Lib.HelloMainHR

/-- info: 'Spike.Lib.HelloMainHR.hMainRH_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloMainHR.hMainRH_of

/-- info: 'Spike.Lib.HelloMainHR.hMainRH_helloM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloMainHR.hMainRH_helloM
