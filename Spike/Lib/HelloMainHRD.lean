/-
**hello.w on AArch64: `HMainRH` from the segment end and the instance's
pieces** (the twin of `Spike.Lib.WakeMainHR` / `WakeMainHRD`):
`hMainRH_ofD`, `HelloSpawnR.HMainRH` by `HelloMainHR.hMainRH_of` with
`MainWSH` assembled inside at the one-frame family (`frames_unitH`,
`γ := Unit`) over the region `⟨Rm.base, -144, 48⟩` of the parent's frame.

Inside:
- the frame family's fields by `frames_unitH`, its flag-word premises by
  `WakeMainFlag.hA0_of` / `hAoff_of` at `R1`'s private-memory invariant
  (`hpv`) and `hhat`'s `Abs`, the flag's word shared (`hsh`);
- the source fields (`htP`, `hlP`, `hval`, `hloc`, `hin`) by
  `HelloMainSrc.src_piecesH` at `PreRH.hsp`, `PreRH.pre.ths` and `PreRH.hcS`;
- `hmA` by `WakeLabMapped.mapped_K0_of_shared`, `hmP`/`hmE` by
  `WakeMainInst.hmP_I`/`hmE_I`, `hwide` from `ExeWide`.

Open, per clone (`hpc`): the segment end `MainSegH` (`hhat`, `hRb`, `hRok`,
`hal`, `hra`), `c`'s placement `hA` and size `hlsz`, and the instance's
pieces `MainInstH` (`hS`, `htls`, `hexit`, `htp4` at the frame); globally the
instance's `hw`, `hpv`, `hsh`, `htop`.
-/
import Spike.Lib.HelloMainHR
import Spike.Lib.WakeMainFlag
import Spike.Lib.WakeMainInst

namespace Spike.Lib.HelloMainHRD

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
open Spike.Lib.WakeMainSrc (waitC)
open Spike.Lib.WakeM0 (mTail wlIf)
open Spike.Lib.A64.HelloLabels (pfx)
open Spike.Lib.HelloW1 (WSideH)
open Spike.Lib.HelloQ (helloQ)
open Spike.Lib.WakeSpawn (SpawnPrem)
open Spike.Lib.HelloSpawnR (PreRH HMainRH)
open Spike.Lib.HelloMainHR (MainWSH)

/-- **The one-frame family at hello's parent frame** (`WakeMainFrames.frames_unit`
at the region `⟨b, -144, 48⟩`): with `Rg`, `Fg`, `fp` constant at the
region, `DFrame` of it from `m0` and `x29`, the fields `hRg`, `hfp`, `hFg`,
`hF`, `hRo`, `hal`, `hlo`, `hhi`, `hdm` of `MainWSH`. -/
theorem frames_unitH {b : BitVec 64} {m0 : MachineData} {x29 A : BitVec 64}
    (hR : (⟨b, -144, 48⟩ : Region).OK) (hal : b.toNat % 16 = 0)
    (hA0 : Mem.loadInt m0.dmem A 8 = none) (hA8 : A.toNat + 8 ≤ 2 ^ 64)
    (hAoff : (A.toNat : Int) + 8 ≤ b.toNat + -144 ∨ (b.toNat : Int) + 48 ≤ A.toNat) :
    let Rg : Unit → Region := fun _ => ⟨b, -144, 48⟩
    let Fg : Unit → MachineData → Prop := fun _ => DFrame ⟨b, -144, 48⟩ m0
    let fp : Unit → BitVec 64 := fun _ => x29
    Rg () = ⟨b, -144, 48⟩ ∧ fp () = x29 ∧ (∀ m, DFrame ⟨b, -144, 48⟩ m0 m → Fg () m) ∧
      (∀ g, FStable (Rg g) (Fg g)) ∧ (∀ g, (Rg g).OK) ∧ (∀ g, (Rg g).base.toNat % 16 = 0) ∧
      (∀ g, (Rg g).lo ≤ -144) ∧ (∀ g, 48 ≤ (Rg g).hi) ∧ (∀ g m, Fg g m → Mem.loadInt m.dmem A 8 = none) :=
  ⟨rfl, rfl, fun _ h => h, fun _ => FStable.dframe _ m0, fun _ => hR, fun _ => hal, fun _ => Int.le_refl _,
    fun _ => Int.le_refl _, fun _ _ hm => (hm A hA8 hAoff).trans hA0⟩

/-- **The segment end's fields** at main's thread `th` after the clone
(`MainWSH`'s `hat`, `hRb`, `hR`, the frame's alignment and the return
address), over the region `⟨Rm.base, -144, 48⟩`. -/
structure MainSegH (exe : _root_.Executable) (endPc : Int64) (th : Thread isaLSE2) (c : Ctl) (Rm : Region)
    (F₂ : MachineData → Prop) (cA x29 ra tp : BitVec 64) : Prop where
  hhat : At exe endPc ⟨Rm.base, -144, 48⟩ F₂ ⟨cloneAtH pfxM exe, oP, JS c cA x29 ra tp⟩ th.st c
  hRb : (Rm.base.toNat : Int) = th.st.st.1.regs.SP.toNat + 144
  hRok : (⟨Rm.base, -144, 48⟩ : Region).OK
  hal : Rm.base.toNat % 16 = 0
  hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainSp1

/-- **The instance's fields** at the one frame `⟨Rm.base, -144, 48⟩`, its
frame condition `DFrame` of it from main's memory after the clone `m0`, the
flag's word `w` at `cA`, the frame pointer `x29` (`MainWSH`'s `hS`, `htp4`,
`htls`, `hexit` at `γ := Unit`). -/
structure MainInstH (exe : _root_.Executable) (endPc : Int64) (Λ : Scc.Sem.Layout)
    (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (ms : MemSide isaLSE2)
    (m0 : MachineData) (Rm : Region) (cA x29 ra tp : BitVec 64) (w : TermRun.Word) : Prop where
  hS : Ret0.StOk ms (DFrame ⟨Rm.base, -144, 48⟩ m0) exe endPc (tp + 16#64) 0#64
  htp4 : (tp + 16#64).toNat % 4 = 0
  htls : SegW (mainWRH (_root_.Executable.labels exe).label exe Λ lbl lsize) (fun _ _ => False) helloSrc lbl ms
    (At exe endPc ⟨Rm.base, -144, 48⟩ (DFrame ⟨Rm.base, -144, 48⟩ m0)
      (Spike.Lib.A64.WaitLoop.N (_root_.Executable.labels exe).label pfx (waitC w) "d" wlIf (.ptr .pub .int)
        (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) cA x29 ra tp .tls))
    (At exe endPc ⟨Rm.base, -144, 48⟩ (DFrame ⟨Rm.base, -144, 48⟩ m0)
      (Spike.Lib.A64.WaitLoop.N (_root_.Executable.labels exe).label pfx (waitC w) "d" wlIf (.ptr .pub .int)
        (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) cA x29 ra tp .n1))
  hexit : ∀ s c, Spike.Lib.A64.WaitLoop.Past (waitC w) "d" wlIf (.ptr .pub .int)
    (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) c →
    At exe endPc ⟨Rm.base, -144, 48⟩ (DFrame ⟨Rm.base, -144, 48⟩ m0)
      ⟨(_root_.Executable.labels exe).label mainSp1 + 4 + 4 + 4, ⟨0, []⟩,
        fun σ _ => σ.regs.X0.toBitVec = 0#64⟩ s c → ¬ ms.abortAt s → MainExit helloSrc ms s c 0

section Inst

variable {ι : Type} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {SR : ι → SpawnRec}
  {cT : ι → Loc} {cS : ι → WeakMem.Address} {pT : ι → Loc} {Pa : ι → Inv2Params isaLSE2}
  {G : ι → Loc → Val → Prop} {passT : State → Prop} {M : WakeM0.MSide ι} {D : WSideH ι} {r0 r1 : ι → Range}
  {Λ : Scc.Sem.Layout} {asm : String} {E : Entry}

/-- **`HMainRH` from the segment end and the instance's pieces** (see the
module doc). -/
theorem hMainRH_ofD {Fr : HelloSpawnR.FrP}
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    {ms : ι → MemSide isaLSE2} (hK : ∀ w, (ms w).K = some Scc.Sem.A64.abi)
    (hMi : ∀ w, M.Mi w = mainInvP helloSrc (SR w).lbl (ms w)
      (mainWRH (_root_.Executable.labels exe).label exe Λ (SR w).lbl (SR w).lsize))
    /- the instance -/
    (hw : Scc.Cert.WideA64.ExeWide exe)
    (hpv : ∀ d s, R1 d s → ∃ (Ent : Entry) (P : State → Prop), Ent.clear Λ = true ∧
      Spike.Lib.DmemPriv.PrivInv abi P Λ Ent d)
    (hwf : Λ.WF)
    (htop : ∀ w, (r1 w).lo + (r1 w).size ≤ 2 ^ 64)
    /- OPEN (per clone): the segment end, `c`'s placement and size, the instance's pieces -/
    (hpc : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l,
      SpawnPrem (helloQ arch R1 ι SR cT cS pT Pa G passT M D r0 r1) Λ asm E 0 d s th stack tls r →
      (helloS arch).Run s [] s' →
      PreRH arch R1 SR cT cS pT Pa G passT M D r0 r1 Λ w d th stack s s' s0 s1 lbl lsize ts j own₀ l →
      Fr lbl lsize th s →
      ∃ c Rm F₂ cA x29 ra tp, MainSegH exe endPc th c Rm F₂ cA x29 ra tp ∧ lbl l = some cA.toNat ∧
        0 < lsize l ∧ Spike.Lib.Consumer1.LocIn Λ.shared ⟨cA, 8⟩ ∧
        MainInstH exe endPc Λ lbl lsize (ms w)
          (Kernel.retThread abi (parentPre abi d.2 0 th ((r1 w).lo + (r1 w).size)) r).st.st.1 Rm cA x29 ra tp
          (TermRun.cst (.loc ⟨l, 0⟩ 0))) :
    HMainRH arch R1 SR cT cS pT Pa G passT M D r0 r1 Λ asm E Fr := by
  refine HelloMainHR.hMainRH_of hp hend hK hMi ?_
  intro d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l hP hrun hR hFr
  obtain ⟨c, Rm, F₂, cA, x29, ra, tp, hM, hA, hlsz, hsh, hI⟩ :=
    hpc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP hrun hR hFr
  obtain ⟨th0, ws, hths, hc, hs'⟩ := hR.hsp
  obtain ⟨htP, hlP, -, hval, hloc, hin⟩ :=
    HelloMainSrc.src_piecesH (cS := ⟨l, 0⟩) hs' hths hR.pre.ths hc hA hlsz rfl
  obtain ⟨Ent, P, hE, hcI⟩ := hpv d s hP.1
  have hth := hR.pre.threads
  have hth0 : d.1.threads[0]? = some th := by rw [hth]; rfl
  obtain ⟨-, -, -, -, σ, hAbs, -, -⟩ := hM.hhat
  have hoff := WakeMainFlag.hAoff_of hcI hE hwf hth0 hM.hRok (show (-144 : Int) % 8 = 0 by decide)
    (show (48 : Int) % 8 = 0 by decide) (show (-144 : Int) < 48 by decide) hAbs hsh
  obtain ⟨hRg, hfp, hFg, hF, hRo, hal, hlo, hhi, hdm⟩ := frames_unitH (x29 := x29)
    (m0 := (Kernel.retThread abi (parentPre abi d.2 0 th ((r1 w).lo + (r1 w).size)) r).st.st.1) hM.hRok hM.hal
    (WakeMainFlag.hA0_of hcI hE hwf hth0 hsh _ r) hoff.1 hoff.2
  have one : ∀ th' : Thread isaLSE2, d.1.threads = #[th'] → th' = th := fun th' h' => by
    rw [hth] at h'; exact (List.singleton_inj.mp (congrArg Array.toList h')).symm
  exact ⟨Ctl.of s0, ⟨Rm.base, -144, 48⟩, F₂, cA, x29, ra, tp, _, _, Unit, fun _ => ⟨Rm.base, -144, 48⟩,
    fun _ => DFrame ⟨Rm.base, -144, 48⟩
      (Kernel.retThread abi (parentPre abi d.2 0 th ((r1 w).lo + (r1 w).size)) r).st.st.1,
    fun _ => x29, (), rfl,
    { hat := fun th' h' => by
        obtain rfl := one th' h'
        obtain ⟨h1, h2, h3, h4, σ, hA', hF0, -, hJ⟩ := hM.hhat
        exact ⟨h1, h2, h3, h4, σ, hA', hF0, rfl, hJ⟩
      hRb := fun th' h' => by obtain rfl := one th' h'; exact hM.hRb
      hRlo := rfl
      hRhi := rfl
      hR := hM.hRok
      htop := htop w
      htP := htP
      hlP := hlP
      hval := hval
      hloc := hloc
      hin := hin
      hRg := hRg
      hfp := hfp
      hFg := fun th' h' => by obtain rfl := one th' h'; exact hFg
      hF := hF
      hRo := hRo
      hal := hal
      hlo := hlo
      hhi := hhi
      hdm := hdm
      hS := fun _ => hI.hS
      htp4 := hI.htp4
      htls := fun _ => hI.htls
      hra := hM.hra
      hexit := fun _ => hI.hexit
      hwide := fun _ he hd => ⟨⟨hd ▸ Scc.Cert.WideA64.declsWide_empty, he ▸ hw⟩, he⟩
      hmA := Spike.Lib.WakeLabMapped.mapped_K0_of_shared hsh
      hmP := WakeMainInst.hmP_I htP
      hmE := WakeMainInst.hmE_I }⟩

end Inst

end Spike.Lib.HelloMainHRD

/-- info: 'Spike.Lib.HelloMainHRD.frames_unitH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloMainHRD.frames_unitH

/-- info: 'Spike.Lib.HelloMainHRD.hMainRH_ofD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloMainHRD.hMainRH_ofD
