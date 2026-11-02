/-
**hello.w on x86-64: `HMainRH` from the segment end and the instance's pieces** (the twin of
`Spike/Lib/HelloMainHRD.lean`): `hMainRH_ofD`, `X64HelloSpawnR.HMainRH` by `X64HelloMainHR.hMainRH_of` with
`MainWSH` assembled inside over the region `⟨Rm.base, -128, 40⟩` of the parent's frame and the frame condition
`DFrame` of it from main's memory after the clone.

Inside:
- the flag-word premise `hdm` by `X64WakeMainFlag.hA0_of` / `hAoff_of` at `R1`'s private-memory invariant
  (`hpv`) and `hhat`'s `Abs`, the flag's word shared (`hsh`); `hF` by `FStable.dframe`;
- the source fields (`htP`, `hlP`, `hval`, `hloc`, `hin`) by `X64HelloMainSrc.src_piecesH` at `PreRH.hsp`,
  `PreRH.pre.ths` and `PreRH.hcS`;
- `hmA` by `X64WakeLabMapped.mapped_K0_of_shared`, `hmP`/`hmE` by `X64WakeLabMapped.labMapped_of_noPtr`,
  `hwide` from `ExeWide`.

Open, per clone (`hpc`): the segment end `MainSegH` (`hhat`, `hRb`, `hRok`, `hfp`, `hra`), `c`'s placement
`hA` and size `hlsz`, and the instance's pieces `MainInstH` (`hlim`, `hT`, `hown`, `hS`, `htp4`, `hexit` at the
frame); globally the instance's `hw`, `hpv`, `hwf`, `htop`, `hK`, `hms`.

## Differences from the AArch64 version

- One region and frame condition (no ghost family), as in `X64HelloMainHR.MainWSH`: `frames_unitH` (the
  one-element family's fields) has no counterpart; its `hF` and `hdm` are inline.
- `MainSegH`'s clone `At` is on the widened region `⟨Rm.base, -128, 40⟩` (the instance's
  `X64HelloCloneSegD.CloneSegD` states it there), its base 128 above `%rsp`; no alignment field (the x86-64
  `parent_at_preH` asks none); the frame pointer field `hfp : fp = R.addr 80` (AArch64: the family's `fp`); the
  return point `mainX3`.
- `MainInstH` carries x86-64 wake's park facts `hlim`, `hT`, `hown` (no `htls`); `hmP`/`hmE` come from
  `labMapped_of_noPtr` (as in `X64WakeMainHRI.hMainR_I`) rather than AArch64's `WakeMainInst.hmP_I`/`hmE_I`.
- Not twinned (unreachable from the AArch64 root, so twins only live constants): none.
-/
import Spike.Lib.X64HelloMainHR
import Spike.Lib.X64WakeMainFlag
import Spike.Lib.X64WakeLabMapped

namespace Spike.Lib.X64HelloMainHRD

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
open Spike.Lib.X64.WaitLoop (RdOne Past)
open Spike.Lib.X64.Flow.Ret0 (LimOk StOk LdOk)
open Spike.Lib.X64WakeInst (RtOff)
open Spike.Lib.X64WakeMainSrc (waitC)
open Spike.Lib.X64WakeM0 (mTail wlIf)
open Spike.Lib.X64HelloW1 (WSideH)
open Spike.Lib.X64HelloQ (helloQ)
open Spike.Lib.X64WakeSpawn (SpawnPrem)
open Spike.Lib.X64HelloSpawnR (PreRH HMainRH)
open Spike.Lib.X64HelloMainHR (MainWSH)

/-- **The segment end's fields** at main's thread `th` after the clone
(`MainWSH`'s `hat`, `hRb`, `hR`, the frame pointer and the return address),
over the region `⟨Rm.base, -128, 40⟩`. -/
structure MainSegH (exe : _root_.Executable) (endPc : Int64) (th : Thread isa) (c : Ctl) (Rm : Region)
    (F₂ : MachineData → Prop) (cA fp ra tp : BitVec 64) : Prop where
  hhat : At exe endPc ⟨Rm.base, -128, 40⟩ F₂ ⟨cloneAtH exe, oP, JS c cA fp ra tp⟩ th.st c
  hRb : (Rm.base.toNat : Int) = (th.st.st.1.regs.get64 .rsp).toNat + 128
  hRok : (⟨Rm.base, -128, 40⟩ : Region).OK
  hfp : fp = (⟨Rm.base, -128, 40⟩ : Region).addr 80
  hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainX3

/-- **The instance's fields** at the frame `⟨Rm.base, -128, 40⟩`, its frame
condition `DFrame` of it from main's memory after the clone `m0`, the flag's
word `w` at `cA` (`MainWSH`'s `hlim`, `hT`, `hown`, `hS`, `htp4`, `hexit`). -/
structure MainInstH (exe : _root_.Executable) (endPc : Int64) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : MemSide isa) (m0 : MachineData) (Rm : Region) (tp : BitVec 64) (w : TermRun.Word) : Prop where
  hlim : LimOk ms (DFrame ⟨Rm.base, -128, 40⟩ m0) (tp + (8 : Int64).toBitVec)
    (((⟨Rm.base, -128, 40⟩ : Region).fp 8).addr 0 - 8#64 - (16 : Int64).toBitVec)
  hT : LdOk ms (DFrame ⟨Rm.base, -128, 40⟩ m0) tp
  hown : OwnAt ms exe endPc ((_root_.Executable.labels exe).label ".Lscc_rt_park.entry") tp tp
  hS : StOk ms (DFrame ⟨Rm.base, -128, 40⟩ m0) (tp + 16#64) 0#64
  htp4 : (tp + 16#64).toNat % 4 = 0
  hexit : ∀ s c, Past (waitC w) "d" wlIf (.ptr .pub .int) (RdOne (ms := ms) lbl) c →
    At exe endPc ((⟨Rm.base, -128, 40⟩ : Region).fp 8) (DFrame ⟨Rm.base, -128, 40⟩ m0)
      ⟨(_root_.Executable.labels exe).label mainX3 + 4 + 4 + 5, ⟨8, [(.rbp, 72)]⟩,
        fun σ _ => σ.regs.rdi.toBitVec = 0#64⟩ s c → ¬ ms.abortAt s → MainExit helloSrc ms s c 0

section Inst

variable {ι : Type} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {SR : ι → SpawnRec}
  {cT : ι → Loc} {cS : ι → WeakMem.Address} {pT : ι → Loc} {Pa : ι → Inv2Params isa}
  {G : ι → Loc → Val → Prop} {passT : State → Prop} {M : X64WakeM0.MSide ι} {D : WSideH ι} {r0 r1 : ι → Range}
  {Λ : Scc.Sem.Layout} {asm : Scc.Sem.X64.Asm} {E : Entry}

/-- **`HMainRH` from the segment end and the instance's pieces** (see the
module doc). -/
theorem hMainRH_ofD {Fr : X64HelloSpawnR.FrP}
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    (hp : Lays exe SccCode.helloCells kp) (hend : endPc = endOf exe SccCode.helloCells kp)
    {ms : ι → MemSide isa} (hK : ∀ w, (ms w).K = some Scc.Sem.X64.abi)
    (hms : ∀ w, RtOff (SR w).lbl (SR w).lsize (ms w))
    (hMi : ∀ w, M.Mi w = mainInvP helloSrc (SR w).lbl (ms w)
      (mainWRH (_root_.Executable.labels exe).label exe Λ (SR w).lbl (SR w).lsize))
    /- the instance -/
    (hw : Scc.Cert.WideX64.ExeWide exe)
    (hpv : ∀ d s, R1 d s → ∃ (Ent : Entry) (P : State → Prop), Ent.clear Λ = true ∧
      Spike.Lib.DmemPriv.PrivInv abi P Λ Ent d)
    (hwf : Λ.WF)
    (htop : ∀ w, (r1 w).lo + (r1 w).size ≤ 2 ^ 64)
    /- per clone: the segment end, `c`'s placement and size, the instance's pieces -/
    (hpc : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l,
      SpawnPrem (helloQ arch R1 ι SR cT cS pT Pa G passT M D r0 r1) Λ asm E 0 d s th stack tls r →
      (helloS arch).Run s [] s' →
      PreRH arch R1 SR cT cS pT Pa G passT M D r0 r1 Λ w d th stack s s' s0 s1 lbl lsize ts j own₀ l →
      Fr lbl lsize th s →
      ∃ c Rm F₂ cA fp ra tp, MainSegH exe endPc th c Rm F₂ cA fp ra tp ∧ lbl l = some cA.toNat ∧
        0 < lsize l ∧ Spike.Lib.Consumer1.LocIn Λ.shared ⟨cA, 8⟩ ∧
        MainInstH exe endPc lbl (ms w)
          (Kernel.retThread abi (parentPre abi d.2 0 th ((r1 w).lo + (r1 w).size)) r).st.st.1 Rm tp
          (TermRun.cst (.loc ⟨l, 0⟩ 0))) :
    HMainRH arch R1 SR cT cS pT Pa G passT M D r0 r1 Λ asm E Fr := by
  refine X64HelloMainHR.hMainRH_of hp hend hK hms hMi ?_
  intro d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l hP hrun hR hFr
  obtain ⟨c, Rm, F₂, cA, fp, ra, tp, hM, hA, hlsz, hsh, hI⟩ :=
    hpc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP hrun hR hFr
  obtain ⟨th0, ws, hths, hc, hs'⟩ := hR.hsp
  obtain ⟨htP, hlP, -, hval, hloc, hin⟩ :=
    X64HelloMainSrc.src_piecesH (cS := ⟨l, 0⟩) hs' hths hR.pre.ths hc hA hlsz rfl
  obtain ⟨Ent, P, hE, hcI⟩ := hpv d s hP.1
  have hth := hR.pre.threads
  have hth0 : d.1.threads[0]? = some th := by rw [hth]; rfl
  obtain ⟨-, -, -, -, σ, hAbs, -, -⟩ := hM.hhat
  have hoff := X64WakeMainFlag.hAoff_of hcI hE hwf hth0 hM.hRok (show (-128 : Int) % 8 = 0 by decide)
    (show (40 : Int) % 8 = 0 by decide) (show (-128 : Int) < 40 by decide) hAbs hsh
  have hA0 := X64WakeMainFlag.hA0_of hcI hE hwf hth0 hsh ((r1 w).lo + (r1 w).size) r
  have one : ∀ th' : Thread isa, d.1.threads = #[th'] → th' = th := fun th' h' => by
    rw [hth] at h'; exact (List.singleton_inj.mp (congrArg Array.toList h')).symm
  exact ⟨Ctl.of s0, ⟨Rm.base, -128, 40⟩, F₂,
    DFrame ⟨Rm.base, -128, 40⟩ (Kernel.retThread abi (parentPre abi d.2 0 th ((r1 w).lo + (r1 w).size)) r).st.st.1,
    cA, fp, ra, tp, _, _, rfl,
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
      hFR := fun th' h' m hm => by obtain rfl := one th' h'; exact hm
      hF := FStable.dframe _ _
      hlim := hI.hlim
      hdm := fun m hm => (hm cA hoff.1 hoff.2).trans hA0
      hT := hI.hT
      hown := hI.hown
      hS := hI.hS
      htp4 := hI.htp4
      hfp := hM.hfp
      hra := hM.hra
      hexit := hI.hexit
      hwide := fun _ he hd => ⟨⟨hd ▸ Scc.Cert.WideX64.declsWide_empty, he ▸ hw⟩, he⟩
      hmA := X64WakeLabMapped.mapped_K0_of_shared hsh
      hmP := X64WakeLabMapped.labMapped_of_noPtr (X64WakeLabMapped.noPtr_of_term fun x op e h => by
        rw [htP] at h; cases h)
      hmE := fun c ⟨_, _, hc⟩ => X64WakeLabMapped.labMapped_of_noPtr (X64WakeLabMapped.noPtr_of_term
        fun x op e h => by rw [hc] at h; cases h) }⟩

end Inst

end Spike.Lib.X64HelloMainHRD

/-- info: 'Spike.Lib.X64HelloMainHRD.hMainRH_ofD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloMainHRD.hMainRH_ofD
