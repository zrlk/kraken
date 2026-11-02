/-
**hello.w on x86-64: `HMainRH` at a placed output from the segment end** (the twin of
`Spike/Lib/HelloMainHRI.lean`): `hMainRH_ofI`, `X64HelloMainHRD.hMainRH_ofD` at
`L := RuntimeLayout.ofPlaceWX hp i`, both threads' memory side `X64HelloMs.helloMs L (Gm w) (SR w).lbl
(SR w).lsize` at hello's root value invariant `Gm w := wakeG (GOf2H L (m0Of …)) (cT w)`, with its open premise
`hpc` narrowed to the segment end.

Inside, per clone:
- `c`'s label holds a word (`PreRH.hlsz`), its word `⟨cA, 8⟩` shared (`X64WakeMsOf.cTin_of_placed` at the
  memory relation `PreRH.pre.inv1.mem`);
- `MainInstH` by `X64HelloMainInstD.mainInstH_G`: the flag's target word `PreRH.hcT` at `c`'s placed word,
  the memory relation, the TCB, permit and limit words' `hA0`/`hoff` by `X64WakeMainFlag.hA0_of`/`hAoff_of`
  at `X64HelloMainInstD.locIn_tp0_I` and `X64WakeMainInstD.locIn_tp16_I`/`locIn_tp8_I` (the private invariant
  from `hpv`, the frame from `MainSegH.hhat`'s `Abs`).

Open (`hpc`, the segment end): `MainSegH`, `c`'s placement `lbl l = some cA.toNat`, main's TCB
`tp = L.pinA + 0 + 8` (the thread pointer at the clone), and `hZ` (the wait loop's room bound in main's frame
above stack 0's guard); globally the instance's `hprog`, `hw`, `hpv`, `htop`, `hMi` and the park's ownership
`hown`.

## Differences from the AArch64 version

- `hown`: `X64HelloMainHRD.MainInstH` carries the park's `OwnAt` of main's TCB word, which `helloMs` (owning
  no word) does not give; it is an open premise here, stated once per record at the TCB `L.pinA + 0 + 8`.
- `hprog` is `o.prog = SccCode.helloCells` (AArch64: `helloProg`), the end `endOf … helloCells L.pfx`.
- `hms` (`X64HelloMainHRD`'s runtime words off the labels) is closed here (`helloMs`'s `rt`).
- The source facts are not needed (`mainInstH_G` has no `htls`), so `X64HelloMainSrc.src_piecesH` is not
  called; the region is `⟨Rm.base, -128, 40⟩` and `hZ` is at `((R.fp 8).addr 0 - 8 - 16)`.
- Not twinned (unreachable from the AArch64 root, so twins only live constants): none.
-/
import Spike.Lib.X64HelloMainInstD
import Spike.Lib.X64WakeMsOfFields

namespace Spike.Lib.X64HelloMainHRI

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.Handover Spike.Lib.X64WakeA64 Spike.Lib.Inv2Core Spike.Lib.X64WakeT1
open Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.PhRec (m0Of)
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.X64HelloSrc (helloSrc helloS)
open Spike.Lib.X64HelloMainInv (mainInvP mainWRH)
open Spike.Lib.X64HelloW1 (WSideH)
open Spike.Lib.X64HelloQ (helloQ)
open Spike.Lib.X64WakeSpawn (SpawnPrem)
open Spike.Lib.X64HelloSpawnR (PreRH HMainRH)
open Spike.Lib.X64HelloMainHRD (MainSegH)
open Spike.Lib.X64HelloMs (helloMs)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  {ι : Type} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {SR : ι → SpawnRec}
  {cT : ι → Loc} {cS : ι → WeakMem.Address} {pT : ι → Loc} {Pa : ι → Inv2Params isa}
  {G : ι → Loc → Val → Prop} {passT : State → Prop} {M : X64WakeM0.MSide ι} {D : WSideH ι} {r0 r1 : ι → Range}
  {asm : Scc.Sem.X64.Asm} {E : Entry}

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- **hello's root value invariant** at record `w`: wake's `wakeG` at the record's flag word `cT w`. -/
abbrev Gm (cT : ι → Loc) (w : ι) : Loc → Val → Prop :=
  WakeG.wakeG (X64HelloGOf2H.GOf2H (Ly) (m0Of (Ly).Λ o.prog o.secs)) (cT w)

/-- **`HMainRH` at the placed output from the segment end** (see the module doc). -/
theorem hMainRH_ofI {Fr : X64HelloSpawnR.FrP}
    (hprog : o.prog = SccCode.helloCells)
    (hMi : ∀ w, M.Mi w = mainInvP helloSrc (SR w).lbl (helloMs (Ly) (Gm hp i cT w) (SR w).lbl (SR w).lsize)
      (mainWRH (_root_.Executable.labels (Ly).exe).label (Ly).exe (Ly).Λ (SR w).lbl (SR w).lsize))
    (hw : Scc.Cert.WideX64.ExeWide (Ly).exe)
    (hpv : ∀ d s, R1 d s → ∃ (Ent : Entry) (P : State → Prop), Ent.clear (Ly).Λ = true ∧
      Spike.Lib.DmemPriv.PrivInv abi P (Ly).Λ Ent d)
    (htop : ∀ w, (r1 w).lo + (r1 w).size ≤ 2 ^ 64)
    /- OPEN: the park's ownership of main's TCB word -/
    (hown : ∀ w, OwnAt (helloMs (Ly) (Gm hp i cT w) (SR w).lbl (SR w).lsize) (Ly).exe
      (endOf (Ly).exe SccCode.helloCells (Ly).pfx)
      ((_root_.Executable.labels (Ly).exe).label ".Lscc_rt_park.entry") ((Ly).pinA + 0#64 + 8#64)
      ((Ly).pinA + 0#64 + 8#64))
    /- OPEN (per clone): the segment end -/
    (hpc : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l,
      SpawnPrem (helloQ arch R1 ι SR cT cS pT Pa G passT M D r0 r1) (Ly).Λ asm E 0 d s th stack tls r →
      (helloS arch).Run s [] s' →
      PreRH arch R1 SR cT cS pT Pa G passT M D r0 r1 (Ly).Λ w d th stack s s' s0 s1 lbl lsize ts j own₀ l →
      Fr lbl lsize th s →
      ∃ c Rm F₂ cA fp ra tp, MainSegH (Ly).exe (endOf (Ly).exe SccCode.helloCells (Ly).pfx)
          th c Rm F₂ cA fp ra tp ∧
        lbl l = some cA.toNat ∧ tp = (Ly).pinA + 0#64 + 8#64 ∧
        (Ly).stacksA.toNat + 4096 ≤
          (((⟨Rm.base, -128, 40⟩ : Region).fp 8).addr 0 - 8#64 - (16 : Int64).toBitVec).toNat) :
    HMainRH arch R1 SR cT cS pT Pa G passT M D r0 r1 (Ly).Λ asm E Fr := by
  haveI := (Ly).valid
  have hl : Lays (Ly).exe SccCode.helloCells (Ly).pfx := by
    rw [← hprog]; exact (Ly).lays
  have hwf : (Ly).Λ.WF := PlaceWX.wf_link_of_placeWX i hp
  refine X64HelloMainHRD.hMainRH_ofD hl rfl (X64HelloMs.K_H _ (Gm hp i cT) SR)
    (fun _ _ h => h) hMi hw hpv hwf htop ?_
  intro d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l hP hrun hR hFr
  obtain ⟨c, Rm, F₂, cA, fp, ra, tp, hM, hA, htp, hZ⟩ :=
    hpc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP hrun hR hFr
  have hlsz : 0 < lsize l := hR.hlsz
  have hm := hR.pre.inv1.mem
  have hsp : ∀ x, (Ly).Λ.heap.contains x ∨ (Ly).Λ.data.contains x → x < 2 ^ 64 := by
    intro y hy
    rcases hy with hy | hy
    · have := (hwf.inSpace (Ly).Λ.heap (by simp [Layout.regions])).2
      unfold Range.contains at hy; omega
    · have := (hwf.inSpace (Ly).Λ.data (by simp [Layout.regions])).2
      unfold Range.contains at hy; omega
  have hsh : Consumer1.LocIn (Ly).Λ.shared ⟨cA, 8⟩ := by
    have h := X64WakeMsOf.cTin_of_placed hm hsp (a := ⟨l, 0⟩) hA hlsz
    simpa [Scc.Sem.wordLoc] using h
  obtain ⟨Ent, P, hE, hcI⟩ := hpv d s hP.1
  have hth0 : d.1.threads[0]? = some th := by rw [hR.pre.threads]; rfl
  obtain ⟨-, -, -, -, σ, hAbs, -, -⟩ := hM.hhat
  have h0 : Consumer1.LocIn (Ly).Λ.shared ⟨tp, 8⟩ := by
    rw [htp]; exact X64HelloMainInstD.locIn_tp0_I hp i
  have h16 : Consumer1.LocIn (Ly).Λ.shared ⟨tp + 16#64, 8⟩ := by
    rw [htp]; exact X64WakeMainInstD.locIn_tp16_I hp i
  have h8 : Consumer1.LocIn (Ly).Λ.shared ⟨tp + 8#64, 8⟩ := by
    rw [htp]; exact X64WakeMainInstD.locIn_tp8_I hp i
  have hoff := fun {A} (hA : Consumer1.LocIn (Ly).Λ.shared ⟨A, 8⟩) =>
    X64WakeMainFlag.hAoff_of hcI hE hwf hth0 hM.hRok (show (-128 : Int) % 8 = 0 by decide)
      (show (40 : Int) % 8 = 0 by decide) (show (-128 : Int) < 40 by decide) hAbs hA
  have hA0 := fun {A} (hA : Consumer1.LocIn (Ly).Λ.shared ⟨A, 8⟩) =>
    X64WakeMainFlag.hA0_of hcI hE hwf hth0 hA ((r1 w).lo + (r1 w).size) r
  have hT : cT w = Scc.Sem.wordLoc (cA.toNat + 8 * (⟨l, 0⟩ : WeakMem.Address).offset) := by
    rw [hR.hcT, hA]; rfl
  have hSR : SR w = ⟨d.1.mem.last, s'.mem.size, lbl, lsize⟩ := hR.pre.SR
  have hown' := hown w
  rw [← htp] at hown'
  refine ⟨c, Rm, F₂, cA, fp, ra, tp, hM, hA, hlsz, hsh, ?_⟩
  show X64HelloMainHRD.MainInstH _ _ lbl (helloMs (Ly) (Gm hp i cT w) (SR w).lbl (SR w).lsize) _ _ _ _
  rw [hSR] at hown' ⊢
  exact X64HelloMainInstD.mainInstH_G hp i hm (cS := ⟨l, 0⟩) hA hlsz hT htp (Rm := Rm)
    (hA0 h0) (hoff h0) (hA0 h16) (hoff h16) (hA0 h8) (hoff h8) hZ hown'

end Inst

end Spike.Lib.X64HelloMainHRI

/-- info: 'Spike.Lib.X64HelloMainHRI.hMainRH_ofI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloMainHRI.hMainRH_ofI
