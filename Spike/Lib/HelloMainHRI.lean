/-
**hello.w on AArch64: `HMainRH` at a placed output from the segment end
alone** (the twin of `Spike.Lib.WakeMainHRD.hMainR_ofD` at hello's records):
`hMainRH_ofI`, `HelloMainHRD.hMainRH_ofD` at `L := RuntimeLayout.ofPlaceW hp
i`, both threads' memory side `HelloMs.helloMs L (Gm w) (SR w).lbl (SR w).lsize`
at hello's root value invariant `Gm w := wakeG (GOf2H L (m0Of …)) (cT w)`,
with its open premise `hpc` narrowed to the segment end.

Inside, per clone:
- `c`'s label holds a word (`PreRH.hlsz`), its word `⟨cA, 8⟩` shared
  (`WakeMsOf.cTin_of_placed` at the memory relation `PreRH.pre.inv1.mem`);
- `MainInstH` by `HelloMainInstD.mainInstH_G`: the flag's target word
  `PreRH.hcT` at `c`'s placed word, the memory relation, the permit and limit
  words' `hA0`/`hoff` by `WakeMainFlag.hA0_of`/`hAoff_of` at
  `WakeMainInstD.locIn_tp16_I`/`locIn_tp8_I` (the private invariant from
  `hpv`, the frame from `MainSegH.hhat`'s `Abs`), the source facts by
  `HelloMainSrc.src_piecesH` at `PreRH.hsp`.

Open (`hpc`, the segment end): `MainSegH`, `c`'s placement `lbl l = some
cA.toNat`, main's TCB `tp = L.pinA + 0 + 8` (the thread pointer at the
clone), and `hZ` (`x9`'s address in main's frame above stack 0's guard);
globally the instance's `hprog`, `hw`, `hpv`, `htop` and `hMi`.
-/
import Spike.Lib.HelloMainInstD
import Spike.Lib.HelloGOf2H

namespace Spike.Lib.HelloMainHRI

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.Handover Spike.Lib.WakeA64 Spike.Lib.Inv2Core Spike.Lib.WakeT1
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.PhRec (m0Of)
open Scc.Cert.Rt.A64 (Lays endOf)
open SccCode (helloProg)
open Spike.Lib.HelloSrc (helloSrc helloS)
open Spike.Lib.HelloMainInv (mainInvP mainWRH)
open Spike.Lib.HelloW1 (WSideH)
open Spike.Lib.HelloQ (helloQ)
open Spike.Lib.WakeSpawn (SpawnPrem)
open Spike.Lib.HelloSpawnR (PreRH HMainRH)
open Spike.Lib.HelloMainHRD (MainSegH)
open Spike.Lib.HelloMs (helloMs)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  {ι : Type} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {SR : ι → SpawnRec}
  {cT : ι → Loc} {cS : ι → WeakMem.Address} {pT : ι → Loc} {Pa : ι → Inv2Params isaLSE2}
  {G : ι → Loc → Val → Prop} {passT : State → Prop} {M : WakeM0.MSide ι} {D : WSideH ι} {r0 r1 : ι → Range}
  {asm : String} {E : Entry}

/-- **hello's root value invariant** at record `w`: wake's `wakeG'` at the
record's flag word `cT w`. -/
abbrev Gm (cT : ι → Loc) (w : ι) : Loc → Val → Prop :=
  WakeG.wakeG (HelloGOf2H.GOf2H (RuntimeLayout.ofPlaceW hp i)
    (m0Of (RuntimeLayout.ofPlaceW hp i).Λ o.prog o.secs)) (cT w)

/-- **`HMainRH` at the placed output from the segment end** (see the module
doc). -/
theorem hMainRH_ofI {Fr : HelloSpawnR.FrP}
    (hprog : o.prog = helloProg)
    (hMi : ∀ w, M.Mi w = mainInvP helloSrc (SR w).lbl
      (helloMs (RuntimeLayout.ofPlaceW hp i) (Gm hp i cT w) (SR w).lbl (SR w).lsize)
      (mainWRH (_root_.Executable.labels (RuntimeLayout.ofPlaceW hp i).exe).label
        (RuntimeLayout.ofPlaceW hp i).exe (RuntimeLayout.ofPlaceW hp i).Λ (SR w).lbl (SR w).lsize))
    (hw : Scc.Cert.WideA64.ExeWide (RuntimeLayout.ofPlaceW hp i).exe)
    (hpv : ∀ d s, R1 d s → ∃ (Ent : Entry) (P : State → Prop), Ent.clear (RuntimeLayout.ofPlaceW hp i).Λ = true ∧
      Spike.Lib.DmemPriv.PrivInv abi P (RuntimeLayout.ofPlaceW hp i).Λ Ent d)
    (htop : ∀ w, (r1 w).lo + (r1 w).size ≤ 2 ^ 64)
    /- OPEN (per clone): the segment end -/
    (hpc : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l,
      SpawnPrem (helloQ arch R1 ι SR cT cS pT Pa G passT M D r0 r1) (RuntimeLayout.ofPlaceW hp i).Λ asm E 0
        d s th stack tls r →
      (helloS arch).Run s [] s' →
      PreRH arch R1 SR cT cS pT Pa G passT M D r0 r1 (RuntimeLayout.ofPlaceW hp i).Λ w d th stack s s' s0 s1
        lbl lsize ts j own₀ l →
      Fr lbl lsize th s →
      ∃ c Rm F₂ cA x29 ra tp, MainSegH (RuntimeLayout.ofPlaceW hp i).exe
          (endOf (RuntimeLayout.ofPlaceW hp i).exe helloProg (RuntimeLayout.ofPlaceW hp i).pfx)
          th c Rm F₂ cA x29 ra tp ∧
        lbl l = some cA.toNat ∧ tp = (RuntimeLayout.ofPlaceW hp i).pinA + 0#64 + 8#64 ∧
        (RuntimeLayout.ofPlaceW hp i).stacksA.toNat + 4096 ≤ ((⟨Rm.base, -144, 48⟩ : Region).addr (-32)).toNat) :
    HMainRH arch R1 SR cT cS pT Pa G passT M D r0 r1 (RuntimeLayout.ofPlaceW hp i).Λ asm E Fr := by
  have hl : Lays (RuntimeLayout.ofPlaceW hp i).exe helloProg (RuntimeLayout.ofPlaceW hp i).pfx := by
    rw [← hprog]; exact (RuntimeLayout.ofPlaceW hp i).lays
  have hwf : (RuntimeLayout.ofPlaceW hp i).Λ.WF := PlaceW.wf_link_of_placeW i hp
  refine HelloMainHRD.hMainRH_ofD hl rfl (HelloMs.K_H _ (Gm hp i cT) SR) hMi hw hpv hwf htop ?_
  intro d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l hP hrun hR hFr
  obtain ⟨c, Rm, F₂, cA, x29, ra, tp, hM, hA, htp, hZ⟩ :=
    hpc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP hrun hR hFr
  have hlsz : 0 < lsize l := hR.hlsz
  have hm := hR.pre.inv1.mem
  have hsp : ∀ x, (RuntimeLayout.ofPlaceW hp i).Λ.heap.contains x ∨
      (RuntimeLayout.ofPlaceW hp i).Λ.data.contains x → x < 2 ^ 64 := by
    intro y hy
    rcases hy with hy | hy
    · have := (hwf.inSpace (RuntimeLayout.ofPlaceW hp i).Λ.heap (by simp [Layout.regions])).2
      unfold Range.contains at hy; omega
    · have := (hwf.inSpace (RuntimeLayout.ofPlaceW hp i).Λ.data (by simp [Layout.regions])).2
      unfold Range.contains at hy; omega
  have hsh : Consumer1.LocIn (RuntimeLayout.ofPlaceW hp i).Λ.shared ⟨cA, 8⟩ := by
    have h := WakeMsOf.cTin_of_placed hm hsp (a := ⟨l, 0⟩) hA hlsz
    simpa [Scc.Sem.wordLoc] using h
  obtain ⟨th0, ws, hths, hc, hs'⟩ := hR.hsp
  obtain ⟨-, -, -, hval, hloc, hin⟩ :=
    HelloMainSrc.src_piecesH (cS := ⟨l, 0⟩) hs' hths hR.pre.ths hc hA hlsz rfl
  obtain ⟨Ent, P, hE, hcI⟩ := hpv d s hP.1
  have hth0 : d.1.threads[0]? = some th := by rw [hR.pre.threads]; rfl
  obtain ⟨-, -, -, -, σ, hAbs, -, -⟩ := hM.hhat
  have h16 : Consumer1.LocIn (RuntimeLayout.ofPlaceW hp i).Λ.shared ⟨tp + 16#64, 8⟩ := by
    rw [htp]; exact WakeMainInstD.locIn_tp16_I hp i
  have h8 : Consumer1.LocIn (RuntimeLayout.ofPlaceW hp i).Λ.shared ⟨tp + 8#64, 8⟩ := by
    rw [htp]; exact WakeMainInstD.locIn_tp8_I hp i
  have hoff := fun {A} (hA : Consumer1.LocIn (RuntimeLayout.ofPlaceW hp i).Λ.shared ⟨A, 8⟩) =>
    WakeMainFlag.hAoff_of hcI hE hwf hth0 hM.hRok (show (-144 : Int) % 8 = 0 by decide)
      (show (48 : Int) % 8 = 0 by decide) (show (-144 : Int) < 48 by decide) hAbs hA
  have hT : cT w = Scc.Sem.wordLoc (cA.toNat + 8 * (⟨l, 0⟩ : WeakMem.Address).offset) := by
    rw [hR.hcT, hA]; rfl
  have hSR : SR w = ⟨d.1.mem.last, s'.mem.size, lbl, lsize⟩ := hR.pre.SR
  refine ⟨c, Rm, F₂, cA, x29, ra, tp, hM, hA, hlsz, hsh, ?_⟩
  show HelloMainHRD.MainInstH _ _ _ lbl lsize
    (helloMs (RuntimeLayout.ofPlaceW hp i) (Gm hp i cT w) (SR w).lbl (SR w).lsize) _ _ _ _ _ _ _
  rw [hSR]
  exact HelloMainInstD.mainInstH_G hp i hprog hw rfl hm (cS := ⟨l, 0⟩) hA hlsz hT htp (Rm := Rm)
    (x29 := x29) (ra := ra)
    (WakeMainFlag.hA0_of hcI hE hwf hth0 h16 ((r1 w).lo + (r1 w).size) r) (hoff h16)
    (WakeMainFlag.hA0_of hcI hE hwf hth0 h8 ((r1 w).lo + (r1 w).size) r) (hoff h8) hZ hsh hval hloc hin

end Inst

end Spike.Lib.HelloMainHRI

/-- info: 'Spike.Lib.HelloMainHRI.hMainRH_ofI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloMainHRI.hMainRH_ofI
