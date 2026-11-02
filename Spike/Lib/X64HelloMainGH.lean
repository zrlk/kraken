/-
**hello.w on x86-64: the segment end at `X64HelloAssemblyI`'s main side** (the twin of
`Spike/Lib/HelloMainGH.lean`; `hello_obligations_I`'s `hMainR`): `X64HelloMainHRD.hMainRH_ofD`'s conclusion at
the instance's `MH` (`helloM` at the target's marks `μH`, `X64HelloCompatI.hoffP`) on main's owning side
`X64HelloMs.msHX L (GH G0)` (`msH` owning main's TCB self word `tcbM`). `MH`'s `Mi` is `hMainRH_ofD`'s at
`ms := msHX` by definition; per clone, `MainInstH` at `msHX` is `mainInstH_GX`, once the records' value invariant
below `wakeG` is hello's root one, `G0 w = GOf2H L (m0Of L.Λ o.prog o.secs)` (`hG0`), with the flag word
`cT w := w.1.cT`.

- `mainInstH_GX`: `X64HelloMainHRD.MainInstH` at `msXW (helloMs …) (tcbM L) (tcbM L) (tcbWH L)`: the fields of
  `X64HelloMainInstD.mainInstH_G` at `helloMs` lifted to the owning side (`X64HelloOwnLift.limOk_msXW`,
  `ldOk_msXW`, `stOk_msXW_park`), and the park's ownership `hown` by `X64WakeOwnX.ownAt_msXW`.
- `hMainRH_ofGH`: `HMainRH` at `R1 ∧ VPriv L.Λ E`, `SRH`, `MH`; open only `hsub1` (the records' `r1` in the
  stack pool) and the segment end `hpc`, given the loader's parses and `hG0`.

## Differences from the AArch64 version

- main's side owns its TCB self word (`msHX`), so the park's `OwnAt` of that word is closed here
  (`ownAt_msXW`); AArch64's park reads the thread pointer from `tpidr_el0`, a register, and owns no word.
- The loader's parses are `cellsOf asm = some …` (AArch64: `textProgram asm = .ok …`); the end is
  `endOf … helloCells L.pfx`; the region `⟨Rm.base, -128, 40⟩` and `hZ` at `((R.fp 8).addr 0 - 8 - 16)`.
- Not twinned (unreachable from the AArch64 root, so twins only live constants): none.
-/
import Spike.Lib.X64HelloMainG
import Spike.Lib.X64HelloMainHRI
import Spike.Lib.X64HelloAssemblyI

namespace Spike.Lib.X64HelloMainGH

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.Inv2Core Spike.Lib.X64WakeT1
open Spike.Lib.X64
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.PhRec (m0Of)
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.X64HelloSrc (helloS)
open Spike.Lib.X64HelloW1 (WSideH)
open Spike.Lib.X64WakeSpawn (SpawnPrem)
open Spike.Lib.X64HelloSpawnR (PreRH HMainRH)
open Spike.Lib.X64HelloMainHRD (MainSegH MainInstH)
open Spike.Lib.X64WakePrivR (VPriv)
open Spike.Lib.X64HelloMs (helloMs)
open Spike.Lib.X64HelloOwnLift (tcbWH)
open Spike.Lib.X64WakeOwnX (msXW)
open Spike.Lib.X64HelloAssemblyI (ιH SRH MH)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- **`MainInstH` at main's owning side** `msXW (helloMs …) (tcbM L) (tcbM L) (tcbWH L)` (see the module doc):
`X64HelloMainInstD.mainInstH_G`'s premises but its `hown`, which the owning side gives. -/
theorem mainInstH_GX {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {exe : _root_.Executable} {endPc : Int64}
    {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tq0 tq sp : List Nat}
    (hm : MemRelP (Ly).Λ lbl lsize ts tm sm tq0 tq sp)
    {cT : Loc} {cS : WeakMem.Address} {b : Nat} (hl : lbl cS.label = some b)
    (ho : cS.offset < lsize cS.label) (hT : cT = Scc.Sem.wordLoc (b + 8 * cS.offset))
    {tp : BitVec 64} (htp : tp = (Ly).pinA + 0#64 + 8#64)
    {Rm : Region} {m0 : MachineData}
    (hA0 : Mem.loadInt m0.dmem tp 8 = none)
    (hoff0 : tp.toNat + 8 ≤ 2 ^ 64 ∧
      ((tp.toNat : Int) + 8 ≤ Rm.base.toNat + -128 ∨ (Rm.base.toNat : Int) + 40 ≤ tp.toNat))
    (hA16 : Mem.loadInt m0.dmem (tp + 16#64) 8 = none)
    (hoff16 : (tp + 16#64).toNat + 8 ≤ 2 ^ 64 ∧
      (((tp + 16#64).toNat : Int) + 8 ≤ Rm.base.toNat + -128 ∨ (Rm.base.toNat : Int) + 40 ≤ (tp + 16#64).toNat))
    (hA8 : Mem.loadInt m0.dmem (tp + 8#64) 8 = none)
    (hoff8 : (tp + 8#64).toNat + 8 ≤ 2 ^ 64 ∧
      (((tp + 8#64).toNat : Int) + 8 ≤ Rm.base.toNat + -128 ∨ (Rm.base.toNat : Int) + 40 ≤ (tp + 8#64).toNat))
    (hZ : (Ly).stacksA.toNat + 4096 ≤
      (((⟨Rm.base, -128, 40⟩ : Region).fp 8).addr 0 - 8#64 - (16 : Int64).toBitVec).toNat)
    {w : TermRun.Word} :
    MainInstH exe endPc lbl
      (msXW (helloMs (Ly) (WakeG.wakeG (X64HelloGOf2H.GOf2H (Ly) (m0Of (Ly).Λ o.prog o.secs)) cT) lbl lsize)
        (WakePh.tcbM (Ly)) (WakePh.tcbM (Ly)) (tcbWH (Ly)))
      m0 Rm tp w := by
  have htpM : tp = WakePh.tcbM (Ly) := htp.trans (by rw [BitVec.add_zero])
  have hpin := X64HelloOwnLift.pin_room120_ofPlaceWX hp i
  refine ⟨?_, ?_, ?_, ?_, X64HelloMainInstD.htp4_IH hp i htp, fun s c h hX =>
    X64HelloMainInstD.hexit_IH (G := WakeG.wakeG (X64HelloGOf2H.GOf2H (Ly) (m0Of (Ly).Λ o.prog o.secs)) cT)
      (lsize := lsize) s c h hX⟩
  · rw [show (8 : Int64).toBitVec = 8#64 by decide]
    exact X64HelloOwnLift.limOk_msXW (X64HelloMainInstD.limOk_IH hp i hm htp (R := ⟨Rm.base, -128, 40⟩) hA8 hoff8
      (X64HelloMainInstD.hroom_limH hp i htp (X64HelloMainInstD.cT_ne_IH hp i hl ho hT hm) hZ))
  · have hu := X64WakeMainInstD.unmapped_I (R := ⟨Rm.base, -128, 40⟩) hA0 hoff0
    subst htp
    exact X64HelloOwnLift.ldOk_msXW ⟨X64HelloMainInstD.tp_free hp i hm,
      ⟨X64WakeLabMapped.mapped_K0_of_shared (X64HelloMainInstD.locIn_tp0_I hp i) false, nofun⟩, hu⟩
  · rw [htpM]; exact X64WakeOwnX.ownAt_msXW
  · have h := X64HelloMainInstD.hS_IH hp i hm htp (R := ⟨Rm.base, -128, 40⟩) hA16 hoff16
      (X64HelloMainInstD.hG_permitH hp i (m0' := m0Of (Ly).Λ o.prog o.secs) (cT := cT) htp _)
    rw [htpM] at h ⊢
    exact X64HelloOwnLift.stOk_msXW_park h (X64HelloOwnLift.tcbM_roomH _ hpin)
      (X64HelloOwnLift.offTcb_park_tcbWH _ hpin)

variable {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {cS : ιH hp i → WeakMem.Address}
  {pT : ιH hp i → Loc} {Pa : ιH hp i → Inv2Params isa} {G : ιH hp i → Loc → Val → Prop}
  {passT : State → Prop} {D : WSideH (ιH hp i)} {r0 r1 : ιH hp i → Range} {asm : Scc.Sem.X64.Asm} {E : Entry}
  {G0 : ιH hp i → Loc → Val → Prop}

/-- **`HMainRH` at `X64HelloAssemblyI`'s `MH`** (see the module doc): the form `hello_obligations_I`'s
`hMainR` takes, at `R1 ∧ VPriv`. -/
theorem hMainRH_ofGH {Fr : X64HelloSpawnR.FrP}
    (hpa : cellsOf asm = some o.prog) (hhp : cellsOf asm = some SccCode.helloCells)
    /- the records' value invariant below `wakeG` is hello's root one -/
    (hG0 : ∀ w, G0 w = X64HelloGOf2H.GOf2H (Ly) (m0Of (Ly).Λ o.prog o.secs))
    /- the records' `r1` in the stack pool -/
    (hsub1 : ∀ w, (r1 w).Sub (Ly).Λ.stackPool)
    /- the segment end, per clone -/
    (hpc : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l,
      SpawnPrem (Spike.Lib.X64HelloQ.helloQ arch (fun d s => R1 d s ∧ VPriv (Ly).Λ E d)
        (ιH hp i) (SRH hp i) (fun w => w.1.cT) cS pT Pa G passT (MH hp i G0 E hpa) D r0 r1)
        (Ly).Λ asm E 0 d s th stack tls r →
      (helloS arch).Run s [] s' →
      PreRH arch (fun d s => R1 d s ∧ VPriv (Ly).Λ E d) (SRH hp i) (fun w => w.1.cT) cS pT Pa G passT
        (MH hp i G0 E hpa) D r0 r1 (Ly).Λ w d th stack s s' s0 s1 lbl lsize ts j own₀ l →
      Fr lbl lsize th s →
      ∃ c Rm F₂ cA fp ra tp, MainSegH (Ly).exe (endOf (Ly).exe SccCode.helloCells (Ly).pfx)
          th c Rm F₂ cA fp ra tp ∧
        lbl l = some cA.toNat ∧ tp = (Ly).pinA + 0#64 + 8#64 ∧
        (Ly).stacksA.toNat + 4096 ≤
          (((⟨Rm.base, -128, 40⟩ : Region).fp 8).addr 0 - 8#64 - (16 : Int64).toBitVec).toNat) :
    HMainRH arch (fun d s => R1 d s ∧ VPriv (Ly).Λ E d) (SRH hp i) (fun w => w.1.cT) cS pT Pa G passT
      (MH hp i G0 E hpa) D r0 r1 (Ly).Λ asm E Fr := by
  haveI := (Ly).valid
  have hl : Lays (Ly).exe SccCode.helloCells (Ly).pfx := by
    rw [← X64HelloMainG.hprog_IH hpa hhp]; exact (Ly).lays
  have hwf : (Ly).Λ.WF := PlaceWX.wf_link_of_placeWX i hp
  refine X64HelloMainHRD.hMainRH_ofD hl rfl (fun _ => rfl) (fun _ _ h => h) (fun _ => rfl)
    (X64HelloMainG.hw_IH hp i) (X64HelloMainG.hpv_IH hp i) hwf (X64HelloMainG.htop_IH hp i hsub1) ?_
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
  obtain ⟨Ent, P, hE, hcI⟩ := X64HelloMainG.hpv_IH hp i d s hP.1
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
  have hT : w.1.cT = Scc.Sem.wordLoc (cA.toNat + 8 * (⟨l, 0⟩ : WeakMem.Address).offset) := by
    rw [hR.hcT, hA]; rfl
  have hSR : SRH hp i w = ⟨d.1.mem.last, s'.mem.size, lbl, lsize⟩ := hR.pre.SR
  refine ⟨c, Rm, F₂, cA, fp, ra, tp, hM, hA, hlsz, hsh, ?_⟩
  show MainInstH _ _ lbl (msXW (helloMs (Ly) (WakeG.wakeG (G0 w) w.1.cT) (SRH hp i w).lbl (SRH hp i w).lsize)
    (WakePh.tcbM (Ly)) (WakePh.tcbM (Ly)) (tcbWH (Ly))) _ _ _ _
  rw [hSR, hG0 w]
  exact mainInstH_GX hp i hm (cS := ⟨l, 0⟩) hA hlsz hT htp (Rm := Rm)
    (hA0 h0) (hoff h0) (hA0 h16) (hoff h16) (hA0 h8) (hoff h8) hZ

end Inst

end Spike.Lib.X64HelloMainGH

/-- info: 'Spike.Lib.X64HelloMainGH.mainInstH_GX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloMainGH.mainInstH_GX

/-- info: 'Spike.Lib.X64HelloMainGH.hMainRH_ofGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloMainGH.hMainRH_ofGH
