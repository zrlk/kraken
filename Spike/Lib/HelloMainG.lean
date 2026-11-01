/-
**hello.w on AArch64: the main side's global instance facts** (B8 row
5j-HMainRH's globals; `HelloMainHRI.hMainRH_ofI`'s `hprog`, `hw`, `hpv`,
`htop`, `hMi`) at a placed output `L := RuntimeLayout.ofPlaceW hp i`.

- `hw_IH`: the placed executable is in the wide fragment, from `PlaceW`'s
  `wideIn` check (`PlaceW.wideIn_of_placeW`, `wideSt_threadAt`), for any
  placed output (wake's statement carries `hwide` as an instance fact).
- `hprog_IH`: `o.prog = helloProg` from the loader's two parses of the
  certificate (as wake's `wake_obligations_RPD`).
- `helloMI`: main's side `HelloMainInv.helloM` at `L`, on hello's memory
  side `helloMs L (Gm w)` at the records' placement, `μ := PhRec.μ L`,
  `hoff := hoff_ofPlaceW`; `hMi_IH`: its `Mi` is `hMainRH_ofI`'s (`rfl`).
- `htop_IH`: the child's ranges `r1` in the stack pool end in the address
  space (`WakeMainInst.htop_I`).
- `hpv_IH`, `pre1T_privH`: `hpv` at `R1 ∧ VPriv L.Λ E` (`WakePrivR`), the
  relation hello's `Pre1T` strengthens to for a placed listing.
- `hMainRH_ofG`: `HMainRH` at `R1 ∧ VPriv`, `helloMI`, open only the
  loader's parses, `hsub1` (the records' `r1` in the stack pool) and the
  segment end `hpc`.
-/
import Spike.Lib.HelloMainHRI
import Spike.Lib.WakePrivR
import Spike.Lib.WakeMainInst

namespace Spike.Lib.HelloMainG

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.Inv2Core Spike.Lib.WakeT1
open Spike.Lib.A64.Rt (RuntimeLayout)
open Scc.Cert.Rt.A64 (endOf)
open SccCode (helloProg)
open Spike.Lib.HelloSrc (helloSrc helloS)
open Spike.Lib.HelloMainInv (mainInvP mainWRH helloM hoff_ofPlaceW)
open Spike.Lib.HelloW1 (WSideH)
open Spike.Lib.WakeSpawn (SpawnPrem)
open Spike.Lib.HelloSpawnR (PreRH HMainRH)
open Spike.Lib.HelloMainHRD (MainSegH)
open Spike.Lib.HelloMs (helloMs)
open Spike.Lib.HelloMainHRI (Gm)
open Spike.Lib.WakePreTi (Pre1T)
open Spike.Lib.WakePrivR (VPriv)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  {ι : Type} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {SR : ι → SpawnRec}
  {cT : ι → Loc} {cS : ι → WeakMem.Address} {pT : ι → Loc} {Pa : ι → Inv2Params isaLSE2}
  {G : ι → Loc → Val → Prop} {passT : State → Prop} {D : WSideH ι} {r0 r1 : ι → Range}
  {asm : String} {E : Entry}

/-- **`hw`: the placed executable is in the wide fragment** (`PlaceW`'s
`wideIn` check at the canonical thread). -/
theorem hw_IH : Scc.Cert.WideA64.ExeWide (RuntimeLayout.ofPlaceW hp i).exe :=
  (Scc.Cert.WideA64.wideSt_threadAt (PlaceW.wideIn_of_placeW hp) Scc.Sem.Entry.linux _ _).2

/-- **`hprog`** from the loader's two parses of the certificate. -/
theorem hprog_IH (hpa : textProgram asm = .ok o.prog) (hhp : textProgram asm = .ok helloProg) :
    o.prog = helloProg :=
  Except.ok.inj (hpa.symm.trans hhp)

/-- **main's side at the placed output**: `helloM` on hello's memory side
`helloMs L (Gm w)` at the records' placement, the layout's marks. -/
noncomputable abbrev helloMI (SR : ι → SpawnRec) (cT : ι → Loc) (cw : ι → TermRun.Word) : WakeM0.MSide ι :=
  helloM (fun w => (SR w).lbl) (fun w => (SR w).lsize)
    (fun w => helloMs (RuntimeLayout.ofPlaceW hp i) (Gm hp i cT w) (SR w).lbl (SR w).lsize) cw
    (RuntimeLayout.ofPlaceW hp i).lab (RuntimeLayout.ofPlaceW hp i).exe (RuntimeLayout.ofPlaceW hp i).Λ
    (Spike.Lib.A64.PhRec.μ (RuntimeLayout.ofPlaceW hp i)) (hoff_ofPlaceW hp i)

/-- **`hMi`** at `helloMI` (`rfl`). -/
theorem hMi_IH (cw : ι → TermRun.Word) : ∀ w, (helloMI hp i SR cT cw).Mi w = mainInvP helloSrc (SR w).lbl
      (helloMs (RuntimeLayout.ofPlaceW hp i) (Gm hp i cT w) (SR w).lbl (SR w).lsize)
      (mainWRH (_root_.Executable.labels (RuntimeLayout.ofPlaceW hp i).exe).label
        (RuntimeLayout.ofPlaceW hp i).exe (RuntimeLayout.ofPlaceW hp i).Λ (SR w).lbl (SR w).lsize) :=
  fun _ => rfl

/-- **`htop`**: the child's ranges in the stack pool end in the address
space. -/
theorem htop_IH (hsub1 : ∀ w, (r1 w).Sub (RuntimeLayout.ofPlaceW hp i).Λ.stackPool) :
    ∀ w, (r1 w).lo + (r1 w).size ≤ 2 ^ 64 :=
  fun w => WakeMainInst.htop_I hp i (hsub1 w)

/-- **`hpv`** at `R1 ∧ VPriv`. -/
theorem hpv_IH : ∀ d s, (R1 d s ∧ VPriv (RuntimeLayout.ofPlaceW hp i).Λ E d) →
    ∃ (Ent : Entry) (P : State → Prop), Ent.clear (RuntimeLayout.ofPlaceW hp i).Λ = true ∧
      Spike.Lib.DmemPriv.PrivInv abi P (RuntimeLayout.ofPlaceW hp i).Λ Ent d :=
  fun _ _ h => WakePrivR.priv_of_R1 h

/-- **hello's `Pre1T` strengthened by `VPriv`** for a placed certificate
(the text is the placed listing, in the wide fragment; `WakePrivR.Pre1T.priv`'s
twin at `helloSrc`). -/
theorem pre1T_privH {Ab Ac : State → Prop} {B : Budget} (hpa : textProgram asm = .ok o.prog)
    (O : Pre1T arch (RuntimeLayout.ofPlaceW hp i).Λ B asm E R1 Ab Ac helloSrc) :
    Pre1T arch (RuntimeLayout.ofPlaceW hp i).Λ B asm E
      (fun d s => R1 d s ∧ VPriv (RuntimeLayout.ofPlaceW hp i).Λ E d) Ab Ac helloSrc :=
  have hw : ∀ prog, (textProgram asm).toOption = some prog → Scc.Cert.WideA64.wideIn prog = true := by
    intro prog h
    rw [hpa] at h
    cases h
    exact PlaceW.wideIn_of_placeW hp
  Spike.Lib.WakePreInv.Pre1T.inv O (fun d _ => VPriv (RuntimeLayout.ofPlaceW hp i).Λ E d)
    (fun _ _ hd _ _ => ⟨WakePrivR.clear_of_load hd, (Spike.Lib.WakeRunInv.runInv_load hw hd).1⟩)
    (fun _ _ _ _ _ _ _ hV _ hs _ _ => ⟨hV.1, Spike.Lib.A64DmemPriv.privInv_step hV.2 hs⟩)

/-- **`HMainRH` at the placed output with the globals discharged** (see the
module doc). Open: the loader's parses, `hsub1`, and the segment end
`hpc` (as `hMainRH_ofI`'s). -/
theorem hMainRH_ofG {Fr : HelloSpawnR.FrP}
    (cw : ι → TermRun.Word) (hpa : textProgram asm = .ok o.prog)
    (hhp : textProgram asm = .ok helloProg)
    (hsub1 : ∀ w, (r1 w).Sub (RuntimeLayout.ofPlaceW hp i).Λ.stackPool)
    (hpc : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l,
      SpawnPrem (Spike.Lib.HelloQ.helloQ arch (fun d s => R1 d s ∧ VPriv (RuntimeLayout.ofPlaceW hp i).Λ E d) ι SR
        cT cS pT Pa G passT (helloMI hp i SR cT cw) D r0 r1) (RuntimeLayout.ofPlaceW hp i).Λ asm E 0
        d s th stack tls r →
      (helloS arch).Run s [] s' →
      PreRH arch (fun d s => R1 d s ∧ VPriv (RuntimeLayout.ofPlaceW hp i).Λ E d) SR cT cS pT Pa G passT
        (helloMI hp i SR cT cw) D r0 r1 (RuntimeLayout.ofPlaceW hp i).Λ w d th stack s s' s0 s1
        lbl lsize ts j own₀ l →
      Fr lbl lsize th s →
      ∃ c Rm F₂ cA x29 ra tp, MainSegH (RuntimeLayout.ofPlaceW hp i).exe
          (endOf (RuntimeLayout.ofPlaceW hp i).exe helloProg (RuntimeLayout.ofPlaceW hp i).pfx)
          th c Rm F₂ cA x29 ra tp ∧
        lbl l = some cA.toNat ∧ tp = (RuntimeLayout.ofPlaceW hp i).pinA + 0#64 + 8#64 ∧
        (RuntimeLayout.ofPlaceW hp i).stacksA.toNat + 4096 ≤ ((⟨Rm.base, -144, 48⟩ : Region).addr (-32)).toNat) :
    HMainRH arch (fun d s => R1 d s ∧ VPriv (RuntimeLayout.ofPlaceW hp i).Λ E d) SR cT cS pT Pa G passT
      (helloMI hp i SR cT cw) D r0 r1 (RuntimeLayout.ofPlaceW hp i).Λ asm E Fr :=
  HelloMainHRI.hMainRH_ofI hp i (hprog_IH hpa hhp) (hMi_IH hp i cw) (hw_IH hp i) (hpv_IH hp i)
    (htop_IH hp i hsub1) hpc

end Inst

end Spike.Lib.HelloMainG

/-- info: 'Spike.Lib.HelloMainG.hMainRH_ofG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloMainG.hMainRH_ofG
