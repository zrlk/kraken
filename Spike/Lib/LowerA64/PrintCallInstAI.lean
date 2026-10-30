/-
**An output call, assembled, at an immediate table other than the layout's**
(AArch64; the twin of `Spike/Lib/LowerX64/PrintCallInstAI.lean`):
`printCallC_instA`, `printCallCH_instA` (`Spike/Lib/LowerA64/PrintCallInstA.lean`)
tie the segments' table to `Λ.imms`, the world's. A compiled block's code
facts (`fnCode2OfP`) carry the lowering's table `i` (`imms2Of p`) while the
world sits at a table with more entries (`imms2Me Λ p`, the first TCB at
the setup start). The variants here take any `i` below `Λ.imms` (`hiL`)
and agreeing with it at each output call's continuation (`hie`): the node
at the call moves to `Λ.imms` (`letAt_mono_i`), the caller's slots at `print`
are the same placement (`hie`). The return-address premises `hraP`, `hraAb`
come from the calls at `BlC2` (`hBl2`) and a caller other than the runtime's
(`hfi`).

- `immIn_mono_i`, `slotRepAt_mono_i`, `letAt_mono_i`: the walk's facts, a
  control's placement and the node at a `let` at a larger table;
- `printCallC_instAI`, `printCallCH_instAI`: at `PrintCallC`, `PrintCallCH`
  at the table `i`.
-/
import Spike.Lib.LowerA64.PrintCallInstA

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (NodeW BlkW ND At okBlk FStable AI AS Abs SO)
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.A64.Flow.Ret0 (StackOff)
open Spike.Lib.LowerNode (FrOk2 ZBad printFrame LblRange printTop0 SlotRepAt)
open Spike.Lib.LowerShape (printInsts)
open Spike.Lib.A64.Flow.PrintCall (pN pR pF pcS pFJ)
open Spike.Lib.PrintSrc (printLD)
open Spike.Lib.A64.StubW (printPhOk)
open Spike.Lib.A64.PrintG (printPhOkF)
open Spike.Lib.ByteOut (ByteOut)

variable {i i' : Expr → String → Nat → Option Nat}

/-- **The walk's immediates at a larger table.** -/
theorem immIn_mono_i (hiL : ∀ t x k v, i t x k = some v → i' t x k = some v) {s : Spike.Lib.Form.SEnv} {t : Expr}
    (h : Spike.Lib.LowerNode.ImmIn i s t) : Spike.Lib.LowerNode.ImmIn i' s t :=
  fun x k v hv => hiL _ _ _ _ (h x k v hv)

/-- **A control placed in the slots at a larger table.** -/
theorem slotRepAt_mono_i (hiL : ∀ t x k v, i t x k = some v → i' t x k = some v)
    {lbl : WeakMem.AllocLabel → Option Nat} {rs : Scc.IR.Reg → Option Int} {sl : Int → BitVec 64} {c : Ctl}
    (h : SlotRepAt i lbl rs sl c) : SlotRepAt i' lbl rs sl c :=
  let ⟨s, hs, ht, hb, hi⟩ := h
  ⟨s, hs, ht, hb, immIn_mono_i hiL hi⟩

/-- **The node at a `let` at a larger table** (`bodyN2`'s placement). -/
theorem letAt_mono_i (hiL : ∀ t x k v, i t x k = some v → i' t x k = some v) {p : Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat} {cx : FnCtx}
    {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {fp ra : BitVec 64}
    {tp : UInt64} {c0 : Ctl} {fs : List TermRun.Frame} {pc : Int64} {t : Expr} {env : Scc.Lower.Env}
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)} {s : State} {c : Ctl}
    {fs' : List TermRun.Frame}
    (h : LetAt p lbl lsize i cx exe endPc R F fp ra tp c0 fs pc t env lits cs bufs s c fs') :
    LetAt p lbl lsize i' cx exe endPc R F fp ra tp c0 fs pc t env lits cs bufs s c fs' := by
  obtain ⟨⟨he, hn, hd, hpc, σ, hA, hF, ⟨hJ1, hJ2, hJ3, hJ4⟩, htp⟩, hfs⟩ := h
  exact ⟨⟨he, hn, hd, hpc, σ, hA, hF, ⟨hJ1, hJ2, hJ3, slotRepAt_mono_i hiL hJ4⟩, htp⟩, hfs⟩

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {R : Region} {F : MachineData → Prop}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : InvS}
  {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}

/-- **An output call at `PrintCallC` at the table `i`** (`printCallC_ofA`
at `i`): `printCallC_instA`'s pieces at `Λ.imms`, the node at the call by
`letAt_mono_i` (`hiL`), the caller's slots at `print` by `hie`, the return
addresses' phase and position from the calls at `BlC2` (`printRa_ph`,
`printRa_notAb`, the caller not the runtime's: `hfi`). -/
theorem printCallC_instAI {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habI : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hph : printPhOkF okPc ph lab = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int) - 48) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) (hFS : FStable R F)
    {ra0 : Int64}
    {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL prog okPc ph lab ra0 pc blk)
    (hBl : ∀ pc g k, Bl pc g k → BlC prog okPc ph lab cx ra0 pc g k ∧ PosOff prog lab pc)
    (hfi : cx.fi ≠ 9 ∧ cx.fi ≠ 12 ∧ cx.fi ≠ 16)
    (hBl2 : ∀ pc k, Bl pc Scc.Lower.Names.print k → BlC2 prog okPc ph lab cx ra0 pc Scc.Lower.Names.print k)
    {lcx : Scc.Lower.Ctx} (hpd : p.find? (·.name == "print") = some Scc.Frontend.printExtD)
    (hd : p.find? (·.name == "printL") = some printLD) (hprog : lcx.prog = p)
    {ownA : OwnS} {IA : InvS}
    (hrg : LblRange Λ lbl lsize) (hb32 : ∀ r ∈ Λ.rodata :: Λ.regions, r.lo + r.size ≤ 2 ^ 32)
    (hfs : ∀ fr ∈ fs, NoS ZBad fr.body) (hFP : ∀ s : State, F s.st.1 → ∃ A, FramesPlacedInI Λ lbl s fs A)
    {G0 : Ctl → Prop} (hG0F : ∀ c0, G0 c0 → FrOk2 c0 fs) {T : Expr → Prop}
    (hTp : ∀ x g is a ts e xe, T (.let_ x (.call g is a ts) e) → lcx.externs.find? (·.1 == g) = some xe →
      g = "print" ∧ ts = [])
    (fp ra : BitVec 64) (tp : UInt64)
    (hNoS : ∀ x is a e, T (.let_ x (.call "print" is a []) e) → NoS ZBad e)
    (hDtP : ∀ (R' : Region) (F' : MachineData → Prop) (Pc Qc : AS → Nat → Ctl → Prop) (σC : AS) s c',
      At exe endPc R' F' (pN (_root_.Executable.labels exe).label Pc Qc σC .svc) s c' → Dt s)
    {Ax : FragS isaLSE2} (hAb : ∀ c0 x is a e c1 s c, G0 c0 → T (.let_ x (.call "print" is a []) e) →
      At exe endPc R F (printNAS (_root_.Executable.labels exe).label cx lbl i x e c1) s c →
      Ax s c (printFrame x e c1 :: fs))
    (hiL : ∀ t x k v, i t x k = some v → Λ.imms t x k = some v)
    (hie : ∀ x is a e, T (.let_ x (.call "print" is a []) e) → Λ.imms e = i e) :
    PrintCallC p lbl lsize lcx cx Cd Bl exe endPc R F
      (fun s c fs' => W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.A64.WriteAb.Ab lab) lbl lsize s c fs') K
      (msOfAB Λ μ p rd G ownA ar IA (Spike.Lib.A64.WriteAb.Ab lab) lbl lsize) fp ra tp fs G0 i T Ax := by
  have hraP : ∀ pc k, Bl pc Scc.Lower.Names.print k →
      ph (pc + 4).toBitVec.toNat = ph (lab ".L9_scc_rt_print.7_done").toBitVec.toNat :=
    fun _ _ hb => printRa_ph hI.lays hI.labOk hpr hph (hBl2 _ _ hb)
  have hraAb : ∀ pc k, Bl pc Scc.Lower.Names.print k → pc + 4 ∉ Spike.Lib.A64.WriteAb.abPcs lab :=
    fun _ _ hb => printRa_notAb hI.lays hI.labOk hpr habI hfi (hBl2 _ _ hb)
  have hWL := printWL_w2 hI hpr habI hf h1 h16 hR hal (by omega) hhi hl hh hsub hfit hFO hp hCd hBl
    (fun _ _ hk => by obtain ⟨h1k, h2k, h3k, -⟩ := rsOf_cell hf hk; exact ⟨h1k, by omega, by omega⟩) hFP
    (W := fun s c fs' => W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.A64.WriteAb.Ab lab) lbl lsize s c fs')
    (rd := rd) (G := G) (ar := ar) (Jv := J) (Dt := Dt) (lsize := lsize)
    (fun _ _ h => h) hG0F (T := T) fp ra tp
  have hPW := printW_hPWA (ownA := ownA) (IA := IA) (G0 := G0) (rd := rd) (G := G) (ar := ar) (J := J) hI hpr
    habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hFS hCd hBl hraP hraAb hrg hb32 hfs hFP fp ra tp hNoS hDtP
  have hPWE := printWE_hPWEA (G0 := G0) (rd := rd) (G := G) (ar := ar) (J := J) (Dt := Dt) (lsize := lsize) (p := p)
    hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hFS hCd hBl hraP hraAb hfs hFP fp ra tp hNoS
  refine printCallC_ofA hf h1 h16 hFS hR hal hlo hhi (fun _ _ h => cdOf_of_cdC hI (hCd _ _ h).toCdC)
    (fun _ _ _ h => cdOf_of_blC hI (hBl _ _ _ h).1) hI.lays hI.endOk hpr hpd hd hprog (fun _ => rfl)
    (fun _ s _ _ _ _ _ hr h hΦ => ByteOut.closed (I := isaLSE2) (s := s) hr h hΦ) hTp
    (fun c0 pc env lits cs bufs n x is a e b o m cw kk pc' s c hG0 hT hi hL =>
      hWL c0 pc env lits cs bufs n x is a e b o m cw kk pc' s c hG0 hT hi (letAt_mono_i hiL hL))
    ?_ ?_ hAb
  · intro c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn nv mv kk pc' hG0 hT hi hpw hSA hLen hS
    have he := hie x is a e hT
    refine hPW c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn nv mv kk pc' hG0 hT hi hpw ?_ hLen ?_
    · unfold PrintSlotsA at hSA ⊢; rw [he]; exact hSA
    · unfold PrintSlots at hS ⊢; rw [he]; exact hS
  · intro c0 pc env lits cs bufs n x is a e b o m cw c1 envR kk pc' hG0 hT hi hSA hLen hS
    have he := hie x is a e hT
    refine hPWE c0 pc env lits cs bufs n x is a e b o m cw c1 envR kk pc' hG0 hT hi ?_ hLen ?_
    · unfold PrintSlotsA at hSA ⊢; rw [he]; exact hSA
    · unfold PrintSlots at hS ⊢; rw [he]; exact hS

/-- **An output call at `PrintCallCH` at the table `i`** (`printCallCH_ofA`
at `i`): `printCallCH_instA`'s pieces at `Λ.imms`, the node at the call by
`letAt_mono_i` (`hiL`), the caller's slots at `print` by `hie`, the return
addresses' phase and position from the calls at `BlC2` (`printRa_ph`,
`printRa_notAb`, the caller not the runtime's: `hfi`). -/
theorem printCallCH_instAI {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habI : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hph : printPhOkF okPc ph lab = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int) - 48) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) (hFS : FStable R F)
    {ra0 : Int64}
    {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL prog okPc ph lab ra0 pc blk)
    (hBl : ∀ pc g k, Bl pc g k → BlC prog okPc ph lab cx ra0 pc g k ∧ PosOff prog lab pc)
    (hfi : cx.fi ≠ 9 ∧ cx.fi ≠ 12 ∧ cx.fi ≠ 16)
    (hBl2 : ∀ pc k, Bl pc Scc.Lower.Names.print k → BlC2 prog okPc ph lab cx ra0 pc Scc.Lower.Names.print k)
    {lcx : Scc.Lower.Ctx} (hpd : p.find? (·.name == "print") = some Scc.Frontend.printExtD)
    (hd : p.find? (·.name == "printL") = some printLD) (hprog : lcx.prog = p)
    {ownA : OwnS} {IA : InvS}
    (hrg : LblRange Λ lbl lsize) (hb32 : ∀ r ∈ Λ.rodata :: Λ.regions, r.lo + r.size ≤ 2 ^ 32)
    (hfs : ∀ fr ∈ fs, NoS ZBad fr.body) (hFP : ∀ s : State, F s.st.1 → ∃ A, FramesPlacedInI Λ lbl s fs A)
    {G0 : Ctl → Prop} (hG0F : ∀ c0, G0 c0 → FrOk2 c0 fs) {T : Expr → Prop}
    (hTp : ∀ x g is a ts e xe, T (.let_ x (.call g is a ts) e) → lcx.externs.find? (·.1 == g) = some xe →
      g = "print" ∧ ts = [])
    (fp ra : BitVec 64) (tp : UInt64)
    (hNoS : ∀ x is a e, T (.let_ x (.call "print" is a []) e) → NoS ZBad e)
    (hDtP : ∀ (R' : Region) (F' : MachineData → Prop) (Pc Qc : AS → Nat → Ctl → Prop) (σC : AS) s c',
      At exe endPc R' F' (pN (_root_.Executable.labels exe).label Pc Qc σC .svc) s c' → Dt s)
    {Ax : FragS isaLSE2} (hAb : ∀ c0 x is a e c1 s c, G0 c0 → T (.let_ x (.call "print" is a []) e) →
      At exe endPc R F (printNAS (_root_.Executable.labels exe).label cx lbl i x e c1) s c →
      Ax s c (printFrame x e c1 :: fs))
    (hiL : ∀ t x k v, i t x k = some v → Λ.imms t x k = some v)
    (hie : ∀ x is a e, T (.let_ x (.call "print" is a []) e) → Λ.imms e = i e) :
    PrintCallCH p lbl lsize lcx cx Cd Bl exe endPc R F
      (fun s c fs' => W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.A64.WriteAb.Ab lab) lbl lsize s c fs') K
      (msOfAB Λ μ p rd G ownA ar IA (Spike.Lib.A64.WriteAb.Ab lab) lbl lsize) fp ra tp fs G0 i T Ax := by
  have hraP : ∀ pc k, Bl pc Scc.Lower.Names.print k →
      ph (pc + 4).toBitVec.toNat = ph (lab ".L9_scc_rt_print.7_done").toBitVec.toNat :=
    fun _ _ hb => printRa_ph hI.lays hI.labOk hpr hph (hBl2 _ _ hb)
  have hraAb : ∀ pc k, Bl pc Scc.Lower.Names.print k → pc + 4 ∉ Spike.Lib.A64.WriteAb.abPcs lab :=
    fun _ _ hb => printRa_notAb hI.lays hI.labOk hpr habI hfi (hBl2 _ _ hb)
  have hWL := printWL_w2 hI hpr habI hf h1 h16 hR hal (by omega) hhi hl hh hsub hfit hFO hp hCd hBl
    (fun _ _ hk => by obtain ⟨h1k, h2k, h3k, -⟩ := rsOf_cell hf hk; exact ⟨h1k, by omega, by omega⟩) hFP
    (W := fun s c fs' => W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.A64.WriteAb.Ab lab) lbl lsize s c fs')
    (rd := rd) (G := G) (ar := ar) (Jv := J) (Dt := Dt) (lsize := lsize)
    (fun _ _ h => h) hG0F (T := T) fp ra tp
  have hPW := printW_hPWA (ownA := ownA) (IA := IA) (G0 := G0) (rd := rd) (G := G) (ar := ar) (J := J) hI hpr
    habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hFS hCd hBl hraP hraAb hrg hb32 hfs hFP fp ra tp hNoS hDtP
  have hPWE := printWE_hPWEA (G0 := G0) (rd := rd) (G := G) (ar := ar) (J := J) (Dt := Dt) (lsize := lsize) (p := p)
    hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hFS hCd hBl hraP hraAb hfs hFP fp ra tp hNoS
  refine printCallCH_ofA hf h1 h16 hFS hR hal hlo hhi (fun _ _ h => cdOf_of_cdC hI (hCd _ _ h).toCdC)
    (fun _ _ _ h => cdOf_of_blC hI (hBl _ _ _ h).1) hI.lays hI.endOk hpr hpd hd hprog (fun _ => rfl)
    (fun _ s _ _ _ _ _ hr h hΦ => ByteOut.closed (I := isaLSE2) (s := s) hr h hΦ) hTp
    (fun c0 pc env lits cs bufs n x is a e b o m cw kk pc' s c hG0 hT hi hL =>
      hWL c0 pc env lits cs bufs n x is a e b o m cw kk pc' s c hG0 hT hi (letAt_mono_i hiL hL))
    ?_ ?_ hAb
  · intro c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn nv mv kk pc' hG0 hT hi hpw hSA hLen hS
    have he := hie x is a e hT
    refine hPW c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn nv mv kk pc' hG0 hT hi hpw ?_ hLen ?_
    · unfold PrintSlotsA at hSA ⊢; rw [he]; exact hSA
    · unfold PrintSlots at hS ⊢; rw [he]; exact hS
  · intro c0 pc env lits cs bufs n x is a e b o m cw c1 envR kk pc' hG0 hT hi hSA hLen hS
    have he := hie x is a e hT
    refine hPWE c0 pc env lits cs bufs n x is a e b o m cw c1 envR kk pc' hG0 hT hi ?_ hLen ?_
    · unfold PrintSlotsA at hSA ⊢; rw [he]; exact hSA
    · unfold PrintSlots at hS ⊢; rw [he]; exact hS

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.immIn_mono_i' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.immIn_mono_i

/-- info: 'Spike.Lib.LowerA64.slotRepAt_mono_i' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.slotRepAt_mono_i

/-- info: 'Spike.Lib.LowerA64.letAt_mono_i' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.letAt_mono_i

/-- info: 'Spike.Lib.LowerA64.printCallC_instAI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.printCallC_instAI

/-- info: 'Spike.Lib.LowerA64.printCallCH_instAI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.printCallCH_instAI
