/-
**hello's level 1 with the heap abort at `wXA`, its control facts discharged** (x86-64; the twin of
`Spike/Lib/A64HelloLevel1HA.lean`): level 1's landing segment with `wc_main`'s box allocation's heap abort at
`HelloWc.wXA` (`Level1.land_segWSLA`: the abort keeps `wc_main`'s spills) and closed by `HabCtlA`'s stub
(`wc_heapAbStubKHA`, `wc_heapAb_segWSHA`) at `HabCtlA.HabCtlHA`, whose producer `HabCtlA.habCtlHA_jr1L` places
`c0H` from the spills. No control premise is left, only the certificate table's `z` at `i0` (`hz`; at the root
`HabCtlA.hz_i0M`).

- `hello_hab_closedLAg`: the heap-abort exit at `wXA` closes inside `StartWcS.WSg ownW` at any level own `ownW`,
  at a fixed caller `σC`, from `HabCtlHA` at `wc_main`'s region and frame condition and the stub's path inside the
  level (`hP0`, `HabCtlA.wc_heapAbStubKHAg`'s).
- `hello_hab_closedLA`: `hello_hab_closedLAg` at `ownGH` (`WS`), `hP0` by `HabCtlS.hpathW_hab0HS`.
- `hB_landAg`: level 1's landing segment at any owned words `own` (`Level1I.W1Rg own`, `StartH0H1.RdLandHg own`),
  from rodata's landing to no exit, the stub's path inside the level given (`hP0`).
- `hB_landA`: it at `ownGH`, `hP0` by `HabCtlS.hpathW_hab0HS`.

## Differences from the AArch64 version

- `scc_rt_main`'s region at the switch base `v` is `MainGlue.RS helloLsw v` (AArch64 `swR v (-helloLsw) 0`), so
  `wc_main`'s is `wcR (RS helloLsw v) helloD` (bounds `-400`, `8`), and `rdJH` takes it (`J'` at `v`).
- `hello_hab_closedLA` is stated at the root's layout `ofPlaceWX hpw (immsH Λ0 i0)` (AArch64: any table `i`), so
  the region's facts are `Land.fstable_FS`'s and `HelloM.wcR_ok`'s; the heap abort's exit is at `4202760`
  (`abH_labsH`).
- The landing's segment is a `SegWSP` (`Level1.land_segWSLA`'s, rows after the source's publication); the closing
  stub's `SegWS` enters it by `SegWS.toP`.
- The caller's slot holding main's TCB is `-16` (`Level1I.slot16_rdJ`; AArch64 `-80`), the thread pointer
  `tpOf (tcbS Ly)`.
-/
import Spike.Lib.X64HelloLevel1I
import Spike.Lib.X64HelloLevel1A
import Spike.Lib.X64HelloHabCtlA
import Spike.Lib.X64HelloHAbStub
import Spike.Lib.X64HelloHAbW
import Spike.Lib.X64HelloStartH0B

namespace Spike.Lib.X64.HelloPh.Level1HA

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Entry)
open Scc.Cert.Rt.X64 (codeT codeT_eq Lays endOf)
open Scc.Sem.X64 (codeLabel pcOf abi cellsOf)
open Spike.Lib (FragS Frag MemSide SegWS PlaceWX)
open Spike.Lib.X64SegWPub (SegWSP)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerA (TakeCKS)
open Spike.Lib.X64.HelloPh (lo)
open Spike.Lib.X64.WakeWf (DtW)
open Spike.Lib.X64 (At)
open Spike.Lib.X64.Flow.Hello1 (mWC mRdJ0)
open Spike.Lib.X64.Flow.HelloM (wcR wcF wcJ0)
open Spike.Lib.X64.Flow.HelloWc (wXA)
open Spike.Lib.X64.WakePh.MainGlue (FS JS RS tcbS topS)
open Spike.Lib.X64.KeepTP (TP)
open Spike.Lib.X64.Alloc (Call)
open Spike.Lib.X64.Flow.Ret0 (tpOf)
open Spike.Lib.X64.HelloPh.StartGlue (X0WH)
open Spike.Lib.X64.HelloPh.StartWcS (WS rdJH)
open Spike.Lib.X64.HelloPh.StartH0G (helloD helloLsw)
open Spike.Lib.X64.HelloPh.StartH0U (msUH)
open Spike.Lib.X64.HelloPh.StartH0H1 (RdLandH)
open Spike.Lib.X64.HelloPh.HabCtlA (HabCtlHA wc_heapAb_segWSHA wc_heapAbStubKHA habCtlHA_jr1L)
open Spike.Lib.X64.HelloPh.MainGlueS (MainWcPS)
open Spike.Lib.X64.HelloPh.Level1 (LandF JpL JpT)
open Spike.Lib.X64.HelloPh.Level1I (W1R XR)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64.HelloPh.C0S (c0S)
open Spike.Lib.X64HelloMainPreSrc (newTerm)
open Spike.Lib.X64HelloSrc (helloSrc)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.X64.AS

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "IH" => Spike.Lib.X64.HelloImms.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw IH

set_option hygiene false in
local notation "RS0" => Spike.Lib.X64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "AR" => Spike.Lib.X64.WakeOD.arW hpw IH

set_option hygiene false in
local notation "NT" => Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab

set_option hygiene false in
local notation "AX" => (Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL

set_option hygiene false in
/-- main's thread pointer. -/
local notation "TV" => tpOf (tcbS (Ly))

set_option hygiene false in
/-- The first stack's top (the start's `v`). -/
local notation "TOP" => topS (Ly) 0#64

/-! ## The heap abort at `wXA` closes -/

section Place

set_option hygiene false in
/-- The memory side at the start's labels, the entry's marks. -/
local notation "MSf" => fun fs => Spike.Lib.X64ConsumerA.msOfA (Ly).Λ
  ((Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ) rd G own (AR) I LB ls fs

/-- **The heap-abort exit at `wXA` closes at any level own `ownW`** (`HabCtlA.wc_heapAbStubKHAg`'s stub): from
`wc_main`'s `wXA` exit at the frames `[]` below the caller `σC`, a segment inside `WSg ownW` at the labels `LB`,
under the take move, with no exit, given `HabCtlHA` at `wc_main`'s region `wcR` and frame condition `wcF`, and the
stub's path inside the level (`hP0`) at the first stack's top. -/
theorem hello_hab_closedLAg {ownW : Spike.Lib.X64Consumer.Own} {LB : Lbl} {E : Scc.Sem.Entry}
    {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
    {own : Spike.Lib.X64ConsumerS.OwnS} {I : Spike.Lib.X64ConsumerS.InvS} {ls : Lsize}
    {Ctx : FragS isa} {ls0 : Lsize} {frM : TermRun.Frame} {t : UInt64}
    {σC : FAS} {Jr1 : FAS → Spike.Lib.Ctl → Prop}
    (hpa : cellsOf asm = some o.prog)
    (hhp : cellsOf asm = some SccCode.helloCells)
    (hlo0 : Λ0.code.lo = lo)
    /- the controls' facts at `wXA` (`HabCtlA.habCtlHA_jr1L` at level 1) -/
    (hhabctl : ∀ v m1 σ1, HabCtlHA ((MSf) []) (Ly).lab helloSrc (Ly).Λ LB (AR)
      [] (wcJ0 (mWC (Ly).lab σC Jr1).J σ1) (wcR (RS helloLsw v) helloD)
      (wcF (RS helloLsw v) helloD (FS (Ly) (RS0) helloLsw 0#64 v) m1 σ1))
    /- the stub's path inside `WSg ownW` (`HabCtlA.wc_heapAbStubKHAg`'s `hP0`) at `wc_main`'s region at the first
    stack's top -/
    (hP0 : ∀ (F' : MachineData → Prop) (c0 : Spike.Lib.Ctl),
      FStable ((wcR (RS helloLsw (TOP)) helloD).callee (-304 - 8) (-24) 16) F' →
      (([] : List TermRun.Frame) = [] → ∀ a, c0.term ≠ .ret a) ∧ Spike.Lib.X64.WakeWf.RunWf helloSrc c0 [] →
      (∀ s : State, F' s.st.1 → Spike.Lib.X64ConsumerS.PlacedSE (Ly).Λ LB s c0 []) →
      Spike.Lib.HeapAbortOblA (AR).cells (AR).ctr c0 →
      Abort.Disp.HPathW (fun s c => Spike.Lib.X64.HelloPh.StartWcS.WSg ownW (Ly) (AR) helloSrc DtW
          (Spike.Lib.X64.HelloPh.ClH (Ly)) Ctx LB ls0 frM (X0WH (Ly) (AX)) s c []) (fun _ _ => False) (Ly).exe
        (Ly).endPc ((wcR (RS helloLsw (TOP)) helloD).callee (-304 - 8) (-24) 16) F' c0
        ((Ly).lab ".Lscc_rt_alloc.full" + 12).toBitVec) :
    SegWS (Spike.Lib.X64.HelloPh.StartWcS.WSg ownW (Ly) (AR) helloSrc DtW (Spike.Lib.X64.HelloPh.ClH (Ly)) Ctx LB
        ls0 frM (X0WH (Ly) (AX)))
      (Spike.Lib.X64.PhRec.K (Ly) (RS0)) helloSrc LB (MSf)
      (Frag.at (fun s c => ∃ v m1 σ1,
        At (Ly).exe (Ly).endPc (wcR (RS helloLsw v) helloD)
          (wcF (RS helloLsw v) helloD (FS (Ly) (RS0) helloLsw 0#64 v) m1 σ1)
          (wXA ((MSf) []) (Ly).lab (wcJ0 (mWC (Ly).lab σC Jr1).J σ1)) s c ∧ TP t s) [])
      (fun _ _ _ => False) := by
  have hp : o.prog = SccCode.helloCells := Option.some.inj (hpa.symm.trans hhp)
  have hprog : (Ly).prog = SccCode.helloCells := hp
  have hlo : (Ly).Λ.code.lo = lo := hlo0
  have hlab : ∀ l x, codeLabel lo SccCode.helloCells l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => Spike.Lib.PlaceWX.hlab_ofPlaceWX hpw IH l x (by rw [hlo, hp]; exact h)
  have hab : ∀ s : State, s.st.2 = (Ly).lab "scc_rt_abort_heap_exit" → ((MSf) []).abortAt s := fun s hs => by
    obtain ⟨-, e9⟩ := Spike.Lib.X64.HelloPh.abH_labsH hlab
    have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
      Spike.Lib.PlaceWX.abortLbl_of_placeWX (Spike.Lib.PlaceWX.link IH hpw)
    refine ⟨.heap, 4202760, ?_, by unfold pcOf; rw [hs, e9]; rfl⟩
    rw [Spike.Lib.X64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hpa]
    show codeLabel (Ly).Λ.code.lo (Ly).prog ((Ly).Λ.abortLbl .heap) = _
    rw [hprog, hlo, hΛ, ← codeT_eq]; decide +kernel
  refine (SegWS.exists_pre (P := fun g : BitVec 64 × MachineData × FAS =>
      Frag.at (At (Ly).exe (Ly).endPc (wcR (RS helloLsw g.1) helloD)
        (wcF (RS helloLsw g.1) helloD (FS (Ly) (RS0) helloLsw 0#64 g.1) g.2.1 g.2.2)
        (wXA ((MSf) []) (Ly).lab (wcJ0 (mWC (Ly).lab σC Jr1).J g.2.2))) [])
      fun ⟨v, m1, σ1⟩ => ?_).mono_pre
    fun _ _ _ ⟨⟨v, m1, σ1, h, _⟩, hf⟩ => ⟨⟨v, m1, σ1⟩, h, hf⟩
  by_cases hv : v = TOP
  case neg =>
    refine SegWS.empty fun _ _ _ h => ?_
    obtain ⟨⟨-, -, -, -, _, -, hF, -⟩, -⟩ := h
    exact hv hF.1.1.2.1.1
  subst hv
  obtain ⟨-, hR0, hF0⟩ := Spike.Lib.X64.HelloPh.Land.fstable_FS hpw i0
  obtain ⟨hR, hF⟩ := Spike.Lib.X64.Flow.HelloM.wcR_ok (D := helloD) (by decide) (by decide) hR0 hF0
    (by show (8 : Int) - helloLsw ≤ -80 - helloD; decide) (by show (0 : Int) ≤ 8; decide) m1 σ1
  exact wc_heapAb_segWSHA hF hR (by show (-helloD : Int) ≤ -336; decide) (by show (-296 : Int) ≤ 8; decide) rfl
    (Spike.Lib.X64.HelloPh.HabCtlA.wc_heapAbStubKHAg hprog hlo hlab hF hR (by show (-helloD : Int) ≤ -336; decide)
      (by show (-296 : Int) ≤ 8; decide) rfl (hhabctl _ m1 σ1) hab hP0) _

/-- **The heap-abort exit at `wXA` closes** (`HabCtlA`'s stub): `hello_hab_closedLAg` at the start's own
`ownGH Ly NT` (`WS`), the stub's path by `HabCtlS.hpathW_hab0HS`. -/
theorem hello_hab_closedLA {LB : Lbl} {E : Scc.Sem.Entry} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
    {own : Spike.Lib.X64ConsumerS.OwnS} {I : Spike.Lib.X64ConsumerS.InvS} {ls : Lsize}
    {Ctx : FragS isa} {ls0 : Lsize} {frM : TermRun.Frame} {t : UInt64}
    {σC : FAS} {Jr1 : FAS → Spike.Lib.Ctl → Prop}
    (hpa : cellsOf asm = some o.prog)
    (hhp : cellsOf asm = some SccCode.helloCells)
    (hlo0 : Λ0.code.lo = lo)
    /- the controls' facts at `wXA` (`HabCtlA.habCtlHA_jr1L` at level 1) -/
    (hhabctl : ∀ v m1 σ1, HabCtlHA ((MSf) []) (Ly).lab helloSrc (Ly).Λ LB (AR)
      [] (wcJ0 (mWC (Ly).lab σC Jr1).J σ1) (wcR (RS helloLsw v) helloD)
      (wcF (RS helloLsw v) helloD (FS (Ly) (RS0) helloLsw 0#64 v) m1 σ1)) :
    SegWS (WS (Ly) (NT) (AR) helloSrc DtW (Spike.Lib.X64.HelloPh.ClH (Ly)) Ctx LB ls0 frM (X0WH (Ly) (AX)))
      (Spike.Lib.X64.PhRec.K (Ly) (RS0)) helloSrc LB (MSf)
      (Frag.at (fun s c => ∃ v m1 σ1,
        At (Ly).exe (Ly).endPc (wcR (RS helloLsw v) helloD)
          (wcF (RS helloLsw v) helloD (FS (Ly) (RS0) helloLsw 0#64 v) m1 σ1)
          (wXA ((MSf) []) (Ly).lab (wcJ0 (mWC (Ly).lab σC Jr1).J σ1)) s c ∧ TP t s) [])
      (fun _ _ _ => False) := by
  have hp : o.prog = SccCode.helloCells := Option.some.inj (hpa.symm.trans hhp)
  have hprog : (Ly).prog = SccCode.helloCells := hp
  have hlo : (Ly).Λ.code.lo = lo := hlo0
  have hlab : ∀ l x, codeLabel lo SccCode.helloCells l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => Spike.Lib.PlaceWX.hlab_ofPlaceWX hpw IH l x (by rw [hlo, hp]; exact h)
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
    Spike.Lib.PlaceWX.abortLbl_of_placeWX (Spike.Lib.PlaceWX.link IH hpw)
  obtain ⟨-, hR0, -⟩ := Spike.Lib.X64.HelloPh.Land.fstable_FS hpw i0
  have hlo1 : (RS helloLsw (TOP)).lo ≤ -80 - helloD := by show (8 : Int) - helloLsw ≤ -80 - helloD; decide
  have hhi1 : (0 : Int) ≤ (RS helloLsw (TOP)).hi := by show (0 : Int) ≤ 8; decide
  have hD : (0 : Int) ≤ helloD := by decide
  have hRw : (wcR (RS helloLsw (TOP)) helloD).OK :=
    Region.callee_ok hR0 (by omega) (by omega) (by omega) (by omega)
  have hlo2 : (wcR (RS helloLsw (TOP)) helloD).lo ≤ -336 := by show (-helloD : Int) ≤ -336; decide
  have hhi2 : (-296 : Int) ≤ (wcR (RS helloLsw (TOP)) helloD).hi := by show (-296 : Int) ≤ 8; decide
  have hR' : ((wcR (RS helloLsw (TOP)) helloD).callee (-304 - 8) (-24) 16).OK :=
    Region.callee_ok hRw (by omega) (by decide) (by omega) (by omega)
  exact hello_hab_closedLAg hpw i0 hpa hhp hlo0 hhabctl fun F' c0 hF' hc0 hpl hobl =>
    Spike.Lib.X64.HelloPh.HabCtlS.hpathW_hab0HS hprog hlo hlab (NT) hΛ hR' (by simp [Region.callee])
      (by simp [Region.callee]) rfl (.inl rfl) Spike.Lib.X64.HelloPh.ClH.cl hc0 hF' hpl hobl
      (Spike.Lib.X64.HelloPh.HAbStub.x0WH_abort hlab rfl)

end Place

/-! ## The landing segment -/

variable (E : Entry) (rd : TermRun.Word → Prop) (I : Spike.Lib.X64ConsumerS.InvS) (ls : Lsize)

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
local notation "FR" => Spike.Lib.X64HelloRdCf.frH c0S.env

set_option hygiene false in
local notation "KR" => Spike.Lib.X64.PhRec.K (Ly) (RS0)

set_option hygiene false in
/-- `wc_rodata`'s entry invariant at the switch base `v`. -/
local notation "J'" v => rdJH (Ly).lab (RS helloLsw v) (JS (Ly) 0#64 c0S)

set_option hygiene false in
/-- Level 0's memory sides (the landing's). -/
local notation "MSU" => msUH (asm := asm) hpw i0 E rd I ls

set_option hygiene false in
/-- The level's memory sides after rodata's allocation of `l` at `b`, `n` words, at the frames `fs`. -/
local notation "MS1" => fun (l : WeakMem.AllocLabel) (b n : Nat) (fs : List TermRun.Frame) =>
  Spike.Lib.X64ConsumerA.msOfA (Ly).Λ
    ((Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ) rd
    (Spike.Lib.X64HelloGOf2H.gWH hpw IH (Spike.Lib.X64WakeHG.cTW hpw IH))
    (fun s _ => Spike.Lib.X64.HelloPh.ownGH (Ly) NT s)
    (AR) I (Spike.Lib.X64ConsumerA.upd (LB) l b) (Spike.Lib.X64ConsumerA.updN (ls0T ls) l n) fs

set_option hygiene false in
/-- Level 0's memory sides (the landing's) at an own map `own`. -/
local notation "MSUg" => fun own => Spike.Lib.X64.HelloPh.StartH0U.msUHg (asm := asm) hpw i0 own E rd I ls

set_option hygiene false in
/-- The level's memory sides after rodata's allocation at an own map `own`. -/
local notation "MS1g" => fun (own : Spike.Lib.X64Consumer.Own) (l : WeakMem.AllocLabel) (b n : Nat)
    (fs : List TermRun.Frame) =>
  Spike.Lib.X64ConsumerA.msOfA (Ly).Λ
    ((Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ) rd
    (Spike.Lib.X64HelloGOf2H.gWH hpw IH (Spike.Lib.X64WakeHG.cTW hpw IH))
    (fun s _ => own s)
    (AR) I (Spike.Lib.X64ConsumerA.upd (LB) l b) (Spike.Lib.X64ConsumerA.updN (ls0T ls) l n) fs

set_option maxHeartbeats 1600000 in
/-- **Level 1's landing segment, the heap abort at `wXA`, at any owned words `own`** (`Level1.land_segWSLA` then
`hello_hab_closedLAg`; module doc), the stub's path inside the level given (`hP0`): from rodata's landing
`RdLandHg own` at `[FR]`, inside `W1Rg own ∧ XR` under `TakeCKS`, with no exit. The
abort's controls are `HabCtlA.habCtlHA_jr1L`'s at the caller's slot `-16` (the case split's `hs`), `l` fresh
(`hl`) and `hz`. -/
theorem hB_landAg {own : Spike.Lib.X64Consumer.Own} {J1 : FAS → FAS → Spike.Lib.Ctl → Prop}
    (hpa : cellsOf asm = some o.prog)
    (hhp : cellsOf asm = some SccCode.helloCells)
    (hlo0 : Λ0.code.lo = lo)
    /- the certificate table's `z` at `newTerm` (at the root's `HelloImms.i0M`: `HabCtlA.hz_i0M`) -/
    (hz : i0 newTerm "z" 0 = some 0)
    /- the landing's caller holds main's TCB at its slot `-16` (`Level1I.slot16_rdJ` at `J1 := mRdJ0 J'`) -/
    (hJ1 : ∀ σC σ c, J1 σC σ c → σC.slot (-16) = Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)
    /- `MainWcPS` at the level: `wc_rodata`'s rest from `.x15` at `JpT (JpL …) TV` and `wc_main` to its box
    allocation, at the first stack's top -/
    (hP : ∀ l b n m0 σC, (LB) l = none → AllocLand (AR).heap (AR).cells b n →
      σC.slot (-16) = Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64 →
      ∃ Jp' Jx1 J2 J2' J3 J4 J4x J5 Jr : FAS → Spike.Lib.Ctl → Prop,
      MainWcPS (Spike.Lib.X64.HelloPh.Level1I.W1Rg (asm := asm) hpw i0 E rd ls own l b n) (KR) helloSrc
        (Spike.Lib.X64ConsumerA.upd (LB) l b)
        ((MS1g) own l b n) (Ly).exe (Ly).endPc (RS helloLsw (TOP)) helloD (FS (Ly) (RS0) helloLsw 0#64 (TOP)) (FR)
        m0 σC
        (JpT (JpL (R := RS helloLsw (TOP)) ((MSUg) own [FR]) (Ly).lab (mRdJ0 (J' (TOP)) σC) (J1 σC) l b n) (TV))
        Jp' Jx1 J2 J2' J3 J4 J4x J5 Jr (Spike.Lib.X64.HelloPh.Land.Jr1LH hpw i0 l b) (TV))
    /- the box allocation's words free at `FS` -/
    (hmem0 : ∀ l b n, ∀ q : Call, q.OKB ((MS1g) own l b n []) (Ly).lab → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ((MS1g) own l b n []).ctr ∨
        ∃ o, o + ((MS1g) own l b n []).units q.n q.τ ≤ ((MS1g) own l b n []).cells ∧
        a.toNat = q.hdrAt ((MS1g) own l b n []) o) →
      ∀ m, FS (Ly) (RS0) helloLsw 0#64 (TOP) m → Mem.loadInt m.dmem a 8 = none)
    /- the stub's path inside the level (`hello_hab_closedLAg`'s `hP0`) at each allocation -/
    (hP0 : ∀ l b n (F' : MachineData → Prop) (c0 : Spike.Lib.Ctl),
      FStable ((wcR (RS helloLsw (TOP)) helloD).callee (-304 - 8) (-24) 16) F' →
      (([] : List TermRun.Frame) = [] → ∀ a, c0.term ≠ .ret a) ∧ Spike.Lib.X64.WakeWf.RunWf helloSrc c0 [] →
      (∀ s : State, F' s.st.1 →
        Spike.Lib.X64ConsumerS.PlacedSE (Ly).Λ (Spike.Lib.X64ConsumerA.upd (LB) l b) s c0 []) →
      Spike.Lib.HeapAbortOblA (AR).cells (AR).ctr c0 →
      Abort.Disp.HPathW (fun s c => Spike.Lib.X64.HelloPh.StartWcS.WSg own (Ly) (AR) helloSrc DtW
          (Spike.Lib.X64.HelloPh.ClH (Ly)) (Spike.Lib.X64.HelloPh.Land.CtxR1H (asm := asm) hpw i0 E rd ls l b n)
          (Spike.Lib.X64ConsumerA.upd (LB) l b) (Spike.Lib.X64ConsumerA.updN (ls0T ls) l n) (FR) (X0WH (Ly) (AX))
          s c []) (fun _ _ => False) (Ly).exe
        (Ly).endPc ((wcR (RS helloLsw (TOP)) helloD).callee (-304 - 8) (-24) 16) F' c0
        ((Ly).lab ".Lscc_rt_alloc.full" + 12).toBitVec) :
    ∀ l b n, (LB) l = none → AllocLand (AR).heap (AR).cells b n →
      SegWSP (fun s c fs => Spike.Lib.X64.HelloPh.Level1I.W1Rg (asm := asm) hpw i0 E rd ls own l b n s c fs ∧
          XR hpw i0 l b n s c fs)
        (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) helloSrc (Spike.Lib.X64ConsumerA.upd (LB) l b)
        ((MS1g) own l b n)
        (Frag.at (Spike.Lib.X64.HelloPh.StartH0H1.RdLandHg (asm := asm) hpw i0 own E rd I ls J1 l b n) [FR])
        (fun _ _ _ => False) := by
  intro l b n hl hb
  have hp : o.prog = SccCode.helloCells := Option.some.inj (hpa.symm.trans hhp)
  have hprog : (Ly).prog = SccCode.helloCells := hp
  have hpS : Lays (Ly).exe SccCode.helloCells (Ly).pfx := hprog ▸ (Ly).lays
  have hendS : (Ly).endPc = endOf (Ly).exe SccCode.helloCells (Ly).pfx := by
    show endOf (Ly).exe (Ly).prog (Ly).pfx = _; rw [hprog]
  obtain ⟨-, hok, hF⟩ := Spike.Lib.X64.HelloPh.Land.fstable_FS hpw i0
  refine (((SegWSP.exists_pre (P := fun g : BitVec 64 × MachineData × FAS =>
      Frag.at (fun s c => LandF ((MSUg) own [FR]) (Ly).exe (Ly).endPc (RS helloLsw g.1)
        (FS (Ly) (RS0) helloLsw 0#64 g.1) (mRdJ0 (J' g.1) g.2.2) (J1 g.2.2) g.2.1 g.2.2 l b n s c ∧ TP (TV) s)
        [FR])
      fun ⟨v, m0, σC⟩ => ?_).mono_K fun s c fs hW s' =>
        Spike.Lib.X64.HelloPh.StartH0B.takeCKS_iffH hpw IH hW.2.1).mono_W
      fun s c fs h => ⟨h, h.2.1⟩).mono_pre
    fun s c fs ⟨⟨v, m0, σC, q, F', h1, h2, hA, _, ht⟩, hfs⟩ => ⟨(v, m0, σC), ⟨⟨q, F', h1, h2, hA⟩, ht⟩, hfs⟩
  by_cases hv : v = TOP
  case neg =>
    refine SegWSP.empty fun s c fs h => ?_
    obtain ⟨⟨⟨q, F', h1, -, -, -, -, -, σ, -, hF', -⟩, -⟩, -⟩ := h
    exact hv (h1 _ hF').1.1.2.1.1
  subst hv
  by_cases hs : σC.slot (-16) = Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64
  case neg =>
    refine SegWSP.empty fun s c fs h => ?_
    obtain ⟨⟨⟨q, F', -, h2, -, -, -, -, σ, -, hF', -⟩, -⟩, -⟩ := h
    obtain ⟨mC, σ', c', -, ⟨⟨σe, hJe, -⟩, -⟩, -⟩ := h2 _ hF'
    exact hs (hJ1 _ _ _ hJe)
  have hC := hello_hab_closedLAg hpw i0 (ownW := own) (E := E) (rd := rd) (I := I)
    (G := Spike.Lib.X64HelloGOf2H.gWH hpw IH (Spike.Lib.X64WakeHG.cTW hpw IH))
    (own := fun s _ => own s) (ls := Spike.Lib.X64ConsumerA.updN (ls0T ls) l n)
    (Ctx := Spike.Lib.X64.HelloPh.Land.CtxR1H (asm := asm) hpw i0 E rd ls l b n)
    (ls0 := Spike.Lib.X64ConsumerA.updN (ls0T ls) l n) (frM := FR) (t := TV) (σC := σC)
    (Jr1 := Spike.Lib.X64.HelloPh.Land.Jr1LH hpw i0 l b) hpa hhp hlo0
    (fun _ _ _ => habCtlHA_jr1L hpw i0 hl hs hz rfl rfl rfl
      (show (-helloD : Int) ≤ -304 by decide) (show (0 : Int) ≤ 8 by decide)) (hP0 l b n)
  obtain ⟨Jp', Jx1, J2, J2', J3, J4, J4x, J5, Jr, hPv⟩ := hP l b n m0 σC hl hb hs
  refine (Spike.Lib.X64.HelloPh.Level1.land_segWSLA rfl rfl hpS hendS (D := helloD) (by decide) (by decide) hF
    hok (show (8 - helloLsw : Int) ≤ -288 by decide) (show (8 - helloLsw : Int) ≤ -80 - helloD by decide)
    (show (8 : Int) ≤ 8 by decide) rfl hPv (hmem0 l b n)).seq ?_
  exact hC.toP.mono_pre fun s c fs ⟨⟨m1, σ1, h, ht⟩, hfs⟩ => ⟨⟨_, m1, σ1, h, ht⟩, hfs⟩

set_option maxHeartbeats 1600000 in
/-- **Level 1's landing segment, the heap abort at `wXA`** (`hB_landAg` at `ownGH`, the stub's path by
`HabCtlS.hpathW_hab0HS`; module doc): from rodata's landing `RdLandH` at `[FR]`, inside `W1R ∧ XR` under
`TakeCKS`, with no exit. The abort's controls are `HabCtlA.habCtlHA_jr1L`'s at the caller's slot `-16` (the case
split's `hs`), `l` fresh (`hl`) and `hz`. -/
theorem hB_landA {J1 : FAS → FAS → Spike.Lib.Ctl → Prop}
    (hpa : cellsOf asm = some o.prog)
    (hhp : cellsOf asm = some SccCode.helloCells)
    (hlo0 : Λ0.code.lo = lo)
    /- the certificate table's `z` at `newTerm` (at the root's `HelloImms.i0M`: `HabCtlA.hz_i0M`) -/
    (hz : i0 newTerm "z" 0 = some 0)
    /- the landing's caller holds main's TCB at its slot `-16` (`Level1I.slot16_rdJ` at `J1 := mRdJ0 J'`) -/
    (hJ1 : ∀ σC σ c, J1 σC σ c → σC.slot (-16) = Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)
    /- `MainWcPS` at the level: `wc_rodata`'s rest from `.x15` at `JpT (JpL …) TV` and `wc_main` to its box
    allocation, at the first stack's top -/
    (hP : ∀ l b n m0 σC, (LB) l = none → AllocLand (AR).heap (AR).cells b n →
      σC.slot (-16) = Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64 →
      ∃ Jp' Jx1 J2 J2' J3 J4 J4x J5 Jr : FAS → Spike.Lib.Ctl → Prop,
      MainWcPS (W1R (asm := asm) hpw i0 E rd ls l b n) (KR) helloSrc (Spike.Lib.X64ConsumerA.upd (LB) l b)
        ((MS1) l b n) (Ly).exe (Ly).endPc (RS helloLsw (TOP)) helloD (FS (Ly) (RS0) helloLsw 0#64 (TOP)) (FR)
        m0 σC
        (JpT (JpL (R := RS helloLsw (TOP)) ((MSU) [FR]) (Ly).lab (mRdJ0 (J' (TOP)) σC) (J1 σC) l b n) (TV))
        Jp' Jx1 J2 J2' J3 J4 J4x J5 Jr (Spike.Lib.X64.HelloPh.Land.Jr1LH hpw i0 l b) (TV))
    /- the box allocation's words free at `FS` -/
    (hmem0 : ∀ l b n, ∀ q : Call, q.OKB ((MS1) l b n []) (Ly).lab → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ((MS1) l b n []).ctr ∨ ∃ o, o + ((MS1) l b n []).units q.n q.τ ≤ ((MS1) l b n []).cells ∧
        a.toNat = q.hdrAt ((MS1) l b n []) o) →
      ∀ m, FS (Ly) (RS0) helloLsw 0#64 (TOP) m → Mem.loadInt m.dmem a 8 = none) :
    ∀ l b n, (LB) l = none → AllocLand (AR).heap (AR).cells b n →
      SegWSP (fun s c fs => W1R (asm := asm) hpw i0 E rd ls l b n s c fs ∧ XR hpw i0 l b n s c fs)
        (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) helloSrc (Spike.Lib.X64ConsumerA.upd (LB) l b)
        ((MS1) l b n) (Frag.at (RdLandH (asm := asm) hpw i0 E rd I ls J1 l b n) [FR]) (fun _ _ _ => False) := by
  have hp : o.prog = SccCode.helloCells := Option.some.inj (hpa.symm.trans hhp)
  have hprog : (Ly).prog = SccCode.helloCells := hp
  have hlo : (Ly).Λ.code.lo = lo := hlo0
  have hlab : ∀ l x, codeLabel lo SccCode.helloCells l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => Spike.Lib.PlaceWX.hlab_ofPlaceWX hpw IH l x (by rw [hlo, hp]; exact h)
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
    Spike.Lib.PlaceWX.abortLbl_of_placeWX (Spike.Lib.PlaceWX.link IH hpw)
  obtain ⟨-, hR0, -⟩ := Spike.Lib.X64.HelloPh.Land.fstable_FS hpw i0
  have hlo1 : (RS helloLsw (TOP)).lo ≤ -80 - helloD := by show (8 : Int) - helloLsw ≤ -80 - helloD; decide
  have hhi1 : (0 : Int) ≤ (RS helloLsw (TOP)).hi := by show (0 : Int) ≤ 8; decide
  have hD : (0 : Int) ≤ helloD := by decide
  have hRw : (wcR (RS helloLsw (TOP)) helloD).OK :=
    Region.callee_ok hR0 (by omega) (by omega) (by omega) (by omega)
  have hlo2 : (wcR (RS helloLsw (TOP)) helloD).lo ≤ -336 := by show (-helloD : Int) ≤ -336; decide
  have hhi2 : (-296 : Int) ≤ (wcR (RS helloLsw (TOP)) helloD).hi := by show (-296 : Int) ≤ 8; decide
  have hR' : ((wcR (RS helloLsw (TOP)) helloD).callee (-304 - 8) (-24) 16).OK :=
    Region.callee_ok hRw (by omega) (by decide) (by omega) (by omega)
  exact hB_landAg hpw i0 E rd I ls hpa hhp hlo0 hz hJ1 hP hmem0 fun _ _ _ F' c0 hF' hc0 hpl hobl =>
    Spike.Lib.X64.HelloPh.HabCtlS.hpathW_hab0HS hprog hlo hlab (NT) hΛ hR' (by simp [Region.callee])
      (by simp [Region.callee]) rfl (.inl rfl) Spike.Lib.X64.HelloPh.ClH.cl hc0 hF' hpl hobl
      (Spike.Lib.X64.HelloPh.HAbStub.x0WH_abort hlab rfl)

end Spike.Lib.X64.HelloPh.Level1HA

/-- info: 'Spike.Lib.X64.HelloPh.Level1HA.hello_hab_closedLAg' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Level1HA.hello_hab_closedLAg

/-- info: 'Spike.Lib.X64.HelloPh.Level1HA.hello_hab_closedLA' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Level1HA.hello_hab_closedLA

/-- info: 'Spike.Lib.X64.HelloPh.Level1HA.hB_landAg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Level1HA.hB_landAg

/-- info: 'Spike.Lib.X64.HelloPh.Level1HA.hB_landA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Level1HA.hB_landA
