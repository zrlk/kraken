/-
**hello's level 1 with the heap abort at `wXA`, its control facts discharged** (AArch64): `Level1I.hB_land` with
`wc_main`'s box allocation's heap abort at `HelloWc.wXA`
(`Level1.land_segWSLA`: the abort keeps `wc_main`'s spills `-144 … -112`) and closed by `HabCtlA`'s stub
(`wc_heapAbStubKHA`, `wc_heapAb_segWSHA`) at `HabCtlA.HabCtlHA`, whose producer `HabCtlA.habCtlHA_jr1L` places
`c0H` from the spills. `HabCtl.HabCtlH` (premise `hhabctl` of `Level1I.hB_land`) asked `c0H` placed at every state
(row `L1-c0pl`, false); here no control premise is left, only the certificate table's `z` at `i0` (`hz`; at the
root `HabCtlA.hz_i0M`).

- `hello_hab_closedLA`: `StartH0CL.hello_hab_closedL` at `wXA`, at a fixed caller `m0`, `σC`, from `HabCtlHA` at
  `wc_main`'s region and frame condition.
- `hB_landA`: `Level1I.hB_land` with `hhabctl` replaced by `hz`.
-/
import Spike.Lib.A64HelloLevel1I
import Spike.Lib.A64HelloLevel1A
import Spike.Lib.A64HelloHabCtlA

namespace Spike.Lib.A64.HelloPh.Level1HA

variable {asm : String}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Scc.Cert.Rt.A64 (codeT codeT_eq Lays endOf)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem.A64 (pcOf abi textProgram)
open Spike.Lib (FragS Frag MemSide SegWS)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerA (TakeCKS)
open Spike.Lib.A64.WakePh (lo)
open Spike.Lib.A64.WakeWf (DtW)
open Spike.Lib.A64.Flow (swR At)
open Spike.Lib.A64.Flow.Hello1 (mWC mRdJ0)
open Spike.Lib.A64.Flow.HelloM (wcR wcF wcJ0)
open Spike.Lib.A64.Flow.HelloWc (wXA)
open Spike.Lib.A64.WakePh.MainGlue (FS JS)
open Spike.Lib.A64.KeepTP (TP)
open Spike.Lib.A64.Alloc (Call)
open Spike.Lib.A64.HelloPh.StartGlue (X0WH)
open Spike.Lib.A64.HelloPh.StartWcS (WS rdJH)
open Spike.Lib.A64.HelloPh.StartH0G (helloD helloLsw)
open Spike.Lib.A64.HelloPh.StartH0U (msUH)
open Spike.Lib.A64.HelloPh.StartH0H1 (RdLandH)
open Spike.Lib.A64.HelloPh.HabCtlA (HabCtlHA wc_heapAb_segWSHA wc_heapAbStubKHA habCtlHA_jr1L)
open Spike.Lib.A64.HelloPh.HAbStub (x0WH_abort)
open Spike.Lib.A64.HelloPh.MainGlueS (MainWcPS)
open Spike.Lib.A64.HelloPh.Level1 (LandF JpL JpT)
open Spike.Lib.A64.HelloPh.Level1I (W1R XR)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.WakeLoadT (L0T ls0T)
open Spike.Lib.A64.HelloPh.C0S (c0S)
open Spike.Lib.HelloMainPreSrc (newTerm)
open Spike.Lib.HelloSrc (helloSrc)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

/-! ## The heap abort at `wXA` closes -/

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw i

set_option hygiene false in
local notation "RS" => Spike.Lib.A64.Rt.rS0 (Ly)

set_option hygiene false in
/-- The memory side at the start's labels, the entry's marks. -/
local notation "MSf" => fun fs => Spike.Lib.A64ConsumerA.msOfA (Ly).Λ
  ((Scc.Sem.A64.target (Scc.Sem.A64.kernel 2) E).marks asm (Ly).Λ) rd G own
  (Spike.Lib.WakeOD.arW hpw i) I LB ls fs

/-- **The heap-abort exit at `wXA` closes** (`StartH0CL.hello_hab_closedL`'s proof at `HabCtlA`'s stub): from
`wc_main`'s `wXA` exit at the frames `[]` below the caller `m0`, `σC`, a segment inside `W0` at the labels `LB`,
under the take move, with no exit, given `HabCtlHA` at `wc_main`'s region `wcR` and frame condition `wcF`. -/
theorem hello_hab_closedLA {LB : Lbl} {E : Scc.Sem.Entry} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
    {own : Spike.Lib.A64ConsumerS.OwnS} {I : Spike.Lib.A64ConsumerS.InvS} {ls : Lsize}
    {Ctx : FragS isaLSE2} {ls0 : Lsize} {frM : TermRun.Frame} {t : UInt64}
    {m0 : MachineData} {σC : FAS} {Jr1 : FAS → Spike.Lib.Ctl → Prop}
    (hpa : textProgram asm = .ok o.prog)
    (hhp : textProgram asm = .ok SccCode.helloProg)
    (hlo0 : Λ0.code.lo = lo)
    /- the controls' facts at `wXA` (`HabCtlA.habCtlHA_jr1L` at level 1) -/
    (hhabctl : ∀ v m1 σ1, HabCtlHA ((MSf) []) (Ly).lab helloSrc (Ly).Λ LB (Spike.Lib.WakeOD.arW hpw i)
      [] (wcJ0 (mWC (Ly).lab σC Jr1).J σ1) (wcR (swR v (-helloLsw) 0) helloD)
      (wcF (swR v (-helloLsw) 0) helloD (FS (Ly) RS helloLsw 0#64 v) m1 σ1)) :
    SegWS (WS (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) (Spike.Lib.WakeOD.arW hpw i) helloSrc DtW
        (Spike.Lib.A64.HelloPh.ClH (Ly)) Ctx LB ls0 frM
        (X0WH (Ly) ((Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL)))
      (Spike.Lib.A64.PhRec.K (Ly) RS) helloSrc LB (MSf)
      (Frag.at (fun s c => ∃ v m1 σ1,
        At (Ly).exe (Ly).endPc (wcR (swR v (-helloLsw) 0) helloD)
          (wcF (swR v (-helloLsw) 0) helloD (FS (Ly) RS helloLsw 0#64 v) m1 σ1)
          (wXA ((MSf) []) (Ly).lab (wcJ0 (mWC (Ly).lab σC Jr1).J σ1)) s c ∧ Spike.Lib.A64.KeepTP.TP t s) [])
      (fun _ _ _ => False) := by
  have hp : o.prog = SccCode.helloProg := Except.ok.inj (hpa.symm.trans hhp)
  have hprog : (Ly).prog = SccCode.helloProg := hp
  have hlo : (Ly).Λ.code.lo = lo := hlo0
  have hpL : textProgram asm = .ok (Ly).prog := by rw [hprog]; exact hhp
  have hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => Spike.Lib.PlaceW.hlab_ofPlaceW hpw i l x (by rw [hlo, hp]; exact h)
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
    Spike.Lib.PlaceW.abortLbl_of_placeW (Spike.Lib.PlaceW.link i hpw)
  have hwf := Spike.Lib.PlaceW.wf_link_of_placeW i hpw
  have hsub := Spike.Lib.A64.Rt.rS0_sub (Ly)
  have hok : (swR (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-helloLsw) 0).OK := by
    rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ (by decide) (by decide)
  have hab : ∀ s : State, s.st.2 = (Ly).lab "scc_rt_abort_heap_exit" → ((MSf) []).abortAt s := fun s hs => by
    obtain ⟨-, -, -, -, -, -, -, -, e9, -⟩ := Spike.Lib.A64.HelloPh.abH_labsH hlab
    refine ⟨.heap, 2168368, ?_, by rw [pcOf, hs, e9]; rfl⟩
    rw [Spike.Lib.A64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hpL]
    show codeOf (Ly).Λ.code.lo (Ly).prog ((Ly).Λ.abortLbl .heap) = _
    rw [hprog, hlo, hΛ, ← codeT_eq]; decide +kernel
  refine (SegWS.exists_pre (P := fun g : BitVec 64 × MachineData × FAS =>
      Frag.at (At (Ly).exe (Ly).endPc (wcR (swR g.1 (-helloLsw) 0) helloD)
        (wcF (swR g.1 (-helloLsw) 0) helloD (FS (Ly) RS helloLsw 0#64 g.1) g.2.1 g.2.2)
        (wXA ((MSf) []) (Ly).lab (wcJ0 (mWC (Ly).lab σC Jr1).J g.2.2))) [])
      fun ⟨v, m1, σ1⟩ => ?_).mono_pre
    fun _ _ _ ⟨⟨v, m1, σ1, h, _⟩, hf⟩ => ⟨⟨v, m1, σ1⟩, h, hf⟩
  by_cases hv : v = Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64
  case neg =>
    refine SegWS.empty fun _ _ _ h => ?_
    obtain ⟨⟨-, -, -, -, _, -, hF, -⟩, -⟩ := h
    exact hv hF.1.2.1.1
  subst hv
  have hF0 := Spike.Lib.A64.Rt.wordsNoneP_swFSL_fstable
    (a := Spike.Lib.A64.Flow.Ret0.limA (UInt64.ofBitVec (Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)))
    (v := Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64) hwf hsub hok (by decide) (by decide)
    (by rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rS0_subRD _ (by decide) (by decide))
    (by rw [Spike.Lib.A64.Rt.pinA_lab0]; exact Spike.Lib.A64.Rt.rt_hfit _)
    (by rw [Spike.Lib.A64.Rt.pinA_lab0, Spike.Lib.A64.Rt.stacksA_lab0]
        exact Spike.Lib.A64.Rt.rt_houtD _ (by decide) (by decide))
    (Spike.Lib.A64.Rt.fitS_of_sub _ hsub)
  obtain ⟨hR, hal, hF⟩ := Spike.Lib.A64.Flow.HelloM.wcR_ok (D := helloD) (by decide) (by decide) hok
    (by rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_h16 _) hF0
    (by show (-helloLsw : Int) ≤ -80 - helloD; decide) (by show (0 : Int) ≤ 0; decide) m1 σ1
  exact wc_heapAb_segWSHA hF hR hal (by show (-helloD : Int) ≤ -352; decide)
    (by show (0 : Int) ≤ 0; decide) rfl
    (wc_heapAbStubKHA hprog hlo hlab _ hΛ hF hR hal (by show (-helloD : Int) ≤ -352; decide)
      (by show (0 : Int) ≤ 0; decide) rfl (.inl rfl) (fun _ h => h.2)
      (hhabctl _ m1 σ1) hab (x0WH_abort hlab rfl)) _

end Place

/-! ## The landing segment -/

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (rd : TermRun.Word → Prop) (I : Spike.Lib.A64ConsumerS.InvS) (ls : Lsize)

set_option hygiene false in
local notation "IH" => Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw IH

set_option hygiene false in
local notation "AR" => Spike.Lib.WakeOD.arW hpw IH

set_option hygiene false in
local notation "NT" => Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab

set_option hygiene false in
local notation "RS" => Spike.Lib.A64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
local notation "AX" => (Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL

set_option hygiene false in
local notation "FR" => Spike.Lib.HelloRdCf.frH c0S.env

set_option hygiene false in
local notation "KR" => Spike.Lib.A64.PhRec.K (Ly) RS

set_option hygiene false in
/-- main's thread pointer. -/
local notation "TV" => UInt64.ofBitVec (Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The first stack's top (the start's `v`). -/
local notation "TOP" => Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
local notation "J'" => rdJH (Ly).lab (JS (Ly) 0#64 c0S)

set_option hygiene false in
/-- Level 0's memory sides (the landing's). -/
local notation "MSU" => msUH (asm := asm) hpw i0 E rd I ls

set_option hygiene false in
/-- The level's memory sides after rodata's allocation of `l` at `b`, `n` words, at the frames `fs`. -/
local notation "MS1" => fun (l : WeakMem.AllocLabel) (b n : Nat) (fs : List TermRun.Frame) =>
  Spike.Lib.A64ConsumerA.msOfA (Ly).Λ
    ((Scc.Sem.A64.target (Scc.Sem.A64.kernel 2) E).marks asm (Ly).Λ) rd
    (Spike.Lib.HelloGOf2H.gWH hpw IH (Spike.Lib.WakeHG.cTW hpw IH))
    (fun s _ => Spike.Lib.A64.HelloPh.ownGH (Ly) NT s)
    (AR) I (Spike.Lib.A64ConsumerA.upd (LB) l b) (Spike.Lib.A64ConsumerA.updN (ls0T ls) l n) fs

set_option maxHeartbeats 1600000 in
/-- **Level 1's landing segment, the heap abort at `wXA`** (`Level1I.hB_land`'s proof through
`Level1.land_segWSLA` and `hello_hab_closedLA`; module doc): from rodata's landing `RdLandH` at `[FR]`, inside
`W1R ∧ XR` under `TakeCKS`, with no exit. The abort's controls are `HabCtlA.habCtlHA_jr1L`'s at the caller's
slot `-80` (the case split's `hs`), `l` fresh (`hl`) and `hz`. -/
theorem hB_landA {J1 : FAS → FAS → Spike.Lib.Ctl → Prop}
    (hpa : textProgram asm = .ok o.prog)
    (hhp : textProgram asm = .ok SccCode.helloProg)
    (hlo0 : Λ0.code.lo = lo)
    /- the certificate table's `z` at `newTerm` (at the root's `ImmsMe.i0M`: `HabCtlA.hz_i0M`) -/
    (hz : i0 newTerm "z" 0 = some 0)
    /- the landing's caller holds main's TCB at its slot `-80` (`slot80_rdJ` at `J1 := mRdJ0 J'`) -/
    (hJ1 : ∀ σC σ c, J1 σC σ c → σC.slot (-80) = Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)
    /- `MainWcPS` at the level: `wc_rodata`'s rest from `.sp0` at `JpT (JpL …) TV` and `wc_main` to its box
    allocation, at the first stack's top -/
    (hP : ∀ l b n m0 σC, (LB) l = none → AllocLand (AR).heap (AR).cells b n →
      σC.slot (-80) = Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64 →
      ∃ Jp' Jx1 J2 J2' J3 J4 J5 Jr : FAS → Spike.Lib.Ctl → Prop,
      MainWcPS (W1R (asm := asm) hpw i0 E rd ls l b n) (KR) helloSrc (Spike.Lib.A64ConsumerA.upd (LB) l b) ((MS1) l b n)
        (Ly).exe (Ly).endPc (swR (TOP) (-helloLsw) 0) helloD (FS (Ly) (RS) helloLsw 0#64 (TOP)) (FR) m0 σC
        (JpT (JpL (R := swR (TOP) (-helloLsw) 0) ((MSU) [FR]) (Ly).lab (mRdJ0 (J') σC) (J1 σC) l b n) (TV))
        Jp' Jx1 J2 J2' J3 J4 J5 Jr (Spike.Lib.A64.HelloPh.Land.Jr1LH hpw i0 l b) (TV))
    /- the box allocation's words free at `FS` (`Level1M.hmem0_level1`) -/
    (hmem0 : ∀ l b n, ∀ q : Call, q.OKB ((MS1) l b n []) (Ly).lab → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ((MS1) l b n []).ctr ∨ ∃ o, o + ((MS1) l b n []).units q.n q.τ ≤ ((MS1) l b n []).cells ∧
        a.toNat = q.hdrAt ((MS1) l b n []) o) →
      ∀ m, FS (Ly) (RS) helloLsw 0#64 (TOP) m → Mem.loadInt m.dmem a 8 = none) :
    ∀ l b n, (LB) l = none → AllocLand (AR).heap (AR).cells b n →
      SegWS (fun s c fs => W1R (asm := asm) hpw i0 E rd ls l b n s c fs ∧ XR hpw i0 l b n s c fs)
        (TakeCKS (AX) (Spike.Lib.A64.HelloPh.ClH (Ly))) helloSrc (Spike.Lib.A64ConsumerA.upd (LB) l b)
        ((MS1) l b n) (Frag.at (RdLandH (asm := asm) hpw i0 E rd I ls J1 l b n) [FR]) (fun _ _ _ => False) := by
  intro l b n hl hb
  have hp : o.prog = SccCode.helloProg := Except.ok.inj (hpa.symm.trans hhp)
  have hprog : (Ly).prog = SccCode.helloProg := hp
  have hpS : Lays (Ly).exe SccCode.helloProg (Ly).pfx := hprog ▸ (Ly).lays
  have hendS : (Ly).endPc = endOf (Ly).exe SccCode.helloProg (Ly).pfx := by
    show endOf (Ly).exe (Ly).prog (Ly).pfx = _; rw [hprog]
  obtain ⟨hok, hal, hF⟩ := Spike.Lib.A64.HelloPh.Land.fstable_FS hpw i0
  refine (((SegWS.exists_pre (P := fun g : BitVec 64 × MachineData × FAS =>
      Frag.at (fun s c => LandF ((MSU) [FR]) (Ly).exe (Ly).endPc (swR g.1 (-helloLsw) 0)
        (FS (Ly) (RS) helloLsw 0#64 g.1) (mRdJ0 (J') g.2.2) (J1 g.2.2) g.2.1 g.2.2 l b n s c ∧ TP (TV) s) [FR])
      fun ⟨v, m0, σC⟩ => ?_).mono_K fun s c fs hW s' =>
        Spike.Lib.A64.HelloPh.StartH0B.takeCKS_iffH hpw IH hW.2.1).mono_W
      fun s c fs h => ⟨h, h.2.1⟩).mono_pre
    fun s c fs ⟨⟨v, m0, σC, q, F', h1, h2, hA, _, ht⟩, hfs⟩ => ⟨(v, m0, σC), ⟨⟨q, F', h1, h2, hA⟩, ht⟩, hfs⟩
  by_cases hv : v = TOP
  case neg =>
    refine SegWS.empty fun s c fs h => ?_
    obtain ⟨⟨⟨q, F', h1, -, -, -, -, -, σ, -, hF', -⟩, -⟩, -⟩ := h
    exact hv (h1 _ hF').1.2.1.1
  subst hv
  by_cases hs : σC.slot (-80) = Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64
  case neg =>
    refine SegWS.empty fun s c fs h => ?_
    obtain ⟨⟨⟨q, F', -, h2, -, -, -, -, σ, -, hF', -⟩, -⟩, -⟩ := h
    obtain ⟨mC, σ', c', -, ⟨⟨σe, hJe, -⟩, -⟩, -⟩ := h2 _ hF'
    exact hs (hJ1 _ _ _ hJe)
  have hC := hello_hab_closedLA hpw IH (E := E) (rd := rd) (I := I)
    (G := Spike.Lib.HelloGOf2H.gWH hpw IH (Spike.Lib.WakeHG.cTW hpw IH))
    (own := fun s _ => Spike.Lib.A64.HelloPh.ownGH (Ly) NT s) (ls := Spike.Lib.A64ConsumerA.updN (ls0T ls) l n)
    (Ctx := Spike.Lib.A64.HelloPh.Land.CtxR1H (asm := asm) hpw i0 E rd ls l b n)
    (ls0 := Spike.Lib.A64ConsumerA.updN (ls0T ls) l n) (frM := FR) (t := TV) (m0 := m0) (σC := σC)
    (Jr1 := Spike.Lib.A64.HelloPh.Land.Jr1LH hpw i0 l b) hpa hhp hlo0
    fun _ _ _ => habCtlHA_jr1L hpw i0 hl hs hz rfl rfl rfl
      (show (-helloD : Int) ≤ -304 by decide) (show (0 : Int) ≤ 0 by decide)
  obtain ⟨Jp', Jx1, J2, J2', J3, J4, J5, Jr, hPv⟩ := hP l b n m0 σC hl hb hs
  refine (Spike.Lib.A64.HelloPh.Level1.land_segWSLA rfl rfl hpS hendS (D := helloD) (by decide) (by decide) hF hok
    hal (show (-helloLsw : Int) ≤ -288 by decide) (show (-helloLsw : Int) ≤ -80 - helloD by decide)
    (show (0 : Int) ≤ 0 by decide) rfl hPv (hmem0 l b n)).seq ?_
  exact hC.mono_pre fun s c fs ⟨⟨m1, σ1, h, ht⟩, hfs⟩ => ⟨⟨_, m1, σ1, h, ht⟩, hfs⟩

end Spike.Lib.A64.HelloPh.Level1HA

/-- info: 'Spike.Lib.A64.HelloPh.Level1HA.hello_hab_closedLA' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Level1HA.hello_hab_closedLA

/-- info: 'Spike.Lib.A64.HelloPh.Level1HA.hB_landA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Level1HA.hB_landA
