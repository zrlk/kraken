/-
**`MainWcPS.hW` at `Level1I`'s choices at `ownGHXW`** (x86-64 only; the `ownGHXW` instance of
`Spike/Lib/X64HelloMainWcL1R.lean`'s `hW_L1`): `wc_rodata`'s rest from `.x15` (`MainPostSWH.rd`,
`RdWfSFX.rdPostW_WSHX`) and `scc_rt_main`'s `.x2` block (`MainPostSWH.sp0`, `RdWfSFX.mB1W_WSHX`) inside the level
`W1Rg (ownGHXW Ly ntA)` at the root's layout, the level's labels `upd LB l b` at a fresh label `l` (`hl`),
`c0S`'s environment, the landing's memory side `msUHg (ownGHXW Ly ntA)`.

- `ne_tcbM_q`: the two buffer words at `MainWcL1B.CellX0Q` are off `tcbM` (inside `.heap`,
  `WakePh.ne_tcbM_of_heap`).
- `hbuf_L1X`, `hbufM_L1X`: `rdPostW_WSHX`'s `hbuf` and `hbufM` at `hW_L1X`'s `.x15` invariant (`MainWcL1B.hbuf_L1`'s
  proof at `msUHg (ownGHXW Ly ntA)`).
- `hW_L1X`: `MainPostSWH` at `W1Rg (ownGHXW Ly ntA) … l b n`, with `MainWcL1R.hW_L1`'s invariants at the memory
  side `msUHg (ownGHXW Ly ntA) … [FR]`. Premises: `hW_L1`'s; `ownGHXW`'s separation (`StartPlaceLy.wsep_W`,
  `tcbWH_notG_W`) from `hA13`, the frames' bands on the pool from `HrdRootX.bandRS`, the buffer off `tcbM` from
  `hbufM_L1X`.
- `hbp_L1X`, `hsl_L1X`: `MainWcPS.hbp`, `hsl` at `hW_L1X`'s `.x15` invariant (`MainWcL1R.hbp_L1`/`hsl_L1`'s proofs).

## Differences from the AArch64 version

AArch64 has no counterpart: main owns no TCB word there. Against `X64HelloMainWcL1R.hW_L1`: the level is
`W1Rg (ownGHXW Ly ntA)` (not `W1R`, at `ownGH`) and the landing's memory side `msUHg (ownGHXW Ly ntA)` (not
`msUH`); `rdPostW_WSHX`/`mB1W_WSHX`'s extra premises (`hsep`, `ha`, `hW`, `hb`, `hbM`, `hbufM`) are discharged
inside, from `hA13` and the layout, so the premises are `hW_L1`'s. `MainWcL1W.rdPostW_L1` and
`MainWcL1S.sp0_L1` are at `WSHF` (`ownGH`), so their bodies are inlined here at `WSHFg (ownGHXW …)`.
-/
import Spike.Lib.X64HelloMainWcL1R
import Spike.Lib.X64HelloRdPostWfSFX
import Spike.Lib.X64HelloHrdRootX

namespace Spike.Lib.X64.HelloPh.MainWcL1RX

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Entry)
open Scc.Sem.X64 (codeLabel)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lsize)
open Spike.Lib (MemSide Region PlaceWX)
open Spike.Lib.X64 (bAddr)
open Spike.Lib.X64.HelloPh (lo ownGHXW)
open Spike.Lib.X64.HelloPh.WcW (BoxOkH)
open Spike.Lib.X64.WakePh (tcbM BandOnP)
open Spike.Lib.X64.Flow.HelloRd (J4P)
open Spike.Lib.X64.Flow.Hello1 (mR mF mRdJ0)
open Spike.Lib.X64.Flow.HelloM (MainPostSWH JrT)
open Spike.Lib.X64.Flow.HelloJr1 (JrRL)
open Spike.Lib.X64.Flow.Ret0 (tpOf)
open Spike.Lib.X64.HelloPh.Level1 (JpL JpT)
open Spike.Lib.X64.HelloPh.StartWcS (rdJH)
open Spike.Lib.X64.WakePh.MainGlue (FS JS RS tcbS topS)
open Spike.Lib.X64.HelloPh.StartH0G (helloLsw)
open Spike.Lib.X64.HelloPh.StartH0U (msUHg)
open Spike.Lib.X64.HelloPh.C0S (c0S)
open Spike.Lib.X64.HelloPh.RdSrcL1 (jP' jX1 jC2 jC2' jX3 jC4 jC5)
open Spike.Lib.X64.HelloPh.RdPlS (RdImms)
open Spike.Lib.X64.HelloPh.MainWcL1B (CellX0Q)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.X64WakeLoadT (L0T ls0T tcb0)
open Spike.Lib.Hello1RodataSrc (τ8)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.X64.AS

/-! ## The buffer off `tcbM` -/

/-- **The two buffer words at `CellX0Q` are off `tcbM`**: they lie inside the cells, which lie inside `.heap`
(`hH`, `hHi`), disjoint from `tcbM`'s byte (`WakePh.ne_tcbM_of_heap`). -/
theorem ne_tcbM_q {L : RuntimeLayout} {ms : MemSide isa} {lab : Label → Int64} (hwf : L.Λ.WF)
    (hH : L.Λ.heap.lo ≤ ms.heap) (hHi : ms.heap + 16 * ms.cells ≤ L.Λ.heap.lo + L.Λ.heap.size)
    {σ : FAS} (h : CellX0Q ms lab σ) :
    ∀ i : Int64, (i = 0 ∨ i = 8) → bAddr σ.regs .rax i ≠ tcbM L := by
  obtain ⟨q, old, hx, hle, ho'⟩ := h
  have hroom : ms.heap + 16 * ms.cells ≤ 2 ^ 64 := by
    have := q.2.room; have := q.2.cells; omega
  have key : ∀ j : Nat, (j = 0 ∨ j = 8) →
      BitVec.ofNat 64 (ms.heap + 16 * old + ms.off q.1.n q.1.τ + j) ≠ tcbM L := by
    intro j hj
    refine Spike.Lib.X64.WakePh.ne_tcbM_of_heap hwf (by omega) ?_
    unfold Scc.Sem.Range.contains; omega
  have hb : ∀ j : Nat, (j = 0 ∨ j = 8) → ∀ i : Int64, i.toInt = j →
      bAddr σ.regs .rax i = BitVec.ofNat 64 (ms.heap + 16 * old + ms.off q.1.n q.1.τ + j) := by
    intro j hj i hi
    apply BitVec.eq_of_toNat_eq
    have hx' : (σ.regs.get64 .rax).toNat = ms.heap + 16 * old + ms.off q.1.n q.1.τ := hx
    simp only [bAddr, hi, BitVec.toNat_add, BitVec.toNat_ofNat, hx']
    rcases hj with rfl | rfl <;> simp <;> omega
  rintro i (rfl | rfl)
  · rw [hb 0 (.inl rfl) 0 rfl]; exact key 0 (.inl rfl)
  · rw [hb 8 (.inr rfl) 8 rfl]; exact key 8 (.inr rfl)

/-! ## At `Level1I`'s choices -/

section Root

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)
  {E : Entry} {rd : TermRun.Word → Prop} {I : Spike.Lib.X64ConsumerS.InvS} {ls : Lsize}

set_option hygiene false in
local notation "IH" => Spike.Lib.X64.HelloImms.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw IH

set_option hygiene false in
local notation "NT" => Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab

set_option hygiene false in
/-- main's owned words at the root. -/
local notation "OX" => ownGHXW (Ly) (NT)

set_option hygiene false in
local notation "RS0" => Spike.Lib.X64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
local notation "FR" => Spike.Lib.X64HelloRdCf.frH c0S.env

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => topS (Ly) 0#64

set_option hygiene false in
/-- main's thread pointer. -/
local notation "TV" => tpOf (tcbS (Ly))

set_option hygiene false in
/-- `scc_rt_main`'s region at the first stack's top. -/
local notation "RR" => RS helloLsw (TOP)

set_option hygiene false in
/-- `wc_rodata`'s caller's entry invariant at `RR`. -/
local notation "J'" => rdJH (Ly).lab (RR) (JS (Ly) 0#64 c0S)

set_option hygiene false in
/-- The root's memory side under main's frame, owning `OX`. -/
local notation "MSUX" => msUHg (asm := asm) hpw i0 (OX) E rd I ls [FR]

set_option hygiene false in
local notation "LBL" => Spike.Lib.X64ConsumerA.upd (LB) l b

/-- **`rdPostW_WSHX`'s `hbuf` at `hW_L1X`'s `.x15` invariant** (`MainWcL1B.hbuf_L1` at `msUHg OX`): the two
buffer words are box cells. -/
theorem hbuf_L1X (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    {l : WeakMem.AllocLabel} {b n : Nat} {m0 : MachineData} {σC : FAS} :
    ∀ σ0 c, JpT (JpL (R := RR) (MSUX) (Ly).lab (mRdJ0 (J') σC) (mRdJ0 (J') σC) l b n) (TV) σ0 c →
      ∀ i : Int64, (i = 0 ∨ i = 8) →
        BoxOkH (Ly).Λ (Ly) (NT) (mF (RR) (FS (Ly) (RS0) helloLsw 0#64 (TOP)) m0 σC) (bAddr σ0.regs .rax i) := by
  intro σ0 c h
  have hpl := Spike.Lib.PlaceWX.link IH hpw
  have hsz : 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.size :=
    Spike.Lib.X64.Rt.ArenaW.PlaceWX.heapSize_of_placeWX hpl
  have hu : (MSUX).units 2 τ8 = 3 := rfl
  refine Spike.Lib.X64.HelloPh.MainWcL1B.boxOkH_q (fun m hm => hm.1.1.1.wn) (Nat.le_refl _) ?_
    (Spike.Lib.X64.HelloPh.HrdArena.offH_own hpw i0 hA13)
    (Spike.Lib.X64.HelloPh.MainWcL1B.cellX0Q_jpL Spike.Lib.X64.HelloPh.RdJpL.rdJH_rdCN hu h.1)
  show (Ly).Λ.heap.lo + 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.lo + (Ly).Λ.heap.size
  omega

/-- **`rdPostW_WSHX`'s `hbufM` at `hW_L1X`'s `.x15` invariant**: the two buffer words are off `tcbM`
(`ne_tcbM_q`). -/
theorem hbufM_L1X {l : WeakMem.AllocLabel} {b n : Nat} {σC : FAS} :
    ∀ σ0 c, JpT (JpL (R := RR) (MSUX) (Ly).lab (mRdJ0 (J') σC) (mRdJ0 (J') σC) l b n) (TV) σ0 c →
      ∀ i : Int64, (i = 0 ∨ i = 8) → bAddr σ0.regs .rax i ≠ tcbM (Ly) := by
  intro σ0 c h
  have hsz : 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.size :=
    Spike.Lib.X64.Rt.ArenaW.PlaceWX.heapSize_of_placeWX (Spike.Lib.PlaceWX.link IH hpw)
  have hu : (MSUX).units 2 τ8 = 3 := rfl
  refine ne_tcbM_q (Spike.Lib.PlaceWX.wf_link_of_placeWX IH hpw) (Nat.le_refl _) ?_
    (Spike.Lib.X64.HelloPh.MainWcL1B.cellX0Q_jpL Spike.Lib.X64.HelloPh.RdJpL.rdJH_rdCN hu h.1)
  show (Ly).Λ.heap.lo + 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.lo + (Ly).Λ.heap.size
  omega

set_option maxHeartbeats 800000 in
/-- **`MainWcPS.hW` at `Level1I`'s choices at `ownGHXW`** (module doc). -/
theorem hW_L1X (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells) (hlo0 : Λ0.code.lo = lo)
    (hc : Spike.Lib.X64.Rt.CtrZ o) (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hI : RdImms (Ly).Λ) (himm : (Ly).Λ.imms Spike.Lib.SrcCalls.setupCont "me" 0 = some (tcb0 (Ly).Λ))
    {l : WeakMem.AllocLabel} {b n : Nat} {m0 : MachineData} {σC : FAS} (hl : (LB) l = none) :
    MainPostSWH (Spike.Lib.X64.HelloPh.Level1I.W1Rg (asm := asm) hpw i0 E rd ls (OX) l b n)
      (Spike.Lib.X64.PhRec.K (Ly) (RS0)) (Ly).exe (Ly).endPc (RR) (FS (Ly) (RS0) helloLsw 0#64 (TOP)) (FR) m0 σC
      (JpT (JpL (R := RR) (MSUX) (Ly).lab (mRdJ0 (J') σC) (mRdJ0 (J') σC) l b n) (TV))
      (jP' (LBL) l) (jX1 (LBL) l) (jC2 (LBL) l) (jC2' (LBL) l) (jX3 (LBL) l) (J4P (jC4 (LBL) l) (jC5 (LBL) l))
      (JrT (JrRL (LBL) c0S.env l) (TV) (RR)) := by
  -- the layout's facts (as `hW_L1`)
  have hp : o.prog = SccCode.helloCells := Option.some.inj (hpa.symm.trans hhp)
  have hprog : (Ly).prog = SccCode.helloCells := hp
  have hlo : (Ly).Λ.code.lo = lo := hlo0
  have hlab : ∀ l x, codeLabel lo SccCode.helloCells l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => Spike.Lib.PlaceWX.hlab_ofPlaceWX hpw IH l x (by rw [hlo, hp]; exact h)
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
    Spike.Lib.PlaceWX.abortLbl_of_placeWX (Spike.Lib.PlaceWX.link IH hpw)
  have hsite := Spike.Lib.PlaceWX.site_ofPlaceWX hpw IH
  have hX0 := Spike.Lib.X64.HelloPh.StartGlue.x0WH_of_freeNH (L := Ly)
    (a := (Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL) hlab rfl
  have hcl := Spike.Lib.X64.HelloPh.ClH.cl (L := Ly)
  have har : (Spike.Lib.X64.WakeOD.arW hpw IH).OK :=
    let h := Spike.Lib.X64.Rt.ArenaW.arOf_ok (Spike.Lib.PlaceWX.link IH hpw) hc
    ⟨h.ctr_out, h.units, h.off, h.units_lt, h.cells_lt, h.ctr_lt⟩
  -- `ownGHXW`'s separation, from A13's data part (as `HrdRootX.hrd_RX`)
  have hs := Spike.Lib.X64.WakePh.StartPlaceLy.wsep_W hpw IH hA13
  have hsep : Spike.Lib.X64.PhRec.TcbSep (Ly) := hs.tcb
  have ha : tcbM (Ly) ≠ NT := hs.tcb_a 1 (by decide)
  have hW := Spike.Lib.X64.HelloPh.tcbWH_notG_W hpw IH hA13
  -- the region and its bands on the pool (as `HrdRootX.hrd_RX`)
  obtain ⟨hok0, hok, -⟩ := Spike.Lib.X64.HelloPh.Land.fstable_FS hpw i0
  have hRlo : (RR).lo ≤ -288 := by show (8 - helloLsw : Int) ≤ -288; decide
  have hhi : (8 : Int) ≤ (RR).hi := by show (8 : Int) ≤ 8; decide
  have hbM : BandOnP (Ly) (RR) (-288) 8 :=
    Spike.Lib.X64.HelloPh.HrdRootX.bandRS (show (8 - helloLsw : Int) ≤ -288 by decide)
      (show helloLsw < 16384 by decide) hok0
  have hb : BandOnP (Ly) (mR (RR)) (-208) 8 := fun k h1 h2 => by
    have e : (mR (RR)).addr k = (RR).addr (-80 + k) := Region.callee_addr _ (-80) (-208) 8 k
    rw [e]; exact hbM _ (by omega) (by omega)
  have hbuf := hbuf_L1X (asm := asm) hpw i0 (E := E) (rd := rd) (I := I) (ls := ls)
    hA13 (l := l) (b := b) (n := n) (m0 := m0) (σC := σC)
  have hbufM := hbufM_L1X (asm := asm) hpw i0 (E := E) (rd := rd) (I := I) (ls := ls)
    (l := l) (b := b) (n := n) (σC := σC)
  -- `scc_rt_main`'s `.x2` block (`MainWcL1S.sp0_L1`'s body at `ownGHXW`)
  refine ⟨?_, Spike.Lib.X64.HelloPh.RdWfSFX.mB1W_WSHX (fs := []) (frM := FR) (rS := RS0) hprog hlo hΛ hlab hsite
    hcl hX0 (.inl rfl) hsep ha hW hbM hok hRlo hhi
    (fun σ c ⟨⟨hc, _⟩, _⟩ => by
      rw [hc]
      exact ⟨fun _ => (Spike.Lib.X64HelloRdCf.cont_ctl _ none).1, (Spike.Lib.X64HelloRdCf.cont_ctl _ none).2⟩)
    (Spike.Lib.X64.HelloPh.MainWcL1S.hplB1_L1 (by omega) (by omega) (env := c0S.env) (tm := .tid)
      (mw := TermRun.cst (.loc ⟨Spike.Lib.X64WakeT1.mainTidLbl 2, 0⟩ 0)) rfl himm
      (Spike.Lib.X64.HelloPh.MainWcL1S.valRep_upd hl (Spike.Lib.X64.WakeImmsC0.valRep_me _)))⟩
  -- `wc_rodata`'s rest (`MainWcL1W.rdPostW_L1`'s body at `ownGHXW`)
  refine Spike.Lib.X64.HelloPh.MainWcL1R.rdPostW_of_inh fun hinh => ?_
  obtain ⟨σi, ci, hi⟩ := hinh
  obtain ⟨hAL, hn2, c', hN⟩ := Spike.Lib.X64.HelloPh.MainWcL1R.jpL_land (ms₀ := MSUX) rfl rfl hi.1
  have hAL' : AllocLand (Spike.Lib.X64.WakeOD.arW hpw IH).heap (Spike.Lib.X64.WakeOD.arW hpw IH).cells b n := hAL
  have hmem : ∀ i : Int64, (i = 0 ∨ i = 8) → ∀ σ0 c,
      JpT (JpL (R := RR) (MSUX) (Ly).lab (mRdJ0 (J') σC) (mRdJ0 (J') σC) l b n) (TV) σ0 c →
      ∀ m, mF (RR) (FS (Ly) (RS0) helloLsw 0#64 (TOP)) m0 σC m →
        Mem.loadInt m.dmem (bAddr σ0.regs .rax i) 8 = none :=
    fun i hi σ0 c h => (hbuf σ0 c h i hi).2.1
  have hP := Spike.Lib.X64.HelloPh.HrdS.frP_mNC (lbl := LBL) hok (by omega) (by omega)
    Spike.Lib.X64.HelloPh.HrdR.hme_c0S
    (fun σ c h => Spike.Lib.X64.HelloPh.MainWcL1S.valRep_upd hl
      (Spike.Lib.X64.HelloPh.HrdR.hJ_JS hpw i0 σ c h).2) ⟨c', hN⟩
  have hmR := (Spike.Lib.X64.Flow.Hello1.mR_ok (F := fun _ => True) hok (fun _ _ _ _ => trivial) hRlo hhi m0 σC).1
  have hC := Spike.Lib.X64.HelloPh.MainWcL1W.rd_ctl (lbl := LBL) (l := l)
    (Jp := JpT (JpL (R := RR) (MSUX) (Ly).lab (mRdJ0 (J') σC) (mRdJ0 (J') σC) l b n) (TV))
    (J4 := J4P (jC4 (LBL) l) (jC5 (LBL) l))
    (Spike.Lib.X64.HelloPh.RdJpL.jpT_rb Spike.Lib.X64.HelloPh.RdJpL.rdJH_rdCN)
    (fun σ0 c h => h.elim (fun ⟨hB, ini, wo0, wo1, e⟩ => ⟨hB, ini, wo0, wo1, .inl e⟩)
      fun ⟨hB, ini, wo0, wo1, e⟩ => ⟨hB, ini, wo0, wo1, .inr (.inl e)⟩)
  exact Spike.Lib.X64.HelloPh.RdWfSFX.rdPostW_WSHX (fs := [FR]) (frM := FR) (rS := RS0) hprog hlo hΛ hlab
    hsite hcl hX0 (.inr rfl) hsep ha hW hb hmR (by simp only [mR, Region.callee]; omega)
    (by simp only [mR, Region.callee]; omega) hbuf hbufM
    (fun σ0 c h => Spike.Lib.X64.HelloPh.MainWcL1W.hra_jpLW h.1)
    (fun σ0 c h => let ⟨_, _, _, ht⟩ := hC σ0 c h; Spike.Lib.X64HelloRdCf.hcf_frH ht)
    (Spike.Lib.X64.HelloPh.RdPlS.rdPostW_plS hI hP fun σ0 c h =>
      let ⟨hB, ini, hc, _⟩ := hC σ0 c h; ⟨l, ini, hB.1, hc⟩)
    (Spike.Lib.X64.HelloPh.XchgWr.nodeW_wrC_rdX1 hprog hlo (NT) hsite har (hmem 0 (.inl rfl))
      (Spike.Lib.X64.HelloPh.MainWcL1R.inArL_jX1 hAL' hn2))
    (Spike.Lib.X64.HelloPh.XchgWr.nodeW_wrC_rdX2 hprog hlo (NT) hsite har (hmem 8 (.inr rfl))
      (Spike.Lib.X64.HelloPh.MainWcL1R.inArL_jX3 hAL' hn2))

/-- **`MainWcPS.hbp` at `hW_L1X`'s `.x15` invariant**: `.x15`'s `%rbp` is `wc_rodata`'s saved-`%rbp` slot
(`Level1A.jpL_rbp`). -/
theorem hbp_L1X {l : WeakMem.AllocLabel} {b n : Nat} {σC : FAS} :
    ∀ σ0 c, JpT (JpL (R := RR) (MSUX) (Ly).lab (mRdJ0 (J') σC) (mRdJ0 (J') σC) l b n) (TV) σ0 c →
      σ0.regs.get64 .rbp = (mR (RR)).addr (-8) :=
  fun _ _ h => Spike.Lib.X64.HelloPh.Level1.jpL_rbp h.1

/-- **`MainWcPS.hsl` at `hW_L1X`'s `.x15` invariant**: `.x15`'s saved-`%rbp` cell is `scc_rt_main`'s saved-`%rbp`
address (`MainWcL1R.jpL_slot8`). -/
theorem hsl_L1X {l : WeakMem.AllocLabel} {b n : Nat} {σC : FAS} :
    ∀ σ0 c, JpT (JpL (R := RR) (MSUX) (Ly).lab (mRdJ0 (J') σC) (mRdJ0 (J') σC) l b n) (TV) σ0 c →
      σ0.slot (-8) = (RR).addr (-8) :=
  fun _ _ h => Spike.Lib.X64.HelloPh.MainWcL1R.jpL_slot8 h.1

end Root

end Spike.Lib.X64.HelloPh.MainWcL1RX

/-! ## Axiom guards -/

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1RX.ne_tcbM_q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1RX.ne_tcbM_q

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1RX.hbuf_L1X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1RX.hbuf_L1X

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1RX.hbufM_L1X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1RX.hbufM_L1X

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1RX.hW_L1X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1RX.hW_L1X

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1RX.hbp_L1X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1RX.hbp_L1X

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1RX.hsl_L1X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1RX.hsl_L1X
