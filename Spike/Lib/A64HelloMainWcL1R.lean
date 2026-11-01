/-
**`MainWcPS.hW` at `Level1I`'s choices** (AArch64; `Level1I.hP`'s first field, stage 2): `wc_rodata`'s rest from
`.sp0` (`MainPostSWH.rd`, `MainWcL1W.rdPostW_L1`) and `scc_rt_main`'s `.sp0` block (`MainPostSWH.sp0`,
`MainWcL1S.sp0_L1`) inside the level `W1R` at the root's layout, the level's labels `upd LB l b` at a fresh label
`l` (`hl`), `c0S`'s environment.

- `rdPostW_void`, `rdPostW_of_inh`: `RdPostW` at an uninhabited `.sp0` invariant is inside any predicate, so its
  premises are asked only at an inhabited one.
- `jpL_land`: a landing image at `.sp0` below `rdJH lab J` fixes the landing: `AllocLand` of `b`, two words, and
  a caller's state at `mNC lab J` (the frame's premise `HrdS.frP_mNC`'s `hJC`).
- `inArL_jX1`, `inArL_jX3`: `XchgWr.nodeW_wrC_rdX1`/`rdX2`'s `hin` at `RdSrcL1`'s invariants and a landing.
- `hW_L1`: `MainPostSWH` at `W1R … l b n`, the region `swR TOP (-helloLsw) 0`, the start's `FS`, `.sp0`'s invariant
  `JpT (JpL … (mRdJ0 J' σC) (mRdJ0 J' σC) l b n) TV`, `RdSrcL1`'s invariants and `wc_main`'s entry at
  `JrT (JrRL (upd LB l b) c0S.env l) TV`. Premises: the certificate's (`hpa`, `hhp`, `hlo0`, `hc`, `hA13`), the
  immediates (`hI`, `himm`), `hl`.
- `hW_L1M`: `hW_L1` at the root's table `ImmsMe.i0M Λ0` (`hI`, `himm` by `ImmsMe.rdImms_iRdM`/`hmeC_iRdM`).
-/
import Spike.Lib.A64HelloMainWcL1B
import Spike.Lib.A64HelloMainWcL1S
import Spike.Lib.A64HelloHrdR
import Spike.Lib.A64HelloXchgWr

namespace Spike.Lib.A64.HelloPh.MainWcL1R

variable {asm : String}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry ValRep lrange Range)
open Scc.Sem.A64 (textProgram)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib (MemSide Region Ctl FragS Frag)
open Spike.Lib.A64.Flow (swR BlkW NodeW ND)
open Spike.Lib.A64.Flow.HelloRd (RdPostW rN)
open Spike.Lib.A64.Flow.Hello1 (AG mF mR mRdJ0 mNC)
open Spike.Lib.A64.Flow.HelloM (MainPostSWH JrT)
open Spike.Lib.A64.Flow.HelloJr1 (JrRL)
open Spike.Lib.A64.Alloc (Ea)
open Spike.Lib.A64.HelloPh.Level1 (JpL JpT)
open Spike.Lib.A64.HelloPh.StartWcS (rdJH)
open Spike.Lib.A64.WakePh.MainGlue (FS JS)
open Spike.Lib.A64.WakePh (lo)
open Spike.Lib.A64.HelloPh.StartH0G (helloLsw)
open Spike.Lib.A64.HelloPh.StartH0U (msUH)
open Spike.Lib.A64.HelloPh.C0S (c0S)
open Spike.Lib.A64.HelloPh.RdSrcL1 (RB jP' jX1 jC2 jC2' jX3 jC4 jRet)
open Spike.Lib.A64.HelloPh.RdPlS (RdImms)
open Spike.Lib.A64.HelloPh.XchgWr (InArL)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.WakeLoadT (L0T ls0T tcb0)
open Spike.Lib.HelloRodataSrc (rdCN)
open Spike.Lib.Hello1RodataSrc (τ8)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

/-! ## Uninhabited invariants -/

section Void

variable {W : Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable}
  {endPc : Int64} {R : Region} {F : MachineData → Prop} {Jp Jp' J1 J2 J2' J3 J4 J5 : FAS → Ctl → Prop}

/-- **`wc_rodata` from the allocator's return at an uninhabited `.sp0` invariant** is inside any predicate: every
node's invariant asks for a state of `Jp`. -/
theorem rdPostW_void (hn : ∀ σ c, ¬ Jp σ c) : RdPostW W K exe endPc R F Jp Jp' J1 J2 J2' J3 J4 J5 := by
  have hb : ∀ {n : ND} {blk : List Directive}, (∀ σ c, ¬ n.J σ c) → BlkW W K exe endPc R F n blk :=
    fun h _ σ c _ _ _ _ _ _ hJ => absurd hJ (h σ c)
  have hd : ∀ {n : ND}, (∀ σ c, ¬ n.J σ c) → NodeW W K exe endPc R F n := by
    intro n h s c hA
    obtain ⟨-, -, -, -, σ, -, -, hJ⟩ := hA
    exact absurd hJ (h σ c)
  refine ⟨hb hn, hd ?_, hb ?_, hd ?_, hb ?_, hd ?_, hb ?_, hd ?_, hd ?_, hb ?_⟩ <;>
    rintro σ c ⟨σ0, ⟨c0, h⟩, -⟩ <;> exact hn σ0 c0 h

/-- **`RdPostW`'s premises asked only at an inhabited `.sp0` invariant** (`rdPostW_void` otherwise). -/
theorem rdPostW_of_inh (h : (∃ σ c, Jp σ c) → RdPostW W K exe endPc R F Jp Jp' J1 J2 J2' J3 J4 J5) :
    RdPostW W K exe endPc R F Jp Jp' J1 J2 J2' J3 J4 J5 := by
  by_cases hi : ∃ σ c, Jp σ c
  · exact h hi
  · exact rdPostW_void fun σ c hj => hi ⟨σ, c, hj⟩

end Void

/-! ## The landing at `.sp0` -/

/-- **A landing image at `.sp0` below `rdJH lab J` fixes the landing** (the memory side's units `3` and offset
`8` of rodata's call, `hu`, `hof`): `b`'s block of `n` words inside the cells, `n = 2`, and a caller's state at
`mNC lab J`. -/
theorem jpL_land {R : Region} {ms₀ : MemSide isaLSE2} {lab : Label → Int64} {J0 J : FAS → Ctl → Prop}
    {σC : FAS} {l : WeakMem.AllocLabel} {b n : Nat} {σ : FAS} {c : Ctl}
    (hu : ms₀.units 2 τ8 = 3) (hof : ms₀.off 2 τ8 = 8)
    (h : JpL (R := R) ms₀ lab J0 (mRdJ0 (rdJH lab J) σC) l b n σ c) :
    AllocLand ms₀.heap ms₀.cells b n ∧ n = 2 ∧ ∃ c', (mNC lab J).J σC c' := by
  obtain ⟨q, σx, σ', c0, ⟨ini, old, _, _, hb, hle, _, _, _, us, hus, hw⟩, ⟨⟨σe, ⟨_, hc0, c', hN⟩, _, _⟩, _⟩,
    ⟨hq0, _⟩, _⟩ := h
  have hq : q.1.c0 = rdCN := hq0.symm.trans hc0
  obtain ⟨-, hτ, -, hn⟩ := Spike.Lib.A64.HelloPh.MainWcL1B.q_rdCN q hq
  rw [hn, hτ] at hb hle
  rw [hn] at hw
  rw [hτ] at hus
  have hw1 : TermRun.nWords us = 1 := by
    obtain ⟨us', e1, e2⟩ : ∃ us', TermRun.accs (TermRun.close [] τ8) = some us' ∧ TermRun.nWords us' = 1 :=
      ⟨_, rfl, rfl⟩
    rw [e1] at hus
    cases hus
    exact e2
  rw [hu] at hle
  rw [hof] at hb
  rw [hw1] at hw
  exact ⟨⟨by omega, by omega, by omega⟩, by omega, c', hN⟩

/-- **`nodeW_wrC_rdX1`'s `hin` at `jX1`**: the buffer's first word is in `l`'s range at `b`, inside the arena. -/
theorem inArL_jX1 {ar : Spike.Lib.Arena} {L0 : Lbl} {ls0 : Lsize} {l : WeakMem.AllocLabel} {b n : Nat}
    (hb : AllocLand ar.heap ar.cells b n) (hn : n = 2) :
    ∀ σ0 c, jX1 (Spike.Lib.A64ConsumerA.upd L0 l b) l σ0 c →
      InArL ar (Spike.Lib.A64ConsumerA.upd L0 l b) (Spike.Lib.A64ConsumerA.updN ls0 l n)
        (Spike.Lib.A64.Flow.rAddr σ0.regs .X0 0).toNat := by
  rintro σ0 c ⟨hB, -⟩
  have hx : σ0.regs.X0.toBitVec.toNat = b := by
    have := hB.1; simp only [Spike.Lib.A64ConsumerA.upd, ite_true, Option.some.injEq] at this; omega
  refine ⟨l, b, by simp [Spike.Lib.A64ConsumerA.upd], ⟨hb.1, by simpa [Spike.Lib.A64ConsumerA.updN] using hb.2.1⟩,
    ?_⟩
  rw [Spike.Lib.A64.HelloPh.RdSrcL1.rAddr0 hB]
  simp only [lrange, Range.contains, Spike.Lib.A64ConsumerA.updN, ite_true]
  omega

/-- **`nodeW_wrC_rdX2`'s `hin` at `jX3`**: the buffer's second word is in `l`'s range at `b`, inside the arena. -/
theorem inArL_jX3 {ar : Spike.Lib.Arena} {L0 : Lbl} {ls0 : Lsize} {l : WeakMem.AllocLabel} {b n : Nat}
    (hb : AllocLand ar.heap ar.cells b n) (hn : n = 2) :
    ∀ σ0 c, jX3 (Spike.Lib.A64ConsumerA.upd L0 l b) l σ0 c →
      InArL ar (Spike.Lib.A64ConsumerA.upd L0 l b) (Spike.Lib.A64ConsumerA.updN ls0 l n)
        (Spike.Lib.A64.Flow.rAddr σ0.regs .X0 8).toNat := by
  rintro σ0 c ⟨hB, -⟩
  have hx : σ0.regs.X0.toBitVec.toNat = b := by
    have := hB.1; simp only [Spike.Lib.A64ConsumerA.upd, ite_true, Option.some.injEq] at this; omega
  refine ⟨l, b, by simp [Spike.Lib.A64ConsumerA.upd], ⟨hb.1, by simpa [Spike.Lib.A64ConsumerA.updN] using hb.2.1⟩,
    ?_⟩
  rw [Spike.Lib.A64.HelloPh.RdSrcL1.rAddr8 hB]
  simp only [lrange, Range.contains, Spike.Lib.A64ConsumerA.updN, ite_true]
  omega

/-! ## At `Level1I`'s choices -/

section Root

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)
  {E : Entry} {rd : TermRun.Word → Prop} {I : Spike.Lib.A64ConsumerS.InvS} {ls : Lsize}

set_option hygiene false in
local notation "IH" => Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw IH

set_option hygiene false in
local notation "NT" => Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab

set_option hygiene false in
local notation "RS" => Spike.Lib.A64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
local notation "FR" => Spike.Lib.HelloRdCf.frH c0S.env

set_option hygiene false in
local notation "TOP" => Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
local notation "TV" => UInt64.ofBitVec (Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
local notation "J'" => rdJH (Ly).lab (JS (Ly) 0#64 c0S)

set_option hygiene false in
local notation "MSU" => msUH (asm := asm) hpw i0 E rd I ls [FR]

set_option hygiene false in
local notation "LBL" => Spike.Lib.A64ConsumerA.upd (LB) l b

set_option hygiene false in
local notation "RR" => swR (TOP) (-helloLsw) 0

/-- **`MainWcPS.hW` at `Level1I`'s choices** (module doc). -/
theorem hW_L1 (hpa : textProgram asm = .ok o.prog)
    (hhp : textProgram asm = .ok SccCode.helloProg) (hlo0 : Λ0.code.lo = lo)
    (hc : Spike.Lib.A64.Rt.CtrZ o) (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hI : RdImms (Ly).Λ) (himm : (Ly).Λ.imms Spike.Lib.SrcCalls.setupCont "me" 0 = some (tcb0 (Ly).Λ))
    {l : WeakMem.AllocLabel} {b n : Nat} {m0 : MachineData} {σC : FAS} (hl : (LB) l = none) :
    MainPostSWH (Spike.Lib.A64.HelloPh.Level1I.W1R (asm := asm) hpw i0 E rd ls l b n) (Spike.Lib.A64.PhRec.K (Ly) RS)
      (Ly).exe (Ly).endPc (RR) (FS (Ly) (RS) helloLsw 0#64 (TOP)) (FR) m0 σC
      (JpT (JpL (R := RR) (MSU) (Ly).lab (mRdJ0 (J') σC) (mRdJ0 (J') σC) l b n) (TV))
      (jP' (LBL) l) (jX1 (LBL) l) (jC2 (LBL) l) (jC2' (LBL) l) (jX3 (LBL) l) (jC4 (LBL) l) (jRet (LBL) l)
      (JrT (JrRL (LBL) c0S.env l) (TV) (RR)) := by
  have hp : o.prog = SccCode.helloProg := Except.ok.inj (hpa.symm.trans hhp)
  have hprog : (Ly).prog = SccCode.helloProg := hp
  have hlo : (Ly).Λ.code.lo = lo := hlo0
  have hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => Spike.Lib.PlaceW.hlab_ofPlaceW hpw IH l x (by rw [hlo, hp]; exact h)
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
    Spike.Lib.PlaceW.abortLbl_of_placeW (Spike.Lib.PlaceW.link IH hpw)
  have hsite := Spike.Lib.PlaceW.site_ofPlaceW hpw IH
  have hX0 := Spike.Lib.A64.HelloPh.StartGlue.x0WH_of_freeNH (L := Ly)
    (a := (Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL) hlab rfl
  have hcl := Spike.Lib.A64.HelloPh.ClH.cl (L := Ly)
  have har : (Spike.Lib.WakeOD.arW hpw IH).OK :=
    let h := Spike.Lib.A64.Rt.ArenaW.arOf_ok (Spike.Lib.PlaceW.link IH hpw) hc
    ⟨h.ctr_out, h.units, h.off, h.units_lt, h.cells_lt, h.ctr_lt⟩
  obtain ⟨hok, hal, -⟩ := Spike.Lib.A64.HelloPh.Land.fstable_FS hpw i0
  have hRlo : (RR).lo ≤ -288 := show (-helloLsw : Int) ≤ -288 by decide
  have hhi : (0 : Int) ≤ (RR).hi := show (0 : Int) ≤ 0 by decide
  have hbuf := Spike.Lib.A64.HelloPh.MainWcL1B.hbuf_L1 (asm := asm) hpw i0 (E := E) (rd := rd) (I := I) (ls := ls) hA13
    (l := l) (b := b) (n := n) (m0 := m0) (σC := σC)
  refine ⟨?_, Spike.Lib.A64.HelloPh.MainWcL1S.sp0_L1 (frM := FR) (rS := RS) hprog hlo hΛ hlab hsite hcl hX0
    hok hal (by omega) hhi (tm := .tid) rfl himm
    (Spike.Lib.A64.HelloPh.MainWcL1S.valRep_upd hl (Spike.Lib.WakeImmsW.valRep_me _))⟩
  refine rdPostW_of_inh fun hinh => ?_
  obtain ⟨σi, ci, hi⟩ := hinh
  obtain ⟨hAL, hn2, c', hN⟩ := jpL_land (ms₀ := MSU) rfl rfl hi.1
  have hAL' : AllocLand (Spike.Lib.WakeOD.arW hpw IH).heap (Spike.Lib.WakeOD.arW hpw IH).cells b n := hAL
  have hmem : ∀ i : Int64, (i = 0 ∨ i = 8) → ∀ σ0 c,
      JpT (JpL (R := RR) (MSU) (Ly).lab (mRdJ0 (J') σC) (mRdJ0 (J') σC) l b n) (TV) σ0 c →
      ∀ m, mF (RR) (FS (Ly) (RS) helloLsw 0#64 (TOP)) m0 σC m →
        Mem.loadInt m.dmem (Spike.Lib.A64.Flow.rAddr σ0.regs .X0 i) 8 = none :=
    fun i hi σ0 c h => (hbuf σ0 c h i hi).2.1
  have hP := Spike.Lib.A64.HelloPh.HrdS.frP_mNC (lbl := LBL) hok (by omega) hhi
    Spike.Lib.A64.HelloPh.HrdR.hme_c0S
    (fun σ c h => Spike.Lib.A64.HelloPh.MainWcL1S.valRep_upd hl
      (Spike.Lib.A64.HelloPh.HrdR.hJ_JS hpw i0 σ c h).2) ⟨c', hN⟩
  exact Spike.Lib.A64.HelloPh.MainWcL1W.rdPostW_L1 (rS := RS) hprog hlo hΛ hlab hsite hcl hX0 hok hal hRlo hhi
    (Spike.Lib.A64.HelloPh.RdJpL.jpT_rb Spike.Lib.A64.HelloPh.RdJpL.rdJH_rdCN) hbuf
    (fun σ0 c h => Spike.Lib.A64.HelloPh.MainWcL1W.hra_jpLW h.1) hI hP
    (Spike.Lib.A64.HelloPh.XchgWr.nodeW_wrC_rdX1 hprog hlo (NT) hsite har (hmem 0 (.inl rfl))
      (inArL_jX1 hAL' hn2))
    (Spike.Lib.A64.HelloPh.XchgWr.nodeW_wrC_rdX2 hprog hlo (NT) hsite har (hmem 8 (.inr rfl))
      (inArL_jX3 hAL' hn2))

/-- **`hW_L1` at the root's table `ImmsMe.i0M Λ0`**: the immediates by `ImmsMe.rdImms_iRdM` and `hmeC_iRdM`. -/
theorem hW_L1M (hpa : textProgram asm = .ok o.prog)
    (hhp : textProgram asm = .ok SccCode.helloProg) (hlo0 : Λ0.code.lo = lo)
    (hc : Spike.Lib.A64.Rt.CtrZ o)
    (hA13 : Scc.Cert.Spawn.A64.a13data (RuntimeLayout.ofPlaceW hpw (Spike.Lib.A64.HelloPh.ImmsMe.iRdM Λ0)).Λ
      o.prog o.secs = true)
    {l : WeakMem.AllocLabel} {b n : Nat} {m0 : MachineData} {σC : FAS}
    (hl : L0T (RuntimeLayout.ofPlaceW hpw (Spike.Lib.A64.HelloPh.ImmsMe.iRdM Λ0)).Λ l = none) :
    let i0 := Spike.Lib.A64.HelloPh.ImmsMe.i0M Λ0
    MainPostSWH (Spike.Lib.A64.HelloPh.Level1I.W1R (asm := asm) hpw i0 E rd ls l b n) (Spike.Lib.A64.PhRec.K (Ly) RS)
      (Ly).exe (Ly).endPc (RR) (FS (Ly) (RS) helloLsw 0#64 (TOP)) (FR) m0 σC
      (JpT (JpL (R := RR) (MSU) (Ly).lab (mRdJ0 (J') σC) (mRdJ0 (J') σC) l b n) (TV))
      (jP' (LBL) l) (jX1 (LBL) l) (jC2 (LBL) l) (jC2' (LBL) l) (jX3 (LBL) l) (jC4 (LBL) l) (jRet (LBL) l)
      (JrT (JrRL (LBL) c0S.env l) (TV) (RR)) :=
  have h := Spike.Lib.A64.HelloPh.ImmsMe.rdImms_iRdM hpw
  hW_L1 hpw _ hpa hhp hlo0 hc hA13 ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
    (Spike.Lib.A64.HelloPh.ImmsMe.hmeC_iRdM hpw) hl

end Root

end Spike.Lib.A64.HelloPh.MainWcL1R

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1R.rdPostW_void' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1R.rdPostW_void

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1R.rdPostW_of_inh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1R.rdPostW_of_inh

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1R.jpL_land' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1R.jpL_land

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1R.inArL_jX1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1R.inArL_jX1

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1R.inArL_jX3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1R.inArL_jX3

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1R.hW_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1R.hW_L1

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1R.hW_L1M' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1R.hW_L1M
