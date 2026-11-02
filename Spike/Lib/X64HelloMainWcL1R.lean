/-
**`MainWcPS.hW` at `Level1I`'s choices** (x86-64; the twin of `Spike/Lib/A64HelloMainWcL1R.lean`): `wc_rodata`'s
rest from `.x15` (`MainPostSWH.rd`, `MainWcL1W.rdPostW_L1`) and `scc_rt_main`'s `.x2` block (`MainPostSWH.sp0`,
`MainWcL1S.sp0_L1`) inside the level `W1R` at the root's layout, the level's labels `upd LB l b` at a fresh label
`l` (`hl`), `c0S`'s environment.

- `rdPostW_void`, `rdPostW_of_inh`: `RdPostW` at an uninhabited `.x15` invariant is inside any predicate, so its
  premises are asked only at an inhabited one.
- `jpL_land`: a landing image at `.x15` below `rdJH lab R' J` fixes the landing: `AllocLand` of `b`, two words, and
  a caller's state at `mNC lab R' J` (the frame's premise `HrdS.frP_mNC`'s `hJC`).
- `jpL_slot8`: at a landing image below `rdJH lab R' J`, `.x15`'s saved-`%rbp` cell holds the caller's `%rbp`,
  `R'`'s saved-`%rbp` address.
- `inArL_jX1`, `inArL_jX3`: `XchgWr.nodeW_wrC_rdX1`/`rdX2`'s `hin` at `RdSrcL1`'s invariants and a landing.
- `hW_L1`: `MainPostSWH` at `W1R … l b n`, the region `RS helloLsw TOP`, the start's `FS`, `.x15`'s invariant
  `JpT (JpL … (mRdJ0 J' σC) (mRdJ0 J' σC) l b n) TV`, `RdSrcL1`'s invariants (the last block's `J4P jC4 jC5`) and
  `wc_main`'s entry at `JrT (JrRL (upd LB l b) c0S.env l) TV`. Premises: the certificate's (`hpa`, `hhp`, `hlo0`,
  `hc`, `hA13`), the immediates (`hI`, `himm`), `hl`.
- `hbp_L1`, `hsl_L1`: `MainWcPS.hbp`, `hsl` at `hW_L1`'s `.x15` invariant (`Level1A.jpL_rbp`, `jpL_slot8`).

## Differences from the AArch64 version

- `RdPostW` has seven invariants (AArch64 eight): the last block's is `J4P J4 J4x`, at `Level1I`'s choices
  `J4P (jC4 …) (jC5 …)` (the controls at the publication and past it; AArch64 `jC4`, then `jRet` as `J5`), so
  `rdPostW_void` has nine fields.
- `scc_rt_main`'s region is `MainGlue.RS helloLsw TOP` (AArch64 `swR TOP (-helloLsw) 0`), with `TOP` the first
  stack's top `topS Ly 0`; `wc_rodata`'s caller's invariant `rdJH` takes it, and `HrdS.frP_mNC` reads `mNC`'s
  `%rdi` (AArch64 `x0`, `mNC` without the region).
- The buffer's base is `%rax` (`bAddr σ.regs .rax i`, `RdSrcL1.bAddr0`/`bAddr8`; AArch64 `rAddr σ.regs .X0 i`).
- The thread pointer is `tpOf (tcbS Ly)` (AArch64 `pinA + 8`); `.x15`'s return address is `hra_jpLW`'s slot `0`.
- `MainWcPS` asks `.x15`'s `%rbp` and saved-`%rbp` cell (`hbp`, `hsl`), as `scc_rt_main` addresses its frame
  off `%rbp`: `jpL_slot8`, `hbp_L1`, `hsl_L1` are new.
- The loader's facts are the two parses `cellsOf asm` (AArch64 `textProgram`).
- Not twinned (unreachable from the AArch64 root, so twins only live constants): `hW_L1M` (`hW_L1` at the root's
  table `i0M Λ0`).
-/
import Spike.Lib.X64HelloMainWcL1B
import Spike.Lib.X64HelloMainWcL1S
import Spike.Lib.X64HelloHrdR
import Spike.Lib.X64HelloHrdS
import Spike.Lib.X64HelloXchgWr
import Spike.Lib.X64HelloRdJpL
import Spike.Lib.X64HelloRdSrcL1
import Spike.Lib.X64HelloLevel1T
import Spike.Lib.X64HelloLevel1A
import Spike.Lib.X64HelloStartGlue
import Spike.Lib.X64SiteOfPlaceW
import Spike.Lib.Rt.X64ArenaOfPlaceW

namespace Spike.Lib.X64.HelloPh.MainWcL1R

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Entry ValRep lrange Range)
open Scc.Sem.X64 (codeLabel)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib (MemSide Region Ctl FragS Frag PlaceWX)
open Spike.Lib.X64 (BlkW NodeW ND bAddr)
open Spike.Lib.X64.Flow.HelloRd (RdPostW rN J4P)
open Spike.Lib.X64.Flow.Hello1 (AG mF mR mRdJ0 mNC)
open Spike.Lib.X64.Flow.HelloM (MainPostSWH JrT)
open Spike.Lib.X64.Flow.HelloJr1 (JrRL)
open Spike.Lib.X64.Flow.Ret0 (tpOf)
open Spike.Lib.X64.Alloc (Ea)
open Spike.Lib.X64.HelloPh.Level1 (JpL JpT)
open Spike.Lib.X64.HelloPh.StartWcS (rdJH)
open Spike.Lib.X64.WakePh.MainGlue (FS JS RS tcbS topS)
open Spike.Lib.X64.HelloPh (lo)
open Spike.Lib.X64.HelloPh.StartH0G (helloLsw)
open Spike.Lib.X64.HelloPh.StartH0U (msUH)
open Spike.Lib.X64.HelloPh.C0S (c0S)
open Spike.Lib.X64.HelloPh.RdSrcL1 (RB jP' jX1 jC2 jC2' jX3 jC4 jC5)
open Spike.Lib.X64.HelloPh.RdPlS (RdImms)
open Spike.Lib.X64.HelloPh.XchgWr (InArL)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.X64WakeLoadT (L0T ls0T tcb0)
open Spike.Lib.X64HelloRodataSrc (rdCN)
open Spike.Lib.Hello1RodataSrc (τ8)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.X64.AS

/-! ## Uninhabited invariants -/

section Void

variable {W : Frag isa} {K : State → State → Prop} {exe : _root_.Executable}
  {endPc : Int64} {R : Region} {F : MachineData → Prop} {Jp Jp' J1 J2 J2' J3 J4 : FAS → Ctl → Prop}

/-- **`wc_rodata` from the allocator's return at an uninhabited `.x15` invariant** is inside any predicate: every
node's invariant asks for a state of `Jp`. -/
theorem rdPostW_void (hn : ∀ σ c, ¬ Jp σ c) : RdPostW W K exe endPc R F Jp Jp' J1 J2 J2' J3 J4 := by
  have hb : ∀ {n : ND} {blk : List (Directive × Nat)}, (∀ σ c, ¬ n.J σ c) → BlkW W K exe endPc R F n blk :=
    fun h _ σ c _ _ _ _ _ _ hJ => absurd hJ (h σ c)
  have hd : ∀ {n : ND}, (∀ σ c, ¬ n.J σ c) → NodeW W K exe endPc R F n := by
    intro n h s c hA
    obtain ⟨-, -, -, -, σ, -, -, hJ⟩ := hA
    exact absurd hJ (h σ c)
  refine ⟨hb hn, hd ?_, hb ?_, hd ?_, hb ?_, hd ?_, hb ?_, hd ?_, hb ?_⟩ <;>
    rintro σ c ⟨σ0, ⟨c0, h⟩, -⟩ <;> exact hn σ0 c0 h

/-- **`RdPostW`'s premises asked only at an inhabited `.x15` invariant** (`rdPostW_void` otherwise). -/
theorem rdPostW_of_inh (h : (∃ σ c, Jp σ c) → RdPostW W K exe endPc R F Jp Jp' J1 J2 J2' J3 J4) :
    RdPostW W K exe endPc R F Jp Jp' J1 J2 J2' J3 J4 := by
  by_cases hi : ∃ σ c, Jp σ c
  · exact h hi
  · exact rdPostW_void fun σ c hj => hi ⟨σ, c, hj⟩

end Void

/-! ## The landing at `.x15` -/

/-- **A landing image at `.x15` below `rdJH lab R' J` fixes the landing** (the memory side's units `3` and offset
`8` of rodata's call, `hu`, `hof`): `b`'s block of `n` words inside the cells, `n = 2`, and a caller's state at
`mNC lab R' J`. -/
theorem jpL_land {R R' : Region} {ms₀ : MemSide isa} {lab : Label → Int64} {J0 J : FAS → Ctl → Prop}
    {σC : FAS} {l : WeakMem.AllocLabel} {b n : Nat} {σ : FAS} {c : Ctl}
    (hu : ms₀.units 2 τ8 = 3) (hof : ms₀.off 2 τ8 = 8)
    (h : JpL (R := R) ms₀ lab J0 (mRdJ0 (rdJH lab R' J) σC) l b n σ c) :
    AllocLand ms₀.heap ms₀.cells b n ∧ n = 2 ∧ ∃ c', (mNC lab R' J).J σC c' := by
  obtain ⟨q, σx, σ', c0, ⟨ini, old, _, _, hb, hle, _, _, us, hus, hw⟩, ⟨⟨σe, ⟨_, hc0, c', hN⟩, _, _⟩, _⟩,
    ⟨hq0, _⟩, _⟩ := h
  have hq : q.1.c0 = rdCN := hq0.symm.trans hc0
  obtain ⟨-, hτ, -, hn⟩ := Spike.Lib.X64.HelloPh.MainWcL1B.q_rdCN q hq
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

/-- **`.x15`'s saved-`%rbp` cell at a landing image below `rdJH lab R' J`**: `leave` keeps the caller's cell
`-8` (outside the allocator's region), which `rN .call`'s `rdJ` has at the caller's `%rbp` at `wc_rodata`'s entry,
`R'`'s saved-`%rbp` address (`mNC`'s). -/
theorem jpL_slot8 {R R' : Region} {ms₀ : MemSide isa} {lab : Label → Int64} {J0 J : FAS → Ctl → Prop}
    {σC : FAS} {l : WeakMem.AllocLabel} {b n : Nat} {σ : FAS} {c : Ctl}
    (h : JpL (R := R) ms₀ lab J0 (mRdJ0 (rdJH lab R' J) σC) l b n σ c) :
    σ.slot (-8) = R'.addr (-8) := by
  obtain ⟨q, σx, σ', c0, -, ⟨⟨σe, ⟨rfl, -, c', hN⟩, -, h8⟩, -⟩, -, rfl⟩ := h
  obtain ⟨-, -, -, -, -, -, -, hbp, -⟩ := hN
  have hoff : ¬ (Spike.Lib.X64.Flow.Hello1.aR (mR R)).Off (-8 - -48) := by
    simp only [Region.Off, Spike.Lib.X64.Flow.Hello1.aR, Region.callee]; omega
  show (@ite _ ((Spike.Lib.X64.Flow.Hello1.aR (mR R)).Off (-8 - -48)) (Classical.propDecidable _) _ _) = _
  rw [ite_eq_right_of_eq_false _ _ (eq_false hoff), h8]
  exact hbp

/-- **`nodeW_wrC_rdX1`'s `hin` at `jX1`**: the buffer's first word is in `l`'s range at `b`, inside the arena. -/
theorem inArL_jX1 {ar : Spike.Lib.Arena} {L0 : Lbl} {ls0 : Lsize} {l : WeakMem.AllocLabel} {b n : Nat}
    (hb : AllocLand ar.heap ar.cells b n) (hn : n = 2) :
    ∀ σ0 c, jX1 (Spike.Lib.X64ConsumerA.upd L0 l b) l σ0 c →
      InArL ar (Spike.Lib.X64ConsumerA.upd L0 l b) (Spike.Lib.X64ConsumerA.updN ls0 l n)
        (bAddr σ0.regs .rax 0).toNat := by
  rintro σ0 c ⟨hB, -⟩
  have hx : σ0.regs.rax.toBitVec.toNat = b := by
    have := hB.1; simp only [Spike.Lib.X64ConsumerA.upd, ite_true, Option.some.injEq] at this; omega
  refine ⟨l, b, by simp [Spike.Lib.X64ConsumerA.upd], ⟨hb.1, by simpa [Spike.Lib.X64ConsumerA.updN] using hb.2.1⟩,
    ?_⟩
  rw [Spike.Lib.X64.HelloPh.RdSrcL1.bAddr0 hB]
  simp only [lrange, Range.contains, Spike.Lib.X64ConsumerA.updN, ite_true]
  omega

/-- **`nodeW_wrC_rdX2`'s `hin` at `jX3`**: the buffer's second word is in `l`'s range at `b`, inside the arena. -/
theorem inArL_jX3 {ar : Spike.Lib.Arena} {L0 : Lbl} {ls0 : Lsize} {l : WeakMem.AllocLabel} {b n : Nat}
    (hb : AllocLand ar.heap ar.cells b n) (hn : n = 2) :
    ∀ σ0 c, jX3 (Spike.Lib.X64ConsumerA.upd L0 l b) l σ0 c →
      InArL ar (Spike.Lib.X64ConsumerA.upd L0 l b) (Spike.Lib.X64ConsumerA.updN ls0 l n)
        (bAddr σ0.regs .rax 8).toNat := by
  rintro σ0 c ⟨hB, -⟩
  have hx : σ0.regs.rax.toBitVec.toNat = b := by
    have := hB.1; simp only [Spike.Lib.X64ConsumerA.upd, ite_true, Option.some.injEq] at this; omega
  refine ⟨l, b, by simp [Spike.Lib.X64ConsumerA.upd], ⟨hb.1, by simpa [Spike.Lib.X64ConsumerA.updN] using hb.2.1⟩,
    ?_⟩
  rw [Spike.Lib.X64.HelloPh.RdSrcL1.bAddr8 hB]
  simp only [lrange, Range.contains, Spike.Lib.X64ConsumerA.updN, ite_true]
  omega

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
local notation "MSU" => msUH (asm := asm) hpw i0 E rd I ls [FR]

set_option hygiene false in
local notation "LBL" => Spike.Lib.X64ConsumerA.upd (LB) l b

set_option maxHeartbeats 800000 in
/-- **`MainWcPS.hW` at `Level1I`'s choices** (module doc). -/
theorem hW_L1 (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells) (hlo0 : Λ0.code.lo = lo)
    (hc : Spike.Lib.X64.Rt.CtrZ o) (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hI : RdImms (Ly).Λ) (himm : (Ly).Λ.imms Spike.Lib.SrcCalls.setupCont "me" 0 = some (tcb0 (Ly).Λ))
    {l : WeakMem.AllocLabel} {b n : Nat} {m0 : MachineData} {σC : FAS} (hl : (LB) l = none) :
    MainPostSWH (Spike.Lib.X64.HelloPh.Level1I.W1R (asm := asm) hpw i0 E rd ls l b n)
      (Spike.Lib.X64.PhRec.K (Ly) (RS0)) (Ly).exe (Ly).endPc (RR) (FS (Ly) (RS0) helloLsw 0#64 (TOP)) (FR) m0 σC
      (JpT (JpL (R := RR) (MSU) (Ly).lab (mRdJ0 (J') σC) (mRdJ0 (J') σC) l b n) (TV))
      (jP' (LBL) l) (jX1 (LBL) l) (jC2 (LBL) l) (jC2' (LBL) l) (jX3 (LBL) l) (J4P (jC4 (LBL) l) (jC5 (LBL) l))
      (JrT (JrRL (LBL) c0S.env l) (TV) (RR)) := by
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
  obtain ⟨-, hok, -⟩ := Spike.Lib.X64.HelloPh.Land.fstable_FS hpw i0
  have hRlo : (RR).lo ≤ -288 := by show (8 - helloLsw : Int) ≤ -288; decide
  have hhi : (8 : Int) ≤ (RR).hi := by show (8 : Int) ≤ 8; decide
  have hbuf := Spike.Lib.X64.HelloPh.MainWcL1B.hbuf_L1 (asm := asm) hpw i0 (E := E) (rd := rd) (I := I) (ls := ls)
    hA13 (l := l) (b := b) (n := n) (m0 := m0) (σC := σC)
  refine ⟨?_, Spike.Lib.X64.HelloPh.MainWcL1S.sp0_L1 (frM := FR) (rS := RS0) (σC := σC) (t := TV) hprog hlo hΛ
    hlab hsite hcl hX0 hok hRlo hhi (env := c0S.env) (tm := .tid)
    (mw := TermRun.cst (.loc ⟨Spike.Lib.X64WakeT1.mainTidLbl 2, 0⟩ 0)) rfl himm
    (Spike.Lib.X64.HelloPh.MainWcL1S.valRep_upd hl (Spike.Lib.X64.WakeImmsC0.valRep_me _))⟩
  refine rdPostW_of_inh fun hinh => ?_
  obtain ⟨σi, ci, hi⟩ := hinh
  obtain ⟨hAL, hn2, c', hN⟩ := jpL_land (ms₀ := MSU) rfl rfl hi.1
  have hAL' : AllocLand (Spike.Lib.X64.WakeOD.arW hpw IH).heap (Spike.Lib.X64.WakeOD.arW hpw IH).cells b n := hAL
  have hmem : ∀ i : Int64, (i = 0 ∨ i = 8) → ∀ σ0 c,
      JpT (JpL (R := RR) (MSU) (Ly).lab (mRdJ0 (J') σC) (mRdJ0 (J') σC) l b n) (TV) σ0 c →
      ∀ m, mF (RR) (FS (Ly) (RS0) helloLsw 0#64 (TOP)) m0 σC m →
        Mem.loadInt m.dmem (bAddr σ0.regs .rax i) 8 = none :=
    fun i hi σ0 c h => (hbuf σ0 c h i hi).2.1
  have hP := Spike.Lib.X64.HelloPh.HrdS.frP_mNC (lbl := LBL) hok (by omega) (by omega)
    Spike.Lib.X64.HelloPh.HrdR.hme_c0S
    (fun σ c h => Spike.Lib.X64.HelloPh.MainWcL1S.valRep_upd hl
      (Spike.Lib.X64.HelloPh.HrdR.hJ_JS hpw i0 σ c h).2) ⟨c', hN⟩
  exact Spike.Lib.X64.HelloPh.MainWcL1W.rdPostW_L1 (rS := RS0) hprog hlo hΛ hlab hsite hcl hX0 hok hRlo hhi
    (Spike.Lib.X64.HelloPh.RdJpL.jpT_rb Spike.Lib.X64.HelloPh.RdJpL.rdJH_rdCN)
    (fun σ0 c h => h.elim (fun ⟨hB, ini, wo0, wo1, e⟩ => ⟨hB, ini, wo0, wo1, .inl e⟩)
      fun ⟨hB, ini, wo0, wo1, e⟩ => ⟨hB, ini, wo0, wo1, .inr (.inl e)⟩) hbuf
    (fun σ0 c h => Spike.Lib.X64.HelloPh.MainWcL1W.hra_jpLW h.1) hI hP
    (Spike.Lib.X64.HelloPh.XchgWr.nodeW_wrC_rdX1 hprog hlo (NT) hsite har (hmem 0 (.inl rfl))
      (inArL_jX1 hAL' hn2))
    (Spike.Lib.X64.HelloPh.XchgWr.nodeW_wrC_rdX2 hprog hlo (NT) hsite har (hmem 8 (.inr rfl))
      (inArL_jX3 hAL' hn2))

/-- **`MainWcPS.hbp` at `Level1I`'s choices**: `.x15`'s `%rbp` is `wc_rodata`'s saved-`%rbp` slot
(`Level1A.jpL_rbp`). -/
theorem hbp_L1 {l : WeakMem.AllocLabel} {b n : Nat} {σC : FAS} :
    ∀ σ0 c, JpT (JpL (R := RR) (MSU) (Ly).lab (mRdJ0 (J') σC) (mRdJ0 (J') σC) l b n) (TV) σ0 c →
      σ0.regs.get64 .rbp = (mR (RR)).addr (-8) :=
  fun _ _ h => Spike.Lib.X64.HelloPh.Level1.jpL_rbp h.1

/-- **`MainWcPS.hsl` at `Level1I`'s choices**: `.x15`'s saved-`%rbp` cell is `scc_rt_main`'s saved-`%rbp` address
(`jpL_slot8`). -/
theorem hsl_L1 {l : WeakMem.AllocLabel} {b n : Nat} {σC : FAS} :
    ∀ σ0 c, JpT (JpL (R := RR) (MSU) (Ly).lab (mRdJ0 (J') σC) (mRdJ0 (J') σC) l b n) (TV) σ0 c →
      σ0.slot (-8) = (RR).addr (-8) :=
  fun _ _ h => jpL_slot8 h.1

end Root

end Spike.Lib.X64.HelloPh.MainWcL1R

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1R.rdPostW_void' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1R.rdPostW_void

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1R.rdPostW_of_inh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1R.rdPostW_of_inh

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1R.jpL_land' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1R.jpL_land

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1R.jpL_slot8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1R.jpL_slot8

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1R.inArL_jX1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1R.inArL_jX1

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1R.inArL_jX3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1R.inArL_jX3

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1R.hbp_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1R.hbp_L1

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1R.hW_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1R.hW_L1

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1R.hsl_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1R.hsl_L1
