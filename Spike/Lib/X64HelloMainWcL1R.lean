/-
**The pieces of `MainWcPS.hW` at `Level1I`'s choices** (x86-64; the twin of `Spike/Lib/A64HelloMainWcL1R.lean`):
the facts about `wc_rodata`'s rest from `.x15` that `MainWcPS.hW` (`X64HelloMainWcL1RX.hW_L1X`, at `ownGHXW`) and
its `hbp`, `hsl` fields build on, at the root's layout, the level's labels `upd LB l b` at a fresh label `l`,
`c0S`'s environment.

- `rdPostW_void`, `rdPostW_of_inh`: `RdPostW` at an uninhabited `.x15` invariant is inside any predicate, so its
  premises are asked only at an inhabited one.
- `jpL_land`: a landing image at `.x15` below `rdJH lab R' J` fixes the landing: `AllocLand` of `b`, two words, and
  a caller's state at `mNC lab R' J` (the frame's premise `HrdS.frP_mNC`'s `hJC`).
- `jpL_slot8`: at a landing image below `rdJH lab R' J`, `.x15`'s saved-`%rbp` cell holds the caller's `%rbp`,
  `R'`'s saved-`%rbp` address.
- `inArL_jX1`, `inArL_jX3`: `XchgWr.nodeW_wrC_rdX1`/`rdX2`'s `hin` at `RdSrcL1`'s invariants and a landing.
- `hbp_L1`, `hsl_L1`: `MainWcPS.hbp`, `hsl` at `.x15`'s invariant
  `JpT (JpL … (mRdJ0 J' σC) (mRdJ0 J' σC) l b n) TV` (`Level1A.jpL_rbp`, `jpL_slot8`).

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
  table `i0M Λ0`). AArch64's `hW_L1` (at `ownGH`) is `MainWcL1RX.hW_L1X` here, at `ownGHXW`.
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
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib (MemSide Region Ctl FragS Frag PlaceWX)
open Spike.Lib.X64 (BlkW NodeW ND bAddr)
open Spike.Lib.X64.Flow.HelloRd (RdPostW rN)
open Spike.Lib.X64.Flow.Hello1 (AG mR mRdJ0 mNC)
open Spike.Lib.X64.Flow.Ret0 (tpOf)
open Spike.Lib.X64.Alloc (Ea)
open Spike.Lib.X64.HelloPh.Level1 (JpL JpT)
open Spike.Lib.X64.HelloPh.StartWcS (rdJH)
open Spike.Lib.X64.WakePh.MainGlue (JS RS tcbS topS)
open Spike.Lib.X64.HelloPh.StartH0G (helloLsw)
open Spike.Lib.X64.HelloPh.StartH0U (msUH)
open Spike.Lib.X64.HelloPh.C0S (c0S)
open Spike.Lib.X64.HelloPh.RdSrcL1 (RB jX1 jX3)
open Spike.Lib.X64.HelloPh.XchgWr (InArL)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.X64WakeLoadT (ls0T)
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

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1R.hsl_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1R.hsl_L1
