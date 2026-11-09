/-
**`wc_rodata`'s rest's `hbuf` at `Level1I`'s choices** (x86-64; the twin of `Spike/Lib/A64HelloMainWcL1B.lean`): at
every `.x15` state of `Level1I`'s invariant (a landing image `JpL` under main's thread pointer, below the root's
call invariant `mRdJ0 J'`), both buffer words `(%rax)` and `8(%rax)` are box cells (`WcW.BoxOkH`) under
`wc_rodata`'s frame condition at the start's `FS`: mapped (the heap), unloaded (`WordsNone`) and owned at no phase
(`HrdArena.offH_own`).

- `q_rdCN`: an allocator call at `rdCN` is rodata's `newBuf` of two `τ8` lanes binding `b`.
- `CellX0Q`, `cellX0Q_jpL`: `%rax` is an allocator call's block with room for its header and two words, at a
  landing image below `rdCN`.
- `boxOkH_q`: both words at `CellX0Q` are `BoxOkH`.
- `hbuf_L1`: `RdWfSFX.rdPostW_WSHX`'s `hbuf` at `Level1I`'s choices.

## Differences from the AArch64 version

- The buffer's base is `%rax` (AArch64 `x0`), its words `bAddr σ.regs .rax i` (AArch64 `rAddr σ.regs .X0 i`).
- `wc_rodata`'s caller's region is `scc_rt_main`'s `RS helloLsw TOP` (AArch64 `swR TOP (-helloLsw) 0`), the caller's
  invariant `rdJH` at it and main's thread pointer `tpOf (tcbS Ly)` (AArch64 `pinA + 8`).
- The owned words are `HelloPh.ownH` (`WcWfR.not_ownW`); `offH_own` is `X64HelloHrdOff`'s.
-/
import Spike.Lib.X64HelloMainWcL1W
import Spike.Lib.X64HelloHrdArena
import Spike.Lib.X64HelloLevel1I

namespace Spike.Lib.X64.HelloPh.MainWcL1B

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Entry)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lsize)
open Spike.Lib (MemSide Region PlaceWX)
open Spike.Lib.X64 (bAddr)
open Spike.Lib.X64.HelloPh.WcW (BoxOkH)
open Spike.Lib.X64.Flow.Hello1 (AG mR mF mRdJ0)
open Spike.Lib.X64.HelloPh.Level1 (JpL JpT)
open Spike.Lib.X64.HelloPh.StartWcS (rdJH)
open Spike.Lib.X64.WakePh.MainGlue (FS JS RS tcbS topS)
open Spike.Lib.X64.Flow.Ret0 (tpOf)
open Spike.Lib.X64.HelloPh.StartH0G (helloLsw)
open Spike.Lib.X64.HelloPh.StartH0U (msUH)
open Spike.Lib.X64.HelloPh.C0S (c0S)
open Spike.Lib.DmemPriv (WordsNone)
open Spike.Lib.X64HelloRodataSrc (rdCN eW0)
open Spike.Lib.Hello1RodataSrc (τ8)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.X64.AS

/-! ## rodata's call -/

/-- **An allocator call at `rdCN` is rodata's `newBuf`** of two `τ8` lanes binding `b` (`Hello1.rdQ_facts`'s
twin at hello's `rdCN`). -/
theorem q_rdCN {ms : MemSide isa} {lab : Label → Int64} (q : AG ms lab) (hq : q.1.c0 = rdCN) :
    q.1.x = "b" ∧ q.1.τ = τ8 ∧ q.1.e = eW0 ∧ q.1.n = 2 := by
  obtain ⟨h1, h2, h3, -, -⟩ := Spike.Lib.X64HelloRodataSrc.rdCN_newBuf
  have ht := q.2.term
  have hv := q.2.ev
  have hn := q.2.num
  rw [hq, h1] at ht
  simp only [Expr.let_.injEq, Op.newBuf.injEq] at ht
  obtain ⟨hx, ⟨ha, hτ⟩, he⟩ := ht
  rw [hq, ← ha, h2] at hv
  simp only [Option.some.injEq, Prod.mk.injEq] at hv
  rw [← hv.2, h3] at hn
  simp only [Option.some.injEq] at hn
  exact ⟨hx.symm, hτ.symm, he.symm, hn.symm⟩

/-- **`%rax` is an allocator call's block with room for its header and two words**: some call `q`, counter value
`old`, the block inside the cells, its offset and two words inside its units. -/
def CellX0Q (ms : MemSide isa) (lab : Label → Int64) (σ : FAS) : Prop :=
  ∃ q : AG ms lab, ∃ old : Nat, σ.regs.rax.toNat = ms.heap + 16 * old + ms.off q.1.n q.1.τ ∧
    old + ms.units q.1.n q.1.τ ≤ ms.cells ∧ ms.off q.1.n q.1.τ + 16 ≤ 16 * ms.units q.1.n q.1.τ

/-- **`CellX0Q` at a landing image below `rdCN`** (`hJ1`), the memory side's units of rodata's call three
(`hu`). -/
theorem cellX0Q_jpL {R : Region} {ms₀ : MemSide isa} {lab : Label → Int64} {J0 J1 : FAS → Ctl → Prop}
    {l : WeakMem.AllocLabel} {b w : Nat} {σ : FAS} {c : Ctl} (hJ1 : ∀ σ c, J1 σ c → c = rdCN)
    (hu : ms₀.units 2 τ8 = 3) (h : JpL (R := R) ms₀ lab J0 J1 l b w σ c) : CellX0Q ms₀ lab σ := by
  obtain ⟨q, σx, σ', c0, ⟨ini, old, -, hx0, hb, hle, -⟩, ⟨⟨σe, hJe, -, -⟩, -, h257, -⟩,
    ⟨hc0, -, -, hh, -⟩, rfl⟩ := h
  have hq : q.1.c0 = rdCN := hc0.symm.trans (hJ1 _ _ hJe)
  have hqh : q.1.h = 257#64 := hh.symm.trans h257
  obtain ⟨-, hτ, -, hn⟩ := q_rdCN q hq
  have hoff := q.2.off
  rw [hqh, show (Spike.Lib.X64.Alloc.mOf 257#64).toNat = 0 by decide] at hoff
  refine ⟨q, old, hx0.trans hb, hle, ?_⟩
  rw [hn, hτ] at hoff
  rw [hn, hτ, hu]
  omega

/-- **The two buffer words at `CellX0Q` are box cells**: the block-room premise of the call at hand only, the
arena's room from the call's `room` and `cells`. -/
theorem boxOkH_q {L : RuntimeLayout} {a : BitVec 64} {F : MachineData → Prop} {ms : MemSide isa}
    {lab : Label → Int64}
    (hwn : ∀ m, F m → WordsNone L.Λ m.dmem) (hH : L.Λ.heap.lo ≤ ms.heap)
    (hHi : ms.heap + 16 * ms.cells ≤ L.Λ.heap.lo + L.Λ.heap.size)
    (hoffO : ∀ w', (w' = L.pnA ∨ w' = L.lockA ∨ w' = L.freeNA ∨ w' = L.nextA ∨ w' = a) →
      ¬ (ms.heap ≤ w'.toNat ∧ w'.toNat < ms.heap + 16 * ms.cells) ∧ w' ≠ BitVec.ofNat 64 ms.ctr)
    {σ : FAS} (h : CellX0Q ms lab σ) :
    ∀ i : Int64, (i = 0 ∨ i = 8) → BoxOkH L.Λ L a F (bAddr σ.regs .rax i) := by
  obtain ⟨q, old, hx, hle, ho'⟩ := h
  have hroom : ms.heap + 16 * ms.cells ≤ 2 ^ 64 := by
    have := q.2.room; have := q.2.cells; omega
  have key : ∀ j : Nat, (j = 0 ∨ j = 8) →
      BoxOkH L.Λ L a F (BitVec.ofNat 64 (ms.heap + 16 * old + ms.off q.1.n q.1.τ + j)) := by
    intro j hj
    have e : (BitVec.ofNat 64 (ms.heap + 16 * old + ms.off q.1.n q.1.τ + j)).toNat =
        ms.heap + 16 * old + ms.off q.1.n q.1.τ + j := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine ⟨Spike.Lib.LowerX64.mapped_K0_of_heap fun k hk => ?_,
      Spike.Lib.X64.Alloc.hbuf_of_wordsNone hwn hH hHi hroom ho' old hle j hj,
      Spike.Lib.X64.WakePh.WcWfR.not_ownW hoffO (.inr ?_)⟩
    · rw [e]; unfold Scc.Sem.Range.contains; omega
    · rw [e]; omega
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
local notation "RS0" => Spike.Lib.X64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "FR" => Spike.Lib.X64HelloRdCf.frH c0S.env

set_option hygiene false in
local notation "TOP" => topS (Ly) 0#64

set_option hygiene false in
/-- `scc_rt_main`'s region at the first stack's top. -/
local notation "RM" => RS helloLsw (TOP)

set_option hygiene false in
local notation "TV" => tpOf (tcbS (Ly))

set_option hygiene false in
local notation "J'" => rdJH (Ly).lab (RM) (JS (Ly) 0#64 c0S)

set_option hygiene false in
local notation "MSU" => msUH (asm := asm) hpw i0 E rd I ls [FR]

/-- **`rdPostW_WSHX`'s `hbuf` at `Level1I`'s choices** (module doc): at every `.x15` state of `Level1I`'s invariant,
both buffer words are box cells under `wc_rodata`'s frame condition at the start's `FS`. -/
theorem hbuf_L1 (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    {l : WeakMem.AllocLabel} {b n : Nat} {m0 : MachineData} {σC : FAS} :
    ∀ σ0 c, JpT (JpL (R := RM) (MSU) (Ly).lab (mRdJ0 (J') σC) (mRdJ0 (J') σC) l b n) (TV) σ0 c →
      ∀ i : Int64, (i = 0 ∨ i = 8) →
        BoxOkH (Ly).Λ (Ly) (NT) (mF (RM) (FS (Ly) (RS0) helloLsw 0#64 (TOP)) m0 σC) (bAddr σ0.regs .rax i) := by
  intro σ0 c h
  have hpl := Spike.Lib.PlaceWX.link IH hpw
  have hsz : 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.size :=
    Spike.Lib.X64.Rt.ArenaW.PlaceWX.heapSize_of_placeWX hpl
  have hu : (MSU).units 2 τ8 = 3 := rfl
  refine boxOkH_q (fun m hm => hm.1.1.1.wn) (Nat.le_refl _) ?_
    (Spike.Lib.X64.HelloPh.HrdArena.offH_own hpw i0 hA13)
    (cellX0Q_jpL Spike.Lib.X64.HelloPh.RdJpL.rdJH_rdCN hu h.1)
  show (Ly).Λ.heap.lo + 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.lo + (Ly).Λ.heap.size
  omega

end Root

end Spike.Lib.X64.HelloPh.MainWcL1B

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1B.q_rdCN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1B.q_rdCN

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1B.cellX0Q_jpL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1B.cellX0Q_jpL

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1B.boxOkH_q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1B.boxOkH_q

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1B.hbuf_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1B.hbuf_L1
