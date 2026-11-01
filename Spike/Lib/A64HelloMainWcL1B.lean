/-
**`MainWcL1W.rdPostW_L1`'s `hbuf` at the root's choices** (AArch64, `Level1I`'s
`hP` stage 2): `.sp0`'s buffer words are box cells (`WcW.BoxOkH`) at every landing image
`JpT (JpL …) TV` of `Level1I` below the root's call invariant, under `wc_rodata`'s frame condition `mF R (FS …) m0 σC`.

`RdBuf.boxOkH_cellX0` asks its block-room premise (`ho`) of every allocator call at the memory side, which fails
at the root for calls of no element (one unit, one header word). Here it is asked of rodata's call only: below
`rdCN` the call allocates two one-word lanes (`q_rdCN`), three units at the root's arena (`hu`), the header word
`8` (`Call.OK.off` at header `257`), so `8 + 16 ≤ 48`; the block's room comes from `Call.OK.room`/`cells`.

- `q_rdCN`: an allocator call at `rdCN` is rodata's `newBuf` (`Hello1.rdQ_facts`'s twin).
- `CellX0Q`, `cellX0Q_jpL`: `.sp0`'s `x0` is rodata's call's block, with its room, at `JpL`.
- `boxOkH_q`: `RdBuf.boxOkH_cellX0` at `CellX0Q`.
- `hbuf_L1`: `rdPostW_L1`'s `hbuf` at `Level1I`'s choices (the arena facts `HrdArena.offH_own`, `WordsNone` of
  `FS`, `.heap`'s size). Left: `hA13` (the certificate's `a13data` check, as `HrdArena.hno_U`).
-/
import Spike.Lib.A64HelloMainWcL1W
import Spike.Lib.A64HelloHrdArena
import Spike.Lib.A64HelloLevel1I

namespace Spike.Lib.A64.HelloPh.MainWcL1B

variable {asm : String}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lsize)
open Spike.Lib (MemSide Region Ctl)
open Spike.Lib.A64.Flow (swR)
open Spike.Lib.A64.Flow.Hello1 (AG mF mR mRdJ0)
open Spike.Lib.A64.Alloc (Ea)
open Spike.Lib.A64.HelloPh.WcW (BoxOkH)
open Spike.Lib.A64.HelloPh.Level1 (JpL JpT)
open Spike.Lib.A64.HelloPh.StartWcS (rdJH)
open Spike.Lib.A64.WakePh.MainGlue (FS JS)
open Spike.Lib.A64.HelloPh.StartH0G (helloLsw)
open Spike.Lib.A64.HelloPh.StartH0U (msUH)
open Spike.Lib.A64.HelloPh.C0S (c0S)
open Spike.Lib.DmemPriv (WordsNone)
open Spike.Lib.HelloRodataSrc (rdCN eW0)
open Spike.Lib.Hello1RodataSrc (τ8)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

/-! ## rodata's call -/

/-- **An allocator call at `rdCN` is rodata's `newBuf`** of two `τ8` lanes binding `b` (`Hello1.rdQ_facts`'s
twin at hello's `rdCN`). -/
theorem q_rdCN {ms : MemSide isaLSE2} {lab : Label → Int64} (q : AG ms lab) (hq : q.1.c0 = rdCN) :
    q.1.x = "b" ∧ q.1.τ = τ8 ∧ q.1.e = eW0 ∧ q.1.n = 2 := by
  obtain ⟨h1, h2, h3, -, -⟩ := Spike.Lib.HelloRodataSrc.rdCN_newBuf
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

/-- **`x0` is an allocator call's block with room for its header and two words**: some call `q`, counter value
`old`, the block inside the cells, its offset and two words inside its units. -/
def CellX0Q (ms : MemSide isaLSE2) (lab : Label → Int64) (σ : FAS) : Prop :=
  ∃ q : AG ms lab, ∃ old : Nat, σ.regs.X0.toNat = ms.heap + 16 * old + ms.off q.1.n q.1.τ ∧
    old + ms.units q.1.n q.1.τ ≤ ms.cells ∧ ms.off q.1.n q.1.τ + 16 ≤ 16 * ms.units q.1.n q.1.τ

/-- **`CellX0Q` at a landing image below `rdCN`** (`hJ1`), the memory side's units of rodata's call three
(`hu`). -/
theorem cellX0Q_jpL {R : Region} {ms₀ : MemSide isaLSE2} {lab : Label → Int64} {J0 J1 : FAS → Ctl → Prop}
    {l : WeakMem.AllocLabel} {b w : Nat} {σ : FAS} {c : Ctl} (hJ1 : ∀ σ c, J1 σ c → c = rdCN)
    (hu : ms₀.units 2 τ8 = 3) (h : JpL (R := R) ms₀ lab J0 J1 l b w σ c) : CellX0Q ms₀ lab σ := by
  obtain ⟨q, σx, σ', c0, ⟨ini, old, -, hx0, hb, hle, -⟩, ⟨⟨σe, hJe, -, -⟩, h257, -⟩,
    ⟨hc0, -, -, hh, -⟩, rfl⟩ := h
  have hq : q.1.c0 = rdCN := hc0.symm.trans (hJ1 _ _ hJe)
  have hqh : q.1.h = 257#64 := hh.symm.trans h257
  obtain ⟨-, hτ, -, hn⟩ := q_rdCN q hq
  have hoff := q.2.off
  rw [hqh, show (Spike.Lib.A64.Alloc.mOf 257#64).toNat = 0 by decide] at hoff
  refine ⟨q, old, hx0.trans hb, hle, ?_⟩
  rw [hn, hτ] at hoff
  rw [hn, hτ, hu]
  omega

/-- **`RdBuf.boxOkH_cellX0` at `CellX0Q`**: the block-room premise of the call at hand only, the arena's room
from the call's `room` and `cells`. -/
theorem boxOkH_q {L : RuntimeLayout} {a : BitVec 64} {F : MachineData → Prop} {ms : MemSide isaLSE2}
    {lab : Label → Int64}
    (hwn : ∀ m, F m → WordsNone L.Λ m.dmem) (hH : L.Λ.heap.lo ≤ ms.heap)
    (hHi : ms.heap + 16 * ms.cells ≤ L.Λ.heap.lo + L.Λ.heap.size)
    (hoffO : ∀ w', (w' = L.pnA ∨ w' = L.lockA ∨ w' = L.freeNA ∨ w' = L.nextA ∨ w' = a) →
      ¬ (ms.heap ≤ w'.toNat ∧ w'.toNat < ms.heap + 16 * ms.cells) ∧ w' ≠ BitVec.ofNat 64 ms.ctr)
    {σ : FAS} (h : CellX0Q ms lab σ) :
    ∀ i : Int64, (i = 0 ∨ i = 8) → BoxOkH L.Λ L a F (Spike.Lib.A64.Flow.rAddr σ.regs .X0 i) := by
  obtain ⟨q, old, hx, hle, ho'⟩ := h
  have hroom : ms.heap + 16 * ms.cells ≤ 2 ^ 64 := by
    have := q.2.room; have := q.2.cells; omega
  have hX : σ.regs.X0.toBitVec = BitVec.ofNat 64 (ms.heap + 16 * old + ms.off q.1.n q.1.τ + 0) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hx
  have key : ∀ j : Nat, (j = 0 ∨ j = 8) →
      BoxOkH L.Λ L a F (BitVec.ofNat 64 (ms.heap + 16 * old + ms.off q.1.n q.1.τ + j)) := by
    intro j hj
    have e : (BitVec.ofNat 64 (ms.heap + 16 * old + ms.off q.1.n q.1.τ + j)).toNat =
        ms.heap + 16 * old + ms.off q.1.n q.1.τ + j := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine ⟨Spike.Lib.LowerA64.mapped_K0_of_heap fun k hk => ?_,
      Spike.Lib.A64.Alloc.hbuf_of_wordsNone hwn hH hHi hroom ho' old hle j hj,
      Spike.Lib.A64.WakePh.WcWfR.not_ownW hoffO (.inr ?_)⟩
    · rw [e]; unfold Scc.Sem.Range.contains; omega
    · rw [e]; omega
  rintro i (rfl | rfl)
  · rw [Spike.Lib.A64.Flow.Hello1.rAddr_x0_0, hX]
    exact key 0 (.inl rfl)
  · rw [Spike.Lib.A64.Flow.Hello1.rAddr_x0_8, hX]
    have : BitVec.ofNat 64 (ms.heap + 16 * old + ms.off q.1.n q.1.τ + 0) + 8#64 =
        BitVec.ofNat 64 (ms.heap + 16 * old + ms.off q.1.n q.1.τ + 8) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega
    rw [this]
    exact key 8 (.inr rfl)

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
local notation "FR" => Spike.Lib.HelloRdCf.frH c0S.env

set_option hygiene false in
local notation "TOP" => Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
local notation "TV" => UInt64.ofBitVec (Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
local notation "J'" => rdJH (Ly).lab (JS (Ly) 0#64 c0S)

set_option hygiene false in
local notation "MSU" => msUH (asm := asm) hpw i0 E rd I ls [FR]

/-- **`rdPostW_L1`'s `hbuf` at `Level1I`'s choices** (module doc): at every `.sp0` state of `Level1I`'s invariant,
both buffer words are box cells under `wc_rodata`'s frame condition at the start's `FS`. -/
theorem hbuf_L1 (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    {l : WeakMem.AllocLabel} {b n : Nat} {m0 : MachineData} {σC : FAS} :
    ∀ σ0 c, JpT (JpL (R := swR (TOP) (-helloLsw) 0) (MSU) (Ly).lab (mRdJ0 (J') σC) (mRdJ0 (J') σC) l b n)
        (TV) σ0 c →
      ∀ i : Int64, (i = 0 ∨ i = 8) →
        BoxOkH (Ly).Λ (Ly) (NT) (mF (swR (TOP) (-helloLsw) 0) (FS (Ly) (RS) helloLsw 0#64 (TOP)) m0 σC)
          (Spike.Lib.A64.Flow.rAddr σ0.regs .X0 i) := by
  intro σ0 c h
  have hpl := Spike.Lib.PlaceW.link IH hpw
  have hsz : 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.size :=
    Spike.Lib.A64.Rt.ArenaW.PlaceW.heapSize_of_placeW hpl
  have hu : (MSU).units 2 τ8 = 3 := rfl
  refine boxOkH_q (fun m hm => hm.1.1.wn) (Nat.le_refl _) ?_
    (Spike.Lib.A64.HelloPh.HrdArena.offH_own hpw i0 hA13)
    (cellX0Q_jpL Spike.Lib.A64.HelloPh.RdJpL.rdJH_rdCN hu h.1)
  show (Ly).Λ.heap.lo + 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.lo + (Ly).Λ.heap.size
  omega

end Root

end Spike.Lib.A64.HelloPh.MainWcL1B

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1B.q_rdCN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1B.q_rdCN

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1B.cellX0Q_jpL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1B.cellX0Q_jpL

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1B.boxOkH_q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1B.boxOkH_q

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1B.hbuf_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1B.hbuf_L1
