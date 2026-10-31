/-
**The allocator at a box allocation on AArch64**: `scc_rt_alloc(h, k, u)`
(`Spike/Lib/A64Alloc.lean`) called at a source box allocation
`let x = new a in e` of one object of `a`'s type `τ`, under a memory side
that allows box rows (`ms.newOk`).

The code and every node but the `ret` are the buffer allocation's
(`seg_allocW_gen` at the site premises `Call.OKS`); only the `ret` differs.
At a box allocation the allocator's return does not take the source's
allocation step: the source's `new` (`TermRun.alloc`: the label's push and
the initialising store) is taken at the caller's store of the box's word
into the cell (`Out.newStore`), so the `ret` is a silent step (`ai_ndW`)
that keeps the hold recording the counter's old value `o`.

- `Call.OKB`: the site premises with the site a box allocation of one
  object, `ms.newOk`.
- `EB`: the exits: the return to `ra` with the source still at the
  allocation, the hold recording `o` (`holdCtr`), `x0` the cell's base
  `ms.heap + 16·o + ms.off 1 τ` with `o + units ≤ cells` and `ms.lo o`,
  `x29` and `x30` restored; and the heap abort, as `E`'s.
- `seg_allocBW_at`, `seg_allocBW`: the segment inside `W` from any node /
  the entry to `EB`.
-/
import Spike.Lib.A64Alloc

namespace Spike.Lib.A64.Alloc

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Spike.Lib.A64.Flow

/-- **The call's premises at a box allocation**: the site premises
(`Call.OKS`), the memory side allowing box rows, the source at
`let x = new a in e` with `a` of type `τ`, one object. -/
structure Call.OKB (ms : MemSide isaLSE2) (lab : Label → Int64) (q : Call) : Prop where
  toS : q.OKS ms lab
  newOk : ms.newOk
  term : ∃ T, q.c0.term = .let_ q.x (.new q.a T) q.e
  ev : TermRun.evalAt q.c0.env q.a = some (q.τ, q.ws)
  one : q.n = 1

/-- **The exits at a box allocation**: the return to `ra` with the source
still at the allocation and the hold recording the counter's old value
`o` (its step is the caller's box store), `x0` the cell's base; and the
heap abort, as `E`'s with `x30` past `.4_full`'s `bl scc_rt_abort`. -/
def EB (lab : Label → Int64) (ms : MemSide isaLSE2) (q : Call) : AX → ND
  | .ret => ⟨Int64.ofBitVec q.ra, oE, fun σ c => ∃ o : BitVec 64, c = holdCtr ms q.c0 o ∧
      σ.regs.X0.toNat = ms.heap + 16 * o.toNat + ms.off q.n q.τ ∧ o.toNat + ms.units q.n q.τ ≤ ms.cells ∧
      ms.lo o.toNat ∧ σ.regs.X29.toBitVec = q.x29 ∧ σ.regs.X30.toBitVec = q.ra⟩
  | .abort => ⟨lab "scc_rt_abort", oI, fun σ c => σ.regs.X0 = 2 ∧
      σ.regs.X30.toBitVec = (lab ".L2_scc_rt_alloc.4_full" + 8).toBitVec ∧ Jfull ms q c⟩

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {q : Call}

/-- **`scc_rt_alloc` at a box allocation is one segment inside `W` from any
of its nodes `i0`** to its return (the hold kept, `x0` the cell's base) or
its heap abort (`EB`): `seg_allocW_gen` with the `ret` a silent step. -/
theorem seg_allocBW_at {W : Frag isaLSE2} {K : State → State → Prop} {F : MachineData → Prop}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -160) (hhi : 0 ≤ R.hi)
    (hq : q.OKB ms (_root_.Executable.labels exe).label) (hcode : Code ms q exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".L2_scc_rt_alloc.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_alloc" + 4 + 4 + 4 + 4 + 4 + 4 + 4)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hW : AllocW ms q W K exe endPc R F) (i0 : AN) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label ms q i0))
      (fun s c => ∃ x, At exe endPc R F (EB (_root_.Executable.labels exe).label ms q x) s c) := by
  refine seg_allocW_genR hF hR hal hlo hhi hq.toS hcode hentry hmem hW (lbl := lbl)
    (Ex := EB _ ms q) (fun _ _ ⟨h1, h2, h0, hf⟩ h30 => ⟨h1, h2, h0, h30, hf⟩) ?_ i0
  refine ai_ndW (a := iRet) (lo := -160) (hi := 0) rfl (by rintro w op ⟨⟩) hF hR hal hlo hhi
    (fun s he hn => hcode.ret s he hn) hW.ret fun σ c hJ => ⟨c, .refl c, .inr ⟨AX.ret, ?_⟩⟩
  obtain ⟨o, rfl, hle, hn28, h0, h29, h30, hlo'⟩ := hJ
  have hk := Call.k_toNat hq.toS.n_lt
  have hcl := hq.toS.cells
  have hA : σ.regs.X0.toBitVec.toNat = ms.heap + 16 * o.toNat + ms.off q.n q.τ := by
    rw [h0, base8_toNat (by omega) (by omega) (mOf_lt _) (by rw [hq.toS.heap]; exact hq.toS.room), hq.toS.heap,
      hk, hq.toS.off]
  refine ⟨?_, rfl, o, rfl, hA, hle, hlo', h29, h30⟩
  simp [EB, iRet, AI.tgt, Reg64s.getXReg, h30]

/-- **`scc_rt_alloc` at a box allocation is one segment inside `W`** from
its entry to its return (the hold kept) or its heap abort. -/
theorem seg_allocBW {W : Frag isaLSE2} {K : State → State → Prop} {F : MachineData → Prop}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -160) (hhi : 0 ≤ R.hi)
    (hq : q.OKB ms (_root_.Executable.labels exe).label) (hcode : Code ms q exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".L2_scc_rt_alloc.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_alloc" + 4 + 4 + 4 + 4 + 4 + 4 + 4)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hW : AllocW ms q W K exe endPc R F) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label ms q .e))
      (fun s c => ∃ x, At exe endPc R F (EB (_root_.Executable.labels exe).label ms q x) s c) :=
  seg_allocBW_at hF hR hal hlo hhi hq hcode hentry hmem hW .e

end Proof

/-! ## The box's store -/

section Store

open Kraken.Promising.Lower.A64

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

/-- **A node at a box's store** `str Xt, [Xn, #i]` (`Out.newStore`): from
every state of the invariant the memory side allows box rows, the address
is mapped for writing and outside the thread's private memory; the source
is at `let x = new a in e` of a one-word value `w` that `Xt` represents,
the hold recording the counter's old value `old`, the address the cell's
base `ms.heap + 16·old + ms.off 1 t` within the arena; and for every fresh
label `l` the state after the store, with the source past its `new` (`x`
bound to `l`'s locative, no hold), is at `Eb l A` (`hxa`: one `ms.xa`
continues in). Its states lie in `W`, and no outside move `K` moves them
(`hW`). -/
theorem newStore_ndW {W : Frag isaLSE2} {K : State → State → Prop} {n : ND} {t b : XReg} {i : Int64}
    (Eb : WeakMem.AllocLabel → Nat → ND)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [strDir t b i])
    (hxa : ∀ l A s c, lbl l = none → At exe endPc R F (Eb l A) s c → ms.xa l A 1 s c)
    (hW : ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s')
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      ms.newOk ∧ ms.mp ⟨rAddr σ.regs b i, 8⟩ true ∧ Mem.loadInt m.dmem (rAddr σ.regs b i) 8 = none ∧
      ∃ (x : String) (a : CoreTerm.At) (ty : Ty) (e : Expr) (w wold : TermRun.Word) (old : Nat),
        (∃ T, c.term = .let_ x (.new a T) e) ∧ TermRun.evalAt c.env a = some (ty, [w]) ∧
        TermRun.accs ty = some [.one] ∧
        Scc.Sem.ValRep lbl w.val (σ.regs.getRegOrZr (.low (.reg t) .W64)).toNat ∧
        c.hold = some (ms.ctr, wold) ∧ TermRun.numOf [wold] = some old ∧
        (rAddr σ.regs b i).toNat = ms.heap + 16 * old + ms.off 1 ty ∧ old + ms.units 1 ty ≤ ms.cells ∧
        ∀ l, lbl l = none → Hit (Eb l (rAddr σ.regs b i).toNat) ⟨n.pc + Int64.ofNat 4, n.o, σ⟩
          ⟨e, (x, .ptr .own ty, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: c.env, none⟩) :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s (strDir t b i) 4 := (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  obtain ⟨hN, hmp, hdm, x, a, ty, e, w, wold, old, ht, hev, hu, hv, hh, hold, hAeq, hcl, hX⟩ := hedge _ σ c hA hD hJ
  have ha : rAddr s.st.1.regs b i = rAddr σ.regs b i := by rw [hA.regs]
  have hex := exec_str_agrees hc ha (by exact hdm) (agrees_of_decls hdc _ _)
  rw [hA.regs] at hex
  have hs1 : after s 4 s.st.1 = { s with st := (s.st.1, n.pc + Int64.ofNat 4) } := by
    simp only [after, hpc]
  rw [hs1] at hex
  refine .newStore _ _ _ _ x a ty e w wold old hN hex hmp ht hev hu ?_ hh hold hAeq hcl fun l hl =>
    hxa _ _ _ _ hl ((hX l hl).at he hn hdc hA hD)
  rwa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide))]

end Store

/-- info: 'Spike.Lib.A64.Alloc.seg_allocBW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms seg_allocBW

/-- info: 'Spike.Lib.A64.Alloc.newStore_ndW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms newStore_ndW

end Spike.Lib.A64.Alloc
