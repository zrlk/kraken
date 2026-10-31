/-
**The allocator at a box allocation on x86-64**: `scc_rt_alloc(h, k, u)`
(`Spike/Lib/X64Alloc.lean`) called at a source box allocation
`let x = new a in e` of one object of `a`'s type `τ`, under a memory side
that allows box rows (`ms.newOk`). The x86-64 twin of
`Spike/Lib/A64AllocBox.lean` (same names).

The code and every node but the `ret` are the buffer allocation's
(`seg_allocW_genR` at the site premises `Call.OKS`,
`Spike/Lib/X64AllocSite.lean`); only the `ret` differs. At a box allocation
the allocator's return does not take the source's allocation step: the
source's `new` (`TermRun.alloc`: the label's push and the initialising
store) is taken at the caller's store of the box's word into the cell
(`Out.newStore`), so the `ret` is a silent step (`ai_ndW`) that keeps the
hold recording the counter's old value `o`.

- `ai_ndW` (namespace `Spike.Lib.X64`): a node at a single silent
  instruction whose step lands at a node after a local run of the source
  (AArch64's `A64AllocNodes.ai_ndW`; `X64AllocNodes.lean` is released and
  not edited).
- `Call.OKB`: the site premises with the site a box allocation of one
  object, `ms.newOk`.
- `EB`: the exits: the return to `ra` with the source still at the
  allocation, the hold recording `o` (`holdCtr`), `%rax` the cell's base
  `ms.heap + 16·o + ms.off 1 τ` with `o + units ≤ cells` and `ms.lo o`,
  `%rbp` restored; and the heap abort, `E`'s with `.full`'s pushed return
  address `.full + 12` at `-160`.
- `seg_allocBW_at`, `seg_allocBW`: the segment inside `W` from any node /
  the entry to `EB`.
- `newStore_ndW`: a node at the box's store `movq %r, k(%b)`
  (`Out.newStore`).
-/
import Spike.Lib.X64AllocSite

namespace Spike.Lib.X64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

/-- **A node at a single silent instruction** `a` (a register move, a
frame access, a branch, a `ret`): from every state of the invariant the
source takes a local run and the abstract step lands at a node (the
allocator's `ret` at a box allocation, where the hold is kept for the box's
store). Its states lie in `W`, and no outside move `K` moves them
(`hW`). -/
theorem ai_ndW {W : Frag isa} {K : State → State → Prop} {n : ND} {lo hi : Int} {a : AI} {z : Nat}
    (hok : a.ok lo hi n.o = true)
    (hreg : ∀ w op, a = .reg w op → RegOnly op = true) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(a.toDir, z)])
    (hW : ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s')
    (hedge : ∀ σ c, n.J σ c → ∃ c', LocalRun p c c' ∧
      Lands N E ⟨a.tgt (_root_.Executable.labels exe).label n.o (n.pc + Int64.ofNat z) σ, a.so n.o,
        a.step n.o (n.pc + Int64.ofNat z) σ⟩ c') :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s a.toDir z := (hcode s he hn).cell0 rfl rfl hpc
  obtain ⟨m', hex, hA', hD'⟩ := exec_ai hok hR hlo hhi hc hreg hA
  have hl : labelAddr s = (_root_.Executable.labels exe).label := by
    funext L; show (_root_.Executable.labels s.exe).label L = _; rw [he]
  rw [hl, hpc] at hex
  rw [hpc] at hA'
  obtain ⟨c', hr, hL⟩ := hedge σ c hJ
  refine .silent _ c' hex hr ?_
  rcases hL with ⟨j, hj⟩ | ⟨y, hy⟩
  · exact .inl ⟨j, hj.at he hn hdc hA' (hF _ _ hD hD')⟩
  · exact .inr ⟨y, hy.at he hn hdc hA' (hF _ _ hD hD')⟩

end Fn

end Spike.Lib.X64

namespace Spike.Lib.X64.Alloc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64
open Scc.Cert.Rt.X64 (Lays endOf code_field)

/-- **The call's premises at a box allocation**: the site premises
(`Call.OKS`), the memory side allowing box rows, the source at
`let x = new a in e` with `a` of type `τ`, one object. -/
structure Call.OKB (ms : MemSide isa) (lab : Label → Int64) (q : Call) : Prop where
  toS : q.OKS ms lab
  newOk : ms.newOk
  term : ∃ T, q.c0.term = .let_ q.x (.new q.a T) q.e
  ev : TermRun.evalAt q.c0.env q.a = some (q.τ, q.ws)
  one : q.n = 1

/-- **The exits at a box allocation**: the return to `ra` with the source
still at the allocation and the hold recording the counter's old value
`o` (its step is the caller's box store), `%rax` the cell's base, `%rbp`
restored; and the heap abort, `E`'s with the return address of `.full`'s
`call scc_rt_abort` in the slot it pushes (`-160`). -/
def EB (lab : Label → Int64) (ms : MemSide isa) (q : Call) : AX → ND
  | .ret => ⟨Int64.ofBitVec q.ra, oR, fun σ c => ∃ o : BitVec 64, c = holdCtr ms q.c0 o ∧
      σ.regs.rax.toNat = ms.heap + 16 * o.toNat + ms.off q.n q.τ ∧ o.toNat + ms.units q.n q.τ ≤ ms.cells ∧
      ms.lo o.toNat ∧ σ.regs.rbp.toBitVec = q.fp⟩
  | .abort => ⟨lab "scc_rt_abort", ⟨-160, [(.rbp, -8)]⟩, fun σ c => σ.regs.rdi.toBitVec = 2#64 ∧ Jfull ms q c ∧
      σ.slot (-160) = (lab fullL + 12).toBitVec⟩

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64} {R : Region}
  {q : Call} {cells : List (Directive × Nat)}

/-- **`scc_rt_alloc` at a box allocation is one segment inside `W` from any
of its nodes `i0`** to its return (the hold kept, `%rax` the cell's base)
or its heap abort (`EB`): `seg_allocW_genR` with the `ret` a silent step. -/
theorem seg_allocBW_at {W : Frag isa} {K : State → State → Prop} {F : MachineData → Prop} {kp : Nat}
    (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : allocIn cells = true) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -160) (hhi : 8 ≤ R.hi) (hq : q.OKB ms (_root_.Executable.labels exe).label)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hW : AllocW ms q W K exe endPc R F) (i0 : AN) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label ms q i0))
      (fun s c => ∃ x, At exe endPc R F (EB (_root_.Executable.labels exe).label ms q x) s c) := by
  have hin' := hin
  simp only [allocIn, fiAt, iCtr, iHeap, iRmw, iHdr, iRet, Bool.and_eq_true] at hin'
  refine seg_allocW_genR hp hend hin hF hR hlo hhi hq.toS hmem hW (lbl := lbl) (Ex := EB _ ms q)
    (fun _ _ ⟨hpc, ho, h2, hf⟩ hs => ⟨hpc, ho, h2, hf, hs⟩) ?_ i0
  refine ai_ndW (a := .ret) (z := 1) (lo := -160) (hi := 8) rfl (by rintro w op ⟨⟩) hF hR hlo hhi
    (code_field hp hend (by simp only [hin']) (l := okL) (off := 226) rfl) hW.ret
    fun σ c hJ => ⟨c, .refl c, .inr ⟨AX.ret, ?_⟩⟩
  obtain ⟨o, rfl, hle, hn28, h0, h29, h30, hlo'⟩ := hJ
  have hk := Call.k_toNat hq.toS.n_lt
  have hcl := hq.toS.cells
  have hA : σ.regs.rax.toBitVec.toNat = ms.heap + 16 * o.toNat + ms.off q.n q.τ := by
    rw [h0, base8_toNat (by omega) (by omega) (mOf_lt _) (by rw [hq.toS.heap]; exact hq.toS.room), hq.toS.heap,
      hk, hq.toS.off]
  refine ⟨?_, rfl, o, rfl, ?_, hle, hlo', ?_⟩
  · simp [N, EB, AI.tgt, h30]
  · rw [← hA]; simp [AI.step, Reg64s.set64, Reg64s.get64]
  · simp [AI.step, Reg64s.set64, Reg64s.get64, h29]

/-- **`scc_rt_alloc` at a box allocation is one segment inside `W`** from
its entry to its return (the hold kept) or its heap abort. -/
theorem seg_allocBW {W : Frag isa} {K : State → State → Prop} {F : MachineData → Prop} {kp : Nat}
    (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : allocIn cells = true) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -160) (hhi : 8 ≤ R.hi) (hq : q.OKB ms (_root_.Executable.labels exe).label)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hW : AllocW ms q W K exe endPc R F) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label ms q .e))
      (fun s c => ∃ x, At exe endPc R F (EB (_root_.Executable.labels exe).label ms q x) s c) :=
  seg_allocBW_at hp hend hin hF hR hlo hhi hq hmem hW .e

end Proof

/-! ## The box's store -/

section Store

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

/-- **A node at a box's store** `movq %r, k(%b)` (`Out.newStore`): from
every state of the invariant the memory side allows box rows, the address
is mapped for writing and outside the thread's private memory; the source
is at `let x = new a in e` of a one-word value `w` that `%r` represents,
the hold recording the counter's old value `old`, the address the cell's
base `ms.heap + 16·old + ms.off 1 t` within the arena; and for every fresh
label `l` the state after the store, with the source past its `new` (`x`
bound to `l`'s locative, no hold), is at `Eb l A` (`hxa`: one `ms.xa`
continues in). Its states lie in `W`, and no outside move `K` moves them
(`hW`). -/
theorem newStore_ndW {W : Frag isa} {K : State → State → Prop} {n : ND} {b r : Reg64} {k : Int64} {z : Nat}
    (Eb : WeakMem.AllocLabel → Nat → ND)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(stDir b k r, z)])
    (hxa : ∀ l A s c, lbl l = none → At exe endPc R F (Eb l A) s c → ms.xa l A 1 s c)
    (hW : ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s')
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      ms.newOk ∧ ms.mp ⟨bAddr σ.regs b k, 8⟩ true ∧ Mem.loadInt m.dmem (bAddr σ.regs b k) 8 = none ∧
      ∃ (x : String) (a : CoreTerm.At) (ty : Ty) (e : Expr) (w wold : TermRun.Word) (old : Nat),
        (∃ T, c.term = .let_ x (.new a T) e) ∧ TermRun.evalAt c.env a = some (ty, [w]) ∧
        TermRun.accs ty = some [.one] ∧
        Scc.Sem.ValRep lbl w.val (σ.regs.get64 r).toNat ∧
        c.hold = some (ms.ctr, wold) ∧ TermRun.numOf [wold] = some old ∧
        (bAddr σ.regs b k).toNat = ms.heap + 16 * old + ms.off 1 ty ∧ old + ms.units 1 ty ≤ ms.cells ∧
        ∀ l, lbl l = none → Hit (Eb l (bAddr σ.regs b k).toNat) ⟨n.pc + Int64.ofNat z, n.o, σ⟩
          ⟨e, (x, .ptr .own ty, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: c.env, none⟩) :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s (stDir b k r) z := (hcode s he hn).cell0 rfl rfl hpc
  obtain ⟨hN, hmp, hdm, x, a, ty, e, w, wold, old, ht, hev, hu, hv, hh, hold, hAeq, hcl, hX⟩ := hedge _ σ c hA hD hJ
  have ha : eaddr s z (mB b k) = bAddr σ.regs b k := (eaddr_mB s z b k).trans (by rw [hA.regs]; rfl)
  have hex := exec_store_agrees hc ha (by exact hdm) (agrees_of_decls hdc _ _)
  rw [Reg64s.get_low64, hA.regs] at hex
  have hs1 : after s z s.st.1 = { s with st := (s.st.1, n.pc + Int64.ofNat z) } := by
    simp only [after, hpc]
  rw [hs1] at hex
  refine .newStore _ _ _ _ x a ty e w wold old hN hex hmp ht hev hu ?_ hh hold hAeq hcl fun l hl =>
    hxa _ _ _ _ hl ((hX l hl).at he hn hdc hA hD)
  rwa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide))]

end Store

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.X64.ai_ndW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.ai_ndW

/-- info: 'Spike.Lib.X64.Alloc.seg_allocBW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms seg_allocBW

/-- info: 'Spike.Lib.X64.Alloc.newStore_ndW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms newStore_ndW

end Spike.Lib.X64.Alloc
