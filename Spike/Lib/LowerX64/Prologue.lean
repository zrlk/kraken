/-
**The stack-limit prologue lands at a lowered body's node** (x86-64),
symbolic in the frame; the twin of `Spike/Lib/LowerA64/Prologue.lean`.

`prologue_body_seg`: `prologue_seg_ofW` (the frame record's push, the stack
check against the thread's limit, the frame's allocation) for a function
without parameters, from the function's label to `bodyN` at the body's
entry: the saved `%rbp` is the entry's `%rbp` and the saved return address
the entry's top cell (`FrJ`), and the source's node invariant holds of any
cells (a body whose environment places no word in a cell, as `main`'s
`[(arg, unit, [])]`), the source control reached locally from the ghost
`c0`.

Where x86-64 differs from AArch64:
- the prologue runs at offsets from the entry `%rsp` (region `R`, the
  return address in cell `0`, the saved `%rbp` in cell `-8`), the body at
  `%rbp`-based offsets (`oB`); the body's region is `R` rebased at the frame
  record (`rbR R`, `8` lower), and `at_rbR` moves a node across (the cells
  shifted by `8`, `shSl`);
- the return address is a cell of the region, not a register: the entry's
  `σ.slot 0` is the ghost `ra`, and the region reaches the entry's top
  cell (`hhi : 8 ≤ R.hi`);
- the cells' sizes of the prologue (`zl zf z1 z2 zs`) are parameters;
- no region alignment hypothesis and no frame bound beyond `2 ^ 31` (the
  x86-64 prologue asks none).
-/
import Spike.Lib.LowerX64.Node
import Spike.Lib.X64CodeSegs

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow (prologueIn prologue_seg_ofW XProW xStSlots xS1)
open Scc.Lower.InvX64
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.Form (SEnv)
open Spike.Lib.LowerNode

set_option linter.unusedSimpArgs false

/-! ## The body's region -/

/-- **The body's region**: the prologue's region `R` (based at the entry
`%rsp`) rebased at the frame record (`%rbp`, `8` lower). -/
def rbR (R : Region) : Region := R.callee (-8) (R.lo + 8) (R.hi + 8)

theorem rbR_addr (R : Region) (k : Int) : (rbR R).addr k = R.addr (-8 + k) :=
  Region.callee_addr R _ _ _ k

theorem rbR_ok {R : Region} (hR : R.OK) (hlo : R.lo ≤ -8) (hhi : 0 ≤ R.hi) : (rbR R).OK :=
  Region.callee_ok hR (by omega) (by omega) (by omega) (by omega)

/-- The rebased region covers the same bytes: a frame condition stable
under the one is stable under the other. -/
theorem rbR_fstable {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -8) (hhi : 0 ≤ R.hi)
    (hF : FStable R F) : FStable (rbR R) F := by
  intro m m' h hd
  refine hF m m' h fun a ha hout => hd a ha ?_
  have hb := Region.callee_base (hi' := R.hi + 8) hR (kc := -8) (lo' := R.lo + 8) (by omega) (by omega)
    (by omega)
  simp only [rbR, Region.callee] at hb ⊢
  omega

/-- The cells seen from the frame record: cell `k` is the entry's `-8 + k`. -/
def shSl (sl : Int → BitVec 64) : Int → BitVec 64 := fun k => sl (-8 + k)

section Shift

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **A node at the frame's offsets is one at the body's**, in the rebased
region, its cells shifted (`shSl`): any offsets with `%rsp` at the frame's
base and `%rbp` at the saved `%rbp` (`-8`), as the prologue's exit `oF`. -/
theorem at_rbR {fr : Scc.Emit.X64.Frame} {o : SO} (hsp : o.sp = -8 - (fr.size : Int))
    (hbp : o.get .rbp = some (-8)) {pc : Int64}
    {J J' : AS → Ctl → Prop} (hJ : ∀ σ c, J σ c → J' { σ with slot := shSl σ.slot } c) {s : State} {c : Ctl}
    (h : At exe endPc R F ⟨pc, o, J⟩ s c) :
    At exe endPc (rbR R) F ⟨pc, oB fr, J'⟩ s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJσ⟩ := h
  refine ⟨he, hn, hdc, hpc, { σ with slot := shSl σ.slot }, ⟨hA.regs, hA.zmms, hA.status, ?_, ?_⟩, hD,
    hJ _ _ hJσ⟩
  · intro r k hk
    simp only [oB, SO.get, lk] at hk
    split at hk
    · rename_i hr
      subst hr
      cases hk
      have := hA.so .rsp o.sp (by simp [SO.get])
      rw [this, rbR_addr, hsp]
      congr 1
    · split at hk
      · rename_i hr hb
        subst hb
        cases hk
        have := hA.so .rbp (-8) hbp
        rw [this, rbR_addr, Int.add_zero]
      · cases hk
  · intro k hk
    obtain ⟨h8, hl, hh⟩ := hk
    simp only [rbR, Region.callee] at hl hh
    obtain ⟨j, hj, hv⟩ := hA.slot (-8 + k) ⟨by omega, by omega, by omega⟩
    exact ⟨j, by rw [rbR_addr]; exact hj, hv⟩

/-- **A node of the rebased region is one of the entry's**, back at the
entry's offsets (`8` lower), its cells unshifted: the body's exits seen by
the caller (the return's `⟨16, []⟩` is `⟨8, []⟩` from the entry `%rsp`, past
the return address). -/
theorem at_of_rbR {sp : Int} {pc : Int64} {J J' : AS → Ctl → Prop}
    (hJ : ∀ σ c, J { σ with slot := shSl σ.slot } c → J' σ c) {s : State} {c : Ctl}
    (h : At exe endPc (rbR R) F ⟨pc, ⟨sp, []⟩, J⟩ s c) :
    At exe endPc R F ⟨pc, ⟨sp - 8, []⟩, J'⟩ s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJσ⟩ := h
  refine ⟨he, hn, hdc, hpc, { σ with slot := fun k => σ.slot (k + 8) },
    ⟨hA.regs, hA.zmms, hA.status, ?_, ?_⟩, hD, hJ _ _ ?_⟩
  · intro r k hk
    simp only [SO.get, lk] at hk
    split at hk
    · rename_i hr
      subst hr
      cases hk
      have := hA.so .rsp sp (by simp [SO.get])
      rw [this, rbR_addr]
      congr 1
      omega
    · cases hk
  · intro k hk
    obtain ⟨h8, hl, hh⟩ := hk
    obtain ⟨j, hj, hv⟩ := hA.slot (k + 8) ⟨by omega, by simp only [rbR, Region.callee]; omega,
      by simp only [rbR, Region.callee]; omega⟩
    refine ⟨j, ?_, hv⟩
    rw [rbR_addr] at hj
    rwa [show -8 + (k + 8) = k by omega] at hj
  · have he : { σ with slot := shSl fun k => σ.slot (k + 8) } = σ := by
      obtain ⟨r, z, st, sl⟩ := σ
      simp only [AS.mk.injEq, true_and]
      funext k
      show sl (-8 + k + 8) = sl k
      rw [show -8 + k + 8 = k by omega]
    rw [he]
    exact hJσ

end Shift

/-! ## The prologue -/

section Pro

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)}
  {endPc : Int64} {R : Region} {F : MachineData → Prop} {W : Frag isa} {K : State → State → Prop}

/-- **A parameterless function's prologue is one segment** in any valid
layout of cells with `prologueIn` at the frame `fr.size`: from the
function's label (`%rsp` at 0, region `R`) to the body's node at its entry
(region `rbR R`), the ghosts `fp`/`ra` the entry's `%rbp` and top cell. -/
theorem prologue_body_seg {fr : Scc.Emit.X64.Frame} (h1 : fr.size ≤ 2 ^ 31)
    {kp : Nat} (hp : Lays exe cells kp)
        (hend : endPc = endOf exe cells kp) {fn sc entry : Label} {lim : Int64} {L : Label}
    {zl zf z1 z2 zs : Nat}
    (hin : prologueIn cells fn sc entry (Int64.ofInt fr.size) lim L zl zf z1 z2 zs [] = true)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -8 - (fr.size : Int)) (hhi : 8 ≤ R.hi)
    {J : AS → Ctl → Prop} {fp ra : BitVec 64} {c0 : Ctl} {t : Expr} {s : SEnv}
    (hW : XProW W K exe endPc R F ms ((_root_.Executable.labels exe).label fn) (Int64.ofInt fr.size) lim L
      zl zf z1 z2 zs [] J)
    (hedge : ∀ σ c, J σ c →
      (ms.rt (σ.regs.fsBase.toBitVec + lim.toBitVec).toNat ∧
        ms.mp ⟨σ.regs.fsBase.toBitVec + lim.toBitVec, 8⟩ false ∧
        (∀ m, F m → Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + lim.toBitVec) 8 = none) ∧
        ∀ v : Val, ms.G ⟨σ.regs.fsBase.toBitVec + lim.toBitVec, 8⟩ v →
          (v.setWidth 64).toNat ≤ (σ.regs.rsp.toBitVec - 8#64 - (Int64.ofInt fr.size).toBitVec).toNat) ∧
      σ.regs.rbp.toBitVec = fp ∧ σ.slot 0 = ra ∧ (∀ sl, NJ p lbl (rsOf fr) t s sl c) ∧ LocalRun p c0 c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label fn, ⟨0, []⟩, J⟩)
      (At exe endPc (rbR R) F (bodyN p lbl fr fp ra c0 ((_root_.Executable.labels exe).label entry) t s)) := by
  have hZ : (Int64.ofInt fr.size).toInt = fr.size := toInt_ofInt_small (by omega) (by omega)
  refine (prologue_seg_ofW (nb := ⟨(_root_.Executable.labels exe).label entry,
      Spike.Lib.X64.Flow.oF (Int64.ofInt fr.size), fun σ c =>
        (bodyN p lbl fr fp ra c0 ((_root_.Executable.labels exe).label entry) t s).J
          { σ with slot := shSl σ.slot } c⟩)
    hp hend hin (by rw [hZ]; omega) hF hR (by rw [hZ]; exact hlo) (by omega) (by simp) rfl
    (by simp [SO.le, lk]) hW fun σ c hJ => ?_).mono_post fun _ _ h =>
      at_rbR (by show -8 - _ = _; rw [hZ]) (by simp [SO.get, lk]) (fun _ _ h => h) h
  obtain ⟨⟨hrt, hmp, hld, hG⟩, hfp, hra, hN, hc0⟩ := hedge σ c hJ
  refine ⟨hrt, hmp, hld, fun v hv => ⟨hG v hv, fun σ' _ hsl => ⟨hN _, ?_, hc0⟩⟩⟩
  simp only [xStSlots] at hsl
  constructor <;> simp [shSl, hsl, xS1, upd_apply, hfp, hra]

end Pro

end Spike.Lib.LowerX64
