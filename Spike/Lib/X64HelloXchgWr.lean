/-
**A store's writes' obligation (`NoWrC`), generic, and its instances at
`wc_rodata`'s two exchange stores** (hello.w, x86-64; the twin of
`Spike/Lib/A64HelloXchgWr.lean`). A store `movq %r, k(%b)` writes only the
word at its address (`AllocG.nodeW_wr_st`); `NoWrC` holds once that word is
not the counter and is either `ArenaW` at every control a frame run reaches
or in the context `Ctx`.

- `nodeW_wrC_stW`: the generic lemma (either route per state).
- `InArL`, `wrOk_of_in`: a word in the range of one placed label that lies
  inside the arena, not the counter and `ArenaW`.
- `nodeW_wrC_stI`: the label route at a node (with `InArL`).
- `nodeW_wrC_rdX1`, `nodeW_wrC_rdX2`: the instances at `HelloRd.pN .x1`,
  `.x2` (the premises `hwr1`, `hwr2` of `wc_rodata`'s post-return segment).

No absolute address appears in this file.

**Where this differs from AArch64**: the stores are `movq %rax, 0(%rcx)` at
`.Lwc_rodata.x0 + 29` and `movq %rax, 8(%rcx)` at `.x15 + 58` (A64:
`str x9, [x10]`, `str x9, [x10, #8]` at word offsets), located by
`blockAtB` on sized cells and a byte offset (A64: `blockAt` and `4 * k`);
the address is `bAddr σ.regs .rcx k`, rewritten to the buffer base `%rax`
of `.x15`'s state by `bAddr_rcx_rax` (A64: `rAddr_x10_x0`). `HelloRd.pN`
has no fence node, so it takes one invariant fewer (no `J5`). Only the
lemmas the hello proof uses are restated: A64's `wrOk_of_lbl`,
`lblIn_of_valRep`, `lblIn_buf`, `inArL_buf` and `nodeW_wrC_stL` are not.
-/
import Spike.Lib.X64HelloRodata
import Spike.Lib.X64HelloPh
import Spike.Lib.X64WakeWfN
import Spike.Lib.LblArena

namespace Spike.Lib.X64.HelloPh.XchgWr

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Range lrange)
open Spike.Lib (Arena FragS FrameRun)
open Spike.Lib.X64Consumer (Lbl Lsize Own)
open Spike.Lib.X64ConsumerA (ArenaW WrAt)
open Spike.Lib.X64 (NodeW ND At stDir bAddr)
open Spike.Lib.X64.Rt (InstOk RuntimeLayout)
open Spike.Lib.X64.WakeWf (NoWrC)
open Scc.Cert.Rt.X64 (blockAtB)

variable {ar : Arena} {p : Prog} {lbl : Lbl} {lsize : Lsize} {Ctx : FragS isa} {fs : List TermRun.Frame}

section Gen

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ' : Scc.Sem.Marks} {own' : Own}
  {Tk : State → Prop} {K' : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}

/-- **A store** `movq %r, k(%b)` of a word unmapped in private memory
(`ha`) has `NoWrC` when at every state of the node (`hok`) its word is not
the counter and is either `ArenaW` at every control a frame run from the
state's reaches or in the context `Ctx`. -/
theorem nodeW_wrC_stW (hI : InstOk exe endPc cells lab μ' own' Tk K' okPc ph kp) {n : ND} {b r : Reg64}
    {k : Int64} {z : Nat} {l : Label} {off : Nat} {q : Int64}
    (hb : blockAtB cells l off [(stDir b k r, z)] = true)
    (he : lab l + Int64.ofNat off = q) (hp : n.pc = q)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (bAddr σ.regs b k) 8 = none)
    (hok : ∀ s c, At exe endPc R F n s c → ∀ σ, n.J σ c → F s.st.1 →
      (⟨bAddr σ.regs b k, 8⟩ : Loc) ≠ ar.ctrLoc ∧
      ((∀ c' fs', FrameRun p (c, fs) (c', fs') → ArenaW ar lbl lsize c' ⟨bAddr σ.regs b k, 8⟩) ∨
        Ctx s c fs)) :
    NodeW (NoWrC ar p lbl lsize Ctx fs) (fun _ _ => False) exe endPc R F n := fun s c hA => by
  obtain ⟨σ, hJ, hF, hw⟩ := (Spike.Lib.X64.AllocG.nodeW_wr_st hI hb he hp ha s c hA).1
  obtain ⟨hne, hor⟩ := hok s c hA σ hJ hF
  refine ⟨⟨fun c' fs' hr L hL _ => ?_, fun hc => (hne (hw _ hc).symm).elim⟩, fun _ h => h⟩
  rw [hw L hL]
  rcases hor with h | h
  · exact .inl (h c' fs' hr)
  · exact .inr ⟨h, fun hc => hne (hw _ hc).symm⟩

end Gen

/-- A word in the range of a placed label `l` at `b`, `l`'s words inside the
arena. -/
def InArL (ar : Arena) (lbl : Lbl) (lsize : Lsize) (A : Nat) : Prop :=
  ∃ l b, lbl l = some b ∧ (ar.heap + 8 ≤ b ∧ b + 8 * lsize l ≤ ar.heap + 16 * ar.cells) ∧
    (lrange lsize l b).contains A

/-- **A word in the range of a placed label inside the arena** (`InArL`;
only that label's place, not every label's) is not the counter (the
counter outside the arena, `Arena.OK`) and is `ArenaW` at every control. -/
theorem wrOk_of_in (har : ar.OK) {A : BitVec 64} (h : InArL ar lbl lsize A.toNat) :
    (⟨A, 8⟩ : Loc) ≠ ar.ctrLoc ∧ ∀ c, ArenaW ar lbl lsize c ⟨A, 8⟩ := by
  obtain ⟨l, b, hl, hA, hc⟩ := h
  refine ⟨fun e => ?_, fun _ => .inr (.inr (.inl ⟨l, b, hl, hc⟩))⟩
  have ha : A = BitVec.ofNat 64 ar.ctr := congrArg Loc.addr e
  have hn : A.toNat = ar.ctr := by rw [ha, BitVec.toNat_ofNat, Nat.mod_eq_of_lt har.ctr_lt]
  simp only [lrange, Range.contains] at hc
  exact har.ctr_out ⟨by omega, by omega⟩

section Lbl

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ' : Scc.Sem.Marks} {own' : Own}
  {Tk : State → Prop} {K' : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}

/-- **A store into a placed label's range, that label inside the arena**
(`hin`, `InArL`) of a word unmapped in private memory (`ha`) has `NoWrC`,
the arena `OK` (`har`). -/
theorem nodeW_wrC_stI (hI : InstOk exe endPc cells lab μ' own' Tk K' okPc ph kp) {n : ND} {b r : Reg64}
    {k : Int64} {z : Nat} {l : Label} {off : Nat} {q : Int64}
    (hb : blockAtB cells l off [(stDir b k r, z)] = true)
    (he : lab l + Int64.ofNat off = q) (hp : n.pc = q)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (bAddr σ.regs b k) 8 = none) (har : ar.OK)
    (hin : ∀ σ c, n.J σ c → InArL ar lbl lsize (bAddr σ.regs b k).toNat) :
    NodeW (NoWrC ar p lbl lsize Ctx fs) (fun _ _ => False) exe endPc R F n :=
  nodeW_wrC_stW hI hb he hp ha fun _ c _ σ hJ _ =>
    let h := wrOk_of_in har (hin σ c hJ)
    ⟨h.1, .inl fun c' _ _ => h.2 c'⟩

end Lbl

/-! ## `wc_rodata`'s exchange stores -/

section Rd

open Spike.Lib.X64.Flow.HelloRd (pN rpIn hello_rpIn)
open Spike.Lib.X64.Flow.Hello1 (bAddr_rcx_rax)

variable {L : RuntimeLayout} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {Jp Jp' J1 J2 J2' J3 J4 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop}
  (hp : L.prog = SccCode.helloCells) (hlo : L.Λ.code.lo = lo) (a : BitVec 64)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (har : ar.OK)

include hp hlo a hsite har

/-- **`wc_rodata`'s first exchange store** (`pN .x1`, `movq %rax, 0(%rcx)`)
has `NoWrC` (the premise `hwr1`): the buffer's first word unmapped in
private memory at every `.x15` state (`hmem`) and in the range of a placed
label inside the arena after the first load (`hin`). -/
theorem nodeW_wrC_rdX1
    (hmem : ∀ σ0 c, Jp σ0 c → ∀ m, F m → Mem.loadInt m.dmem (bAddr σ0.regs .rax 0) 8 = none)
    (hin : ∀ σ0 c, J1 σ0 c → InArL ar lbl lsize (bAddr σ0.regs .rax 0).toNat) :
    NodeW (NoWrC ar p lbl lsize Ctx fs) (fun _ _ => False) L.exe L.endPc R F
      (pN L.lab Jp Jp' J1 J2 J2' J3 J4 .x1) := by
  have h := hello_rpIn
  simp only [rpIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, bx1⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  exact nodeW_wrC_stI (instOkH hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)) (by rw [hp]; exact bx1) rfl rfl
    (fun σ c m ⟨σ0, ⟨c0, hJp⟩, _, _, _, hx⟩ hF => by rw [bAddr_rcx_rax hx]; exact hmem σ0 c0 hJp m hF) har
    (fun σ c ⟨σ0, _, hJ, _, _, hx⟩ => by rw [bAddr_rcx_rax hx]; exact hin σ0 c hJ)

/-- **`wc_rodata`'s second exchange store** (`pN .x2`,
`movq %rax, 8(%rcx)`) has `NoWrC` (the premise `hwr2`), as `nodeW_wrC_rdX1`
at the buffer's second word after the second load. -/
theorem nodeW_wrC_rdX2
    (hmem : ∀ σ0 c, Jp σ0 c → ∀ m, F m → Mem.loadInt m.dmem (bAddr σ0.regs .rax 8) 8 = none)
    (hin : ∀ σ0 c, J3 σ0 c → InArL ar lbl lsize (bAddr σ0.regs .rax 8).toNat) :
    NodeW (NoWrC ar p lbl lsize Ctx fs) (fun _ _ => False) L.exe L.endPc R F
      (pN L.lab Jp Jp' J1 J2 J2' J3 J4 .x2) := by
  have h := hello_rpIn
  simp only [rpIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, bx2⟩, -⟩ := h
  exact nodeW_wrC_stI (instOkH hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)) (by rw [hp]; exact bx2) rfl rfl
    (fun σ c m ⟨σ0, ⟨c0, hJp⟩, _, _, _, hx⟩ hF => by rw [bAddr_rcx_rax hx]; exact hmem σ0 c0 hJp m hF) har
    (fun σ c ⟨σ0, _, hJ, _, _, hx⟩ => by rw [bAddr_rcx_rax hx]; exact hin σ0 c hJ)

end Rd

end Spike.Lib.X64.HelloPh.XchgWr

/-- info: 'Spike.Lib.X64.HelloPh.XchgWr.nodeW_wrC_stW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.XchgWr.nodeW_wrC_stW

/-- info: 'Spike.Lib.X64.HelloPh.XchgWr.wrOk_of_in' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.XchgWr.wrOk_of_in

/-- info: 'Spike.Lib.X64.HelloPh.XchgWr.nodeW_wrC_stI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.XchgWr.nodeW_wrC_stI

/-- info: 'Spike.Lib.X64.HelloPh.XchgWr.nodeW_wrC_rdX1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.XchgWr.nodeW_wrC_rdX1

/-- info: 'Spike.Lib.X64.HelloPh.XchgWr.nodeW_wrC_rdX2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.XchgWr.nodeW_wrC_rdX2
