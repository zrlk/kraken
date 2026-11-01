/-
**A store's writes' obligation (`NoWrC`), generic, and its instances at
`wc_rodata`'s two exchange stores** (hello.w, AArch64). A store `str Xt, [Xn, #i]` writes only the word at its
address (`AllocG.nodeW_wr_st`); `NoWrC` holds once that word is not the
counter and is either `ArenaW` at every control a frame run reaches or in
the context `Ctx`. The two routes:

- a word inside a placed label's range (`ArenaW`'s third disjunct), not the
  counter by the label's place inside the arena (`LblArena`) and the
  counter's outside it (`Arena.OK.ctr_out`): `wc_rodata`'s exchange stores
  into rodata's buffer (`rdPostW_WSH` premises `hwr1`, `hwr2`);
- the context `Ctx`: the box's store at `wc_main`'s `.sp0` (the premise
  `hwr` of `WcWfS.wcSp0W_WSH`), whose cell lies at the counter's old value or
  above it, so not in `ArenaW`; wake discharges its twin through `StAt`
  (`WakePh.Land.hwr_R`), hello's instance is `Land3`'s.

- `nodeW_wrC_stW`: the generic lemma (either route per state).
- `wrOk_of_lbl`: a word in a placed label's range is not the counter and is
  `ArenaW` at every control.
- `lblIn_of_valRep`: a source location's word inside its label's range, from
  its representation and offset.
- `InArL`, `wrOk_of_in`: a word in the range of one placed label that lies
  inside the arena (no `LblArena` over every label: main's TCB label is
  placed by `scc_rt_alloc_tcb`, not by the arena), not the counter and
  `ArenaW`.
- `lblIn_buf`: rodata's buffer element `i < n` in the range of its label
  landed with `n` words.
- `inArL_buf`: the same with the label inside the arena (`hin`'s discharge,
  from the exchange's `ValRep`, `Fresh2H`'s `AllocLand` and `n = 2`).
- `nodeW_wrC_stL`, `nodeW_wrC_stI`: the label route at a node (with
  `LblArena`; with `InArL`).
- `nodeW_wrC_rdX1`, `nodeW_wrC_rdX2`: the instances at `HelloRd.pN .x1`,
  `.x2` (`hwr1`, `hwr2`).

No absolute address appears in this file.
-/
import Spike.Lib.A64HelloRodata
import Spike.Lib.A64HelloPh
import Spike.Lib.A64WakeWfW
import Spike.Lib.LblArena

namespace Spike.Lib.A64.HelloPh.XchgWr

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Range lrange)
open Spike.Lib (Arena FragS FrameRun LblArena)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerA (ArenaW WrAt)
open Spike.Lib.A64.Flow (NodeW ND At strDir rAddr)
open Spike.Lib.A64.Rt (InstOk RuntimeLayout)
open Spike.Lib.A64.WakeWf (NoWrC)
open Scc.Cert.Rt.A64 (blockAt)

variable {ar : Arena} {p : Prog} {lbl : Lbl} {lsize : Lsize} {Ctx : FragS isaLSE2} {fs : List TermRun.Frame}

section Gen

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}
  {prog : List Directive} {lab : Label → Int64} {μ' : Scc.Sem.Marks} {own' : Spike.Lib.A64Consumer.Own}
  {Tk : State → Prop} {K' : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}

/-- **A store** `str Xt, [Xn, #i]` of a word unmapped in private memory
(`ha`) has `NoWrC` when at every state of the node (`hok`) its word is not
the counter and is either `ArenaW` at every control a frame run from the
state's reaches or in the context `Ctx`. -/
theorem nodeW_wrC_stW (hI : InstOk exe endPc prog lab μ' own' Tk K' okPc ph kp) {n : ND} {t rb : XReg}
    {i : Int64} {l : Label} {k : Nat} {q : Int64} (hb : blockAt prog l k [strDir t rb i] = true)
    (he : lab l + Int64.ofNat (4 * k) = q) (hp : n.pc = q)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (rAddr σ.regs rb i) 8 = none)
    (hok : ∀ s c, At exe endPc R F n s c → ∀ σ, n.J σ c → F s.st.1 →
      (⟨rAddr σ.regs rb i, 8⟩ : Loc) ≠ ar.ctrLoc ∧
      ((∀ c' fs', FrameRun p (c, fs) (c', fs') → ArenaW ar lbl lsize c' ⟨rAddr σ.regs rb i, 8⟩) ∨
        Ctx s c fs)) :
    NodeW (NoWrC ar p lbl lsize Ctx fs) (fun _ _ => False) exe endPc R F n := fun s c hA => by
  obtain ⟨σ, hJ, hF, hw⟩ := (Spike.Lib.A64.AllocG.nodeW_wr_st hI hb he hp ha s c hA).1
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

/-- **A word in a placed label's range** is not the counter (the label
inside the arena, `LblArena`; the counter outside it, `Arena.OK`) and is
`ArenaW` at every control. -/
theorem wrOk_of_lbl (har : ar.OK) (hLA : LblArena ar lbl lsize) {A : BitVec 64}
    (h : ∃ l b, lbl l = some b ∧ (lrange lsize l b).contains A.toNat) :
    (⟨A, 8⟩ : Loc) ≠ ar.ctrLoc ∧ ∀ c, ArenaW ar lbl lsize c ⟨A, 8⟩ :=
  let ⟨l, b, hl, hc⟩ := h
  wrOk_of_in har ⟨l, b, hl, hLA l b hl, hc⟩

/-- **A source location's word is in its label's range** when it
represents the location (`ValRep`) at an offset below the label's size. -/
theorem lblIn_of_valRep {sa : WeakMem.Address} {v : Nat} (h : Scc.Sem.ValRep lbl (.loc sa 0) v)
    (hs : sa.offset < lsize sa.label) : ∃ l b, lbl l = some b ∧ (lrange lsize l b).contains v := by
  obtain ⟨-, x, hx, hv⟩ := h
  simp only [Scc.Sem.wordAddr] at hx
  cases hb : lbl sa.label with
  | none => simp [hb] at hx
  | some b =>
    rw [hb, Option.map_some, Option.some.injEq] at hx
    refine ⟨sa.label, b, hb, ?_⟩
    subst hv hx
    simp only [lrange, Range.contains]
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left hs (by decide)) _⟩

/-- **A buffer element's word is in its label's range** (`hin`'s discharge
at `wc_rodata`'s exchanges): the element `offs ⟨l, 0⟩ i` of the label `l`
the allocation landed with `n` words (`msOfA`'s `xa`, sizes `updN ls0 l n`;
rodata's `newBuf` of `m = 2` one-word lanes, `rdCN_newBuf`, so `n = 2`),
`i < n` (`i = 0, 1`: `rdCA_store`, `rdC2_store`). -/
theorem lblIn_buf {ls0 : Lsize} {l : WeakMem.AllocLabel} {n i v : Nat}
    (h : Scc.Sem.ValRep lbl (.loc (TermRun.offs ⟨l, 0⟩ i) 0) v) (hi : i < n) :
    ∃ l0 b0, lbl l0 = some b0 ∧ (lrange (Spike.Lib.A64ConsumerA.updN ls0 l n) l0 b0).contains v :=
  lblIn_of_valRep h (by simp [TermRun.offs, Spike.Lib.A64ConsumerA.updN, hi])

/-- **A buffer element's word in its label's range, the label inside the
arena** (`InArL`, `hin`'s discharge at `wc_rodata`'s exchanges without
`LblArena`): `l` placed at `b` (`hl`; `upd L0 l b` at `l`) where the arena
hands out `n` words (`hb`, `Fresh2H`'s `AllocLand`), sized `n` (`hn`;
`updN ls0 l n` at `l`), the element `i < n`. -/
theorem inArL_buf {l : WeakMem.AllocLabel} {b n i v : Nat}
    (h : Scc.Sem.ValRep lbl (.loc (TermRun.offs ⟨l, 0⟩ i) 0) v) (hi : i < n) (hl : lbl l = some b)
    (hb : Spike.Lib.HeapLand.AllocLand ar.heap ar.cells b n) (hn : lsize l = n) : InArL ar lbl lsize v := by
  obtain ⟨-, x, hx, hv⟩ := h
  simp only [Scc.Sem.wordAddr, TermRun.offs, hl, Option.map_some, Option.some.injEq] at hx
  subst hv hx
  refine ⟨l, b, hl, ⟨hb.1, hn ▸ hb.2.1⟩, ?_⟩
  simp only [lrange, Range.contains, hn, Nat.zero_add]
  exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left hi (by decide)) _⟩

section Lbl

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}
  {prog : List Directive} {lab : Label → Int64} {μ' : Scc.Sem.Marks} {own' : Spike.Lib.A64Consumer.Own}
  {Tk : State → Prop} {K' : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}

/-- **A store into a placed label's range** (`hin`) of a word unmapped in
private memory (`ha`) has `NoWrC`, the arena `OK` and the placement inside
it (`har`, `hLA`). -/
theorem nodeW_wrC_stL (hI : InstOk exe endPc prog lab μ' own' Tk K' okPc ph kp) {n : ND} {t rb : XReg}
    {i : Int64} {l : Label} {k : Nat} {q : Int64} (hb : blockAt prog l k [strDir t rb i] = true)
    (he : lab l + Int64.ofNat (4 * k) = q) (hp : n.pc = q)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (rAddr σ.regs rb i) 8 = none)
    (har : ar.OK) (hLA : LblArena ar lbl lsize)
    (hin : ∀ σ c, n.J σ c → ∃ l0 b0, lbl l0 = some b0 ∧ (lrange lsize l0 b0).contains (rAddr σ.regs rb i).toNat) :
    NodeW (NoWrC ar p lbl lsize Ctx fs) (fun _ _ => False) exe endPc R F n :=
  nodeW_wrC_stW hI hb he hp ha fun _ c _ σ hJ _ =>
    let h := wrOk_of_lbl har hLA (hin σ c hJ)
    ⟨h.1, .inl fun c' _ _ => h.2 c'⟩

/-- **A store into a placed label's range, that label inside the arena**
(`hin`, `InArL`) of a word unmapped in private memory (`ha`) has `NoWrC`,
the arena `OK` (`har`); `nodeW_wrC_stL` without `LblArena`. -/
theorem nodeW_wrC_stI (hI : InstOk exe endPc prog lab μ' own' Tk K' okPc ph kp) {n : ND} {t rb : XReg}
    {i : Int64} {l : Label} {k : Nat} {q : Int64} (hb : blockAt prog l k [strDir t rb i] = true)
    (he : lab l + Int64.ofNat (4 * k) = q) (hp : n.pc = q)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (rAddr σ.regs rb i) 8 = none) (har : ar.OK)
    (hin : ∀ σ c, n.J σ c → InArL ar lbl lsize (rAddr σ.regs rb i).toNat) :
    NodeW (NoWrC ar p lbl lsize Ctx fs) (fun _ _ => False) exe endPc R F n :=
  nodeW_wrC_stW hI hb he hp ha fun _ c _ σ hJ _ =>
    let h := wrOk_of_in har (hin σ c hJ)
    ⟨h.1, .inl fun c' _ _ => h.2 c'⟩

end Lbl

/-! ## `wc_rodata`'s exchange stores -/

section Rd

open Spike.Lib.A64.Flow.HelloRd (pN rpIn hello_rpIn)
open Spike.Lib.A64.Flow.Hello1 (rAddr_x10_x0)

variable {L : RuntimeLayout} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {Jp Jp' J1 J2 J2' J3 J4 J5 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop}
  (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo) (a : BitVec 64)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (har : ar.OK)

include hp hlo a hsite har

/-- **`wc_rodata`'s first exchange store** (`pN .x1`, `str x9, [x10]`) has
`NoWrC` (`rdPostW_WSH` premise `hwr1`): the buffer's first word
unmapped in private memory at every `.sp0` state (`hmem`, `BoxOkH`'s second
part) and in the range of a placed label inside the arena after the first
load (`hin`, `inArL_buf` at the exchange's `ValRep` of `offs ⟨l, 0⟩ 0`). -/
theorem nodeW_wrC_rdX1
    (hmem : ∀ σ0 c, Jp σ0 c → ∀ m, F m → Mem.loadInt m.dmem (rAddr σ0.regs .X0 0) 8 = none)
    (hin : ∀ σ0 c, J1 σ0 c → InArL ar lbl lsize (rAddr σ0.regs .X0 0).toNat) :
    NodeW (NoWrC ar p lbl lsize Ctx fs) (fun _ _ => False) L.exe L.endPc R F
      (pN L.lab Jp Jp' J1 J2 J2' J3 J4 J5 .x1) := by
  have h := hello_rpIn
  simp only [rpIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, bx1⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  exact nodeW_wrC_stI (instOkH hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)) (by rw [hp]; exact bx1) rfl rfl
    (fun σ c m ⟨σ0, ⟨c0, hJp⟩, _, _, _, hx⟩ hF => by rw [rAddr_x10_x0 hx]; exact hmem σ0 c0 hJp m hF) har
    (fun σ c ⟨σ0, _, hJ, _, _, hx⟩ => by rw [rAddr_x10_x0 hx]; exact hin σ0 c hJ)

/-- **`wc_rodata`'s second exchange store** (`pN .x2`, `str x9, [x10, #8]`)
has `NoWrC` (`rdPostW_WSH` premise `hwr2`), as `nodeW_wrC_rdX1` at
the buffer's second word after the second load. -/
theorem nodeW_wrC_rdX2
    (hmem : ∀ σ0 c, Jp σ0 c → ∀ m, F m → Mem.loadInt m.dmem (rAddr σ0.regs .X0 8) 8 = none)
    (hin : ∀ σ0 c, J3 σ0 c → InArL ar lbl lsize (rAddr σ0.regs .X0 8).toNat) :
    NodeW (NoWrC ar p lbl lsize Ctx fs) (fun _ _ => False) L.exe L.endPc R F
      (pN L.lab Jp Jp' J1 J2 J2' J3 J4 J5 .x2) := by
  have h := hello_rpIn
  simp only [rpIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, bx2⟩, -⟩, -⟩ := h
  exact nodeW_wrC_stI (instOkH hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)) (by rw [hp]; exact bx2) rfl rfl
    (fun σ c m ⟨σ0, ⟨c0, hJp⟩, _, _, _, hx⟩ hF => by rw [rAddr_x10_x0 hx]; exact hmem σ0 c0 hJp m hF) har
    (fun σ c ⟨σ0, _, hJ, _, _, hx⟩ => by rw [rAddr_x10_x0 hx]; exact hin σ0 c hJ)

end Rd

end Spike.Lib.A64.HelloPh.XchgWr

/-- info: 'Spike.Lib.A64.HelloPh.XchgWr.nodeW_wrC_stW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.XchgWr.nodeW_wrC_stW

/-- info: 'Spike.Lib.A64.HelloPh.XchgWr.wrOk_of_lbl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.XchgWr.wrOk_of_lbl

/-- info: 'Spike.Lib.A64.HelloPh.XchgWr.lblIn_of_valRep' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.XchgWr.lblIn_of_valRep

/-- info: 'Spike.Lib.A64.HelloPh.XchgWr.lblIn_buf' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.XchgWr.lblIn_buf

/-- info: 'Spike.Lib.A64.HelloPh.XchgWr.wrOk_of_in' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.XchgWr.wrOk_of_in

/-- info: 'Spike.Lib.A64.HelloPh.XchgWr.inArL_buf' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.XchgWr.inArL_buf

/-- info: 'Spike.Lib.A64.HelloPh.XchgWr.nodeW_wrC_stL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.XchgWr.nodeW_wrC_stL

/-- info: 'Spike.Lib.A64.HelloPh.XchgWr.nodeW_wrC_stI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.XchgWr.nodeW_wrC_stI

/-- info: 'Spike.Lib.A64.HelloPh.XchgWr.nodeW_wrC_rdX1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.XchgWr.nodeW_wrC_rdX1

/-- info: 'Spike.Lib.A64.HelloPh.XchgWr.nodeW_wrC_rdX2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.XchgWr.nodeW_wrC_rdX2
