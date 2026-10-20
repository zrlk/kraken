/-
The **fence-released MP writer**: the program, the event trees
of its cells, and its resource invariant for a `ThreadRuleRXG (GHyb rel)`
(`SLR/FenceWRule.lean`).

```
 fwriterMp:
 0   mov  w2, #1
 1   mov  w3, #1
 2   str  w2, [x1]      // data := 1 (plain)
 3   dmb  ish           // fence .sy
 4   str  w3, [x0]      // flag := 1 (plain, fence-released)
 5 done_w:
```
This is `PromisePureFTests.fwriter` with the data value `1` instead
of `42`: the MP reader side (`Mp.flagPred`/`Mp.Good`, `Mp.mpGhost`,
`Mp.mpRuleR`, `Mp.mp_final`) is stated for the published value `1`, and the
whole reader proof is reused unchanged. The end of the text is position `6`,
which shares its address with the label `done_w` (position `5`).

The resources are those of the existing MP writer (`SLR/MpInv.lean`: `Own0`,
`Own1`, `Prepaid`, `WorldW`, the flag's predicate `φ`); the differences are
the positions and, at the flag store (position 4), the fact
`Views.FenceRel` (set by `dmb ish`, kept by the environment and by
prepayments, which do not touch the thread's views). The flag store is plain,
so a release split happens at a plain store: the erasure rules
(`EvTree.eraseWPR_store_rel`, `Erase.fresh_of_impure`) are agnostic of the
store kind, and the timestamp bound `vwOld < tw` that `stlr` gets from its
pre-view comes here from `FenceRel` (`FenceW.writeSuccs_fresh_vwOld_F`,
`writeSuccs_relF_relPre`).
-/
import Kraken.Promising.SLR.MpWriter
import Kraken.Promising.FenceRelease

namespace Kraken.Promising.SLR.FenceW

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.Mp
open Kraken.Promising.SLR.A64Trees (At goto next_pc addrOf_label)

/-- The fence-released MP writer: data `:= 1` (plain), `dmb ish`, flag `:= 1`
(plain). -/
def fwriterMp : Program := parseAArch64("
    mov w2, #1
    mov w3, #1
    str w2, [x1]
    dmb ish
    str w3, [x0]
done_w:
")

/-- info: 6 -/
#guard_msgs in
#eval fwriterMp.length

variable [layout : _root_.Layout]

/-! ## The cells -/

section Cells

variable [hw : Executable.ValidLayout (layout fwriterMp)]

/-- The end of the text (position 6) is the address of `done_w` (position 5). -/
theorem f_addr_6 : (layout fwriterMp).addrOf 6 = (layout fwriterMp).addrOf 5 :=
  addrOf_label (i := 5) (l := "done_w") rfl

/-- Read the writer's cell at position `i` (as `MpTrees.wcell`). -/
local macro "fcell" h:ident i:num "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  have hc := Kraken.Executable.codeAt_addrOf (p := fwriterMp) (i := $i)
    (d := fwriterMp[$i]) (by decide) (by decide)
  rw [← ($h).pc] at hc
  generalize hd : fwriterMp[$i] = d at hc
  simp only [fwriterMp, List.getElem_cons_succ, List.getElem_cons_zero] at hd
  subst hd
  rw [exec_eq_of_codeAt ($h).exe ($h).decls ($h).ne hc]
  simp only [Directive.interp, Instr.interp, Operation.interp, ConstExpr.evalBranchTarget,
    ConstExpr.interp]
  simp [goto, toEv, RegOrSp.interpBase, MachineData.rmwK, MachineData.loadK,
    MachineData.storeK, MachineData.load, MachineData.store, EvTree.access_empty, EvTree.map,
    AddrOrLit.interpLoad, AddrExpr.interpLoad, AddrExpr.interpStore, AddrExpr.checkSPAlignment,
    AddrExpr.eval, MachineData.setRegOrZr, MachineData.setRegOrSp, Reg64s.getRegOrSp,
    Reg64s.getRegOrSp64, RegOrSp.base, RegOrZr.base, RegOrZr.isZr, Reg64s.getXReg, $ts,*]))

/-- `mov w2, #1` (position 0): silent, `X2 := 1`. -/
theorem exec_f_mov2 (st : State) (h : At fwriterMp st 0) :
    isa.exec st = some (.done (goto st
      { st.st.1 with regs := st.st.1.regs.setXReg .X2 1#64 } ((layout fwriterMp).addrOf 1))) := by
  rw [next_pc h (by decide)]
  fcell h 0 []

/-- `mov w3, #1` (position 1): silent, `X3 := 1`. -/
theorem exec_f_mov3 (st : State) (h : At fwriterMp st 1) :
    isa.exec st = some (.done (goto st
      { st.st.1 with regs := st.st.1.regs.setXReg .X3 1#64 } ((layout fwriterMp).addrOf 2))) := by
  rw [next_pc h (by decide)]
  fcell h 1 []

/-- `str w2, [x1]` (position 2): a plain store of `X2`'s low word to the data
word. -/
theorem exec_f_str (st : State) (h : At fwriterMp st 2) {d : BitVec 64}
    (hx1 : st.st.1.regs.X1.toBitVec = d) (hdd : Mem.loadInt st.st.1.dmem d 4 = none) :
    isa.exec st = some (.store .plain false ⟨d, 4⟩
      (BitVec.setWidth 128 (BitVec.setWidth 32 st.st.1.regs.X2.toBitVec))
      fun _ => .done (goto st st.st.1 ((layout fwriterMp).addrOf 3))) := by
  rw [next_pc h (by decide)]
  fcell h 2 [hx1, hdd]

/-- `dmb ish` (position 3): a full fence. -/
theorem exec_f_dmb (st : State) (h : At fwriterMp st 3) :
    isa.exec st = some (.fence .sy fun _ => .done (goto st st.st.1 ((layout fwriterMp).addrOf 4))) := by
  rw [next_pc h (by decide)]
  fcell h 3 []

/-- `str w3, [x0]` (position 4): a plain store of `X3`'s low word to the
flag. -/
theorem exec_f_strf (st : State) (h : At fwriterMp st 4) {f : BitVec 64}
    (hx0 : st.st.1.regs.X0.toBitVec = f) (hdf : Mem.loadInt st.st.1.dmem f 4 = none) :
    isa.exec st = some (.store .plain false ⟨f, 4⟩
      (BitVec.setWidth 128 (BitVec.setWidth 32 st.st.1.regs.X3.toBitVec))
      fun _ => .done (goto st st.st.1 ((layout fwriterMp).addrOf 5))) := by
  rw [next_pc h (by decide)]
  fcell h 4 [hx0, hdf]

end Cells

/-! ## Frame, phases, invariant -/

/-- The writer's frame (`Mp.FrameW` for `fwriterMp`). -/
structure FrameF (P : Params) (st : State) : Prop where
  exe : st.exe = layout fwriterMp
  decls : st.decls = {}
  endPc : st.endPc = (layout fwriterMp).addrOf 6
  x0 : st.st.1.regs.X0.toBitVec = P.f
  x1 : st.st.1.regs.X1.toBitVec = P.d
  df : Mem.loadInt st.st.1.dmem P.f 4 = none
  dd : Mem.loadInt st.st.1.dmem P.d 4 = none

/-- The writer's phase at each position (`x2`, `x3`: the low words of `X2`,
`X3`). At the flag store (position 4) the views are fence-released. -/
def PhaseF (P : Params) (i : Nat) (x2 x3 : BitVec 32) (vs : Views) (r : Res) : Prop :=
  match i with
  | 0 => Own0 P r
  | 1 => Own0 P r ∧ x2 = 1
  | 2 => Own0 P r ∧ x2 = 1 ∧ x3 = 1
  | 3 => Own1 P vs r ∧ x3 = 1
  | 4 => (Own1 P vs r ∨ Prepaid P r) ∧ x3 = 1 ∧ vs.FenceRel
  | 5 => 1 ≤ (r.wr P.W).q
  | _ => False

/-- A prepaid writer (position 4 without `Dt`) has the flag promise
outstanding. -/
def PrepaidPromF (P : Params) (tid : Nat) (i : Nat) (t : Thread isa) (m : Memory) (r : Res) : Prop :=
  i = 4 → (r.wr P.Dt).q = 0 → ∃ ts ∈ t.prom, m.get? ts = some ⟨P.Fl, 1#128, tid⟩

/-- **The writer's invariant** (the analogue of `Mp.InvW`). -/
def InvF (P : Params) (tid : Nat) (_cl : Prop) (c : Config isa) (r : Res) (g : Ghost) : Prop :=
  WorldW P g ∧ ∃ t, c.threads[tid]? = some t ∧ FrameF P t.st ∧
    ∃ i, AtPos fwriterMp t.st i ∧
      PhaseF P i (BitVec.setWidth 32 t.st.st.1.regs.X2.toBitVec)
        (BitVec.setWidth 32 t.st.st.1.regs.X3.toBitVec) t.views r ∧
      PrepaidPromF P tid i t c.mem r

/-- An own pending promise is the prepaid flag store: the writer is at
position 4, has given `Dt` away, and it is the only own pending promise. -/
def OwnPendF (P : Params) (tid : Nat) (c : Config isa) (r : Res) (g : Ghost) : Prop :=
  ∀ t, c.threads[tid]? = some t → ∀ ts ∈ t.prom, ts ∈ g.pend → AtPos fwriterMp t.st 4 ∧ (r.wr P.Dt).q = 0 ∧
    ∀ ts' ∈ t.prom, ts' ∈ g.pend → ts' = ts

/-- **The writer's instance invariant** (`InvXOf` shape). -/
def InvXF (P : Params) (tid : Nat) (cl : Prop) (c : Config isa) (r : Res) (g : Ghost) : Prop :=
  InvF P tid cl c r g ∧ PendIn g c.mem ∧ OwnPendF P tid c r g

/-! ## Plumbing -/

section Plumbing

variable [hw : Executable.ValidLayout (layout fwriterMp)]

omit hw in
/-- `FrameF` across a step that keeps `X0`, `X1` and the private memory. -/
theorem FrameF.goto {P : Params} {st : State} (h : FrameF P st) {m : MachineData} {pc : Int64}
    (h0 : m.regs.X0 = st.st.1.regs.X0) (h1 : m.regs.X1 = st.st.1.regs.X1) (hd : m.dmem = st.st.1.dmem) :
    FrameF P (A64Trees.goto st m pc) :=
  ⟨h.exe, h.decls, h.endPc, by simp [h0, h.x0], by simp [h1, h.x1], by simp [hd, h.df], by simp [hd, h.dd]⟩

/-- Distinct positions `≤ 5` have distinct addresses. -/
theorem addrOf_ne_f {k n : Nat} (hk : k < n) (hn : n ≤ 5) :
    (layout fwriterMp).addrOf k ≠ (layout fwriterMp).addrOf n := by
  rcases n with _ | _ | _ | _ | _ | _ | n
  · omega
  all_goals first
    | omega
    | exact Executable.addrOf_ne_of_valid (layout fwriterMp) hk
        (by rw [Layout.apply_snd, Layout.frag_getElem?]; simp [fwriterMp]) (by
          intro l z
          rw [Layout.apply_snd, Layout.frag_getElem?]
          simp [fwriterMp])

/-- **Positions `≤ 5` are determined by the address.** -/
theorem atPosF_inj {st : State} {i j : Nat} (hi : i ≤ 5) (hj : j ≤ 5) (h1 : AtPos fwriterMp st i)
    (h2 : AtPos fwriterMp st j) : i = j := by
  have heq : (layout fwriterMp).addrOf i = (layout fwriterMp).addrOf j := h1.symm.trans h2
  rcases Nat.lt_trichotomy i j with h | h | h
  · exact absurd heq (addrOf_ne_f h hj)
  · exact h
  · exact absurd heq.symm (addrOf_ne_f h hi)

/-- The writer's positions `< 5` are not the end. -/
theorem FrameF.at {P : Params} {st : State} (h : FrameF P st) {i : Nat} (hp : AtPos fwriterMp st i) (hi : i < 5) :
    At fwriterMp st i := by
  refine ⟨h.exe, h.decls, hp, ?_⟩
  rw [hp, h.endPc, f_addr_6]
  simp only [beq_eq_false_iff_ne, ne_eq]
  exact addrOf_ne_f hi (Nat.le_refl _)

/-- At the end the writer has halted. -/
theorem exec_end_f {P : Params} {st : State} (h : FrameF P st) (hp : AtPos fwriterMp st 5) : isa.exec st = none := by
  show exec st = none
  have : st.st.2 = st.endPc := by rw [hp, h.endPc, f_addr_6]
  simp [exec, this]

end Plumbing

omit layout in
/-- The positions of `PhaseF`. -/
theorem PhaseF.pos {P : Params} {i : Nat} {x2 x3 : BitVec 32} {vs : Views} {r : Res}
    (h : PhaseF P i x2 x3 vs r) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
  revert h
  unfold PhaseF
  split <;> intro h <;> first | omega | exact h.elim

/-- **`InvF` after a step of thread `tid`** with new memory `m`. -/
theorem invF_withThread {P : Params} {tid : Nat} {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    {t t' : Thread isa} {m : Memory} (hW : WorldW P g) (ht : c.threads[tid]? = some t) {s : State}
    (hst : t'.st = s) (hF : FrameF P s) {i : Nat} (hp : AtPos fwriterMp s i)
    (hph : PhaseF P i (BitVec.setWidth 32 s.st.1.regs.X2.toBitVec)
      (BitVec.setWidth 32 s.st.1.regs.X3.toBitVec) t'.views r)
    (hpp : PrepaidPromF P tid i t' m r) :
    InvF P tid cl (c.withThread tid t' m) r g := by
  have hn := lt_size_of_get? ht
  exact ⟨hW, t', by rw [Config.withThread_get? c t' m hn, ite_eq_left rfl], hst ▸ hF, i, hst ▸ hp,
    hst ▸ hph, hpp⟩

end Kraken.Promising.SLR.FenceW
