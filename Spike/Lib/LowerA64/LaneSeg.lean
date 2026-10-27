/-
**A lane store's code segment** (AArch64): `xchgLoad d a; xchgStore a w`
(`Spike/Lib/LowerShapeC2.lean`) as one `xchg_segW`
(`Spike/Lib/A64XchgSeg.lean`), the source side abstract.

The two instructions emit `ldr x10 ← rb; ldrOff x9, [x10, disp]; str x9 →
d` and `ld x9 ← w; ldr x10 ← rb; strOff x9, [x10, disp]`
(`Scc/Emit/A64.lean`, `FnCtx.inst`), the accesses each a prefix (none, or
`x16 := disp`) then one plain access (`ldrOff_form`, `strOff_form`). So
`xchg_segW`'s blocks are `B1 = [ldr x10 ← rb] ++ preL`, the load,
`B2 = [str x9 → d; ld x9 ← w; ldr x10 ← rb] ++ preS` (across the two
instructions' code), the store.

- `CodeAt.append`, `CdOf.append`: a code segment's concatenation;
- `inst_xchgLoad_inv`, `inst_xchgStore_inv`: the instructions' items;
- `LaneW`: the memory side's states at one lane's nodes in `W₀`;
- `lane_segW`: the segment from the node before the load to the node after
  the store, the source side's facts at the exchange site premises.
-/
import Spike.Lib.LowerA64.XchgOff
import Spike.Lib.LowerA64.Body2
import Spike.Lib.LowerA64.PrintArgs

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64 (CodeAt)
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.LowerNode
open Spike.Lib.LowerShape (xchgLoad xchgStore)
open Spike.Lib.Form (opdVal)
open Scc.Sem (ValRep)

/-! ## Code segments, joined -/

/-- **A code segment's concatenation**: `a` at `pc`, `b` right after it. -/
theorem CodeAt.append {st : State} {pc : Int64} {a b : List Directive} (ha : CodeAt st pc a)
    (hb : CodeAt st (pc + Int64.ofNat (4 * a.length)) b) : CodeAt st pc (a ++ b) := by
  intro j d hd
  rw [List.getElem?_append] at hd
  split at hd
  · exact ha j d hd
  · have := hb (j - a.length) d hd
    rwa [Int64.add_assoc, ← Int64.ofNat_add, ← Nat.mul_add, Nat.add_sub_cancel' (by omega)] at this

theorem CdOf.append {exe : _root_.Executable} {endPc pc : Int64} {a b : List Directive} (ha : CdOf exe endPc pc a)
    (hb : CdOf exe endPc (pc + Int64.ofNat (4 * a.length)) b) : CdOf exe endPc pc (a ++ b) :=
  fun s he hn => CodeAt.append (ha s he hn) (hb s he hn)

theorem CdOf.take {exe : _root_.Executable} {endPc pc : Int64} {a : List Directive} (h : CdOf exe endPc pc a)
    (k : Nat) : CdOf exe endPc pc (a.take k) :=
  fun s he hn => (h s he hn).take k

theorem CdOf.drop {exe : _root_.Executable} {endPc pc : Int64} {a : List Directive} (h : CdOf exe endPc pc a)
    (k : Nat) : CdOf exe endPc (pc + Int64.ofNat (4 * k)) (a.drop k) :=
  fun s he hn => (h s he hn).drop k

theorem CdOf.left {exe : _root_.Executable} {endPc pc : Int64} {a b : List Directive} (h : CdOf exe endPc pc (a ++ b)) :
    CdOf exe endPc pc a := by
  simpa using h.take a.length

theorem CdOf.right {exe : _root_.Executable} {endPc pc : Int64} {a b : List Directive}
    (h : CdOf exe endPc pc (a ++ b)) : CdOf exe endPc (pc + Int64.ofNat (4 * a.length)) b := by
  simpa using h.drop a.length

/-! ## The instructions' items -/

/-- **The items of a lane store's load**: the base's load into `x10`, the
word load into `x9`, `x9`'s store into `d`. -/
theorem inst_xchgLoad_inv {cx : FnCtx} {k : Nat} {d : Scc.IR.Reg} {a : Scc.IR.Addr} {ci : List Item}
    (h : cx.inst k (xchgLoad d a) = .ok ci) :
    ∃ lb ls, cx.getReg .X10 a.base = .ok lb ∧ cx.setReg d .X9 = .ok ls ∧
      ci = lb ++ ldrOff .W64 .X9 (xs .X10) a.disp ++ ls := by
  simp only [xchgLoad, FnCtx.inst] at h
  obtain ⟨lb, hb, h⟩ := bind_eq_ok h
  obtain ⟨lp, hp, h⟩ := bind_eq_ok h
  cases ok_inj hp
  obtain ⟨ls, hs, h⟩ := bind_eq_ok h
  exact ⟨lb, ls, hb, hs, (ok_inj h).symm⟩

/-- **The items of a lane store's store**: the value's load into `x9`, the
base's into `x10`, the word store of `x9`. -/
theorem inst_xchgStore_inv {cx : FnCtx} {k : Nat} {a : Scc.IR.Addr} {w : Scc.IR.Operand} {ci : List Item}
    (h : cx.inst k (xchgStore a w) = .ok ci) :
    ∃ lv lb, cx.getOp .X9 w = .ok lv ∧ cx.getReg .X10 a.base = .ok lb ∧
      ci = lv ++ lb ++ strOff .W64 .X9 (xs .X10) a.disp := by
  simp only [xchgStore, FnCtx.inst] at h
  obtain ⟨lv, hv, h⟩ := bind_eq_ok h
  obtain ⟨rel, hrel, h⟩ := bind_eq_ok h
  cases ok_inj hrel
  obtain ⟨lb, hb, h⟩ := bind_eq_ok h
  exact ⟨lv, lb, hv, hb, (ok_inj h).symm⟩

/-- **The run of an access's prefix** (none, or `x16 := disp`) at offsets
that do not track `x16`: the pc past it, the offsets, slots and registers
other than `x16` kept. -/
theorem arun_pre {pre : List Item} {disp : Int} (hp : pre = [] ∨ pre = movImm scratch0 disp) (lab : Label → Int64)
    (pc : Int64) {o : SO} (ho : o.kill scratch0 = o) (σ : AS) :
    ∃ regs : Reg64s, arun lab (directives pre) ⟨pc, o, σ⟩ =
      ⟨pc + Int64.ofNat (4 * (directives pre).length), o, { σ with regs := regs }⟩ ∧
      ∀ X, X ≠ scratch0 → regs.getXReg X = σ.regs.getXReg X := by
  rcases hp with rfl | rfl
  · exact ⟨σ.regs, by simp [arun, directives], fun _ _ => rfl⟩
  · refine ⟨σ.regs.setXReg scratch0 (BitVec.ofInt 64 disp), ?_, fun X hX => ?_⟩
    · rw [arun_movImm, ho]
    · simp [hX]

/-- **An access's prefix is covered** at offsets that do not track `x16`. -/
theorem okBlk_pre {pre : List Item} {disp : Int} (hp : pre = [] ∨ pre = movImm scratch0 disp) {lo hi : Int}
    {o : SO} (ho : o.kill scratch0 = o) : okBlk lo hi o (directives pre) = true := by
  rcases hp with rfl | rfl
  · rfl
  · rw [← List.append_nil (directives _), okBlk_movImm, ho]; rfl

/-! ## The memory side at an exchange -/

/-- **The memory side's states at one lane's nodes in `W₀`**: for the
lane's code (the load's and the store's items `lb`, `ls`, `lv`, the
accesses' prefixes and directives `preL`, `dL`, `preS`, `dS` with their
address functions `adL`, `adS`; the two instructions' chunks of the code
predicate `Cd`), the states along `B1` from `⟨pc, oF cx, J⟩`, at the load's node,
along `B2` and at the store's node (`xchg_segW`'s nodes from the lane's `J`
and `P`) lie in `W₀`, not moved by `K`. (The access's address unmapped in
private memory is `lane_segW`'s `hsite`.) -/
def LaneW (Cd : Int64 → List Directive → Prop) (W₀ : Frag isaLSE2) (K : State → State → Prop)
    (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (ms : MemSide isaLSE2) (lbl : WeakMem.AllocLabel → Option Nat) (cx : FnCtx)
    (pc : Int64) (d : Scc.IR.Reg) (a : Scc.IR.Addr) (w : Scc.IR.Operand) (J : AS → Ctl → Prop)
    (P : AS → Ctl → Ctl → Prop) : Prop :=
  ∀ (lb ls lv preL preS : List Item) (dL dS : Directive) (adL adS : Reg64s → BitVec 64),
    cx.getReg .X10 a.base = .ok lb → cx.setReg d .X9 = .ok ls → cx.getOp .X9 w = .ok lv →
    directives (ldrOff .W64 .X9 (xs .X10) a.disp) = directives preL ++ [dL] → LdAt dL .X9 adL →
    (preL = [] ∨ preL = movImm scratch0 a.disp) →
    (∀ lab pc o σ, adL (arun lab (directives preL) ⟨pc, o, σ⟩).σ.regs =
      (σ.regs.getXReg .X10).toBitVec + BitVec.ofInt 64 a.disp) →
    directives (strOff .W64 .X9 (xs .X10) a.disp) = directives preS ++ [dS] → StAt dS .X9 adS →
    (preS = [] ∨ preS = movImm scratch0 a.disp) →
    (∀ lab pc o σ, adS (arun lab (directives preS) ⟨pc, o, σ⟩).σ.regs =
      (σ.regs.getXReg .X10).toBitVec + BitVec.ofInt 64 a.disp) →
    let L := (_root_.Executable.labels exe).label
    let B1 := directives lb ++ directives preL
    let B2 := directives ls ++ (directives lv ++ directives lb ++ directives preS)
    let pcL := pc + Int64.ofNat (4 * B1.length)
    let pcS := pcL + Int64.ofNat 4 + Int64.ofNat (4 * B2.length)
    Cd pc (directives (lb ++ ldrOff .W64 .X9 (xs .X10) a.disp ++ ls)) →
    Cd (pc + Int64.ofNat (4 * (directives (lb ++ ldrOff .W64 .X9 (xs .X10) a.disp ++ ls)).length))
      (directives (lv ++ lb ++ strOff .W64 .X9 (xs .X10) a.disp)) →
    BlkW W₀ K exe endPc R F ⟨pc, oF cx, J⟩ B1 ∧
    NodeW W₀ K exe endPc R F (XchgSeg.xsNL L B1 pc pcL (oF cx) (oF cx) J P) ∧
    BlkW W₀ K exe endPc R F (XchgSeg.xsNH ms lbl L B1 pc pcL (oF cx) (oF cx) .X9 adL J P) B2 ∧
    NodeW W₀ K exe endPc R F (XchgSeg.xsNS ms lbl L B1 B2 pc pcL pcS (oF cx) (oF cx) (oF cx) .X9 adL J P)

/-! ## The segment -/

section Lane

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **A lane store's segment**: from the node at `pc` (the frame's offsets
`oF`, `J`) to the node after both instructions with `J'`. At each state `σ`,
control `c` of `J`: the source takes a local run to `c1` with `P σ c c1`
(`hsrc`), an exchange site of `x`'s word at `sa` (`XchgSite`), no hold
pending; with the base register `a.base` valued `vb` (`opdVal` at `rsOf`):
`vb + disp` represents `sa` and is unmapped in the private memory of the
frame condition's states; for every loaded `r` and held word `w'` the memory side
relates, `d`'s slot
updated by `r` keeps the base's value, the stored operand `w`'s value `vw`
represents `v`'s word, and `J'` holds of every state with those slots and
`tpidr_el0`, the source past the exchange (`x` bound to `w'`). -/
theorem lane_segW {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) {k : Nat} {d : Scc.IR.Reg} {a : Scc.IR.Addr} {w : Scc.IR.Operand} {l1 l2 : List Item}
    {off : Int} (hd : cx.slotOff d = .ok off)
    (hl1 : cx.inst k (xchgLoad d a) = .ok l1) (hl2 : cx.inst (k + 1) (xchgStore a w) = .ok l2) {pc : Int64}
    {Cd : Int64 → List Directive → Prop} (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    (hC1 : Cd pc (directives l1)) (hC2 : Cd (pc + Int64.ofNat (4 * (directives l1).length)) (directives l2))
    {W₀ : Frag isaLSE2} {Kw : State → State → Prop}
    {J J' : AS → Ctl → Prop} {P : AS → Ctl → Ctl → Prop}
    (hsrc : ∀ σ c, J σ c → ∃ c1, LocalRun p c c1 ∧ P σ c c1)
    (hsite : ∀ σ c c1, J σ c → P σ c c1 → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : At) (e : Expr),
      XchgSite c1 x sa u v e ∧ c1.hold = none ∧
      ∀ vb : BitVec 64, opdVal (rsOf cx) σ.slot (.reg a.base) = some vb.toNat →
        ValRep lbl (.loc sa 0) (vb + BitVec.ofInt 64 a.disp).toNat ∧
        (∀ m, F m → Mem.loadInt m.dmem (vb + BitVec.ofInt 64 a.disp) 8 = none) ∧
        ∀ (r : BitVec 64) (w' : TermRun.Word), ms.rd w' → ValRep lbl w'.val r.toNat →
          opdVal (rsOf cx) (upd σ.slot (off - cx.frame) r) (.reg a.base) = some vb.toNat ∧
          ∀ vw : BitVec 64, opdVal (rsOf cx) (upd σ.slot (off - cx.frame) r) w = some vw.toNat →
            (∃ tv wv, TermRun.evalAt c1.env v = some (tv, [wv]) ∧ ValRep lbl wv.val vw.toNat) ∧
            ∀ σ2 : AS, σ2.slot = upd σ.slot (off - cx.frame) r → σ2.regs.TPIDR_EL0 = σ.regs.TPIDR_EL0 →
              J' σ2 ⟨e, (x, u, [w']) :: c1.env, none⟩)
    (hLW : LaneW Cd W₀ Kw exe endPc R F ms lbl cx pc d a w J P) :
    SegW W₀ Kw p lbl ms (At exe endPc R F ⟨pc, oF cx, J⟩)
      (At exe endPc R F ⟨pc + Int64.ofNat (4 * ((directives l1).length + (directives l2).length)), oF cx, J'⟩) := by
  have hc1 := hCd _ _ hC1
  have hc2 := hCd _ _ hC2
  obtain ⟨lb, ls, hb, hs, rfl⟩ := inst_xchgLoad_inv hl1
  obtain ⟨lv, lb', hv, hb', rfl⟩ := inst_xchgStore_inv hl2
  obtain ⟨preL, dL, adL, heL, hLd, hpL, haL⟩ := ldrOff_form .X9 (b := .X10) (by decide) a.disp
  obtain ⟨preS, dS, adS, heS, hSt, hpS, haS⟩ := strOff_form .X9 (b := .X10) (by decide) a.disp
  have hb0 : cx.getOp .X10 (.reg a.base) = .ok lb := hb
  have hb0' : cx.getOp .X10 (.reg a.base) = .ok lb' := hb'
  simp only [directives_append, heL, heS, List.length_append, List.length_singleton] at hc1 hc2 ⊢
  cases (show lb' = lb from ok_inj (hb'.symm.trans hb))
  let L := (_root_.Executable.labels exe).label
  let B1 := directives lb ++ directives preL
  let B2 := directives ls ++ (directives lv ++ directives lb ++ directives preS)
  let pcL := pc + Int64.ofNat (4 * B1.length)
  let pcS := pcL + Int64.ofNat 4 + Int64.ofNat (4 * B2.length)
  have hoF : (oF cx).kill .X9 = oF cx := rfl
  have hoF16 : (oF cx).kill scratch0 = oF cx := rfl
  -- the code
  have hc1' : CdOf exe endPc pc (B1 ++ ([dL] ++ directives ls)) := by
    simpa only [B1, List.append_assoc] using hc1
  have hcB1 := hc1'.left
  have hcL : CdOf exe endPc pcL [dL] := hc1'.right.left
  have hcls : CdOf exe endPc (pcL + Int64.ofNat 4) (directives ls) := hc1'.right.right
  have hc2' : CdOf exe endPc (pcL + Int64.ofNat 4 + Int64.ofNat (4 * (directives ls).length))
      ((directives lv ++ directives lb ++ directives preS) ++ [dS]) := by
    have he : pc + Int64.ofNat (4 * ((directives lb).length + ((directives preL).length + 1) +
        (directives ls).length)) = pcL + Int64.ofNat 4 + Int64.ofNat (4 * (directives ls).length) := by
      simp only [pcL, B1, List.length_append, Nat.mul_add, Nat.mul_one, Int64.ofNat_add, Int64.add_assoc]
    rw [← he]; simpa only [List.append_assoc] using hc2
  have hcB2 : CdOf exe endPc (pcL + Int64.ofNat 4) B2 := CdOf.append hcls hc2'.left
  have hcS : CdOf exe endPc pcS [dS] := by
    have := hc2'.right
    simpa only [pcS, B2, List.length_append, Nat.mul_add, Int64.ofNat_add, Int64.add_assoc] using this
  have hend : pc + Int64.ofNat (4 * ((directives lb).length + ((directives preL).length + 1) +
      (directives ls).length + ((directives lv).length + (directives lb).length + ((directives preS).length + 1))))
      = pcS + Int64.ofNat 4 := by
    simp only [pcS, pcL, B1, B2, List.length_append, Nat.mul_add, Nat.mul_one, Int64.ofNat_add, Int64.add_assoc]
  rw [hend]
  -- the runs
  have hB1 : ∀ σ, ∃ vb : BitVec 64, opdVal (rsOf cx) σ.slot (.reg a.base) = some vb.toNat ∧
      (arun L B1 ⟨pc, oF cx, σ⟩).pc = pcL ∧ (arun L B1 ⟨pc, oF cx, σ⟩).so = oF cx ∧
      (arun L B1 ⟨pc, oF cx, σ⟩).σ.slot = σ.slot ∧
      adL (arun L B1 ⟨pc, oF cx, σ⟩).σ.regs = vb + BitVec.ofInt 64 a.disp := by
    intro σ
    obtain ⟨vb, hvb, he⟩ := arun_getOp hf h1 hb0 L pc σ
    obtain ⟨regs, hp, -⟩ := arun_pre hpL L (pc + Int64.ofNat (4 * (directives lb).length)) hoF16
      { σ with regs := σ.regs.setXReg .X10 vb }
    have ha := haL L (pc + Int64.ofNat (4 * (directives lb).length)) (oF cx) { σ with regs := σ.regs.setXReg .X10 vb }
    have he' : arun L B1 ⟨pc, oF cx, σ⟩ = arun L (directives preL)
        ⟨pc + Int64.ofNat (4 * (directives lb).length), oF cx, { σ with regs := σ.regs.setXReg .X10 vb }⟩ := by
      simp only [B1, arun_append]; exact congrArg _ he
    rw [he'] at ⊢
    rw [hp] at ha ⊢
    refine ⟨vb, hvb, ?_, rfl, rfl, ?_⟩
    · simp only [pcL, B1, List.length_append, Nat.mul_add, Int64.ofNat_add, Int64.add_assoc]
    · rw [ha]; simp
  have hB2 : ∀ σ : AS, ∃ vw vb : BitVec 64,
      opdVal (rsOf cx) (upd σ.slot (off - cx.frame) σ.regs.X9.toBitVec) w = some vw.toNat ∧
      opdVal (rsOf cx) (upd σ.slot (off - cx.frame) σ.regs.X9.toBitVec) (.reg a.base) = some vb.toNat ∧
      (arun L B2 ⟨pcL + Int64.ofNat 4, oF cx, σ⟩).pc = pcS ∧ (arun L B2 ⟨pcL + Int64.ofNat 4, oF cx, σ⟩).so = oF cx ∧
      (arun L B2 ⟨pcL + Int64.ofNat 4, oF cx, σ⟩).σ.slot = upd σ.slot (off - cx.frame) σ.regs.X9.toBitVec ∧
      adS (arun L B2 ⟨pcL + Int64.ofNat 4, oF cx, σ⟩).σ.regs = vb + BitVec.ofInt 64 a.disp ∧
      ((arun L B2 ⟨pcL + Int64.ofNat 4, oF cx, σ⟩).σ.regs.getXReg .X9).toBitVec = vw := by
    intro σ
    obtain ⟨hl, hs'⟩ := arun_setReg9 hf h1 hd hs L (pcL + Int64.ofNat 4) σ
    let σs : AS := { σ with slot := upd σ.slot (off - cx.frame) σ.regs.X9.toBitVec }
    obtain ⟨vw, hvw, he1⟩ := arun_getOp hf h1 hv L (pcL + Int64.ofNat 4 + 4) σs
    obtain ⟨vb, hvb, he2⟩ := arun_getOp hf h1 hb0 L
      (pcL + Int64.ofNat 4 + 4 + Int64.ofNat (4 * (directives lv).length)) { σs with regs := σs.regs.setXReg .X9 vw }
    obtain ⟨regs, hp, hr⟩ := arun_pre hpS L (pcL + Int64.ofNat 4 + 4 + Int64.ofNat (4 * (directives lv).length) +
      Int64.ofNat (4 * (directives lb).length)) hoF16
      { σs with regs := (σs.regs.setXReg .X9 vw).setXReg .X10 vb }
    have ha := haS L (pcL + Int64.ofNat 4 + 4 + Int64.ofNat (4 * (directives lv).length) +
      Int64.ofNat (4 * (directives lb).length)) (oF cx) { σs with regs := (σs.regs.setXReg .X9 vw).setXReg .X10 vb }
    have he' : arun L B2 ⟨pcL + Int64.ofNat 4, oF cx, σ⟩ = arun L (directives preS)
        ⟨pcL + Int64.ofNat 4 + 4 + Int64.ofNat (4 * (directives lv).length) + Int64.ofNat (4 * (directives lb).length),
          oF cx, { σs with regs := (σs.regs.setXReg .X9 vw).setXReg .X10 vb }⟩ := by
      simp only [B2, arun_append]
      rw [hs']
      change arun L (directives preS) (arun L (directives lb) (arun L (directives lv)
        ⟨_, ⟨-(cx.frame : Int), []⟩, σs⟩)) = _
      rw [he1]
      change arun L (directives preS) (arun L (directives lb) ⟨_, ⟨-(cx.frame : Int), []⟩, _⟩) = _
      rw [he2]; rfl
    rw [he'] at ⊢
    rw [hp] at ha ⊢
    refine ⟨vw, vb, hvw, hvb, ?_, rfl, rfl, ?_, ?_⟩
    · simp only [pcS, B2, List.length_append, hl, Nat.mul_add, Nat.mul_one, Int64.ofNat_add, Int64.add_assoc]
      rfl
    · rw [ha]; simp
    · rw [hr _ (by decide)]; simp
  -- the blocks covered
  have hok1 : okBlk (-(cx.frame : Int)) 0 (oF cx) B1 = true := by
    simp only [B1]; rw [show oF cx = ⟨-(cx.frame : Int), []⟩ from rfl, okBlk_getOp hf h1 h16 hb0]
    exact okBlk_pre hpL rfl
  have hok2 : okBlk (-(cx.frame : Int)) 0 ((oF cx).kill .X9) B2 = true := by
    simp only [B2, List.append_assoc]
    rw [hoF, show oF cx = ⟨-(cx.frame : Int), []⟩ from rfl, okBlk_setReg9 hf h1 h16 hd hs, okBlk_getOp hf h1 h16 hv,
      okBlk_getOp hf h1 h16 hb0]
    exact okBlk_pre hpS rfl
  have hne1 : B1 ≠ [] := by
    rcases getOp_cases hf h1 hb0 with ⟨r, o', -, -, hl⟩ | ⟨v, h, -⟩
    · simp [B1, hl]
    · cases h
  have hne2 : B2 ≠ [] := by
    rw [setReg_eq hf (by omega) hd] at hs
    cases hs
    simp [B2, directives, ins]
  -- the source's exchange site
  have hsite' : ∀ σ c c1, J σ c → P σ c c1 →
      ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c1 x sa u v e ∧ c1.hold = none ∧
      ValRep lbl (.loc sa 0) (adL (arun L B1 ⟨pc, oF cx, σ⟩).σ.regs).toNat ∧
      ∀ (r : BitVec 64) (w' : TermRun.Word), ms.rd w' → ValRep lbl w'.val r.toNat →
        adS (arun L B2 ⟨pcL + Int64.ofNat 4, (oF cx).kill .X9, ldStep .X9 r (arun L B1 ⟨pc, oF cx, σ⟩).σ⟩).σ.regs =
          adL (arun L B1 ⟨pc, oF cx, σ⟩).σ.regs ∧
        (∃ tv wv, TermRun.evalAt c1.env v = some (tv, [wv]) ∧
          ValRep lbl wv.val (((arun L B2 ⟨pcL + Int64.ofNat 4, (oF cx).kill .X9,
            ldStep .X9 r (arun L B1 ⟨pc, oF cx, σ⟩).σ⟩).σ.regs.getRegOrZr (.low (.reg .X9) .W64)).setWidth 128).toNat) ∧
        J' (arun L B2 ⟨pcL + Int64.ofNat 4, (oF cx).kill .X9, ldStep .X9 r (arun L B1 ⟨pc, oF cx, σ⟩).σ⟩).σ
          ⟨e, (x, u, [w']) :: c1.env, none⟩ := by
    intro σ c c1 hJ hP
    obtain ⟨x, sa, u, v, e, hX, hh, hk⟩ := hsite σ c c1 hJ hP
    obtain ⟨vb, hvb, -, -, hsl1, hadL⟩ := hB1 σ
    obtain ⟨hrep, -, hk⟩ := hk vb hvb
    refine ⟨x, sa, u, v, e, hX, hh, by rw [hadL]; exact hrep, ?_⟩
    intro r w' hrd hr
    obtain ⟨hb2, hk⟩ := hk r w' hrd hr
    rw [hoF]
    obtain ⟨vw, vb', hvw, hvb', -, -, hsl2, hadS, hX9⟩ := hB2 (ldStep .X9 r (arun L B1 ⟨pc, oF cx, σ⟩).σ)
    have hx9 : (ldStep .X9 r (arun L B1 ⟨pc, oF cx, σ⟩).σ).regs.X9.toBitVec = r := by simp [ldStep]
    have hsl : (ldStep .X9 r (arun L B1 ⟨pc, oF cx, σ⟩).σ).slot = σ.slot := hsl1
    rw [hx9, hsl] at hvw hvb' hsl2
    have hvv : vb' = vb := BitVec.eq_of_toNat_eq (Option.some.inj (hvb'.symm.trans hb2))
    rw [hvv] at hadS
    obtain ⟨⟨tv, wv, hev, hV⟩, hJ'⟩ := hk vw hvw
    refine ⟨by rw [hadS, hadL], ⟨tv, wv, hev, ?_⟩, hJ' _ hsl2 ?_⟩
    · rw [Reg64s.getRegOrZr_X, hX9, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := vw.isLt; omega)]
      exact hV
    · rw [arun_tpidr]; simp only [ldStep]; rw [setRegOrZr_TPIDR, arun_tpidr]
  -- the access's address unmapped in private memory
  have hdm1 : ∀ σ c c1, J σ c → P σ c c1 → ∀ m, F m →
      Mem.loadInt m.dmem (adL (arun L B1 ⟨pc, oF cx, σ⟩).σ.regs) 8 = none := by
    intro σ c c1 hJ hP m hm
    obtain ⟨_, _, _, _, _, _, _, hk⟩ := hsite σ c c1 hJ hP
    obtain ⟨vb, hvb, -, -, -, hadL⟩ := hB1 σ
    rw [hadL]
    exact (hk vb hvb).2.1 m hm
  have hDL : ∀ s c σ, W₀ s c → Abs R (oF cx) s.st.1 σ → F s.st.1 →
      (XchgSeg.xsNL L B1 pc pcL (oF cx) (oF cx) J P).J σ c → Mem.loadInt s.st.1.dmem (adL σ.regs) 8 = none := by
    rintro s c σ - - hFs ⟨σ0, c0, hJ, hP, rfl⟩
    exact hdm1 σ0 c0 c hJ hP _ hFs
  have hDS : ∀ s c σ, W₀ s c → Abs R (oF cx) s.st.1 σ → F s.st.1 →
      (XchgSeg.xsNS ms lbl L B1 B2 pc pcL pcS (oF cx) (oF cx) (oF cx) .X9 adL J P).J σ c →
      Mem.loadInt s.st.1.dmem (adS σ.regs) 8 = none := by
    rintro s c σ - - hFs ⟨σ0, c0, c1, r, w', hJ, hP, hrd, hr, rfl, -⟩
    obtain ⟨_, _, _, _, _, _, _, _, hk⟩ := hsite' σ0 c0 c1 hJ hP
    rw [(hk r w' hrd hr).1]
    exact hdm1 σ0 c0 c1 hJ hP _ hFs
  -- the memory side's states
  obtain ⟨hW1, hWL, hW2, hWS⟩ := hLW lb ls lv preL preS dL dS adL adS hb hs hv heL hLd hpL haL heS hSt hpS haS
    hC1 hC2
  exact XchgSeg.xchg_segW (B1 := B1) (B2 := B2) (pcL := pcL) (pcS := pcS) (oL := oF cx) (oS := oF cx)
    hLd hSt hne1 hne2 hok1 hok2 hF hR hal hlo (by omega) hcB1 hcL hcB2 hcS
    (fun σ => let ⟨_, _, h1, h2, _⟩ := hB1 σ; ⟨h1, h2⟩)
    (fun σ => by rw [hoF]; exact let ⟨_, _, _, _, h1, h2, _⟩ := hB2 σ; ⟨h1, h2⟩)
    ⟨so_le_refl _ rfl, so_le_refl _ rfl, so_le_refl _ rfl⟩ hsrc hsite' hW1 hWL hW2 hWS hDL hDS

end Lane

end Spike.Lib.LowerA64
