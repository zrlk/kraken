/-
**A function's return block** (AArch64): the result words and the epilogue.

`FnCtx.term (.ret vs)` (`Scc/Lower`) ends a function with one instruction
per result word into `x0`, `x1`, ... (a frame cell `ldr xi, [sp, #n]` or a
16-bit immediate `movz xi, #v`), then the epilogue (`ldr x29, [sp, #F-16]`,
`ldr x30, [sp, #F-8]`, `add sp, sp, #F`) and `ret`.

- `retBlk F ws`: the block's directives for a frame of `F` bytes and the
  words `ws` (at most four, `retRegs`);
- `retBlk_ok`: the block lemma's side conditions hold when the frame is a
  multiple of 16 and every slot lies inside it;
- `retBlk_run`: the state after the block: the return address in `pc`, the
  frame popped, each `xi` the `i`-th word, `x29`/`x30` the saved cells;
- `retBlk_hit`: the block reaches an exit node at the return address.
-/
import Spike.Lib.A64Cfg
import Kraken.AArch64.Parser
open Kraken Kraken.AArch64.Parser Spike.Lib.A64.Flow Spike.Lib

namespace Spike.Lib.A64.Flow

/-- **A result word's source**: a frame cell `[sp, #n]` or a 16-bit
immediate. -/
inductive RW where
  | slot (n : Int64)
  | imm (v : Int64)

/-- The instruction that puts the word in `Xr`. -/
def RW.dir (r : XReg) : RW → Directive
  | .slot n => (AI.ldr (.low (.reg r) .W64) n).toDir
  | .imm v => .instr ⟨.W64, .MOVZ (.low (.reg r) .W64) (.int64 v) .LSL0⟩

/-- The word, `sp` at offset `sp`, the cells `sl`. -/
def RW.val (sp : Int) (sl : Int → BitVec 64) : RW → BitVec 64
  | .slot n => sl (sp + n.toInt)
  | .imm v => v.toBitVec &&& 65535#64

/-- The word's side condition in a frame of `F` bytes: a cell inside. -/
def RW.ok (F : Int) : RW → Bool
  | .slot n => offOk (-F) 0 (-F + n.toInt)
  | .imm _ => true

theorem dstep_rw (lab : Label → Int64) (pc : Int64) (sp : Int) (σ : AS) (r : XReg) (w : RW) :
    dstep lab ⟨pc, ⟨sp, []⟩, σ⟩ (w.dir r) =
      ⟨pc + Int64.ofNat 4, ⟨sp, []⟩, { σ with regs := σ.regs.setXReg r (w.val sp σ.slot) }⟩ := by
  cases w <;>
  simp [RW.dir, RW.val, AI.toDir, dstep, classify, RegOnly, AI.so, AI.step, AI.tgt, soReg, regDst, regRes,
    Operation.interp, MachineData.setRegOrZr, Reg64s.setRegOrZr, Reg64s.setRegOrZr64, ConstExpr.interp, zrB,
    SO.write, SO.kill, SO.killZ, rm]

theorem okBlk_rw {lo hi : Int} {sp : Int} {r : XReg} {w : RW} {ds : List Directive} :
    okBlk lo hi ⟨sp, []⟩ (w.dir r :: ds) =
      ((match w with | .slot n => offOk lo hi (sp + n.toInt) && decide (sp % 16 = 0) | .imm _ => true) &&
        okBlk lo hi ⟨sp, []⟩ ds) := by
  cases w <;>
  simp [RW.dir, AI.toDir, okBlk, classify, RegOnly, AI.ok, AI.so, AI.isTerm, soReg, regDst, zrB, SO.write,
    SO.kill, SO.killZ, rm]

/-- The registers after the words `ps` (each `(r, w)`: `w` into `Xr`). -/
def setWords (sp : Int) (sl : Int → BitVec 64) : List (XReg × RW) → Reg64s → Reg64s
  | [], regs => regs
  | (r, w) :: ps, regs => setWords sp sl ps (regs.setXReg r (w.val sp sl))

/-- The words' instructions. -/
def wordDirs (ps : List (XReg × RW)) : List Directive := ps.map fun p => p.2.dir p.1

theorem arun_words (lab : Label → Int64) (sp : Int) (ps : List (XReg × RW)) (pc : Int64) (σ : AS) :
    arun lab (wordDirs ps) ⟨pc, ⟨sp, []⟩, σ⟩ =
      ⟨pc + Int64.ofNat (4 * ps.length), ⟨sp, []⟩, { σ with regs := setWords sp σ.slot ps σ.regs }⟩ := by
  induction ps generalizing pc σ with
  | nil => simp [wordDirs, arun, setWords]
  | cons p ps ih =>
    obtain ⟨r, w⟩ := p
    simp only [wordDirs, List.map_cons, arun, List.foldl] at ih ⊢
    rw [dstep_rw, ih]
    simp only [setWords, List.length_cons, AM.mk.injEq, and_true]
    rw [Int64.add_assoc, ← Int64.ofNat_add]
    congr 2
    omega

theorem setWords_get_of_not_mem (sp : Int) (sl : Int → BitVec 64) (ps : List (XReg × RW)) (regs : Reg64s)
    {r : XReg} (h : r ∉ ps.map Prod.fst) : (setWords sp sl ps regs).getXReg r = regs.getXReg r := by
  induction ps generalizing regs with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨r', w⟩ := p
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [setWords]
    rw [ih _ h.2, Reg64s.getXReg_setXReg]; simp [h.1]

theorem setWords_get (sp : Int) (sl : Int → BitVec 64) (ps : List (XReg × RW)) (regs : Reg64s)
    (hnd : (ps.map Prod.fst).Nodup) {r : XReg} {w : RW} (h : (r, w) ∈ ps) :
    (setWords sp sl ps regs).getXReg r = .ofBitVec (w.val sp sl) := by
  induction ps generalizing regs with
  | nil => cases h
  | cons p ps ih =>
    obtain ⟨r', w'⟩ := p
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [setWords]
    rcases List.mem_cons.mp h with h | h
    · cases h
      rw [setWords_get_of_not_mem _ _ _ _ hnd.1, Reg64s.getXReg_setXReg]; simp
    · exact ih _ hnd.2 h

/-- The epilogue of a frame of `F` bytes: `x29`, `x30` restored, `sp`
popped, `ret`. -/
def epi (F : Int64) : List Directive :=
  [RW.dir .X29 (.slot (F - 16)), RW.dir .X30 (.slot (F - 8)),
   .instr ⟨.W64, .ADD_e (.low .SP .W64) (.low .SP .W64) (.imm ⟨.int64 F, .S0⟩)⟩,
   (AI.ret (.low (.reg .X30) .W64)).toDir]

theorem getXReg_setSP (s : Reg64s) (v : UInt64) (r : XReg) : { s with SP := v }.getXReg r = s.getXReg r := by
  cases r <;> rfl

theorem arun_epi (lab : Label → Int64) (pc : Int64) (sp : Int) (σ : AS) (F : Int64) :
    (arun lab (epi F) ⟨pc, ⟨sp, []⟩, σ⟩).pc = Int64.ofBitVec (σ.slot (sp + (F - 8).toInt)) ∧
    (arun lab (epi F) ⟨pc, ⟨sp, []⟩, σ⟩).so = ⟨sp + F.toInt, []⟩ ∧
    (arun lab (epi F) ⟨pc, ⟨sp, []⟩, σ⟩).σ.slot = σ.slot ∧
    (arun lab (epi F) ⟨pc, ⟨sp, []⟩, σ⟩).σ.status = σ.status ∧
    (arun lab (epi F) ⟨pc, ⟨sp, []⟩, σ⟩).σ.regs.X29.toBitVec = σ.slot (sp + (F - 16).toInt) ∧
    (arun lab (epi F) ⟨pc, ⟨sp, []⟩, σ⟩).σ.regs.X30.toBitVec = σ.slot (sp + (F - 8).toInt) ∧
    ∀ r, r ≠ .X29 → r ≠ .X30 → (arun lab (epi F) ⟨pc, ⟨sp, []⟩, σ⟩).σ.regs.getXReg r = σ.regs.getXReg r := by
  simp only [epi, arun, List.foldl, dstep_rw]
  simp [dstep, classify, RegOnly, AI.so, AI.step, AI.tgt, soReg, regRes, AI.toDir, RW.val,
    Operation.interp, MachineData.setRegOrSp, Reg64s.setRegOrSp, Reg64s.setRegOrSp64, ConstExpr.interp,
    SO.set, ExtOrImmReg.interp, Reg64s.getRegOrSp, Reg64s.getRegOrSp64, RegOrSp.base, SO.get]
  intro r h1 h2
  cases r <;> first | exact absurd rfl h1 | exact absurd rfl h2 | rfl

theorem bmod_sub {F : Int64} {k : Int} (hk : 0 ≤ k) (h : k ≤ F.toInt) :
    (F.toInt - k).bmod 18446744073709551616 = F.toInt - k :=
  Int.bmod_eq_of_le (by omega) (by have := Int64.toInt_lt F; omega)

theorem okBlk_epi {F : Int64} (h16 : F.toInt % 16 = 0) (hF : 16 ≤ F.toInt) :
    okBlk (-F.toInt) 0 ⟨-F.toInt, []⟩ (epi F) = true := by
  simp [epi, RW.dir, AI.toDir, okBlk, classify, RegOnly, AI.ok, AI.so, AI.isTerm, soReg,
    SO.kill, SO.killZ, rm, offOk, SO.set, SO.get, bmod_sub (by omega : (0:Int) ≤ 16) hF,
    bmod_sub (by omega : (0:Int) ≤ 8) (by omega : (8:Int) ≤ F.toInt)]
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩ <;> first | omega | exact decide_eq_true (by omega)

theorem okBlk_words {lo hi sp : Int} (h16 : sp % 16 = 0) {ps : List (XReg × RW)}
    (hw : ∀ p ∈ ps, match p.2 with | .slot n => offOk lo hi (sp + n.toInt) = true | .imm _ => True)
    {ds : List Directive} (hds : okBlk lo hi ⟨sp, []⟩ ds = true) :
    okBlk lo hi ⟨sp, []⟩ (wordDirs ps ++ ds) = true := by
  induction ps with
  | nil => simpa [wordDirs] using hds
  | cons p ps ih =>
    obtain ⟨r, w⟩ := p
    simp only [wordDirs, List.map_cons, List.cons_append] at ih ⊢
    rw [okBlk_rw, ih fun q hq => hw q (List.mem_cons_of_mem _ hq), Bool.and_true]
    have := hw (r, w) List.mem_cons_self
    cases w with
    | slot n => simp only at this; simp [this, h16]
    | imm v => rfl

/-- The result registers. -/
def retRegs : List XReg := [.X0, .X1, .X2, .X3]

/-- **A function's return block**, frame of `F` bytes: the result words
`ws` into `x0`, `x1`, … (each a frame cell or an immediate), then the
epilogue. -/
def retBlk (F : Int64) (ws : List RW) : List Directive := wordDirs (retRegs.zip ws) ++ epi F

/-- **The return block is covered** in the frame `[-F, 0)`. -/
theorem retBlk_ok {F : Int64} (h16 : F.toInt % 16 = 0) (hF : 16 ≤ F.toInt) {ws : List RW}
    (hw : ∀ w ∈ ws, w.ok F.toInt = true) : okBlk (-F.toInt) 0 ⟨-F.toInt, []⟩ (retBlk F ws) = true := by
  refine okBlk_words (by omega) (fun p hp => ?_) (okBlk_epi h16 hF)
  have := hw p.2 (List.of_mem_zip hp).2
  obtain ⟨r, w⟩ := p
  cases w with
  | slot n => simpa [RW.ok] using this
  | imm v => trivial

theorem retRegs_zip_nodup (ws : List RW) : ((retRegs.zip ws).map Prod.fst).Nodup := by
  rcases ws with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, t⟩⟩⟩⟩ <;> simp [retRegs]

/-- **The return block's run**: the pc the saved return address, `sp` at
offset 0, the cells and flags unchanged, `x29` and `x30` restored, and each
result register holding its word. -/
theorem retBlk_run (lab : Label → Int64) (pc : Int64) (σ : AS) {F : Int64} (hF : 16 ≤ F.toInt) (ws : List RW) :
    (arun lab (retBlk F ws) ⟨pc, ⟨-F.toInt, []⟩, σ⟩).pc = Int64.ofBitVec (σ.slot (-8)) ∧
    (arun lab (retBlk F ws) ⟨pc, ⟨-F.toInt, []⟩, σ⟩).so = ⟨0, []⟩ ∧
    (arun lab (retBlk F ws) ⟨pc, ⟨-F.toInt, []⟩, σ⟩).σ.slot = σ.slot ∧
    (arun lab (retBlk F ws) ⟨pc, ⟨-F.toInt, []⟩, σ⟩).σ.status = σ.status ∧
    (arun lab (retBlk F ws) ⟨pc, ⟨-F.toInt, []⟩, σ⟩).σ.regs.X29.toBitVec = σ.slot (-16) ∧
    (arun lab (retBlk F ws) ⟨pc, ⟨-F.toInt, []⟩, σ⟩).σ.regs.X30.toBitVec = σ.slot (-8) ∧
    ∀ r w, (r, w) ∈ retRegs.zip ws →
      ((arun lab (retBlk F ws) ⟨pc, ⟨-F.toInt, []⟩, σ⟩).σ.regs.getXReg r).toBitVec = w.val (-F.toInt) σ.slot := by
  have h16 : (F - 16).toInt = F.toInt - 16 := by
    rw [Int64.toInt_sub, show (16 : Int64).toInt = 16 from rfl]; exact bmod_sub (by omega) hF
  have h8 : (F - 8).toInt = F.toInt - 8 := by
    rw [Int64.toInt_sub, show (8 : Int64).toInt = 8 from rfl]; exact bmod_sub (by omega) (by omega)
  simp only [retBlk, arun, List.foldl_append] at *
  have hw := arun_words lab (-F.toInt) (retRegs.zip ws) pc σ
  simp only [arun] at hw
  rw [hw]
  obtain ⟨hpc, hso, hsl, hst, h29, h30, hr⟩ := arun_epi lab (pc + Int64.ofNat (4 * (retRegs.zip ws).length))
    (-F.toInt) { σ with regs := setWords (-F.toInt) σ.slot (retRegs.zip ws) σ.regs } F
  simp only [arun] at hpc hso hsl hst h29 h30 hr
  rw [h16] at h29
  rw [h8] at hpc h30
  refine ⟨by rw [hpc]; congr 2; omega, by rw [hso]; congr 1; omega, hsl, hst, by rw [h29]; congr 1; omega,
    by rw [h30]; congr 1; omega, fun r w hm => ?_⟩
  have hr29 : r ≠ .X29 := by
    intro h; subst h; have := (List.of_mem_zip hm).1; simp [retRegs] at this
  have hr30 : r ≠ .X30 := by
    intro h; subst h; have := (List.of_mem_zip hm).1; simp [retRegs] at this
  rw [hr r hr29 hr30]
  rw [setWords_get _ _ _ _ (retRegs_zip_nodup ws) hm]

/-- **A return block lands at an exit** `x` whose pc is the saved return
address and whose offsets are the entry's, if its invariant holds of every
state with the cells and flags unchanged, `x29` and `x30` restored and each
result register holding its word. -/
theorem retBlk_hit (lab : Label → Int64) (pc : Int64) (σ : AS) {F : Int64} (hF : 16 ≤ F.toInt) (ws : List RW)
    {x : ND} {c : Ctl} (hpc : x.pc = Int64.ofBitVec (σ.slot (-8))) (ho : x.o = ⟨0, []⟩)
    (hJ : ∀ σ' : AS, σ'.slot = σ.slot → σ'.status = σ.status → σ'.regs.X29.toBitVec = σ.slot (-16) →
      σ'.regs.X30.toBitVec = σ.slot (-8) →
      (∀ r w, (r, w) ∈ retRegs.zip ws → (σ'.regs.getXReg r).toBitVec = w.val (-F.toInt) σ.slot) → x.J σ' c) :
    Hit x (arun lab (retBlk F ws) ⟨pc, ⟨-F.toInt, []⟩, σ⟩) c := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := retBlk_run lab pc σ hF ws
  exact ⟨by rw [hpc, h1], by rw [ho, h2]; rfl, hJ _ h3 h4 h5 h6 h7⟩

/-- `retBlk` is what Kraken's parser makes of `scc`'s returns. -/
example : retBlk 32 [.slot 0] = parseAArch64("ldr x0, [sp]
ldr x29, [sp, #16]
ldr x30, [sp, #24]
add sp, sp, #32
ret") := by decide

example : retBlk 48 [.slot 8, .imm 1] = parseAArch64("ldr x0, [sp, #8]
movz x1, #1
ldr x29, [sp, #32]
ldr x30, [sp, #40]
add sp, sp, #48
ret") := by decide

end Spike.Lib.A64.Flow
