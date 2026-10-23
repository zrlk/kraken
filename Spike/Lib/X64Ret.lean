/-
**A function's return block** (x86-64): the result words and the
epilogue; the twin of `Spike/Lib/A64Ret.lean`.

`emitTerm fr (.ret vs)` (`Scc/Emit/X64.lean`) ends a function with one
`movq` per result word into `%rax`, `%rdx`, … (a frame cell
`movq n(%rbp), %r` or an immediate `movq $v, %r`), then the epilogue
(`movq %rbp, %rsp`, `popq %rbp`) and `ret`.

The block runs in the frame's region, based at the frame record (`%rbp`):
`%rsp` at `sp`, `%rbp` at `0`, the saved `%rbp` in cell `0`, the return
address in cell `8`.

- `retBlk ws`: the block's directives for the words `ws` (at most six,
  `retRegs`); the frame's size does not occur in the code;
- `retBlk_ok`: the block is covered in `[lo, 16)` when every slot lies in
  it;
- `retBlk_run`: the state after the block, at any cell sizes: the return
  address in `pc`, `%rsp` at offset `16`, `%rbp` the saved cell, each
  result register the `i`-th word;
- `retBlk_hit`: the block reaches an exit node at the return address.

Where x86-64 differs from AArch64: the cells are sized (assembler input),
so a block is `ds.zip zs` and the pc after a straight-line part is
`pc + Int64.ofNat zs.sum`; the frame record is addressed from `%rbp`, so
no frame size or alignment side condition is needed for the epilogue.
-/
import Spike.Lib.X64Cfg
import Kraken.X64.Parser

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64 Spike.Lib

namespace Spike.Lib.X64

set_option linter.unusedSimpArgs false

/-- **A result word's source**: a frame cell `n(%rbp)` or a 64-bit
immediate. -/
inductive RW where
  | slot (n : Int64)
  | imm (v : UInt64)

/-- The instruction that puts the word in `r`. -/
def RW.dir (r : Reg64) : RW → Directive
  | .slot n => (AI.ld r .rbp n).toDir
  | .imm v => op64 (.mov (.reg (.low r .W64)) (.imm (.int64 v.toInt64)))

/-- The word, the cells `sl` (offsets from `%rbp`). -/
def RW.val (sl : Int → BitVec 64) : RW → BitVec 64
  | .slot n => sl n.toInt
  | .imm v => v.toBitVec

/-- The word's side condition for cells in `[lo, hi)`: a cell inside. -/
def RW.ok (lo hi : Int) : RW → Bool
  | .slot n => offOk lo hi n.toInt
  | .imm _ => true

/-- The body's static offsets: `%rsp` at `sp`, `%rbp` at `0`. -/
abbrev oR (sp : Int) : SO := ⟨sp, [(.rbp, 0)]⟩

theorem dstep_rw (lab : String → Int64) (pc : Int64) (sp : Int) (σ : AS) {r : Reg64} (hr : r ≠ .rbp)
    (hr' : r ≠ .rsp) (w : RW) (z : Nat) :
    dstep lab ⟨pc, oR sp, σ⟩ (w.dir r, z) =
      ⟨pc + Int64.ofNat z, oR sp, { σ with regs := σ.regs.set64 r (w.val σ.slot) }⟩ := by
  cases w <;>
  simp [RW.dir, RW.val, AI.toDir, dstep, classify, RegOnly, AI.so, AI.step, AI.tgt, soReg, regDst, regRes,
    Operation.interp, Operand.interp, MachineData.set, MachineData.setReg, Reg64s.set, ConstExpr.interp,
    SO.write, SO.kill, SO.get, lk, rm, Reg.base, hr, hr', Ne.symm hr, Ne.symm hr']

theorem okBlk_rw {lo hi : Int} {sp : Int} {r : Reg64} (hr : r ≠ .rbp) (hr' : r ≠ .rsp) {w : RW} {z : Nat}
    {ds : List (Directive × Nat)} :
    okBlk lo hi (oR sp) ((w.dir r, z) :: ds) = (w.ok lo hi && okBlk lo hi (oR sp) ds) := by
  cases w <;>
  simp [RW.dir, RW.ok, AI.toDir, okBlk, classify, RegOnly, AI.ok, AI.so, AI.isTerm, soReg, regDst, SO.write,
    SO.kill, SO.get, lk, rm, Reg.base, hr, hr', Ne.symm hr, Ne.symm hr']

/-- The registers after the words `ps` (each `(r, w)`: `w` into `r`). -/
def setWords (sl : Int → BitVec 64) : List (Reg64 × RW) → Reg64s → Reg64s
  | [], regs => regs
  | (r, w) :: ps, regs => setWords sl ps (regs.set64 r (w.val sl))

/-- The words' instructions. -/
def wordDirs (ps : List (Reg64 × RW)) : List Directive := ps.map fun p => p.2.dir p.1

theorem arun_words (lab : String → Int64) (sp : Int) (ps : List (Reg64 × RW))
    (hps : ∀ p ∈ ps, p.1 ≠ .rbp ∧ p.1 ≠ .rsp) (pc : Int64) (σ : AS) {zs : List Nat}
    (hz : zs.length = ps.length) :
    arun lab ((wordDirs ps).zip zs) ⟨pc, oR sp, σ⟩ =
      ⟨pc + Int64.ofNat zs.sum, oR sp, { σ with regs := setWords σ.slot ps σ.regs }⟩ := by
  induction ps generalizing pc σ zs with
  | nil =>
    match zs, hz with
    | [], _ => simp [wordDirs, arun, setWords]
  | cons p ps ih =>
    match zs, hz with
    | z :: zs, hz =>
    obtain ⟨r, w⟩ := p
    have hr := hps (r, w) List.mem_cons_self
    simp only [wordDirs, List.map_cons, List.zip_cons_cons, arun, List.foldl] at ih ⊢
    rw [dstep_rw lab pc sp σ hr.1 hr.2, ih (fun q hq => hps q (List.mem_cons_of_mem _ hq)) _ _
      (by simpa using hz)]
    simp only [setWords, List.sum_cons, AM.mk.injEq, and_true]
    rw [Int64.add_assoc, ← Int64.ofNat_add]

theorem setWords_get_of_not_mem (sl : Int → BitVec 64) (ps : List (Reg64 × RW)) (regs : Reg64s)
    {r : Reg64} (h : r ∉ ps.map Prod.fst) : (setWords sl ps regs).get64 r = regs.get64 r := by
  induction ps generalizing regs with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨r', w⟩ := p
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [setWords]
    rw [ih _ h.2, Reg64s.get64_set64_ne _ h.1]

theorem setWords_get (sl : Int → BitVec 64) (ps : List (Reg64 × RW)) (regs : Reg64s)
    (hnd : (ps.map Prod.fst).Nodup) {r : Reg64} {w : RW} (h : (r, w) ∈ ps) :
    (setWords sl ps regs).get64 r = w.val sl := by
  induction ps generalizing regs with
  | nil => cases h
  | cons p ps ih =>
    obtain ⟨r', w'⟩ := p
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [setWords]
    rcases List.mem_cons.mp h with h | h
    · cases h
      rw [setWords_get_of_not_mem _ _ _ hnd.1, Reg64s.get64_set64_self]
    · exact ih _ hnd.2 h

/-- **The epilogue**: `movq %rbp, %rsp`, `popq %rbp`, `ret`. -/
def epi : List Directive :=
  [op64 (.mov (.reg (.low .rsp .W64)) (.regOrMem (.reg (.low .rbp .W64)))), (AI.pop .rbp).toDir, AI.ret.toDir]

theorem arun_epi (lab : String → Int64) (pc : Int64) (sp : Int) (σ : AS) (z0 z1 z2 : Nat) :
    (arun lab (epi.zip [z0, z1, z2]) ⟨pc, oR sp, σ⟩).pc = Int64.ofBitVec (σ.slot 8) ∧
    (arun lab (epi.zip [z0, z1, z2]) ⟨pc, oR sp, σ⟩).so = ⟨16, []⟩ ∧
    (arun lab (epi.zip [z0, z1, z2]) ⟨pc, oR sp, σ⟩).σ.slot = σ.slot ∧
    (arun lab (epi.zip [z0, z1, z2]) ⟨pc, oR sp, σ⟩).σ.status = σ.status ∧
    (arun lab (epi.zip [z0, z1, z2]) ⟨pc, oR sp, σ⟩).σ.regs.get64 .rbp = σ.slot 0 ∧
    (arun lab (epi.zip [z0, z1, z2]) ⟨pc, oR sp, σ⟩).σ.regs.get64 .rsp = σ.regs.get64 .rbp + 16#64 ∧
    ∀ r, r ≠ .rbp → r ≠ .rsp →
      (arun lab (epi.zip [z0, z1, z2]) ⟨pc, oR sp, σ⟩).σ.regs.get64 r = σ.regs.get64 r := by
  simp [epi, arun, dstep, AI.toDir, classify, RegOnly, AI.so, AI.step, AI.tgt, soReg, regDst, regRes,
    Operation.interp, Operand.interp, RegOrMem.interp, MachineData.set, MachineData.setReg, Reg64s.set,
    SO.set, SO.get, SO.kill, lk, rm, Reg.base]
  refine ⟨by rw [BitVec.add_assoc]; rfl, fun r h1 h2 => ?_⟩
  simp [h1, h2]

theorem okBlk_epi {lo : Int} (hlo : lo ≤ 0) {sp : Int} (z0 z1 z2 : Nat) :
    okBlk lo 16 (oR sp) (epi.zip [z0, z1, z2]) = true := by
  simp [epi, AI.toDir, okBlk, classify, RegOnly, AI.ok, AI.so, AI.isTerm, soReg, regDst, SO.set, SO.get, SO.kill,
    lk, rm, offOk, Reg.base]
  omega

theorem okBlk_words {lo hi sp : Int} {ps : List (Reg64 × RW)} (hps : ∀ p ∈ ps, p.1 ≠ .rbp ∧ p.1 ≠ .rsp)
    (hw : ∀ p ∈ ps, p.2.ok lo hi = true) {zs : List Nat} (hz : zs.length = ps.length)
    {ds : List (Directive × Nat)} (hds : okBlk lo hi (oR sp) ds = true) :
    okBlk lo hi (oR sp) ((wordDirs ps).zip zs ++ ds) = true := by
  induction ps generalizing zs with
  | nil =>
    match zs, hz with
    | [], _ => simpa [wordDirs] using hds
  | cons p ps ih =>
    match zs, hz with
    | z :: zs, hz =>
    obtain ⟨r, w⟩ := p
    have hr := hps (r, w) List.mem_cons_self
    simp only [wordDirs, List.map_cons, List.zip_cons_cons, List.cons_append] at ih ⊢
    rw [okBlk_rw hr.1 hr.2, ih (fun q hq => hps q (List.mem_cons_of_mem _ hq))
      (fun q hq => hw q (List.mem_cons_of_mem _ hq)) (by simpa using hz), hw (r, w) List.mem_cons_self]
    rfl

/-- The result registers (`Scc.Emit.X64.retRegs`). -/
def retRegs : List Reg64 := [.rax, .rdx, .rcx, .rsi, .rdi, .r8]

theorem retRegs_ok {ws : List RW} : ∀ p ∈ retRegs.zip ws, p.1 ≠ .rbp ∧ p.1 ≠ .rsp := by
  intro p hp
  have := (List.of_mem_zip hp).1
  simp [retRegs] at this
  rcases this with h | h | h | h | h | h <;> rw [h] <;> decide

theorem retRegs_zip_nodup (ws : List RW) : ((retRegs.zip ws).map Prod.fst).Nodup := by
  rcases ws with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, t⟩⟩⟩⟩⟩⟩ <;> simp [retRegs]

/-- **A function's return block**: the result words `ws` into `%rax`,
`%rdx`, … (each a frame cell or an immediate), then the epilogue. -/
def retBlk (ws : List RW) : List Directive := wordDirs (retRegs.zip ws) ++ epi

theorem zip_split {α β : Type} (a b : List α) (zs : List β) (hz : zs.length = a.length + b.length) :
    (a ++ b).zip zs = a.zip (zs.take a.length) ++ b.zip (zs.drop a.length) := by
  conv => lhs; rw [← List.take_append_drop a.length zs]
  exact List.zip_append (by simp; omega)

theorem drop_three {β : Type} {zs : List β} (h : zs.length = 3) : ∃ z0 z1 z2, zs = [z0, z1, z2] := by
  match zs, h with
  | [a, b, c], _ => exact ⟨a, b, c, rfl⟩

/-- **The return block is covered** in `[lo, 16)` when every word's cell
lies in it. -/
theorem retBlk_ok {lo : Int} (hlo : lo ≤ 0) {sp : Int} {ws : List RW} (hw : ∀ w ∈ ws, w.ok lo 16 = true)
    {zs : List Nat} (hz : zs.length = (retBlk ws).length) :
    okBlk lo 16 (oR sp) ((retBlk ws).zip zs) = true := by
  have hl : (retBlk ws).length = (wordDirs (retRegs.zip ws)).length + epi.length := by simp [retBlk]
  rw [retBlk, zip_split _ _ _ (by omega)]
  have hd : (zs.drop (wordDirs (retRegs.zip ws)).length).length = 3 := by simp [epi] at hl ⊢; omega
  obtain ⟨z0, z1, z2, he⟩ := drop_three hd
  rw [he]
  exact okBlk_words retRegs_ok (fun p hp => hw p.2 (List.of_mem_zip hp).2)
    (by rw [List.length_take_of_le (by omega)]; simp [wordDirs])
    (okBlk_epi hlo z0 z1 z2)

/-- **The return block's run**, at any cell sizes: the pc the saved return
address, `%rsp` at offset `16`, the cells and flags unchanged, `%rbp`
restored, and each result register holding its word. -/
theorem retBlk_run (lab : String → Int64) (pc : Int64) (sp : Int) (σ : AS) (ws : List RW) {zs : List Nat}
    (hz : zs.length = (retBlk ws).length) :
    (arun lab ((retBlk ws).zip zs) ⟨pc, oR sp, σ⟩).pc = Int64.ofBitVec (σ.slot 8) ∧
    (arun lab ((retBlk ws).zip zs) ⟨pc, oR sp, σ⟩).so = ⟨16, []⟩ ∧
    (arun lab ((retBlk ws).zip zs) ⟨pc, oR sp, σ⟩).σ.slot = σ.slot ∧
    (arun lab ((retBlk ws).zip zs) ⟨pc, oR sp, σ⟩).σ.status = σ.status ∧
    (arun lab ((retBlk ws).zip zs) ⟨pc, oR sp, σ⟩).σ.regs.get64 .rbp = σ.slot 0 ∧
    (arun lab ((retBlk ws).zip zs) ⟨pc, oR sp, σ⟩).σ.regs.get64 .rsp = σ.regs.get64 .rbp + 16#64 ∧
    ∀ r w, (r, w) ∈ retRegs.zip ws →
      (arun lab ((retBlk ws).zip zs) ⟨pc, oR sp, σ⟩).σ.regs.get64 r = w.val σ.slot := by
  have hl : (retBlk ws).length = (wordDirs (retRegs.zip ws)).length + epi.length := by simp [retBlk]
  rw [retBlk, zip_split _ _ _ (by omega)]
  have hd : (zs.drop (wordDirs (retRegs.zip ws)).length).length = 3 := by simp [epi] at hl ⊢; omega
  obtain ⟨z0, z1, z2, he⟩ := drop_three hd
  rw [he]
  simp only [arun, List.foldl_append]
  have hw := arun_words lab sp (retRegs.zip ws) retRegs_ok pc σ
    (zs := zs.take (wordDirs (retRegs.zip ws)).length) (by rw [List.length_take_of_le (by omega)]; simp [wordDirs])
  simp only [arun] at hw
  rw [hw]
  obtain ⟨hpc, hso, hsl, hst, hbp, hsp, hr⟩ := arun_epi lab _ sp
    { σ with regs := setWords σ.slot (retRegs.zip ws) σ.regs } z0 z1 z2
  simp only [arun] at hpc hso hsl hst hbp hsp hr
  refine ⟨hpc, hso, hsl, hst, hbp, ?_, fun r w hm => ?_⟩
  · rw [hsp, setWords_get_of_not_mem]
    simp only [List.mem_map, not_exists, not_and]
    intro p hp he
    exact (retRegs_ok p hp).1 he
  · have hrr := retRegs_ok (r, w) hm
    rw [hr r hrr.1 hrr.2, setWords_get _ _ _ (retRegs_zip_nodup ws) hm]

/-- **A return block lands at an exit** `x` whose pc is the saved return
address and whose offsets are the exit's, if its invariant holds of every
state with the cells and flags unchanged, `%rbp` restored, `%rsp` past the
return address and each result register holding its word. -/
theorem retBlk_hit (lab : String → Int64) (pc : Int64) (sp : Int) (σ : AS) (ws : List RW) {zs : List Nat}
    (hz : zs.length = (retBlk ws).length) {x : ND} {c : Ctl} (hpc : x.pc = Int64.ofBitVec (σ.slot 8))
    (ho : x.o = ⟨16, []⟩)
    (hJ : ∀ σ' : AS, σ'.slot = σ.slot → σ'.status = σ.status → σ'.regs.get64 .rbp = σ.slot 0 →
      σ'.regs.get64 .rsp = σ.regs.get64 .rbp + 16#64 →
      (∀ r w, (r, w) ∈ retRegs.zip ws → σ'.regs.get64 r = w.val σ.slot) → x.J σ' c) :
    Hit x (arun lab ((retBlk ws).zip zs) ⟨pc, oR sp, σ⟩) c := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := retBlk_run lab pc sp σ ws hz
  exact ⟨by rw [hpc, h1], by rw [ho, h2]; simp [SO.le], hJ _ h3 h4 h5 h6 h7⟩

section
open Kraken.X64.Parser

/-- `retBlk` is what Kraken's parser makes of `scc`'s returns. -/
example : retBlk [.slot (-8)] = parse("movq -8(%rbp), %rax
movq %rbp, %rsp
popq %rbp
ret") := by decide

example : retBlk [.slot (-16), .imm 1] = parse("movq -16(%rbp), %rax
movq $1, %rdx
movq %rbp, %rsp
popq %rbp
ret") := by decide

end

end Spike.Lib.X64
