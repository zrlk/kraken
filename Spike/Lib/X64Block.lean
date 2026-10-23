/-
**Straight-line blocks on x64**: one theorem for every block of register
operations, stack accesses and a final branch.

The x64 analogue of `Spike/Lib/A64Block.lean`. `scc --arch x64` keeps every
IR register in a stack cell `-8·i(%rbp)`, and its prologue and epilogue
move `%rsp` and `%rbp` themselves (`push %rbp; mov %rsp, %rbp; sub $N,
%rsp` and `mov %rbp, %rsp; pop %rbp; ret`). So the block is stated over a **region** of the stack and **static
offsets** of the registers that point into it, rather than over a fixed
frame base:

* **Region** (`Region`, `Spike/Lib/Region.lean`): a base address and a
  byte range `[lo, hi)` of offsets from it; `R.Off k` is an aligned 8-byte
  cell inside the range.
  `R.OK` (the range fits in the address space) makes distinct cells
  disjoint (`Region.addr_sep`).
* **Static offsets** (`SO`): the offset of `%rsp` and of every register
  known to hold `base + k`; `SORel` relates them to the register file.
  `soReg` updates them across a register operation (a copy `mov`, `lea
  n(%b)`, `add`/`sub` of an immediate on a known register, otherwise the
  destination is forgotten; a write of `%rsp` to an unknown value is not
  covered). Offsets are integers fixed per block, so the frame's cell of
  every access is decided on the concrete block.
* **Classification** (`classify`): a load `mov n(%b), %r` or store `mov %r,
  n(%b)` (64-bit, base register only, known offset), `push`/`pop`, a
  **register operation** (`RegOnly`: `mov`, `movsx`/`movzx`, `setcc`,
  `cmovcc`, `lea n(%b)`, `add`/`adc`/`sub`/`sbb`/`cmp`, `inc`/`dec`/`neg`/
  `not`, `cqo`, `nop`, register or 64-bit immediate operands), or a
  **branch** (`jmp L`, `jcc L`, `call L`, `ret`), which can only end the
  block. Instructions with an undefined flag (`and`/`or`/`xor`/`test`/
  `imul`/shifts) make a `.choose` in Kraken's event and are not
  covered here: they are nodes of their own (`Out.choice`, `flag_nd` in
  `Spike/Lib/X64Flags.lean`).
* **One theorem for all register operations** (`interp_regOnly`): Kraken's
  own `Operation.interp` of a register operation is its continuation
  applied to `regRes op m`; proved once by one case split on `RegOnly`.
* **An abstract state** (`AS`): register file and flags as Kraken has them,
  and the region's cells as a function `Int → BitVec 64` (`Abs`; `DFrame`:
  memory outside the region is unchanged). `AI.step`/`AI.tgt` are
  structurally recursive on concrete directives, so `arun lab blk am` on a
  concrete block reduces by `simp` with labels, pc and state symbolic.
* **Kraken's executable step is never reduced**: each instruction's step
  goes through the cell at the pc (`CellAt`, from `CodeAt`) and Kraken's
  rows in `Kraken/Promising/Lower/EventsX64.lean` (`exec_load_mapped`,
  `exec_store_mapped`, `exec_jmp_label`, `exec_jcc`, `exec_call_label`,
  `exec_ret`); `exec_ai` covers every covered instruction.
* **`seg_block`**: from every pair of `P` (at the block's address, its cells
  there, the region related to an abstract state `σ` at offsets `o`), the
  source stutters until the last instruction, which carries the source's
  local run; the exit sees the machine data of `arun`, and the pc `arun`
  computes: the address after the block, a label (`jmp`, `call`), either
  edge of `jcc`, or the address `ret` pops from its cell. Exits to labels
  are `Seg` exits, so blocks compose with `Seg.seq`/`Seg.loop`. The side
  condition `okBlk lo hi o blk = true` is decided on the concrete block.

`block_spec` generates, for a concrete block, `okBlk` by `decide` and the
closed form of `arun` by `simp` (`Spike/Lib/X64Hello.lean` applies it to a
whole listing).
-/
import Spike.Lib.X64
import Spike.Lib.Region
import Spike.Lib.SegW

namespace Spike.Lib.X64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem (ValRep)

set_option linter.unusedSimpArgs false

/-! ## Register operations -/

/-- **A register operation**: register and 64-bit immediate operands only
(no memory operand, no label, no pc), no undefined flag (no `.undefined`
choice in `Operation.interp`). -/
def RegOnly {w : Width} : Operation w → Bool
  | .mov (.reg _) (.regOrMem (.reg _)) | .mov (.reg _) (.imm (.int64 _)) => true
  | .movsx (.reg _) (.reg _) | .movzx (.reg _) (.reg _) => true
  | .setcc _ (.reg _) | .cmovcc _ _ (.reg _) => true
  | .lea _ { base := some (.reg _), idx := none, disp := .int64 _ } => true
  | .add (.reg _) (.regOrMem (.reg _)) | .add (.reg _) (.imm (.int64 _)) => true
  | .adc (.reg _) (.regOrMem (.reg _)) | .adc (.reg _) (.imm (.int64 _)) => true
  | .sub (.reg _) (.regOrMem (.reg _)) | .sub (.reg _) (.imm (.int64 _)) => true
  | .sbb (.reg _) (.regOrMem (.reg _)) | .sbb (.reg _) (.imm (.int64 _)) => true
  | .cmp (.reg _) (.regOrMem (.reg _)) | .cmp (.reg _) (.imm (.int64 _)) => true
  | .inc (.reg _) | .dec (.reg _) | .neg (.reg _) | .not (.reg _) => true
  | .cqo | .nop _ => true
  | _ => false

/-- The general register a register operation writes, if any. -/
def regDst {w : Width} : Operation w → Option Reg64
  | .mov (.reg d) _ | .movsx (.reg d) _ | .movzx (.reg d) _ | .setcc _ (.reg d) | .cmovcc _ d _ => some (Reg.base d)
  | .lea d _ | .add (.reg d) _ | .adc (.reg d) _ | .sub (.reg d) _ | .sbb (.reg d) _ => some (Reg.base d)
  | .inc (.reg d) | .dec (.reg d) | .neg (.reg d) | .not (.reg d) => some (Reg.base d)
  | .cqo => some .rdx
  | _ => none

/-- No labels (a register operation reads none). -/
abbrev labels0 : Labels := ⟨fun _ => 0⟩

/-- **The machine data a register operation computes**, by Kraken's own
`Operation.interp` (64-bit addressing). -/
def regRes {w : Width} (op : Operation w) (m : MachineData) : MachineData :=
  match @Operation.interp labels0 ⟨.W64⟩ w op ⟨0, 0⟩ m (fun m' => .done (m', 0)) (fun _ m' => .done (m', 0)) with
  | .done (m', _) => m'
  | _ => m

/-- **Every register operation, at once**: `Operation.interp` continues with
`regRes op m`, whatever the labels, pc range and continuations. -/
theorem interp_regOnly [Labels] {w : Width} {op : Operation w} (h : RegOnly op = true)
    (p : Std.Rco Int64) (m : MachineData) (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects) :
    @Operation.interp _ ⟨.W64⟩ w op p m next jmp = next (regRes op m) := by
  unfold RegOnly at h
  split at h <;> first | rfl | exact absurd h (by decide)

/-- A register operation's result depends on the registers and flags only,
and changes only them. -/
theorem regRes_eq {w : Width} {op : Operation w} (h : RegOnly op = true) (m : MachineData) :
    regRes op m = { m with regs := (regRes op { m with dmem := ∅ }).regs,
                           status := (regRes op { m with dmem := ∅ }).status } := by
  unfold RegOnly at h
  split at h <;> first | rfl | exact absurd h (by decide)

theorem Reg64s.get64_set64_ne (s : Reg64s) {r r' : Reg64} (h : r' ≠ r) (v : BitVec 64) :
    (s.set64 r v).get64 r' = s.get64 r' := by
  cases r <;> cases r' <;> first | exact absurd rfl h | rfl

theorem Reg64s.get64_set64_self (s : Reg64s) (r : Reg64) (v : BitVec 64) : (s.set64 r v).get64 r = v := by
  cases r <;> simp [Reg64s.set64, Reg64s.get64]

theorem Reg64s.get64_set_ne (s : Reg64s) {w : Width} (d : Reg w) (v : w.type) {r' : Reg64}
    (h : r' ≠ Reg.base d) : (s.set d v).get64 r' = s.get64 r' := by
  cases d with
  | low r w => cases w <;> exact Reg64s.get64_set64_ne _ h _
  | _ => exact Reg64s.get64_set64_ne _ h _

/-- A register operation keeps every general register it does not write. -/
theorem regRes_get64 {w : Width} {op : Operation w} (h : RegOnly op = true) (m : MachineData) {r : Reg64}
    (hr : ∀ d, regDst op = some d → r ≠ d) : (regRes op m).regs.get64 r = m.regs.get64 r := by
  unfold RegOnly at h
  split at h <;> first
    | exact absurd h (by decide)
    | (simp only [regDst, Option.some.injEq, forall_eq'] at hr
       first
       | exact Reg64s.get64_set_ne _ _ _ hr
       | rfl
       | (show (Reg64s.set _ _ _).get64 _ = _; exact Reg64s.get64_set_ne _ _ _ hr))

/-! ## The stack region and the static offsets -/

/-- **Static offsets** of a point in a block: `%rsp` holds `base + sp`, and
each listed register `r` (never `%rsp`) holds `base + k`. They are computed
from the code alone (`AI.so`), so they are concrete on a concrete block. -/
structure SO where
  sp : Int
  regs : List (Reg64 × Int)

/-- The static offset of a register, if known. -/
def SO.get (o : SO) (r : Reg64) : Option Int := if r = .rsp then some o.sp else lk o.regs r

/-- Forget a register's offset. -/
def SO.kill (o : SO) (r : Reg64) : SO := { o with regs := rm o.regs r }

/-- Set a register's offset. -/
def SO.set (o : SO) (r : Reg64) (k : Int) : SO :=
  if r = .rsp then { o with sp := k } else { sp := o.sp, regs := (r, k) :: (o.kill r).regs }

/-- A write of an unknown value to `r`: not covered for `%rsp`, which must
stay known. -/
def SO.write (o : SO) (r : Reg64) : Option SO := if r = .rsp then none else some (o.kill r)

theorem SO.get_kill (o : SO) {r : Reg64} (hr : r ≠ .rsp) (r' : Reg64) :
    (o.kill r).get r' = if r' = r then none else o.get r' := by
  unfold SO.get SO.kill
  by_cases h : r' = .rsp
  · subst h; simp [Ne.symm hr]
  · simp [h, lk_rm]

theorem SO.get_set (o : SO) (r : Reg64) (k : Int) (r' : Reg64) :
    (o.set r k).get r' = if r' = r then some k else o.get r' := by
  unfold SO.set SO.get
  by_cases hr : r = .rsp
  · subst hr; by_cases h : r' = .rsp <;> simp [h]
  · simp only [hr, ↓reduceIte]
    by_cases h : r' = .rsp
    · subst h; simp [Ne.symm hr]
    · simp only [h, ↓reduceIte, lk, SO.kill, lk_rm]
      by_cases h' : r' = r <;> simp [h']

/-- **The registers agree with the static offsets** in region `R`. -/
def SORel (R : Region) (o : SO) (regs : Reg64s) : Prop :=
  ∀ r k, o.get r = some k → regs.get64 r = R.addr k

theorem SORel.write {R : Region} {o o' : SO} {d : Reg64} {regs regs' : Reg64s} (hw : o.write d = some o')
    (hr : SORel R o regs) (hk : ∀ r, r ≠ d → regs'.get64 r = regs.get64 r) : SORel R o' regs' := by
  unfold SO.write at hw
  split at hw
  · cases hw
  · rename_i hd
    cases hw
    intro r k h
    rw [SO.get_kill _ hd] at h
    split at h
    · cases h
    · rename_i hrd
      rw [hk r hrd]; exact hr r k h

theorem SORel.set {R : Region} {o : SO} {d : Reg64} {k : Int} {regs regs' : Reg64s} (hr : SORel R o regs)
    (hd : regs'.get64 d = R.addr k) (hk : ∀ r, r ≠ d → regs'.get64 r = regs.get64 r) :
    SORel R (o.set d k) regs' := by
  intro r k' h
  rw [SO.get_set] at h
  split at h
  · rename_i hrd; cases h; subst hrd; exact hd
  · rename_i hrd; rw [hk r hrd]; exact hr r k' h

/-- **The static offsets after a register operation**: a copy, `lea`, or
an immediate `add`/`sub` of a known register gives a known register (the
frame-pointer set-up `mov %rsp, %rbp`, the allocation `sub $n, %rsp`, the
release `mov %rbp, %rsp`); any other write forgets the register, and is not
covered on `%rsp`. -/
def soReg : (w : Width) → Operation w → SO → Option SO
  | .W64, .mov (.reg (.low d .W64)) (.regOrMem (.reg (.low s .W64))), o =>
    match o.get s with
    | some k => some (o.set d k)
    | none => o.write d
  | .W64, .lea (.low d .W64) { base := some (.reg b), idx := none, disp := .int64 n }, o =>
    match o.get b with
    | some k => some (o.set d (k + n.toInt))
    | none => o.write d
  | .W64, .add (.reg (.low d .W64)) (.imm (.int64 n)), o =>
    match o.get d with
    | some k => some (o.set d (k + n.toInt))
    | none => o.write d
  | .W64, .sub (.reg (.low d .W64)) (.imm (.int64 n)), o =>
    match o.get d with
    | some k => some (o.set d (k - n.toInt))
    | none => o.write d
  | _, op, o =>
    match regDst op with
    | some d => o.write d
    | none => some o

theorem soReg_sound {R : Region} {w : Width} {op : Operation w} (h : RegOnly op = true) {o o' : SO}
    (hs : soReg w op o = some o') {m : MachineData} (hr : SORel R o m.regs) :
    SORel R o' (regRes op m).regs := by
  have hk : ∀ r, (∀ d, regDst op = some d → r ≠ d) → (regRes op m).regs.get64 r = m.regs.get64 r :=
    fun r hr => regRes_get64 h m hr
  unfold soReg at hs
  split at hs
  · split at hs
    · rename_i k hgk
      cases hs
      refine SORel.set hr ?_ fun r hrd => hk r (by simpa [regDst, Reg.base] using hrd)
      simp [regRes, Operation.interp, Operand.interp, RegOrMem.interp, MachineData.set, MachineData.setReg,
        Reg64s.set, Reg64s.get64_set64_self]
      exact hr _ _ hgk
    · exact SORel.write hs hr fun r hrd => hk r (by simpa [regDst, Reg.base] using hrd)
  · split at hs
    · rename_i k hgk
      cases hs
      refine SORel.set hr ?_ fun r hrd => hk r (by simpa [regDst, Reg.base] using hrd)
      simp [regRes, Operation.interp, Operand.interp, RegOrMem.interp, MachineData.set, MachineData.setReg,
        Reg64s.set, Reg64s.get64_set64_self, AddrExpr.interp, ConstExpr.interp]
      rw [hr _ _ hgk, Region.addr_add]
      simp only [BitVec.toAddressSize, BitVec.take, Width.bits, BitVec.setWidth_eq, BitVec.ofInt_add,
        BitVec.ofInt_toInt, BitVec.extractLsb', Nat.shiftRight_zero, BitVec.ofNat_toNat]
    · exact SORel.write hs hr fun r hrd => hk r (by simpa [regDst, Reg.base] using hrd)
  · split at hs
    · rename_i k hgk
      cases hs
      refine SORel.set hr ?_ fun r hrd => hk r (by simpa [regDst, Reg.base] using hrd)
      simp [regRes, Operation.interp, Operand.interp, RegOrMem.interp, MachineData.set, MachineData.setReg,
        Reg64s.set, Reg64s.get64_set64_self, ConstExpr.interp]
      rw [hr _ _ hgk, Region.addr_add, BitVec.add_comm, int64_ofInt_toInt]
    · exact SORel.write hs hr fun r hrd => hk r (by simpa [regDst, Reg.base] using hrd)
  · split at hs
    · rename_i k hgk
      cases hs
      refine SORel.set hr ?_ fun r hrd => hk r (by simpa [regDst, Reg.base] using hrd)
      simp [regRes, Operation.interp, Operand.interp, RegOrMem.interp, MachineData.set, MachineData.setReg,
        Reg64s.set, Reg64s.get64_set64_self, ConstExpr.interp]
      rw [hr _ _ hgk, Region.addr_sub, int64_ofInt_toInt]
    · exact SORel.write hs hr fun r hrd => hk r (by simpa [regDst, Reg.base] using hrd)
  · split at hs
    · rename_i d hd
      exact SORel.write hs hr fun r hrd => hk r (by rw [hd]; simpa using hrd)
    · rename_i hd
      cases hs
      exact fun r k hg => (hk r (by simp [hd])).trans (hr r k hg)

/-! ## The abstract state -/

/-- **The abstract state of a block**: Kraken's registers, vector registers
and flags, and the region's cells by offset. -/
structure AS where
  regs : Reg64s
  zmms : RegZmms
  status : StatusFlags
  slot : Int → BitVec 64

/-- **The machine data `m` is the abstract state `σ`** in region `R` at
static offsets `o`: same registers and flags, the registers at their static
offsets, and each cell of the region mapped in private memory and holding
`σ.slot k`. -/
structure Abs (R : Region) (o : SO) (m : MachineData) (σ : AS) : Prop where
  regs : m.regs = σ.regs
  zmms : m.zmms = σ.zmms
  status : m.status = σ.status
  so : SORel R o σ.regs
  slot : ∀ k, R.Off k → ∃ j, Mem.loadInt m.dmem (R.addr k) 8 = some j ∧ BitVec.ofInt 64 j = σ.slot k

/-- **The private memory outside the region is unchanged** from `m` to `m'`
(every 8-byte range that does not meet the region). -/
def DFrame (R : Region) (m m' : MachineData) : Prop :=
  ∀ a : BitVec 64, a.toNat + 8 ≤ 2 ^ 64 →
    ((a.toNat : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a.toNat) →
    Mem.loadInt m'.dmem a 8 = Mem.loadInt m.dmem a 8

theorem DFrame.refl (R : Region) (m : MachineData) : DFrame R m m := fun _ _ _ => rfl

theorem DFrame.trans {R : Region} {m₁ m₂ m₃ : MachineData} (h₁ : DFrame R m₁ m₂) (h₂ : DFrame R m₂ m₃) :
    DFrame R m₁ m₃ := fun a ha hd => (h₂ a ha hd).trans (h₁ a ha hd)

/-- **A store of `v` into cell `k`**: the cells read the updated file, and
memory outside the region is unchanged. -/
theorem Abs.store {R : Region} {o : SO} {m : MachineData} {σ : AS} (hA : Abs R o m σ) (hR : R.OK) {k : Int}
    (hk : R.Off k) (v : BitVec 64) :
    (∀ k', R.Off k' → ∃ j, Mem.loadInt (Mem.storeInt m.dmem (R.addr k) 8 v.toInt) (R.addr k') 8 = some j ∧
      BitVec.ofInt 64 j = upd σ.slot k v k') ∧
    DFrame R m { m with dmem := Mem.storeInt m.dmem (R.addr k) 8 v.toInt } := by
  refine ⟨fun k' hk' => ?_, fun a ha hd => ?_⟩
  · by_cases hkk : k' = k
    · subst hkk
      exact ⟨_, loadInt_storeInt8_same _ _ _, by rw [ofInt_toNat]; simp [upd_apply]⟩
    · rw [loadInt_storeInt8_disj _ _ _ _ (R.addr_fit hR hk) (R.addr_fit hR hk')
        (R.addr_sep hR hk hk' (Ne.symm hkk))]
      simp only [upd_apply, hkk, ↓reduceIte]
      exact hA.slot k' hk'
  · apply loadInt_storeInt8_disj _ _ _ _ (R.addr_fit hR hk) ha
    have := R.addr_toNat hR hk
    obtain ⟨-, h0, h5⟩ := hk
    omega

/-! ## Classification -/

/-- `n(%b)`. -/
abbrev mB (b : Reg64) (n : Int64) : AddrExpr := { base := some (.reg b), idx := none, disp := .int64 n }

/-- The parser's `L` as a branch target. -/
abbrev relL (L : String) : RelRegOrMem := .rel (.sub (.label L) .after_current_instruction)

/-- **A covered instruction**: a stack load or store, a push or pop, a
register operation, or a branch (`jmp`, `jcc`, `call`, `ret`), which can
only end a block. -/
inductive AI where
  /-- `mov n(%b), %r`. -/
  | ld (r b : Reg64) (n : Int64)
  /-- `mov %r, n(%b)`. -/
  | st (b : Reg64) (n : Int64) (r : Reg64)
  /-- `push %r`. -/
  | push (r : Reg64)
  /-- `pop %r`. -/
  | pop (r : Reg64)
  /-- A register operation (`RegOnly`). -/
  | reg (w : Width) (op : Operation w)
  /-- `jmp L`. -/
  | jmp (L : String)
  /-- `jcc L`. -/
  | jcc (cc : CondCode) (L : String)
  /-- `call L`. -/
  | call (L : String)
  /-- `ret`. -/
  | ret

/-- The directive of a covered instruction. -/
def AI.toDir : AI → Directive
  | .ld r b n => op64 (.mov (.reg (.low r .W64)) (.mem (mB b n)))
  | .st b n r => op64 (.mov (.mem (mB b n)) (.reg (.low r .W64)))
  | .push r => op64 (.push (.reg (.low r .W64)))
  | .pop r => op64 (.pop (.reg (.low r .W64)))
  | .reg w op => .instr (.regular .W64 w op)
  | .jmp L => op64 (.jmp (relL L))
  | .jcc cc L => op64 (.jcc cc L)
  | .call L => op64 (.call (relL L))
  | .ret => op64 .ret

/-- **Classify a directive.** -/
def classify : Directive → Option AI
  | .instr (.regular .W64 .W64 (.mov (.reg (.low r .W64))
      (.regOrMem (.mem { base := some (.reg b), idx := none, disp := .int64 n })))) => some (.ld r b n)
  | .instr (.regular .W64 .W64 (.mov (.mem { base := some (.reg b), idx := none, disp := .int64 n })
      (.regOrMem (.reg (.low r .W64))))) => some (.st b n r)
  | .instr (.regular .W64 .W64 (.push (.regOrMem (.reg (.low r .W64))))) => some (.push r)
  | .instr (.regular .W64 .W64 (.pop (.reg (.low r .W64)))) => some (.pop r)
  | .instr (.regular .W64 .W64 (.jmp (.rel (.sub (.label L) .after_current_instruction)))) => some (.jmp L)
  | .instr (.regular .W64 .W64 (.jcc cc L)) => some (.jcc cc L)
  | .instr (.regular .W64 .W64 (.call (.rel (.sub (.label L) .after_current_instruction)))) => some (.call L)
  | .instr (.regular .W64 .W64 .ret) => some .ret
  | .instr (.regular .W64 w op) => if RegOnly op then some (.reg w op) else none
  | _ => none

theorem classify_sound {d : Directive} {a : AI} (h : classify d = some a) :
    d = a.toDir ∧ (∀ w op, a = .reg w op → RegOnly op = true) := by
  unfold classify at h
  split at h
  all_goals first
    | (cases h; exact ⟨rfl, by simp⟩)
    | (split at h
       · cases h; exact ⟨rfl, by rintro w op ⟨⟩; assumption⟩
       · cases h)
    | cases h

/-- The side condition of a covered instruction at static offsets `o`, for
cells in `[lo, hi)`: the base register's offset is known and the cell is
inside, `%rsp` is never loaded or popped into, a register operation keeps
`%rsp` known. -/
def AI.ok (lo hi : Int) (o : SO) : AI → Bool
  | .ld r b n => (match o.get b with | some k => offOk lo hi (k + n.toInt) | none => false) && decide (r ≠ .rsp)
  | .st b n _ => match o.get b with | some k => offOk lo hi (k + n.toInt) | none => false
  | .push _ => offOk lo hi (o.sp - 8)
  | .pop r => offOk lo hi o.sp && decide (r ≠ .rsp)
  | .reg w op => (soReg w op o).isSome
  | .jmp _ | .jcc .. => true
  | .call _ => offOk lo hi (o.sp - 8)
  | .ret => offOk lo hi o.sp

/-- **The static offsets after a covered instruction.** -/
def AI.so (o : SO) : AI → SO
  | .ld r _ _ => o.kill r
  | .st .. => o
  | .push _ => { o with sp := o.sp - 8 }
  | .pop r => { o.kill r with sp := o.sp + 8 }
  | .reg w op => (soReg w op o).getD o
  | .jmp _ | .jcc .. => o
  | .call _ => { o with sp := o.sp - 8 }
  | .ret => { o with sp := o.sp + 8 }

/-- A branch (it ends a block). -/
def AI.isTerm : AI → Bool
  | .jmp _ | .jcc .. | .call _ | .ret => true
  | _ => false

/-- **The abstract step** at static offsets `o`, `fall` being the address
after the instruction: a load writes the register, a store or push the cell,
a register operation does what Kraken's step does (`regRes`), `call` pushes
`fall`. -/
def AI.step (o : SO) (fall : Int64) : AI → AS → AS
  | .ld r b n, σ => { σ with regs := σ.regs.set64 r (σ.slot ((o.get b).getD 0 + n.toInt)) }
  | .st b n r, σ => { σ with slot := upd σ.slot ((o.get b).getD 0 + n.toInt) (σ.regs.get64 r) }
  | .push r, σ =>
    { σ with regs := σ.regs.set64 .rsp (σ.regs.get64 .rsp - 8#64), slot := upd σ.slot (o.sp - 8) (σ.regs.get64 r) }
  | .pop r, σ => { σ with regs := (σ.regs.set64 .rsp (σ.regs.get64 .rsp + 8#64)).set64 r (σ.slot o.sp) }
  | .reg _ op, σ =>
    { σ with regs := (regRes op ⟨σ.regs, σ.zmms, σ.status, ∅⟩).regs,
             status := (regRes op ⟨σ.regs, σ.zmms, σ.status, ∅⟩).status }
  | .jmp _, σ | .jcc .., σ => σ
  | .call _, σ =>
    { σ with regs := σ.regs.set64 .rsp (σ.regs.get64 .rsp - 8#64), slot := upd σ.slot (o.sp - 8) fall.toBitVec }
  | .ret, σ => { σ with regs := σ.regs.set64 .rsp (σ.regs.get64 .rsp + 8#64) }

/-- **The next pc**: `fall`, a label (`lab`), the taken or fall-through
edge of `jcc`, or the return address `ret` pops. -/
def AI.tgt (lab : String → Int64) (o : SO) (fall : Int64) : AI → AS → Int64
  | .jmp L, _ | .call L, _ => lab L
  | .jcc cc L, σ => if cc.interp σ.status then lab L else fall
  | .ret, σ => Int64.ofBitVec (σ.slot o.sp)
  | _, _ => fall

theorem AI.tgt_of_not_term {a : AI} (h : a.isTerm = false) (lab : String → Int64) (o : SO) (fall : Int64)
    (σ : AS) : a.tgt lab o fall σ = fall := by
  cases a <;> first | rfl | cases h

/-- **A covered block for cells in `[lo, hi)` from static offsets `o`**:
every directive classified, its side condition holds at its static offsets,
and only the last one is a branch (decided on a concrete block). -/
def okBlk (lo hi : Int) : SO → List (Directive × Nat) → Bool
  | _, [] => true
  | o, (d, _) :: ds =>
    match classify d with
    | some a => a.ok lo hi o && (ds.isEmpty || !a.isTerm) && okBlk lo hi (a.so o) ds
    | none => false

/-- **An abstract machine state**: pc, static offsets, abstract state. -/
structure AM where
  pc : Int64
  so : SO
  σ : AS

/-- One cell's abstract step (the identity off the covered ones): the
directive `d` of `z` bytes, the address after it `pc + z`. -/
def dstep (lab : String → Int64) (am : AM) : Directive × Nat → AM
  | (d, z) =>
    match classify d with
    | some a => ⟨a.tgt lab am.so (am.pc + Int64.ofNat z) am.σ, a.so am.so, a.step am.so (am.pc + Int64.ofNat z) am.σ⟩
    | none => am

/-- **The abstract run of a block** of sized cells, with the labels `lab`. -/
def arun (lab : String → Int64) (blk : List (Directive × Nat)) (am : AM) : AM := blk.foldl (dstep lab) am

theorem arun_take_succ (lab : String → Int64) {blk : List (Directive × Nat)} {k : Nat} (hk : k < blk.length)
    (am : AM) :
    arun lab (blk.take (k + 1)) am = dstep lab (arun lab (blk.take k) am) blk[k] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [arun, List.foldl_append, Option.toList, List.foldl]

/-- The `k`-th directive of a covered block is classified, its side
condition holds at the static offsets the run reaches, and it is not a
branch unless it is the last. -/
theorem okBlk_get (lab : String → Int64) {lo hi : Int} {blk : List (Directive × Nat)} {am : AM}
    (h : okBlk lo hi am.so blk = true) {k : Nat} (hk : k < blk.length) :
    ∃ a, classify blk[k].1 = some a ∧ a.ok lo hi (arun lab (blk.take k) am).so = true ∧
      (k + 1 < blk.length → a.isTerm = false) := by
  induction blk generalizing am k with
  | nil => cases hk
  | cons d ds ih =>
    unfold okBlk at h
    split at h
    · rename_i a ha
      simp only [Bool.and_eq_true, Bool.or_eq_true, List.isEmpty_iff, Bool.not_eq_eq_eq_not, Bool.not_true] at h
      obtain ⟨⟨hok, hterm⟩, hrest⟩ := h
      cases k with
      | zero =>
        refine ⟨a, ha, by simpa [arun] using hok, fun h1 => ?_⟩
        rcases hterm with h2 | h2
        · subst h2; simp at h1
        · exact h2
      | succ k =>
        have hds := ih (am := dstep lab am d) (by simpa [dstep, ha] using hrest) (k := k)
          (by simp at hk; omega)
        obtain ⟨a', ha', hok', ht'⟩ := hds
        exact ⟨a', ha', by simpa [arun] using hok', fun h1 => ht' (by simp at h1; omega)⟩
    · cases h

@[simp] theorem cellOff_zero (cs : List (Directive × Nat)) : cellOff cs 0 = 0 := by
  simp [cellOff]

theorem cellOff_cons_succ (c : Directive × Nat) (cs : List (Directive × Nat)) (k : Nat) :
    cellOff (c :: cs) (k + 1) = c.2 + cellOff cs k := by
  simp [cellOff]

theorem cellOff_succ {cs : List (Directive × Nat)} {k : Nat} (hk : k < cs.length) :
    cellOff cs (k + 1) = cellOff cs k + cs[k].2 := by
  unfold cellOff
  rw [List.take_add_one, List.getElem?_eq_getElem hk, List.map_append, List.sum_append]
  simp

/-- **The pc before the `k`-th directive** of a covered block: `k` past
the entry (no branch before the last). -/
theorem arun_pc (lab : String → Int64) {lo hi : Int} {blk : List (Directive × Nat)} {am : AM}
    (h : okBlk lo hi am.so blk = true) {k : Nat} (hk : k < blk.length) :
    (arun lab (blk.take k) am).pc = am.pc + Int64.ofNat (cellOff blk k) := by
  induction blk generalizing am k with
  | nil => cases hk
  | cons dz ds ih =>
    obtain ⟨d, z⟩ := dz
    cases k with
    | zero => simp [arun]
    | succ k =>
      unfold okBlk at h
      split at h
      · rename_i a ha
        simp only [Bool.and_eq_true, Bool.or_eq_true, List.isEmpty_iff, Bool.not_eq_eq_eq_not, Bool.not_true] at h
        obtain ⟨⟨-, hterm⟩, hrest⟩ := h
        have hk' : k < ds.length := by simp at hk; omega
        have hnt : a.isTerm = false := by
          rcases hterm with h2 | h2
          · subst h2; simp at hk'
          · exact h2
        have := ih (am := dstep lab am (d, z)) (by simpa [dstep, ha] using hrest) hk'
        simp only [List.take_succ_cons, arun, List.foldl] at this ⊢
        rw [this, cellOff_cons_succ]
        simp only [dstep, ha, AI.tgt_of_not_term hnt]
        rw [Int64.add_assoc, ← Int64.ofNat_add]
      · cases h

/-! ## One covered instruction -/

section Rows

variable {st : State} {sz : Nat}

/-- Read the cell through `exec_of_cellAt` and unfold it. -/
local macro "cell" hc:ident "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  show X64.exec _ = _
  rw [exec_of_cellAt $hc]
  simp [Directive.interp, Instr.interp, Operation.interp, toEv, EvTree.map, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.load, MachineData.store, MachineData.setReg, ConstExpr.interp, Width.bytesv,
    $ts,*]
  try rfl))

theorem Reg64s.get_low64 (s : Reg64s) (r : Reg64) : s.get (.low r .W64) = s.get64 r := by
  simp [Reg64s.get, Reg.base, Reg.offset, BitVec.take, BitVec.drop, BitVec.extractLsb', BitVec.ofNat_toNat]

/-- **`push %r`, the slot `[rsp-8, rsp)` mapped**: no event. -/
theorem exec_push_mapped {r : Reg64} (hc : CellAt st (op64 (.push (.reg (.low r .W64)))) sz) {j : Int}
    (hdm : Mem.loadInt st.st.1.dmem (st.st.1.regs.get64 .rsp - 8#64) 8 = some j) :
    isa.exec st = some (.done (after st sz
      { st.st.1 with regs := st.st.1.regs.set64 .rsp (st.st.1.regs.get64 .rsp - 8#64),
                     dmem := Mem.storeInt st.st.1.dmem (st.st.1.regs.get64 .rsp - 8#64) 8
                       (st.st.1.regs.get64 r).toInt })) := by
  have hdm' : Mem.loadInt st.st.1.dmem (st.st.1.regs.rsp.toBitVec - 8#64) 8 = some j := hdm
  cell hc [hdm', Reg64s.get_low64]

/-- **`pop %r`, the slot `[rsp, rsp+8)` mapped**: no event. -/
theorem exec_pop_mapped {r : Reg64} (hc : CellAt st (op64 (.pop (.reg (.low r .W64)))) sz) {j : Int}
    (hdm : Mem.loadInt st.st.1.dmem (st.st.1.regs.get64 .rsp) 8 = some j) :
    isa.exec st = some (.done (after st sz { st.st.1 with
      regs := (st.st.1.regs.set64 .rsp (st.st.1.regs.get64 .rsp + 8#64)).set64 r (BitVec.ofInt 64 j) })) := by
  have hdm' : Mem.loadInt st.st.1.dmem st.st.1.regs.rsp.toBitVec 8 = some j := hdm
  cell hc [hdm']

/-- **A register operation's cell**: no event, the machine data `regRes`
gives. -/
theorem exec_reg {w : Width} {op : Operation w} (h : RegOnly op = true)
    (hc : CellAt st (.instr (.regular .W64 w op)) sz) :
    isa.exec st = some (.done (after st sz (regRes op st.st.1))) := by
  show X64.exec _ = _
  rw [exec_of_cellAt hc]
  simp only [Directive.interp, Instr.interp, @interp_regOnly (_root_.Executable.labels st.exe) _ _ h, toEv,
    EvTree.map]
  rfl

/-- `n(%b)`, as an address. -/
theorem eaddr_mB (st : State) (sz : Nat) (b : Reg64) (n : Int64) :
    eaddr st sz (mB b n) = st.st.1.regs.get64 b + BitVec.ofInt 64 n.toInt := by
  rw [eaddr_reg_disp, BitVec.ofInt_add, BitVec.ofInt_toInt]

end Rows

theorem ofInt_eight : BitVec.ofInt 64 8 = 8#64 := rfl

theorem SO.get_rsp (o : SO) : o.get .rsp = some o.sp := by simp [SO.get]

theorem SO.get_ne_rsp {o : SO} {r : Reg64} (h : r ≠ .rsp) (sp : Int) : ({ o with sp } : SO).get r = o.get r := by
  simp [SO.get, h]

/-- The registers after `%rsp` moved to `base + k`. -/
theorem SORel.rsp {R : Region} {o : SO} {regs : Reg64s} (hr : SORel R o regs) {k : Int} {v : BitVec 64}
    (hv : v = R.addr k) : SORel R { o with sp := k } (regs.set64 .rsp v) := by
  intro r k' h
  by_cases hr' : r = .rsp
  · subst hr'
    simp only [SO.get, ↓reduceIte, Option.some.injEq] at h
    subst h
    rw [Reg64s.get64_set64_self, hv]
  · rw [SO.get_ne_rsp hr'] at h
    rw [Reg64s.get64_set64_ne _ hr']
    exact hr r k' h

theorem SORel.kill {R : Region} {o : SO} {regs : Reg64s} (hr : SORel R o regs) {r : Reg64} (hrs : r ≠ .rsp) :
    SORel R (o.kill r) regs := by
  intro r' k h
  rw [SO.get_kill _ hrs] at h
  split at h
  · cases h
  · exact hr r' k h

/-- **One covered instruction** at the pc: no event; the next pc is
`AI.tgt`, the machine data the abstract step's at the new static offsets,
with the memory outside the region unchanged. -/
theorem exec_ai {st : State} {R : Region} {lo hi : Int} {o : SO} {σ : AS} {a : AI} (hok : a.ok lo hi o = true)
    (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) {z : Nat} (hc : CellAt st a.toDir z)
    (hreg : ∀ w op, a = .reg w op → RegOnly op = true) (hA : Abs R o st.st.1 σ) :
    ∃ m', isa.exec st = some (.done { st with st := (m', a.tgt (labelAddr st) o (st.st.2 + Int64.ofNat z) σ) }) ∧
      Abs R (a.so o) m' (a.step o (st.st.2 + Int64.ofNat z) σ) ∧ DFrame R st.st.1 m' := by
  have hso : ∀ r k, o.get r = some k → st.st.1.regs.get64 r = R.addr k := fun r k h => by
    rw [hA.regs]; exact hA.so r k h
  have hsp := hso .rsp o.sp o.get_rsp
  cases a with
  | ld r b n =>
    simp only [AI.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hk, hr⟩ := hok
    split at hk
    · rename_i k hgk
      have ho := offOk_off hk hlo hhi
      obtain ⟨j, hj, hjv⟩ := hA.slot _ ho
      refine ⟨_, exec_load_mapped hc (by rw [eaddr_mB, hso b k hgk, ← Region.addr_add]) hj, ?_,
        DFrame.refl _ _⟩
      refine ⟨by simp [AI.step, hA.regs, hgk, hjv], hA.zmms, hA.status, ?_, hA.slot⟩
      intro r' k' h
      simp only [AI.so] at h
      rw [SO.get_kill _ hr] at h
      split at h
      · cases h
      · rename_i hrr
        simp only [AI.step]
        rw [Reg64s.get64_set64_ne _ hrr]
        exact hA.so r' k' h
    · cases hk
  | st b n r =>
    simp only [AI.ok] at hok
    split at hok
    · rename_i k hgk
      have ho := offOk_off hok hlo hhi
      obtain ⟨j, hj, -⟩ := hA.slot _ ho
      have ha : eaddr st z (mB b n) = R.addr (k + n.toInt) := by rw [eaddr_mB, hso b k hgk, ← Region.addr_add]
      obtain ⟨hsl, hD⟩ := hA.store hR ho (σ.regs.get64 r)
      refine ⟨_, exec_store_mapped hc ha hj, ?_, ?_⟩
      · refine ⟨hA.regs, hA.zmms, hA.status, hA.so, fun k' hk' => ?_⟩
        simp only [AI.step, hgk, Option.getD_some]
        rw [Reg64s.get_low64, hA.regs]
        exact hsl k' hk'
      · rw [Reg64s.get_low64, hA.regs]; exact hD
    · cases hok
  | push r =>
    simp only [AI.ok] at hok
    have ho := offOk_off hok hlo hhi
    obtain ⟨j, hj, -⟩ := hA.slot _ ho
    have ha : st.st.1.regs.get64 .rsp - 8#64 = R.addr (o.sp - 8) := by rw [hsp, Region.addr_sub]; rfl
    obtain ⟨hsl, hD⟩ := hA.store hR ho (σ.regs.get64 r)
    refine ⟨_, exec_push_mapped hc (by rw [ha]; exact hj), ?_, ?_⟩
    · refine ⟨by simp only [AI.step, hA.regs], hA.zmms, hA.status, ?_, fun k' hk' => ?_⟩
      · simp only [AI.step, AI.so]
        exact hA.so.rsp (by rw [← hA.regs, hsp, Region.addr_sub8])
      · simp only [AI.step]
        rw [ha, hA.regs]
        exact hsl k' hk'
    · rw [ha, hA.regs]; exact hD
  | pop r =>
    simp only [AI.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hk, hr⟩ := hok
    have ho := offOk_off hk hlo hhi
    obtain ⟨j, hj, hjv⟩ := hA.slot _ ho
    refine ⟨_, exec_pop_mapped hc (by rw [hsp]; exact hj), ?_, DFrame.refl _ _⟩
    refine ⟨by simp only [AI.step, hA.regs, hjv], hA.zmms, hA.status, ?_, hA.slot⟩
    intro r' k' h
    simp only [AI.step, AI.so] at h ⊢
    by_cases hrr : r' = r
    · subst hrr
      rw [SO.get_ne_rsp hr, SO.get_kill _ hr] at h
      simp at h
    · rw [Reg64s.get64_set64_ne _ hrr]
      have h2 := (hA.so.kill hr).rsp (k := o.sp + 8) (v := σ.regs.get64 .rsp + 8#64)
        (by rw [← hA.regs, hsp, Region.addr_add8])
      exact h2 r' k' h
  | reg w op =>
    have hr := hreg w op rfl
    simp only [AI.ok] at hok
    obtain ⟨o', ho'⟩ := Option.isSome_iff_exists.mp hok
    refine ⟨_, exec_reg hr hc, ?_, fun b _ _ => by rw [regRes_eq hr]⟩
    have he := regRes_eq hr st.st.1
    have hm : ({ st.st.1 with dmem := ∅ } : MachineData) = ⟨σ.regs, σ.zmms, σ.status, ∅⟩ := by
      rw [← hA.regs, ← hA.zmms, ← hA.status]
    rw [hm] at he
    refine ⟨by rw [he]; rfl, by rw [he]; exact hA.zmms, by rw [he]; rfl, ?_, ?_⟩
    · simp only [AI.so, AI.step, ho', Option.getD_some]
      exact soReg_sound hr ho' hA.so
    · intro k hk
      rw [he]
      exact hA.slot k hk
  | jmp L =>
    exact ⟨_, exec_jmp_label hc, hA, DFrame.refl _ _⟩
  | jcc cc L =>
    refine ⟨_, ?_, hA, DFrame.refl _ _⟩
    rw [exec_jcc hc]
    simp [AI.tgt, hA.status]
  | call L =>
    simp only [AI.ok] at hok
    have ho := offOk_off hok hlo hhi
    obtain ⟨j, hj, -⟩ := hA.slot _ ho
    have ha : st.st.1.regs.get64 .rsp - 8#64 = R.addr (o.sp - 8) := by rw [hsp, Region.addr_sub]; rfl
    obtain ⟨hsl, hD⟩ := hA.store hR ho (st.st.2 + Int64.ofNat z).toBitVec
    refine ⟨_, exec_call_label hc (by simp only [rspOf]; rw [ha]; exact hj), ?_, ?_⟩
    · refine ⟨by simp only [AI.step, callPost, rspOf, hA.regs], hA.zmms, hA.status, ?_, fun k' hk' => ?_⟩
      · simp only [AI.step, AI.so]
        exact hA.so.rsp (by rw [← hA.regs, hsp, Region.addr_sub8])
      · simp only [AI.step, callPost, rspOf, retAddr]
        rw [ha]
        exact hsl k' hk'
    · simp only [callPost, rspOf, retAddr]
      rw [ha]; exact hD
  | ret =>
    simp only [AI.ok] at hok
    have ho := offOk_off hok hlo hhi
    obtain ⟨j, hj, hjv⟩ := hA.slot _ ho
    refine ⟨{ st.st.1 with regs := st.st.1.regs.set64 .rsp (st.st.1.regs.get64 .rsp + 8#64) }, ?_, ?_,
      fun _ _ _ => rfl⟩
    · rw [exec_ret hc (by simp only [rspOf]; rw [hsp]; exact hj)]
      simp [AI.tgt, hjv]
    · refine ⟨by simp only [AI.step, hA.regs], hA.zmms, hA.status, ?_, hA.slot⟩
      simp only [AI.step, AI.so]
      exact hA.so.rsp (by rw [← hA.regs, hsp, Region.addr_add8])

/-! ## Blocks -/

section Block

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}

/-- **A block simulates a local run of the source**: from every pair of
`P`, the block's instructions are no-event steps; the source stutters until
the last one, which carries a local run `c ↦ c'`; at the exit the machine
data is related to the abstract run's state at its static offsets, with the
memory outside the region unchanged, and the pc is the abstract run's: the
address after the block, or the target of the final branch (a label, the
taken or fall-through edge of `jcc`, the address `ret` pops). One theorem
for every block with `okBlk lo hi o blk = true` (decided on a concrete
block). The
block's internal states (before its `k`-th instruction, the machine data
related to the abstract run of the first `k` instructions, the memory
outside the region unchanged, the source control as at entry) are in `W`
and not moved by `K` (a block holds no take). -/
theorem seg_blockW {W : Frag isa} {K : State → State → Prop} {R : Region} {pc : Int64} {lo hi : Int} {o : SO}
    {blk : List (Directive × Nat)} (hne : blk ≠ [])
    {P Q : Frag isa}
    (h : ∀ s c, P s c → s.st.2 = pc ∧ CodeAt s pc blk ∧ okBlk lo hi o blk = true ∧ R.OK ∧ R.lo ≤ lo ∧
      hi ≤ R.hi ∧ ∃ σ, Abs R o s.st.1 σ ∧
      (∀ k < blk.length, ∀ m, Abs R (arun (labelAddr s) (blk.take k) ⟨pc, o, σ⟩).so m
          (arun (labelAddr s) (blk.take k) ⟨pc, o, σ⟩).σ → DFrame R s.st.1 m →
        W { s with st := (m, pc + Int64.ofNat (cellOff blk k)) } c ∧
          ∀ s', ¬ K { s with st := (m, pc + Int64.ofNat (cellOff blk k)) } s') ∧
      ∃ c', LocalRun p c c' ∧ ∀ m', Abs R (arun (labelAddr s) blk ⟨pc, o, σ⟩).so m'
          (arun (labelAddr s) blk ⟨pc, o, σ⟩).σ → DFrame R s.st.1 m' →
        Q { s with st := (m', (arun (labelAddr s) blk ⟨pc, o, σ⟩).pc) } c') :
    SegW W K p lbl ms P Q := by
  refine ⟨fun s c => ∃ (s0 : State) (σ0 : AS) (c' : Ctl) (k : Nat) (m : MachineData), k < blk.length ∧
      s = { s0 with st := (m, pc + Int64.ofNat (cellOff blk k)) } ∧ CodeAt s0 pc blk ∧ okBlk lo hi o blk = true ∧ R.OK ∧
      R.lo ≤ lo ∧ hi ≤ R.hi ∧
      Abs R (arun (labelAddr s0) (blk.take k) ⟨pc, o, σ0⟩).so m (arun (labelAddr s0) (blk.take k) ⟨pc, o, σ0⟩).σ ∧
      DFrame R s0.st.1 m ∧
      (∀ k < blk.length, ∀ m, Abs R (arun (labelAddr s0) (blk.take k) ⟨pc, o, σ0⟩).so m
          (arun (labelAddr s0) (blk.take k) ⟨pc, o, σ0⟩).σ → DFrame R s0.st.1 m →
        W { s0 with st := (m, pc + Int64.ofNat (cellOff blk k)) } c ∧
          ∀ s', ¬ K { s0 with st := (m, pc + Int64.ofNat (cellOff blk k)) } s') ∧ LocalRun p c c' ∧
      (∀ m', Abs R (arun (labelAddr s0) blk ⟨pc, o, σ0⟩).so m' (arun (labelAddr s0) blk ⟨pc, o, σ0⟩).σ →
        DFrame R s0.st.1 m' → Q { s0 with st := (m', (arun (labelAddr s0) blk ⟨pc, o, σ0⟩).pc) } c'), ?_, ?_, ?_⟩
  · intro s c hP
    obtain ⟨hpc, hcode, hok, hR, hlo, hhi, σ, hA, hW, c', hr, hQ⟩ := h s c hP
    refine ⟨s, σ, c', 0, s.st.1, List.length_pos_iff.mpr hne, ?_, hcode, hok, hR, hlo, hhi,
      by simpa [arun] using hA, DFrame.refl _ _, hW, hr, hQ⟩
    obtain ⟨exe, endPc, ⟨m, q⟩, showPc, decls⟩ := s
    simp only at hpc
    subst hpc
    rw [cellOff_zero, show q + Int64.ofNat 0 = q by simp]
  · rintro s c ⟨s0, σ0, c', k, m, hk, rfl, -, -, -, -, -, hA, hD, hW, -, -⟩
    exact (hW k hk m hA hD).1
  · rintro s c ⟨s0, σ0, c', k, m, hk, rfl, hcode, hok, hR, hlo, hhi, hA, hD, hW, hr, hQ⟩
    refine ⟨fun _ => ?_, KOut.none (hW k hk m hA hD).2⟩
    have hd : blk[k]? = some blk[k] := List.getElem?_eq_getElem hk
    obtain ⟨a, hca, haok, hnt⟩ := okBlk_get (labelAddr s0) (am := ⟨pc, o, σ0⟩) hok hk
    obtain ⟨hdir, hreg⟩ := classify_sound hca
    have hc : CellAt { s0 with st := (m, pc + Int64.ofNat (cellOff blk k)) } a.toDir blk[k].2 :=
      hcode.cell (j := k) (d := a.toDir) (z := blk[k].2) (by rw [hd, ← hdir]) rfl rfl rfl
    obtain ⟨m', hex, hA', hD'⟩ := exec_ai haok hR hlo hhi hc hreg hA
    have hpck := arun_pc (labelAddr s0) (am := ⟨pc, o, σ0⟩) hok hk
    have hstep : arun (labelAddr s0) (blk.take (k + 1)) ⟨pc, o, σ0⟩ =
        ⟨a.tgt (labelAddr s0) (arun (labelAddr s0) (blk.take k) ⟨pc, o, σ0⟩).so
          (pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2)
          (arun (labelAddr s0) (blk.take k) ⟨pc, o, σ0⟩).σ,
         a.so (arun (labelAddr s0) (blk.take k) ⟨pc, o, σ0⟩).so,
         a.step (arun (labelAddr s0) (blk.take k) ⟨pc, o, σ0⟩).so
          (pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2)
          (arun (labelAddr s0) (blk.take k) ⟨pc, o, σ0⟩).σ⟩ := by
      rw [arun_take_succ _ hk, dstep, hca]
      simp only [hpck]
    by_cases hlast : k + 1 = blk.length
    · refine .silent _ c' hex hr (.inr ?_)
      have he : blk.take (k + 1) = blk := by rw [hlast, List.take_length]
      rw [he] at hstep
      have hQ' := hQ m' (by rw [hstep]; exact hA') (hD.trans hD')
      rw [hstep] at hQ'
      exact hQ'
    · have hnt' := hnt (by omega)
      refine .silent _ c hex (.refl c) (.inl ⟨s0, σ0, c', k + 1, m', by omega, ?_, hcode, hok, hR, hlo, hhi,
        by rw [hstep]; exact hA', hD.trans hD', hW, hr, hQ⟩)
      simp only [AI.tgt_of_not_term hnt']
      rw [Int64.add_assoc, ← Int64.ofNat_add, cellOff_succ hk]

/-- **A block simulates a local run of the source**: from every pair of
`P`, the block's instructions are no-event steps; the source stutters until
the last one, which carries a local run `c ↦ c'`; at the exit the machine
data is related to the abstract run's state at its static offsets, with the
memory outside the region unchanged, and the pc is the abstract run's: the
address after the block, or the target of the final branch (a label, the
taken or fall-through edge of `jcc`, the address `ret` pops). One theorem
for every block with `okBlk lo hi o blk = true` (decided on a concrete
block). -/
theorem seg_block {R : Region} {pc : Int64} {lo hi : Int} {o : SO} {blk : List (Directive × Nat)} (hne : blk ≠ [])
    {P Q : Frag isa}
    (h : ∀ s c, P s c → s.st.2 = pc ∧ CodeAt s pc blk ∧ okBlk lo hi o blk = true ∧ R.OK ∧ R.lo ≤ lo ∧
      hi ≤ R.hi ∧ ∃ σ, Abs R o s.st.1 σ ∧
      ∃ c', LocalRun p c c' ∧ ∀ m', Abs R (arun (labelAddr s) blk ⟨pc, o, σ⟩).so m'
          (arun (labelAddr s) blk ⟨pc, o, σ⟩).σ → DFrame R s.st.1 m' →
        Q { s with st := (m', (arun (labelAddr s) blk ⟨pc, o, σ⟩).pc) } c') :
    Seg p lbl ms P Q :=
  (seg_blockW (W := fun _ _ => True) (K := fun _ _ => False) hne fun s c hP =>
    let ⟨hpc, hcode, hok, hR, hlo, hhi, σ, hA, hr⟩ := h s c hP
    ⟨hpc, hcode, hok, hR, hlo, hhi, σ, hA, fun _ _ _ _ _ => ⟨trivial, fun _ h => h⟩, hr⟩).toSeg

end Block

/-! ## Per-block specifications, generated -/

namespace BlockSpec

open Lean Meta Elab Command Term

/-- The definitions `simp` unfolds to run a concrete block on a symbolic
abstract state. -/
def unfolds : List Name :=
  [``arun, ``dstep, ``classify, ``RegOnly, ``AI.so, ``AI.step, ``AI.tgt, ``soReg, ``regDst, ``regRes,
   ``Operation.interp, ``Operand.interp, ``RegOrMem.interp, ``MachineData.set, ``MachineData.setReg,
   ``Reg64s.set, ``ConstExpr.interp, ``AddrExpr.interp, ``SO.get, ``SO.set, ``SO.kill, ``SO.write, ``lk, ``rm,
   ``List.foldl, ``Reg.base]

/- Non-`rfl` equations for `AI.step` and `AI.tgt`: `simp` applies them with
a proof, leaving the kernel no definitional gap to close (closing one would
re-evaluate the block under the free `σ`, where the kernel's `Nat` literal
arithmetic is disabled). -/
section NoRfl
variable (o : SO) (f : Int64) (σ : AS) (lab : String → Int64)
theorem AI.step_ld' r b n :
    AI.step o f (.ld r b n) σ = { σ with regs := σ.regs.set64 r (σ.slot ((o.get b).getD 0 + n.toInt)) } := by
  cases σ; rfl
theorem AI.step_st' b n r :
    AI.step o f (.st b n r) σ = { σ with slot := upd σ.slot ((o.get b).getD 0 + n.toInt) (σ.regs.get64 r) } := by
  cases σ; rfl
theorem AI.step_push' r :
    AI.step o f (.push r) σ =
      { σ with regs := σ.regs.set64 .rsp (σ.regs.get64 .rsp - 8#64),
               slot := upd σ.slot (o.sp - 8) (σ.regs.get64 r) } := by
  cases σ; rfl
theorem AI.step_pop' r :
    AI.step o f (.pop r) σ =
      { σ with regs := (σ.regs.set64 .rsp (σ.regs.get64 .rsp + 8#64)).set64 r (σ.slot o.sp) } := by
  cases σ; rfl
theorem AI.step_reg' w op :
    AI.step o f (.reg w op) σ =
      { σ with regs := (regRes op ⟨σ.regs, σ.zmms, σ.status, ∅⟩).regs,
               status := (regRes op ⟨σ.regs, σ.zmms, σ.status, ∅⟩).status } := by
  cases σ; rfl
theorem AI.step_jmp' L : AI.step o f (.jmp L) σ = σ := by cases σ; rfl
theorem AI.step_jcc' cc L : AI.step o f (.jcc cc L) σ = σ := by cases σ; rfl
theorem AI.step_call' L :
    AI.step o f (.call L) σ =
      { σ with regs := σ.regs.set64 .rsp (σ.regs.get64 .rsp - 8#64), slot := upd σ.slot (o.sp - 8) f.toBitVec } := by
  cases σ; rfl
theorem AI.step_ret' :
    AI.step o f .ret σ = { σ with regs := σ.regs.set64 .rsp (σ.regs.get64 .rsp + 8#64) } := by
  cases σ; rfl
theorem AI.tgt_jmp' L : AI.tgt lab o f (.jmp L) σ = lab L := by cases σ; rfl
theorem AI.tgt_call' L : AI.tgt lab o f (.call L) σ = lab L := by cases σ; rfl
theorem AI.tgt_jcc' cc L : AI.tgt lab o f (.jcc cc L) σ = if cc.interp σ.status then lab L else f := by cases σ; rfl
theorem AI.tgt_ret' : AI.tgt lab o f .ret σ = Int64.ofBitVec (σ.slot o.sp) := by cases σ; rfl
theorem AI.tgt_ld' r b n : AI.tgt lab o f (.ld r b n) σ = f := by cases σ; rfl
theorem AI.tgt_st' b n r : AI.tgt lab o f (.st b n r) σ = f := by cases σ; rfl
theorem AI.tgt_push' r : AI.tgt lab o f (.push r) σ = f := by cases σ; rfl
theorem AI.tgt_pop' r : AI.tgt lab o f (.pop r) σ = f := by cases σ; rfl
theorem AI.tgt_reg' w op : AI.tgt lab o f (.reg w op) σ = f := by cases σ; rfl
end NoRfl

/-- The non-`rfl` equations, used in place of unfolding `AI.step`, `AI.tgt`. -/
def noRfl : List Name :=
  [``AI.step_ld', ``AI.step_st', ``AI.step_push', ``AI.step_pop', ``AI.step_reg', ``AI.step_jmp', ``AI.step_jcc',
   ``AI.step_call', ``AI.step_ret', ``AI.tgt_jmp', ``AI.tgt_call', ``AI.tgt_jcc', ``AI.tgt_ret', ``AI.tgt_ld',
   ``AI.tgt_st', ``AI.tgt_push', ``AI.tgt_pop', ``AI.tgt_reg']

/-- Replace each `ite`'s `Decidable` instance by the synthesized one for its
(simplified) condition: `simp` rewrites the condition but not the instance. -/
def normIteInst (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun t => do
    if t.isAppOfArity ``ite 5 then
      match ← trySynthInstance (mkApp (mkConst ``Decidable) (t.getArg! 1)) with
      | .some inst => return .done (mkAppN t.getAppFn (t.getAppArgs.set! 2 inst))
      | _ => return .done t
    else return .done t)

/-- **`block_spec name lo hi o blk`**: `name_ok : okBlk lo hi o blk = true`
(by `decide`) and `name_run : ∀ lab pc σ, arun lab blk ⟨pc, o, σ⟩ = <normal
form>`, the normal form being what `simp` (the default set, the default
simprocs, `unfolds` with `AI.step`/`AI.tgt` through `noRfl`, `upd_apply`
and `Reg64s.get_low64`) makes of the
abstract run for symbolic labels, entry pc and abstract state. `blk` may be
the name of a definition (unfolded by `simp`), so that a function's proof
can name its blocks. -/
elab "block_spec " nm:ident lo:term:max hi:term:max o:term:max blk:term : command => do
  let okId := mkIdent (nm.getId.appendAfter "_ok")
  elabCommand (← `(theorem $okId : okBlk $lo $hi $o $blk = true := by decide))
  let runName := (← getCurrNamespace) ++ nm.getId.appendAfter "_run"
  liftTermElabM do
    let b ← elabTermEnsuringType blk (← mkAppM ``List #[← mkAppM ``Prod #[mkConst ``Directive, mkConst ``Nat]])
    let o ← elabTermEnsuringType o (mkConst ``SO)
    synthesizeSyntheticMVarsNoPostponing
    let b ← instantiateMVars b
    let o ← instantiateMVars o
    let mut thms ← getSimpTheorems
    for u in unfolds do
      if u != ``AI.step && u != ``AI.tgt then thms ← thms.addDeclToUnfold u
    for l in noRfl do
      thms ← thms.addConst l
    if let .const n _ := b then
      thms ← thms.addDeclToUnfold n
    thms ← thms.addConst ``upd_apply
    thms ← thms.addConst ``Reg64s.get_low64
    thms ← thms.addConst ``Int64.add_assoc
    let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
    let simprocs ← Simp.getSimprocs
    let labTy ← mkArrow (mkConst ``String) (mkConst ``Int64)
    withLocalDeclD `lab labTy fun lab => withLocalDeclD `pc (mkConst ``Int64) fun pc =>
        withLocalDeclD `σ (mkConst ``AS) fun σ => do
      let e ← mkAppM ``arun #[lab, b, ← mkAppM ``AM.mk #[pc, o, σ]]
      let (r, _) ← withTheReader Core.Context (fun c => { c with maxRecDepth := 100000 }) <|
        simp e ctx #[simprocs]
      let prf ← r.getProof
      let rhs ← normIteInst r.expr
      let ty ← instantiateMVars (← mkForallFVars #[lab, pc, σ] (← mkEq e rhs))
      let val ← instantiateMVars (← mkLambdaFVars #[lab, pc, σ] prf)
      withTheReader Core.Context (fun c => { c with maxRecDepth := 100000 }) <|
        addDecl (.thmDecl { name := runName, levelParams := [], type := ty, value := val })

end BlockSpec

end Spike.Lib.X64
