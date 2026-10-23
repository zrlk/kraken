/-
**Blocks with control flow and `sp` updates on AArch64**: one theorem for
every block of register operations, stack accesses, `sp` moves and a final
branch.

The AArch64 twin of `Spike/Lib/X64Block.lean`, extending
`Spike/Lib/A64Block.lean` (a fixed frame at `sp`, no branch) to the code
around the frame: `scc --arch arm` allocates and releases its frame by
moving `sp` (`sub sp, sp, #n` / `add sp, sp, #n`, or the stack check `sub
x9, sp, #n; …; add sp, x9, #0`), sets the frame pointer (`add x29, sp,
#n`), and ends its blocks with `b`, `b.cond`, `cbz`/`cbnz`, `bl` or `ret`.
So the block is stated over a **region** of the stack (`Region`,
`Spike/Lib/Region.lean`, based at the entry `sp`) and **static offsets**:

* **Static offsets** (`SO`): the offset of `sp` and of every general
  register known to hold `base + k`; `SORel` relates them to the register
  file. `soReg` updates them across a register operation: `add`/`sub` of an
  immediate to a known register or `sp` gives a known destination (`sp`
  included), any other write forgets the register, and a write of an
  unknown value to `sp` is not covered.
* **Classification** (`classify`): `ldr`/`str Xt, [sp, #n]` (64-bit,
  scaled immediate), a **register operation** (`RegOnly`: the operations of
  `A64Block.RegOnly`, and `add`/`sub` with an integer immediate writing any
  register or `sp`), or a **branch** to a label (`b`, `b.cond`, `cbz`,
  `cbnz`, `bl`) or `ret Xn`, which can only end the block. A stack access
  needs `sp` 16-aligned (Kraken's alignment check), decided on the static
  offset given a 16-aligned base.
* **One theorem for all register operations** (`interp_regOnly`): Kraken's
  own `Operation.interp` of a register operation is its continuation
  applied to `regRes op m`; and `regRes_getRegOrSp64`: it keeps every
  register `regDst` does not name. Both by one case split on `RegOnly`.
* **An abstract state** (`AS`, `Abs`, `DFrame`) and an abstract run
  (`arun lab blk am`, with the labels `lab`, the pc and the static offsets
  in `AM`) that reduce by `simp` on a concrete block.
* **Kraken's rows** (`Kraken/Promising/Lower/EventsA64.lean`) give each
  step through the cell at the pc: `exec_ldr_sp`, `exec_str_sp`, `exec_b`,
  `exec_bcond`, `exec_cbz`, `exec_cbnz`, `exec_bl`, `exec_ret`, and
  `exec_reg` for the register operations (`exec_ai`).
* **`seg_block`**: from every pair of `P` (at the block's address, its cells
  there, the region related to an abstract state at offsets `o`), the
  source stutters until the last instruction, which carries the source's
  local run; the exit sees the machine data of `arun` at its static offsets
  and the pc `arun` computes: the address after the block, a label, either
  edge of a conditional branch, or the address in the register `ret` reads.
  Exits to labels are `Seg` exits, so blocks compose with
  `Seg.seq`/`Seg.loop`. `seg_blockW` is the same inside a predicate `W` on
  the hidden pairs and closed under outside moves `K` (`SegW`), given `W`
  and no `K` move at each internal state.

`block_spec` generates, for a concrete block, `okBlk` by `decide` and the
closed form of `arun` by `simp` (`Spike/Lib/A64Hello.lean` applies it to a
whole listing). The module lives in `Spike.Lib.A64.Flow` so that its names
(`AS`, `Abs`, `AI`, `seg_block`, …) do not clash with `A64Block`'s.
-/
import Spike.Lib.A64
import Spike.Lib.Region
import Spike.Lib.SegW

namespace Spike.Lib.A64.Flow

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64

set_option linter.unusedSimpArgs false

/-! ## Register operations -/

/-- **A register operation**: reads and writes only general registers, `sp`
and flags, reads no label and no pc (`add`/`sub Xd|SP, Xn|SP, #imm` may
write `sp`). -/
def RegOnly {w : RegWidth} : Operation w → Bool
  | .ADD_s .. | .ADDS_s .. | .SUB_s .. | .SUBS_s .. | .MADD .. | .MSUB .. | .AND_s .. | .ORR_s ..
  | .EOR_s .. | .UBFM .. | .SBFM .. | .LSLV .. | .LSRV .. | .ASRV .. | .CSEL .. | .CSINC .. | .MRS .. => true
  | .MOVZ _ (.int64 _) _ | .MOVK _ (.int64 _) _ => true
  | .ADD_e _ _ (.imm ⟨.int64 _, _⟩) | .SUB_e _ _ (.imm ⟨.int64 _, _⟩) => true
  | .SUBS_e _ _ (.imm ⟨.int64 _, _⟩) => true
  | _ => false

/-- The register a `RegOrZr` operand names as a destination (none for the
zero register). -/
def zrB {w : RegWidth} : RegOrZr w → Option XRegOrSp
  | .low (.reg x) _ => some (.reg x)
  | .low .XZR _ => none

/-- **The register a register operation writes**, if any (`sp` included). -/
def regDst {w : RegWidth} : Operation w → Option XRegOrSp
  | .ADD_s d .. | .ADDS_s d .. | .SUB_s d .. | .SUBS_s d .. | .MADD d .. | .MSUB d .. | .AND_s d ..
  | .ORR_s d .. | .EOR_s d .. | .UBFM d .. | .SBFM d .. | .LSLV d .. | .LSRV d .. | .ASRV d .. | .CSEL d ..
  | .CSINC d .. | .MOVZ d .. | .MOVK d .. | .SUBS_e d .. => zrB d
  | .MRS d _ => zrB d
  | .ADD_e d .. | .SUB_e d .. => some d.base
  | _ => none

/-- No labels (a register operation reads none). -/
abbrev labels0 : Labels := ⟨fun _ => 0⟩

/-- **The machine data a register operation computes**, by Kraken's own
`Operation.interp`. -/
def regRes {w : RegWidth} (op : Operation w) (m : MachineData) : MachineData :=
  match @Operation.interp labels0 w op ⟨0, 0⟩ m (fun m' => .done (m', 0)) (fun _ m' => .done (m', 0)) with
  | .done (m', _) => m'
  | _ => m

/-- **Every register operation, at once**: `Operation.interp` continues with
`regRes op m`, whatever the labels, pc range and continuations. -/
theorem interp_regOnly [Labels] {w : RegWidth} {op : Operation w} (h : RegOnly op = true)
    (p : Std.Rco Int64) (m : MachineData) (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects) :
    Operation.interp op p m next jmp = next (regRes op m) := by
  unfold RegOnly at h
  split at h <;> first | rfl | exact absurd h (by decide)

/-- A register operation's result depends on the registers and flags only. -/
theorem regRes_eq {w : RegWidth} {op : Operation w} (h : RegOnly op = true) (m : MachineData) :
    regRes op m = { m with regs := (regRes op { m with dmem := ∅ }).regs,
                           status := (regRes op { m with dmem := ∅ }).status } := by
  unfold RegOnly at h
  split at h <;> first | rfl | exact absurd h (by decide)

/-- A register operation keeps the private memory. -/
theorem regRes_dmem {w : RegWidth} {op : Operation w} (h : RegOnly op = true) (m : MachineData) :
    (regRes op m).dmem = m.dmem := by
  rw [regRes_eq h]

theorem lse2Free_of_regOnly {w : RegWidth} {op : Operation w} (h : RegOnly op = true) :
    (Directive.instr ⟨w, op⟩).LSE2Free := by
  unfold RegOnly at h
  split at h <;> first | exact absurd h (by decide) | trivial | (cases w <;> trivial)

theorem Reg64s.getRegOrSp64_setRegOrSp64_ne (s : Reg64s) {d r : XRegOrSp} (h : r ≠ d) (v : BitVec 64) :
    (s.setRegOrSp64 d v).getRegOrSp64 r = s.getRegOrSp64 r := by
  rcases d with x | _ <;> rcases r with y | _
  · cases x <;> cases y <;> first | exact absurd rfl h | rfl
  · cases x <;> rfl
  · cases y <;> rfl
  · exact absurd rfl h

theorem Reg64s.getRegOrSp64_setRegOrSp64_self (s : Reg64s) (d : XRegOrSp) (v : BitVec 64) :
    (s.setRegOrSp64 d v).getRegOrSp64 d = v := by
  rcases d with x | _
  · cases x <;> simp [Reg64s.setRegOrSp64, Reg64s.getRegOrSp64, Reg64s.setXReg, Reg64s.getXReg]
  · simp [Reg64s.setRegOrSp64, Reg64s.getRegOrSp64]

theorem Reg64s.getRegOrSp64_setRegOrZr_ne (s : Reg64s) {w : RegWidth} (d : RegOrZr w) (v : w.type)
    {r : XRegOrSp} (h : ∀ x, zrB d = some x → r ≠ x) : (s.setRegOrZr d v).getRegOrSp64 r = s.getRegOrSp64 r := by
  rcases d with ⟨x | _, w⟩
  · have h' : r ≠ .reg x := h _ rfl
    cases w <;> exact Reg64s.getRegOrSp64_setRegOrSp64_ne s h' _
  · cases w <;> rfl

theorem Reg64s.getRegOrSp64_setRegOrSp_ne (s : Reg64s) {w : RegWidth} (d : RegOrSp w) (v : w.type)
    {r : XRegOrSp} (h : r ≠ d.base) : (s.setRegOrSp d v).getRegOrSp64 r = s.getRegOrSp64 r := by
  rcases d with ⟨b, w⟩
  cases w <;> exact Reg64s.getRegOrSp64_setRegOrSp64_ne s h _

/-- **A register operation keeps every register it does not write.** -/
theorem regRes_getRegOrSp64 {w : RegWidth} {op : Operation w} (h : RegOnly op = true) (m : MachineData)
    {r : XRegOrSp} (hr : ∀ d, regDst op = some d → r ≠ d) :
    (regRes op m).regs.getRegOrSp64 r = m.regs.getRegOrSp64 r := by
  unfold RegOnly at h
  split at h <;> first
    | exact absurd h (by decide)
    | (simp only [regDst] at hr
       simp only [regRes, Operation.interp, MachineData.setRegOrZr, MachineData.setRegOrSp]
       first
       | exact Reg64s.getRegOrSp64_setRegOrZr_ne _ _ _ hr
       | exact Reg64s.getRegOrSp64_setRegOrSp_ne _ _ _ (hr _ rfl)
       | rfl)

/-! ## Static offsets -/

/-- **Static offsets** of a point in a block: `sp` holds `base + sp`, and
each listed general register `x` holds `base + k`. They are computed from
the code alone (`AI.so`), so they are concrete on a concrete block. -/
structure SO where
  sp : Int
  regs : List (XReg × Int)

/-- The static offset of a register or `sp`, if known. -/
def SO.get (o : SO) : XRegOrSp → Option Int
  | .SP => some o.sp
  | .reg x => lk o.regs x

/-- Forget a general register's offset. -/
def SO.kill (o : SO) (x : XReg) : SO := { o with regs := rm o.regs x }

/-- Set the offset of a register or `sp`. -/
def SO.set (o : SO) : XRegOrSp → Int → SO
  | .SP, k => { o with sp := k }
  | .reg x, k => { sp := o.sp, regs := (x, k) :: rm o.regs x }

/-- A write of an unknown value: not covered for `sp`, which must stay
known. -/
def SO.write (o : SO) : XRegOrSp → Option SO
  | .SP => none
  | .reg x => some (o.kill x)

/-- Forget the general register a `RegOrZr` destination names. -/
def SO.killZ {w : RegWidth} (o : SO) : RegOrZr w → SO
  | .low (.reg x) _ => o.kill x
  | .low .XZR _ => o

theorem SO.get_kill (o : SO) (x : XReg) (r : XRegOrSp) :
    (o.kill x).get r = if r = .reg x then none else o.get r := by
  rcases r with y | _
  · simp only [SO.get, SO.kill, lk_rm, XRegOrSp.reg.injEq]
  · simp [SO.get, SO.kill]

theorem SO.get_set (o : SO) (d : XRegOrSp) (k : Int) (r : XRegOrSp) :
    (o.set d k).get r = if r = d then some k else o.get r := by
  rcases d with x | _ <;> rcases r with y | _
  · simp only [SO.set, SO.get, lk, lk_rm, XRegOrSp.reg.injEq]
    by_cases h : y = x <;> simp [h]
  · simp [SO.set, SO.get]
  · simp [SO.set, SO.get]
  · simp [SO.set, SO.get]

/-- **The registers agree with the static offsets** in region `R`. -/
def SORel (R : Region) (o : SO) (regs : Reg64s) : Prop :=
  ∀ r k, o.get r = some k → regs.getRegOrSp64 r = R.addr k

theorem SORel.kill {R : Region} {o : SO} {regs regs' : Reg64s} (hr : SORel R o regs) (x : XReg)
    (hk : ∀ r, r ≠ .reg x → regs'.getRegOrSp64 r = regs.getRegOrSp64 r) : SORel R (o.kill x) regs' := by
  intro r k h
  rw [SO.get_kill] at h
  split at h
  · cases h
  · rename_i hrx
    rw [hk r hrx]; exact hr r k h

theorem SORel.write {R : Region} {o o' : SO} {d : XRegOrSp} {regs regs' : Reg64s} (hw : o.write d = some o')
    (hr : SORel R o regs) (hk : ∀ r, r ≠ d → regs'.getRegOrSp64 r = regs.getRegOrSp64 r) : SORel R o' regs' := by
  rcases d with x | _
  · cases hw
    exact hr.kill x hk
  · cases hw

theorem SORel.set {R : Region} {o : SO} {d : XRegOrSp} {k : Int} {regs regs' : Reg64s} (hr : SORel R o regs)
    (hd : regs'.getRegOrSp64 d = R.addr k) (hk : ∀ r, r ≠ d → regs'.getRegOrSp64 r = regs.getRegOrSp64 r) :
    SORel R (o.set d k) regs' := by
  intro r k' h
  rw [SO.get_set] at h
  split at h
  · rename_i hrd; cases h; subst hrd; exact hd
  · rename_i hrd; rw [hk r hrd]; exact hr r k' h

theorem SORel.killZ {R : Region} {o : SO} {regs : Reg64s} (hr : SORel R o regs) {w : RegWidth} (t : RegOrZr w)
    (v : w.type) : SORel R (o.killZ t) (regs.setRegOrZr t v) := by
  rcases t with ⟨x | _, w⟩
  · exact hr.kill x fun r hrx => Reg64s.getRegOrSp64_setRegOrZr_ne _ _ _ (by
      simp only [zrB, Option.some.injEq]; rintro _ rfl; exact hrx)
  · intro r k h
    rw [Reg64s.getRegOrSp64_setRegOrZr_ne _ _ _ (by simp [zrB])]
    exact hr r k h

/-- **The static offsets after a register operation**: `add`/`sub` of an
immediate to a known register or `sp` gives a known register or `sp` (the
frame allocation `sub sp, sp, #n`, the stack-check `sub x9, sp, #n; …;
add sp, x9, #0`, the frame pointer `add x29, sp, #n`, the release `add sp,
sp, #n`); any other write forgets the register, and is not covered on
`sp`. -/
def soReg : (w : RegWidth) → Operation w → SO → Option SO
  | .W64, .ADD_e (.low d .W64) (.low s .W64) (.imm ⟨.int64 n, .S0⟩), o =>
    match o.get s with
    | some k => some (o.set d (k + n.toInt))
    | none => o.write d
  | .W64, .SUB_e (.low d .W64) (.low s .W64) (.imm ⟨.int64 n, .S0⟩), o =>
    match o.get s with
    | some k => some (o.set d (k - n.toInt))
    | none => o.write d
  | _, op, o =>
    match regDst op with
    | some d => o.write d
    | none => some o

theorem Reg64s.getRegOrSp_low64 (s : Reg64s) (r : XRegOrSp) : s.getRegOrSp (.low r .W64) = s.getRegOrSp64 r := by
  simp [Reg64s.getRegOrSp, RegOrSp.base, BitVec.take, BitVec.setWidth_eq]

theorem soReg_sound {R : Region} {w : RegWidth} {op : Operation w} (h : RegOnly op = true) {o o' : SO}
    (hs : soReg w op o = some o') {m : MachineData} (hr : SORel R o m.regs) :
    SORel R o' (regRes op m).regs := by
  have hk : ∀ r, (∀ d, regDst op = some d → r ≠ d) → (regRes op m).regs.getRegOrSp64 r = m.regs.getRegOrSp64 r :=
    fun r hr => regRes_getRegOrSp64 h m hr
  unfold soReg at hs
  split at hs
  · split at hs
    · rename_i d s n k hgk
      cases hs
      refine SORel.set hr ?_ fun r hrd => hk r (by simpa [regDst, RegOrSp.base] using hrd)
      simp only [regRes, Operation.interp, MachineData.setRegOrSp, Reg64s.setRegOrSp,
        Reg64s.getRegOrSp64_setRegOrSp64_self, Reg64s.getRegOrSp_low64, ExtOrImmReg.interp, ConstExpr.interp]
      rw [hr _ _ hgk, Region.addr_add]
    · exact SORel.write hs hr fun r hrd => hk r (by simpa [regDst, RegOrSp.base] using hrd)
  · split at hs
    · rename_i d s n k hgk
      cases hs
      refine SORel.set hr ?_ fun r hrd => hk r (by simpa [regDst, RegOrSp.base] using hrd)
      simp only [regRes, Operation.interp, MachineData.setRegOrSp, Reg64s.setRegOrSp,
        Reg64s.getRegOrSp64_setRegOrSp64_self, Reg64s.getRegOrSp_low64, ExtOrImmReg.interp, ConstExpr.interp]
      rw [hr _ _ hgk, Region.addr_sub]
    · exact SORel.write hs hr fun r hrd => hk r (by simpa [regDst, RegOrSp.base] using hrd)
  · split at hs
    · rename_i d hd
      exact SORel.write hs hr fun r hrd => hk r (by rw [hd]; simpa using hrd)
    · rename_i hd
      cases hs
      exact fun r k hg => (hk r (by simp [hd])).trans (hr r k hg)

/-! ## The abstract state -/

/-- **The abstract state of a block**: Kraken's registers and flags, and the
region's cells by offset. -/
structure AS where
  regs : Reg64s
  status : StatusFlags
  slot : Int → BitVec 64

/-- **The machine data `m` is the abstract state `σ`** in region `R` at
static offsets `o`: same registers and flags, the registers and `sp` at
their static offsets, and each cell of the region mapped in private memory
and holding `σ.slot k`. -/
structure Abs (R : Region) (o : SO) (m : MachineData) (σ : AS) : Prop where
  regs : m.regs = σ.regs
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

/-- **A covered instruction**: a stack load or store, a register operation,
or a branch (`b`, `b.cond`, `cbz`, `cbnz`, `bl`, `ret`), which can only end
a block. -/
inductive AI where
  /-- `ldr Xt, [sp, #n]`. -/
  | ldr (t : RegOrZr .W64) (n : Int64)
  /-- `str Xt, [sp, #n]`. -/
  | str (t : RegOrZr .W64) (n : Int64)
  /-- A register operation (`RegOnly`). -/
  | reg (w : RegWidth) (op : Operation w)
  /-- `b L`. -/
  | b (L : Label)
  /-- `b.cond L`. -/
  | bcond (c : CondCode) (L : Label)
  /-- `cbz Xt, L`. -/
  | cbz (t : RegOrZr .W64) (L : Label)
  /-- `cbnz Xt, L`. -/
  | cbnz (t : RegOrZr .W64) (L : Label)
  /-- `bl L`. -/
  | bl (L : Label)
  /-- `ret Xn`. -/
  | ret (r : RegOrZr .W64)

/-- The directive of a covered instruction. -/
def AI.toDir : AI → Directive
  | .ldr t n => .instr ⟨.W64, .LDR t (.addr ⟨.SP, .imm ⟨.int64 n, none⟩⟩)⟩
  | .str t n => .instr ⟨.W64, .STR t ⟨.SP, .imm ⟨.int64 n, none⟩⟩⟩
  | .reg w op => .instr ⟨w, op⟩
  | .b L => .instr ⟨.W64, .B (.label L)⟩
  | .bcond c L => .instr ⟨.W64, .B_cond c (.label L)⟩
  | .cbz t L => .instr ⟨.W64, .CBZ t (.label L)⟩
  | .cbnz t L => .instr ⟨.W64, .CBNZ t (.label L)⟩
  | .bl L => .instr ⟨.W64, .BL (.label L)⟩
  | .ret r => .instr ⟨.W64, .RET r⟩

/-- **Classify a directive.** -/
def classify : Directive → Option AI
  | .instr ⟨.W64, .LDR t (.addr ⟨.SP, .imm ⟨.int64 n, none⟩⟩)⟩ => some (.ldr t n)
  | .instr ⟨.W64, .STR t ⟨.SP, .imm ⟨.int64 n, none⟩⟩⟩ => some (.str t n)
  | .instr ⟨.W64, .B (.label L)⟩ => some (.b L)
  | .instr ⟨.W64, .B_cond c (.label L)⟩ => some (.bcond c L)
  | .instr ⟨.W64, .CBZ t (.label L)⟩ => some (.cbz t L)
  | .instr ⟨.W64, .CBNZ t (.label L)⟩ => some (.cbnz t L)
  | .instr ⟨.W64, .BL (.label L)⟩ => some (.bl L)
  | .instr ⟨.W64, .RET r⟩ => some (.ret r)
  | .instr ⟨w, op⟩ => if RegOnly op then some (.reg w op) else none
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
cells in `[lo, hi)`: a stack access is inside and `sp` is 16-aligned (the
alignment check of an `sp`-based access), a register operation keeps `sp`
known. -/
def AI.ok (lo hi : Int) (o : SO) : AI → Bool
  | .ldr _ n | .str _ n => offOk lo hi (o.sp + n.toInt) && decide (o.sp % 16 = 0)
  | .reg w op => (soReg w op o).isSome
  | _ => true

/-- **The static offsets after a covered instruction.** -/
def AI.so (o : SO) : AI → SO
  | .ldr t _ => o.killZ t
  | .reg w op => (soReg w op o).getD o
  | .bl _ => o.kill .X30
  | _ => o

/-- A branch (it ends a block). -/
def AI.isTerm : AI → Bool
  | .ldr .. | .str .. | .reg .. => false
  | _ => true

/-- **The abstract step** at static offsets `o`, `fall` being the address
after the instruction: a load writes the register, a store the cell, a
register operation does what Kraken's step does (`regRes`), `bl` writes the
return address `fall` to `x30`. -/
def AI.step (o : SO) (fall : Int64) : AI → AS → AS
  | .ldr t n, σ => { σ with regs := σ.regs.setRegOrZr t (σ.slot (o.sp + n.toInt)) }
  | .str t n, σ => { σ with slot := upd σ.slot (o.sp + n.toInt) (σ.regs.getRegOrZr t) }
  | .reg _ op, σ =>
    { σ with regs := (regRes op ⟨σ.regs, σ.status, ∅⟩).regs, status := (regRes op ⟨σ.regs, σ.status, ∅⟩).status }
  | .bl _, σ => { σ with regs := σ.regs.setRegOrZr (.low (.reg .X30) .W64) (BitVec.ofInt 64 fall.toInt) }
  | _, σ => σ

/-- **The next pc**: `fall`, a label (`lab`), the taken or fall-through
edge of a conditional branch, or the address `ret` reads. -/
def AI.tgt (lab : Label → Int64) (fall : Int64) : AI → AS → Int64
  | .b L, _ | .bl L, _ => lab L
  | .bcond c L, σ => if c.interp σ.status then lab L else fall
  | .cbz t L, σ => if σ.regs.getRegOrZr t = 0 then lab L else fall
  | .cbnz t L, σ => if σ.regs.getRegOrZr t ≠ 0 then lab L else fall
  | .ret r, σ => Int64.ofInt (σ.regs.getRegOrZr r).signed
  | _, _ => fall

theorem AI.tgt_of_not_term {a : AI} (h : a.isTerm = false) (lab : Label → Int64) (fall : Int64) (σ : AS) :
    a.tgt lab fall σ = fall := by
  cases a <;> first | rfl | cases h

/-- **A covered block for cells in `[lo, hi)` from static offsets `o`**:
every directive classified, its side condition holds at its static offsets,
and only the last one is a branch (decided on a concrete block). -/
def okBlk (lo hi : Int) : SO → List Directive → Bool
  | _, [] => true
  | o, d :: ds =>
    match classify d with
    | some a => a.ok lo hi o && (ds.isEmpty || !a.isTerm) && okBlk lo hi (a.so o) ds
    | none => false

/-- **An abstract machine state**: pc, static offsets, abstract state. -/
structure AM where
  pc : Int64
  so : SO
  σ : AS

/-- One directive's abstract step (the identity off the covered ones). -/
def dstep (lab : Label → Int64) (am : AM) (d : Directive) : AM :=
  match classify d with
  | some a => ⟨a.tgt lab (am.pc + Int64.ofNat 4) am.σ, a.so am.so, a.step am.so (am.pc + Int64.ofNat 4) am.σ⟩
  | none => am

/-- **The abstract run of a block**, with the labels `lab`. -/
def arun (lab : Label → Int64) (blk : List Directive) (am : AM) : AM := blk.foldl (dstep lab) am

theorem arun_take_succ (lab : Label → Int64) {blk : List Directive} {k : Nat} (hk : k < blk.length) (am : AM) :
    arun lab (blk.take (k + 1)) am = dstep lab (arun lab (blk.take k) am) blk[k] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [arun, List.foldl_append, Option.toList, List.foldl]

/-- The `k`-th directive of a covered block is classified, its side
condition holds at the static offsets the run reaches, and it is not a
branch unless it is the last. -/
theorem okBlk_get (lab : Label → Int64) {lo hi : Int} {blk : List Directive} {am : AM}
    (h : okBlk lo hi am.so blk = true) {k : Nat} (hk : k < blk.length) :
    ∃ a, classify blk[k] = some a ∧ a.ok lo hi (arun lab (blk.take k) am).so = true ∧
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

/-- **The pc before the `k`-th directive** of a covered block: `4k` past
the entry (no branch before the last). -/
theorem arun_pc (lab : Label → Int64) {lo hi : Int} {blk : List Directive} {am : AM}
    (h : okBlk lo hi am.so blk = true) {k : Nat} (hk : k < blk.length) :
    (arun lab (blk.take k) am).pc = am.pc + Int64.ofNat (4 * k) := by
  induction blk generalizing am k with
  | nil => cases hk
  | cons d ds ih =>
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
        have := ih (am := dstep lab am d) (by simpa [dstep, ha] using hrest) hk'
        simp only [List.take_succ_cons, arun, List.foldl] at this ⊢
        rw [this]
        simp only [dstep, ha, AI.tgt_of_not_term hnt]
        rw [Int64.add_assoc, ← Int64.ofNat_add]
        congr 2
        omega
      · cases h

/-! ## One covered instruction -/

/-- A label's address in `st`'s program. -/
abbrev labA (st : State) (L : Label) : Int64 := (_root_.Executable.labels st.exe).label L

/-- **A register operation's cell**: no event, the machine data `regRes`
gives. -/
theorem exec_reg {st : State} {sz : Nat} {w : RegWidth} {op : Operation w} (h : RegOnly op = true)
    (hc : CellAt st (.instr ⟨w, op⟩) sz) :
    isaLSE2.exec st = some (.done (after st sz (regRes op st.st.1))) := by
  show execLSE2 _ = _
  rw [execLSE2_of_cellAt_free hc (lse2Free_of_regOnly h)]
  simp only [Directive.interp, Instr.interp, @interp_regOnly (_root_.Executable.labels st.exe) _ _ h, toEv,
    EvTree.map]
  rfl

/-- `sp`'s value, as the static offsets say. -/
theorem SORel.sp {R : Region} {o : SO} {regs : Reg64s} (hr : SORel R o regs) : regs.SP.toBitVec = R.addr o.sp :=
  hr .SP o.sp rfl

/-- The address of `[sp, #n]`. -/
theorem addr_spn (R : Region) (k : Int) (n : Int64) :
    BitVec.ofInt 64 ((R.addr k).toInt + n.toInt) = R.addr (k + n.toInt) := by
  rw [BitVec.ofInt_add, BitVec.ofInt_toInt, Region.addr_add]

/-- **One covered instruction** at the pc: no event; the next pc is
`AI.tgt`, the machine data the abstract step's at the new static offsets,
with the memory outside the region unchanged. -/
theorem exec_ai {st : State} {R : Region} {lo hi : Int} {o : SO} {σ : AS} {a : AI} (hok : a.ok lo hi o = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) (hc : CellAt st a.toDir 4)
    (hreg : ∀ w op, a = .reg w op → RegOnly op = true) (hA : Abs R o st.st.1 σ) :
    ∃ m', isaLSE2.exec st = some (.done { st with st := (m', a.tgt (labA st) (st.st.2 + Int64.ofNat 4) σ) }) ∧
      Abs R (a.so o) m' (a.step o (st.st.2 + Int64.ofNat 4) σ) ∧ DFrame R st.st.1 m' := by
  have hsp : st.st.1.regs.SP.toBitVec = R.addr o.sp := by rw [hA.regs]; exact hA.so.sp
  cases a with
  | ldr t n =>
    simp only [AI.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hk, h16⟩ := hok
    have ho := offOk_off hk hlo hhi
    obtain ⟨j, hj, hjv⟩ := hA.slot _ ho
    refine ⟨_, exec_ldr_sp hc (by rw [hsp]; exact R.addr_align16 hal h16) (by rw [hsp, addr_spn]) hj, ?_,
      DFrame.refl _ _⟩
    refine ⟨by simp [AI.step, hA.regs, hjv], hA.status, ?_, hA.slot⟩
    simp only [AI.so, AI.step]
    exact hA.so.killZ t _
  | str t n =>
    simp only [AI.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hk, h16⟩ := hok
    have ho := offOk_off hk hlo hhi
    obtain ⟨j, hj, -⟩ := hA.slot _ ho
    obtain ⟨hsl, hD⟩ := hA.store hR ho (σ.regs.getRegOrZr t)
    refine ⟨_, exec_str_sp hc (by rw [hsp]; exact R.addr_align16 hal h16) (by rw [hsp, addr_spn]) hj, ?_, ?_⟩
    · refine ⟨hA.regs, hA.status, hA.so, fun k' hk' => ?_⟩
      simp only [AI.step]
      rw [hA.regs]
      exact hsl k' hk'
    · rw [hA.regs]; exact hD
  | reg w op =>
    have hr := hreg w op rfl
    simp only [AI.ok] at hok
    obtain ⟨o', ho'⟩ := Option.isSome_iff_exists.mp hok
    refine ⟨_, exec_reg hr hc, ?_, fun b _ _ => by rw [regRes_dmem hr]⟩
    have he := regRes_eq hr st.st.1
    have hm : ({ st.st.1 with dmem := ∅ } : MachineData) = ⟨σ.regs, σ.status, ∅⟩ := by
      rw [← hA.regs, ← hA.status]
    rw [hm] at he
    refine ⟨by rw [he]; rfl, by rw [he]; rfl, ?_, ?_⟩
    · simp only [AI.so, AI.step, ho', Option.getD_some]
      have := soReg_sound hr ho' (m := ⟨σ.regs, σ.status, ∅⟩) hA.so
      exact this
    · intro k hk
      rw [he]
      exact hA.slot k hk
  | b L =>
    exact ⟨_, exec_b hc, hA, DFrame.refl _ _⟩
  | bcond c L =>
    refine ⟨_, ?_, hA, DFrame.refl _ _⟩
    rw [exec_bcond hc]
    simp only [AI.tgt, hA.status]; rfl
  | cbz t L =>
    refine ⟨_, ?_, hA, DFrame.refl _ _⟩
    rw [exec_cbz hc]
    simp only [AI.tgt, hA.regs]; rfl
  | cbnz t L =>
    refine ⟨_, ?_, hA, DFrame.refl _ _⟩
    rw [exec_cbnz hc]
    simp only [AI.tgt, hA.regs]; rfl
  | bl L =>
    refine ⟨_, exec_bl hc, ⟨by simp only [AI.step, hA.regs, retAddr], hA.status, ?_, hA.slot⟩, DFrame.refl _ _⟩
    simp only [AI.so, AI.step]
    exact hA.so.killZ (.low (.reg .X30) .W64) _
  | ret r =>
    refine ⟨_, ?_, hA, DFrame.refl _ _⟩
    rw [exec_ret hc]
    simp only [AI.tgt, hA.regs]

/-! ## Blocks -/

section Block

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}

/-- **A block simulates a local run of the source, inside `W`**: from every
pair of `P`, the block's instructions are no-event steps; the source stutters
until the last one, which carries a local run `c ↦ c'`; at the exit the
machine data is related to the abstract run's state at its static offsets,
with the memory outside the region unchanged, and the pc is the abstract
run's: the address after the block, or the target of the final branch (a
label, either edge of a conditional branch, the address `ret` reads). The
block's internal states (before its `k`-th instruction, the machine data
related to the abstract run of the first `k` instructions, the memory
outside the region unchanged, the source control as at entry) are in `W`
and not moved by `K` (a block holds no take). One theorem for every block
with `okBlk lo hi o blk = true` (decided on a concrete block). -/
theorem seg_blockW {W : Frag isaLSE2} {K : State → State → Prop} {R : Region} {pc : Int64} {lo hi : Int} {o : SO} {blk : List Directive}
    (hne : blk ≠ []) {P Q : Frag isaLSE2}
    (h : ∀ s c, P s c → s.st.2 = pc ∧ CodeAt s pc blk ∧ okBlk lo hi o blk = true ∧ R.OK ∧
      R.base.toNat % 16 = 0 ∧ R.lo ≤ lo ∧ hi ≤ R.hi ∧ ∃ σ, Abs R o s.st.1 σ ∧
      (∀ k < blk.length, ∀ m, Abs R (arun (labA s) (blk.take k) ⟨pc, o, σ⟩).so m
          (arun (labA s) (blk.take k) ⟨pc, o, σ⟩).σ → DFrame R s.st.1 m →
        W { s with st := (m, pc + Int64.ofNat (4 * k)) } c ∧
          ∀ s', ¬ K { s with st := (m, pc + Int64.ofNat (4 * k)) } s') ∧
      ∃ c', LocalRun p c c' ∧ ∀ m', Abs R (arun (labA s) blk ⟨pc, o, σ⟩).so m'
          (arun (labA s) blk ⟨pc, o, σ⟩).σ → DFrame R s.st.1 m' →
        Q { s with st := (m', (arun (labA s) blk ⟨pc, o, σ⟩).pc) } c') :
    SegW W K p lbl ms P Q := by
  refine ⟨fun s c => ∃ (s0 : State) (σ0 : AS) (c' : Ctl) (k : Nat) (m : MachineData), k < blk.length ∧
      s = { s0 with st := (m, pc + Int64.ofNat (4 * k)) } ∧ CodeAt s0 pc blk ∧ okBlk lo hi o blk = true ∧
      R.OK ∧ R.base.toNat % 16 = 0 ∧ R.lo ≤ lo ∧ hi ≤ R.hi ∧
      Abs R (arun (labA s0) (blk.take k) ⟨pc, o, σ0⟩).so m (arun (labA s0) (blk.take k) ⟨pc, o, σ0⟩).σ ∧
      DFrame R s0.st.1 m ∧
      (∀ k < blk.length, ∀ m, Abs R (arun (labA s0) (blk.take k) ⟨pc, o, σ0⟩).so m
          (arun (labA s0) (blk.take k) ⟨pc, o, σ0⟩).σ → DFrame R s0.st.1 m →
        W { s0 with st := (m, pc + Int64.ofNat (4 * k)) } c ∧
          ∀ s', ¬ K { s0 with st := (m, pc + Int64.ofNat (4 * k)) } s') ∧ LocalRun p c c' ∧
      (∀ m', Abs R (arun (labA s0) blk ⟨pc, o, σ0⟩).so m' (arun (labA s0) blk ⟨pc, o, σ0⟩).σ →
        DFrame R s0.st.1 m' → Q { s0 with st := (m', (arun (labA s0) blk ⟨pc, o, σ0⟩).pc) } c'), ?_, ?_, ?_⟩
  · intro s c hP
    obtain ⟨hpc, hcode, hok, hR, hal, hlo, hhi, σ, hA, hW, c', hr, hQ⟩ := h s c hP
    refine ⟨s, σ, c', 0, s.st.1, List.length_pos_iff.mpr hne, ?_, hcode, hok, hR, hal, hlo, hhi,
      by simpa [arun] using hA, DFrame.refl _ _, hW, hr, hQ⟩
    obtain ⟨exe, endPc, ⟨m, q⟩, showPc, decls⟩ := s
    simp only at hpc
    subst hpc
    rw [show q + Int64.ofNat (4 * 0) = q by simp]
  · rintro s c ⟨s0, σ0, c', k, m, hk, rfl, -, -, -, -, -, -, hA, hD, hW, -, -⟩
    exact (hW k hk m hA hD).1
  · rintro s c ⟨s0, σ0, c', k, m, hk, rfl, hcode, hok, hR, hal, hlo, hhi, hA, hD, hW, hr, hQ⟩
    refine ⟨fun _ => ?_, KOut.none (hW k hk m hA hD).2⟩
    have hd : blk[k]? = some blk[k] := List.getElem?_eq_getElem hk
    obtain ⟨a, hca, haok, hnt⟩ := okBlk_get (labA s0) (am := ⟨pc, o, σ0⟩) hok hk
    obtain ⟨hdir, hreg⟩ := classify_sound hca
    have hc : CellAt { s0 with st := (m, pc + Int64.ofNat (4 * k)) } a.toDir 4 :=
      hcode.cell (j := k) (hdir ▸ hd) rfl rfl rfl
    obtain ⟨m', hex, hA', hD'⟩ := exec_ai haok hR hal hlo hhi hc hreg hA
    have hpck := arun_pc (labA s0) (am := ⟨pc, o, σ0⟩) hok hk
    have hstep : arun (labA s0) (blk.take (k + 1)) ⟨pc, o, σ0⟩ =
        ⟨a.tgt (labA s0) (pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
          (arun (labA s0) (blk.take k) ⟨pc, o, σ0⟩).σ,
         a.so (arun (labA s0) (blk.take k) ⟨pc, o, σ0⟩).so,
         a.step (arun (labA s0) (blk.take k) ⟨pc, o, σ0⟩).so (pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
          (arun (labA s0) (blk.take k) ⟨pc, o, σ0⟩).σ⟩ := by
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
      refine .silent _ c hex (.refl c) (.inl ⟨s0, σ0, c', k + 1, m', by omega, ?_, hcode, hok, hR, hal, hlo, hhi,
        by rw [hstep]; exact hA', hD.trans hD', hW, hr, hQ⟩)
      simp only [AI.tgt_of_not_term hnt']
      rw [Int64.add_assoc, ← Int64.ofNat_add]
      congr 3

/-- **A block simulates a local run of the source** (`seg_blockW` with no
predicate on the internal states). -/
theorem seg_block {R : Region} {pc : Int64} {lo hi : Int} {o : SO} {blk : List Directive} (hne : blk ≠ [])
    {P Q : Frag isaLSE2}
    (h : ∀ s c, P s c → s.st.2 = pc ∧ CodeAt s pc blk ∧ okBlk lo hi o blk = true ∧ R.OK ∧
      R.base.toNat % 16 = 0 ∧ R.lo ≤ lo ∧ hi ≤ R.hi ∧ ∃ σ, Abs R o s.st.1 σ ∧
      ∃ c', LocalRun p c c' ∧ ∀ m', Abs R (arun (labA s) blk ⟨pc, o, σ⟩).so m'
          (arun (labA s) blk ⟨pc, o, σ⟩).σ → DFrame R s.st.1 m' →
        Q { s with st := (m', (arun (labA s) blk ⟨pc, o, σ⟩).pc) } c') :
    Seg p lbl ms P Q :=
  (seg_blockW (W := fun _ _ => True) (K := fun _ _ => False) hne fun s c hP =>
    let ⟨hpc, hcode, hok, hR, hal, hlo, hhi, σ, hA, hr⟩ := h s c hP
    ⟨hpc, hcode, hok, hR, hal, hlo, hhi, σ, hA, fun _ _ _ _ _ => ⟨trivial, fun _ h => h⟩, hr⟩).toSeg

end Block

/-! ## Per-block specifications, generated -/

namespace BlockSpec

open Lean Meta Elab Command Term

/-- The definitions `simp` unfolds to run a concrete block on a symbolic
abstract state. -/
def unfolds : List Name :=
  [``arun, ``dstep, ``classify, ``RegOnly, ``AI.so, ``AI.step, ``AI.tgt, ``soReg, ``regDst, ``zrB, ``regRes,
   ``Operation.interp, ``MachineData.setRegOrZr, ``MachineData.setRegOrSp, ``Reg64s.setRegOrZr,
   ``Reg64s.getRegOrZr, ``Reg64s.setRegOrZr64, ``Reg64s.getRegOrZr64, ``Reg64s.setRegOrSp, ``Reg64s.getRegOrSp,
   ``Reg64s.setRegOrSp64, ``Reg64s.getRegOrSp64, ``Reg64s.setXReg, ``Reg64s.getXReg, ``ShiftRegExpr.interp,
   ``ExtOrImmReg.interp, ``ConstExpr.interp, ``RegOrZr.base, ``RegOrSp.base, ``SO.get, ``SO.set, ``SO.kill,
   ``SO.write, ``SO.killZ, ``lk, ``rm, ``List.foldl]

/- Non-`rfl` equations for `AI.step` and `AI.tgt`: `simp` applies them with
a proof, leaving the kernel no definitional gap to close (closing one would
re-evaluate the block under the free `σ`, where the kernel's `Nat` literal
arithmetic is disabled). -/
section NoRfl
variable (o : SO) (f : Int64) (σ : AS) (lab : Label → Int64)
theorem AI.step_ldr' t n :
    AI.step o f (.ldr t n) σ = { σ with regs := σ.regs.setRegOrZr t (σ.slot (o.sp + n.toInt)) } := by
  cases σ; rfl
theorem AI.step_str' t n :
    AI.step o f (.str t n) σ = { σ with slot := upd σ.slot (o.sp + n.toInt) (σ.regs.getRegOrZr t) } := by
  cases σ; rfl
theorem AI.step_reg' w op :
    AI.step o f (.reg w op) σ =
      { σ with regs := (regRes op ⟨σ.regs, σ.status, ∅⟩).regs,
               status := (regRes op ⟨σ.regs, σ.status, ∅⟩).status } := by
  cases σ; rfl
theorem AI.step_bl' L :
    AI.step o f (.bl L) σ = { σ with regs := σ.regs.setRegOrZr (.low (.reg .X30) .W64) (BitVec.ofInt 64 f.toInt) } := by
  cases σ; rfl
theorem AI.step_b' L : AI.step o f (.b L) σ = σ := by cases σ; rfl
theorem AI.step_bcond' c L : AI.step o f (.bcond c L) σ = σ := by cases σ; rfl
theorem AI.step_cbz' t L : AI.step o f (.cbz t L) σ = σ := by cases σ; rfl
theorem AI.step_cbnz' t L : AI.step o f (.cbnz t L) σ = σ := by cases σ; rfl
theorem AI.step_ret' r : AI.step o f (.ret r) σ = σ := by cases σ; rfl
theorem AI.tgt_b' L : AI.tgt lab f (.b L) σ = lab L := by cases σ; rfl
theorem AI.tgt_bl' L : AI.tgt lab f (.bl L) σ = lab L := by cases σ; rfl
theorem AI.tgt_bcond' c L : AI.tgt lab f (.bcond c L) σ = if c.interp σ.status then lab L else f := by cases σ; rfl
theorem AI.tgt_cbz' t L : AI.tgt lab f (.cbz t L) σ = if σ.regs.getRegOrZr t = 0 then lab L else f := by cases σ; rfl
theorem AI.tgt_cbnz' t L : AI.tgt lab f (.cbnz t L) σ = if σ.regs.getRegOrZr t ≠ 0 then lab L else f := by cases σ; rfl
theorem AI.tgt_ret' r : AI.tgt lab f (.ret r) σ = Int64.ofInt (σ.regs.getRegOrZr r).signed := by cases σ; rfl
theorem AI.tgt_ldr' t n : AI.tgt lab f (.ldr t n) σ = f := by cases σ; rfl
theorem AI.tgt_str' t n : AI.tgt lab f (.str t n) σ = f := by cases σ; rfl
theorem AI.tgt_reg' w op : AI.tgt lab f (.reg w op) σ = f := by cases σ; rfl
end NoRfl

/-- The non-`rfl` equations, used in place of unfolding `AI.step`, `AI.tgt`. -/
def noRfl : List Name :=
  [``AI.step_ldr', ``AI.step_str', ``AI.step_reg', ``AI.step_bl', ``AI.step_b', ``AI.step_bcond', ``AI.step_cbz',
   ``AI.step_cbnz', ``AI.step_ret', ``AI.tgt_b', ``AI.tgt_bl', ``AI.tgt_bcond', ``AI.tgt_cbz', ``AI.tgt_cbnz',
   ``AI.tgt_ret', ``AI.tgt_ldr', ``AI.tgt_str', ``AI.tgt_reg']

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
simprocs, `unfolds` with `AI.step`/`AI.tgt` through `noRfl`, and
`upd_apply`, without unfolding `StatusFlags.subs`) makes of the abstract run
for symbolic labels, entry pc and abstract state. `blk` may be the name of a definition
(unfolded by `simp`), so that a function's proof can name its blocks. -/
elab "block_spec " nm:ident lo:term:max hi:term:max o:term:max blk:term : command => do
  let okId := mkIdent (nm.getId.appendAfter "_ok")
  elabCommand (← `(theorem $okId : okBlk $lo $hi $o $blk = true := by decide))
  let runName := (← getCurrNamespace) ++ nm.getId.appendAfter "_run"
  liftTermElabM do
    let b ← elabTermEnsuringType blk (← mkAppM ``List #[mkConst ``Directive])
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
    -- `StatusFlags.subs` stays folded: unfolded on a known constant its `C`/`V` are
    -- `Nat`/`Int` arithmetic whose `simp` cost grows with the constant.
    thms ← thms.erase (.decl ``StatusFlags.subs)
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

end Spike.Lib.A64.Flow
