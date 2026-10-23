/-
**Straight-line blocks on AArch64**: one theorem for every block of
register operations and stack-slot accesses.

`scc` keeps every IR register in a frame slot (`[sp, #8·i]`) and computes
in scratch registers, so most of its code is runs of `ldr Xt, [sp, #o]`,
register operations and `str Xt, [sp, #o]` with no shared-memory event
(`Spike/Lib/A64.lean`, module docstring). This module proves the `Seg`
judgement for every such run at once (`seg_block`), instead of one `Out`
row per instruction:

* **Classification** (`classify`): a directive is a slot load `ldr Xt, [sp,
  #o]`, a slot store `str Xt, [sp, #o]` (64-bit, scaled immediate), or a
  **register operation** (`RegOnly`: `add`/`sub`/`adds`/`subs`/`madd`/
  `msub`/`and`/`orr`/`eor`/`ubfm`/`sbfm`/`lslv`/`lsrv`/`asrv`/`csel`/
  `csinc`/`mrs`, `movz`/`movk` and `add`/`sub`/`subs` with an integer
  immediate, `add`/`sub` not writing `sp`), or not covered.
* **One theorem for all register operations** (`interp_regOnly`): Kraken's
  own `Operation.interp` of a register operation is its continuation
  applied to `regRes op m`, the machine data `Operation.interp` itself
  computes (with no labels and a dummy pc range, which a register operation
  does not read). Proved once, by one case split on `RegOnly`; the abstract
  step of a register operation *is* Kraken's step (`regRes`), so nothing
  about any instruction's meaning is restated.
* **An abstract state** (`AS`): the register file and flags as Kraken has
  them, and the frame's slots as a function `Int64 → BitVec 64` (`Abs`
  relates it to the private memory; `DFrame`: memory outside the frame is
  unchanged). `AI.step` is a structurally recursive function on concrete
  directives, so `arun blk σ` on a concrete block reduces by `simp`/`rfl`
  with `σ` symbolic.
* **Kraken's executable step is never reduced**: `isaLSE2.exec` goes through
  `execLSE2_of_cellAt_free` (the cell at the pc, `CellAt`) to
  `Directive.interp`, which is structural; the well-founded
  `withAddresses`/`codeAt` stays behind the `CodeAt` hypothesis.
* **`seg_block`**: from every pair of `P` (at the block's address, the
  block's cells there, the frame related to an abstract state `σ`), the
  source stutters until the last instruction, which carries the source's
  local run; the exit sees the machine data of `arun blk σ`. The side
  condition `okBlk n blk = true` (each directive classified, each slot
  offset inside a frame of `n` bytes) is decided on the concrete block.

`Slots.abs`/`Slots.of_abs` move between the slot fragment (`Slots`) and
`Abs`. `seg_add'` re-derives the checked `+` of `Spike/Lib/A64.lean` with
its two straight-line parts as `seg_block` instances (offsets symbolic),
with the statement of `seg_add`. `seg_sub`: the saturating `-` (`subSat`:
`subs` then `csel`, `Scc/Emit/A64.lean`) as one `seg_block` instance, for
any operand words (`Scc.Sem.valRep_subW`). `block_spec` generates, for a concrete
block, `okBlk` by `decide` and the closed form of `arun` by `simp`
(`Spike/Lib/A64Hello.lean` applies it to a whole listing).
-/
import Spike.Lib.A64
import Scc.Sem.TypingRows

namespace Spike.Lib.A64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (ValRep)

set_option linter.unusedSimpArgs false

/-! ## Register operations -/

/-- **A register operation**: reads and writes only general registers (never
`sp`) and flags, reads no label and no pc. -/
def RegOnly {w : RegWidth} : Operation w → Bool
  | .ADD_s .. | .ADDS_s .. | .SUB_s .. | .SUBS_s .. | .MADD .. | .MSUB .. | .AND_s .. | .ORR_s ..
  | .EOR_s .. | .UBFM .. | .SBFM .. | .LSLV .. | .LSRV .. | .ASRV .. | .CSEL .. | .CSINC .. | .MRS .. => true
  | .MOVZ _ (.int64 _) _ | .MOVK _ (.int64 _) _ => true
  | .ADD_e (.low (.reg _) _) _ (.imm ⟨.int64 _, _⟩) => true
  | .SUB_e (.low (.reg _) _) _ (.imm ⟨.int64 _, _⟩) => true
  | .SUBS_e _ _ (.imm ⟨.int64 _, _⟩) => true
  | _ => false

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

theorem Reg64s.setXReg_SP (r : Reg64s) (x : XReg) (v : BitVec 64) : (r.setXReg x v).SP = r.SP := by
  cases x <;> rfl

theorem Reg64s.setRegOrZr_SP (r : Reg64s) {w : RegWidth} (d : RegOrZr w) (v : w.type) :
    (r.setRegOrZr d v).SP = r.SP := by
  cases d with
  | low x => cases w <;> cases x <;> simp [Reg64s.setRegOrZr, Reg64s.setRegOrZr64, Reg64s.setXReg_SP]

theorem Reg64s.setRegOrSp_reg_SP (r : Reg64s) {w : RegWidth} (x : XReg) (v : w.type) :
    (r.setRegOrSp (.low (.reg x) w) v).SP = r.SP := by
  cases w <;> simp [Reg64s.setRegOrSp, Reg64s.setRegOrSp64, Reg64s.setXReg_SP]

/-- A register operation keeps `sp`. -/
theorem regRes_SP {w : RegWidth} {op : Operation w} (h : RegOnly op = true) (m : MachineData) :
    (regRes op m).regs.SP = m.regs.SP := by
  unfold RegOnly at h
  split at h <;> first
    | exact absurd h (by decide)
    | simp only [regRes, Operation.interp, MachineData.setRegOrZr, MachineData.setRegOrSp,
        Reg64s.setRegOrZr_SP, Reg64s.setRegOrSp_reg_SP]

/-- A register operation keeps the private memory. -/
theorem regRes_dmem {w : RegWidth} {op : Operation w} (h : RegOnly op = true) (m : MachineData) :
    (regRes op m).dmem = m.dmem := by
  rw [regRes_eq h]

theorem lse2Free_of_regOnly {w : RegWidth} {op : Operation w} (h : RegOnly op = true) :
    (Directive.instr ⟨w, op⟩).LSE2Free := by
  unfold RegOnly at h
  split at h <;> first | exact absurd h (by decide) | trivial | (cases w <;> trivial)

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

/-! ## The abstract state -/

/-- **The abstract state of a block**: Kraken's registers and flags, and the
frame's slots by offset. -/
structure AS where
  regs : Reg64s
  status : StatusFlags
  slot : Int64 → BitVec 64

/-- **The machine data `m` is the abstract state `σ`** in frame `F`: same
registers and flags, `sp` at the frame, and each slot of the frame mapped in
private memory and holding `σ.slot o`. -/
structure Abs (F : Frame) (m : MachineData) (σ : AS) : Prop where
  regs : m.regs = σ.regs
  status : m.status = σ.status
  sp : σ.regs.SP.toBitVec = F.sp
  slot : ∀ o, F.Off o → ∃ j, Mem.loadInt m.dmem (slotA F.sp o) 8 = some j ∧ BitVec.ofInt 64 j = σ.slot o

/-- **The private memory outside the frame is unchanged** from `m` to `m'`
(every 8-byte range that does not meet the frame). -/
def DFrame (F : Frame) (m m' : MachineData) : Prop :=
  ∀ a : BitVec 64, a.toNat + 8 ≤ 2 ^ 64 → (a.toNat + 8 ≤ F.sp.toNat ∨ F.sp.toNat + F.size ≤ a.toNat) →
    Mem.loadInt m'.dmem a 8 = Mem.loadInt m.dmem a 8

theorem DFrame.refl (F : Frame) (m : MachineData) : DFrame F m m := fun _ _ _ => rfl

theorem DFrame.trans {F : Frame} {m₁ m₂ m₃ : MachineData} (h₁ : DFrame F m₁ m₂) (h₂ : DFrame F m₂ m₃) :
    DFrame F m₁ m₃ := fun a ha hd => (h₂ a ha hd).trans (h₁ a ha hd)

/-! ## Classification -/

/-- Update a slot file at one offset. -/
def upd (f : Int64 → BitVec 64) (o : Int64) (v : BitVec 64) : Int64 → BitVec 64 :=
  fun o' => if o' = o then v else f o'

@[simp] theorem upd_self (f : Int64 → BitVec 64) (o : Int64) (v : BitVec 64) : upd f o v o = v := by
  simp [upd]

/-- A slot read through an update (for `simp` on an applied slot file). -/
theorem upd_apply (f : Int64 → BitVec 64) (o : Int64) (v : BitVec 64) (o' : Int64) :
    upd f o v o' = if o' = o then v else f o' := rfl

theorem upd_of_ne {f : Int64 → BitVec 64} {o o' : Int64} {v : BitVec 64} (h : o' ≠ o) : upd f o v o' = f o' := by
  simp [upd, h]

/-- **A covered instruction**: a slot load, a slot store, or a register
operation. -/
inductive AI where
  /-- `ldr Xt, [sp, #o]`. -/
  | ldr (t : RegOrZr .W64) (o : Int64)
  /-- `str Xt, [sp, #o]`. -/
  | str (t : RegOrZr .W64) (o : Int64)
  /-- A register operation (`RegOnly`). -/
  | reg (w : RegWidth) (op : Operation w)

/-- The directive of a covered instruction. -/
def AI.toDir : AI → Directive
  | .ldr t o => .instr ⟨.W64, .LDR t (.addr ⟨.SP, .imm ⟨.int64 o, none⟩⟩)⟩
  | .str t o => .instr ⟨.W64, .STR t ⟨.SP, .imm ⟨.int64 o, none⟩⟩⟩
  | .reg w op => .instr ⟨w, op⟩

/-- **Classify a directive.** -/
def classify : Directive → Option AI
  | .instr ⟨.W64, .LDR t (.addr ⟨.SP, .imm ⟨.int64 o, none⟩⟩)⟩ => some (.ldr t o)
  | .instr ⟨.W64, .STR t ⟨.SP, .imm ⟨.int64 o, none⟩⟩⟩ => some (.str t o)
  | .instr ⟨w, op⟩ => if RegOnly op then some (.reg w op) else none
  | _ => none

theorem classify_sound {d : Directive} {a : AI} (h : classify d = some a) :
    d = a.toDir ∧ (∀ w op, a = .reg w op → RegOnly op = true) := by
  unfold classify at h
  split at h
  · cases h; exact ⟨rfl, by simp⟩
  · cases h; exact ⟨rfl, by simp⟩
  · split at h
    · cases h; exact ⟨rfl, by rintro w op ⟨⟩; assumption⟩
    · cases h
  · cases h

/-- A slot offset inside a frame of `n` bytes. -/
def offOk (n : Nat) (o : Int64) : Bool := decide (0 ≤ o.toInt ∧ o.toInt % 8 = 0 ∧ o.toInt + 8 ≤ n)

/-- The side condition of a covered instruction in a frame of `n` bytes. -/
def AI.ok (n : Nat) : AI → Bool
  | .ldr _ o | .str _ o => offOk n o
  | .reg .. => true

theorem offOk_off {n : Nat} {F : Frame} {o : Int64} (h : offOk n o = true) (hn : n ≤ F.size) : F.Off o := by
  simp only [offOk, decide_eq_true_eq] at h
  exact ⟨h.1, h.2.1, by omega⟩

/-- **The abstract step**: a slot load writes the register, a slot store the
slot, a register operation does what Kraken's step does (`regRes`). -/
def AI.step : AI → AS → AS
  | .ldr t o, σ => { σ with regs := σ.regs.setRegOrZr t (σ.slot o) }
  | .str t o, σ => { σ with slot := upd σ.slot o (σ.regs.getRegOrZr t) }
  | .reg _ op, σ =>
    { σ with regs := (regRes op ⟨σ.regs, σ.status, ∅⟩).regs, status := (regRes op ⟨σ.regs, σ.status, ∅⟩).status }

/-- **A covered block in a frame of `n` bytes**: every directive is
classified and its side condition holds (decided on a concrete block). -/
def okBlk (n : Nat) (blk : List Directive) : Bool :=
  blk.all fun d => match classify d with
    | some a => a.ok n
    | none => false

/-- One directive's abstract step (the identity off the covered ones). -/
def dstep (σ : AS) (d : Directive) : AS :=
  match classify d with
  | some a => a.step σ
  | none => σ

/-- **The abstract run of a block.** -/
def arun (blk : List Directive) (σ : AS) : AS := blk.foldl dstep σ

theorem arun_take_succ {blk : List Directive} {k : Nat} (hk : k < blk.length) (σ : AS) :
    arun (blk.take (k + 1)) σ = dstep (arun (blk.take k) σ) blk[k] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [arun, List.foldl_append, Option.toList, List.foldl]

/-! ## One covered instruction -/

theorem ofInt_toNat (x : BitVec 64) : BitVec.ofInt 64 (x.toNat : Int) = x := by
  simp

/-- **One covered instruction** at the pc: no event, and the machine data is
the abstract step's, with the memory outside the frame unchanged. -/
theorem exec_ai {st : State} {F : Frame} {n : Nat} {σ : AS} {a : AI} (hok : a.ok n = true)
    (hn : n ≤ F.size) (hF : F.OK) (hc : CellAt st a.toDir 4) (hreg : ∀ w op, a = .reg w op → RegOnly op = true)
    (hA : Abs F st.st.1 σ) :
    ∃ m', isaLSE2.exec st = some (.done (after st 4 m')) ∧ Abs F m' (a.step σ) ∧ DFrame F st.st.1 m' := by
  have hsp : st.st.1.regs.SP.toBitVec = F.sp := by rw [hA.regs]; exact hA.sp
  cases a with
  | ldr t o =>
    have ho := offOk_off hok hn
    obtain ⟨j, hj, hjv⟩ := hA.slot o ho
    refine ⟨_, exec_ldr_sp hc (by rw [hsp]; exact hF.align) (by rw [hsp]; rfl) hj, ?_, DFrame.refl _ _⟩
    refine ⟨by simp [AI.step, hA.regs, hjv], hA.status, ?_, hA.slot⟩
    simp only [AI.step, Reg64s.setRegOrZr_SP]; exact hA.sp
  | str t o =>
    have ho := offOk_off hok hn
    obtain ⟨j, hj, -⟩ := hA.slot o ho
    refine ⟨_, exec_str_sp hc (by rw [hsp]; exact hF.align) (by rw [hsp]; rfl) hj, ?_, ?_⟩
    · refine ⟨hA.regs, hA.status, hA.sp, fun o' ho' => ?_⟩
      simp only [AI.step]
      by_cases hoo : o' = o
      · subst hoo
        refine ⟨_, loadInt_storeInt8_same _ _ _, ?_⟩
        rw [ofInt_toNat, upd_self, hA.regs]
      · rw [loadInt_storeInt8_disj _ _ _ _ (slot_fit hF ho) (slot_fit hF ho') (slot_sep hF ho ho' (Ne.symm hoo)),
          upd_of_ne hoo]
        exact hA.slot o' ho'
    · intro b hb hd
      apply loadInt_storeInt8_disj _ _ _ _ (slot_fit hF ho) hb
      rw [slotA_toNat hF ho]
      obtain ⟨h0, -, h5⟩ := ho
      omega
  | reg w op =>
    have hr := hreg w op rfl
    refine ⟨_, exec_reg hr hc, ?_, fun b _ _ => by rw [regRes_dmem hr]⟩
    have he := regRes_eq hr st.st.1
    have hm : ({ st.st.1 with dmem := ∅ } : MachineData) = ⟨σ.regs, σ.status, ∅⟩ := by
      rw [← hA.regs, ← hA.status]
    rw [hm] at he
    refine ⟨by rw [he]; rfl, by rw [he]; rfl, ?_, ?_⟩
    · simp only [AI.step]
      rw [regRes_SP hr]; exact hA.sp
    · intro o ho
      rw [regRes_dmem hr]
      exact hA.slot o ho

/-! ## Blocks -/

section Block

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}

theorem pc_add (pc : Int64) (k : Nat) : pc + Int64.ofNat (4 * k) + Int64.ofNat 4 = pc + Int64.ofNat (4 * (k + 1)) := by
  rw [Int64.add_assoc, ← Int64.ofNat_add]; rfl

/-- **A straight-line block simulates a local run of the source**: from every
pair of `P`, the block's instructions are no-event steps; the source
stutters until the last one, which carries a local run `c ↦ c'`; at the exit
the machine data is related to `arun blk σ`, with the memory outside the
frame unchanged. One theorem for every block with `okBlk n blk = true`
(decided on a concrete block, or derived from the frame's facts when the
offsets are symbolic). -/
theorem seg_block {F : Frame} {pc : Int64} {n : Nat} {blk : List Directive} (hne : blk ≠ [])
    {P Q : Frag isaLSE2}
    (h : ∀ s c, P s c → s.st.2 = pc ∧ CodeAt s pc blk ∧ okBlk n blk = true ∧ F.OK ∧ n ≤ F.size ∧
      ∃ σ, Abs F s.st.1 σ ∧
      ∃ c', LocalRun p c c' ∧ ∀ m', Abs F m' (arun blk σ) → DFrame F s.st.1 m' →
        Q { s with st := (m', pc + Int64.ofNat (4 * blk.length)) } c') :
    Seg p lbl ms P Q := by
  refine ⟨fun s c => ∃ (s0 : State) (σ0 : AS) (c' : Ctl) (k : Nat) (m : MachineData), k < blk.length ∧
      s = { s0 with st := (m, pc + Int64.ofNat (4 * k)) } ∧ CodeAt s0 pc blk ∧ okBlk n blk = true ∧ F.OK ∧
      n ≤ F.size ∧
      Abs F m (arun (blk.take k) σ0) ∧ DFrame F s0.st.1 m ∧ LocalRun p c c' ∧
      (∀ m', Abs F m' (arun blk σ0) → DFrame F s0.st.1 m' →
        Q { s0 with st := (m', pc + Int64.ofNat (4 * blk.length)) } c'), ?_, ?_⟩
  · intro s c hP
    obtain ⟨hpc, hcode, hok, hF, hn, σ, hA, c', hr, hQ⟩ := h s c hP
    refine ⟨s, σ, c', 0, s.st.1, List.length_pos_iff.mpr hne, ?_, hcode, hok, hF, hn, by simpa [arun] using hA,
      DFrame.refl _ _, hr, hQ⟩
    obtain ⟨exe, endPc, ⟨m, q⟩, showPc, decls⟩ := s
    simp only at hpc
    subst hpc
    rw [show q + Int64.ofNat (4 * 0) = q by simp]
  · rintro s c ⟨s0, σ0, c', k, m, hk, rfl, hcode, hok, hF, hn, hA, hD, hr, hQ⟩
    have hd : blk[k]? = some blk[k] := List.getElem?_eq_getElem hk
    have hcl : ∃ a, classify blk[k] = some a ∧ a.ok n = true := by
      have := List.all_eq_true.mp hok blk[k] (List.getElem_mem hk)
      revert this
      cases hc : classify blk[k] with
      | none => simp
      | some a => intro ha; exact ⟨a, rfl, ha⟩
    obtain ⟨a, hca, haok⟩ := hcl
    obtain ⟨hdir, hreg⟩ := classify_sound hca
    have hc : CellAt { s0 with st := (m, pc + Int64.ofNat (4 * k)) } a.toDir 4 :=
      hcode.cell (j := k) (hdir ▸ hd) rfl rfl rfl
    obtain ⟨m', hex, hA', hD'⟩ := exec_ai haok hn hF hc hreg hA
    have hstep : arun (blk.take (k + 1)) σ0 = a.step (arun (blk.take k) σ0) := by
      rw [arun_take_succ hk]; simp [dstep, hca]
    by_cases hlast : k + 1 = blk.length
    · refine .silent _ c' hex hr (.inr ?_)
      have hQ' := hQ m' (by rw [← List.take_length (l := blk), ← hlast, hstep]; exact hA') (hD.trans hD')
      simp only [after]
      rw [pc_add, hlast]
      exact hQ'
    · refine .silent _ c hex (.refl c) (.inl ⟨s0, σ0, c', k + 1, m', by omega, ?_, hcode, hok, hF, hn,
        by rw [hstep]; exact hA', hD.trans hD', hr, hQ⟩)
      simp only [after]
      rw [pc_add]

end Block

/-! ## The slot fragment as an abstract state -/

section SlotsAbs

variable {lbl : WeakMem.AllocLabel → Option Nat} {F : Frame} {slot : String → Option Int64} {s : State}
  {env : TermRun.Env}

/-- The abstract state of a thread state in frame `F`: its registers and
flags, each slot's 8 bytes. -/
def absOf (F : Frame) (m : MachineData) : AS :=
  ⟨m.regs, m.status, fun o => BitVec.ofInt 64 ((Mem.loadInt m.dmem (slotA F.sp o) 8).getD 0)⟩

theorem Slots.abs (h : Slots lbl F slot s env) : Abs F s.st.1 (absOf F s.st.1) where
  regs := rfl
  status := rfl
  sp := h.sp
  slot o ho := by
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (h.mapped o ho)
    exact ⟨j, hj, by simp [absOf, hj]⟩

/-- Each placed variable's slot, in the abstract state, represents it. -/
theorem Slots.rep_abs (h : Slots lbl F slot s env) {x : String} {o : Int64} (hx : slot x = some o) :
    ∃ ty w, TermRun.lookupE env x = some (ty, [w]) ∧ ValRep lbl w.val ((absOf F s.st.1).slot o).toNat := by
  obtain ⟨ty, w, j, hl, hj, hv⟩ := h.rep x o hx
  exact ⟨ty, w, hl, by simpa [absOf, hj] using hv⟩

/-- **Back to the slot fragment**: after a block, for a new placement `slot'`
and environment `env'` whose placed variables are represented by the
abstract slots. -/
theorem Slots.of_abs (h : Slots lbl F slot s env) {m' : MachineData} {σ' : AS} (hA : Abs F m' σ')
    (hD : DFrame F s.st.1 m') (q : Int64) {slot' : String → Option Int64} {env' : TermRun.Env}
    (off : ∀ x o, slot' x = some o → F.Off o) (inj : ∀ x y o, slot' x = some o → slot' y = some o → x = y)
    (rep : ∀ x o, slot' x = some o → ∃ ty w, TermRun.lookupE env' x = some (ty, [w]) ∧
      ValRep lbl w.val (σ'.slot o).toNat) :
    Slots lbl F slot' { s with st := (m', q) } env' where
  ok := h.ok
  sp := by rw [hA.regs]; exact hA.sp
  off := off
  inj := inj
  rep x o hx := by
    obtain ⟨ty, w, hl, hv⟩ := rep x o hx
    obtain ⟨j, hj, hjv⟩ := hA.slot o (off x o hx)
    exact ⟨ty, w, j, hl, hj, by rw [hjv]; exact hv⟩
  mapped o ho := by
    obtain ⟨j, hj, -⟩ := hA.slot o ho
    simp [hj]
  heap w a hl hv := by
    obtain ⟨h1, h2, h3, h4⟩ := h.heap w a hl hv
    exact ⟨by rw [hD a h3 h4]; exact h1, h2, h3, h4⟩

/-- **After a block that writes no placed slot**: the same placement and
environment. -/
theorem Slots.keep_abs (h : Slots lbl F slot s env) {m' : MachineData} {σ' : AS} (hA : Abs F m' σ')
    (hD : DFrame F s.st.1 m') (q : Int64) (hkeep : ∀ o, σ'.slot o = (absOf F s.st.1).slot o) :
    Slots lbl F slot { s with st := (m', q) } env :=
  h.of_abs hA hD q h.off h.inj fun _ _ hy => by rw [hkeep]; exact h.rep_abs hy

/-- **After a block that writes one free slot `od`**: the variable `x`,
bound first to a word that the slot represents, is placed there. -/
theorem Slots.bind_abs (h : Slots lbl F slot s env) {m' : MachineData} {σ' : AS} (hA : Abs F m' σ')
    (hD : DFrame F s.st.1 m') (q : Int64) {x : String} {od : Int64} {ty : Ty} {w : TermRun.Word}
    (hod : F.Off od) (hfree : ∀ y, slot y = some od → y = x)
    (hkeep : ∀ o, o ≠ od → σ'.slot o = (absOf F s.st.1).slot o) (hv : ValRep lbl w.val (σ'.slot od).toNat) :
    Slots lbl F (fun y => if y = x then some od else slot y) { s with st := (m', q) } ((x, ty, [w]) :: env) := by
  refine h.of_abs hA hD q ?_ ?_ fun y o hy => ?_
  · intro y o hy
    by_cases hyx : y = x
    · simp only [hyx, ↓reduceIte, Option.some.injEq] at hy; exact hy ▸ hod
    · simp only [hyx, ↓reduceIte] at hy; exact h.off y o hy
  · intro y z o hy hz
    by_cases hyx : y = x <;> by_cases hzx : z = x
    · rw [hyx, hzx]
    · simp only [hyx, hzx, ↓reduceIte, Option.some.injEq] at hy hz
      subst hy; exact absurd (hfree z hz) hzx
    · simp only [hyx, hzx, ↓reduceIte, Option.some.injEq] at hy hz
      subst hz; exact absurd (hfree y hy) hyx
    · simp only [hyx, hzx, ↓reduceIte] at hy hz; exact h.inj y z o hy hz
  · by_cases hyx : y = x
    · simp only [hyx, ↓reduceIte, Option.some.injEq] at hy
      subst hy hyx
      exact ⟨ty, w, by simp [TermRun.lookupE], hv⟩
    · simp only [hyx, ↓reduceIte] at hy
      obtain ⟨ty', w', hl, hv'⟩ := h.rep_abs hy
      have hne : (x == y) = false := by simp [Ne.symm hyx]
      have hoo : o ≠ od := by rintro rfl; exact hyx (hfree y hy)
      refine ⟨ty', w', by simp [TermRun.lookupE, List.find?, hne] at hl ⊢; exact hl, ?_⟩
      rw [hkeep o hoo]; exact hv'

end SlotsAbs

/-! ## Code segments, split -/

/-- A code segment does not depend on the machine data or pc. -/
theorem CodeAt.withSt {st : State} {pc : Int64} {ds : List Directive} (h : CodeAt st pc ds)
    (x : MachineData × Int64) : CodeAt { st with st := x } pc ds := by
  intro j d hd
  obtain ⟨h1, h2, h3⟩ := h j d hd
  exact ⟨h1, h2, h3⟩

/-- A prefix of a code segment. -/
theorem CodeAt.take {st : State} {pc : Int64} {ds : List Directive} (h : CodeAt st pc ds) (k : Nat) :
    CodeAt st pc (ds.take k) := by
  intro j d hd
  rw [List.getElem?_take] at hd
  split at hd
  · exact h j d hd
  · cases hd

/-- A suffix of a code segment, at its address. -/
theorem CodeAt.drop {st : State} {pc : Int64} {ds : List Directive} (h : CodeAt st pc ds) (k : Nat) :
    CodeAt st (pc + Int64.ofNat (4 * k)) (ds.drop k) := by
  intro j d hd
  rw [List.getElem?_drop] at hd
  have := h (k + j) d hd
  rwa [Int64.add_assoc, ← Int64.ofNat_add, ← Nat.mul_add]

/-- **Run a block on a symbolic abstract state** (`simp` with the step's
definitions), at the goal or at hypotheses. -/
macro "arun_simp" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp [arun, List.foldl, dstep,
  classify, RegOnly, AI.step, regRes, Operation.interp, MachineData.setRegOrZr, MachineData.setRegOrSp,
  Reg64s.setRegOrZr, Reg64s.getRegOrZr, Reg64s.setRegOrZr64, Reg64s.getRegOrZr64, Reg64s.setXReg, Reg64s.getXReg,
  ShiftRegExpr.interp, RegOrZr.base, RegOrSp.base, upd_apply] $[$loc]?)

/-! ## The checked `+` from blocks -/

section Add

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} {F : Frame}
  {slot : String → Option Int64}

/-- **`seg_add` again, from blocks**: `ldr x9; ldr x10; adds` and `str x9`
are `seg_block` instances (offsets symbolic: `okBlk` from the frame's
facts), `b.cs` the `Out` row of `seg_add`. Same statement
(`seg_add'_type`). -/
theorem seg_add' {pc : Int64} {x a b : String} {e : Expr} {oa ob : Int64} {L : String} {od lpc : Int64}
    {env0 : TermRun.Env} (ha : slot a = some oa) (hb : slot b = some ob) {ta tb : Ty} {wa wb : TermRun.Word}
    {n m : Nat} (hla : TermRun.lookupE env0 a = some (ta, [wa])) (hlb : TermRun.lookupE env0 b = some (tb, [wb]))
    (hna : wa.val = .num n) (hnb : wb.val = .num m) (hod : F.Off od) (hfree : ∀ y, slot y = some od → y = x) :
    Seg p lbl ms (AddIn lbl F slot pc x a b e oa ob L od lpc env0)
      (fun s c => AddOut lbl F slot pc x e oa ob L od lpc env0 (TermRun.addW wa wb) s c ∨
        AddAbort lbl F slot pc x a b e oa ob L od lpc env0 s c) := by
  have hea : TermRun.evalAt env0 (.var a) = some (ta, [wa]) := by simpa [TermRun.evalAt] using hla
  have heb : TermRun.evalAt env0 (.var b) = some (tb, [wb]) := by simpa [TermRun.evalAt] using hlb
  refine Seg.seq (Q := fun (s : State) (c : Ctl) => s.st.2 = pc + Int64.ofNat 12 ∧
      CodeAt s pc (addSeq oa ob L od) ∧ (_root_.Executable.labels s.exe).label L = lpc ∧
      c = ⟨addTerm x a b e, env0, none⟩ ∧ Slots lbl F slot s env0 ∧
      (s.st.1.status.c = true → 2 ^ 64 ≤ n + m) ∧
      (s.st.1.status.c = false → (s.st.1.regs.getRegOrZr (.low (.reg .X9) .W64)).toNat = n + m)) ?_
    (Seg.seq_left (Q := fun (s : State) (c : Ctl) => s.st.2 = pc + Int64.ofNat 16 ∧
      CodeAt s pc (addSeq oa ob L od) ∧ (_root_.Executable.labels s.exe).label L = lpc ∧
      c = ⟨e, (x, .int, [TermRun.addW wa wb]) :: env0, none⟩ ∧ Slots lbl F slot s env0 ∧
      (s.st.1.regs.getRegOrZr (.low (.reg .X9) .W64)).toNat = n + m) (Seg.step ?_) ?_)
  · -- `ldr x9; ldr x10; adds`: one block
    refine seg_block (F := F) (pc := pc) (n := F.size) (blk := [dLdr .X9 oa, dLdr .X10 ob, dAdds]) (by simp) ?_
    rintro s c ⟨hpc, hcode, hL, rfl, hS⟩
    have hoa := hS.off a oa ha
    have hob := hS.off b ob hb
    refine ⟨hpc, hcode.take 3, ?_, hS.ok, Nat.le_refl _, absOf F s.st.1, hS.abs, _, .refl _,
      fun m' hA hD => ?_⟩
    · simp [okBlk, classify, AI.ok, offOk, RegOnly, hoa.1, hoa.2.1, hoa.2.2, hob.1, hob.2.1, hob.2.2]
    obtain ⟨ta', wa', hla', hva⟩ := hS.rep_abs ha
    obtain ⟨tb', wb', hlb', hvb⟩ := hS.rep_abs hb
    rw [hla] at hla'; cases hla'
    rw [hlb] at hlb'; cases hlb'
    rw [hna] at hva; rw [hnb] at hvb
    have hr := hA.regs
    have hst := hA.status
    have hsl : ∀ o, (arun [dLdr .X9 oa, dLdr .X10 ob, dAdds] (absOf F s.st.1)).slot o = (absOf F s.st.1).slot o := by
      intro o; arun_simp
    arun_simp at hr hst
    refine ⟨rfl, hcode.withSt _, hL, rfl, hS.keep_abs hA hD _ hsl, fun hc => ?_, fun hc => ?_⟩
    · rw [hst] at hc
      simp [StatusFlags.adds, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at hc
      have := hva.2; have := hvb.2
      omega
    · rw [hst] at hc
      rw [hr]
      simp [StatusFlags.adds, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at hc ⊢
      have := hva.2; have := hvb.2
      omega
  · -- `b.cs`, as in `seg_add`
    rintro s c ⟨hpc, hcode, hL, rfl, hS, hcar, hsum⟩
    have hc := hcode.cell (j := 3) rfl rfl rfl (by rw [hpc]; try rfl)
    have hbt : branchTarget s 4 (.label L) = lpc := by
      simp [branchTarget, ConstExpr.evalBranchTarget, ConstExpr.interp, hL]
    cases hc' : s.st.1.status.c
    · refine .silent _ _ (exec_bcond hc) (.single (localStep_add rfl hea heb)) (.inl ?_)
      have h9 := hsum hc'
      refine ⟨?_, hcode.jump _ _, hL, rfl, hS.regs rfl rfl rfl, by simpa using h9⟩
      simp only [jumpTo, CondCode.interp, hc', Bool.false_eq_true, ↓reduceIte, hpc]
      exact pc_step pc (by decide)
    · refine .silent _ _ (exec_bcond hc) (.refl _) (.inr ?_)
      refine ⟨?_, hcode.jump _ _, rfl, ⟨x, .var a, .var b, e, ta, tb, wa, wb, n, m, rfl, hea, heb, hna, hnb,
        hcar hc'⟩, hS.regs rfl rfl rfl⟩
      simp only [jumpTo, CondCode.interp, hc', ↓reduceIte, hbt]
  · -- `str x9`: one block
    refine seg_block (F := F) (pc := pc + Int64.ofNat 16) (n := F.size) (blk := [dStr .X9 od]) (by simp) ?_
    rintro s c ⟨hpc, hcode, hL, rfl, hS, h9⟩
    refine ⟨hpc, ?_, ?_, hS.ok, Nat.le_refl _, absOf F s.st.1, hS.abs, _, .refl _, fun m' hA hD => ?_⟩
    · have := hcode.drop 4
      simpa [addSeq] using this
    · simp [okBlk, classify, AI.ok, offOk, hod.1, hod.2.1, hod.2.2]
    have hv : ValRep lbl (TermRun.addW wa wb).val (s.st.1.regs.getRegOrZr (.low (.reg .X9) .W64)).toNat := by
      have hlt := s.st.1.regs.X9.toNat_lt
      have h9' : s.st.1.regs.X9.toNat = n + m := by simpa using h9
      simp [TermRun.addW, hna, hnb, TermRun.cst, Promises.TVal.mk0, ValRep, h9']
      omega
    refine ⟨pc_step pc (by decide), hcode.withSt _, hL, rfl, hS.bind_abs hA hD _ hod hfree
      (fun o ho => by arun_simp; simp [ho]) (by arun_simp; simpa [absOf] using hv)⟩

theorem seg_add'_type : type_of% @seg_add' = type_of% @seg_add := rfl

end Add

/-! ## The saturating `-` from one block -/

section Sub

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} {F : Frame}
  {slot : String → Option Int64}

/-- `subs x9, x9, x10` (`subSat`: the difference, carry set iff no borrow). -/
abbrev dSubs : Directive :=
  .instr ⟨.W64, .SUBS_s (.low (.reg .X9) .W64) (.low (.reg .X9) .W64) ⟨.low (.reg .X10) .W64, 0, .LSL⟩⟩

/-- `csel x9, x9, xzr, hs` (`subSat`: the difference, or zero on a borrow). -/
abbrev dCselCs : Directive :=
  .instr ⟨.W64, .CSEL (.low (.reg .X9) .W64) (.low (.reg .X9) .W64) (.low .XZR .W64) .CS⟩

/-- The saturating `-` of slots `oa` and `ob` into slot `od` (`.subSat`). -/
def subSeq (oa ob od : Int64) : List Directive := [dLdr .X9 oa, dLdr .X10 ob, dSubs, dCselCs, dStr .X9 od]

/-- The source term of `-`. -/
def subTerm (x a b : String) (e : Expr) : Expr := .let_ x (.sub (.var a) (.var b)) e

/-- **The saturating `-` on the abstract state**: slot `od` gets the
truncated difference of slots `oa` and `ob`; no other slot changes. -/
theorem subSeq_run (σ : AS) (oa ob od : Int64) :
    ((arun (subSeq oa ob od) σ).slot od).toNat = (σ.slot oa).toNat - (σ.slot ob).toNat ∧
      ∀ o, o ≠ od → (arun (subSeq oa ob od) σ).slot o = σ.slot o := by
  obtain ⟨r, st, f⟩ := σ
  refine ⟨?_, fun o ho => ?_⟩
  · simp only [subSeq]
    arun_simp
    have h1 := (f oa).isLt
    have h2 := (f ob).isLt
    split <;> rename_i h <;> simp [BitVec.toNat_sub] at h ⊢ <;> omega
  · simp only [subSeq]
    arun_simp
    simp [ho]

/-- **Entry of `-`.** -/
def SubIn (lbl : WeakMem.AllocLabel → Option Nat) (F : Frame) (slot : String → Option Int64) (pc : Int64)
    (x a b : String) (e : Expr) (oa ob od : Int64) (env0 : TermRun.Env) : Frag isaLSE2 := fun s c =>
  s.st.2 = pc ∧ CodeAt s pc (subSeq oa ob od) ∧ c = ⟨subTerm x a b e, env0, none⟩ ∧ Slots lbl F slot s env0

/-- **Exit of `-`**: the source at `e` with `x` bound to the difference
`w`, placed at slot `od`. -/
def SubOut (lbl : WeakMem.AllocLabel → Option Nat) (F : Frame) (slot : String → Option Int64) (pc : Int64)
    (x : String) (e : Expr) (oa ob od : Int64) (env0 : TermRun.Env) (w : TermRun.Word) : Frag isaLSE2 :=
  fun s c => s.st.2 = pc + Int64.ofNat 20 ∧ CodeAt s pc (subSeq oa ob od) ∧ c = ⟨e, (x, .int, [w]) :: env0, none⟩ ∧
    Slots lbl F (fun y => if y = x then some od else slot y) s ((x, .int, [w]) :: env0)

/-- **The saturating `-` simulates the source's `-`**: one block (two slot
loads, `subs`, `csel`, the slot store), the source's local step at the
store. Any operand words: the target's truncated difference represents the
source's truncated `subW` (`Scc.Sem.valRep_subW`), so no typing is needed. -/
theorem seg_sub {pc : Int64} {x a b : String} {e : Expr} {oa ob od : Int64} {env0 : TermRun.Env}
    (ha : slot a = some oa) (hb : slot b = some ob) {ta tb : Ty} {wa wb : TermRun.Word}
    (hla : TermRun.lookupE env0 a = some (ta, [wa])) (hlb : TermRun.lookupE env0 b = some (tb, [wb]))
    (hod : F.Off od) (hfree : ∀ y, slot y = some od → y = x) :
    Seg p lbl ms (SubIn lbl F slot pc x a b e oa ob od env0)
      (SubOut lbl F slot pc x e oa ob od env0 (TermRun.subW wa wb)) := by
  have hea : TermRun.evalAt env0 (.var a) = some (ta, [wa]) := by simpa [TermRun.evalAt] using hla
  have heb : TermRun.evalAt env0 (.var b) = some (tb, [wb]) := by simpa [TermRun.evalAt] using hlb
  refine seg_block (F := F) (pc := pc) (n := F.size) (blk := subSeq oa ob od) (by simp [subSeq]) ?_
  rintro s c ⟨hpc, hcode, rfl, hS⟩
  have hoa := hS.off a oa ha
  have hob := hS.off b ob hb
  refine ⟨hpc, hcode, ?_, hS.ok, Nat.le_refl _, absOf F s.st.1, hS.abs, _,
    .single (localStep_sub rfl hea heb), fun m' hA hD => ?_⟩
  · simp [okBlk, subSeq, classify, AI.ok, offOk, RegOnly, hoa.1, hoa.2.1, hoa.2.2, hob.1, hob.2.1, hob.2.2,
      hod.1, hod.2.1, hod.2.2]
  obtain ⟨ta', wa', hla', hva⟩ := hS.rep_abs ha
  obtain ⟨tb', wb', hlb', hvb⟩ := hS.rep_abs hb
  rw [hla] at hla'; cases hla'
  rw [hlb] at hlb'; cases hlb'
  obtain ⟨hv, hkeep⟩ := subSeq_run (absOf F s.st.1) oa ob od
  refine ⟨rfl, hcode.withSt _, rfl, hS.bind_abs hA hD _ hod hfree hkeep ?_⟩
  rw [hv]
  exact Scc.Sem.valRep_subW hva hvb

end Sub

/-! ## Per-block specifications, generated -/

namespace BlockSpec

open Lean Meta Elab Command Term

/-- The definitions `simp` unfolds to run a concrete block on a symbolic
abstract state. -/
def unfolds : List Name :=
  [``arun, ``dstep, ``classify, ``RegOnly, ``AI.step, ``regRes, ``Operation.interp, ``MachineData.setRegOrZr,
   ``MachineData.setRegOrSp, ``Reg64s.setRegOrZr, ``Reg64s.getRegOrZr, ``Reg64s.setRegOrZr64,
   ``Reg64s.getRegOrZr64, ``Reg64s.setRegOrSp, ``Reg64s.getRegOrSp, ``Reg64s.setRegOrSp64, ``Reg64s.getRegOrSp64,
   ``Reg64s.setXReg, ``Reg64s.getXReg, ``ShiftRegExpr.interp, ``ExtOrImmReg.interp, ``ConstExpr.interp,
   ``RegOrZr.base, ``RegOrSp.base, ``List.foldl]

/-- **`block_spec name n blk`**: `name_ok : okBlk n blk = true` (by
`decide`) and `name_run : ∀ σ, arun blk σ = <normal form>`, the normal form
being what `simp` (the default set, the default simprocs, `unfolds` and
`upd_apply`)
makes of `arun blk σ` for a symbolic `σ`. -/
elab "block_spec " nm:ident n:num blk:term : command => do
  let okId := mkIdent (nm.getId.appendAfter "_ok")
  elabCommand (← `(theorem $okId : okBlk $n $blk = true := by decide))
  let runName := (← getCurrNamespace) ++ nm.getId.appendAfter "_run"
  liftTermElabM do
    let ty ← mkAppM ``List #[mkConst ``Directive]
    let b ← instantiateMVars (← elabTermEnsuringType blk ty)
    let mut thms ← getSimpTheorems
    for u in unfolds do
      thms ← thms.addDeclToUnfold u
    thms ← thms.addConst ``upd_apply
    let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
    let simprocs ← Simp.getSimprocs
    withLocalDeclD `σ (mkConst ``AS) fun σ => do
      let e ← mkAppM ``arun #[b, σ]
      let (r, _) ← withTheReader Core.Context (fun c => { c with maxRecDepth := 100000 }) <|
        simp e ctx #[simprocs]
      let prf ← r.getProof
      let ty ← mkForallFVars #[σ] (← mkEq e r.expr)
      let val ← mkLambdaFVars #[σ] prf
      let ty ← instantiateMVars ty
      let val ← instantiateMVars val
      addDecl (.thmDecl { name := runName, levelParams := [], type := ty, value := val })

end BlockSpec

end Spike.Lib.A64
