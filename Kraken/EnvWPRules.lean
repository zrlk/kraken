/-
The shared-location rules of the environment-aware wp Design
note: `Kraken/Promising/EnvWP.md`.

Where a `MachineWP` rule asks for the address to be mapped, the shared rule
asks for it to be outside `dmem` (`Mem.loadInt s.dmem a n = none`), for the
access to be permitted (`env.ok`), and for the tail's wp at every outcome the
environment allows (`env.step`), exactly as `Effects.AllEnv` consults the
environment. Each rule unfolds one cell, like the `MachineWP` rules.

The rules are `TripleEnv` theorems, not `@[spec]` triples: `vcgen` needs a
`Std.WP.WP` instance, and the environment wp has none (`EnvWP.md` §8). A
program mixing private and shared accesses composes them with
`Executable.wpEnv_cons`, the shared accesses by these rules and the rest by
`MachineWP.wpEnv_of_triple` of a `vcgen` triple
(`Kraken/X64/Examples/EnvWP.lean`, `Kraken/X64/Examples/AtomicsLink.lean`).

| Instruction | Rule | Access |
|---|---|---|
| `movq d(%b), %r` / `movl d(%b), %r32` | `mov_load_shared`, `mov32_load_shared` | `load .plain` of 8 / 4 |
| `movq %r, d(%b)` / `movl %r32, d(%b)` | `mov_store_shared` (`MovStoreSharedRule`), `mov32_store_shared` | `store .plain` of 8 / 4 |
| `xchgq %r, d(%b)` | `xchg_shared` (`XchgSharedRule`) | `rmw .acqRel` of 8 |
| `lock cmpxchgq %r, d(%b)` | `lock_cmpxchg_shared` | `rmw .acqRel` of 8 (writes only on a match) |
| `lock xaddq %r, d(%b)` | `lock_xadd_shared` | `rmw .acqRel` of 8 |
| `lock op $i, d(%b)`, `lock op %r, d(%b)` | `lock_bin_imm_shared`, `lock_bin_reg_shared` | `rmw .acqRel` of 8 |
| `lock inc/dec/neg/not d(%b)` | `lock_un_shared` | `rmw .acqRel` of 8 |
| `movb d(%b), %r8`; `movb $i, d(%b)`, `movb %r8, d(%b)` | `mov8_load_shared`; `mov8_store_imm_shared`, `mov8_store_reg_shared` | `load`/`store .plain` of 1 |
| `movslq (%b,%i,s), %r` | `movsxd_load_sib_shared` | `load .plain` of 4, sign-extended |
| `cmpl $i, d(%b)` | `cmp32_mem_imm_shared` | `load .plain` of 4 |
| `mfence` / `lfence` / `sfence` | `mfence_shared`, `lfence_shared`, `sfence_shared` | `fence .sy` / `.ld` / `.st` |
| `movdqa`/`movapd`/`movaps` load and store, `d(%b)` | `movdqa_load_shared`, … | one 16-byte `load`/`store` (atomic) |
| `movdqu`/`movups` load and store, `d(%b)` | `movdqu_load_shared`, … | two 8-byte pieces (`LoadPieces`/`StorePieces`) |
| `lock cmpxchg16b d(%b)` | `lock_cmpxchg16b_shared` | `rmw .acqRel` of 16 (atomic) |
| `movaps` load and store, `(%b,%i)` / `d(%b,%i)` | `movaps_load_sib1_shared`, `movaps_store_sib1_shared`, `movaps_load/store_sib1_disp_shared` | one 16-byte `load`/`store` (atomic) |
| `vmovdqa`/`vmovapd` load and store, `d(%b)`, any `AvxWidth` | `vmovdqa_load_shared`, `vmovdqa_store_shared`, `vmovapd_load/store_shared` | `AvxLoad`/`AvxStore`: one access at `W128` (atomic), else `w.bytes / 8` pieces |
| `vmovdqu` load and store, `d(%b)`, any `AvxWidth` | `vmovdqu_load_shared`, `vmovdqu_store_shared` | `w.bytes / 8` 8-byte pieces |
| `vmovaps` / `vmovups d(%b,%i), %xmm`/`%ymm` | `vmovaps_load_sib1_disp_shared`, `vmovups_load_sib1_disp_shared` | one 16-byte `load` (atomic) / four 8-byte pieces |
| `mulps d(%b,%i), %xmm`, `xorps sym(%rip), %xmm` | `mulps_load_sib1_disp_shared`, `xorps_load_rip_shared` | aligned, two 8-byte pieces (checked but not atomic in the semantics) |
| `vmulps`/`vfmadd231ps d(%b,%i), …` | `vmulps_load_sib1_disp_shared`, `vfmadd231ps_load_sib1_disp_shared` | two / four 8-byte pieces |

Every memory-operand shape with a `MachineWP` mapped-memory rule has a rule
above or a combined rule in `Kraken/EnvVCGen.lean` (the x64 parity
check): the stack and the indirect jump are combined rules only
(`push_reg_env_spec`, `pop_reg_env_spec`, `ret_env_spec`,
`jmp_mem_base_disp_env_spec`; `call_env_spec` for `call_spec`;
`call_proc_env_spec`/`call_proc_env_spec_at` for `call_proc_spec`/`_at`,
the callee's `ProcSpecEnv` from `ProcSpecEnv.of_tripleEnv`). Still open:

| `MachineWP` rule | Shape | Why not yet |
|---|---|---|
| `call_proc_specK*` | a call through a continuation-form procedure spec | no `ProcSpecKEnv` yet; `call_proc_env_spec` covers the `ProcSpec` form |
| (none) | `push`/`pop` of memory or immediates, `call *%r`/`call *d(%b)` | no mapped rule either |

Non-locked read-modify-writes to memory (`addq %r, d(%b)` …) and other
widths of `mov` have no `MachineWP` mapped rule either; on a shared location
each would be a plain load and a plain store.
-/
import Kraken.EnvWP

open Kraken

namespace Kraken.SharedEnv

/-- `LoadPieces` is monotone in its continuation. -/
theorem LoadPieces.mono {env : SharedEnv} {k₁ k₂ : List (BitVec 64) → env.State → Prop}
    (hk : ∀ vs g, k₁ vs g → k₂ vs g) :
    ∀ {n : Nat} {addr : BitVec 64} {g : env.State}, env.LoadPieces addr n g k₁ → env.LoadPieces addr n g k₂
  | 0, _, _, h => hk _ _ h
  | _ + 1, _, _, h => ⟨h.1, fun v g' hs =>
      LoadPieces.mono (k₁ := fun vs g'' => k₁ (v.setWidth 64 :: vs) g'')
        (k₂ := fun vs g'' => k₂ (v.setWidth 64 :: vs) g'') (fun _ g'' => hk _ g'') (h.2 v g' hs)⟩

/-- `StorePieces` is monotone in its continuation. -/
theorem StorePieces.mono {env : SharedEnv} {k₁ k₂ : env.State → Prop} (hk : ∀ g, k₁ g → k₂ g) :
    ∀ {ps : List (BitVec 64)} {addr : BitVec 64} {g : env.State},
      env.StorePieces addr ps g k₁ → env.StorePieces addr ps g k₂
  | [], _, _, h => hk _ h
  | _ :: _, _, _, h => ⟨h.1, fun b g' hs => StorePieces.mono hk (h.2 b g' hs)⟩

/-- The environment's side of a vector load of `w` at `addr` outside `dmem`, as
`Effects.AllEnv` reads `nonmem_load_avx`: one access of `w.bytes` if `atomic`
(the aligned 16-byte moves), else `w.bytes / 8` plain 8-byte pieces in
address order, reassembled little-endian (`SharedEnv.LoadPieces`, `ofPieces`); `k` gets the value and the
environment state after it. -/
def AvxLoad (env : SharedEnv) (atomic : Bool) (addr : BitVec 64) (w : AvxWidth) (g : env.State)
    (k : BitVec w.bits → env.State → Prop) : Prop :=
  match atomic with
  | true => env.ok (.load .plain false addr w.bytes) g ∧
      ∀ v g', env.step (.load .plain false addr w.bytes) g v g' → k (v.setWidth w.bits) g'
  | false => env.LoadPieces addr (w.bytes / 8) g (fun vs g' => k (ofPieces w.bits vs) g')

/-- The environment's side of a vector store of `v` at `addr` outside `dmem`,
as `Effects.AllEnv` reads `nonmem_store_avx`: one access if `atomic`, else
8-byte pieces in address order. -/
def AvxStore (env : SharedEnv) (atomic : Bool) (addr : BitVec 64) {w : AvxWidth} (v : BitVec w.bits)
    (g : env.State) (k : env.State → Prop) : Prop :=
  match atomic with
  | true => env.ok (.store .plain false addr w.bytes (v.setWidth 128)) g ∧
      ∀ b g', env.step (.store .plain false addr w.bytes (v.setWidth 128)) g b g' → k g'
  | false => env.StorePieces addr (toPieces v (w.bytes / 8)) g k

@[simp] theorem AvxLoad_true {env : SharedEnv} {addr : BitVec 64} {w : AvxWidth} {g : env.State}
    {k : BitVec w.bits → env.State → Prop} :
    env.AvxLoad true addr w g k = (env.ok (.load .plain false addr w.bytes) g ∧
      ∀ v g', env.step (.load .plain false addr w.bytes) g v g' → k (v.setWidth w.bits) g') := rfl

@[simp] theorem AvxLoad_false {env : SharedEnv} {addr : BitVec 64} {w : AvxWidth} {g : env.State}
    {k : BitVec w.bits → env.State → Prop} :
    env.AvxLoad false addr w g k = env.LoadPieces addr (w.bytes / 8) g (fun vs g' => k (ofPieces w.bits vs) g') :=
  rfl

@[simp] theorem AvxStore_true {env : SharedEnv} {addr : BitVec 64} {w : AvxWidth} {v : BitVec w.bits}
    {g : env.State} {k : env.State → Prop} :
    env.AvxStore true addr v g k = (env.ok (.store .plain false addr w.bytes (v.setWidth 128)) g ∧
      ∀ b g', env.step (.store .plain false addr w.bytes (v.setWidth 128)) g b g' → k g') := rfl

@[simp] theorem AvxStore_false {env : SharedEnv} {addr : BitVec 64} {w : AvxWidth} {v : BitVec w.bits}
    {g : env.State} {k : env.State → Prop} :
    env.AvxStore false addr v g k = env.StorePieces addr (toPieces v (w.bytes / 8)) g k := rfl

/-- The widths at which a VEX move is atomic (`w == .W128`), decided at a
width literal. -/
@[simp] theorem _root_.AvxWidth.W128_beq_W128 : (AvxWidth.W128 == AvxWidth.W128) = true := rfl
@[simp] theorem _root_.AvxWidth.W256_beq_W128 : (AvxWidth.W256 == AvxWidth.W128) = false := rfl
@[simp] theorem _root_.AvxWidth.W512_beq_W128 : (AvxWidth.W512 == AvxWidth.W128) = false := rfl

/-- `AvxLoad` is monotone in its continuation. -/
theorem AvxLoad.mono {env : SharedEnv} {atomic : Bool} {addr : BitVec 64} {w : AvxWidth}
    {g : env.State} {k₁ k₂ : BitVec w.bits → env.State → Prop} (hk : ∀ v g, k₁ v g → k₂ v g)
    (h : env.AvxLoad atomic addr w g k₁) : env.AvxLoad atomic addr w g k₂ := by
  cases atomic with
  | true => exact ⟨h.1, fun v g' hs => hk _ _ (h.2 v g' hs)⟩
  | false => exact LoadPieces.mono (fun vs g' => hk _ _) h

/-- `AvxStore` is monotone in its continuation. -/
theorem AvxStore.mono {env : SharedEnv} {atomic : Bool} {addr : BitVec 64} {w : AvxWidth}
    {v : BitVec w.bits} {g : env.State} {k₁ k₂ : env.State → Prop} (hk : ∀ g, k₁ g → k₂ g)
    (h : env.AvxStore atomic addr v g k₁) : env.AvxStore atomic addr v g k₂ := by
  cases atomic with
  | true => exact ⟨h.1, fun b g' hs => hk _ (h.2 b g' hs)⟩
  | false => exact StorePieces.mono hk h

end Kraken.SharedEnv

/-- A vector load outside `dmem` (`MachineData.loadAvx`), at an address
aligned where `checkAlign` asks: the environment's side (`SharedEnv.AvxLoad`). -/
theorem MachineData.loadAvx_AllEnv {env : SharedEnv} {g : env.State}
    {P : MachineState → env.State → Prop} {s : MachineData} {addr : BitVec 64} {w : AvxWidth}
    {ret : w.type → MachineData → Effects} {checkAlign atomic : Bool}
    (hal : checkAlign = true → isAligned w.bytes addr = true)
    (hnone : Mem.loadInt s.dmem addr w.bytes = none)
    (hk : env.AvxLoad atomic addr w g (fun v g' => (ret v s).AllEnv env g' P)) :
    (s.loadAvx addr w ret checkAlign atomic).AllEnv env g P := by
  have hc : (checkAlign && !isAligned w.bytes addr) = false := by
    cases checkAlign <;> simp_all
  simp only [MachineData.loadAvx, hc, Bool.false_eq_true, ite_false, Effects.AllEnv, hnone]
  cases atomic with
  | true => exact hk
  | false => exact hk

/-- A vector store outside `dmem` (`MachineData.storeAvx`): the environment's
side (`SharedEnv.AvxStore`). -/
theorem MachineData.storeAvx_AllEnv {env : SharedEnv} {g : env.State}
    {P : MachineState → env.State → Prop} {s : MachineData} {addr : BitVec 64} {w : AvxWidth}
    {v : w.type} {ret : MachineData → Effects} {checkAlign atomic : Bool}
    (hal : checkAlign = true → isAligned w.bytes addr = true)
    (hnone : Mem.loadInt s.dmem addr w.bytes = none)
    (hk : env.AvxStore atomic addr v g (fun g' => (ret s).AllEnv env g' P)) :
    (s.storeAvx addr v ret checkAlign atomic).AllEnv env g P := by
  have hc : (checkAlign && !isAligned w.bytes addr) = false := by
    cases checkAlign <;> simp_all
  simp only [MachineData.storeAvx, hc, Bool.false_eq_true, ite_false, Effects.AllEnv, hnone]
  cases atomic with
  | true => exact hk
  | false => exact hk

namespace MachineWP

/-- Unfold the fall-through address past one instruction cell. -/
private theorem after_instr [CodeEnv] {i : Instr} {q : Program} {pc : Int64} {z : Nat}
    {rest : List (Directive × Nat)}
    (hcode : cenv.codeAt pc = (Directive.instr i, z) :: rest) :
    cenv.after pc (Directive.instr i :: q) = cenv.after (pc + .ofNat z) q := by
  simp only [Executable.after, hcode]

set_option hygiene false in
/-- One cell: place it, step it, and leave the `AllEnv` goal of its
fall-through tree, with the placement of the tail as `hpl'`. -/
local macro "env_step" : tactic =>
  `(tactic| (
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    refine step_cps _ _ _ ⟨_, z, rest, hseg, Or.inl ?_⟩))

/-! ## Moves of a general-purpose register -/

/-- `movq d(%b), %r` on a location outside `dmem`: a plain 8-byte load; the
tail runs from every value and environment state the environment allows. -/
theorem mov_load_shared [CodeEnv] (env : SharedEnv) (r b : Reg64) (d : Int64) {p : Program}
    {Q : MachineData → env.State → Prop} {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        Mem.loadInt s.dmem a 8 = none ∧ env.ok (.load .plain false a 8) g ∧
          ∀ v g', env.step (.load .plain false a 8) g v g' →
            cenv.wpEnv env p Q E { s with regs := s.regs.set64 r (v.setWidth 64) } g')
      (Directive.instr (.regular .W64 .W64
          (.mov (.reg (.low r .W64)) (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩)))) :: p)
      Q E := by
  intro s g ⟨hnone, hok, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.setReg, MachineData.load,
    AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64, Reg64s.set_low64, Width.bytes,
    hnone, Effects.AllEnv]
  exact ⟨hok, fun v g' hs => hk v g' hs _ hpl'⟩

/-- `movl d(%b), %r32` on a location outside `dmem`: a plain 4-byte load, the
value zero-extended in the register. -/
theorem mov32_load_shared [CodeEnv] (env : SharedEnv) (r b : Reg64) (d : Int64) {p : Program}
    {Q : MachineData → env.State → Prop} {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        Mem.loadInt s.dmem a 4 = none ∧ env.ok (.load .plain false a 4) g ∧
          ∀ v g', env.step (.load .plain false a 4) g v g' →
            cenv.wpEnv env p Q E { s with regs := s.regs.set64 r ((v.setWidth 32).setWidth 64) } g')
      (Directive.instr (.regular .W64 .W32
          (.mov (.reg (.low r .W32)) (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩)))) :: p)
      Q E := by
  intro s g ⟨hnone, hok, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.setReg, MachineData.load,
    AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64, Reg64s.set_low32, Width.bytes,
    hnone, Effects.AllEnv]
  exact ⟨hok, fun v g' hs => hk v g' hs _ hpl'⟩

/-- `movq %r, d(%b)` on a location outside `dmem` (`MovStoreSharedRule`). -/
theorem mov_store_shared : MovStoreSharedRule := by
  intro _ env b d r p Q E s g ⟨hnone, hok, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.store,
    AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64, Reg64s.get_low64, Width.bytes,
    hnone, Effects.AllEnv]
  exact ⟨hok, fun v g' hs => hk v g' hs _ hpl'⟩

/-- `movl %r32, d(%b)` on a location outside `dmem`: a plain 4-byte store of
the low half of the register. -/
theorem mov32_store_shared [CodeEnv] (env : SharedEnv) (b : Reg64) (d : Int64) (r : Reg64)
    {p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        let v := ((s.regs.get64 r).setWidth 32).setWidth 128
        Mem.loadInt s.dmem a 4 = none ∧ env.ok (.store .plain false a 4 v) g ∧
          ∀ ok g', env.step (.store .plain false a 4 v) g ok g' → cenv.wpEnv env p Q E s g')
      (Directive.instr (.regular .W64 .W32
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩) (.regOrMem (.reg (.low r .W32))))) :: p)
      Q E := by
  intro s g ⟨hnone, hok, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.store,
    AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64, Reg64s.get_low32, Width.bytes,
    hnone, Effects.AllEnv]
  exact ⟨hok, fun v g' hs => hk v g' hs _ hpl'⟩

/-! ## Other plain accesses (x64 parity)

The remaining shapes with a `MachineWP` mapped-memory rule that are one plain
access: byte moves, the sign-extending `movslq` load of a jump table, and the
memory compare. -/

/-- `movb d(%b), %r8` on a location outside `dmem`: a plain 1-byte load into
the register's low byte. -/
theorem mov8_load_shared [CodeEnv] (env : SharedEnv) (r b : Reg64) (d : Int64) {p : Program}
    {Q : MachineData → env.State → Prop} {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        Mem.loadInt s.dmem a 1 = none ∧ env.ok (.load .plain false a 1) g ∧
          ∀ v g', env.step (.load .plain false a 1) g v g' →
            cenv.wpEnv env p Q E
              { s with regs := s.regs.set64 r ((s.regs.get64 r).replaceLow (v.setWidth 8)) } g')
      (Directive.instr (.regular .W64 .W8
          (.mov (.reg (.low r .W8)) (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩)))) :: p)
      Q E := by
  intro s g ⟨hnone, hok, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.setReg, MachineData.load,
    AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64, Reg64s.set_low8, Width.bytes,
    hnone, Effects.AllEnv]
  exact ⟨hok, fun v g' hs => hk v g' hs _ hpl'⟩

/-- `movb $i, d(%b)` on a location outside `dmem`: a plain 1-byte store of the
immediate's low byte. -/
theorem mov8_store_imm_shared [CodeEnv] (env : SharedEnv) (b : Reg64) (d i : Int64) {p : Program}
    {Q : MachineData → env.State → Prop} {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        let v := (i.toBitVec.truncate 8).setWidth 128
        Mem.loadInt s.dmem a 1 = none ∧ env.ok (.store .plain false a 1 v) g ∧
          ∀ ok g', env.step (.store .plain false a 1 v) g ok g' → cenv.wpEnv env p Q E s g')
      (Directive.instr (.regular .W64 .W8
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩) (.imm (.int64 i)))) :: p)
      Q E := by
  intro s g ⟨hnone, hok, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    MachineData.set, MachineData.store,
    AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64, Width.bytes,
    hnone, Effects.AllEnv]
  exact ⟨hok, fun v g' hs => hk v g' hs _ hpl'⟩

/-- `movb %r8, d(%b)` on a location outside `dmem`: a plain 1-byte store of the
register's low byte. -/
theorem mov8_store_reg_shared [CodeEnv] (env : SharedEnv) (b : Reg64) (d : Int64) (r : Reg64)
    {p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        let v := ((s.regs.get64 r).setWidth 8).setWidth 128
        Mem.loadInt s.dmem a 1 = none ∧ env.ok (.store .plain false a 1 v) g ∧
          ∀ ok g', env.step (.store .plain false a 1 v) g ok g' → cenv.wpEnv env p Q E s g')
      (Directive.instr (.regular .W64 .W8
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩) (.regOrMem (.reg (.low r .W8))))) :: p)
      Q E := by
  intro s g ⟨hnone, hok, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.store,
    AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64, Reg64s.get_low8, Width.bytes,
    hnone, Effects.AllEnv]
  exact ⟨hok, fun v g' hs => hk v g' hs _ hpl'⟩

/-- `movslq (%b,%i,s), %r` (`movsxd`) on a location outside `dmem`: a plain
4-byte load, sign-extended in the register. -/
theorem movsxd_load_sib_shared [CodeEnv] (env : SharedEnv) (r b i : Reg64) (c : Width)
    {p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + s.regs.get64 i * BitVec.ofNat 64 c.bytes
        Mem.loadInt s.dmem a 4 = none ∧ env.ok (.load .plain false a 4) g ∧
          ∀ v g', env.step (.load .plain false a 4) g v g' →
            cenv.wpEnv env p Q E { s with regs := s.regs.set64 r ((v.setWidth 32).signExtend 64) } g')
      (Directive.instr (.regular .W64 .W64
          (.movsx (w' := .W32) (.reg (.low r .W64))
            (.mem ⟨some (.reg b), some ⟨i, c⟩, .int64 0⟩))) :: p)
      Q E := by
  intro s g ⟨hnone, hok, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, Operation.interp,
    RegOrMem.interp, MachineData.set, MachineData.setReg, MachineData.load,
    AddrExpr.zeroExtend_interp_sib_scale, Reg64s.set_low64, Width.bytes,
    hnone, Effects.AllEnv]
  exact ⟨hok, fun v g' hs => hk v g' hs _ hpl'⟩

/-- `cmpl $i, d(%b)` on a location outside `dmem`: a plain 4-byte load; the
flags are those of its 32-bit difference with the immediate. -/
theorem cmp32_mem_imm_shared [CodeEnv] (env : SharedEnv) (b : Reg64) (d i : Int64) {p : Program}
    {Q : MachineData → env.State → Prop} {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let addr := s.regs.get64 b + d.toBitVec
        Mem.loadInt s.dmem addr 4 = none ∧ env.ok (.load .plain false addr 4) g ∧
          ∀ m g', env.step (.load .plain false addr 4) g m g' →
            let a := m.setWidth 32
            let c := i.toBitVec.truncate 32
            let v := a - c
            cenv.wpEnv env p Q E { s with
              status := StatusFlags.from_result v
                { cf := v.unsigned != a.unsigned - c.unsigned,
                  af := (v.take 4).unsigned != (a.take 4).unsigned - (c.take 4).unsigned,
                  of := v.signed != a.signed - c.signed } } g')
      (Directive.instr (.regular .W64 .W32
          (.cmp (.mem ⟨some (.reg b), none, .int64 d⟩) (.imm (.int64 i)))) :: p)
      Q E := by
  intro s g ⟨hnone, hok, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load,
    AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64, Width.bytes,
    hnone, Effects.AllEnv]
  exact ⟨hok, fun v g' hs => hk v g' hs _ hpl'⟩

/-! ## Read-modify-writes -/

/-- `xchgq %r, d(%b)` on a location outside `dmem` (`XchgSharedRule`). -/
theorem xchg_shared : XchgSharedRule := by
  intro _ env r b d p Q E s g ⟨hnone, hok, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, Operation.interp,
    RegOrMem.rmw, MachineData.rmwK, MachineData.setReg,
    AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64, Reg64s.get_low64,
    Reg64s.set_low64, Width.bytes, hnone, Effects.AllEnv, ite_true]
  exact ⟨hok, fun v g' hs => hk v g' hs _ hpl'⟩

/-- `lock cmpxchgq %r, d(%b)` on a location outside `dmem`: one atomic `rmw`
that writes `r` if the old value equals `rax`. The flags are those of `cmp` of
`rax` with the old value; on a mismatch the old value lands in `rax`. -/
theorem lock_cmpxchg_shared [CodeEnv] (env : SharedEnv) (b : Reg64) (d : Int64) (r : Reg64)
    {p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        let acc := s.regs.get64 .rax
        let op := rmwOp128 .W64 (fun x => if x == acc then some (s.regs.get64 r) else none)
        Mem.loadInt s.dmem a 8 = none ∧ env.ok (.rmw .acqRel a 8 op) g ∧
          ∀ v g', env.step (.rmw .acqRel a 8 op) g v g' →
            let old := v.setWidth 64
            let dv := acc - old
            let status := StatusFlags.from_result dv
              { cf := dv.unsigned != acc.unsigned - old.unsigned,
                af := (dv.take 4).unsigned != (acc.take 4).unsigned - (old.take 4).unsigned,
                of := dv.signed != acc.signed - old.signed }
            (old = acc → cenv.wpEnv env p Q E { s with status } g')
            ∧ (old ≠ acc → cenv.wpEnv env p Q E { s with regs := s.regs.set64 .rax old, status } g'))
      (Directive.instr (.regular .W64 .W64
          (.cmpxchg true (.mem ⟨some (.reg b), none, .int64 d⟩) (.low r .W64))) :: p)
      Q E := by
  intro s g ⟨hnone, hok, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, Operation.interp,
    RegOrMem.rmw, MachineData.rmwK, MachineData.setReg,
    AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64, Reg64s.get_low64,
    Reg64s.set_low64, Width.bytes, hnone, Effects.AllEnv, ite_true]
  refine ⟨hok, fun v g' hs => ?_⟩
  obtain ⟨heq, hne⟩ := hk v g' hs
  by_cases h : v.setWidth 64 = s.regs.get64 .rax
  · have hb : (v.setWidth 64 == s.regs.get64 .rax) = true := by simpa using h
    simp only [hb, ite_true]
    exact heq h _ hpl'
  · have hb : (v.setWidth 64 == s.regs.get64 .rax) = false := by simpa using h
    simp only [hb, Bool.false_eq_true, ite_false]
    exact hne h _ hpl'

/-- `lock xaddq %r, d(%b)` on a location outside `dmem`: one atomic `rmw` that
adds `r`; the old value lands in `r`, the flags are those of the sum. -/
theorem lock_xadd_shared [CodeEnv] (env : SharedEnv) (b : Reg64) (d : Int64) (r : Reg64)
    {p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        let src := s.regs.get64 r
        let op := rmwOp128 .W64 (fun x => some (x + src))
        Mem.loadInt s.dmem a 8 = none ∧ env.ok (.rmw .acqRel a 8 op) g ∧
          ∀ v g', env.step (.rmw .acqRel a 8 op) g v g' →
            let old := v.setWidth 64
            cenv.wpEnv env p Q E { s with
              regs := s.regs.set64 r old,
              status := LockBinOp.add.status old src (old + src) false } g')
      (Directive.instr (.regular .W64 .W64
          (.xadd true (.mem ⟨some (.reg b), none, .int64 d⟩) (.low r .W64))) :: p)
      Q E := by
  intro s g ⟨hnone, hok, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, Operation.interp,
    RegOrMem.rmw, MachineData.rmwK, MachineData.setReg,
    AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64, Reg64s.get_low64,
    Reg64s.set_low64, Width.bytes, hnone, Effects.AllEnv, ite_true]
  exact ⟨hok, fun v g' hs => hk v g' hs _ hpl'⟩

/-- `lock op $i, d(%b)` for `op` among `add sub and or xor`, on a location
outside `dmem`: one atomic `rmw`; the tail runs with the result's flags, for
either value of the `AF` the logic operations leave undefined. -/
theorem lock_bin_imm_shared [CodeEnv] (env : SharedEnv) (op : LockBinOp) (b : Reg64) (d i : Int64)
    {p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        let src := BitVec.setWidth 64 i.toBitVec
        let f := rmwOp128 .W64 (fun x => some (op.eval x src))
        Mem.loadInt s.dmem a 8 = none ∧ env.ok (.rmw .acqRel a 8 f) g ∧
          ∀ v g', env.step (.rmw .acqRel a 8 f) g v g' → ∀ af : Bool,
            let old := v.setWidth 64
            cenv.wpEnv env p Q E { s with status := op.status old src (op.eval old src) af } g')
      (Directive.instr (.regular .W64 .W64
          (.lockBin op ⟨some (.reg b), none, .int64 d⟩ (.imm (.int64 i)))) :: p)
      Q E := by
  intro s g ⟨hnone, hok, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    MachineData.rmwK, AddrExpr.zeroExtend_interp_base_disp,
    BitVec.ofInt_toInt_int64, Width.bytes, hnone, Effects.AllEnv]
  exact ⟨hok, fun v g' hs af => hk v g' hs af _ hpl'⟩

/-- `lock op %r, d(%b)` for `op` among `add sub and or xor`, as with an
immediate. -/
theorem lock_bin_reg_shared [CodeEnv] (env : SharedEnv) (op : LockBinOp) (b : Reg64) (d : Int64)
    (r : Reg64) {p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        let src := s.regs.get64 r
        let f := rmwOp128 .W64 (fun x => some (op.eval x src))
        Mem.loadInt s.dmem a 8 = none ∧ env.ok (.rmw .acqRel a 8 f) g ∧
          ∀ v g', env.step (.rmw .acqRel a 8 f) g v g' → ∀ af : Bool,
            let old := v.setWidth 64
            cenv.wpEnv env p Q E { s with status := op.status old src (op.eval old src) af } g')
      (Directive.instr (.regular .W64 .W64
          (.lockBin op ⟨some (.reg b), none, .int64 d⟩ (.regOrMem (.reg (.low r .W64))))) :: p)
      Q E := by
  intro s g ⟨hnone, hok, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.rmwK, AddrExpr.zeroExtend_interp_base_disp,
    BitVec.ofInt_toInt_int64, Reg64s.get_low64, Width.bytes, hnone, Effects.AllEnv]
  exact ⟨hok, fun v g' hs af => hk v g' hs af _ hpl'⟩

/-- `lock op d(%b)` for `op` among `inc dec neg not`, on a location outside
`dmem`: one atomic `rmw`; the tail runs with the result's flags (`not` keeps
them). -/
theorem lock_un_shared [CodeEnv] (env : SharedEnv) (op : LockUnOp) (b : Reg64) (d : Int64)
    {p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        let f := rmwOp128 .W64 (fun x => some (op.eval x))
        Mem.loadInt s.dmem a 8 = none ∧ env.ok (.rmw .acqRel a 8 f) g ∧
          ∀ v g', env.step (.rmw .acqRel a 8 f) g v g' →
            let old := v.setWidth 64
            cenv.wpEnv env p Q E { s with status := op.status old (op.eval old) s.status } g')
      (Directive.instr (.regular .W64 .W64 (.lockUn op ⟨some (.reg b), none, .int64 d⟩)) :: p)
      Q E := by
  intro s g ⟨hnone, hok, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, Operation.interp,
    MachineData.rmwK, AddrExpr.zeroExtend_interp_base_disp,
    BitVec.ofInt_toInt_int64, Width.bytes, hnone, Effects.AllEnv]
  exact ⟨hok, fun v g' hs => hk v g' hs _ hpl'⟩

/-! ## Barriers -/

/-- `mfence`: a full fence, permitted by the environment; the tail runs in
every state it leaves (an environment with views raises them here). -/
theorem mfence_shared [CodeEnv] (env : SharedEnv) (asz osz : Width) {p : Program}
    {Q : MachineData → env.State → Prop} {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g => env.ok (.fence .sy) g ∧ ∀ g', env.step (.fence .sy) g () g' → cenv.wpEnv env p Q E s g')
      (Directive.instr (.regular asz osz .mfence) :: p) Q E := by
  intro s g ⟨hok, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, Operation.interp, Effects.AllEnv]
  exact ⟨hok, fun g' hs => hk g' hs _ hpl'⟩

/-- `lfence`: a `.ld` fence (no order on write-back memory under TSO). -/
theorem lfence_shared [CodeEnv] (env : SharedEnv) (asz osz : Width) {p : Program}
    {Q : MachineData → env.State → Prop} {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g => env.ok (.fence .ld) g ∧ ∀ g', env.step (.fence .ld) g () g' → cenv.wpEnv env p Q E s g')
      (Directive.instr (.regular asz osz .lfence) :: p) Q E := by
  intro s g ⟨hok, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, Operation.interp, Effects.AllEnv]
  exact ⟨hok, fun g' hs => hk g' hs _ hpl'⟩

/-- `sfence`: a `.st` fence (no order on write-back memory under TSO). -/
theorem sfence_shared [CodeEnv] (env : SharedEnv) (asz osz : Width) {p : Program}
    {Q : MachineData → env.State → Prop} {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g => env.ok (.fence .st) g ∧ ∀ g', env.step (.fence .st) g () g' → cenv.wpEnv env p Q E s g')
      (Directive.instr (.regular asz osz .sfence) :: p) Q E := by
  intro s g ⟨hok, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, Operation.interp, Effects.AllEnv]
  exact ⟨hok, fun g' hs => hk g' hs _ hpl'⟩

/-! ## Vector moves and `cmpxchg16b`

The aligned 16-byte moves (`movdqa`, `movapd`) are one atomic 16-byte access;
the unaligned ones (`movdqu`, `movups`) are two plain 8-byte pieces in
address order, each permitted and answered by the environment
(`SharedEnv.LoadPieces`, `SharedEnv.StorePieces`), and reassembled
little-endian (`ofPieces`, `toPieces`). The legacy forms keep the register's
bits above 128. -/

private theorem w128_beq : (AvxWidth.W128 == AvxWidth.W128) = true := rfl

/-- `movdqa d(%b), %xmm` on a location outside `dmem`: the address must be
16-byte aligned; one atomic 16-byte load. -/
theorem movdqa_load_shared [CodeEnv] (env : SharedEnv) (x : RegMm) (b : Reg64) (d : Int64)
    {p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        isAligned 16 a = true ∧ Mem.loadInt s.dmem a 16 = none ∧ env.ok (.load .plain false a 16) g ∧
          ∀ v g', env.step (.load .plain false a 16) g v g' →
            cenv.wpEnv env p Q E { s with zmms := s.zmms.setLegacy (.xmm x) v } g')
      (Directive.instr (.avx .W64 .W128
          (.movdqa (.avx (.xmm x)) (.mem ⟨some (.reg b), none, .int64 d⟩))) :: p)
      Q E := by
  intro s g ⟨hal, hnone, hok, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, AvxOperation.interp, AvxRegOrMem.interp,
    MachineData.loadAvx, MachineData.setAvxLegacy, MachineData.setAvxLegacyReg,
    AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64, AvxWidth.bytes, AvxWidth.bits,
    hal, hnone, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false, w128_beq,
    Effects.AllEnv]
  simp only [BitVec.setWidth_eq]
  exact ⟨hok, fun v g' hs => hk v g' hs _ hpl'⟩

/-- `movdqa %xmm, d(%b)` on a location outside `dmem`: the address must be
16-byte aligned; one atomic 16-byte store. -/
theorem movdqa_store_shared [CodeEnv] (env : SharedEnv) (x : RegMm) (b : Reg64) (d : Int64)
    {p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        let v := s.zmms.get (.xmm x)
        isAligned 16 a = true ∧ Mem.loadInt s.dmem a 16 = none ∧
          env.ok (.store .plain false a 16 v) g ∧
          ∀ ok g', env.step (.store .plain false a 16 v) g ok g' → cenv.wpEnv env p Q E s g')
      (Directive.instr (.avx .W64 .W128
          (.movdqa (.mem ⟨some (.reg b), none, .int64 d⟩) (.avx (.xmm x)))) :: p)
      Q E := by
  intro s g ⟨hal, hnone, hok, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, AvxOperation.interp, AvxRegOrMem.interp,
    MachineData.storeAvx, MachineData.setAvxLegacy,
    AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64, AvxWidth.bytes, AvxWidth.bits,
    hal, hnone, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false, w128_beq,
    Effects.AllEnv]
  simp only [BitVec.setWidth_eq]
  exact ⟨hok, fun v g' hs => hk v g' hs _ hpl'⟩

/-- `movapd d(%b), %xmm`, as `movdqa_load_shared`. -/
theorem movapd_load_shared [CodeEnv] (env : SharedEnv) (x : RegMm) (b : Reg64) (d : Int64)
    {p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        isAligned 16 a = true ∧ Mem.loadInt s.dmem a 16 = none ∧ env.ok (.load .plain false a 16) g ∧
          ∀ v g', env.step (.load .plain false a 16) g v g' →
            cenv.wpEnv env p Q E { s with zmms := s.zmms.setLegacy (.xmm x) v } g')
      (Directive.instr (.avx .W64 .W128
          (.movapd (.avx (.xmm x)) (.mem ⟨some (.reg b), none, .int64 d⟩))) :: p)
      Q E := by
  intro s g ⟨hal, hnone, hok, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, AvxOperation.interp, AvxRegOrMem.interp,
    MachineData.loadAvx, MachineData.setAvxLegacy, MachineData.setAvxLegacyReg,
    AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64, AvxWidth.bytes, AvxWidth.bits,
    hal, hnone, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false, w128_beq,
    Effects.AllEnv]
  simp only [BitVec.setWidth_eq]
  exact ⟨hok, fun v g' hs => hk v g' hs _ hpl'⟩

/-- `movapd %xmm, d(%b)`, as `movdqa_store_shared`. -/
theorem movapd_store_shared [CodeEnv] (env : SharedEnv) (x : RegMm) (b : Reg64) (d : Int64)
    {p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        let v := s.zmms.get (.xmm x)
        isAligned 16 a = true ∧ Mem.loadInt s.dmem a 16 = none ∧
          env.ok (.store .plain false a 16 v) g ∧
          ∀ ok g', env.step (.store .plain false a 16 v) g ok g' → cenv.wpEnv env p Q E s g')
      (Directive.instr (.avx .W64 .W128
          (.movapd (.mem ⟨some (.reg b), none, .int64 d⟩) (.avx (.xmm x)))) :: p)
      Q E := by
  intro s g ⟨hal, hnone, hok, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, AvxOperation.interp, AvxRegOrMem.interp,
    MachineData.storeAvx, MachineData.setAvxLegacy,
    AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64, AvxWidth.bytes, AvxWidth.bits,
    hal, hnone, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false, w128_beq,
    Effects.AllEnv]
  simp only [BitVec.setWidth_eq]
  exact ⟨hok, fun v g' hs => hk v g' hs _ hpl'⟩

/-- `movaps d(%b), %xmm`, as `movdqa_load_shared`. -/
theorem movaps_load_shared [CodeEnv] (env : SharedEnv) (x : RegMm) (b : Reg64) (d : Int64)
    {p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        isAligned 16 a = true ∧ Mem.loadInt s.dmem a 16 = none ∧ env.ok (.load .plain false a 16) g ∧
          ∀ v g', env.step (.load .plain false a 16) g v g' →
            cenv.wpEnv env p Q E { s with zmms := s.zmms.setLegacy (.xmm x) v } g')
      (Directive.instr (.avx .W64 .W128
          (.movaps (.avx (.xmm x)) (.mem ⟨some (.reg b), none, .int64 d⟩))) :: p)
      Q E := by
  intro s g ⟨hal, hnone, hok, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, AvxOperation.interp, AvxRegOrMem.interp,
    MachineData.loadAvx, MachineData.setAvxLegacy, MachineData.setAvxLegacyReg,
    AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64, AvxWidth.bytes, AvxWidth.bits,
    hal, hnone, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false, w128_beq,
    Effects.AllEnv]
  simp only [BitVec.setWidth_eq]
  exact ⟨hok, fun v g' hs => hk v g' hs _ hpl'⟩

/-- `movaps %xmm, d(%b)`, as `movdqa_store_shared`. -/
theorem movaps_store_shared [CodeEnv] (env : SharedEnv) (x : RegMm) (b : Reg64) (d : Int64)
    {p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        let v := s.zmms.get (.xmm x)
        isAligned 16 a = true ∧ Mem.loadInt s.dmem a 16 = none ∧
          env.ok (.store .plain false a 16 v) g ∧
          ∀ ok g', env.step (.store .plain false a 16 v) g ok g' → cenv.wpEnv env p Q E s g')
      (Directive.instr (.avx .W64 .W128
          (.movaps (.mem ⟨some (.reg b), none, .int64 d⟩) (.avx (.xmm x)))) :: p)
      Q E := by
  intro s g ⟨hal, hnone, hok, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, AvxOperation.interp, AvxRegOrMem.interp,
    MachineData.storeAvx, MachineData.setAvxLegacy,
    AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64, AvxWidth.bytes, AvxWidth.bits,
    hal, hnone, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false, w128_beq,
    Effects.AllEnv]
  simp only [BitVec.setWidth_eq]
  exact ⟨hok, fun v g' hs => hk v g' hs _ hpl'⟩

/-- `movdqu d(%b), %xmm` on a location outside `dmem`, at any alignment: two
plain 8-byte pieces in address order; the tail runs from every pair of values
the environment allows, reassembled little-endian. -/
theorem movdqu_load_shared [CodeEnv] (env : SharedEnv) (x : RegMm) (b : Reg64) (d : Int64)
    {p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        Mem.loadInt s.dmem a 16 = none ∧
          env.LoadPieces a 2 g (fun vs g' =>
            cenv.wpEnv env p Q E { s with zmms := s.zmms.setLegacy (.xmm x) (ofPieces 128 vs) } g'))
      (Directive.instr (.avx .W64 .W128
          (.movdqu (.avx (.xmm x)) (.mem ⟨some (.reg b), none, .int64 d⟩))) :: p)
      Q E := by
  intro s g ⟨hnone, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, AvxOperation.interp, AvxRegOrMem.interp,
    MachineData.loadAvx, MachineData.setAvxLegacy, MachineData.setAvxLegacyReg,
    AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64, AvxWidth.bytes, AvxWidth.bits,
    hnone, Bool.false_and, Bool.false_eq_true, ite_false, Effects.AllEnv]
  exact SharedEnv.LoadPieces.mono (fun vs g' h => h _ hpl') hk

/-- `movdqu %xmm, d(%b)` on a location outside `dmem`, at any alignment: two
plain 8-byte stores of the register's halves, low half first. -/
theorem movdqu_store_shared [CodeEnv] (env : SharedEnv) (x : RegMm) (b : Reg64) (d : Int64)
    {p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        Mem.loadInt s.dmem a 16 = none ∧
          env.StorePieces a (toPieces (s.zmms.get (.xmm x)) 2) g (fun g' => cenv.wpEnv env p Q E s g'))
      (Directive.instr (.avx .W64 .W128
          (.movdqu (.mem ⟨some (.reg b), none, .int64 d⟩) (.avx (.xmm x)))) :: p)
      Q E := by
  intro s g ⟨hnone, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, AvxOperation.interp, AvxRegOrMem.interp,
    MachineData.storeAvx, MachineData.setAvxLegacy,
    AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64, AvxWidth.bytes,
    hnone, Bool.false_and, Bool.false_eq_true, ite_false, Effects.AllEnv]
  exact SharedEnv.StorePieces.mono (fun g' h => h _ hpl') hk

/-- `movups d(%b), %xmm`, as `movdqu_load_shared`. -/
theorem movups_load_shared [CodeEnv] (env : SharedEnv) (x : RegMm) (b : Reg64) (d : Int64)
    {p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        Mem.loadInt s.dmem a 16 = none ∧
          env.LoadPieces a 2 g (fun vs g' =>
            cenv.wpEnv env p Q E { s with zmms := s.zmms.setLegacy (.xmm x) (ofPieces 128 vs) } g'))
      (Directive.instr (.avx .W64 .W128
          (.movups (.avx (.xmm x)) (.mem ⟨some (.reg b), none, .int64 d⟩))) :: p)
      Q E := by
  intro s g ⟨hnone, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, AvxOperation.interp, AvxRegOrMem.interp,
    MachineData.loadAvx, MachineData.setAvxLegacy, MachineData.setAvxLegacyReg,
    AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64, AvxWidth.bytes, AvxWidth.bits,
    hnone, Bool.false_and, Bool.false_eq_true, ite_false, Effects.AllEnv]
  exact SharedEnv.LoadPieces.mono (fun vs g' h => h _ hpl') hk

/-- `movups %xmm, d(%b)`, as `movdqu_store_shared`. -/
theorem movups_store_shared [CodeEnv] (env : SharedEnv) (x : RegMm) (b : Reg64) (d : Int64)
    {p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        Mem.loadInt s.dmem a 16 = none ∧
          env.StorePieces a (toPieces (s.zmms.get (.xmm x)) 2) g (fun g' => cenv.wpEnv env p Q E s g'))
      (Directive.instr (.avx .W64 .W128
          (.movups (.mem ⟨some (.reg b), none, .int64 d⟩) (.avx (.xmm x)))) :: p)
      Q E := by
  intro s g ⟨hnone, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, AvxOperation.interp, AvxRegOrMem.interp,
    MachineData.storeAvx, MachineData.setAvxLegacy,
    AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64, AvxWidth.bytes,
    hnone, Bool.false_and, Bool.false_eq_true, ite_false, Effects.AllEnv]
  exact SharedEnv.StorePieces.mono (fun g' h => h _ hpl') hk

/-- `lock cmpxchg16b d(%b)` on a location outside `dmem`: the address must be
16-byte aligned; one atomic 16-byte `rmw` that writes `rcx:rbx` if the old
value equals `rdx:rax`. ZF records the match; on a mismatch the old value lands
in `rdx:rax`. -/
theorem lock_cmpxchg16b_shared [CodeEnv] (env : SharedEnv) (b : Reg64) (d : Int64)
    {p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        let acc := s.regs.get64 .rdx ++ s.regs.get64 .rax
        let op := fun old : BitVec 128 =>
          if old == acc then some (s.regs.get64 .rcx ++ s.regs.get64 .rbx) else none
        isAligned 16 a = true ∧ Mem.loadInt s.dmem a 16 = none ∧ env.ok (.rmw .acqRel a 16 op) g ∧
          ∀ old g', env.step (.rmw .acqRel a 16 op) g old g' →
            (old = acc → cenv.wpEnv env p Q E { s with status := { s.status with zf := true } } g')
            ∧ (old ≠ acc → cenv.wpEnv env p Q E
                { s with
                    regs := (s.regs.set64 .rax (old.extractLsb' 0 64)).set64 .rdx (old.extractLsb' 64 64),
                    status := { s.status with zf := false } } g'))
      (Directive.instr (.avx .W64 .W128 (.cmpxchg16b true ⟨some (.reg b), none, .int64 d⟩)) :: p)
      Q E := by
  intro s g ⟨hal, hnone, hok, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, AvxOperation.interp, MachineData.rmw16K,
    AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64, hal, hnone, ite_true,
    Effects.AllEnv]
  refine ⟨hok, fun old g' hs => ?_⟩
  obtain ⟨heq, hne⟩ := hk old g' hs
  by_cases h : old = s.regs.get64 .rdx ++ s.regs.get64 .rax
  · have hb : (old == s.regs.get64 .rdx ++ s.regs.get64 .rax) = true := by simpa using h
    simp only [hb, ite_true]
    exact heq h _ hpl'
  · have hb : (old == s.regs.get64 .rdx ++ s.regs.get64 .rax) = false := by simpa using h
    simp only [hb, Bool.false_eq_true, ite_false]
    exact hne h _ hpl'

/-! ## VEX moves and the SIB and memory-source forms

The VEX moves of any `AvxWidth` (`vmovdqa`, `vmovapd`, `vmovdqu` at `d(%b)`;
`vmovaps`/`vmovups` at `d(%b,%i,1)`): a register destination is written whole,
the bits above the operation width cleared (`ZMMs.set`). Atomicity follows
the semantics: the aligned moves at 16 bytes are one access, every
other vector access is 8-byte pieces in address order (`SharedEnv.AvxLoad`,
`SharedEnv.AvxStore`, which reduce at a width literal by `AvxLoad_true`,
`AvxLoad_false`, …). The `movaps` SIB forms are the `d(%b)` rules at the SIB
address. The packed arithmetic with a memory source (`mulps`, `xorps`,
`vmulps`, `vfmadd231ps`) is its load (`mulps`/`xorps` check 16-byte alignment
but are not atomic: two pieces) followed by the register rule. -/

/-- `vmovdqa d(%b), %xmm/%ymm/%zmm` on a location outside `dmem`: the address must be
aligned to the width; one atomic access at 16 bytes, 8-byte pieces wider; the
register written whole. -/
theorem vmovdqa_load_shared [CodeEnv] (env : SharedEnv) {w : AvxWidth} (x : AvxReg w) (b : Reg64)
    (d : Int64)
    {p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        isAligned w.bytes a = true ∧ Mem.loadInt s.dmem a w.bytes = none ∧
          env.AvxLoad (w == .W128) a w g (fun v g' =>
            cenv.wpEnv env p Q E { s with zmms := s.zmms.set x v } g'))
      (Directive.instr (.avx .W64 w
          (.vmovdqa (.avx x) (.mem ⟨some (.reg b), none, .int64 d⟩))) :: p)
      Q E := by
  intro s g ⟨hal, hnone, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, AvxOperation.interp, AvxRegOrMem.interp,
    MachineData.setAvx, MachineData.setAvxReg, AddrExpr.zeroExtend_interp_base_disp,
    BitVec.ofInt_toInt_int64]
  exact MachineData.loadAvx_AllEnv (fun _ => hal) hnone (SharedEnv.AvxLoad.mono
    (fun _ _ h => h _ hpl') hk)

/-- `vmovapd d(%b), %xmm/%ymm/%zmm`, as `vmovdqa_load_shared`. -/
theorem vmovapd_load_shared [CodeEnv] (env : SharedEnv) {w : AvxWidth} (x : AvxReg w) (b : Reg64)
    (d : Int64)
    {p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        isAligned w.bytes a = true ∧ Mem.loadInt s.dmem a w.bytes = none ∧
          env.AvxLoad (w == .W128) a w g (fun v g' =>
            cenv.wpEnv env p Q E { s with zmms := s.zmms.set x v } g'))
      (Directive.instr (.avx .W64 w
          (.vmovapd (.avx x) (.mem ⟨some (.reg b), none, .int64 d⟩))) :: p)
      Q E := by
  intro s g ⟨hal, hnone, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, AvxOperation.interp, AvxRegOrMem.interp,
    MachineData.setAvx, MachineData.setAvxReg, AddrExpr.zeroExtend_interp_base_disp,
    BitVec.ofInt_toInt_int64]
  exact MachineData.loadAvx_AllEnv (fun _ => hal) hnone (SharedEnv.AvxLoad.mono
    (fun _ _ h => h _ hpl') hk)

/-- `vmovdqu d(%b), %xmm/%ymm/%zmm` on a location outside `dmem`, at any alignment:
8-byte pieces; the register written whole. -/
theorem vmovdqu_load_shared [CodeEnv] (env : SharedEnv) {w : AvxWidth} (x : AvxReg w) (b : Reg64)
    (d : Int64)
    {p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        Mem.loadInt s.dmem a w.bytes = none ∧
          env.AvxLoad false a w g (fun v g' =>
            cenv.wpEnv env p Q E { s with zmms := s.zmms.set x v } g'))
      (Directive.instr (.avx .W64 w
          (.vmovdqu (.avx x) (.mem ⟨some (.reg b), none, .int64 d⟩))) :: p)
      Q E := by
  intro s g ⟨hnone, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, AvxOperation.interp, AvxRegOrMem.interp,
    MachineData.setAvx, MachineData.setAvxReg, AddrExpr.zeroExtend_interp_base_disp,
    BitVec.ofInt_toInt_int64]
  exact MachineData.loadAvx_AllEnv (fun h => nomatch h) hnone (SharedEnv.AvxLoad.mono
    (fun _ _ h => h _ hpl') hk)

/-- `vmovdqa %xmm/%ymm/%zmm, d(%b)` on a location outside `dmem`: the address must be
aligned to the width; one atomic access at 16 bytes, 8-byte pieces wider. -/
theorem vmovdqa_store_shared [CodeEnv] (env : SharedEnv) {w : AvxWidth} (x : AvxReg w) (b : Reg64)
    (d : Int64)
    {p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        isAligned w.bytes a = true ∧ Mem.loadInt s.dmem a w.bytes = none ∧
          env.AvxStore (w == .W128) a (s.zmms.get x) g (fun g' => cenv.wpEnv env p Q E s g'))
      (Directive.instr (.avx .W64 w
          (.vmovdqa (.mem ⟨some (.reg b), none, .int64 d⟩) (.avx x))) :: p)
      Q E := by
  intro s g ⟨hal, hnone, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, AvxOperation.interp, AvxRegOrMem.interp,
    MachineData.setAvx, AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64]
  exact MachineData.storeAvx_AllEnv (fun _ => hal) hnone (SharedEnv.AvxStore.mono
    (fun _ h => h _ hpl') hk)

/-- `vmovapd %xmm/%ymm/%zmm, d(%b)`, as `vmovdqa_store_shared`. -/
theorem vmovapd_store_shared [CodeEnv] (env : SharedEnv) {w : AvxWidth} (x : AvxReg w) (b : Reg64)
    (d : Int64)
    {p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        isAligned w.bytes a = true ∧ Mem.loadInt s.dmem a w.bytes = none ∧
          env.AvxStore (w == .W128) a (s.zmms.get x) g (fun g' => cenv.wpEnv env p Q E s g'))
      (Directive.instr (.avx .W64 w
          (.vmovapd (.mem ⟨some (.reg b), none, .int64 d⟩) (.avx x))) :: p)
      Q E := by
  intro s g ⟨hal, hnone, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, AvxOperation.interp, AvxRegOrMem.interp,
    MachineData.setAvx, AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64]
  exact MachineData.storeAvx_AllEnv (fun _ => hal) hnone (SharedEnv.AvxStore.mono
    (fun _ h => h _ hpl') hk)

/-- `vmovdqu %xmm/%ymm/%zmm, d(%b)` on a location outside `dmem`, at any alignment:
8-byte pieces. -/
theorem vmovdqu_store_shared [CodeEnv] (env : SharedEnv) {w : AvxWidth} (x : AvxReg w) (b : Reg64)
    (d : Int64)
    {p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        Mem.loadInt s.dmem a w.bytes = none ∧
          env.AvxStore false a (s.zmms.get x) g (fun g' => cenv.wpEnv env p Q E s g'))
      (Directive.instr (.avx .W64 w
          (.vmovdqu (.mem ⟨some (.reg b), none, .int64 d⟩) (.avx x))) :: p)
      Q E := by
  intro s g ⟨hnone, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, AvxOperation.interp, AvxRegOrMem.interp,
    MachineData.setAvx, AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64]
  exact MachineData.storeAvx_AllEnv (fun h => nomatch h) hnone (SharedEnv.AvxStore.mono
    (fun _ h => h _ hpl') hk)

/-- `movaps (%b,%i,1), %xmm` on a location outside `dmem`, as
`movaps_load_shared` at the SIB address. -/
theorem movaps_load_sib1_shared [CodeEnv] (env : SharedEnv) (x : RegMm) (b i : Reg64)
    {p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + s.regs.get64 i
        isAligned 16 a = true ∧ Mem.loadInt s.dmem a 16 = none ∧ env.ok (.load .plain false a 16) g ∧
          ∀ v g', env.step (.load .plain false a 16) g v g' →
            cenv.wpEnv env p Q E { s with zmms := s.zmms.setLegacy (.xmm x) v } g')
      (Directive.instr (.avx .W64 .W128
          (.movaps (.avx (.xmm x)) (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 0⟩))) :: p)
      Q E := by
  intro s g ⟨hal, hnone, hok, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, AvxOperation.interp, AvxRegOrMem.interp,
    MachineData.setAvxLegacy, MachineData.setAvxLegacyReg,
    AddrExpr.zeroExtend_interp_sib1]
  refine MachineData.loadAvx_AllEnv (fun _ => hal) hnone ?_
  simp only [w128_beq, SharedEnv.AvxLoad_true, AvxWidth.bytes, AvxWidth.bits, BitVec.setWidth_eq]
  exact ⟨hok, fun v g' hs => hk v g' hs _ hpl'⟩

/-- `movaps %xmm, (%b,%i,1)` on a location outside `dmem`, as
`movaps_store_shared` at the SIB address. -/
theorem movaps_store_sib1_shared [CodeEnv] (env : SharedEnv) (x : RegMm) (b i : Reg64)
    {p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + s.regs.get64 i
        let v := s.zmms.get (.xmm x)
        isAligned 16 a = true ∧ Mem.loadInt s.dmem a 16 = none ∧
          env.ok (.store .plain false a 16 v) g ∧
          ∀ ok g', env.step (.store .plain false a 16 v) g ok g' → cenv.wpEnv env p Q E s g')
      (Directive.instr (.avx .W64 .W128
          (.movaps (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 0⟩) (.avx (.xmm x)))) :: p)
      Q E := by
  intro s g ⟨hal, hnone, hok, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, AvxOperation.interp, AvxRegOrMem.interp,
    MachineData.setAvxLegacy, AddrExpr.zeroExtend_interp_sib1]
  refine MachineData.storeAvx_AllEnv (fun _ => hal) hnone ?_
  simp only [w128_beq, SharedEnv.AvxStore_true, AvxWidth.bytes, AvxWidth.bits, BitVec.setWidth_eq]
  exact ⟨hok, fun v g' hs => hk v g' hs _ hpl'⟩

/-- `movaps d(%b,%i,1), %xmm` on a location outside `dmem`, as
`movaps_load_shared` at the SIB address. -/
theorem movaps_load_sib1_disp_shared [CodeEnv] (env : SharedEnv) (x : RegMm) (b i : Reg64)
    (d : Int64)
    {p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + s.regs.get64 i + d.toBitVec
        isAligned 16 a = true ∧ Mem.loadInt s.dmem a 16 = none ∧ env.ok (.load .plain false a 16) g ∧
          ∀ v g', env.step (.load .plain false a 16) g v g' →
            cenv.wpEnv env p Q E { s with zmms := s.zmms.setLegacy (.xmm x) v } g')
      (Directive.instr (.avx .W64 .W128
          (.movaps (.avx (.xmm x)) (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩))) :: p)
      Q E := by
  intro s g ⟨hal, hnone, hok, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, AvxOperation.interp, AvxRegOrMem.interp,
    MachineData.setAvxLegacy, MachineData.setAvxLegacyReg,
    AddrExpr.zeroExtend_interp_sib1_disp]
  refine MachineData.loadAvx_AllEnv (fun _ => hal) hnone ?_
  simp only [w128_beq, SharedEnv.AvxLoad_true, AvxWidth.bytes, AvxWidth.bits, BitVec.setWidth_eq]
  exact ⟨hok, fun v g' hs => hk v g' hs _ hpl'⟩

/-- `movaps %xmm, d(%b,%i,1)` on a location outside `dmem`, as
`movaps_store_shared` at the SIB address. -/
theorem movaps_store_sib1_disp_shared [CodeEnv] (env : SharedEnv) (x : RegMm) (b i : Reg64)
    (d : Int64)
    {p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + s.regs.get64 i + d.toBitVec
        let v := s.zmms.get (.xmm x)
        isAligned 16 a = true ∧ Mem.loadInt s.dmem a 16 = none ∧
          env.ok (.store .plain false a 16 v) g ∧
          ∀ ok g', env.step (.store .plain false a 16 v) g ok g' → cenv.wpEnv env p Q E s g')
      (Directive.instr (.avx .W64 .W128
          (.movaps (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩) (.avx (.xmm x)))) :: p)
      Q E := by
  intro s g ⟨hal, hnone, hok, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, AvxOperation.interp, AvxRegOrMem.interp,
    MachineData.setAvxLegacy, AddrExpr.zeroExtend_interp_sib1_disp]
  refine MachineData.storeAvx_AllEnv (fun _ => hal) hnone ?_
  simp only [w128_beq, SharedEnv.AvxStore_true, AvxWidth.bytes, AvxWidth.bits, BitVec.setWidth_eq]
  exact ⟨hok, fun v g' hs => hk v g' hs _ hpl'⟩

/-- `vmovaps d(%b,%i,1), %xmm` on a location outside `dmem`: the address must be
16-byte aligned; one atomic 16-byte load, the register written whole. -/
theorem vmovaps_load_sib1_disp_shared [CodeEnv] (env : SharedEnv) (x : AvxReg .W128) (b i : Reg64)
    (d : Int64)
    {p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + s.regs.get64 i + d.toBitVec
        isAligned 16 a = true ∧ Mem.loadInt s.dmem a 16 = none ∧ env.ok (.load .plain false a 16) g ∧
          ∀ v g', env.step (.load .plain false a 16) g v g' →
            cenv.wpEnv env p Q E { s with zmms := s.zmms.set x v } g')
      (Directive.instr (.avx .W64 .W128
          (.vmovaps (.avx x) (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩))) :: p)
      Q E := by
  intro s g ⟨hal, hnone, hok, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, AvxOperation.interp, AvxRegOrMem.interp,
    MachineData.setAvx, MachineData.setAvxReg, AddrExpr.zeroExtend_interp_sib1_disp]
  refine MachineData.loadAvx_AllEnv (fun _ => hal) hnone ?_
  simp only [w128_beq, SharedEnv.AvxLoad_true, AvxWidth.bytes, AvxWidth.bits, BitVec.setWidth_eq]
  exact ⟨hok, fun v g' hs => hk v g' hs _ hpl'⟩

/-- `vmovups d(%b,%i,1), %ymm` on a location outside `dmem`, at any alignment:
four 8-byte pieces; the register written whole. -/
theorem vmovups_load_sib1_disp_shared [CodeEnv] (env : SharedEnv) (y : AvxReg .W256) (b i : Reg64)
    (d : Int64)
    {p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + s.regs.get64 i + d.toBitVec
        Mem.loadInt s.dmem a 32 = none ∧
          env.LoadPieces a 4 g (fun vs g' =>
            let m := ofPieces 256 vs
            cenv.wpEnv env p Q E { s with zmms := s.zmms.set y m } g'))
      (Directive.instr (.avx .W64 .W256
          (.vmovups (.avx y) (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩))) :: p)
      Q E := by
  intro s g ⟨hnone, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, AvxOperation.interp, AvxRegOrMem.interp,
    MachineData.setAvx, MachineData.setAvxReg, AddrExpr.zeroExtend_interp_sib1_disp]
  exact MachineData.loadAvx_AllEnv (fun h => nomatch h) hnone (SharedEnv.LoadPieces.mono
    (fun _ _ h => h _ hpl') hk)

/-- `mulps d(%b,%i,1), %xmm` on a location outside `dmem`: the address must be
16-byte aligned, the load is two 8-byte pieces (not atomic); then `xmm * mem`,
lanewise, the bits above 128 kept. -/
theorem mulps_load_sib1_disp_shared [CodeEnv] (env : SharedEnv) (x : RegMm) (b i : Reg64)
    (d : Int64)
    {p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + s.regs.get64 i + d.toBitVec
        isAligned 16 a = true ∧ Mem.loadInt s.dmem a 16 = none ∧
          env.LoadPieces a 2 g (fun vs g' =>
            let m := ofPieces 128 vs
            cenv.wpEnv env p Q E { s with zmms := (s.zmms.setLegacy (.xmm x)
              (BitVec.packedBinOp 32 BitVec.f32mul (s.zmms.get (.xmm x)) m)) } g'))
      (Directive.instr (.avx .W64 .W128
          (.mulps (.avx (.xmm x)) (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩))) :: p)
      Q E := by
  intro s g ⟨hal, hnone, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, AvxOperation.interp, AvxRegOrMem.interp,
    MachineData.setAvxLegacy, MachineData.setAvxLegacyReg,
    AddrExpr.zeroExtend_interp_sib1_disp]
  exact MachineData.loadAvx_AllEnv (fun _ => hal) hnone (SharedEnv.LoadPieces.mono
    (fun _ _ h => h _ hpl') hk)

/-- `xorps sym(%rip), %xmm` on a location outside `dmem`: the label's address must
be 16-byte aligned, the load is two 8-byte pieces; then xored into the
register. -/
theorem xorps_load_rip_shared [CodeEnv] (env : SharedEnv) (x : RegMm) (l : Label)
    {p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := ((_root_.Executable.labels cenv).label l).toBitVec
        isAligned 16 a = true ∧ Mem.loadInt s.dmem a 16 = none ∧
          env.LoadPieces a 2 g (fun vs g' =>
            let m := ofPieces 128 vs
            cenv.wpEnv env p Q E { s with zmms := s.zmms.setLegacy (.xmm x) (s.zmms.get (.xmm x) ^^^ m) } g'))
      (Directive.instr (.avx .W64 .W128
          (.xorps (.avx (.xmm x))
            (.mem ⟨some .rip, none, .sub (.label l) .after_current_instruction⟩))) :: p)
      Q E := by
  intro s g ⟨hal, hnone, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, AvxOperation.interp, AvxRegOrMem.interp,
    MachineData.setAvxLegacy, MachineData.setAvxLegacyReg,
    AddrExpr.zeroExtend_interp_rip_label]
  exact MachineData.loadAvx_AllEnv (fun _ => hal) hnone (SharedEnv.LoadPieces.mono
    (fun _ _ h => h _ hpl') hk)

/-- `vmulps d(%b,%i,1), %xmm1, %xmm0` on a location outside `dmem`, at any
alignment: two 8-byte pieces; then `xmm1 * mem` in `xmm0`, written whole. -/
theorem vmulps_load_sib1_disp_shared [CodeEnv] (env : SharedEnv) (dst src1 : AvxReg .W128)
    (b i : Reg64) (d : Int64)
    {p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + s.regs.get64 i + d.toBitVec
        Mem.loadInt s.dmem a 16 = none ∧
          env.LoadPieces a 2 g (fun vs g' =>
            let m := ofPieces 128 vs
            cenv.wpEnv env p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOp 32 BitVec.f32mul (s.zmms.get src1) m) } g'))
      (Directive.instr (.avx .W64 .W128
          (.vmulps dst src1 (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩))) :: p)
      Q E := by
  intro s g ⟨hnone, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, AvxOperation.interp, AvxRegOrMem.interp,
    MachineData.setAvxReg, AddrExpr.zeroExtend_interp_sib1_disp]
  exact MachineData.loadAvx_AllEnv (fun h => nomatch h) hnone (SharedEnv.LoadPieces.mono
    (fun _ _ h => h _ hpl') hk)

/-- `vfmadd231ps d(%b,%i,1), %ymm1, %ymm0` on a location outside `dmem`, at any
alignment: four 8-byte pieces; then `ymm0 + ymm1 * mem`, each lane rounded
once, in `ymm0`. -/
theorem vfmadd231ps_load_sib1_disp_shared [CodeEnv] (env : SharedEnv) (dst src1 : AvxReg .W256)
    (b i : Reg64) (d : Int64)
    {p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + s.regs.get64 i + d.toBitVec
        Mem.loadInt s.dmem a 32 = none ∧
          env.LoadPieces a 4 g (fun vs g' =>
            let m := ofPieces 256 vs
            cenv.wpEnv env p Q E { s with zmms := (s.zmms.set dst
              (BitVec.packedTernOp 32 BitVec.f32fma (s.zmms.get src1) m (s.zmms.get dst))) } g'))
      (Directive.instr (.avx .W64 .W256
          (.vfmadd231ps dst src1 (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩))) :: p)
      Q E := by
  intro s g ⟨hnone, hk⟩
  env_step
  simp only [Directive.interp, Instr.interp, AvxOperation.interp, AvxRegOrMem.interp,
    MachineData.setAvxReg, AddrExpr.zeroExtend_interp_sib1_disp]
  exact MachineData.loadAvx_AllEnv (fun h => nomatch h) hnone (SharedEnv.LoadPieces.mono
    (fun _ _ h => h _ hpl') hk)
end MachineWP
