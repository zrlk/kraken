/-
The atomic and barrier rules of the AArch64 machine-founded wp, next
to the straight-line dictionary of
`Kraken.AArch64.WP.Rules`.

These are the single-threaded meanings of the instructions the weak-memory
layer (`Kraken/Promising`) orders, read from `MachineData.loadK`/`storeK`/`rmwK`
on mapped memory (`dmem`): an acquire or exclusive load is a load, a release
store is a store, a read-modify-write is its load and its store, and a barrier
is a no-op. As in the memory rules of `WP.Rules`, the bytes must be readable (`isSome`), a
load runs the tail at every value they may hold, and an access through `SP`
needs `SP` 16-byte aligned (`RegOrSp.SPAligned`, the base-register form of
`AddrExpr.SPAligned`). The base is a bare register (`[Xn|SP]`), so no rule
reads the instruction's range. A store-exclusive on mapped memory may fail
spuriously: its rule quantifies over the outcome (`∀ ok : Bool`, the pattern of
x64's `fallthrough_nondet_spec`).

Mapped memory only: the preconditions have exactly the shape of `WP.Rules`
(alignment `⊓` readable bytes `⊓` the tail's wp), with no side condition on
shared locations, so the lifting theorem (`MachineWP.wpEnv_of_triple`)
carries these rules over unchanged; the shared-location versions are in
`Kraken.AArch64.EnvWPRules`.

The rules are generic in the register width `w` and the access width `sz`; a
`W`/`B`/`H` form reads `Rs`/`Rt` truncated to `sz` and zero-extends the value
it loads. `LD<op>` is one rule over `AtomicOp` (`AtomicOp.apply_*` reduce the
operation); the parser writes `ST<op>` as `LD<op>` with `Rt = ZR`, so the
same rule covers it.

## Coverage

| Rule | Instruction forms | Widths |
|---|---|---|
| `ldar_spec` | `LDAR`, `LDAPR`, `LDXR`, `LDAXR` (`k`, `xcl`), `[Xn\|SP]` | X, W; B, H, W, X access |
| `stlr_spec` | `STLR` | X, W; B, H, W, X access |
| `stxr_spec` | `STXR`, `STLXR` (success nondeterministic: `∀ ok`) | X, W; B, H, W, X access |
| `cas_spec` | `CAS`, `CASA`, `CASL`, `CASAL` (success and failure branches) | X, W; B, H, W, X access |
| `swp_spec` | `SWP`, `SWPA`, `SWPL`, `SWPAL` | X, W; B, H, W, X access |
| `ldop_spec` | `LDADD`, `LDCLR`, `LDEOR`, `LDSET`, `LDSMAX`, `LDSMIN`, `LDUMAX`, `LDUMIN` (+`A`/`L`/`AL`), and the `ST<op>` aliases (`Rt = ZR`) | X, W; B, H, W, X access |
| `dmb_spec`, `dsb_spec`, `isb_spec` | `DMB`, `DSB` (every option), `ISB`: no-ops | — |

`RegWidth.bytes_W64`, `RegWidth.bytes_W32`, `RegWidth.bits_W64`,
`RegWidth.bits_W32` are the concrete width simp lemmas (they
reduce the `match RegWidth.W64 … => 8` byte counts writeback VCs leave).
-/
import Kraken.AArch64.WP.Rules

open Kraken
open Std.WP
open Lean.Order

/-! ## Operand reductions -/

@[simp, grind =] theorem RegWidth.bytes_W64 : RegWidth.W64.bytes = 8 := rfl
@[simp, grind =] theorem RegWidth.bytes_W32 : RegWidth.W32.bytes = 4 := rfl
@[simp, grind =] theorem RegWidth.bits_W64 : RegWidth.W64.bits = 64 := rfl
@[simp, grind =] theorem RegWidth.bits_W32 : RegWidth.W32.bits = 32 := rfl

@[simp, grind =] theorem AtomicOp.apply_ADD {n} (old rs : BitVec n) :
    AtomicOp.ADD.apply old rs = old + rs := rfl
@[simp, grind =] theorem AtomicOp.apply_CLR {n} (old rs : BitVec n) :
    AtomicOp.CLR.apply old rs = old &&& ~~~rs := rfl
@[simp, grind =] theorem AtomicOp.apply_EOR {n} (old rs : BitVec n) :
    AtomicOp.EOR.apply old rs = old ^^^ rs := rfl
@[simp, grind =] theorem AtomicOp.apply_SET {n} (old rs : BitVec n) :
    AtomicOp.SET.apply old rs = old ||| rs := rfl
@[simp, grind =] theorem AtomicOp.apply_SMAX {n} (old rs : BitVec n) :
    AtomicOp.SMAX.apply old rs = if old.slt rs then rs else old := rfl
@[simp, grind =] theorem AtomicOp.apply_SMIN {n} (old rs : BitVec n) :
    AtomicOp.SMIN.apply old rs = if old.slt rs then old else rs := rfl
@[simp, grind =] theorem AtomicOp.apply_UMAX {n} (old rs : BitVec n) :
    AtomicOp.UMAX.apply old rs = if old.ult rs then rs else old := rfl
@[simp, grind =] theorem AtomicOp.apply_UMIN {n} (old rs : BitVec n) :
    AtomicOp.UMIN.apply old rs = if old.ult rs then old else rs := rfl

/-! ### The base register -/

/-- `RegOrSp.interpBase` passes: an access through `SP` needs `SP` 16-byte
aligned. At a base register literal it reduces to `True` or to the alignment
of `SP`. -/
def RegOrSp.SPAligned (b : RegOrSp .W64) (s : MachineData) : Prop :=
  b = .low .SP .W64 → s.regs.SP.toBitVec % 16#64 = 0#64

@[simp, grind =] theorem RegOrSp.SPAligned_X (r : XReg) (s : MachineData) :
    RegOrSp.SPAligned (.low (.reg r) .W64) s = True := by
  simp [RegOrSp.SPAligned]

@[simp, grind =] theorem RegOrSp.SPAligned_SP (s : MachineData) :
    RegOrSp.SPAligned (.low .SP .W64) s = (s.regs.SP.toBitVec % 16#64 = 0#64) := by
  simp [RegOrSp.SPAligned]

private theorem RegOrSp.interpBase_All {b : RegOrSp .W64} {s : MachineData}
    {ok : BitVec 64 → Effects} {P : MachineState → Prop} (ha : b.SPAligned s)
    (hk : (ok (s.regs.getRegOrSp b)).All P) : (b.interpBase s ok).All P := by
  obtain ⟨b, w⟩ := b
  cases b with
  | reg r => exact hk
  | SP =>
    have h := ha rfl
    simp only [RegOrSp.interpBase, Reg64s.getRegOrSp_SP, h, bne_self_eq_false,
      Bool.false_eq_true, ite_false]
    simpa using hk

/-! ### The kinded accesses on mapped memory -/

private theorem MachineData.loadK_All {s : MachineData} {k : LoadKind} {xcl : Bool}
    {addr : BitVec 64} {w : MemWidth} {ret : w.type → MachineData → Effects}
    {P : MachineState → Prop} {v : Int}
    (hv : Mem.loadInt s.dmem addr w.bytes = some v) (hk : (ret (.ofInt _ v) s).All P) :
    (s.loadK k xcl addr w ret).All P := by
  simp only [MachineData.loadK, Effects.All, hv]
  exact hk

private theorem MachineData.storeK_All {s : MachineData} {k : StoreKind}
    {addr : BitVec 64} {w : MemWidth} {val : w.type} {ret : Bool → MachineData → Effects}
    {P : MachineState → Prop}
    (hv : (Mem.loadInt s.dmem addr w.bytes).isSome = true)
    (hk : (ret true { s with dmem := Mem.storeInt s.dmem addr w.bytes val.toInt }).All P) :
    (s.storeK k false addr val ret).All P := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hv
  simp only [MachineData.storeK, Effects.All, hv, Bool.false_eq_true, ite_false]
  exact hk

private theorem MachineData.storeK_xcl_All {s : MachineData} {k : StoreKind}
    {addr : BitVec 64} {w : MemWidth} {val : w.type} {ret : Bool → MachineData → Effects}
    {P : MachineState → Prop}
    (hv : (Mem.loadInt s.dmem addr w.bytes).isSome = true)
    (hk : ∀ ok : Bool,
      (ret ok (if ok then { s with dmem := Mem.storeInt s.dmem addr w.bytes val.toInt }
        else s)).All P) :
    (s.storeK k true addr val ret).All P := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hv
  simp only [MachineData.storeK, Effects.All, hv, ite_true]
  intro ok
  cases ok
  · simpa using hk false
  · simpa using hk true

private theorem MachineData.rmwK_All {s : MachineData} {k : RmwKind} {noRet : Bool}
    {addr : BitVec 64} {w : MemWidth} {op : w.type → Option w.type}
    {ret : w.type → MachineData → Effects} {P : MachineState → Prop} {v : Int}
    (hv : Mem.loadInt s.dmem addr w.bytes = some v)
    (hk : (ret (.ofInt _ v) (match op (.ofInt _ v) with
      | some new => { s with dmem := Mem.storeInt s.dmem addr w.bytes new.toInt }
      | none => s)).All P) :
    (s.rmwK k noRet addr w op ret).All P := by
  simp only [MachineData.rmwK, Effects.All, hv]
  revert hk
  cases op (.ofInt _ v) <;> exact id

section Specs

open MachineWP

variable [CodeEnv] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}
  {p : Program}

local macro "wp_step" : tactic =>
  `(tactic| simp only [Executable.stepAt, Directive.interp, Instr.interp,
      Operation.interp, MachineData.setRegOrZr, MachineData.setRegOrSp, Effects.All,
      or_false, false_or])

/-- Unfold the fall-through address past one instruction cell (`Rules.lean`). -/
private theorem after_instr {i : Instr} {q : Program} {pc : Int64} {z : Nat}
    {rest : List (Directive × Nat)}
    (hcode : cenv.codeAt pc = (Directive.instr i, z) :: rest) :
    cenv.after pc (Directive.instr i :: q) = cenv.after (pc + .ofNat z) q := by
  simp only [Executable.after, hcode]

/-- Run one cell and continue (`Rules.lean`). -/
private theorem step_here {post : @Post MachineState} {s : MachineData} {pc : Int64}
    {d : Directive} {z : Nat} {rest : List (Directive × Nat)}
    (hseg : cenv.codeAt pc = (d, z) :: rest)
    (hall : cenv.stepAt d z (s, pc) (fun st => Eventually cenv.instrStep post st)) :
    Eventually cenv.instrStep post (s, pc) :=
  step_cps _ _ _ ⟨d, z, rest, hseg, hall⟩

/-- The rule of a cell that falls through with an arbitrary precondition
(`Rules.lean`'s `fallthrough_pre_spec`). -/
private theorem fallthrough_pre_spec {i : Instr} {P : MachineData → Prop}
    (hcell : ∀ (s : MachineData) (rng : Std.Rco Int64) (R : MachineState → Prop),
      P s → (∀ s', WP.wp p Q E s' → R (s', 0)) →
      (@Directive.interp (_root_.Executable.labels cenv) (Directive.instr i) s rng
        (fun s' => .done (s', 0)) (fun _ _ => .unimplemented "jump")).All R) :
    ⦃ P ⦄ (Directive.instr i :: p) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    exact step_here hseg (Or.inl (hcell s _ _ h (fun s' hs' => hs' _ hpl')))

/-! ### Acquire, exclusive and release accesses -/

/-- `LDAR`/`LDAPR`/`LDXR`/`LDAXR Rt, [Xn|SP]` (+`B`/`H`) : the bytes must be
readable; the tail runs with them zero-extended in `Rt`. -/
@[spec] theorem MachineWP.ldar_spec {w : RegWidth} (k : LoadKind) (xcl : Bool) (sz : MemWidth)
    (dst : RegOrZr w) (base : RegOrSp .W64) :
    ⦃ fun s => base.SPAligned s ⊓
        let a := s.regs.getRegOrSp base
        ((Mem.loadInt s.dmem a sz.bytes).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a sz.bytes = some v →
            WP.wp p Q E
              { s with regs := s.regs.setRegOrZr dst ((BitVec.ofInt sz.bits v).setWidth w.bits) }) ⦄
      (Directive.instr ⟨w, .LDAR k xcl sz dst base⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_pre_spec (fun s rng R h hR => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨ha, hsome, hk⟩ := h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    wp_step
    exact RegOrSp.interpBase_All ha (MachineData.loadK_All hv (hR _ (hk v hv))))

/-- `STLR Rt, [Xn|SP]` (+`B`/`H`) : the bytes must be owned (readable); the
tail runs on the updated memory. -/
@[spec] theorem MachineWP.stlr_spec {w : RegWidth} (sz : MemWidth) (src : RegOrZr w)
    (base : RegOrSp .W64) :
    ⦃ fun s => base.SPAligned s ⊓
        let a := s.regs.getRegOrSp base
        ((Mem.loadInt s.dmem a sz.bytes).isSome = true)
          ⊓ WP.wp p Q E { s with
              dmem := Mem.storeInt s.dmem a sz.bytes
                ((s.regs.getRegOrZr src).setWidth sz.bits).toInt } ⦄
      (Directive.instr ⟨w, .STLR sz src base⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_pre_spec (fun s rng R h hR => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨ha, hsome, hk⟩ := h
    wp_step
    simp only [BitVec.take_eq_setWidth]
    exact RegOrSp.interpBase_All ha (MachineData.storeK_All hsome (hR _ hk)))

/-- `STXR`/`STLXR Ws, Rt, [Xn|SP]` (+`B`/`H`) : the bytes must be owned; on
mapped memory the store may fail spuriously, so the tail must hold for either
outcome `ok`: on success the value is stored and `Ws` gets `0`, on failure
memory is untouched and `Ws` gets `1`. -/
@[spec] theorem MachineWP.stxr_spec {w : RegWidth} (k : StoreKind) (sz : MemWidth)
    (status : RegOrZr .W32) (src : RegOrZr w) (base : RegOrSp .W64) :
    ⦃ fun s => base.SPAligned s ⊓
        let a := s.regs.getRegOrSp base
        ((Mem.loadInt s.dmem a sz.bytes).isSome = true)
          ⊓ ∀ ok : Bool, WP.wp p Q E
              { s with
                regs := s.regs.setRegOrZr status (if ok then 0#32 else 1#32),
                dmem := if ok then
                    Mem.storeInt s.dmem a sz.bytes ((s.regs.getRegOrZr src).setWidth sz.bits).toInt
                  else s.dmem } ⦄
      (Directive.instr ⟨w, .STXR k sz status src base⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_pre_spec (fun s rng R h hR => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨ha, hsome, hk⟩ := h
    wp_step
    simp only [BitVec.take_eq_setWidth]
    refine RegOrSp.interpBase_All ha (MachineData.storeK_xcl_All hsome fun ok => ?_)
    cases ok
    · exact hR _ (hk false)
    · exact hR _ (hk true))

/-! ### Read-modify-write -/

/-- `CAS`/`CASA`/`CASL`/`CASAL Rs, Rt, [Xn|SP]` (+`B`/`H`) : the bytes must be
readable and owned; `Rs` gets the old value zero-extended. If the old value
equals `Rs` (truncated to the access) the tail runs with `Rt` stored,
otherwise with memory untouched. -/
@[spec] theorem MachineWP.cas_spec {w : RegWidth} (k : RmwKind) (sz : MemWidth)
    (rs rt : RegOrZr w) (base : RegOrSp .W64) :
    ⦃ fun s => base.SPAligned s ⊓
        let a := s.regs.getRegOrSp base
        ((Mem.loadInt s.dmem a sz.bytes).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a sz.bytes = some v →
            let old := BitVec.ofInt sz.bits v
            let cmp := (s.regs.getRegOrZr rs).setWidth sz.bits
            let regs := s.regs.setRegOrZr rs (old.setWidth w.bits)
            (old = cmp → WP.wp p Q E { s with
                regs,
                dmem := Mem.storeInt s.dmem a sz.bytes
                  ((s.regs.getRegOrZr rt).setWidth sz.bits).toInt })
            ⊓ (old ≠ cmp → WP.wp p Q E { s with regs })) ⦄
      (Directive.instr ⟨w, .CAS k sz rs rt base⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_pre_spec (fun s rng R h hR => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨ha, hsome, hk⟩ := h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨heq_k, hne_k⟩ := hk v hv
    wp_step
    simp only [BitVec.take_eq_setWidth]
    refine RegOrSp.interpBase_All ha (MachineData.rmwK_All hv ?_)
    by_cases heq : BitVec.ofInt sz.bits v = (s.regs.getRegOrZr rs).setWidth sz.bits
    · have hb : (BitVec.ofInt sz.bits v == (s.regs.getRegOrZr rs).setWidth sz.bits) = true := by
        simpa using heq
      simp only [hb, ite_true, Effects.All]
      exact hR _ (heq_k heq)
    · have hb : (BitVec.ofInt sz.bits v == (s.regs.getRegOrZr rs).setWidth sz.bits) = false := by
        simpa using heq
      simp only [hb, Bool.false_eq_true, ite_false, Effects.All]
      exact hR _ (hne_k heq))

/-- `SWP`/`SWPA`/`SWPL`/`SWPAL Rs, Rt, [Xn|SP]` (+`B`/`H`) : the bytes must be
readable and owned; the tail runs with `Rs` stored and the old value
zero-extended in `Rt`. -/
@[spec] theorem MachineWP.swp_spec {w : RegWidth} (k : RmwKind) (sz : MemWidth)
    (rs rt : RegOrZr w) (base : RegOrSp .W64) :
    ⦃ fun s => base.SPAligned s ⊓
        let a := s.regs.getRegOrSp base
        ((Mem.loadInt s.dmem a sz.bytes).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a sz.bytes = some v →
            WP.wp p Q E { s with
              regs := s.regs.setRegOrZr rt ((BitVec.ofInt sz.bits v).setWidth w.bits),
              dmem := Mem.storeInt s.dmem a sz.bytes
                ((s.regs.getRegOrZr rs).setWidth sz.bits).toInt }) ⦄
      (Directive.instr ⟨w, .SWP k sz rs rt base⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_pre_spec (fun s rng R h hR => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨ha, hsome, hk⟩ := h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    wp_step
    simp only [BitVec.take_eq_setWidth]
    exact RegOrSp.interpBase_All ha (MachineData.rmwK_All hv (hR _ (hk v hv))))

/-- `LD<op>`/`LD<op>A`/`LD<op>L`/`LD<op>AL Rs, Rt, [Xn|SP]` (+`B`/`H`) for `op`
among `ADD CLR EOR SET SMAX SMIN UMAX UMIN`, and `ST<op> Rs, [Xn|SP]` (`Rt` is
`ZR`) : the bytes must be readable and owned; the tail runs with
`op old Rs` stored and the old value zero-extended in `Rt`. -/
@[spec] theorem MachineWP.ldop_spec {w : RegWidth} (op : AtomicOp) (k : RmwKind) (sz : MemWidth)
    (rs rt : RegOrZr w) (base : RegOrSp .W64) :
    ⦃ fun s => base.SPAligned s ⊓
        let a := s.regs.getRegOrSp base
        ((Mem.loadInt s.dmem a sz.bytes).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a sz.bytes = some v →
            let old := BitVec.ofInt sz.bits v
            WP.wp p Q E { s with
              regs := s.regs.setRegOrZr rt (old.setWidth w.bits),
              dmem := Mem.storeInt s.dmem a sz.bytes
                (op.apply old ((s.regs.getRegOrZr rs).setWidth sz.bits)).toInt }) ⦄
      (Directive.instr ⟨w, .LDOP op k sz rs rt base⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_pre_spec (fun s rng R h hR => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨ha, hsome, hk⟩ := h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    wp_step
    simp only [BitVec.take_eq_setWidth]
    exact RegOrSp.interpBase_All ha (MachineData.rmwK_All hv (hR _ (hk v hv))))

/-! ### Barriers -/

/-- `DMB <option>` : a no-op on one thread. -/
@[spec] theorem MachineWP.dmb_spec (k : FenceKind) :
    ⦃ fun s => WP.wp p Q E s ⦄ (Directive.instr ⟨.W64, .DMB k⟩ :: p) ⦃ Q; E ⦄ :=
  fallthrough_pre_spec (fun s rng R h hR => by wp_step; exact hR _ h)

/-- `DSB <option>` : a no-op on one thread. -/
@[spec] theorem MachineWP.dsb_spec (k : FenceKind) :
    ⦃ fun s => WP.wp p Q E s ⦄ (Directive.instr ⟨.W64, .DSB k⟩ :: p) ⦃ Q; E ⦄ :=
  fallthrough_pre_spec (fun s rng R h hR => by wp_step; exact hR _ h)

/-- `ISB` : a no-op on one thread. -/
@[spec] theorem MachineWP.isb_spec :
    ⦃ fun s => WP.wp p Q E s ⦄ (Directive.instr ⟨.W64, .ISB⟩ :: p) ⦃ Q; E ⦄ :=
  fallthrough_pre_spec (fun s rng R h hR => by wp_step; exact hR _ h)

end Specs
