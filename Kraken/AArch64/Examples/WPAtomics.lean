/-
`vcgen` twins of the atomic and barrier `kstep` examples of
`Kraken/AArch64/Examples/Atomics.lean` (`stlr_ldar`, `ldadd`, `swp`, `cas`
success and failure, `ldxr_stxr`), on the machine-founded wp with the rules of
`Kraken.AArch64.WP.RulesAtomic`.

As in `WPStraight.lean`, the examples are stated on mapped memory: the 8 bytes
at `X0` hold `v` (`Mem.loadInt … = some v.toBitVec.toInt`), where the `kstep`
originals assume a separating conjunction of their contents. The store-exclusive
rule quantifies over its outcome, so `ldxr_stxr`'s VC is split on it.

Each triple is also read at the machine (`Kraken.AArch64.WP.Bridge`): by
`Program.instrStep_of_triple` as the instruction-step judgment from the start
address to the end of the text, and by `Program.run_of_triple` as the baseline
judgment `Eventually (straightlineStep …)`. Coverage tests at the end exercise
`ST<op>`, other `LD<op>` operations, the byte and `W` widths, `SP` as the base,
and the remaining barriers.
-/
import Kraken.AArch64.Parser
import Kraken.AArch64.WP.Bridge
import Kraken.AArch64.WP.RulesAtomic

open Kraken.AArch64.Parser
open Kraken
open Std.WP
open MachineWP

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## Helpers -/

/-- A load at the address an 8-byte store wrote reads back the stored bytes. -/
private theorem loadInt_storeInt_same (m : DataMem) (a : BitVec 64) (x : Int) :
    Mem.loadInt (Mem.storeInt m a 8 x) a 8 = some (Int.ofBytes (Int.toBytes 8 x)) :=
  Mem.loadInt_storeInt m a 8 x (by decide)

/-- Reducing an integer modulo `2^64` does not change its 64-bit value. -/
private theorem ofInt_bmod64 (x : Int) :
    BitVec.ofInt 64 (x.bmod 18446744073709551616) = BitVec.ofInt 64 x := by
  apply BitVec.eq_of_toInt_eq
  simp [BitVec.toInt_ofInt, Int.bmod_bmod]

/-- A load at the address a 1-byte store wrote reads back the stored byte. -/
private theorem loadInt_storeInt_same1 (m : DataMem) (a : BitVec 64) (x : Int) :
    Mem.loadInt (Mem.storeInt m a 1 x) a 1 = some (Int.ofBytes (Int.toBytes 1 x)) :=
  Mem.loadInt_storeInt m a 1 x (by decide)

/-- The low byte of a register, read as a signed byte and re-encoded. -/
private theorem ofInt_bmod_toNat (x : UInt64) :
    BitVec.ofInt 8 ((x.toNat : Int).bmod 256) = x.toBitVec.setWidth 8 := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_ofInt, BitVec.toInt_setWidth]
  simp only [Int.bmod_bmod]
  rfl

/-! ## Programs -/

/-- Release store, barriers, acquire loads. -/
def stlr_ldar : Program := parseAArch64("
    stlr x1, [x0]
    dmb ish
    dmb ishld
    dsb sy
    isb
    ldar x2, [x0]
    ldapr x3, [x0]
")

/-- Atomic add: the old value is returned, the sum is stored. -/
def ldadd : Program := parseAArch64("
    ldaddal x1, x2, [x0]
    ldr x3, [x0]
")

/-- Swap: the old value is returned, the register is stored. -/
def swp : Program := parseAArch64("
    swpal x1, x2, [x0]
    ldr x3, [x0]
")

/-- Compare-and-swap: `x1` receives the old value either way. -/
def cas : Program := parseAArch64("
    casal x1, x2, [x0]
    ldr x3, [x0]
")

/-- Load-exclusive/store-exclusive: `w3` reports whether the store happened
(0 on success). -/
def ldxr_stxr : Program := parseAArch64("
    ldaxr x2, [x0]
    stlxr w3, x1, [x0]
    ldr x4, [x0]
")

variable [layout : _root_.Layout]

/-! ## `stlr_ldar` -/

section
local instance stlr_ldar.env : CodeEnv := ⟨layout stlr_ldar⟩

theorem stlr_ldar_correct (d : MachineData)
    (h : (Mem.loadInt d.dmem d.regs.X0.toBitVec 8).isSome) :
    ⦃ fun s => s = d ⦄
      stlr_ldar
    ⦃ fun _ s => s.regs.X2 = d.regs.X1 ∧ s.regs.X3 = d.regs.X1 ⦄ := by
  vcgen [stlr_ldar]
  all_goals subst_vars
  all_goals simp [loadInt_storeInt_same] at *
  all_goals subst_vars
  all_goals simp_all [BitVec.ofInt_ofBytes_toBytes_eq 64 8 rfl]

theorem stlr_ldar_instrStep [Executable.ValidLayout (layout stlr_ldar)] (d : MachineData)
    (h : (Mem.loadInt d.dmem d.regs.X0.toBitVec 8).isSome) :
    Eventually (layout stlr_ldar).instrStep
      (fun st => st.2 = (layout stlr_ldar).addrOf stlr_ldar.length
        ∧ st.1.regs.X2 = d.regs.X1 ∧ st.1.regs.X3 = d.regs.X1)
      (d, Kraken.Layout.start Directive) :=
  Program.instrStep_of_triple (stlr_ldar_correct d h) rfl

theorem stlr_ldar_run [Executable.ValidLayout (layout stlr_ldar)] (d : MachineData)
    (h : (Mem.loadInt d.dmem d.regs.X0.toBitVec 8).isSome) :
    Eventually (straightlineStep (layout stlr_ldar))
      (fun st => st.1.regs.X2 = d.regs.X1 ∧ st.1.regs.X3 = d.regs.X1)
      (d, Kraken.Layout.start Directive) :=
  Program.run_of_triple (stlr_ldar_correct d h) rfl
end

/-! ## `ldadd` -/

section
local instance ldadd.env : CodeEnv := ⟨layout ldadd⟩

theorem ldadd_correct (d : MachineData) (v : UInt64)
    (h : Mem.loadInt d.dmem d.regs.X0.toBitVec 8 = some v.toBitVec.toInt) :
    ⦃ fun s => s = d ⦄
      ldadd
    ⦃ fun _ s => s.regs.X2 = v ∧ s.regs.X3 = v + d.regs.X1 ⦄ := by
  vcgen [ldadd]
  all_goals subst_vars
  all_goals simp [loadInt_storeInt_same] at *
  all_goals subst_vars
  all_goals simp_all [BitVec.ofInt_ofBytes_toBytes_eq 64 8 rfl, ofInt_bmod64, BitVec.ofInt_add]

theorem ldadd_instrStep [Executable.ValidLayout (layout ldadd)] (d : MachineData) (v : UInt64)
    (h : Mem.loadInt d.dmem d.regs.X0.toBitVec 8 = some v.toBitVec.toInt) :
    Eventually (layout ldadd).instrStep
      (fun st => st.2 = (layout ldadd).addrOf ldadd.length
        ∧ st.1.regs.X2 = v ∧ st.1.regs.X3 = v + d.regs.X1)
      (d, Kraken.Layout.start Directive) :=
  Program.instrStep_of_triple (ldadd_correct d v h) rfl

theorem ldadd_run [Executable.ValidLayout (layout ldadd)] (d : MachineData) (v : UInt64)
    (h : Mem.loadInt d.dmem d.regs.X0.toBitVec 8 = some v.toBitVec.toInt) :
    Eventually (straightlineStep (layout ldadd))
      (fun st => st.1.regs.X2 = v ∧ st.1.regs.X3 = v + d.regs.X1)
      (d, Kraken.Layout.start Directive) :=
  Program.run_of_triple (ldadd_correct d v h) rfl
end

/-! ## `swp` -/

section
local instance swp.env : CodeEnv := ⟨layout swp⟩

theorem swp_correct (d : MachineData) (v : UInt64)
    (h : Mem.loadInt d.dmem d.regs.X0.toBitVec 8 = some v.toBitVec.toInt) :
    ⦃ fun s => s = d ⦄
      swp
    ⦃ fun _ s => s.regs.X2 = v ∧ s.regs.X3 = d.regs.X1 ⦄ := by
  vcgen [swp]
  all_goals subst_vars
  all_goals simp [loadInt_storeInt_same] at *
  all_goals subst_vars
  all_goals simp_all [BitVec.ofInt_ofBytes_toBytes_eq 64 8 rfl]

theorem swp_instrStep [Executable.ValidLayout (layout swp)] (d : MachineData) (v : UInt64)
    (h : Mem.loadInt d.dmem d.regs.X0.toBitVec 8 = some v.toBitVec.toInt) :
    Eventually (layout swp).instrStep
      (fun st => st.2 = (layout swp).addrOf swp.length
        ∧ st.1.regs.X2 = v ∧ st.1.regs.X3 = d.regs.X1)
      (d, Kraken.Layout.start Directive) :=
  Program.instrStep_of_triple (swp_correct d v h) rfl

theorem swp_run [Executable.ValidLayout (layout swp)] (d : MachineData) (v : UInt64)
    (h : Mem.loadInt d.dmem d.regs.X0.toBitVec 8 = some v.toBitVec.toInt) :
    Eventually (straightlineStep (layout swp))
      (fun st => st.1.regs.X2 = v ∧ st.1.regs.X3 = d.regs.X1)
      (d, Kraken.Layout.start Directive) :=
  Program.run_of_triple (swp_correct d v h) rfl
end

/-! ## `cas` -/

section
local instance cas.env : CodeEnv := ⟨layout cas⟩

/-- The compare succeeds: the store happens, and `x1` receives the old value. -/
theorem cas_success (d : MachineData) (v : UInt64)
    (h : Mem.loadInt d.dmem d.regs.X0.toBitVec 8 = some v.toBitVec.toInt)
    (h_eq : d.regs.X1 = v) :
    ⦃ fun s => s = d ⦄
      cas
    ⦃ fun _ s => s.regs.X1 = v ∧ s.regs.X3 = d.regs.X2 ⦄ := by
  vcgen [cas]
  all_goals subst_vars
  all_goals simp [loadInt_storeInt_same] at *
  all_goals subst_vars
  all_goals simp_all [BitVec.ofInt_ofBytes_toBytes_eq 64 8 rfl]

theorem cas_success_instrStep [Executable.ValidLayout (layout cas)] (d : MachineData) (v : UInt64)
    (h : Mem.loadInt d.dmem d.regs.X0.toBitVec 8 = some v.toBitVec.toInt)
    (h_eq : d.regs.X1 = v) :
    Eventually (layout cas).instrStep
      (fun st => st.2 = (layout cas).addrOf cas.length
        ∧ st.1.regs.X1 = v ∧ st.1.regs.X3 = d.regs.X2)
      (d, Kraken.Layout.start Directive) :=
  Program.instrStep_of_triple (cas_success d v h h_eq) rfl

theorem cas_success_run [Executable.ValidLayout (layout cas)] (d : MachineData) (v : UInt64)
    (h : Mem.loadInt d.dmem d.regs.X0.toBitVec 8 = some v.toBitVec.toInt)
    (h_eq : d.regs.X1 = v) :
    Eventually (straightlineStep (layout cas))
      (fun st => st.1.regs.X1 = v ∧ st.1.regs.X3 = d.regs.X2)
      (d, Kraken.Layout.start Directive) :=
  Program.run_of_triple (cas_success d v h h_eq) rfl

/-- The compare fails: nothing is stored, and `x1` receives the old value. -/
theorem cas_failure (d : MachineData) (v : UInt64)
    (h : Mem.loadInt d.dmem d.regs.X0.toBitVec 8 = some v.toBitVec.toInt)
    (h_ne : d.regs.X1 ≠ v) :
    ⦃ fun s => s = d ⦄
      cas
    ⦃ fun _ s => s.regs.X1 = v ∧ s.regs.X3 = v ⦄ := by
  vcgen [cas]
  all_goals subst_vars
  all_goals simp [loadInt_storeInt_same] at *
  all_goals subst_vars
  all_goals simp_all [BitVec.ofInt_ofBytes_toBytes_eq 64 8 rfl]
  -- The success branch of the rule is vacuous: its compare contradicts `h_ne`.
  exact h_ne (UInt64.toBitVec_inj.mp ‹_›).symm

theorem cas_failure_instrStep [Executable.ValidLayout (layout cas)] (d : MachineData) (v : UInt64)
    (h : Mem.loadInt d.dmem d.regs.X0.toBitVec 8 = some v.toBitVec.toInt)
    (h_ne : d.regs.X1 ≠ v) :
    Eventually (layout cas).instrStep
      (fun st => st.2 = (layout cas).addrOf cas.length
        ∧ st.1.regs.X1 = v ∧ st.1.regs.X3 = v)
      (d, Kraken.Layout.start Directive) :=
  Program.instrStep_of_triple (cas_failure d v h h_ne) rfl

theorem cas_failure_run [Executable.ValidLayout (layout cas)] (d : MachineData) (v : UInt64)
    (h : Mem.loadInt d.dmem d.regs.X0.toBitVec 8 = some v.toBitVec.toInt)
    (h_ne : d.regs.X1 ≠ v) :
    Eventually (straightlineStep (layout cas))
      (fun st => st.1.regs.X1 = v ∧ st.1.regs.X3 = v)
      (d, Kraken.Layout.start Directive) :=
  Program.run_of_triple (cas_failure d v h h_ne) rfl
end

/-! ## `ldxr_stxr` -/

section
local instance ldxr_stxr.env : CodeEnv := ⟨layout ldxr_stxr⟩

theorem ldxr_stxr_correct (d : MachineData) (v : UInt64)
    (h : Mem.loadInt d.dmem d.regs.X0.toBitVec 8 = some v.toBitVec.toInt) :
    ⦃ fun s => s = d ⦄
      ldxr_stxr
    ⦃ fun _ s => s.regs.X2 = v ∧
        (s.regs.X3 = 0 ∧ s.regs.X4 = d.regs.X1 ∨ s.regs.X3 = 1 ∧ s.regs.X4 = v) ⦄ := by
  vcgen [ldxr_stxr]
  all_goals subst_vars
  all_goals simp at *
  -- Split on the store-exclusive's outcome `ok`, the only `Bool` in the context.
  all_goals try (by_cases hb : (‹Bool› = true) <;>
    simp only [hb, ite_true, ite_false, Bool.false_eq_true] at *)
  all_goals try simp [loadInt_storeInt_same] at *
  all_goals subst_vars
  all_goals simp_all [BitVec.ofInt_ofBytes_toBytes_eq 64 8 rfl]

theorem ldxr_stxr_instrStep [Executable.ValidLayout (layout ldxr_stxr)] (d : MachineData)
    (v : UInt64) (h : Mem.loadInt d.dmem d.regs.X0.toBitVec 8 = some v.toBitVec.toInt) :
    Eventually (layout ldxr_stxr).instrStep
      (fun st => st.2 = (layout ldxr_stxr).addrOf ldxr_stxr.length ∧ st.1.regs.X2 = v ∧
        (st.1.regs.X3 = 0 ∧ st.1.regs.X4 = d.regs.X1 ∨ st.1.regs.X3 = 1 ∧ st.1.regs.X4 = v))
      (d, Kraken.Layout.start Directive) :=
  Program.instrStep_of_triple (ldxr_stxr_correct d v h) rfl

theorem ldxr_stxr_run [Executable.ValidLayout (layout ldxr_stxr)] (d : MachineData)
    (v : UInt64) (h : Mem.loadInt d.dmem d.regs.X0.toBitVec 8 = some v.toBitVec.toInt) :
    Eventually (straightlineStep (layout ldxr_stxr))
      (fun st => st.1.regs.X2 = v ∧
        (st.1.regs.X3 = 0 ∧ st.1.regs.X4 = d.regs.X1 ∨ st.1.regs.X3 = 1 ∧ st.1.regs.X4 = v))
      (d, Kraken.Layout.start Directive) :=
  Program.run_of_triple (ldxr_stxr_correct d v h) rfl
end

/-! ## Coverage tests

Small programs that exercise more of the atomic rules under `vcgen`: the
`ST<op>` alias, other `LD<op>` operations, byte and `W` widths, an access
through `SP`, and the `DSB`/`ISB` barriers. -/

/-- `STADD` (no result), then `LDCLRAL` and `LDUMAX` returning the old values. -/
def wp_ldop : Program := parseAArch64("
    stadd x1, [x0]
    ldclral x2, x3, [x0]
    ldumax x4, x5, [x0]
    dsb st
")

section
local instance wp_ldop.env : CodeEnv := ⟨layout wp_ldop⟩

theorem wp_ldop_correct (d : MachineData) (v : UInt64)
    (h : Mem.loadInt d.dmem d.regs.X0.toBitVec 8 = some v.toBitVec.toInt) :
    ⦃ fun s => s = d ⦄
      wp_ldop
    ⦃ fun _ s => s.regs.X3.toBitVec = v.toBitVec + d.regs.X1.toBitVec
        ∧ s.regs.X5.toBitVec = (v.toBitVec + d.regs.X1.toBitVec) &&& ~~~d.regs.X2.toBitVec ⦄ := by
  vcgen [wp_ldop]
  all_goals subst_vars
  all_goals simp [loadInt_storeInt_same, - BitVec.toInt_and, - BitVec.toInt_add] at *
  all_goals subst_vars
  all_goals simp_all [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, - BitVec.toInt_and, - BitVec.toInt_add]
end

/-- Byte width: `STLRB` stores the low byte, `LDARB` zero-extends it; `ISB`. -/
def wp_byte_acq : Program := parseAArch64("
    stlrb w1, [x0]
    isb
    ldarb w2, [x0]
")

section
local instance wp_byte_acq.env : CodeEnv := ⟨layout wp_byte_acq⟩

theorem wp_byte_acq_correct (d : MachineData)
    (h : (Mem.loadInt d.dmem d.regs.X0.toBitVec 1).isSome) :
    ⦃ fun s => s = d ⦄
      wp_byte_acq
    ⦃ fun _ s => s.regs.X2.toBitVec = (d.regs.X1.toBitVec.setWidth 8).setWidth 64 ⦄ := by
  vcgen [wp_byte_acq]
  all_goals subst_vars
  all_goals simp [loadInt_storeInt_same1] at *
  all_goals subst_vars
  all_goals simp_all [BitVec.ofInt_ofBytes_toBytes_eq 8 1 rfl, ofInt_bmod_toNat]
end

/-- `W` width through `SP`: `SWP` stores the low word of `w3`, `w4` gets the
old word zero-extended. -/
def wp_swp_sp : Program := parseAArch64("
    swp w3, w4, [sp]
")

section
local instance wp_swp_sp.env : CodeEnv := ⟨layout wp_swp_sp⟩

theorem wp_swp_sp_correct (d : MachineData) (x : Int) (hal : d.regs.SP.toBitVec % 16#64 = 0#64)
    (h : Mem.loadInt d.dmem d.regs.SP.toBitVec 4 = some x) :
    ⦃ fun s => s = d ⦄
      wp_swp_sp
    ⦃ fun _ s => s.regs.X4.toBitVec = (BitVec.ofInt 32 x).setWidth 64 ⦄ := by
  vcgen [wp_swp_sp]
  all_goals subst_vars
  all_goals simp_all
end
