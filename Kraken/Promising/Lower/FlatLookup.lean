/-
**WeakCore's FlatHashMap `lookup` (portable,
`x = false`) for `Int` keys and values, lowered to AArch64.** ISA: AArch64;
machine: the **sequential** machine-founded wp
(`MachineWP`), total correctness, through `ProcSpec.of_cfg`-style `MachineWP.cfg`
blocks. The group match and the pure word model: `FlatGroupMatch.lean`.

* §1 adds the `@[spec]` rules for `RBIT`, `CLZ` and `UMULH`, which the
  dictionary `WP/Rules.lean` lacks (the instructions and their semantics are
  present; the rules are stated here, scoped to this namespace, as candidates
  for `WP/Rules.lean`), and the facts that `rbit; clz` is WeakCore's
  `bit1 ctz` and `umulh` its `bits mulhi`.
* §2: the model `lookupN`, WeakCore's `lookupD false` / `findD false` /
  `candD false` at `K = V = Int`, `hash = hashInt` (the identity), `eq = eqInt`,
  is in the ISA-neutral `FlatModel.lean`; §2 here is the table in memory and
  the hash as the code computes it.
* §3 is the code and `lookup_spec`.
-/
import Kraken.Promising.Lower.FlatGroupMatch

open Kraken.AArch64.Parser
open Kraken
open Std.WP
open MachineWP
open Lean.Order

set_option mvcgen.warning false
set_option experimental.vcgen true

namespace Kraken.Promising.Lower.Flat

/-! ## 1. Rules for `RBIT`, `CLZ`, `UMULH`

The rule pattern of `WP/Rules.lean` (`fallthrough_spec`, private there, is
restated). -/

section Rules
variable [CodeEnv] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}
  {p : Program}

private theorem after_instr' {i : Instr} {q : Program} {pc : Int64} {z : Nat}
    {rest : List (Directive × Nat)}
    (hcode : cenv.codeAt pc = (Directive.instr i, z) :: rest) :
    cenv.after pc (Directive.instr i :: q) = cenv.after (pc + .ofNat z) q := by
  simp only [Executable.after, hcode]

private theorem fallthrough_spec' {i : Instr} {f : MachineData → MachineData}
    (hcell : ∀ (s : MachineData) (rng : Std.Rco Int64) (P : MachineState → Prop),
      P (f s, 0) → (@Directive.interp (_root_.Executable.labels cenv) (Directive.instr i) s rng
        (fun s' => .done (s', 0)) (fun _ _ => .unimplemented "jump")).All P) :
    ⦃ fun s => WP.wp p Q E (f s) ⦄ (Directive.instr i :: p) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr' hseg]
    exact step_cps _ _ _ ⟨_, z, rest, hseg, Or.inl (hcell s _ _ (h _ hpl'))⟩

local macro "wp_step" : tactic =>
  `(tactic| simp only [Executable.stepAt, Directive.interp, Instr.interp,
      Operation.interp, MachineData.setRegOrZr, MachineData.setRegOrSp, Effects.All,
      or_false, false_or])

/-- `RBIT Rd, Rn` : the bits of `Rn` reversed. -/
@[spec] theorem rbit_spec {w : RegWidth} (dst src : RegOrZr w) :
    ⦃ fun s => WP.wp p Q E
        { s with regs := s.regs.setRegOrZr dst (s.regs.getRegOrZr src).reverse } ⦄
      (Directive.instr ⟨w, .RBIT dst src⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec' (fun s rng P hP => by wp_step; exact hP)

/-- `CLZ Rd, Rn` : the leading zeros of `Rn`. -/
@[spec] theorem clz_spec {w : RegWidth} (dst src : RegOrZr w) :
    ⦃ fun s => WP.wp p Q E
        { s with regs := s.regs.setRegOrZr dst (s.regs.getRegOrZr src).clz } ⦄
      (Directive.instr ⟨w, .CLZ dst src⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec' (fun s rng P hP => by wp_step; exact hP)

/-- `UMULH Xd, Xn, Xm` : the high word of the unsigned 128-bit product. -/
@[spec] theorem umulh_spec (dst src1 src2 : RegOrZr .W64) :
    ⦃ fun s => WP.wp p Q E
        { s with regs := s.regs.setRegOrZr dst
                    ((BitVec.ofInt 128 ((s.regs.getRegOrZr src1).unsigned
                      * (s.regs.getRegOrZr src2).unsigned)).extractLsb' 64 64) } ⦄
      (Directive.instr ⟨.W64, .UMULH dst src1 src2⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec' (fun s rng P hP => by wp_step; exact hP)

end Rules

/-! ### `umulh` is `mulhi`

(`rbit; clz` is `ctz`: `ctz_toNat`, in `FlatModel.lean`.) -/

theorem mulhi_toNat (a b : BitVec 64) :
    ((BitVec.ofInt 128 (a.unsigned * b.unsigned)).extractLsb' 64 64).toNat
      = bitN .mulhi a.toNat b.toNat := by
  have ha := a.isLt
  have hb := b.isLt
  have hab : a.toNat * b.toNat < 2 ^ 128 := by
    calc a.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' ha hb
      _ = 2 ^ 128 := by rw [← Nat.pow_add]
  have hq : a.toNat * b.toNat / 2 ^ 64 < 2 ^ 64 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 64)]
    rw [← Nat.pow_add]; exact hab
  simp only [BitVec.unsigned, bitN, W64, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [← Int.natCast_mul, BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hab,
    Nat.mod_eq_of_lt hq]

/-! ## 2. The table in memory and the hash as the code computes it

The model (`Tbl`, `candN`, `findN`, `lookupN`, `ProbeEnds`, `Tbl.Bounded`,
the concrete table `tbl1`) and its register-level facts (`rv`, `candN_rv`, …)
are ISA-neutral and live in `FlatModel.lean`. Here are the parts stated with
the AArch64 machine's `DataMem` and `BitVec.unsigned`. -/

/-- The table in memory: control word `g` at `cb + 8g` (`g ≤ m`), slot `s` at
`sb + 16s` (key) and `sb + 16s + 8` (value) (`s ≤ c`); `Mem.loadInt` reads a
word unsigned. Read-only for `lookup`. -/
def Tbl.InMem (T : Tbl) (m : DataMem) : Prop :=
  (∀ g : BitVec 64, g.toNat ≤ T.mv → Mem.loadInt m (T.cb + g <<< 3) 8 = some (T.ctrl g.toNat)) ∧
  (∀ s : BitVec 64, s.toNat ≤ T.cv →
    Mem.loadInt m (T.sb + s <<< 4) 8 = some (T.key s.toNat)
      ∧ Mem.loadInt m (T.sb + s <<< 4 + 8#64) 8 = some (T.val s.toNat))

/-- The hash mix as the code computes it (`umulh`, `mul`, `eor`). -/
def hmB (kb : BitVec 64) : BitVec 64 :=
  (BitVec.ofInt 128 (kb.unsigned * (0x9E3779B97F4A7C15#64).unsigned)).extractLsb' 64 64
    ^^^ kb * 0x9E3779B97F4A7C15#64

theorem hashN_bv (kb : BitVec 64) :
    hashN kb.toNat = ((hmB kb &&& 0x7F#64 ||| 0x80#64).toNat, (hmB kb >>> 7).toNat) := by
  simp only [hashN, Cmix]
  rw [bitN_lit .mulhi, bitN_lit .wmul, bitN_lit .and _ 0x7F, bitN_lit .or _ 0x80]
  simp only [← mulhi_toNat, bitN_wmul, bitN_xor, bitN_and, bitN_or, bitN_shr _ 7 (by decide), hmB]

/-! ## 3. The code and its specification

ABI (adapted from WeakCore's by-value `MapT`): arguments
`x0 = cb`, `x1 = sb`, `x2 = m`, `x3 = c`, `x4 = k`; result `x0` = the sum's tag
(`0` = `inl ()`, `1` = `inr y`) and `x1 = y`. The map comes back unchanged
(`lookup` writes nothing; `gl`, `n`, `hash`, `eq` are not read: `hashInt` and
`eqInt` are inlined). Scratch: `x5`–`x17`; `x18`–`x30` and `sp` are untouched. -/

/-- `lookup`, lowered. Blocks: the hash (`hashOps`), `find` (one group:
`loadAt`, `matchOps`, `emptyOps`, `base`), `cand` (one candidate lane),
`cand_none` (`find`'s `ifeq Gem 0`), `next` (the triangular step), `found`. -/
def flatLookup : Program := parseAArch64("
flat_lookup:
  movz x9, #0x7c15
  movk x9, #0x7f4a, lsl #16
  movk x9, #0x79b9, lsl #32
  movk x9, #0x9e37, lsl #48
  umulh x10, x4, x9
  mul x11, x4, x9
  eor x10, x10, x11
  and x11, x10, #0x7f
  orr x5, x11, #0x80
  lsr x6, x10, #7
  movz x7, #0
  mov x12, #0x7f7f7f7f7f7f7f7f
  mov x13, #0x0101010101010101
find:
  and x8, x6, x2
  ldr x14, [x0, x8, lsl #3]
  mul x15, x5, x13
  eor x15, x14, x15
  and x16, x15, x12
  add x16, x16, x12
  orr x16, x16, x15
  orr x16, x16, x12
  mvn x15, x16
  and x16, x14, x12
  add x16, x16, x12
  orr x16, x16, x14
  orr x16, x16, x12
  mvn x14, x16
  lsl x8, x8, #3
cand:
  cbz x15, cand_none
  rbit x16, x15
  clz x16, x16
  lsr x16, x16, #3
  orr x16, x8, x16
  and x17, x16, x3
  lsl x17, x17, #4
  ldr x9, [x1, x17]
  cmp x4, x9
  b.eq found
  sub x9, x15, #1
  and x15, x15, x9
  b cand
cand_none:
  cbz x14, next
  movz x0, #0
  ret
next:
  add x7, x7, #1
  add x6, x6, x7
  b find
found:
  add x17, x1, x17
  ldr x1, [x17, #8]
  movz x0, #1
  ret
")

theorem hashN_rv (kb : BitVec 64) :
    hashN (rv kb) = (rv (hmB kb &&& 0x7F#64 ||| 0x80#64), rv (hmB kb >>> 7)) := by
  simp only [rv_def, hashN_bv]

theorem ctrl_load {T : Tbl} {m : DataMem} {mb : BitVec 64} (hm : T.InMem m) (h : rv mb = T.mv)
    (a : BitVec 64) : Mem.loadInt m (T.cb + (a &&& mb) <<< 3) 8 = some (T.ctrl (rv (a &&& mb))) := by
  rw [rv_def] at h ⊢; exact hm.1 _ (h ▸ by rw [BitVec.toNat_and]; exact Nat.and_le_right)
theorem key_load {T : Tbl} {m : DataMem} {cb : BitVec 64} (hm : T.InMem m) (h : rv cb = T.cv)
    (a : BitVec 64) : Mem.loadInt m (T.sb + (a &&& cb) <<< 4) 8 = some (T.key (rv (a &&& cb))) := by
  rw [rv_def] at h ⊢; exact (hm.2 _ (h ▸ by rw [BitVec.toNat_and]; exact Nat.and_le_right)).1

theorem val_load {T : Tbl} {m : DataMem} (hm : T.InMem m) (hc : T.cv < W64) (n : Nat)
    (hn : n ≤ T.cv) :
    Mem.loadInt m (T.sb + BitVec.ofNat 64 n <<< 4 + 8#64) 8 = some (T.val n) := by
  have e : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by unfold W64 at hc; omega)
  have := (hm.2 (BitVec.ofNat 64 n) (by rw [e]; exact hn)).2
  rwa [e] at this

/-- `sp` and the callee-saved `x19`–`x28` as in `t₀`. -/
def Callee (t₀ s : MachineData) : Prop :=
  s.regs.SP = t₀.regs.SP ∧ s.regs.X19 = t₀.regs.X19 ∧ s.regs.X20 = t₀.regs.X20
    ∧ s.regs.X21 = t₀.regs.X21 ∧ s.regs.X22 = t₀.regs.X22 ∧ s.regs.X23 = t₀.regs.X23
    ∧ s.regs.X24 = t₀.regs.X24 ∧ s.regs.X25 = t₀.regs.X25 ∧ s.regs.X26 = t₀.regs.X26
    ∧ s.regs.X27 = t₀.regs.X27 ∧ s.regs.X28 = t₀.regs.X28

/-- The arguments in their registers, and the return address. -/
def Args (T : Tbl) (k : Nat) (ra : Int64) (s : MachineData) : Prop :=
  s.regs.X0.toBitVec = T.cb ∧ s.regs.X1.toBitVec = T.sb ∧ (rv s.regs.X2.toBitVec) = T.mv
    ∧ (rv s.regs.X3.toBitVec) = T.cv ∧ (rv s.regs.X4.toBitVec) = k ∧ s.regs.X30.toBitVec = ra.toBitVec

/-- `lookup`'s precondition: arguments, the table in memory, R-INT, and the
probe-termination property. -/
def LookupPre (x : Tbl × Nat) (ra : Int64) (t : MachineData) : Prop :=
  Args x.1 x.2 ra t ∧ x.1.InMem t.dmem ∧ x.1.Bounded x.2 ∧ ProbeEnds x.1 x.2

/-- The result registers for the model's answer. -/
def ResRegs : Option Nat → MachineData → Prop
  | none, s => s.regs.X0 = 0
  | some y, s => s.regs.X0 = 1 ∧ s.regs.X1.toNat = y

/-- `lookup`'s postcondition: the model's answer, memory and the callee-saved
registers unchanged. -/
def LookupPost (x : Tbl × Nat) (_ra : Int64) (t₀ s : MachineData) : Prop :=
  ∃ r, lookupN x.1 x.2 = some r ∧ ResRegs r s ∧ s.dmem = t₀.dmem ∧ Callee t₀ s

/-- What every block after the hash keeps. -/
def Common (x : Tbl × Nat) (ra : Int64) (t₀ s : MachineData) : Prop :=
  LookupPre x ra s ∧ s.dmem = t₀.dmem ∧ Callee t₀ s ∧ (rv s.regs.X5.toBitVec) = (hashN x.2).1
    ∧ s.regs.X12.toBitVec = 0x7F7F7F7F7F7F7F7F#64 ∧ s.regs.X13.toBitVec = 0x0101010101010101#64
    ∧ (rv s.regs.X7.toBitVec) ≤ x.1.mv

/-- `find`'s answer from the next group on (the registers `pos`, `st` not yet
stepped). -/
abbrev restN (x : Tbl × Nat) (s : MachineData) : Option (Option Nat) :=
  findN x.1 x.2 (hashN x.2).1 (x.1.mv - (rv s.regs.X7.toBitVec))
    (bitN .wadd (rv s.regs.X6.toBitVec) (bitN .wadd (rv s.regs.X7.toBitVec) 1)) (bitN .wadd (rv s.regs.X7.toBitVec) 1)

/-- The spec table. -/
def lookupTable (x : Tbl × Nat) (ra : Int64) (t₀ : MachineData) : Label → MachineData → Prop
  | "flat_lookup", s => s = t₀ ∧ LookupPre x ra t₀
  | "find", s => Common x ra t₀ s ∧ findN x.1 x.2 (hashN x.2).1 (x.1.mv + 1 - (rv s.regs.X7.toBitVec))
      (rv s.regs.X6.toBitVec) (rv s.regs.X7.toBitVec) = Rf x.1 x.2
  | "cand", s => Common x ra t₀ s
      ∧ contN (candN x.1 x.2 (rv s.regs.X8.toBitVec) (rv s.regs.X15.toBitVec)) (rv s.regs.X14.toBitVec) (restN x s) = Rf x.1 x.2
  | "cand_none", s => Common x ra t₀ s ∧ contN none (rv s.regs.X14.toBitVec) (restN x s) = Rf x.1 x.2
  | "next", s => Common x ra t₀ s ∧ restN x s = Rf x.1 x.2
  | "found", s => Common x ra t₀ s ∧ ∃ sr, Rf x.1 x.2 = some (some sr)
      ∧ s.regs.X17.toBitVec = BitVec.ofNat 64 (bandN sr x.1.cv) <<< 4
  | _, _ => False

/-- The variant: the remaining fuel, then the candidate mask. -/
def lookupVar : Label → MachineData → Nat
  | "flat_lookup", s => (rv s.regs.X2.toBitVec + 2) * (W64 + 1)
  | "find", s => (rv s.regs.X2.toBitVec + 1 - (rv s.regs.X7.toBitVec)) * (W64 + 1) + W64
  | "cand", s => (rv s.regs.X2.toBitVec + 1 - (rv s.regs.X7.toBitVec)) * (W64 + 1) + (rv s.regs.X15.toBitVec)
  | "cand_none", s => (rv s.regs.X2.toBitVec + 1 - (rv s.regs.X7.toBitVec)) * (W64 + 1)
  | "next", s => (rv s.regs.X2.toBitVec + 1 - (rv s.regs.X7.toBitVec)) * (W64 + 1)
  | _, _ => 0

section Spec
variable [CodeEnv]

set_option hygiene false in
/-- Open block `l`'s invariant into `h0`–`h4`, `hlr`, `hmem` (at `t₀`'s memory),
`hb`, `hpe`, `hdm`, `hcs`, `h5`, `h12`, `h13`, `hst` and the model fact `hf`. -/
local macro "open_inv" l:str : tactic => `(tactic| (
  have h := ‹lookupTable _ _ _ $l _ ∧ _›
  simp only [lookupTable, lookupVar, Common, LookupPre, Args, Callee] at h
  obtain ⟨⟨⟨⟨⟨h0, h1, h2, h3, h4, hlr⟩, hmem, hb, hpe⟩, hdm, hcs, h5, h12, h13, hst⟩, hf⟩, rfl⟩ := h
  rw [hdm] at hmem))

set_option hygiene false in
/-- Jump to a label: its invariant from the opened facts and `ts`. -/
local macro "goto_inv" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  refine Or.inl (Table.ofLabels_at ⟨by decide, ?_⟩)
  simp only [lookupTable, lookupVar, Common, LookupPre, Args, Callee, restN]
  simp [h0, h1, h2, h3, h4, hlr, hmem, hb, hpe, hdm, hcs, h5, h12, h13, hst, $ts,*]))

set_option linter.unusedSimpArgs false in
/-- **`lookup`'s specification** (sequential machine, total correctness):
entered at `flat_lookup` with the table `T` in memory, its masks and `k` in
`x0`–`x4`, R-INT and `ProbeEnds T k`, every run returns to `ra` with the
model's answer `lookupN T k` in `x0`/`x1`, memory and `sp`, `x19`–`x28`
unchanged. -/
theorem lookup_spec (hpl : Program.PlacedIn flatLookup) :
    cenv.ProcSpec ((_root_.Executable.labels cenv).label "flat_lookup") LookupPre LookupPost := by
  refine Kraken.Executable.ProcSpec.of_cfg (p := flatLookup) lookupTable lookupVar
    (hblocks := ?_) (hpre := fun x ra t h => ⟨rfl, h⟩)
  rintro ⟨T, k⟩ ra t₀
  cfg_cases [flatLookup]
  · -- the hash
    vcgen
    have h := ‹lookupTable _ ra _ "flat_lookup" _ ∧ _›
    simp only [lookupTable, lookupVar] at h
    obtain ⟨⟨rfl, ⟨h0, h1, h2, h3, rfl, hlr⟩, hmem, hb, hpe⟩, rfl⟩ := h
    simp only [lookupTable, lookupVar, Common, LookupPre, Args, Callee]
    simp [h0, h1, h2, h3, hlr, hmem, hb, hpe, hashN_rv, hmB, var_le, Rf]
  · -- find: one group
    vcgen
    all_goals
      open_inv "find"
      rw [findN_step _ _ _ _ _ hst] at hf
      simp only [bandN_rv h2, shl3_rv, matchN_rv (hb.ctrl _) h5, emptyN_rv (hb.ctrl _),
        matchBV, zbBV] at hf
      try (rename_i v hv _; simp [h0, hdm, ctrl_load hmem h2] at hv; subst hv)
      simp only [lookupTable, lookupVar, Common, LookupPre, Args, Callee, restN]
      simp [h0, h1, h2, h3, h4, hlr, hmem, hb, hpe, hdm, hcs, h5, h12, h13, hst, ctrl_load hmem h2,
        hf, Nat.le_of_lt (rv_lt _)]
  · -- cand: one lane
    vcgen
    all_goals open_inv "cand"
    case vc1 => -- no lane left
      rename_i hz _
      simp at hz
      simp only [hz, rv_zero, candN_zero] at hf
      goto_inv [hf, hz]
      decide
    case vc4 => -- the key matches
      rename_i hz _ v hv hc _
      simp [h1, hdm, key_load hmem h3] at hv hz
      subst hv
      simp at hc
      rw [sub_rv _ _ (hb.key _), h4] at hc
      rw [candN_rv _ _ _ _ hz] at hf
      simp only [bandN_rv h3, ← hc, eq_self, ite_true, contN] at hf
      refine Or.inl (Table.ofLabels_at ⟨by decide, ?_⟩)
      simp only [lookupTable, lookupVar, Common, LookupPre, Args, Callee]
      simp [h0, h1, h2, h4, hlr, hmem, hb, hpe, hdm, hcs, h5, h12, h13, hst]
      exact ⟨⟨h3, _, hf.symm, by rw [bandN_rv h3, ofNat_rv]⟩,
        Or.inl (Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero (rv_ne _ hz)) (Nat.le_add_left _ _))⟩
    case vc5 => -- it does not: the next lane
      rename_i hz _ v hv hc _
      simp [h1, hdm, key_load hmem h3] at hv hz
      subst hv
      simp at hc
      rw [sub_rv _ _ (hb.key _), h4] at hc
      rw [candN_rv _ _ _ _ hz] at hf
      simp only [bandN_rv h3, hc, ite_false] at hf
      goto_inv [hf, clear_lt _ hz]
    all_goals simp [h1, hdm, key_load hmem h3]
  · -- cand_none
    vcgen
    all_goals open_inv "cand_none"
    case vc1 => -- no empty lane: the next group
      rename_i hz _
      simp at hz
      simp only [contN, hz, rv_zero, ↓reduceIte] at hf
      goto_inv [hf]
      decide
    case vc2 => -- an empty lane: absent
      rename_i hz _
      simp at hz
      simp only [contN, rv_ne _ hz, ↓reduceIte] at hf
      refine Or.inr ⟨by simp [hlr], none, by rw [lookupN_eq, ← hf]; rfl, ?_⟩
      simp [ResRegs, hdm, Callee, hcs]
  · -- next: the triangular step
    vcgen
    all_goals
      open_inv "next"
      have hlt := next_lt hpe hst hf
      have h7 := rv_add1 _ (Nat.lt_trans (Nat.succ_lt_succ hlt) hb.mv)
      simp only [restN, wadd1] at hf
      simp only [wadd_rv] at hf
      simp only [h7] at hf
      goto_inv [hf, h7, var_lt _ _ hst, Nat.succ_le_of_lt hlt]
  · -- found: the value
    vcgen
    all_goals
      open_inv "found"
      obtain ⟨sr, hf, h17⟩ := hf
      have hvl := val_load hmem hb.cv (bandN sr T.cv) Nat.and_le_right
    case vc1 | vc2 => simp [h1, h17, hdm, hvl]
    case vc3 =>
      rename_i v hv _
      simp [h1, h17, hdm, hvl] at hv
      subst hv
      refine Or.inr ⟨by simp [hlr], some (T.val (bandN sr T.cv)), by rw [lookupN_eq, hf]; rfl, ?_⟩
      simp [ResRegs, hdm, Callee, hcs, UInt64.toNat_ofNat,
        Nat.mod_eq_of_lt (show T.val (bandN sr T.cv) < 2 ^ 64 from hb.val _)]

/-- **Non-vacuity**: `lookup_spec` at the concrete table `tbl1` and key `5`,
whose `Bounded` and `ProbeEnds` hypotheses are discharged (`tbl1_bounded`,
`tbl1_probeEnds`, by `decide`): with the arguments in their registers and
`tbl1` in memory, `lookup` returns to `ra` with `x0 = 1`, `x1 = 55`. -/
theorem lookup_tbl1 (hpl : Program.PlacedIn flatLookup) (ra : Int64) (t : MachineData)
    (ha : Args tbl1 5 ra t) (hm : tbl1.InMem t.dmem) :
    Eventually cenv.instrStep (fun st => st.2 = ra ∧ st.1.regs.X0 = 1 ∧ st.1.regs.X1.toNat = 55
        ∧ st.1.dmem = t.dmem)
      (t, (_root_.Executable.labels cenv).label "flat_lookup") :=
  eventually_weaken _ _ _ _ (fun st ⟨hra, r, hr, hres, hd, _⟩ => by
      rw [tbl1_lookup5] at hr; cases hr; exact ⟨hra, hres.1, hres.2, hd⟩)
    (lookup_spec hpl (tbl1, 5) ra t ⟨ha, hm, tbl1_bounded, tbl1_probeEnds⟩)

end Spec

end Kraken.Promising.Lower.Flat
