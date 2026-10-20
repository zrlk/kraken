/-
WeakCore's FlatHashMap `lookup` (portable, `x = false`) for `Int` keys and
values, lowered to x64. ISA: x64; machine: the sequential machine-founded wp
(`MachineWP`), total correctness, through `ProcSpec.of_cfg`-style
`MachineWP.cfg` blocks. The twin of the AArch64 `FlatLookup.lean`, over the
same ISA-neutral model (`FlatModel.lean`: `lookupN`, `findN`, `candN`,
`hashN`, `zbBV`, `matchBV`) and the group match of `FlatGroupMatchX64.lean`,
here inlined.

ABI. x64 has six SysV argument registers and the loop needs nine live words,
so the table is passed by a descriptor: `rdi = D` points at the four words
`cb`, `sb`, `m`, `c` (control-word base, slot base, group mask, slot mask),
and `rsi = k` is the key. The result is a tag in `rax` (`0` absent, `1`
present) and, when present, the value in `rdx`. Scratch: `rax`, `rcx`,
`rdx`, `r8`–`r11` (caller-saved); `rdi`, `rsi` are preserved.

Instructions. The hash's `128`-bit product uses BMI2 `mulx` and the first
candidate lane BMI1 `tzcnt`, as `gcc -O2 -march=haswell` emits them.

* §1: the hash as the code computes it (`hashN_rvX`), and the table and its
  descriptor in memory (`Tbl.InMemX`).
* §2: the code `flatLookupX`, the block table and the variant.
* §3: `lookup_specX`, the functional spec against `lookupN`, and
  `lookup_tbl1X`, its instance at the sample table (the spec's premise is
  satisfiable and the code returns `55` for key `5`).

The variant is bounded by `W64` rather than by the table's `m` (a variant
reads only the machine state).
-/
import Kraken.Promising.Lower.FlatGroupMatchX64

open Kraken
open Std.WP
open MachineWP
open Lean.Order

set_option mvcgen.warning false
set_option experimental.vcgen true

namespace Kraken.Promising.Lower.Flat

/-! ## 1. The hash and the table in memory -/

private theorem mulhi_toNatX (a b : BitVec 64) :
    (BitVec.ofInt 64 ((a.unsigned * b.unsigned) >>> 64)).toNat = bitN .mulhi a.toNat b.toNat := by
  have ha := a.isLt
  have hb := b.isLt
  have hab : a.toNat * b.toNat < 2 ^ 128 := by
    calc a.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' ha hb
      _ = 2 ^ 128 := by rw [← Nat.pow_add]
  have hq : a.toNat * b.toNat / 2 ^ 64 < 2 ^ 64 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 64)]
    rw [← Nat.pow_add]; exact hab
  simp only [BitVec.unsigned, bitN, W64, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  rw [← Int.natCast_mul, ← Int.natCast_shiftRight, BitVec.ofInt_natCast, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hq]

private theorem mullo_X (a b : BitVec 64) : BitVec.ofInt 64 (a.unsigned * b.unsigned) = a * b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.unsigned]
  rw [← Int.natCast_mul, BitVec.ofInt_natCast, BitVec.toNat_ofNat, BitVec.toNat_mul]

/-- The mixed hash word as the code computes it: `mulx`'s high and low
halves of `k * C`, xored. -/
def hmX (kb : BitVec 64) : BitVec 64 :=
  BitVec.ofInt 64 ((kb.unsigned * (0x9E3779B97F4A7C15#64).unsigned) >>> 64)
    ^^^ BitVec.ofInt 64 (kb.unsigned * (0x9E3779B97F4A7C15#64).unsigned)

/-- `hashN` (`h2`, `h1`) from the code's mixed word. -/
theorem hashN_bvX (kb : BitVec 64) :
    hashN kb.toNat = ((hmX kb &&& 0x7F#64 ||| 0x80#64).toNat, (hmX kb >>> 7).toNat) := by
  simp only [hashN, Cmix]
  rw [bitN_lit .mulhi, bitN_lit .wmul, bitN_lit .and _ 0x7F, bitN_lit .or _ 0x80]
  simp only [← mulhi_toNatX, bitN_wmul, bitN_xor, bitN_and, bitN_or, bitN_shr _ 7 (by decide), hmX,
    mullo_X]

/-- `hashN_bvX` with the key as a register value. -/
theorem hashN_rvX (kb : BitVec 64) :
    hashN (rv kb) = (rv (hmX kb &&& 0x7F#64 ||| 0x80#64), rv (hmX kb >>> 7)) := by
  simp only [rv_def, hashN_bvX]

/-- The table in memory, as for the AArch64 lowering, and its descriptor at
`D`: the words `cb`, `sb`, `m`, `c` at `D`, `D + 8`, `D + 16`, `D + 24`. -/
def Tbl.InMemX (T : Tbl) (D : BitVec 64) (m : DataMem) : Prop :=
  Mem.loadInt m D 8 = some (T.cb.toNat : Int) ∧ Mem.loadInt m (D + 8#64) 8 = some (T.sb.toNat : Int)
  ∧ Mem.loadInt m (D + 16#64) 8 = some (T.mv : Int) ∧ Mem.loadInt m (D + 24#64) 8 = some (T.cv : Int)
  ∧ (∀ g : BitVec 64, g.toNat ≤ T.mv →
    Mem.loadInt m (T.cb + g <<< 3) 8 = some (T.ctrl g.toNat : Int))
  ∧ (∀ s : BitVec 64, s.toNat ≤ T.cv →
    Mem.loadInt m (T.sb + s <<< 4) 8 = some (T.key s.toNat : Int)
      ∧ Mem.loadInt m (T.sb + s <<< 4 + 8#64) 8 = some (T.val s.toNat : Int))

/-! ## 2. The code, its blocks and the variant -/

/-- The lookup's text: the hash, then `find` (one group: the match mask in
`rdx`), `cand` (one candidate lane), `cand_none` (the group's empty mask),
`next` (the triangular probe step) and `found` (the value). -/
def flatLookupX : Program := parse("
flat_lookup:
  movabsq $0x9e3779b97f4a7c15, %rdx
  mulxq %rsi, %rcx, %rax
  xorq %rcx, %rax
  movq %rax, %r8
  andq $0x7f, %r8
  orq $0x80, %r8
  movq %rax, %r9
  shrq $7, %r9
  movq $0, %r10
find:
  movq 16(%rdi), %rcx
  movq %r9, %rax
  andq %rcx, %rax
  shlq $3, %rax
  movq (%rdi), %rdx
  movq (%rdx,%rax), %r11
  movabsq $0x0101010101010101, %rcx
  movq %r8, %rdx
  imulq %rcx, %rdx
  xorq %rdx, %r11
  movabsq $0x7f7f7f7f7f7f7f7f, %rcx
  movq %r11, %rdx
  andq %rcx, %rdx
  addq %rcx, %rdx
  orq %r11, %rdx
  orq %rcx, %rdx
  notq %rdx
cand:
  testq %rdx, %rdx
  je cand_none
  tzcntq %rdx, %rcx
  shrq $3, %rcx
  movq %rax, %r11
  orq %rcx, %r11
  movq 24(%rdi), %rcx
  andq %rcx, %r11
  shlq $4, %r11
  movq 8(%rdi), %rcx
  movq (%rcx,%r11), %rcx
  cmpq %rcx, %rsi
  je found
  movq %rdx, %rcx
  subq $1, %rcx
  andq %rcx, %rdx
  jmp cand
cand_none:
  movq (%rdi), %rdx
  movq (%rdx,%rax), %r11
  movabsq $0x7f7f7f7f7f7f7f7f, %rcx
  movq %r11, %rdx
  andq %rcx, %rdx
  addq %rcx, %rdx
  orq %r11, %rdx
  orq %rcx, %rdx
  notq %rdx
  testq %rdx, %rdx
  je next
  movl $0, %eax
  ret
next:
  addq $1, %r10
  addq %r10, %r9
  jmp find
found:
  movq 8(%rdi), %rcx
  movq 8(%rcx,%r11), %rdx
  movl $1, %eax
  ret
")

/-- `rsp` and the SysV callee-saved registers as in `t₀`. -/
def SavedX (t₀ s : MachineData) : Prop :=
  s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbx = t₀.regs.get64 .rbx
    ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ s.regs.get64 .r12 = t₀.regs.get64 .r12
    ∧ s.regs.get64 .r13 = t₀.regs.get64 .r13 ∧ s.regs.get64 .r14 = t₀.regs.get64 .r14
    ∧ s.regs.get64 .r15 = t₀.regs.get64 .r15

/-- The arguments in their registers, and the return address on the stack. -/
def ArgsX (k : Nat) (D : BitVec 64) (ra : Int64) (s : MachineData) : Prop :=
  s.regs.get64 .rdi = D ∧ rv (s.regs.get64 .rsi) = k ∧ s.retAddr = some ra

/-- The precondition: arguments, the table in memory, and the model's
bounds and probe termination (`Tbl.Bounded`, `ProbeEnds`). -/
def LookupPreX (x : Tbl × Nat × BitVec 64) (ra : Int64) (t : MachineData) : Prop :=
  ArgsX x.2.1 x.2.2 ra t ∧ x.1.InMemX x.2.2 t.dmem ∧ x.1.Bounded x.2.1 ∧ ProbeEnds x.1 x.2.1

/-- The result registers: tag in `rax`, value in `rdx`. -/
def ResRegsX : Option Nat → MachineData → Prop
  | none, s => s.regs.get64 .rax = 0
  | some y, s => s.regs.get64 .rax = 1 ∧ (s.regs.get64 .rdx).toNat = y

/-- The postcondition: the result is `lookupN`'s, memory is unchanged and the
callee-saved registers are restored with the stack popped. -/
def LookupPostX (x : Tbl × Nat × BitVec 64) (_ra : Int64) (t₀ s : MachineData) : Prop :=
  ∃ r, lookupN x.1 x.2.1 = some r ∧ ResRegsX r s ∧ s.dmem = t₀.dmem ∧ CalleeX t₀ s

/-- The invariant at every loop block: the entry precondition, the
arguments, memory and callee-saved registers as at entry, `h2` in `r8`, and
the probe step `st` (`r10`) within `m`. -/
def CommonX (x : Tbl × Nat × BitVec 64) (ra : Int64) (t₀ s : MachineData) : Prop :=
  LookupPreX x ra t₀ ∧ s.regs.get64 .rdi = x.2.2 ∧ rv (s.regs.get64 .rsi) = x.2.1
    ∧ s.dmem = t₀.dmem ∧ SavedX t₀ s ∧ rv (s.regs.get64 .r8) = (hashN x.2.1).1
    ∧ rv (s.regs.get64 .r10) ≤ x.1.mv

section CommonFacts
variable {x : Tbl × Nat × BitVec 64} {ra : Int64} {t₀ s : MachineData}

private theorem CommonX.rdi (h : CommonX x ra t₀ s) : s.regs.get64 .rdi = x.2.2 := h.2.1
private theorem CommonX.mem (h : CommonX x ra t₀ s) : x.1.InMemX (s.regs.get64 .rdi) s.dmem := by
  rw [h.2.2.2.1, h.rdi]; exact h.1.2.1
private theorem CommonX.ld0 (h : CommonX x ra t₀ s) :
    Mem.loadInt s.dmem (s.regs.get64 .rdi) 8 = some (x.1.cb.toNat : Int) := h.mem.1
private theorem CommonX.ld8 (h : CommonX x ra t₀ s) :
    Mem.loadInt s.dmem (s.regs.get64 .rdi + 8#64) 8 = some (x.1.sb.toNat : Int) := h.mem.2.1
private theorem CommonX.ld16 (h : CommonX x ra t₀ s) :
    Mem.loadInt s.dmem (s.regs.get64 .rdi + 16#64) 8 = some (x.1.mv : Int) := h.mem.2.2.1
private theorem CommonX.ld24 (h : CommonX x ra t₀ s) :
    Mem.loadInt s.dmem (s.regs.get64 .rdi + 24#64) 8 = some (x.1.cv : Int) := h.mem.2.2.2.1
private theorem CommonX.ctrl (h : CommonX x ra t₀ s) (a : BitVec 64) :
    Mem.loadInt s.dmem (x.1.cb + (a &&& BitVec.ofNat 64 x.1.mv) <<< 3) 8
      = some (x.1.ctrl (rv (a &&& BitVec.ofNat 64 x.1.mv)) : Int) := by
  rw [rv_def]; exact h.mem.2.2.2.2.1 _ (by
    rw [BitVec.toNat_and]; exact Nat.le_trans Nat.and_le_right (by simp [Nat.mod_le]))
private theorem CommonX.key (h : CommonX x ra t₀ s) (a : BitVec 64) :
    Mem.loadInt s.dmem (x.1.sb + (a &&& BitVec.ofNat 64 x.1.cv) <<< 4) 8
      = some (x.1.key (rv (a &&& BitVec.ofNat 64 x.1.cv)) : Int) := by
  rw [rv_def]; exact (h.mem.2.2.2.2.2 _ (by
    rw [BitVec.toNat_and]; exact Nat.le_trans Nat.and_le_right (by simp [Nat.mod_le]))).1
private theorem CommonX.val (h : CommonX x ra t₀ s) (n : Nat) (hn : n ≤ x.1.cv) :
    Mem.loadInt s.dmem (x.1.sb + BitVec.ofNat 64 n <<< 4 + 8#64) 8 = some (x.1.val n : Int) := by
  have hc := h.1.2.2.1.cv
  have e : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by unfold W64 at hc; omega)
  have := (h.mem.2.2.2.2.2 (BitVec.ofNat 64 n) (by rw [e]; exact hn)).2
  rwa [e] at this

/-- `CommonX` survives a step that keeps the argument, hash, step and
callee-saved registers and memory. -/
private theorem CommonX.keep (h : CommonX x ra t₀ s) (s' : MachineData) (hd : s'.dmem = s.dmem)
    (hr : ∀ r ∈ [Reg64.rdi, .rsi, .r8, .r10, .rsp, .rbx, .rbp, .r12, .r13, .r14, .r15],
      s'.regs.get64 r = s.regs.get64 r) : CommonX x ra t₀ s' := by
  obtain ⟨hp, h0, h4, hdm, ⟨h1, h2, h3, h5, h6, h7, h9⟩, h8, hst⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  obtain ⟨e0, e4, e8, e10, e1, e2, e3, e5, e6, e7, e9⟩ := hr
  exact ⟨hp, e0 ▸ h0, e4 ▸ h4, hd ▸ hdm, ⟨e1 ▸ h1, e2 ▸ h2, e3 ▸ h3, e5 ▸ h5, e6 ▸ h6, e7 ▸ h7,
    e9 ▸ h9⟩, e8 ▸ h8, e10 ▸ hst⟩

private theorem CommonX.retAddr (h : CommonX x ra t₀ s) : s.retAddr = some ra := by
  rw [MachineData.retAddr_congr s t₀ h.2.2.2.1 h.2.2.2.2.1.1]; exact h.1.1.2.2
private theorem CommonX.retAddr' (h : CommonX x ra t₀ s) (s' : MachineData) (hd : s'.dmem = s.dmem)
    (hsp : s'.regs.get64 .rsp = s.regs.get64 .rsp) : s'.retAddr = some ra := by
  rw [MachineData.retAddr_congr s' s hd hsp]; exact h.retAddr
private theorem CommonX.callee (h : CommonX x ra t₀ s) (s' : MachineData)
    (hsp : s'.regs.get64 .rsp = s.regs.get64 .rsp + 8#64)
    (hr : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], s'.regs.get64 r = s.regs.get64 r) :
    CalleeX t₀ s' := by
  obtain ⟨-, -, -, -, ⟨h1, h2, h3, h5, h6, h7, h9⟩, -, -⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  obtain ⟨e2, e3, e5, e6, e7, e9⟩ := hr
  exact ⟨hsp.trans (h1 ▸ rfl), e2.trans h2, e3.trans h3, e5.trans h5, e6.trans h6, e7.trans h7,
    e9.trans h9⟩
/-- `CommonX` across `next`, which steps `st` (`r10`) within `m`. -/
private theorem CommonX.step (h : CommonX x ra t₀ s) (s' : MachineData) (hd : s'.dmem = s.dmem)
    (hr : ∀ r ∈ [Reg64.rdi, .rsi, .r8, .rsp, .rbx, .rbp, .r12, .r13, .r14, .r15],
      s'.regs.get64 r = s.regs.get64 r) (hst : rv (s'.regs.get64 .r10) ≤ x.1.mv) :
    CommonX x ra t₀ s' := by
  obtain ⟨hp, h0, h4, hdm, ⟨h1, h2, h3, h5, h6, h7, h9⟩, h8, -⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  obtain ⟨e0, e4, e8, e1, e2, e3, e5, e6, e7, e9⟩ := hr
  exact ⟨hp, e0 ▸ h0, e4 ▸ h4, hd ▸ hdm, ⟨e1 ▸ h1, e2 ▸ h2, e3 ▸ h3, e5 ▸ h5, e6 ▸ h6, e7 ▸ h7,
    e9 ▸ h9⟩, e8 ▸ h8, hst⟩
private theorem CommonX.r8 (h : CommonX x ra t₀ s) : rv (s.regs.get64 .r8) = (hashN x.2.1).1 :=
  h.2.2.2.2.2.1
private theorem CommonX.st (h : CommonX x ra t₀ s) : rv (s.regs.get64 .r10) ≤ x.1.mv := h.2.2.2.2.2.2
private theorem CommonX.bd (h : CommonX x ra t₀ s) : x.1.Bounded x.2.1 := h.1.2.2.1

end CommonFacts

/-- The probe after the current group. -/
abbrev restNX (x : Tbl × Nat × BitVec 64) (s : MachineData) : Option (Option Nat) :=
  findN x.1 x.2.1 (hashN x.2.1).1 (x.1.mv - rv (s.regs.get64 .r10))
    (bitN .wadd (rv (s.regs.get64 .r9)) (bitN .wadd (rv (s.regs.get64 .r10)) 1))
    (bitN .wadd (rv (s.regs.get64 .r10)) 1)

/-- The block table: at each label, the invariant and the remaining probe's
result equal to the whole lookup's (`Rf`). -/
def lookupTableX (x : Tbl × Nat × BitVec 64) (ra : Int64) (t₀ : MachineData) :
    Label → MachineData → Prop
  | "flat_lookup", s => s = t₀ ∧ LookupPreX x ra t₀
  | "find", s => CommonX x ra t₀ s ∧ findN x.1 x.2.1 (hashN x.2.1).1
      (x.1.mv + 1 - rv (s.regs.get64 .r10)) (rv (s.regs.get64 .r9)) (rv (s.regs.get64 .r10))
        = Rf x.1 x.2.1
  | "cand", s => CommonX x ra t₀ s
      ∧ s.regs.get64 .rax = (s.regs.get64 .r9 &&& BitVec.ofNat 64 x.1.mv) <<< 3
      ∧ contN (candN x.1 x.2.1 (rv (s.regs.get64 .rax)) (rv (s.regs.get64 .rdx)))
          (emptyN (x.1.ctrl (bandN (rv (s.regs.get64 .r9)) x.1.mv))) (restNX x s) = Rf x.1 x.2.1
  | "cand_none", s => CommonX x ra t₀ s
      ∧ s.regs.get64 .rax = (s.regs.get64 .r9 &&& BitVec.ofNat 64 x.1.mv) <<< 3
      ∧ contN none (emptyN (x.1.ctrl (bandN (rv (s.regs.get64 .r9)) x.1.mv))) (restNX x s)
          = Rf x.1 x.2.1
  | "next", s => CommonX x ra t₀ s ∧ restNX x s = Rf x.1 x.2.1
  | "found", s => CommonX x ra t₀ s ∧ ∃ sr, Rf x.1 x.2.1 = some (some sr)
      ∧ s.regs.get64 .r11 = BitVec.ofNat 64 (bandN sr x.1.cv) <<< 4
  | _, _ => False

/-- The entry's variant: above `find`'s at `st = 0`. -/
def varTop : Nat := W64 + (W64 + 1) * W64

/-- The variant: lexicographic in (`W64 - st`, block, remaining lanes). -/
def lookupVarX : Label → MachineData → Nat
  | "flat_lookup", _ => varTop
  | "find", s => W64 + (W64 + 1) * (W64 - rv (s.regs.get64 .r10))
  | "cand", s => rv (s.regs.get64 .rdx) + (W64 + 1) * (W64 - rv (s.regs.get64 .r10))
  | "cand_none", s => (W64 + 1) * (W64 - rv (s.regs.get64 .r10))
  | "next", s => (W64 + 1) * (W64 - rv (s.regs.get64 .r10))
  | _, _ => 0

private theorem var_flat (s : MachineData) : lookupVarX "flat_lookup" s = varTop := rfl
private theorem var_find (s : MachineData) :
    lookupVarX "find" s = W64 + (W64 + 1) * (W64 - rv (s.regs.get64 .r10)) := rfl
private theorem var_cand (s : MachineData) :
    lookupVarX "cand" s = rv (s.regs.get64 .rdx) + (W64 + 1) * (W64 - rv (s.regs.get64 .r10)) := rfl
private theorem var_cn (s : MachineData) :
    lookupVarX "cand_none" s = (W64 + 1) * (W64 - rv (s.regs.get64 .r10)) := rfl
private theorem var_next (s : MachineData) :
    lookupVarX "next" s = (W64 + 1) * (W64 - rv (s.regs.get64 .r10)) := rfl

private theorem var_find_le (s t : MachineData) (h : rv (s.regs.get64 .r10) = 0) :
    lookupVarX "find" s ≤ lookupVarX "flat_lookup" t := by
  rw [var_find, var_flat, h, Nat.sub_zero, varTop]; exact Nat.le_refl _

private theorem hmX_code (kb : BitVec 64) :
    BitVec.ofInt 64 ((kb.unsigned * (BitVec.setWidth 64 (-7046029254386353131 : Int64).toBitVec).unsigned) >>> 64)
      ^^^ BitVec.ofInt 64 (kb.unsigned * (BitVec.setWidth 64 (-7046029254386353131 : Int64).toBitVec).unsigned)
      = hmX kb := by simp [hmX]

private theorem lit127 : BitVec.setWidth 64 (Int64.toBitVec 127) = 0x7F#64 := by decide
private theorem lit128 : BitVec.setWidth 64 (Int64.toBitVec 128) = 0x80#64 := by decide
private theorem lit0 : BitVec.setWidth 64 (Int64.toBitVec 0) = 0#64 := by decide
private theorem lit7 : (Int64.toBitVec 7).toNat % 64 = 7 := by decide

private theorem lit16 : Int64.toBitVec 16 = 16#64 := by decide
private theorem lit24 : Int64.toBitVec 24 = 24#64 := by decide
private theorem lit8 : Int64.toBitVec 8 = 8#64 := by decide
private theorem lit0d (b : BitVec 64) : b + Int64.toBitVec 0 = b := by
  rw [show Int64.toBitVec 0 = 0#64 by decide, BitVec.add_zero]

private theorem lit3 : (Int64.toBitVec 3).toNat % 64 = 3 := by decide
private theorem lit4 : (Int64.toBitVec 4).toNat % 64 = 4 := by decide
private theorem litL8 : BitVec.setWidth 64 (Int64.toBitVec 72340172838076673) = 0x0101010101010101#64 := by
  decide
private theorem litLo7 : BitVec.setWidth 64 (Int64.toBitVec 9187201950435737471) = 0x7F7F7F7F7F7F7F7F#64 := by
  decide
private theorem ofNat_toNat64 (b : BitVec 64) : BitVec.ofNat 64 b.toNat = b := by simp

private theorem lit3' : (3#64).toNat % 64 = 3 := rfl
private theorem lit4' : (4#64).toNat % 64 = 4 := rfl

private theorem var_found (s : MachineData) : lookupVarX "found" s = 0 := rfl
private theorem var_cn_eq (s' s : MachineData) (h : s'.regs.get64 .r10 = s.regs.get64 .r10)
    (hz : s.regs.get64 .rdx = 0#64) : lookupVarX "cand_none" s' = lookupVarX "cand" s := by
  rw [var_cn, var_cand, h, hz, rv_zero, Nat.zero_add]
private theorem var_cand_lt (s' s : MachineData) (h : s'.regs.get64 .r10 = s.regs.get64 .r10)
    (hl : rv (s'.regs.get64 .rdx) < rv (s.regs.get64 .rdx)) :
    lookupVarX "cand" s' < lookupVarX "cand" s := by
  rw [var_cand, var_cand, h]; omega
private theorem var_found_lt (s' s : MachineData) (hz : s.regs.get64 .rdx ≠ 0#64) :
    lookupVarX "found" s' < lookupVarX "cand" s := by
  rw [var_found, var_cand]; have := rv_ne _ hz; omega
private theorem ctz_def (b : BitVec 64) : b.ctz = b.reverse.clz := rfl

private theorem var_next_cn (s' s : MachineData) (h : s'.regs.get64 .r10 = s.regs.get64 .r10) :
    lookupVarX "next" s' = lookupVarX "cand_none" s := by
  rw [var_next, var_cn, h]

private theorem var_find_lt (s' s : MachineData)
    (h : rv (s'.regs.get64 .r10) = rv (s.regs.get64 .r10) + 1)
    (hl : rv (s.regs.get64 .r10) + 1 < W64) : lookupVarX "find" s' < lookupVarX "next" s := by
  rw [var_find, var_next, h, show W64 - rv (s.regs.get64 .r10) = (W64 - (rv (s.regs.get64 .r10) + 1)) + 1
    by omega, Nat.mul_succ]
  omega

private theorem sub_add1 (m : Nat) (b : BitVec 64) (h : rv (b + 1#64) = rv b + 1) :
    m + 1 - rv (b + 1#64) = m - rv b := by rw [h]; omega

private theorem var_cand_le (s' s : MachineData) (h : s'.regs.get64 .r10 = s.regs.get64 .r10) :
    lookupVarX "cand" s' ≤ lookupVarX "find" s := by
  rw [var_cand, var_find, h]; have := rv_lt (s'.regs.get64 .rdx); omega

/-- The code's `zb`: its `add` has the constant first. -/
private theorem zb_code (y : BitVec 64) :
    ~~~((0x7F7F7F7F7F7F7F7F#64 + (y &&& 0x7F7F7F7F7F7F7F7F#64) ||| y) ||| 0x7F7F7F7F7F7F7F7F#64)
      = zbBV y := by
  rw [BitVec.add_comm]; rfl

/-! ## 3. The spec -/

section Spec
variable [CodeEnv]

set_option linter.unusedSimpArgs false in
/-- The x64 lowering computes `lookupN`, returning to the caller. -/
theorem lookup_specX (hpl : Program.PlacedIn flatLookupX) :
    cenv.ProcSpec ((_root_.Executable.labels cenv).label "flat_lookup") LookupPreX LookupPostX := by
  refine Kraken.Executable.ProcSpec.of_cfg (p := flatLookupX) lookupTableX lookupVarX
    (hblocks := ?_) (hpre := fun x ra t h => ⟨rfl, h⟩)
  rintro ⟨T, k, D⟩ ra t₀
  cfg_cases [flatLookupX]
  · -- the hash
    vcgen
    · decide
    · rename_i s h _ _ _ _
      obtain ⟨⟨rfl, hpre⟩, hn⟩ := h
      have ⟨⟨h0, h4, hra⟩, hmem, hb, hpe⟩ := hpre
      simp only at h0 h4 hmem hb hpe
      have hh := hashN_rvX (s.regs.get64 .rsi)
      rw [h4] at hh
      refine ⟨?_, ?_⟩
      · simp only [lookupTableX, CommonX, SavedX, Reg64s.get64_set64, reduceCtorEq,
          ↓reduceIte, hpre, true_and, and_true, h0, h4, hh, hmX_code, lit127, lit128, lit0,
          lit7, rv_zero, Nat.zero_le, Nat.sub_zero, Rf]
      · rw [← hn]
        refine var_find_le _ _ ?_
        simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, lit0, rv_zero]
  · -- find: one group
    refine triple_of_pointwise fun s₀ hT => ?_
    have hc : CommonX (T, k, D) ra t₀ s₀ := hT.1.1
    have hf := hT.1.2
    have hn := hT.2
    clear hT
    vcgen
    case vc5 =>
      subst_vars
      rename_i v1 hv1 _ _ v2 hv2 v3 hv3 _ _ _ _ _ _ _ _
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, lit16, lit0d, hc.ld0, hc.ld16,
        Option.some.injEq] at hv1 hv2
      subst hv1 hv2
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, lit3, BitVec.ofInt_natCast,
        ofNat_toNat64, BitVec.mul_one, BitVec.ofNat_eq_ofNat, hc.ctrl, Option.some.injEq] at hv3
      subst hv3
      have hmv : rv (BitVec.ofNat 64 T.mv) = T.mv := by
        rw [rv_def, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (Nat.lt_of_succ_lt hc.bd.mv)
      rw [findN_step _ _ _ _ _ hc.st] at hf
      simp only [bandN_rv hmv, shl3_rv, matchN_rv (hc.bd.ctrl _) hc.r8, matchBV] at hf
      refine ⟨?_, var_cand_le _ _ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte])⟩
      simp only [lookupTableX, restNX, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, lit3,
        BitVec.ofInt_natCast, litL8, litLo7, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat,
        BitVec.setWidth_eq, lit3', zb_code, bandN_rv hmv, true_and, Rf]
      refine ⟨hc.keep _ rfl ?_, hf⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, and_self]
    all_goals
      subst_vars
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, lit16, lit0d, lit3,
        hc.ld0, hc.ld16, Option.some.injEq, Option.isSome_some, BitVec.ofInt_natCast,
        ofNat_toNat64, BitVec.mul_one, BitVec.ofNat_eq_ofNat, hc.ctrl, not_false_eq_true] at *
      try (subst_vars; simp only [BitVec.ofInt_natCast, ofNat_toNat64, hc.ctrl, Option.isSome_some])
  · -- cand: one lane
    refine triple_of_pointwise fun s₀ hT => ?_
    have hc : CommonX (T, k, D) ra t₀ s₀ := hT.1.1
    have hax := hT.1.2.1
    have hf := hT.1.2.2
    have hn := hT.2
    clear hT
    vcgen
    all_goals
      subst_vars
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, lit16, lit24, lit8, lit0d, lit3,
        lit4, hc.ld8, hc.ld24, Option.some.injEq, Option.isSome_some, BitVec.ofInt_natCast,
        ofNat_toNat64, BitVec.mul_one, BitVec.ofNat_eq_ofNat, not_false_eq_true,
        Int64.toBitVec_ofNat, BitVec.setWidth_eq, lit3', lit4'] at *
      try (subst_vars; simp only [BitVec.ofInt_natCast, ofNat_toNat64, Option.isSome_some,
        BitVec.mul_one, hc.key, Option.some.injEq] at *)
      try subst_vars
    case vc1 => -- no lane left
      rename_i _ hz
      simp only [CondCode.z_interp_from_result, CondCode.z_interp_from_result_false,
          BitVec.and_self, BitVec.ofInt_natCast] at hz
      rw [hz, rv_zero, candN_zero] at hf
      refine Or.inl (Table.ofLabels_at ⟨by decide, ?_⟩)
      simp only [lookupTableX, restNX]
      exact ⟨⟨hc.keep _ rfl (fun _ _ => rfl), hax, hf⟩, Or.inr ⟨var_cn_eq _ _ rfl hz, by decide⟩⟩
    case vc7 => -- the key matches
      rename_i _ hz _ _ _ _ _ _ _ _ hk
      simp only [CondCode.z_interp_from_result, CondCode.z_interp_from_result_false,
          BitVec.and_self, BitVec.ofInt_natCast] at hz hk
      have hcv : rv (BitVec.ofNat 64 T.cv) = T.cv := by
        rw [rv_def, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hc.bd.cv
      rw [sub_rv _ _ (hc.bd.key _), hc.2.2.1, ctz_def] at hk
      rw [candN_rv _ _ _ _ hz, bandN_rv hcv, ← hk] at hf
      simp only [eq_self, ite_true, contN] at hf
      refine Or.inl (Table.ofLabels_at ⟨by decide, ?_⟩)
      simp only [lookupTableX, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, ctz_def]
      refine ⟨⟨hc.keep _ rfl ?_, _, hf.symm, by rw [bandN_rv hcv, ofNat_rv]⟩,
        Or.inl (var_found_lt _ _ hz)⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, and_self]
    case vc8 => -- it does not: the next lane
      rename_i hz _ _ _ _ _ _ _ _ _ hk
      simp only [CondCode.z_interp_from_result, CondCode.z_interp_from_result_false,
          BitVec.and_self, BitVec.ofInt_natCast] at hz hk
      have hcv : rv (BitVec.ofNat 64 T.cv) = T.cv := by
        rw [rv_def, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hc.bd.cv
      rw [sub_rv _ _ (hc.bd.key _), hc.2.2.1, ctz_def] at hk
      rw [candN_rv _ _ _ _ hz, bandN_rv hcv] at hf
      simp only [hk, ite_false] at hf
      refine Or.inl (Table.ofLabels_at ⟨by decide, ?_⟩)
      simp only [lookupTableX, restNX, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      refine ⟨⟨hc.keep _ rfl ?_, hax, hf⟩, Or.inl (var_cand_lt _ _ ?_ ?_)⟩
      all_goals simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, and_self]
      exact clear_lt _ hz

  · -- cand_none
    refine triple_of_pointwise fun s₀ hT => ?_
    have hc : CommonX (T, k, D) ra t₀ s₀ := hT.1.1
    have hax := hT.1.2.1
    have hf := hT.1.2.2
    have hn := hT.2
    clear hT
    vcgen
    all_goals
      subst_vars
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, lit0d, hc.ld0, Option.some.injEq,
        Option.isSome_some, BitVec.ofInt_natCast, ofNat_toNat64, BitVec.mul_one,
        BitVec.ofNat_eq_ofNat, not_false_eq_true, Int64.toBitVec_ofNat, BitVec.setWidth_eq,
        litLo7, hax, BitVec.add_zero] at *
      try subst_vars
      try simp only [BitVec.ofInt_natCast, ofNat_toNat64, Option.isSome_some,
        BitVec.mul_one, hc.ctrl, Option.some.injEq] at *
      try subst_vars
    case vc3 => -- no empty lane: the next group
      rename_i hz
      simp only [CondCode.z_interp_from_result, CondCode.z_interp_from_result_false,
          BitVec.and_self, BitVec.ofInt_natCast, zb_code] at hz
      have hmv : rv (BitVec.ofNat 64 T.mv) = T.mv := by
        rw [rv_def, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (Nat.lt_of_succ_lt hc.bd.mv)
      rw [bandN_rv hmv, emptyN_rv (hc.bd.ctrl _), hz, rv_zero] at hf
      simp only [contN, ↓reduceIte] at hf
      refine Or.inl (Table.ofLabels_at ⟨by decide, ?_⟩)
      simp only [lookupTableX, restNX, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      refine ⟨⟨hc.keep _ rfl ?_, hf⟩, Or.inr ⟨var_next_cn _ _ ?_, by decide⟩⟩
      all_goals simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, and_self]
    case vc4 =>
      simp only [MachineData.retAddr_eq, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      rw [← MachineData.retAddr_eq, hc.retAddr]; rfl
    case vc5 => -- an empty lane: absent
      rename_i ra' hz hra'
      simp only [CondCode.z_interp_from_result, CondCode.z_interp_from_result_false,
          BitVec.and_self, BitVec.ofInt_natCast, zb_code] at hz
      simp only [MachineData.retAddr_eq, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at hra'
      rw [← MachineData.retAddr_eq, hc.retAddr, Option.some.injEq] at hra'
      subst hra'
      have hmv : rv (BitVec.ofNat 64 T.mv) = T.mv := by
        rw [rv_def, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (Nat.lt_of_succ_lt hc.bd.mv)
      rw [bandN_rv hmv, emptyN_rv (hc.bd.ctrl _)] at hf
      simp only [contN, rv_ne _ hz, ↓reduceIte] at hf
      refine Or.inr ⟨rfl, none, by rw [lookupN_eq, Rf, ← hf]; rfl, ?_, hc.2.2.2.1, hc.callee _ ?_ ?_⟩
      all_goals simp only [ResRegsX, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, and_self]
      rfl
  · -- next: the triangular step
    refine triple_of_pointwise fun s₀ hT => ?_
    have hc : CommonX (T, k, D) ra t₀ s₀ := hT.1.1
    have hf := hT.1.2
    have hn := hT.2
    clear hT
    vcgen
    subst_vars
    have hlt := next_lt hc.1.2.2.2 hc.st hf
    have h7 := rv_add1 _ (Nat.lt_trans (Nat.succ_lt_succ hlt) hc.bd.mv)
    simp only [restNX, wadd1] at hf
    simp only [wadd_rv] at hf
    refine Or.inl (Table.ofLabels_at ⟨by decide, ?_⟩)
    simp only [lookupTableX, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, Int64.toBitVec_ofNat,
      BitVec.ofNat_eq_ofNat, BitVec.setWidth_eq, BitVec.add_comm 1#64,
      BitVec.add_comm (_ + 1#64), sub_add1 _ _ h7]
    refine ⟨⟨hc.step _ rfl ?_ ?_, hf⟩, Or.inl (var_find_lt _ _ ?_ ?_)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, and_self]
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, Int64.toBitVec_ofNat,
      BitVec.ofNat_eq_ofNat, BitVec.setWidth_eq, BitVec.add_comm 1#64, h7]
    all_goals first | exact hlt | exact Nat.lt_trans (Nat.succ_lt_succ hlt) hc.bd.mv

  · -- found: the value
    refine triple_of_pointwise fun s₀ hT => ?_
    have hc : CommonX (T, k, D) ra t₀ s₀ := hT.1.1
    obtain ⟨sr, hf, h11⟩ := hT.1.2
    clear hT
    have hvl := hc.val (bandN sr T.cv) Nat.and_le_right
    vcgen
    all_goals
      subst_vars
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, lit8, hc.ld8, Option.some.injEq,
        Option.isSome_some, BitVec.ofInt_natCast, ofNat_toNat64, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_ofNat, BitVec.setWidth_eq, h11] at *
      try subst_vars
      try simp only [BitVec.ofInt_natCast, ofNat_toNat64, Option.isSome_some, hvl,
        Option.some.injEq] at *
      try subst_vars
    case vc3 =>
      simp only [MachineData.retAddr_eq, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      rw [← MachineData.retAddr_eq, hc.retAddr]; rfl
    case vc4 =>
      rename_i ra' hra'
      simp only [MachineData.retAddr_eq, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at hra'
      rw [← MachineData.retAddr_eq, hc.retAddr, Option.some.injEq] at hra'
      subst hra'
      refine Or.inr ⟨rfl, some (T.val (bandN sr T.cv)), by rw [lookupN_eq, Rf, hf]; rfl, ⟨?_, ?_⟩,
        hc.2.2.2.1, hc.callee _ ?_ ?_⟩
      all_goals simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, and_self]
      · rfl
      · rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt (hc.bd.val _)

/-- Non-vacuity: at the sample table `tbl1` with key `5`, the lookup returns
present with value `55`. -/
theorem lookup_tbl1X (hpl : Program.PlacedIn flatLookupX) (D : BitVec 64) (ra : Int64)
    (t : MachineData) (ha : ArgsX 5 D ra t) (hm : tbl1.InMemX D t.dmem) :
    Eventually cenv.instrStep (fun st => st.2 = ra ∧ st.1.regs.get64 .rax = 1
        ∧ (st.1.regs.get64 .rdx).toNat = 55 ∧ st.1.dmem = t.dmem)
      (t, (_root_.Executable.labels cenv).label "flat_lookup") :=
  eventually_weaken _ _ _ _ (fun st ⟨hra, r, hr, hres, hd, _⟩ => by
      rw [tbl1_lookup5] at hr; cases hr; exact ⟨hra, hres.1, hres.2, hd⟩)
    (lookup_specX hpl (tbl1, 5, D) ra t ⟨ha, hm, tbl1_bounded, tbl1_probeEnds⟩)

end Spec

end Kraken.Promising.Lower.Flat
