/-
**A constant into a register** (AArch64), for any constant: the emitter's
`movImm d n` (`Scc/Emit/A64.lean`) is covered by the block lemma and puts
`n` modulo `2^64` in `xd`.

`movImm d n` emits one `movz` of the lowest non-zero halfword of `n mod
2^64` (or `movz xd, #0`) and one `movk` per other non-zero halfword. Each
`movk` replaces one halfword; over the halfwords in increasing order the
register holds `n mod 2^(16(k+1))` after halfword `k` (`mkStep_eq`), and a
zero halfword needs no instruction (`mod_succ_of_zero`).

- `movDs d hs`: the directives for the filtered halfword list `hs`;
  `directives_movImm`: `movImm d n` is `movDs` of its non-zero halfwords;
- `okBlk_movImm`: the instructions are covered register operations that
  forget `xd`'s static offset and nothing else;
- `arun_movImm`: the abstract run: the pc past the instructions, `xd`
  forgotten in the static offsets, `xd := BitVec.ofInt 64 n`, the rest of
  the state unchanged.
-/
import Spike.Lib.A64Ret
import Scc.Emit.A64
import Kraken.AArch64.Parser

namespace Spike.Lib.LowerA64

open Kraken Kraken.AArch64.Parser Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 (movImm halfwords movShiftOf xz i64 ins directives)

set_option linter.unusedSimpArgs false

/-! ## One halfword -/

/-- **One `movk`**: halfword `k` of `x` replaced by `h`. -/
def mkStep (x : BitVec 64) (p : Nat × Nat) : BitVec 64 :=
  (x &&& ~~~(0xFFFF#64 <<< (16 * p.2))) ||| (BitVec.ofNat 64 p.1 <<< (16 * p.2))

theorem ofNat_getElem (x i : Nat) (hi : i < 64) : (BitVec.ofNat 64 x)[i] = x.testBit i := by
  rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat, Nat.testBit_mod_two_pow]; simp [hi]

/-- Replacing halfword `K` of `v mod 2^(16K)` by `v`'s gives `v mod
2^(16(K+1))`. -/
theorem mkStep_eq (v K : Nat) :
    mkStep (BitVec.ofNat 64 (v % 2 ^ (16 * K))) ((v >>> (16 * K)) % 65536, K) =
      BitVec.ofNat 64 (v % 2 ^ (16 * (K + 1))) := by
  unfold mkStep
  rw [show (0xFFFF#64) = BitVec.ofNat 64 (2^16 - 1) from rfl, show (65536 : Nat) = 2 ^ 16 from rfl]
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not, BitVec.getElem_shiftLeft,
    ofNat_getElem _ _ hi, ofNat_getElem _ _ (show i - 16 * K < 64 by omega),
    Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  by_cases h1 : i < 16 * K
  · have : i < 16 * (K + 1) := by omega
    simp [h1, this]
  · have : 16 * K + (i - 16 * K) = i := by omega
    simp only [h1, this, decide_false, Bool.not_false, Bool.true_and, Bool.false_and, Bool.false_or]
    by_cases h2 : i < 16 * (K + 1)
    · have : i - 16 * K < 16 := by omega
      simp [h2, this]
    · have : ¬ i - 16 * K < 16 := by omega
      simp [h2, this]

/-- A zero halfword `K` adds nothing to `v mod 2^(16K)`. -/
theorem mod_succ_of_zero (v K : Nat) (h : (v >>> (16 * K)) % 65536 = 0) :
    v % 2 ^ (16 * (K + 1)) = v % 2 ^ (16 * K) := by
  rw [show 16 * (K + 1) = 16 * K + 16 by omega, Nat.pow_add, Nat.mod_mul, ← Nat.shiftRight_eq_div_pow,
    show (2 : Nat) ^ 16 = 65536 from rfl, h]
  simp

theorem imm16 {h : Nat} (hh : h < 65536) :
    BitVec.ofInt 64 ((h : Int).bmod Int64.size) &&& 65535#64 = BitVec.ofNat 64 h := by
  rw [Int.bmod_eq_of_le (by simp [Int64.size]) (by simp [Int64.size]; omega), BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, show (65535#64).toNat = 2 ^ 16 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  simp; omega

theorem movShiftOf_toNat {k : Nat} (hk : k < 4) : (movShiftOf k).toNat = 16 * k := by
  rcases k with _ | _ | _ | _ | k <;> simp [movShiftOf] <;> omega

/-- `movk xd, #h, lsl #16k`. -/
def movkD (d : XReg) (p : Nat × Nat) : Directive := .instr ⟨.W64, .MOVK (xz d) (i64 p.1) (movShiftOf p.2)⟩

/-- `movz xd, #h, lsl #16k`. -/
def movzD (d : XReg) (p : Nat × Nat) : Directive := .instr ⟨.W64, .MOVZ (xz d) (i64 p.1) (movShiftOf p.2)⟩

theorem dstep_movk (lab : Label → Int64) (pc : Int64) (o : SO) (σ : AS) (d : XReg) {h k : Nat}
    (hh : h < 65536) (hk : k < 4) :
    dstep lab ⟨pc, o, σ⟩ (movkD d (h, k)) =
      ⟨pc + Int64.ofNat 4, o.kill d,
        { σ with regs := σ.regs.setXReg d (mkStep (σ.regs.getXReg d).toBitVec (h, k)) }⟩ := by
  simp [movkD, dstep, classify, RegOnly, AI.tgt, AI.so, soReg, regDst, zrB, SO.write, AI.step, regRes,
    Operation.interp, MachineData.setRegOrZr, Reg64s.setRegOrZr, Reg64s.setRegOrZr64, ConstExpr.interp, xz, i64,
    imm16 hh, movShiftOf_toNat hk, mkStep]

theorem dstep_movz (lab : Label → Int64) (pc : Int64) (o : SO) (σ : AS) (d : XReg) {h k : Nat}
    (hh : h < 65536) (hk : k < 4) :
    dstep lab ⟨pc, o, σ⟩ (movzD d (h, k)) =
      ⟨pc + Int64.ofNat 4, o.kill d, { σ with regs := σ.regs.setXReg d (mkStep 0 (h, k)) }⟩ := by
  simp [movzD, dstep, classify, RegOnly, AI.tgt, AI.so, soReg, regDst, zrB, SO.write, AI.step, regRes,
    Operation.interp, MachineData.setRegOrZr, Reg64s.setRegOrZr, Reg64s.setRegOrZr64, ConstExpr.interp, xz, i64,
    imm16 hh, movShiftOf_toNat hk, mkStep]

/-! ## The instruction list -/

/-- **The directives of `movImm`** for its non-zero halfwords `hs` (each
`(h, k)`: halfword `k` is `h`). -/
def movDs (d : XReg) : List (Nat × Nat) → List Directive
  | [] => [movzD d (0, 0)]
  | p :: rest => movzD d p :: rest.map (movkD d)

/-- The non-zero halfwords of `v`, each with its index from `j`. -/
def nzHw (L : List Nat) (j : Nat) : List (Nat × Nat) := (L.zipIdx j).filter fun p => p.1 != 0

theorem directives_movImm (d : XReg) (n : Int) :
    directives (movImm d n) = movDs d (nzHw (halfwords (n % 18446744073709551616).toNat) 0) := by
  unfold movImm nzHw
  dsimp only
  split <;> rename_i h
  · rw [h]; rfl
  · rw [h]; simp [directives, movDs, ins, movzD, movkD, List.filterMap_map, Function.comp_def]

theorem rm_rm {ρ : Type} [DecidableEq ρ] (l : List (ρ × Int)) (r : ρ) : rm (rm l r) r = rm l r := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨a, k⟩ := e
    by_cases h : a = r <;> simp [rm, h, ih]

theorem SO.kill_kill (o : SO) (x : XReg) : (o.kill x).kill x = o.kill x := by
  simp [SO.kill, rm_rm]

/-! ## Coverage -/

theorem okBlk_movk {lo hi : Int} {o : SO} {d : XReg} (p : Nat × Nat) {ds : List Directive} :
    okBlk lo hi o (movkD d p :: ds) = okBlk lo hi (o.kill d) ds := by
  simp [movkD, okBlk, classify, RegOnly, AI.ok, AI.so, AI.isTerm, soReg, regDst, zrB, SO.write, xz, i64]

theorem okBlk_movz {lo hi : Int} {o : SO} {d : XReg} (p : Nat × Nat) {ds : List Directive} :
    okBlk lo hi o (movzD d p :: ds) = okBlk lo hi (o.kill d) ds := by
  simp [movzD, okBlk, classify, RegOnly, AI.ok, AI.so, AI.isTerm, soReg, regDst, zrB, SO.write, xz, i64]

theorem okBlk_movks {lo hi : Int} {o : SO} {d : XReg} (ho : o.kill d = o) (ps : List (Nat × Nat))
    {ds : List Directive} : okBlk lo hi o (ps.map (movkD d) ++ ds) = okBlk lo hi o ds := by
  induction ps with
  | nil => rfl
  | cons p ps ih => rw [List.map_cons, List.cons_append, okBlk_movk, ho, ih]

theorem okBlk_movDs {lo hi : Int} {o : SO} {d : XReg} (hs : List (Nat × Nat)) {ds : List Directive} :
    okBlk lo hi o (movDs d hs ++ ds) = okBlk lo hi (o.kill d) ds := by
  cases hs with
  | nil => exact okBlk_movz _
  | cons p ps => rw [movDs, List.cons_append, okBlk_movz, okBlk_movks (SO.kill_kill o d)]

/-- **`movImm` is covered**: it only forgets `xd`'s static offset. -/
theorem okBlk_movImm {lo hi : Int} {o : SO} (d : XReg) (n : Int) {ds : List Directive} :
    okBlk lo hi o (directives (movImm d n) ++ ds) = okBlk lo hi (o.kill d) ds := by
  rw [directives_movImm, okBlk_movDs]

/-! ## The run -/

theorem arun_movks (lab : Label → Int64) (d : XReg) (v : Nat) :
    ∀ (L : List Nat) (j : Nat) (pc : Int64) (o : SO) (σ : AS),
    (∀ i (h : i < L.length), L[i] = (v >>> (16 * (j + i))) % 65536) → j + L.length ≤ 4 → o.kill d = o →
    (σ.regs.getXReg d).toBitVec = BitVec.ofNat 64 (v % 2 ^ (16 * j)) →
    arun lab ((nzHw L j).map (movkD d)) ⟨pc, o, σ⟩ =
      ⟨pc + Int64.ofNat (4 * (nzHw L j).length), o,
        { σ with regs := σ.regs.setXReg d (BitVec.ofNat 64 (v % 2 ^ (16 * (j + L.length)))) }⟩
  | [], j, pc, o, σ, _, _, _, hd => by
    simp only [nzHw, List.zipIdx_nil, List.filter_nil, List.map_nil, List.length_nil, Nat.mul_zero,
      Nat.add_zero, arun, List.foldl_nil]
    rw [← hd, Reg64s.setXReg_getXReg]
    simp
  | h :: L, j, pc, o, σ, hL, hj, ho, hd => by
    have h0 := hL 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at h0
    have hL' : ∀ i (hi : i < L.length), L[i] = (v >>> (16 * (j + 1 + i))) % 65536 := fun i hi => by
      have := hL (i + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      rw [this]; congr 3; omega
    have hlen : j + 1 + L.length = j + (h :: L).length := by simp; omega
    by_cases hz : h = 0
    · subst hz
      have := arun_movks lab d v L (j + 1) pc o σ hL' (by simp at hj; omega) ho
        (by rw [hd, mod_succ_of_zero v j h0.symm])
      simpa [nzHw, List.zipIdx_cons, hlen] using this
    · have hh : h < 65536 := by rw [h0]; exact Nat.mod_lt _ (by omega)
      have hstep : nzHw (h :: L) j = (h, j) :: nzHw L (j + 1) := by simp [nzHw, hz]
      rw [hstep, List.map_cons, arun, List.foldl_cons, dstep_movk lab pc o σ d hh (by simp at hj; omega), ho]
      have := arun_movks lab d v L (j + 1) (pc + Int64.ofNat 4) o
        { σ with regs := σ.regs.setXReg d (mkStep (σ.regs.getXReg d).toBitVec (h, j)) } hL'
        (by simp at hj; omega) ho (by simp [hd, h0, mkStep_eq])
      simp only [arun] at this
      rw [this]
      simp only [Reg64s.setXReg_setXReg, hlen, List.length_cons, AM.mk.injEq, and_true]
      rw [Int64.add_assoc, ← Int64.ofNat_add]
      congr 2
      omega

theorem arun_movDs (lab : Label → Int64) (d : XReg) (v : Nat) :
    ∀ (L : List Nat) (j : Nat) (pc : Int64) (o : SO) (σ : AS),
    (∀ i (h : i < L.length), L[i] = (v >>> (16 * (j + i))) % 65536) → j + L.length ≤ 4 →
    v % 2 ^ (16 * j) = 0 →
    arun lab (movDs d (nzHw L j)) ⟨pc, o, σ⟩ =
      ⟨pc + Int64.ofNat (4 * (movDs d (nzHw L j)).length), o.kill d,
        { σ with regs := σ.regs.setXReg d (BitVec.ofNat 64 (v % 2 ^ (16 * (j + L.length)))) }⟩
  | [], j, pc, o, σ, _, _, hv => by
    simp only [nzHw, List.zipIdx_nil, List.filter_nil, movDs, arun, List.foldl_cons, List.foldl_nil,
      List.length_cons, List.length_nil, List.length_nil, Nat.add_zero]
    rw [dstep_movz lab pc o σ d (by omega) (by omega), hv]
    simp [mkStep]
  | h :: L, j, pc, o, σ, hL, hj, hv => by
    have h0 := hL 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at h0
    have hL' : ∀ i (hi : i < L.length), L[i] = (v >>> (16 * (j + 1 + i))) % 65536 := fun i hi => by
      have := hL (i + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      rw [this]; congr 3; omega
    have hlen : j + 1 + L.length = j + (h :: L).length := by simp; omega
    by_cases hz : h = 0
    · subst hz
      have := arun_movDs lab d v L (j + 1) pc o σ hL' (by simp at hj; omega)
        (by rw [mod_succ_of_zero v j h0.symm, hv])
      simpa [nzHw, List.zipIdx_cons, hlen] using this
    · have hh : h < 65536 := by rw [h0]; exact Nat.mod_lt _ (by omega)
      have hstep : nzHw (h :: L) j = (h, j) :: nzHw L (j + 1) := by simp [nzHw, hz]
      rw [hstep, movDs, arun, List.foldl_cons, dstep_movz lab pc o σ d hh (by simp at hj; omega)]
      have hm : mkStep 0#64 (h, j) = BitVec.ofNat 64 (v % 2 ^ (16 * (j + 1))) := by
        rw [← mkStep_eq, hv, h0]
      have := arun_movks lab d v L (j + 1) (pc + Int64.ofNat 4) (o.kill d)
        { σ with regs := σ.regs.setXReg d (mkStep 0 (h, j)) } hL'
        (by simp at hj; omega) (SO.kill_kill o d) (by simp [hm])
      simp only [arun] at this
      rw [this]
      simp only [Reg64s.setXReg_setXReg, hlen, List.length_cons, List.length_map, AM.mk.injEq, and_true]
      rw [Int64.add_assoc, ← Int64.ofNat_add]
      congr 2
      omega

theorem halfwords_spec (v : Nat) :
    ∀ i (h : i < (halfwords v).length), (halfwords v)[i] = (v >>> (16 * (0 + i))) % 65536 := by
  intro i h
  simp [halfwords]

/-- **The run of `movImm d n`**: `xd` holds `n` modulo `2^64` and is
forgotten in the static offsets; the pc moves past the instructions; the
rest of the state is unchanged. -/
theorem arun_movImm (lab : Label → Int64) (pc : Int64) (o : SO) (σ : AS) (d : XReg) (n : Int) :
    arun lab (directives (movImm d n)) ⟨pc, o, σ⟩ =
      ⟨pc + Int64.ofNat (4 * (directives (movImm d n)).length), o.kill d,
        { σ with regs := σ.regs.setXReg d (BitVec.ofInt 64 n) }⟩ := by
  rw [directives_movImm]
  have hv : (n % 18446744073709551616).toNat < 2 ^ 64 := by omega
  rw [arun_movDs lab d _ _ 0 pc o σ (halfwords_spec _) (by simp [halfwords]) (by simp [Nat.mod_one])]
  simp only [halfwords, List.length_map, List.length_range, Nat.zero_add,
    Nat.mod_eq_of_lt (show _ < 2 ^ (16 * 4) from hv), AM.mk.injEq, true_and]
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofInt]
  omega

/-- **A 16-bit constant is one `movz`**, the return block's immediate word
(`RW.imm`). -/
theorem directives_movImm_small (d : XReg) {n : Nat} (hn : n < 65536) :
    directives (movImm d n) = [RW.dir d (.imm (Int64.ofInt n))] := by
  rw [directives_movImm]
  have h1 : ((n : Int) % 18446744073709551616).toNat = n := by omega
  have hs : ∀ k, 0 < k → n >>> (16 * k) = 0 := fun k hk => by
    rw [Nat.shiftRight_eq_div_pow]; apply Nat.div_eq_of_lt
    calc n < 2 ^ 16 := hn
      _ ≤ 2 ^ (16 * k) := Nat.pow_le_pow_right (by omega) (by omega)
  rw [h1]
  by_cases h0 : n = 0
  · subst h0; rfl
  · simp [halfwords, nzHw, List.range_succ, hs, h0, Nat.mod_eq_of_lt hn, movDs, movzD, RW.dir, movShiftOf, xz, i64]
    exact ⟨by rw [show n >>> 16 = 0 by simpa using hs 1 (by omega)],
      by rw [show n >>> 32 = 0 by simpa using hs 2 (by omega)],
      by rw [show n >>> 48 = 0 by simpa using hs 3 (by omega)]⟩

/-- `movImm` against Kraken's parser: one `movz`, or `movz` and `movk`s. -/
example : directives (movImm .X9 40) = parseAArch64("movz x9, #40") := by decide
example : directives (movImm .X9 0x10000002A) = parseAArch64("movz x9, #42
movk x9, #1, lsl #32") := by decide
example : directives (movImm .X9 (-1)) = parseAArch64("movz x9, #65535
movk x9, #65535, lsl #16
movk x9, #65535, lsl #32
movk x9, #65535, lsl #48") := by decide

end Spike.Lib.LowerA64
