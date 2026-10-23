/-
**WeakCore-lowerable AArch64 forms with 16-byte units** (`Instr.WCLowerable16`).

`Instr.WCLowerable` (`Lower/Lowerable.lean`) rejects every 64-bit `LDP`/`STP`
(clause 1), because the lowering kit is proved on `isa` and moved to the
FEAT_LSE2 target `isaLSE2` only for texts without them (`Lower/KitLSE2.lean`'s
`hfree`). `Instr.WCLowerable16` is `Instr.WCLowerable` with clause 1 dropped:
a 64-bit `LDP`/`STP` is admitted, as the single-copy-atomic 16-byte access
`isaLSE2` performs at a 16-aligned declared 16-byte location
(`Lower/EventsA64Pair.lean`: `instrSemInf_ldp_lse2`, `instrSemInf_stp_lse2`).
Every other clause is unchanged; in particular `CASP` stays excluded (clause
5: the FEAT_LSE2 environment logic has no rule for it yet), and so do the pair
exclusives.

The alignment and the declared 16-byte location are dynamic, so they are not
part of the predicate: they are the premises of the FEAT_LSE2 rules
(`ldp_lse2_shared`, `stp_lse2_shared`, `Kraken/AArch64/EnvLSE2.lean`).

What this predicate is backed by today: the one-thread route (the FEAT_LSE2
environment logic and `env_link_halt_lse2`, `Promising/EnvLSE2AArch64.lean`),
as in `AArch64/Examples/EnvLSE2Lowered.lean`. The multi-thread lowering kit
for `isaLSE2` with declared 16-byte locations is not built (`Lower/README.md`,
"16-byte units on AArch64: remaining work"); a lowered text that needs the
kit must still be `Program.WCLowerable`.

Acquire and release pairs: Kraken has no `LDIAPP`/`STILP`. A WeakCore acquire
pair load lowers to `ldp` then `dmb ishld`, a release pair store to `dmb ish`
then `stp` (litmus: `corpus/lowering/aarch64/lse2/`).

- `Instr.WCLowerable.to16`, `Program.WCLowerable.to16`: every lowerable form
  is a 16-byte lowerable form;
- `Instr.WCLowerable16.toWC`, `Program.WCLowerable16.toWC`: a 16-byte
  lowerable form without a FEAT_LSE2 reading (`LSE2Free`) is lowerable.
-/
import Kraken.Promising.Lower.Lowerable

/-- **`Instr.wcLowerable16B i`**: `Instr.wcLowerableB` with 64-bit
`LDP`/`STP` admitted. -/
def Instr.wcLowerable16B : Instr → Bool
  | ⟨.W64, .LDP ..⟩ => true
  | ⟨.W64, .STP ..⟩ => true
  | i => i.wcLowerableB

/-- **WeakCore-lowerable instruction with 16-byte units.** -/
def Instr.WCLowerable16 (i : Instr) : Prop := i.wcLowerable16B = true

instance (i : Instr) : Decidable i.WCLowerable16 := inferInstanceAs (Decidable (_ = true))

/-- A cell's lowerability with 16-byte units; labels and byte arrays are
lowerable. -/
def Directive.wcLowerable16B : Directive → Bool
  | .instr i => i.wcLowerable16B
  | _ => true

/-- **WeakCore-lowerable cell with 16-byte units.** -/
def Directive.WCLowerable16 (d : Directive) : Prop := d.wcLowerable16B = true

instance (d : Directive) : Decidable d.WCLowerable16 := inferInstanceAs (Decidable (_ = true))

/-- **WeakCore-lowerable program with 16-byte units**: every cell is. -/
def Program.WCLowerable16 (p : Program) : Prop := ∀ d ∈ p, d.WCLowerable16

instance (p : Program) : Decidable p.WCLowerable16 :=
  inferInstanceAs (Decidable (∀ d ∈ p, d.WCLowerable16))

theorem Directive.wcLowerable16_instr {i : Instr} : (Directive.instr i).WCLowerable16 ↔ i.WCLowerable16 :=
  Iff.rfl

theorem Program.wcLowerable16_append {p q : Program} :
    (p ++ q).WCLowerable16 ↔ p.WCLowerable16 ∧ q.WCLowerable16 := by
  simp only [Program.WCLowerable16, List.mem_append]
  exact ⟨fun h => ⟨fun d hd => h d (.inl hd), fun d hd => h d (.inr hd)⟩,
    fun h d hd => hd.elim (h.1 d) (h.2 d)⟩

/-! ## Relation to `WCLowerable` -/

/-- **Every lowerable instruction is lowerable with 16-byte units.** -/
theorem Instr.WCLowerable.to16 {i : Instr} (h : i.WCLowerable) : i.WCLowerable16 := by
  unfold Instr.WCLowerable16 Instr.wcLowerable16B
  split
  · rfl
  · rfl
  · exact h

theorem Directive.WCLowerable.to16 {d : Directive} (h : d.WCLowerable) : d.WCLowerable16 := by
  cases d with
  | instr i => exact Instr.WCLowerable.to16 h
  | _ => rfl

theorem Program.WCLowerable.to16 {p : Program} (h : p.WCLowerable) : p.WCLowerable16 :=
  fun d hd => (h d hd).to16

/-- **A 16-byte lowerable instruction without a FEAT_LSE2 reading is
lowerable**: the two predicates differ exactly at 64-bit `LDP`/`STP`. -/
theorem Instr.WCLowerable16.toWC {i : Instr} (h : i.WCLowerable16) (hf : (Directive.instr i).LSE2Free) :
    i.WCLowerable := by
  revert h hf
  unfold Instr.WCLowerable16 Instr.wcLowerable16B
  split
  · intro _ hf; exact hf.elim
  · intro _ hf; exact hf.elim
  · intro h _; exact h

theorem Directive.WCLowerable16.toWC {d : Directive} (h : d.WCLowerable16) (hf : d.LSE2Free) :
    d.WCLowerable := by
  cases d with
  | instr i => exact Instr.WCLowerable16.toWC h hf
  | _ => rfl

theorem Program.WCLowerable16.toWC {p : Program} (h : p.WCLowerable16) (hf : ∀ d ∈ p, d.LSE2Free) :
    p.WCLowerable :=
  fun d hd => (h d hd).toWC (hf d hd)

/-! ## Tests -/

section Tests
open Kraken.AArch64.Parser

-- The 64-bit pairs and the lowering's acquire/release pair forms are admitted.
/-- info: [true, true, true, true, true, true, true] -/
#guard_msgs in
#eval (parseAArch64("
    ldp x1, x2, [x0]
    stp x1, x2, [x0]
    ldp x1, x2, [x0, #16]
    stp x1, x2, [x0, #-16]!
    dmb ish
    dmb ishld
    ldp w1, w2, [x0]
") : Program).map Directive.wcLowerable16B

-- Every other clause still rejects its forms, `CASP` and the pair exclusives included.
/-- info: [false, false, false, false, false, false, false, false, false, false, false, false] -/
#guard_msgs in
#eval (parseAArch64("
    casp x2, x3, x4, x5, [x0]
    caspal x2, x3, x4, x5, [x0]
    ldxp x1, x2, [x0]
    stxp w3, x1, x2, [x0]
    cas x3, x1, [x0]
    casl x3, x1, [x0]
    casal xzr, x1, [x0]
    swpal x1, xzr, [x0]
    stadd x1, [x0]
    ldapr x1, [x0]
    strb w1, [x0]
    stlrh w1, [x0]
") : Program).map Directive.wcLowerable16B

example : Program.WCLowerable16 parseAArch64("
    dmb ish
    stp x1, x2, [x0]
    ldp x3, x4, [x0]
    dmb ishld
") := by decide

example : ¬ Program.WCLowerable parseAArch64("
    stp x1, x2, [x0]
") := by decide

end Tests
