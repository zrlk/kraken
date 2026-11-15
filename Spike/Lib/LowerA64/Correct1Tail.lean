/-
**The AArch64 compiler theorem on a text with a tail** (untrusted): the
twin of `a64_scc_correctE_text_closedAt1` (`Spike/Lib/LowerA64/Correct1.lean`)
for scc's output with its last cell (the end label) replaced by a tail `T`
(`withTail`), as the granule pass leaves it: only the program changes, so
the output still names the lowering's IR and has a bare tail, and the
proof is `a64_lower_correctE1_of` and `hgen1_ofPlaceOK_of` at the output
with the tail. Nothing about the pre-pass output's layout is used; the
pipeline's success (`hlow`) is a premise.

- `withTail`, `withTail_secs`, `withTail_prog`: an output with its last
  cell replaced by a tail.
- `a64_scc_correctE_text_closedAt1_tail`: at any layout passing `placeOKAt`
  on the output with the tail, closed, on the text.
- `a64_scc_correctE_text_closedAt_tail`: the `Accepted0` statement
  (`immsOf d`) as a corollary, as `a64_scc_correctE_text_closedAt_of1`.
-/
import Spike.Lib.LowerA64.Correct1

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Scc.Sem (Entry)

/-- An output with its end label replaced by the tail `T`. -/
def withTail (o : Scc.Cert.PlaceOK.A64.Out) (T : Program) : Scc.Cert.PlaceOK.A64.Out :=
  { o with prog := o.prog.dropLast ++ T }

/-- The tail leaves the data sections. -/
theorem withTail_secs (o : Scc.Cert.PlaceOK.A64.Out) (T : Program) : (withTail o T).secs = o.secs := rfl

/-- The text with the tail. -/
theorem withTail_prog (o : Scc.Cert.PlaceOK.A64.Out) (T : Program) :
    (withTail o T).prog = o.prog.dropLast ++ T := rfl

section Tail

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {d : Decl}

set_option quotPrecheck false

/-- The lowering's output. -/
local notation "O" => Out.ofEmitted (Scc.Lower.A64.lowerAll cfg [d])

/-- **The AArch64 compiler theorem on a text with a tail, for a main-only
call-free `Accepted1` program, at any layout, closed**: for a program `[d]`
that `scc` accepts (`hd`) and lowers (`hlow`), whose output with its end
label replaced by `T` passes the placement check at `Λ` (`h`) and whose
assembler text `asm` the loader parses to it (`hpa`), `asm` is `Correct`
over `target (kernel 1) E` at every admissible entry state `E`, at `Λ` with
no static label and the lowering's immediates (as
`a64_scc_correctE_text_closedAt1`). -/
theorem a64_scc_correctE_text_closedAt1_tail (Λ : Scc.Sem.Layout) (hd : Scc.Lower.Accepted1 [d] = true)
    (hlow : ∃ em, Scc.Lower.A64.lowerAll? cfg [d] = .ok em) {T : Program}
    (h : placeOKAt pcfg Λ (withTail (O) T) = true) {asm : String}
    (hpa : Scc.Cert.Link.A64.parsesTo asm (withTail (O) T).prog (withTail (O) T).secs = true)
    {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
    Scc.Sem.A64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
      { Λ with static := fun _ => none, imms := Scc.Lower.imms1Of [d] } B asm := by
  have h' : placeOKAt pcfg { Λ with static := fun _ => none } (withTail (O) T) = true :=
    (Scc.Cert.PlaceOK.A64.placeOKAt_static pcfg Λ _ (fun _ => none) Λ.imms).trans h
  obtain ⟨_, hl⟩ := hlow
  intro E hE
  obtain ⟨hp1, hp2⟩ := Scc.Cert.Link.A64.parsed_of_parsesTo hpa
  exact Scc.Sem.A64.correct_of_parsed _ E hp1 hp2
    (a64_lower_correctE1_of hd hl h' (lowerAll_place_ir cfg [d]) (tail_bare_of_accepted1main hd hl)
      (fun _ => rfl) hE (hgen1_ofPlaceOK_of h' E hE))

/-- **The `Accepted0` statement on a text with a tail**:
`a64_scc_correctE_text_closedAt`'s statement for the output with the tail,
from `a64_scc_correctE_text_closedAt1_tail` (as
`a64_scc_correctE_text_closedAt_of1`). -/
theorem a64_scc_correctE_text_closedAt_tail (Λ : Scc.Sem.Layout) (hd : Scc.Lower.Accepted0 [d] = true)
    (hlow : ∃ em, Scc.Lower.A64.lowerAll? cfg [d] = .ok em) {T : Program}
    (h : placeOKAt pcfg Λ (withTail (O) T) = true) {asm : String}
    (hpa : Scc.Cert.Link.A64.parsesTo asm (withTail (O) T).prog (withTail (O) T).secs = true)
    {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
    Scc.Sem.A64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
      { Λ with static := fun _ => none, imms := Spike.Lib.LowerNode.immsOf d } B asm :=
  Spike.Lib.ImmsMono.a64_correctE_imms_mono'
    (Λ := { Λ with static := fun _ => none })
    (a64_scc_correctE_text_closedAt1_tail Λ (Scc.Lower.accepted1_of_accepted0 hd) hlow h hpa)
    fun _ _ _ _ => Spike.Lib.LowerNode.imms1Of_sub_immsOf hd

end Tail

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/--
info: 'Spike.Lib.LowerA64.a64_scc_correctE_text_closedAt1_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.LowerA64.a64_scc_correctE_text_closedAt1_tail

/--
info: 'Spike.Lib.LowerA64.a64_scc_correctE_text_closedAt_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.LowerA64.a64_scc_correctE_text_closedAt_tail
