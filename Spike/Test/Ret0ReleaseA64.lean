import Spike.Lib.LowerA64.Correct
import Spike.Test.Cert.A64Ret0Cert

/-!
# Release theorem: `ret0.w` on AArch64

`scc` compiles `Scc/Test/ret0.w` (`main` returns `40 + 2`) to the assembler
text `SccCertificate.asm`. The theorem below says that this text is correct
(`Scc.Sem.A64.CorrectE`) with respect to the source semantics of the
program, on the kernel-model AArch64 target `Scc.Sem.A64.target (kernel 1) E`
(one thread slot) for each entry state `E`, at **every** admissible entry
state (any initial stack that `Scc.Sem.Entry.Ok` admits, not only
Linux's), at **any** layout `Λ` at which the output passes the placement
check (`placeOKAt`; `Λ` read off the linked executable, say), with no
static label and the lowering's immediates. The placement check reads
neither field (`placeOKAt_static`); a program in the fragment (`Accepted0`)
allocates no static label, and `imms` is the proof's table of constants
folded into instructions, not an input of the loader
nor of anything `Correct` fixes outside the witness.

If the program exits, it exits as the source does; the theorem does not
promise that it exits. `Correct` is a safety and refinement statement:
every finite observable trace of the target, including one that ends in
exit, is a trace of the source; a target that diverges or blocks before
exiting satisfies it.

The hypotheses are `h`, the placement check at `Λ`, and `hpa`: the loader's
parse of the text is the program the certificate checked. The certificate
establishes `hpa` with a compiled `#guard`
(`Spike/Test/Cert/A64Ret0Cert.lean`); the kernel cannot replay it because
the assembler parser has `partial` definitions, which the kernel does not
unfold. That `#guard` is the trust boundary. At the certificate's own
layout (`tablesOf placeCfg out`) the certificate proves `h`
(`prog_placeOK`): `ret0_correct_tables`. Everything else (acceptance and
the runtime's obligations) is proved.
-/

namespace Spike.Test.Ret0ReleaseA64

open SccCertificate (asm out prog_src config placeCfg prog_accepted prog_placeOK)

/-- `ret0.w`'s one declaration, `main`. -/
abbrev main : CoreTerm.Decl := prog_src.head (by decide)

/-- **`ret0.w` compiled for AArch64 is correct at every admissible entry
state**, at any layout `Λ` passing the placement check, for every budget
`B` and memory model `arch`. -/
theorem ret0_correct (Λ : Scc.Sem.Layout) (B : Scc.Sem.Budget) (arch : WeakMem.Arch)
    (h : Scc.Cert.PlaceOK.A64.placeOKAt placeCfg Λ out = true)
    (hpa : Scc.Cert.Link.A64.parsesTo asm out.prog out.secs = true) :
    Scc.Sem.A64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) prog_src)
      { Λ with static := fun _ => none, imms := Spike.Lib.LowerNode.immsOf main } B asm :=
  Spike.Lib.LowerA64.a64_scc_correctE_text_closedAt (cfg := config) Λ prog_accepted h hpa

/-- **At the certificate's layout** (`tablesOf placeCfg out`), where the
certificate proves the placement check (`prog_placeOK`). -/
theorem ret0_correct_tables (B : Scc.Sem.Budget) (arch : WeakMem.Arch)
    (hpa : Scc.Cert.Link.A64.parsesTo asm out.prog out.secs = true) :
    Scc.Sem.A64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) prog_src)
      { (Scc.Cert.PlaceOK.A64.tablesOf placeCfg out).Λ with
        static := fun _ => none, imms := Spike.Lib.LowerNode.immsOf main } B asm :=
  ret0_correct _ B arch (Scc.Cert.PlaceOK.A64.atTables prog_placeOK) hpa

/-- **The entry quantifier is not vacuous**: at any layout passing the
placement check, the 64 KiB stack at `2 ^ 32` is admissible. -/
theorem ok_witness_of_placeOKAt {Λ : Scc.Sem.Layout}
    (h : Scc.Cert.PlaceOK.A64.placeOKAt placeCfg Λ out = true) :
    Scc.Sem.Entry.Ok ⟨⟨2 ^ 32, 65536⟩⟩
      { Λ with static := fun _ => none, imms := Spike.Lib.LowerNode.immsOf main } :=
  Scc.Sem.Entry.ok_witness (Scc.Cert.PlaceOK.A64.below32_of_placeOKAt h)

/--
info: 'Spike.Test.Ret0ReleaseA64.ret0_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ret0_correct

/--
info: 'Spike.Test.Ret0ReleaseA64.ret0_correct_tables' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ret0_correct_tables

/--
info: 'Spike.Test.Ret0ReleaseA64.ok_witness_of_placeOKAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ok_witness_of_placeOKAt

end Spike.Test.Ret0ReleaseA64
