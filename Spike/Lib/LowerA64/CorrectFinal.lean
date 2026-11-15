/-
**The AArch64 compiler theorem on the post-pass text** (untrusted): the
twin of `a64_scc_correctE_text_closedAt1` (`Spike/Lib/LowerA64/Correct1.lean`)
for the output after the granule pass, `ofFinal st final`
(`Scc/Cert/GranuleOutA64.lean`), in place of scc's output `Out.ofEmitted
(lowerAll cfg [d])`.

A certificate of a program built with the pass decides the stages of the
lowering and the emitter (`h1`, `h2`, as for the pre-pass output), the pass
check (`hc`: the post-pass items `Expand` the emitter's) and the post-pass
block table (`hb`) on literals, and `placeOKAt` and the loader's parse
(`hpa`) on the post-pass output itself. Nothing about the pre-pass layout is
transferred: the composition is `a64_lower_correctE1_of` and
`hgen1_ofPlaceOK_of` at the post-pass output, whose IR and tail are scc's
(`ofFinal_of_stages`: only the program and the block table differ;
`lowerAll_place_ir`, `tail_bare_of_accepted1main`).

- `lowerAll?_ok_of_stages`: the pipeline succeeds where its stages do.
- `ofFinal_place_ir`, `ofFinal_tail_bare1`: the post-pass output names the
  lowering's IR and has a bare tail.
- `a64_scc_correctE_closedAt1_final`, `a64_scc_correctE_text_closedAt1_final`:
  at any layout passing `placeOKAt` on the post-pass output, closed; the
  latter on the text.
-/
import Spike.Lib.LowerA64.Correct1
import Scc.Cert.GranuleOutA64

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib.A64Consumer (TParE)
open Scc.Sem (Entry)

section CorrectFinal

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {d : Decl}

set_option quotPrecheck false

set_option hygiene false in
/-- The post-pass output: the stage `(ir, items, sps, tbl, need, setup)` with the
pass's items `final`. -/
local notation "F" => Scc.Cert.Granule.A64.ofFinal (ir, items, sps, tbl, (Scc.Lower.stackNeed .arm ir).toOption, setup)
  final

/-- **The pipeline succeeds where its stages do**: the lowering gives `ir`
(`h1`) and the emitter succeeds on it (`h2`). -/
theorem lowerAll?_ok_of_stages {p : Prog} {ir : Scc.IR.Program} {setup : Bool}
    {items : List Scc.Emit.A64.Item} {sps : List Scc.Emit.A64.Safepoint}
    (h1 : lowered1 cfg p = some (ir, setup)) (h2 : Scc.Emit.A64.emitItemsMaps ir = .ok (items, sps)) :
    ∃ em, Scc.Lower.A64.lowerAll? cfg p = .ok em := by
  unfold lowered1 at h1
  split at h1
  · rename_i l hl
    cases h1
    exact ⟨_, by simp only [Scc.Lower.A64.lowerAll?, hl, bind, Except.bind, Scc.Lower.A64.emitAll, h2]; rfl⟩
  · cases h1

/-- **The post-pass output names the lowering's IR** (`ofFinal_of_stages`:
only the program and the block table differ from scc's output). -/
theorem ofFinal_place_ir {p : Prog} {ir : Scc.IR.Program} {setup : Bool}
    {items final tits : List Scc.Emit.A64.Item} {sps : List Scc.Emit.A64.Safepoint} {blks : List Scc.Cert.Rt.A64.OGrp}
    {tbl : List Kraken.DataImage.Item}
    (h1 : lowered1 cfg p = some (ir, setup)) (h2 : Scc.Emit.A64.emitItemsMaps ir = .ok (items, sps))
    (h3 : Scc.Lower.A64.tablesOf ir items cfg.gcWit = .ok (tits, tbl))
    (hc : Scc.Cert.Granule.A64.check final items = true)
    (hb : Scc.Cert.Granule.A64.blocksOfFinal ir final = some blks) :
    (Scc.Cert.Granule.A64.ofFinal (ir, items, sps, tbl, (Scc.Lower.stackNeed .arm ir).toOption, setup) final).place.ir =
      some (Scc.Lower.A64.lowerAll cfg p).low.ir := by
  rw [(Scc.Cert.Granule.A64.ofFinal_of_stages h1 h2 h3 hc hb).1]
  exact lowerAll_place_ir cfg p

/-- **The post-pass output of a main-only call-free `Accepted1` program has a
bare tail** (scc's: `tail_bare_of_accepted1main`). -/
theorem ofFinal_tail_bare1 (hd : Scc.Lower.Accepted1 [d] = true) {ir : Scc.IR.Program} {setup : Bool}
    {items final tits : List Scc.Emit.A64.Item} {sps : List Scc.Emit.A64.Safepoint} {blks : List Scc.Cert.Rt.A64.OGrp}
    {tbl : List Kraken.DataImage.Item}
    (h1 : lowered1 cfg [d] = some (ir, setup)) (h2 : Scc.Emit.A64.emitItemsMaps ir = .ok (items, sps))
    (h3 : Scc.Lower.A64.tablesOf ir items cfg.gcWit = .ok (tits, tbl))
    (hc : Scc.Cert.Granule.A64.check final items = true)
    (hb : Scc.Cert.Granule.A64.blocksOfFinal ir final = some blks) :
    (F).place.tail = .bare := by
  have ⟨_, hlow⟩ := lowerAll?_ok_of_stages h1 h2
  rw [(Scc.Cert.Granule.A64.ofFinal_of_stages h1 h2 h3 hc hb).1]
  exact tail_bare_of_accepted1main hd hlow

/-- **The AArch64 compiler theorem for a main-only call-free `Accepted1`
program after the granule pass, at any layout, closed**: for a program `[d]`
that `scc` accepts (`hd`), whose lowering and emission give `ir`, `items`
and `sps` (`h1`, `h2`), whose post-pass items `final` pass the check (`hc`)
with the block table `blks` (`hb`), and whose post-pass output passes the
placement check at a layout `Λ` (`h`), the post-pass output is `Correct`
over the kernel-model target `target (kernel 1) E` on parsed texts at every
admissible entry state `E`, at `Λ` with no static label and the lowering's
immediates (as `a64_scc_correctE_closedAt1`). -/
theorem a64_scc_correctE_closedAt1_final (Λ : Scc.Sem.Layout) (hd : Scc.Lower.Accepted1 [d] = true)
    {ir : Scc.IR.Program} {setup : Bool} {items final tits : List Scc.Emit.A64.Item}
    {sps : List Scc.Emit.A64.Safepoint} {blks : List Scc.Cert.Rt.A64.OGrp} {tbl : List Kraken.DataImage.Item}
    (h1 : lowered1 cfg [d] = some (ir, setup)) (h2 : Scc.Emit.A64.emitItemsMaps ir = .ok (items, sps))
    (h3 : Scc.Lower.A64.tablesOf ir items cfg.gcWit = .ok (tits, tbl))
    (hc : Scc.Cert.Granule.A64.check final items = true)
    (hb : Scc.Cert.Granule.A64.blocksOfFinal ir final = some blks)
    (h : placeOKAt pcfg Λ (F) = true) {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
    ∀ E : Entry, E.Ok { Λ with static := fun _ => none, imms := Scc.Lower.imms1Of [d] } →
      Scc.Sem.Correct (TParE E) (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
        { Λ with static := fun _ => none, imms := Scc.Lower.imms1Of [d] } B ((F).prog, (F).secs) :=
  have h' : placeOKAt pcfg { Λ with static := fun _ => none } (F) = true :=
    (Scc.Cert.PlaceOK.A64.placeOKAt_static pcfg Λ (F) (fun _ => none) Λ.imms).trans h
  fun E hE =>
    have ⟨_, hlow⟩ := lowerAll?_ok_of_stages h1 h2
    a64_lower_correctE1_of hd hlow h' (ofFinal_place_ir h1 h2 h3 hc hb) (ofFinal_tail_bare1 hd h1 h2 h3 hc hb)
      (fun _ => rfl) hE (hgen1_ofPlaceOK_of h' E hE)

/-- **The AArch64 compiler theorem on the post-pass text for a main-only
call-free `Accepted1` program, at any layout, closed**
(`Scc.Sem.A64.CorrectE`): `a64_scc_correctE_text_closedAt1` with the
post-pass output in place of scc's, given its stages (`h1`, `h2`), the pass
check (`hc`) and the post-pass block table (`hb`). The assembler text `asm`
the loader parses to the post-pass output (`hpa`, the certificate's compiled
`#guard`, the trust boundary) is `Correct` over the kernel-model target
`target (kernel 1) E` at every admissible entry state `E`, at `Λ` with no
static label and the lowering's immediates.

If the program exits, it exits as the source does; the theorem does not
promise that it exits. `Correct` is a safety and refinement statement:
every finite observable trace of the target, including one that ends in
exit, is a trace of the source; a target that diverges or blocks before
exiting satisfies it. -/
theorem a64_scc_correctE_text_closedAt1_final (Λ : Scc.Sem.Layout) (hd : Scc.Lower.Accepted1 [d] = true)
    {ir : Scc.IR.Program} {setup : Bool} {items final tits : List Scc.Emit.A64.Item}
    {sps : List Scc.Emit.A64.Safepoint} {blks : List Scc.Cert.Rt.A64.OGrp} {tbl : List Kraken.DataImage.Item}
    (h1 : lowered1 cfg [d] = some (ir, setup)) (h2 : Scc.Emit.A64.emitItemsMaps ir = .ok (items, sps))
    (h3 : Scc.Lower.A64.tablesOf ir items cfg.gcWit = .ok (tits, tbl))
    (hc : Scc.Cert.Granule.A64.check final items = true)
    (hb : Scc.Cert.Granule.A64.blocksOfFinal ir final = some blks)
    (h : placeOKAt pcfg Λ (F) = true) {asm : String}
    (hpa : Scc.Cert.Link.A64.parsesTo asm (F).prog (F).secs = true) {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
    Scc.Sem.A64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
      { Λ with static := fun _ => none, imms := Scc.Lower.imms1Of [d] } B asm :=
  fun E hE =>
    let ⟨hp1, hp2⟩ := Scc.Cert.Link.A64.parsed_of_parsesTo hpa
    Scc.Sem.A64.correct_of_parsed _ E hp1 hp2 (a64_scc_correctE_closedAt1_final Λ hd h1 h2 h3 hc hb h E hE)

end CorrectFinal

end Spike.Lib.LowerA64
