/-
**The x86-64 compiler theorems on the post-pass text** (untrusted): the
twins of `x64_scc_correctE_text_closedAt1` (`Spike/Lib/LowerX64/Correct1.lean`)
and `x64_scc_correctE_text_closedAt` (`Spike/Lib/LowerX64/Correct.lean`) for
the output after the granule pass, `ofFinal sizes labelOffs st final`
(`Scc/Cert/GranuleOutX64.lean`), in place of scc's output `Out.ofEmitted
(lowerAll cfg [d]) sizes labelOffs`.

A certificate of a program built with the pass decides the stages of the
lowering and the emitter (`h1`, `h2`, as for the pre-pass output), the pass
check (`hc`: the post-pass items `Expand` the emitter's), that the post-pass
program fits the sizes (`hz`) and the post-pass block table (`hb`) on
literals, and `placeOKAt` and the loader's parse (`hpa`) on the post-pass
output itself. `sizes` and `labelOffs` are the assembler's of the rendered
post-pass text (the pass moves blocks, and relaxable branches change width
with them); A2 checks them as for any output. Nothing about the pre-pass
layout is transferred: the composition is `x64_lower_correctE1_of` /
`x64_lower_correctE_of` and `hgen1_ofPlaceOK_of` / `hgen_ofPlaceOK_of` at the
post-pass output, whose IR and tail are scc's (`ofFinal_of_stages`: only the
cells and the block table differ; `lowerAll_place_ir`,
`tail_bare_of_accepted1main`, `tail_bare_of_accepted0`).

- `lowerAll?_ok_of_stages`: the pipeline succeeds where its stages do.
- `ofFinal_place_ir`, `ofFinal_tail_bare1`, `ofFinal_tail_bare0`: the
  post-pass output names the lowering's IR and has a bare tail.
- `x64_scc_correctE_closedAt1_final`, `x64_scc_correctE_text_closedAt1_final`:
  `Accepted1` with the frame bound, at any layout passing `placeOKAt` on the
  post-pass output, closed; the latter on the text.
- `x64_scc_correctE_closedAt_final`, `x64_scc_correctE_text_closedAt_final`:
  the same for `Accepted0` (certify.sh's fallback when `main`'s frame is not
  within `MainFrame1Ok`).
-/
import Spike.Lib.LowerX64.Correct1
import Scc.Cert.GranuleOutX64

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.LowerNode (immsOf)
open Spike.Lib.X64Consumer (TParE)
open Scc.Sem (Entry)
open Kraken.Promising.X64 (sizedCells)

section CorrectFinal

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {d : Decl} {sizes : List Nat}
  {labelOffs : List (String × Nat)}

set_option quotPrecheck false

set_option hygiene false in
/-- The post-pass output: the stage `(ir, items, sps, tbl, need, setup)` with the
pass's items `final`, at the assembler's `sizes` and `labelOffs`. -/
local notation "F" => Scc.Cert.Granule.X64.ofFinal sizes labelOffs
  (ir, items, sps, tbl, (Scc.Lower.stackNeed .x64 ir).toOption, setup) final

/-- **The pipeline succeeds where its stages do**: the lowering gives `ir`
(`h1`) and the emitter succeeds on it (`h2`). -/
theorem lowerAll?_ok_of_stages {p : Prog} {ir : Scc.IR.Program} {setup : Bool}
    {items : List Scc.Emit.X64.Item} {sps : List (String × List Int × List Int)}
    (h1 : lowered1 cfg p = some (ir, setup)) (h2 : Scc.Emit.X64.emitItemsMaps ir = .ok (items, sps)) :
    ∃ em, Scc.Lower.X64.lowerAll? cfg p = .ok em := by
  unfold lowered1 at h1
  split at h1
  · rename_i l hl
    cases h1
    exact ⟨_, by simp only [Scc.Lower.X64.lowerAll?, hl, bind, Except.bind, Scc.Lower.X64.emitAll, h2]; rfl⟩
  · cases h1

/-- **The post-pass output names the lowering's IR** (`ofFinal_of_stages`:
only the cells and the block table differ from scc's output). -/
theorem ofFinal_place_ir {p : Prog} {ir : Scc.IR.Program} {setup : Bool}
    {items final tits : List Scc.Emit.X64.Item} {sps : List (String × List Int × List Int)}
    {tbl : List Kraken.DataImage.Item}
    {cs : List (Directive × Nat)} {blks : List Scc.Cert.Rt.X64.OGrp}
    (h1 : lowered1 cfg p = some (ir, setup)) (h2 : Scc.Emit.X64.emitItemsMaps ir = .ok (items, sps))
    (h3 : Scc.Lower.X64.tablesOf ir items cfg.gcWit = .ok (tits, tbl))
    (hc : Scc.Cert.Granule.X64.check final items = true)
    (hz : (Scc.Cert.Granule.X64.textCells final).bind (sizedCells · sizes) = some cs)
    (hb : Scc.Cert.Granule.X64.blocksOfFinal sizes ir final = some blks) :
    (F).place.ir = some (Scc.Lower.X64.lowerAll cfg p).low.ir := by
  rw [(Scc.Cert.Granule.X64.ofFinal_of_stages sizes labelOffs h1 h2 h3 hc hz hb).1]
  exact lowerAll_place_ir cfg p sizes labelOffs

/-- **The post-pass output of a main-only call-free `Accepted1` program has a
bare tail** (scc's: `tail_bare_of_accepted1main`). -/
theorem ofFinal_tail_bare1 (hd : Scc.Lower.Accepted1 [d] = true) {ir : Scc.IR.Program} {setup : Bool}
    {items final tits : List Scc.Emit.X64.Item} {sps : List (String × List Int × List Int)}
    {tbl : List Kraken.DataImage.Item}
    {cs : List (Directive × Nat)} {blks : List Scc.Cert.Rt.X64.OGrp}
    (h1 : lowered1 cfg [d] = some (ir, setup)) (h2 : Scc.Emit.X64.emitItemsMaps ir = .ok (items, sps))
    (h3 : Scc.Lower.X64.tablesOf ir items cfg.gcWit = .ok (tits, tbl))
    (hc : Scc.Cert.Granule.X64.check final items = true)
    (hz : (Scc.Cert.Granule.X64.textCells final).bind (sizedCells · sizes) = some cs)
    (hb : Scc.Cert.Granule.X64.blocksOfFinal sizes ir final = some blks) :
    (F).place.tail = .bare := by
  have ⟨_, hlow⟩ := lowerAll?_ok_of_stages h1 h2
  rw [(Scc.Cert.Granule.X64.ofFinal_of_stages sizes labelOffs h1 h2 h3 hc hz hb).1]
  exact tail_bare_of_accepted1main hd hlow sizes labelOffs

/-- **The post-pass output of an `Accepted0` program has a bare tail**
(scc's: `tail_bare_of_accepted0`). -/
theorem ofFinal_tail_bare0 (hd : Scc.Lower.Accepted0 [d] = true) {ir : Scc.IR.Program} {setup : Bool}
    {items final tits : List Scc.Emit.X64.Item} {sps : List (String × List Int × List Int)}
    {tbl : List Kraken.DataImage.Item}
    {cs : List (Directive × Nat)} {blks : List Scc.Cert.Rt.X64.OGrp}
    (h1 : lowered1 cfg [d] = some (ir, setup)) (h2 : Scc.Emit.X64.emitItemsMaps ir = .ok (items, sps))
    (h3 : Scc.Lower.X64.tablesOf ir items cfg.gcWit = .ok (tits, tbl))
    (hc : Scc.Cert.Granule.X64.check final items = true)
    (hz : (Scc.Cert.Granule.X64.textCells final).bind (sizedCells · sizes) = some cs)
    (hb : Scc.Cert.Granule.X64.blocksOfFinal sizes ir final = some blks) :
    (F).place.tail = .bare := by
  have ⟨_, hlow⟩ := lowerAll?_ok_of_stages h1 h2
  rw [(Scc.Cert.Granule.X64.ofFinal_of_stages sizes labelOffs h1 h2 h3 hc hz hb).1]
  exact tail_bare_of_accepted0 hd hlow sizes labelOffs

/-- **The x86-64 compiler theorem for a main-only call-free `Accepted1`
program after the granule pass, at any layout, closed**: for a program `[d]`
that `scc` accepts (`hd`) with `main`'s frame within 4096 bytes (`hfr`),
whose lowering and emission give `ir`, `items` and `sps` (`h1`, `h2`), whose
post-pass items `final` pass the check (`hc`), fit the sizes (`hz`) with the
block table `blks` (`hb`), and whose post-pass output passes the placement
check at a layout `Λ` (`h`), the post-pass output is `Correct` over the
kernel-model target `target (kernel 1) E` on parsed triples at every
admissible entry state `E`, at `Λ` with no static label and the lowering's
immediates (as `x64_scc_correctE_closedAt1`). -/
theorem x64_scc_correctE_closedAt1_final (Λ : Scc.Sem.Layout) (hd : Scc.Lower.Accepted1 [d] = true)
    (hfr : MainFrame1Ok cfg d = true) {ir : Scc.IR.Program} {setup : Bool}
    {items final tits : List Scc.Emit.X64.Item} {sps : List (String × List Int × List Int)}
    {tbl : List Kraken.DataImage.Item}
    {cs : List (Directive × Nat)} {blks : List Scc.Cert.Rt.X64.OGrp}
    (h1 : lowered1 cfg [d] = some (ir, setup)) (h2 : Scc.Emit.X64.emitItemsMaps ir = .ok (items, sps))
    (h3 : Scc.Lower.X64.tablesOf ir items cfg.gcWit = .ok (tits, tbl))
    (hc : Scc.Cert.Granule.X64.check final items = true)
    (hz : (Scc.Cert.Granule.X64.textCells final).bind (sizedCells · sizes) = some cs)
    (hb : Scc.Cert.Granule.X64.blocksOfFinal sizes ir final = some blks)
    (h : placeOKAt pcfg Λ (F) = true) {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
    ∀ E : Entry, E.Ok { Λ with static := fun _ => none, imms := Scc.Lower.imms1Of [d] } →
      Scc.Sem.Correct (TParE E) (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
        { Λ with static := fun _ => none, imms := Scc.Lower.imms1Of [d] } B
        ((F).prog, (F).secs, (F).labelOffs) :=
  have h' : placeOKAt pcfg { Λ with static := fun _ => none } (F) = true :=
    (Scc.Cert.PlaceOK.X64.placeOKAt_static pcfg Λ (F) (fun _ => none) Λ.imms).trans h
  have htl := ofFinal_tail_bare1 hd h1 h2 h3 hc hz hb
  fun E hE =>
    have ⟨_, hlow⟩ := lowerAll?_ok_of_stages h1 h2
    x64_lower_correctE1_of hd hfr hlow h' (ofFinal_place_ir h1 h2 h3 hc hz hb) htl
      (fun _ => rfl) hE (hgen1_ofPlaceOK_of h' htl E hE)

/-- **The x86-64 compiler theorem on the post-pass text for a main-only
call-free `Accepted1` program, at any layout, closed**
(`Scc.Sem.X64.CorrectE`): `x64_scc_correctE_text_closedAt1` with the
post-pass output in place of scc's, given its stages (`h1`, `h2`), the pass
check (`hc`), the post-pass cells (`hz`) and block table (`hb`). The
assembler text `⟨text, sizes, labelOffs⟩` the loader parses to the post-pass
output (`hpa`, the certificate's compiled `#guard`, the trust boundary;
`sizes` and `labelOffs` are the assembler's of the rendered post-pass text)
is `Correct` over the kernel-model target `target (kernel 1) E` at every
admissible entry state `E`, at `Λ` with no static label and the lowering's
immediates.

If the program exits, it exits as the source does; the theorem does not
promise that it exits. `Correct` is a safety and refinement statement:
every finite observable trace of the target, including one that ends in
exit, is a trace of the source; a target that diverges or blocks before
exiting satisfies it. -/
theorem x64_scc_correctE_text_closedAt1_final (Λ : Scc.Sem.Layout) (hd : Scc.Lower.Accepted1 [d] = true)
    (hfr : MainFrame1Ok cfg d = true) {ir : Scc.IR.Program} {setup : Bool}
    {items final tits : List Scc.Emit.X64.Item} {sps : List (String × List Int × List Int)}
    {tbl : List Kraken.DataImage.Item}
    {cs : List (Directive × Nat)} {blks : List Scc.Cert.Rt.X64.OGrp}
    (h1 : lowered1 cfg [d] = some (ir, setup)) (h2 : Scc.Emit.X64.emitItemsMaps ir = .ok (items, sps))
    (h3 : Scc.Lower.X64.tablesOf ir items cfg.gcWit = .ok (tits, tbl))
    (hc : Scc.Cert.Granule.X64.check final items = true)
    (hz : (Scc.Cert.Granule.X64.textCells final).bind (sizedCells · sizes) = some cs)
    (hb : Scc.Cert.Granule.X64.blocksOfFinal sizes ir final = some blks)
    (h : placeOKAt pcfg Λ (F) = true) {text : String}
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨text, sizes, labelOffs⟩ (F).prog (F).secs = true)
    {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
    Scc.Sem.X64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
      { Λ with static := fun _ => none, imms := Scc.Lower.imms1Of [d] } B ⟨text, sizes, labelOffs⟩ :=
  fun E hE =>
    let ⟨hp1, hp2⟩ := Scc.Cert.Link.X64.parsed_of_parsesTo hpa
    Scc.Sem.X64.correct_of_parsed _ E hp1 hp2 (x64_scc_correctE_closedAt1_final Λ hd hfr h1 h2 h3 hc hz hb h E hE)

/-- **The x86-64 compiler theorem for an `Accepted0` program after the
granule pass, at any layout, closed** (as `x64_scc_correctE_closedAt`, with
the post-pass output given its stages, check, cells and block table). -/
theorem x64_scc_correctE_closedAt_final (Λ : Scc.Sem.Layout) (hd : Scc.Lower.Accepted0 [d] = true)
    {ir : Scc.IR.Program} {setup : Bool}
    {items final tits : List Scc.Emit.X64.Item} {sps : List (String × List Int × List Int)}
    {tbl : List Kraken.DataImage.Item}
    {cs : List (Directive × Nat)} {blks : List Scc.Cert.Rt.X64.OGrp}
    (h1 : lowered1 cfg [d] = some (ir, setup)) (h2 : Scc.Emit.X64.emitItemsMaps ir = .ok (items, sps))
    (h3 : Scc.Lower.X64.tablesOf ir items cfg.gcWit = .ok (tits, tbl))
    (hc : Scc.Cert.Granule.X64.check final items = true)
    (hz : (Scc.Cert.Granule.X64.textCells final).bind (sizedCells · sizes) = some cs)
    (hb : Scc.Cert.Granule.X64.blocksOfFinal sizes ir final = some blks)
    (h : placeOKAt pcfg Λ (F) = true) {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
    ∀ E : Entry, E.Ok { Λ with static := fun _ => none, imms := immsOf d } →
      Scc.Sem.Correct (TParE E) (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
        { Λ with static := fun _ => none, imms := immsOf d } B ((F).prog, (F).secs, (F).labelOffs) :=
  have h' : placeOKAt pcfg { Λ with static := fun _ => none } (F) = true :=
    (Scc.Cert.PlaceOK.X64.placeOKAt_static pcfg Λ (F) (fun _ => none) Λ.imms).trans h
  have htl := ofFinal_tail_bare0 hd h1 h2 h3 hc hz hb
  fun E hE =>
    have ⟨_, hlow⟩ := lowerAll?_ok_of_stages h1 h2
    x64_lower_correctE_of hd hlow h' (ofFinal_place_ir h1 h2 h3 hc hz hb) htl
      (fun _ => rfl) hE (hgen_ofPlaceOK_of h' htl E hE)

/-- **The x86-64 compiler theorem on the post-pass text for an `Accepted0`
program, at any layout, closed** (`Scc.Sem.X64.CorrectE`):
`x64_scc_correctE_text_closedAt` with the post-pass output in place of
scc's (`x64_scc_correctE_text_closedAt1_final`'s premises without the frame
bound, at `immsOf d`).

If the program exits, it exits as the source does; the theorem does not
promise that it exits. `Correct` is a safety and refinement statement:
every finite observable trace of the target, including one that ends in
exit, is a trace of the source; a target that diverges or blocks before
exiting satisfies it. -/
theorem x64_scc_correctE_text_closedAt_final (Λ : Scc.Sem.Layout) (hd : Scc.Lower.Accepted0 [d] = true)
    {ir : Scc.IR.Program} {setup : Bool}
    {items final tits : List Scc.Emit.X64.Item} {sps : List (String × List Int × List Int)}
    {tbl : List Kraken.DataImage.Item}
    {cs : List (Directive × Nat)} {blks : List Scc.Cert.Rt.X64.OGrp}
    (h1 : lowered1 cfg [d] = some (ir, setup)) (h2 : Scc.Emit.X64.emitItemsMaps ir = .ok (items, sps))
    (h3 : Scc.Lower.X64.tablesOf ir items cfg.gcWit = .ok (tits, tbl))
    (hc : Scc.Cert.Granule.X64.check final items = true)
    (hz : (Scc.Cert.Granule.X64.textCells final).bind (sizedCells · sizes) = some cs)
    (hb : Scc.Cert.Granule.X64.blocksOfFinal sizes ir final = some blks)
    (h : placeOKAt pcfg Λ (F) = true) {text : String}
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨text, sizes, labelOffs⟩ (F).prog (F).secs = true)
    {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
    Scc.Sem.X64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
      { Λ with static := fun _ => none, imms := immsOf d } B ⟨text, sizes, labelOffs⟩ :=
  fun E hE =>
    let ⟨hp1, hp2⟩ := Scc.Cert.Link.X64.parsed_of_parsesTo hpa
    Scc.Sem.X64.correct_of_parsed _ E hp1 hp2 (x64_scc_correctE_closedAt_final Λ hd h1 h2 h3 hc hz hb h E hE)

end CorrectFinal

end Spike.Lib.LowerX64
