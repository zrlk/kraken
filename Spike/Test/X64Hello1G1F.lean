/-
**`hello1` after the granule pass, as a corollary of the generic `Accepted2`
theorem** (x86-64): `x64_scc_correctE_text_closedAt2_final`
(`Spike/Lib/LowerX64/Closed2TailFinal.lean`) at `hello1`'s configuration,
the end label `scc_text_end` and the pass's labels `B = [scc_text_end,
.Lgw0]`.

- `hello1_finalC_genF`: `CorrectE` at the post-pass text at any layout at
  which the pre-pass output (`hE`) and the post-pass output (`hF`) pass the
  placement check, from the post-pass certificate's stage facts (the pass's
  items `final`, its cells `cs` at the post-pass `sizes`, its block table,
  the parse of the post-pass text) and the tail's shape (`hPE`, `hPF`,
  `hT`, `hTi`, `hfree`, the abort labels off `B`). The label facts of `B`
  are decided here.
-/
import Spike.Lib.LowerX64.Closed2TailFinal
import Spike.Test.X64Hello1G1

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.X64LabelCongr (Directive.Free)

/-- The program. -/
local notation "P1" => Spike.Test.Hello1MainSrc.hello1o

/-- The labels the pass moves or adds. -/
local notation "BT" => ["scc_text_end", ".Lgw0"]

open Kraken.Promising.X64 (sizedCells) in
/-- **`hello1`'s x86-64 statement at the post-pass text**, at any layout `Λ`
at which the compiler's output (`hE`) and the post-pass output (`hF`) pass
the placement check: `x64_scc_correctE_text_closedAt2_final` at `hello1`'s
configuration, the header bound `hello1_hobj`, `B = [scc_text_end, .Lgw0]`
(the transfer sites', the runtime's words' and the phase table's labels off
`B` by decision). -/
theorem hello1_finalC_genF {Λ : Scc.Sem.Layout}
    (hE : placeOKAt SccCertificate.placeCfg Λ
      (Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.config P1) SccCertificate.sizes
        SccCertificate.labelOffs) = true)
    {sizes : List Nat} {labelOffs : List (String × Nat)}
    {ir : Scc.IR.Program} {setup : Bool} {items final tits : List Scc.Emit.X64.Item}
    {sps : List (String × List Int × List Int)} {tbl : List Kraken.DataImage.Item}
    {cs : List (Directive × Nat)} {blks : List Scc.Cert.Rt.X64.OGrp}
    (h1 : lowered1 SccCertificate.config P1 = some (ir, setup))
    (h2 : Scc.Emit.X64.emitItemsMaps ir = .ok (items, sps))
    (h3 : Scc.Lower.X64.tablesOf ir items SccCertificate.config.gcWit = .ok (tits, tbl))
    (hc : Scc.Cert.Granule.X64.check final items = true)
    (hz : (Scc.Cert.Granule.X64.textCells final).bind (sizedCells · sizes) = some cs)
    (hb : Scc.Cert.Granule.X64.blocksOfFinal sizes ir final = some blks)
    (hF : placeOKAt SccCertificate.placeCfg Λ (Scc.Cert.Granule.X64.ofFinal sizes labelOffs
      (ir, items, sps, tbl, (Scc.Lower.stackNeed .x64 ir).toOption, setup) final) = true)
    {P T : List (Directive × Nat)}
    (hPE : (Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.config P1) SccCertificate.sizes
      SccCertificate.labelOffs).prog = P ++ [(.label "scc_text_end", 0)])
    (hPF : cs = P ++ T)
    (hT : ∀ dz ∈ T, ∀ l, dz.1 = .label l → l ∈ BT) (hTi : ∀ dz ∈ T, ∀ i, dz.1 ≠ .instr i)
    (hfree : ∀ i z, (Directive.instr i, z) ∈ P → Directive.Free BT (.instr i))
    (ha : ∀ k, Λ.abortLbl k ∉ BT)
    {text : String}
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨text, sizes, labelOffs⟩
      (Scc.Cert.Granule.X64.ofFinal sizes labelOffs
        (ir, items, sps, tbl, (Scc.Lower.stackNeed .x64 ir).toOption, setup) final).prog
      (Scc.Cert.Granule.X64.ofFinal sizes labelOffs
        (ir, items, sps, tbl, (Scc.Lower.stackNeed .x64 ir).toOption, setup) final).secs = true)
    {Bu : Scc.Sem.Budget} (hB : Bu.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch P1) P1) (lay2 Λ P1) Bu
      ⟨text, sizes, labelOffs⟩ :=
  x64_scc_correctE_text_closedAt2_final SccCertificate.config hello1_hobj
    Spike.Lib.LowerNode.hello1o_accepted2 (by decide) hE (by decide) h1 h2 h3 hc hz hb hF hPE hPF
    (by decide) hT hTi hfree (fun k => by cases k <;> decide) ha (by decide) (by decide) hpa hB

end Spike.Lib.LowerX64

/-- info: 'Spike.Lib.LowerX64.hello1_finalC_genF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_finalC_genF
