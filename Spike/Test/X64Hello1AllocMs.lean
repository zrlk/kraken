/-
**`hello1`'s allocation: the units, header and memory side** (x86-64; the
twin of `hello1_rodata_huA`, `hello1_rodata_hdrA` in
`Spike/Test/A64Hello1AllocPt.lean`): at `rodata`'s allocation
(`let b = newBuf m LanesU8`, count `2`), the premises of the allocation
point at the record of an output passing `placeOKAt`.

- `hello1_rodata_hu`: the units' operand `unitsOf 1 kv` is the arena's
  units (`3`) at `msOfAX`, at any arena layout;
- `hello1_rodata_hdr`: the allocation's header has no trace words (`mOf = 0`);
- `hello1_hms`: `CallMsOK` at the record's memory side over `arOf` and the
  record's labels, by `callMsOK_arOf` (the counter zeroed by
  `ctrZ_ofPlaceOK`, `GOf` free at the counter and the heap).
-/
import Spike.Lib.LowerX64.ArCallMs
import Spike.Lib.LowerX64.Closed2Of
import Spike.Lib.LowerX64.Construct
import Spike.Lib.Rt.X64CtrZOfEmitted
import Spike.Lib.Hello1RodataSrc
import Spike.Lib.LowerShapeC2
import Spike.Lib.Src.ImmsMe
import Spike.Test.Hello1MainSrc
import Spike.Test.Hello1LinkedX64

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.X64ConsumerA (msOfAX)
open Spike.Lib.X64.Alloc (Call mOf)
open Spike.Lib.X64.Rt (RuntimeLayout arOf)
open Spike.Lib.Hello1RodataSrc (τ8)

/-- The program. -/
local notation "P1" => Spike.Test.Hello1MainSrc.hello1o

/-- `ld`'s layout of the linked executable. -/
local notation "Le" => Spike.Test.Hello1LinkedX64.Λe

/-- The compiler's output for the program at the certificate's sizes and label offsets. -/
local notation "OX" =>
  Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.config P1) SccCertificate.sizes SccCertificate.labelOffs

/-- **The units' operand at `rodata`'s allocation** (`AllocPtW.hu`): at the
count `2` (`hk`), the operand `unitsOf 1 kv` (`LanesU8` one word an element)
is the immediate `3`, the arena's units of `2` elements of `LanesU8`
(`Arena.ofWords`: `2 · 1 + 1`) at the rows' memory side at either abort
phase, at any arena layout `Λ'` and any counts `en`, `em`. -/
theorem hello1_rodata_hu {Λ Λ' : Scc.Sem.Layout} {μ : Scc.Sem.Marks} {p : Prog} {rd : TermRun.Word → Prop}
    {G : Kraken.Promising.Loc → Kraken.Promising.Val → Prop} {own : Spike.Lib.X64ConsumerS.OwnS}
    {I : Spike.Lib.X64ConsumerS.InvS} {ab : Option (Kraken.Promising.X64.State → Prop)}
    {lbl : Spike.Lib.X64Consumer.Lbl} {lsize : Spike.Lib.X64Consumer.Lsize} {fs : List TermRun.Frame}
    (fr : Scc.Emit.X64.Frame) {en em : Nat} {kv : UInt64} (hk : kv.toNat = 2) :
    ∀ sl, Spike.Lib.Form.opdVal (Spike.Lib.LowerX64.rsOf fr) sl
        (Spike.Lib.LowerShape.unitsOf ((Scc.Frontend.words τ8).getD (en + em)) kv) =
      some ((msOfAX Λ μ p rd G own (arOf Λ') I ab lbl lsize fs).units kv.toNat τ8) := by
  intro sl
  have hw : Scc.Frontend.words τ8 = some 1 := by decide
  rw [hw, Option.getD_some, hk]
  have hu : (arOf Λ').units 2 τ8 = 3 := by
    simp only [arOf, Spike.Lib.Arena.ofWords]; decide
  cases ab <;>
  · show Spike.Lib.Form.opdVal _ sl (Spike.Lib.LowerShape.unitsOf 1 kv) = some ((arOf Λ').units 2 τ8)
    rw [hu]
    simp [Spike.Lib.LowerShape.unitsOf, Spike.Lib.Form.opdVal, Scc.Lower.imm, hk]

/-- **`rodata`'s allocation header has no trace words**: `LanesU8`'s counts
are `(1, 0)`, its array header `257`, of trace-word count `0`. -/
theorem hello1_rodata_hdr {en em h : Nat}
    (hco : Spike.Lib.LowerShape.countsO SccCertificate.config.layout.obj τ8 = some (en, em))
    (hhd : Scc.Obj.header0 SccCertificate.config.layout.obj .array en em = some h) :
    (mOf (BitVec.ofNat 64 h)).toNat = 0 := by
  have h10 : Spike.Lib.LowerShape.countsO SccCertificate.config.layout.obj τ8 = some (1, 0) := by decide
  rw [h10] at hco
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hco).symm
  have hv : Scc.Obj.header0 SccCertificate.config.layout.obj .array 1 0 = some 257 := by decide
  rw [hv] at hhd
  cases Option.some.inj hhd
  decide

section Hello1

variable (h : placeOKAt SccCertificate.placeCfg (lay2 Le P1) OX = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Spike.Lib.LowerNode.imms2Me Le P1)

set_option hygiene false in
/-- The record's initial memory. -/
local notation "M0" =>
  Spike.Lib.X64.PhRec.m0Of (Ly).Λ (Scc.Cert.PlaceOK.Out.prog OX) (OX).secs

/-- **`CallMsOK` at `rodata`'s allocation** (`AllocPtW.hms`): at a call of
`kv` elements of `LanesU8` with `rodata`'s header, the record's memory side
over `arOf` at the record's labels, by `callMsOK_arOf` at the record's link
(`placeOKAt` ignores the immediates), the counter zeroed by
`ctrZ_ofPlaceOK`, `GOf` free at the counter and the heap
(`gOf_ctr_arOf`, `gOf_heap_arOf`), the header by `hello1_rodata_hdr`. -/
theorem hello1_hms {rd : TermRun.Word → Prop} {I : Spike.Lib.X64ConsumerS.InvS}
    {ab : Option (Kraken.Promising.X64.State → Prop)} {ls : Spike.Lib.X64Consumer.Lsize}
    {fs : List TermRun.Frame} {en em hh : Nat} {kv : UInt64}
    (hco : Spike.Lib.LowerShape.countsO SccCertificate.config.layout.obj τ8 = some (en, em))
    (hhd : Scc.Obj.header0 SccCertificate.config.layout.obj .array en em = some hh) :
    ∀ q : Call, q.n = kv.toNat → q.τ = τ8 → q.h = BitVec.ofNat 64 hh →
      CallMsOK
        (msOfAX (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) P1 rd (Spike.Lib.X64.PhRec.GOf (Ly) M0)
          (fun s _ => Spike.Lib.X64.PhRec.own (Ly) s) (arOf (Ly).Λ) I ab (fun _ => none) ls fs)
        (_root_.Executable.labels (Ly).exe).label q := by
  intro q _ hτ hqh
  exact callMsOK_arOf (cfg := SccCertificate.placeCfg) (o := OX) h (Spike.Lib.X64.Rt.ctrZ_ofPlaceOK h)
    Scc.Sem.Entry.linux ab (gOf_ctr_arOf h _ _) (gOf_heap_arOf h _ _)
    (hacc := by rw [hτ]; exact ⟨_, rfl⟩) (hm := by rw [hqh]; exact hello1_rodata_hdr hco hhd)

end Hello1

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.hello1_rodata_hu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_rodata_hu

/-- info: 'Spike.Lib.LowerX64.hello1_rodata_hdr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_rodata_hdr

/-- info: 'Spike.Lib.LowerX64.hello1_hms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_hms
