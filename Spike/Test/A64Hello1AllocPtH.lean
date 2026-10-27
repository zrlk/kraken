/-
**`hello1`'s allocation point: the walk's fields** (AArch64): at
`rodata`'s allocation (`let b = newBuf m LanesU8`), from the allocation's
resumption facts `PtC2` at `hello1o`'s compiled blocks, the fields
`hleaf`, `hu`, `hacc`, `hnr` of `AllocPtW` (`Spike/Lib/LowerA64/AllocW2AtOf.lean`)
at the record of an output passing `placeOKAt`, the context `CxOkH` (the
setup frame `[fr]`), for `Spike/Test/A64Hello1HAWNone.lean`'s `OpenAPtA`.

- `hello1_rodata_ptA`: at a `PtC2` of a compiled block of `hello1o` at an
  allocation, the allocation is `rodata`'s `eB` with count `2` and a leaf
  count layout (`hello1_rodata_nbTailA`, `hello1_rodata_count2A`,
  `hello1_rodata_packLeafA` at the walk's head);
- `hello1_rodata_fieldsA`: the four fields at any `msOfAX` at a frame `[fr]`;
- `hello1_ptFieldsA`: the four fields at `OpenAPtA`'s instance (the block's
  lowering context `lcx2`, `fnCode2OfPMe_spec`; the frames `[fr]` from `CxOkH`).
-/
import Spike.Test.A64Hello1AllocPt
import Spike.Test.A64Hello1HolesW
import Spike.Lib.LowerA64.AllocW2AtOf

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib.A64.Flow
open Spike.Lib.LowerNode (compiled2 TailAt2 hello1o_accepted2)
open Spike.Lib.Hello1RodataSrc (eW0 τ8)

/-- The program. -/
local notation "P1A" => Spike.Test.Hello1MainSrc.hello1o

variable {Λx : Scc.Sem.Layout}

set_option hygiene false in
/-- The layout: any layout at which the placement check passes (`h`). -/
local notation "LeA" => Λx

/-- The compiler's output for the program. -/
local notation "OA" => Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A)

/-- **`hello1o`'s allocation from its resumption facts**: at a `PtC2` of the
`j`th compiled block at `let x = newBuf cn τ in e` (the lowering context
`lcx2`, the theorem's immediates `imms2Me`, the terms `TailAt2`), with the
count's word an immediate `kv`, the allocation is `rodata`'s `eB`
(`hello1_rodata_nbTailA` at the walk's head), the count `2`
(`hello1_rodata_count2A`) and its literal layout a leaf
(`hello1_rodata_packLeafA` from the literal walk's `LitPt`). -/
theorem hello1_rodata_ptA {Λ : Scc.Sem.Layout} {obj : Scc.ObjLayout} {j : Nat} {d : Decl}
    (hd : (compiled2 P1A)[j]? = some d) {cx : Scc.Emit.A64.FnCtx} {Cd : Int64 → List Directive → Prop}
    {Bl : Int64 → Label → Nat → Prop} {lab : Label → Int64} {Lk : Expr × List (String × Scc.Lower.LitV) → Prop}
    {kk : Nat} {pc : Int64} {env : Scc.Lower.Env} {n : Nat} {lits : List (String × Scc.Lower.LitV)}
    {cs bufs : List (String × Nat)} {x : String} {cn : At} {τ : Ty} {e : Expr} {tk : Ty} {kv : UInt64}
    (hat : Scc.Lower.Inv.atomV env cn = some (tk, [.imm kv]))
    (hP : PtC2 (Spike.Lib.LowerNode.lcx2 P1A obj d) cx Cd Bl lab (Spike.Lib.LowerNode.imms2Me Λ P1A)
      (TailAt2 P1A j) Lk kk pc env n lits cs bufs (.let_ x (.newBuf cn τ) e)) :
    x = "b" ∧ cn = .var "m" ∧ τ = τ8 ∧ e = eW0 ∧ kv.toNat = 2 ∧ ∃ o, Scc.Lower.litAt lits cn = .leaf o := by
  obtain ⟨l, k, r, -, -, -, hWs, hLs, -, -⟩ := hP
  obtain ⟨hi, ht, -, hg, -⟩ := Spike.Lib.LowerNode.walk2_head hWs
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hello1_rodata_nbTailA hd ht
  exact ⟨rfl, rfl, rfl, rfl, hello1_rodata_count2A hd ht hg hi hat, hello1_rodata_packLeafA fun q hq => (hLs q hq).1⟩

/-- **`AllocPtW`'s walk fields at `hello1o`'s allocation** at any memory
side `msOfAX` over an arena `arOf Λ'` at a frame `[fr]`, at either abort
phase: the count's leaf (`hleaf`), the units (`hu`, `hello1_rodata_huA` at
the count `2`), the element's accesses (`hacc`) and no `main` return
(`hnr`), from `hello1_rodata_ptA`, at the configuration's object layout. -/
theorem hello1_rodata_fieldsA {Λ Λm Λ' : Scc.Sem.Layout} {j : Nat} {d : Decl}
    (hd : (compiled2 P1A)[j]? = some d) {cx : Scc.Emit.A64.FnCtx} {Cd : Int64 → List Directive → Prop}
    {Bl : Int64 → Label → Nat → Prop} {lab : Label → Int64} {Lk : Expr × List (String × Scc.Lower.LitV) → Prop}
    {kk : Nat} {pc : Int64} {env : Scc.Lower.Env} {n : Nat} {lits : List (String × Scc.Lower.LitV)}
    {cs bufs : List (String × Nat)} {x : String} {cn : At} {τ : Ty} {e : Expr} {tk : Ty} {kv : UInt64}
    {en em : Nat} {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop}
    {G : Kraken.Promising.Loc → Kraken.Promising.Val → Prop} {own : Spike.Lib.A64ConsumerS.OwnS}
    {I : Spike.Lib.A64ConsumerS.InvS} {ab : Option (Kraken.Promising.AArch64.State → Prop)}
    {lbl : Spike.Lib.A64Consumer.Lbl} {lsize : Spike.Lib.A64Consumer.Lsize} {fr : TermRun.Frame}
    (hat : Scc.Lower.Inv.atomV env cn = some (tk, [.imm kv]))
    (hco : Spike.Lib.LowerShape.countsO SccCertificate.config.layout.obj τ = some (en, em))
    (hP : PtC2 (Spike.Lib.LowerNode.lcx2 P1A SccCertificate.config.layout.obj d) cx Cd Bl lab
      (Spike.Lib.LowerNode.imms2Me Λ P1A) (TailAt2 P1A j) Lk kk pc env n lits cs bufs (.let_ x (.newBuf cn τ) e)) :
    (∃ o, Scc.Lower.litAt lits cn = .leaf o) ∧
    (∀ sl, Spike.Lib.Form.opdVal (Spike.Lib.LowerA64.rsOf cx) sl
        (Spike.Lib.LowerShape.unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv) =
      some ((Spike.Lib.A64ConsumerA.msOfAX Λm μ P1A rd G own (Spike.Lib.A64.Rt.arOf Λ') I ab lbl lsize
        [fr]).units kv.toNat τ)) ∧
    (∃ us, TermRun.accs (TermRun.close [] τ) = some us) ∧
    ([fr] = [] → ∀ a, e ≠ .ret a) := by
  obtain ⟨-, -, rfl, -, hk, hl⟩ := hello1_rodata_ptA hd hat hP
  exact ⟨hl, hello1_rodata_huA cx hk hco, hello1_haccA, hello1_hnrA⟩

section Hello1

variable (h : placeOKAt SccCertificate.placeCfg (lay2 LeA P1A) OA = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Spike.Lib.LowerNode.imms2Me LeA P1A)

set_option hygiene false in
/-- The record's static memory. -/
local notation "M0" => Spike.Lib.A64.PhRec.m0Of (Ly).Λ (Scc.Cert.PlaceOK.Out.prog OA) (OA).secs

set_option hygiene false in
/-- The `j`th block's code facts. -/
local notation "FC" => fnCode2OfPMe hello1o_accepted2 h LeA j d hd

/-- **`AllocPtW`'s walk fields at `OpenAPtA`'s instance** (`hleaf`, `hu`,
`hacc`, `hnr`): at a context `CxOkH` (the frames `[fr]`) of the `j`th
block, the block's lowering context `lcx2 … d` (`fnCode2OfPMe_spec`), the
fields by `hello1_rodata_fieldsA` at the record's memory side at the nodes'
abort `ab2`, at any family `J`. -/
theorem hello1_ptFieldsA {j : Nat} {d : Decl} (hd : (compiled2 P1A)[j]? = some d) {R : Spike.Lib.Region}
    {F : MachineData → Prop} {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64}
    {G0 : Ctl → Prop} {Ab' : Spike.Lib.FragS isaLSE2}
    (hcx : CxOkH h hello1o_accepted2 j R F fs fp ra tp G0 Ab') {Cd : Int64 → List Directive → Prop}
    {Bl : Int64 → Label → Nat → Prop} {lab : Label → Int64} {Lk : Expr × List (String × Scc.Lower.LitV) → Prop}
    {kk : Nat} {pc : Int64} {env : Scc.Lower.Env} {n : Nat} {lits : List (String × Scc.Lower.LitV)}
    {cs bufs : List (String × Nat)} {x : String} {cn : At} {τ : Ty} {e : Expr} {tk : Ty} {kv : UInt64}
    {en em : Nat} (J : Spike.Lib.A64ConsumerS.InvS)
    (hat : Scc.Lower.Inv.atomV env cn = some (tk, [.imm kv]))
    (hco : Spike.Lib.LowerShape.countsO (FC).lcx.obj τ = some (en, em))
    (hP : PtC2 (FC).lcx (FC).cx Cd Bl lab (Spike.Lib.LowerNode.imms2Me LeA P1A) (TailAt2 P1A j) Lk kk pc env n
      lits cs bufs (.let_ x (.newBuf cn τ) e)) :
    (∃ o, Scc.Lower.litAt lits cn = .leaf o) ∧
    (∀ sl, Spike.Lib.Form.opdVal (Spike.Lib.LowerA64.rsOf (FC).cx) sl
        (Spike.Lib.LowerShape.unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv) =
      some ((Spike.Lib.A64ConsumerA.msOfAX (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) P1A Spike.Lib.LowerNode.IsNum
        (Spike.Lib.A64.PhRec.GOf Ly M0) (fun s _ => Spike.Lib.A64.PhRec.own (Ly) s) (Spike.Lib.A64.Rt.arOf (Ly).Λ)
        (Spike.Lib.AllocReach.IN (Spike.Lib.A64.Rt.arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J)
        (ab2 P1A (Ly).lab) (fun _ => none) (fun _ => 0) fs).units kv.toNat τ)) ∧
    (∃ us, TermRun.accs (TermRun.close [] τ) = some us) ∧
    (fs = [] → ∀ a, e ≠ .ret a) := by
  obtain ⟨_, _, _, _, _, _, _, _, fr, _, H⟩ := hcx
  have hfs : fs = [fr] := H.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  subst hfs
  have hl := (fnCode2OfPMe_spec hello1o_accepted2 h LeA j d hd).1
  rw [hl] at hP hco
  exact hello1_rodata_fieldsA hd hat hco hP

end Hello1

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.hello1_rodata_ptA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_rodata_ptA

/-- info: 'Spike.Lib.LowerA64.hello1_rodata_fieldsA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_rodata_fieldsA

/-- info: 'Spike.Lib.LowerA64.hello1_ptFieldsA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_ptFieldsA
