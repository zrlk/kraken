/-
**The x86-64 compiler theorem for an `Accepted1` program with calls**
(`x64_scc_correctE_text_closedAtC`): `Spike/Lib/LowerX64/Correct1.lean`'s
`x64_scc_correctE_text_closedAt1` for any `Accepted1` program `p` in place of
`[d]`, at the immediates `imms1Of p`, without the frame bound `MainFrame1Ok`,
given the configuration's `CfgNeedOk`. The lowering lowers calls plain (no
frames limit); every function's code facts come from the placement check
(`fnCodes_ofPlaceOK`).

- `lowerAll?_ok_of_placeOKC`: the lowering succeeds on an output passing
  `placeOKAt` (`lowerAll?_ok_of_placeOK` for any program);
- `mainFunc_of_accepted1`: the IR has the stack-checked user `main`;
- `x64_lower_correctEC`: at an admissible entry state, `main`'s depth `D`
  and limit room its frame (`userMainSW_ofPlaceOK`, `hroomU_ofPlaceOK'`
  within `12224`);
- `x64_scc_correctE_closedAtC`, `x64_scc_correctE_text_closedAtC`: at any
  layout passing `placeOKAt`; the latter on the text.
-/
import Spike.Lib.LowerX64.StartCorrectS
import Spike.Lib.LowerX64.MainRoomU
import Spike.Lib.LowerX64.MainC

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Lower.InvX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Scc.Sem
open Spike.Lib.X64Consumer (TParE)
open Spike.Lib.X64ConsumerS (SFactsS msOfS)
open Spike.Lib.X64.Rt (RuntimeLayout bareMC)
open Spike.Lib.X64.Flow.Ret0 (limA tpOf)
open Spike.Lib.X64.PhRec (μ K)

section Correct

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog} {sizes : List Nat}
  {labelOffs : List (String × Nat)}

set_option quotPrecheck false

/-- The lowering's output. -/
local notation "O" => Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs

/-- The runtime's layout of the output, at the lowering's immediates. -/
local notation "Ly" h => RuntimeLayout.ofPlaceOK h (Scc.Lower.imms1Of p)

/-- The value invariant: the first TCB's limit word holds its loaded value or the limit. -/
local notation "G0" h:max => Spike.Lib.X64.PhRec.GOf (Ly h) (Spike.Lib.X64.PhRec.m0Of (Ly h).Λ (O).prog (O).secs)

/-- **The lowering succeeds on an output passing `placeOKAt`**
(`lowerAll?_ok_of_placeOK` for any program): where `lowerAll?` fails,
`lowerAll`'s output is empty and fails the check (A11). -/
theorem lowerAll?_ok_of_placeOKC {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true) :
    ∃ em, Scc.Lower.X64.lowerAll? cfg p = .ok em := by
  cases he : Scc.Lower.X64.lowerAll? cfg p with
  | ok em => exact ⟨em, rfl⟩
  | error _ =>
    unfold Scc.Lower.X64.lowerAll at h
    rw [he] at h
    have h0 : placeOKAt pcfg Λ (Out.ofEmitted (default : Scc.Lower.X64.Emitted) sizes labelOffs) = false :=
      placeOKAt_eq_false_of_a11 rfl
    exact absurd h (by rw [h0]; decide)

/-- **The IR has the stack-checked user `main`**: for an `Accepted1`
program lowered to `em`, `func1` of `main`'s closed form. -/
theorem mainFunc_of_accepted1 (hp : Scc.Lower.Accepted1 p = true) {em : Scc.Lower.X64.Emitted}
    (hlow : Scc.Lower.X64.lowerAll? cfg p = .ok em) :
    ∃ f ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs,
      f.name = Scc.Lower.Names.user "main" ∧ f.checkStack = true := by
  obtain ⟨rs, rt, hrs, -, hir, -⟩ := lowerAll_accepted1_x64 cfg hp hlow
  have hm : p.any (·.name == "main") = true := by
    simp only [Scc.Lower.Accepted1, Bool.and_eq_true] at hp
    exact hp.1.1.2
  obtain ⟨dm, hf⟩ := Option.isSome_iff_exists.mp
    (List.find?_isSome.mpr (List.any_eq_true.mp hm) : (p.find? (·.name == "main")).isSome)
  have hn : dm.name = "main" := by simpa using List.find?_some hf
  obtain ⟨i, hi, rfl⟩ := Spike.Lib.LowerNode.find_index hf
  have hmem := Spike.Lib.LowerNode.mem_progOf_funcs1 cfg.layout rt hrs i hi
  rw [List.mem_zipIdx_iff_getElem?] at hmem
  have hmem' := List.mem_of_getElem? hmem
  rw [← hir] at hmem'
  exact ⟨_, hmem', by show Scc.Lower.Names.user p[i].name = _; rw [hn], rfl⟩

/-- **The x86-64 compiler theorem for an `Accepted1` program at an
admissible entry state `E`** (`hE`), no static label (`hs`), at a
configuration with `CfgNeedOk` (`hcfg`): `Correct` over the target on
parsed texts at `E`. -/
theorem x64_lower_correctEC (hp : Scc.Lower.Accepted1 p = true) {em : Scc.Lower.X64.Emitted}
    (hlow : Scc.Lower.X64.lowerAll? cfg p = .ok em) {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (O) = true) (hs : ∀ l, Λ.static l = none) (hcfg : CfgNeedOk pcfg = true)
    {B : Scc.Sem.Budget} {arch : WeakMem.Arch} {E : Entry} (hE : E.Ok (Ly h).Λ) :
    Scc.Sem.Correct (TParE E) (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) p) (Ly h).Λ B
      ((O).prog, (O).secs, (O).labelOffs) := by
  obtain ⟨D, fsz, hD0, hD8, hD, hfu, H⟩ := userMainSW_ofPlaceOK (cells := B.cells) hp hlow h hcfg
  exact x64_lower_correctES_of_user hp hlow h hs hE hD0 hD8 hD
    (hroomU_ofPlaceOK' h _ (Int.natCast_nonneg _) (by omega)) H

/-- **The x86-64 compiler theorem for an `Accepted1` program at any
layout**: for a program `p` that `scc` accepts (`hp`), whose output passes
the placement check at a layout `Λ` (`h`) at a configuration with
`CfgNeedOk` (`hcfg`), the output is `Correct` over the kernel-model target
at every entry state `E` that `Entry.Ok` admits, at `Λ` with no static
label and the lowering's immediates. -/
theorem x64_scc_correctE_closedAtC (Λ : Scc.Sem.Layout) (hp : Scc.Lower.Accepted1 p = true)
    (h : placeOKAt pcfg Λ (O) = true) (hcfg : CfgNeedOk pcfg = true)
    {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
    ∀ E : Entry, E.Ok { Λ with static := fun _ => none, imms := Scc.Lower.imms1Of p } →
      Scc.Sem.Correct (TParE E) (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) p)
        { Λ with static := fun _ => none, imms := Scc.Lower.imms1Of p } B
        ((O).prog, (O).secs, (O).labelOffs) :=
  have h' : placeOKAt pcfg { Λ with static := fun _ => none } (O) = true :=
    (Scc.Cert.PlaceOK.X64.placeOKAt_static pcfg Λ (O) (fun _ => none) Λ.imms).trans h
  fun _ hE =>
    have ⟨_, hlow⟩ := lowerAll?_ok_of_placeOKC h
    x64_lower_correctEC hp hlow h' (fun _ => rfl) hcfg hE

/-- **The x86-64 compiler theorem on the text for an `Accepted1` program,
at any layout** (`Scc.Sem.X64.CorrectE`): for a program `p` that `scc`
accepts (`hp`), whose output passes the placement check at a layout `Λ`
(`h`) at a configuration with `CfgNeedOk` (`hcfg`, decided on the
configuration) and whose assembler text `⟨text, sizes, labelOffs⟩` the
loader parses to it (`hpa`), the text is `Correct` over the kernel-model
target at every admissible entry state, at `Λ` with no static label and the
lowering's immediates.

If the program exits, it exits as the source does; the theorem does not
promise that it exits. -/
theorem x64_scc_correctE_text_closedAtC (Λ : Scc.Sem.Layout) (hp : Scc.Lower.Accepted1 p = true)
    (h : placeOKAt pcfg Λ (O) = true) (hcfg : CfgNeedOk pcfg = true)
    {text : String}
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨text, sizes, labelOffs⟩ (O).prog (O).secs = true)
    {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
    Scc.Sem.X64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) p)
      { Λ with static := fun _ => none, imms := Scc.Lower.imms1Of p } B ⟨text, sizes, labelOffs⟩ :=
  fun E hE =>
    let ⟨h1, h2⟩ := Scc.Cert.Link.X64.parsed_of_parsesTo hpa
    Scc.Sem.X64.correct_of_parsed _ E h1 h2 (x64_scc_correctE_closedAtC Λ hp h hcfg E hE)

end Correct

end Spike.Lib.LowerX64
