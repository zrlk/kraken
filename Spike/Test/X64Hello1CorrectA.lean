/-
**`hello1.w` is correct on x86-64, from its remaining obligations**
(`correctKA`, `Spike/Lib/X64ConsumerACorrect.lean`, at `hello1.w`'s text,
layout and arena `ar`, `Spike/Test/X64ArenaHello1.lean`): the consumer's
obligations come from two segment levels around `hello1.w`'s one
allocation (`inst_of_segWA2`, `Spike/Lib/X64SegInstA.lean`), `WriteNoPromA`
from `write` being a certification dead end (`writeNoPromA_b`), the arena premises from the
layout (`ar_ok`, `stat`, `sub`, `al`, and `z0`, `c0` at the load's initial
words, `init_of_loadParsed`), the program's words and the layout's
well-formedness from the code (`hello1_wide`, `hello1Λ_wf`).

What remains are the hypotheses of `hello1_correctKA`, by owner:
- **the hello1 producer** (pre- and post-allocation segments with their
  invariants explicit, and `SFactsA` at every pair, the pre-allocation
  level's at the pairs of `inv0`, including `WrOkA` per row): `h0`, `h1`,
  `hμ`, `hW0`, `hW1`;
  on x86-64 with the `SegWS` combinators and start chain of branch `x64cs`
  (`X64PlacedS`), the H7c merge;
- **the abort stubs** (the phase `Ab` and its fields in `SFactsA` on the
  write-abort path, `stubHW_sfactsA` / `stubWW_sfactsA`): through `hW0` /
  `hW1`, and `hab0` (the loaded thread not in `Ab`);
- **the source** (`SrcSafeS` over the fragment `I2`): `hsafe`;
- **the load facts**: `hpa`, `hd` (the parse equations, the trust boundary:
  the kernel cannot run the parser, `Spike/Test/X64Hello1Load.lean`),
  `hst` (the loaded thread in the pre-allocation invariant, the producer's
  `inv0`), and, in `hello1_correctKA`, `himg`, `hss`, `hload`, `hfr0`,
  `htk0`, `hown0`, `hG0`, `hGpl`;
- **the source parameters**: `hP`, `hinit`, `hrd`.

`hello1_correctKL` discharges the latter load facts
(`Spike/Test/X64Hello1Load.lean`) at the producer's owned words and take phase (`Inst.own`, `Inst.Tk`,
`Spike/Lib/X64Hello1I.lean`), the value invariant `FixG Fix hello1M0` with
its fixed words off the heap and `.data` (`hFix`), and the code labels the
load resolves: its remaining hypotheses are the producer's, the abort
stubs', the source's, the parse equations, `hst` and the source parameters.
-/
import Spike.Lib.X64SegInstA
import Spike.Lib.X64WriteDead
import Spike.Test.X64ArenaHello1
import Spike.Test.X64Hello1Load

namespace Spike.Test.X64Hello1CorrectA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Arena FragS)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64.Flow.Ret0 (TakeK)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Test.X64ArenaHello1 (ar)
open SccCode (hello1Asm hello1Λ hello1Cells hello1Secs)

/-- **The canonical load's initial words** are `initOf`'s. -/
theorem init_of_loadParsed {H : Hooks isa} {E : Entry} {Λ : Scc.Sem.Layout} {cells : List (Directive × Nat)}
    {secs : DataSecs} {offs : List (String × Nat)} {t0 : (machine H).Cfg}
    (h : loadParsed H E Λ cells secs offs = some t0) :
    t0.1.mem.init = Scc.Cert.Rt.X64.initOf Λ cells secs := by
  unfold loadParsed at h
  dsimp only at h
  split at h
  · cases h; rfl
  · cases h

/-- The fragment of `hello1.w`'s one allocation, at the static placement
and the sizes `lsize`. -/
abbrev Ih (lsize : Lsize) (inv0 : FragS isa) (inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa) : InvS :=
  I2 ar hello1Λ.static lsize inv0 inv1

open Scc.Cert.Link in
/-- **`hello1.w` is correct on x86-64** (`Correct` over the canonical
target at its text, the budget's heap cells the arena's), given the
remaining obligations (the module docstring lists them by owner). -/
theorem hello1_correctKA {P : SrcSem.SrcParams} {p : Prog} {B : Budget} (hB : B.cells = ar.cells)
    {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {own : OwnS} {code : String → Option Nat} {lsize : Lsize}
    {name : WeakMem.AllocLabel → String} {rS : Range} {Tk : State → Prop} {a : Int64}
    {W0 inv0 : FragS isa} {W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa} {Dt Ab : State → Prop}
    -- the parse equations and the load facts
    (hpa : cellsOf hello1Asm = some hello1Cells) (hd : dataSections hello1Asm.text = some hello1Secs)
    (himg : imageOk hello1Λ hello1Secs code = true) (hss : Scc.Sem.StaticSyms hello1Λ hello1Secs code lsize name)
    (hload : ∃ t0, T.load hello1Asm hello1Λ = some t0)
    (hst : inv0 (threadAt Entry.linux hello1Λ.code.lo hello1Cells (loadSyms hello1Λ hello1Secs.rodata)) c0 [])
    (hfr0 : Spike.Lib.AllocInv.FreshInv hello1Λ.static (s0 P.cap).lbase (s0 P.cap).n 0 0)
    (htk0 : ¬ Tk (threadAt Entry.linux hello1Λ.code.lo hello1Cells (loadSyms hello1Λ hello1Secs.rodata)))
    (hown0 : ∀ t0, T.load hello1Asm hello1Λ = some t0 →
      OwnInit (own (threadAt Entry.linux hello1Λ.code.lo hello1Cells (loadSyms hello1Λ hello1Secs.rodata)) [])
        t0.1.mem)
    (hG0 : ∀ t0, T.load hello1Asm hello1Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, hello1Λ.heap.contains a ∨ hello1Λ.data.contains a → G (wordLoc a) v)
    -- the source parameters
    (hP : P.hooks = SrcSem.SrcHooks.none) (hinit : P.init (s0 P.cap)) (hrd : ∀ w, rd w)
    -- the producer: the post-allocation family, the pre-allocation segment, the per-pair facts
    (h1 : ∀ l b n, hello1Λ.static l = none → AllocLand ar.heap ar.cells b n →
      SegInvS (W1 l b n) (TakeK a rS) p (upd hello1Λ.static l b)
        (msOfA hello1Λ (T.marks hello1Asm hello1Λ) rd G own ar (fun _ _ _ _ _ => False) (upd hello1Λ.static l b)
          (updN lsize l n)) (inv1 l b n))
    (h0 : SegInvS W0 (TakeK a rS) p hello1Λ.static
      (msOfA hello1Λ (T.marks hello1Asm hello1Λ) rd G own ar (Ih lsize inv0 inv1) hello1Λ.static lsize) inv0)
    (hμ : (T.marks hello1Asm hello1Λ).site .take = some a.toBitVec.toNat)
    (hW0 : ∀ s c fs, inv0 s c fs → W0 s c fs →
      SFactsA hello1Λ (T.marks hello1Asm hello1Λ) p rd G own rS Tk ar (Ih lsize inv0 inv1) hello1Λ.static lsize
        s c fs Dt Ab)
    (hW1 : ∀ l b n s c fs, hello1Λ.static l = none → AllocLand ar.heap ar.cells b n → W1 l b n s c fs →
      SFactsA hello1Λ (T.marks hello1Asm hello1Λ) p rd G own rS Tk ar (Ih lsize inv0 inv1)
        (upd hello1Λ.static l b) (updN lsize l n) s c fs Dt Ab)
    -- the abort stubs' phase at load
    (hab0 : ¬ Ab (threadAt Entry.linux hello1Λ.code.lo hello1Cells (loadSyms hello1Λ hello1Secs.rodata)))
    -- the source
    (hsafe : SrcSafeS P p (Ih lsize inv0 inv1)) :
    Correct T (SrcSem.source P p) hello1Λ B hello1Asm := by
  obtain ⟨hN, hT, hA, -⟩ := inst_of_segWA2 h1 h0 hμ hW0 hW1
  have hl := load_of_parsed (kernel 1) Entry.linux hello1Λ hpa hd
  have hinit0 : ∀ t0, T.load hello1Asm hello1Λ = some t0 →
      t0.1.mem.init = Scc.Cert.Rt.X64.initOf hello1Λ hello1Cells hello1Secs := fun t0 h0 =>
    init_of_loadParsed (hl.symm.trans h0)
  exact correctKA hB hpa hd himg hss SccCode.hello1_wide (.inl ⟨rfl, rfl, hst⟩) hfr0 hload
    (Spike.Lib.HookOK.none hP) hinit hN hsafe hT htk0
    hown0 (writeNoPromA_b hN hT) hrd SccCode.hello1Λ_wf hG0 hGpl hA hab0 Spike.Test.X64ArenaHello1.ar_ok
    Spike.Test.X64ArenaHello1.stat Spike.Test.X64ArenaHello1.sub Spike.Test.X64ArenaHello1.al
    (fun t0 h0 _ ha => Spike.Test.X64ArenaHello1.z0 (hinit0 t0 h0) ha)
    (fun t0 h0 => Spike.Test.X64ArenaHello1.c0 (hinit0 t0 h0))


open Spike.Lib.X64.Flow.Hello1.Inst in
open Spike.Test.X64Hello1Load in
/-- **`hello1.w` is correct on x86-64, the load facts discharged**:
`hello1_correctKA` at the producer's owned words (`Inst.own`) and take phase
(`Inst.Tk`), the value invariant `FixG Fix hello1M0` (`hFix`: its words off
the heap and `.data`) and the load's code labels, with `himg`, `hss`,
`hload`, `hfr0`, `htk0`, `hown0`, `hG0`, `hGpl` from
`Spike/Test/X64Hello1Load.lean`. -/
theorem hello1_correctKL {P : SrcSem.SrcParams} {p : Prog} {B : Budget} (hB : B.cells = ar.cells)
    {rd : TermRun.Word → Prop} {Fix : List (Nat × Val)} {lsize : Lsize} {rS : Range} {a : Int64}
    {W0 inv0 : FragS isa} {W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa} {Dt Ab : State → Prop}
    -- the parse equations (the trust boundary) and the loaded thread in `inv0`
    (hpa : cellsOf hello1Asm = some hello1Cells) (hd : dataSections hello1Asm.text = some hello1Secs)
    (hst : inv0 (threadAt Entry.linux hello1Λ.code.lo hello1Cells (loadSyms hello1Λ hello1Secs.rodata)) c0 [])
    -- the value invariant's fixed words
    (hFix : ∀ a w, (a, w) ∈ Fix → a < 2 ^ 64 ∧ ¬ hello1Λ.heap.contains a ∧ ¬ hello1Λ.data.contains a)
    -- the source parameters
    (hP : P.hooks = SrcSem.SrcHooks.none) (hinit : P.init (s0 P.cap)) (hrd : ∀ w, rd w)
    -- the producer: the post-allocation family, the pre-allocation segment, the per-pair facts
    (h1 : ∀ l b n, hello1Λ.static l = none → AllocLand ar.heap ar.cells b n →
      SegInvS (W1 l b n) (TakeK a rS) p (upd hello1Λ.static l b)
        (msOfA hello1Λ (T.marks hello1Asm hello1Λ) rd (FixG Fix hello1M0) (fun s _ => own s) ar
          (fun _ _ _ _ _ => False) (upd hello1Λ.static l b) (updN lsize l n)) (inv1 l b n))
    (h0 : SegInvS W0 (TakeK a rS) p hello1Λ.static
      (msOfA hello1Λ (T.marks hello1Asm hello1Λ) rd (FixG Fix hello1M0) (fun s _ => own s) ar (Ih lsize inv0 inv1)
        hello1Λ.static lsize) inv0)
    (hμ : (T.marks hello1Asm hello1Λ).site .take = some a.toBitVec.toNat)
    (hW0 : ∀ s c fs, inv0 s c fs → W0 s c fs →
      SFactsA hello1Λ (T.marks hello1Asm hello1Λ) p rd (FixG Fix hello1M0) (fun s _ => own s) rS Tk ar
        (Ih lsize inv0 inv1) hello1Λ.static lsize s c fs Dt Ab)
    (hW1 : ∀ l b n s c fs, hello1Λ.static l = none → AllocLand ar.heap ar.cells b n → W1 l b n s c fs →
      SFactsA hello1Λ (T.marks hello1Asm hello1Λ) p rd (FixG Fix hello1M0) (fun s _ => own s) rS Tk ar
        (Ih lsize inv0 inv1) (upd hello1Λ.static l b) (updN lsize l n) s c fs Dt Ab)
    -- the abort stubs' phase at load
    (hab0 : ¬ Ab (threadAt Entry.linux hello1Λ.code.lo hello1Cells (loadSyms hello1Λ hello1Secs.rodata)))
    -- the source
    (hsafe : SrcSafeS P p (Ih lsize inv0 inv1)) :
    Correct T (SrcSem.source P p) hello1Λ B hello1Asm :=
  hello1_correctKA hB hpa hd hello1_himg
    (hello1_hss (code := Scc.Sem.X64.codeLabel hello1Λ.code.lo hello1Cells) (lsize := lsize) (name := fun _ => ""))
    (hello1_hload hpa hd) hst (hello1_hfr0 _ _) hello1_htk0 (hello1_hown0 hpa hd)
    (hello1_hG0 hpa hd Fix) (hello1_hGpl hFix) hP hinit hrd h1 h0 hμ hW0 hW1 hab0 hsafe

end Spike.Test.X64Hello1CorrectA
