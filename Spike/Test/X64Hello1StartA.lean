/-
**`hello1.w` is correct on x86-64 at any source start** (`correctKA'`,
`Spike/Lib/X64ConsumerAStart.lean`): `Spike/Test/X64Hello1CorrectA.lean`'s
theorems with the source's start a parameter `s0'` with its thread `th0`
(`StartOk`), not `s0 P.cap`; in particular the start before the setup block,
whose thread calls `rodata` and then enters `main` (`setupStart`,
`Spike/Test/SetupStartSrc.lean`). The x86-64 twin of
`Spike/Test/A64Hello1StartA.lean`.

- `labT_siteL`, `hello1_hμ`: the take site's label is `μ0`'s take site, so
  the canonical target's take site is its address, given the parse.
- `hello1_correctKA'`: `hello1_correctKA` at a start with `StartOk`; `hst`
  is the loaded thread in `inv0` at the start's pair `⟨th0.term, th0.env, none⟩`.
- `hello1_correctKL'`: `hello1_correctKL` at such a start, with `hμ`
  discharged too (`hello1_hμ`, the take site's label `labT siteL`).
- `hello1_correctKLS`: `hello1_correctKL'` at `setupStart P.cap meW`, every start
  a `setupStart P.cap` (`srcSafeS_of_accepted2`'s `hinit`).

Where x86-64 differs from AArch64: the parse equation is `cellsOf` with the
cells `hello1Cells` (AArch64's `textProgram`, `hello1Prog`) and the data
sections are `hello1Asm.text`'s; the memory model is TSO (`Arch.tso`); the
code labels are `codeLabel`'s; `hello1_hμ` lives here (AArch64's is in
`Spike/Test/A64Hello1Load.lean`), from `hello1_marks` and `μ0`'s take
site at `labT siteL` (`4196218`).
-/
import Spike.Lib.X64ConsumerAStart
import Spike.Test.X64Hello1CorrectA
import Spike.Test.SetupStartSrc

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

open Scc.Cert.Link in
/-- **`hello1.w` is correct on x86-64 at a source start with `StartOk`**
(`hello1_correctKA` through `correctKA'`). -/
theorem hello1_correctKA' {P : SrcSem.SrcParams} {p : Prog} {B : Budget} (hB : B.cells = ar.cells)
    {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {own : OwnS} {code : String → Option Nat} {lsize : Lsize}
    {name : WeakMem.AllocLabel → String} {rS : Range} {Tk : State → Prop} {a : Int64}
    {W0 inv0 : FragS isa} {W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa} {Dt Ab : State → Prop}
    {s0' : TermRun.Cfg} {th0 : TermRun.TTh}
    -- the parse equations and the load facts
    (hpa : cellsOf hello1Asm = some hello1Cells) (hd : dataSections hello1Asm.text = some hello1Secs)
    (himg : imageOk hello1Λ hello1Secs code = true) (hss : Scc.Sem.StaticSyms hello1Λ hello1Secs code lsize name)
    (hload : ∃ t0, T.load hello1Asm hello1Λ = some t0)
    (hst : inv0 (threadAt Entry.linux hello1Λ.code.lo hello1Cells (loadSyms hello1Λ hello1Secs.rodata))
      ⟨th0.term, th0.env, none⟩ [])
    (hfr0 : Spike.Lib.AllocInv.FreshInv hello1Λ.static s0'.lbase s0'.n 0 0)
    (htk0 : ¬ Tk (threadAt Entry.linux hello1Λ.code.lo hello1Cells (loadSyms hello1Λ hello1Secs.rodata)))
    (hown0 : ∀ t0, T.load hello1Asm hello1Λ = some t0 →
      OwnInit (own (threadAt Entry.linux hello1Λ.code.lo hello1Cells (loadSyms hello1Λ hello1Secs.rodata)) [])
        t0.1.mem)
    (hG0 : ∀ t0, T.load hello1Asm hello1Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, hello1Λ.heap.contains a ∨ hello1Λ.data.contains a → G (wordLoc a) v)
    -- the source parameters and the start
    (hP : P.hooks = SrcSem.SrcHooks.none) (hinit : P.init s0') (hs : StartOk s0' th0) (hrd : ∀ w, rd w)
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
  exact correctKA' hB hpa hd himg hss SccCode.hello1_wide hs (.inl ⟨rfl, rfl, hst⟩) hfr0 hload
    (Spike.Lib.HookOK.none hP) hinit hN hsafe
    hT htk0 hown0 (writeNoPromA_b hN hT) hrd SccCode.hello1Λ_wf hG0 hGpl hA hab0
    Spike.Test.X64ArenaHello1.ar_ok Spike.Test.X64ArenaHello1.stat Spike.Test.X64ArenaHello1.sub
    Spike.Test.X64ArenaHello1.al (fun t0 h0 _ ha => Spike.Test.X64ArenaHello1.z0 (hinit0 t0 h0) ha)
    (fun t0 h0 => Spike.Test.X64ArenaHello1.c0 (hinit0 t0 h0))

/-- The take site's label is at `4196218`, `μ0`'s take site. -/
theorem labT_siteL :
    (Spike.Lib.X64.Flow.Hello1.Inst.labT Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat = 4196218 := by
  decide +kernel

/-- **`hμ`**: the canonical target's take site of `hello1` is the site
label's address, given the parse. -/
theorem hello1_hμ (hpa : cellsOf hello1Asm = some hello1Cells) :
    (T.marks hello1Asm hello1Λ).site .take =
      some (Spike.Lib.X64.Flow.Hello1.Inst.labT Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat := by
  rw [Spike.Lib.X64.Flow.Hello1.Inst.hello1_marks hpa, labT_siteL]; rfl

open Spike.Lib.X64.Flow.Hello1.Inst in
open Spike.Test.X64Hello1Load in
/-- **`hello1.w` is correct on x86-64 at a source start with `StartOk`,
the load facts and `hμ` discharged** (`hello1_correctKL` through
`hello1_correctKA'`; the take site is `labT siteL`, `hello1_hμ`). -/
theorem hello1_correctKL' {P : SrcSem.SrcParams} {p : Prog} {B : Budget} (hB : B.cells = ar.cells)
    {rd : TermRun.Word → Prop} {Fix : List (Nat × Val)} {lsize : Lsize} {rS : Range}
    {W0 inv0 : FragS isa} {W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa} {Dt Ab : State → Prop}
    {s0' : TermRun.Cfg} {th0 : TermRun.TTh}
    -- the parse equations (the trust boundary) and the loaded thread in `inv0`
    (hpa : cellsOf hello1Asm = some hello1Cells) (hd : dataSections hello1Asm.text = some hello1Secs)
    (hst : inv0 (threadAt Entry.linux hello1Λ.code.lo hello1Cells (loadSyms hello1Λ hello1Secs.rodata))
      ⟨th0.term, th0.env, none⟩ [])
    -- the value invariant's fixed words
    (hFix : ∀ a w, (a, w) ∈ Fix → a < 2 ^ 64 ∧ ¬ hello1Λ.heap.contains a ∧ ¬ hello1Λ.data.contains a)
    -- the source parameters and the start
    (hP : P.hooks = SrcSem.SrcHooks.none) (hinit : P.init s0') (hs : StartOk s0' th0) (hrd : ∀ w, rd w)
    -- the producer: the post-allocation family, the pre-allocation segment, the per-pair facts
    (h1 : ∀ l b n, hello1Λ.static l = none → AllocLand ar.heap ar.cells b n →
      SegInvS (W1 l b n) (TakeK (labT Spike.Lib.X64.Flow.Ret0.StackTake.siteL) rS) p (upd hello1Λ.static l b)
        (msOfA hello1Λ (T.marks hello1Asm hello1Λ) rd (FixG Fix hello1M0) (fun s _ => own s) ar
          (fun _ _ _ _ _ => False) (upd hello1Λ.static l b) (updN lsize l n)) (inv1 l b n))
    (h0 : SegInvS W0 (TakeK (labT Spike.Lib.X64.Flow.Ret0.StackTake.siteL) rS) p hello1Λ.static
      (msOfA hello1Λ (T.marks hello1Asm hello1Λ) rd (FixG Fix hello1M0) (fun s _ => own s) ar (Ih lsize inv0 inv1)
        hello1Λ.static lsize) inv0)
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
  hello1_correctKA' hB hpa hd hello1_himg
    (hello1_hss (code := Scc.Sem.X64.codeLabel hello1Λ.code.lo hello1Cells) (lsize := lsize) (name := fun _ => ""))
    (hello1_hload hpa hd) hst (hello1_hfr0 _ _) hello1_htk0 (hello1_hown0 hpa hd)
    (hello1_hG0 hpa hd Fix) (hello1_hGpl hFix) hP hinit hs hrd h1 h0 (hello1_hμ hpa) hW0 hW1 hab0 hsafe

/-- The start before the setup block has `StartOk` at its one thread. -/
theorem startOk_setupStart (cap : Nat) (meW : TermRun.Word) :
    StartOk (Scc.Sem.SrcSem.setupStart cap meW)
      { term := Scc.Sem.SrcSem.setupTerm, env := [("me", .ptr .pub .void, [meW]), ("u", .unit, [])] } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

open Spike.Lib.X64.Flow.Hello1.Inst in
open Spike.Test.X64Hello1Load in
/-- **`hello1.w` is correct on x86-64 from the start before the setup
block** (`hello1_correctKL'` at `setupStart P.cap meW`, `startOk_setupStart`):
`hst` is the loaded thread in `inv0` at `setupTerm`'s pair. `_hinitC` (every
start is a `setupStart P.cap`, unused here) is the form the source safety
`srcSafeS_of_accepted2` takes, so an instantiation discharges `hsafe` from it. -/
theorem hello1_correctKLS {P : SrcSem.SrcParams} {p : Prog} {B : Budget} (hB : B.cells = ar.cells)
    {rd : TermRun.Word → Prop} {Fix : List (Nat × Val)} {lsize : Lsize} {rS : Range}
    {W0 inv0 : FragS isa} {W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa} {Dt Ab : State → Prop}
    {meW : TermRun.Word}
    -- the parse equations (the trust boundary) and the loaded thread in `inv0`
    (hpa : cellsOf hello1Asm = some hello1Cells) (hd : dataSections hello1Asm.text = some hello1Secs)
    (hst : inv0 (threadAt Entry.linux hello1Λ.code.lo hello1Cells (loadSyms hello1Λ hello1Secs.rodata))
      ⟨Scc.Sem.SrcSem.setupTerm, [("me", .ptr .pub .void, [meW]), ("u", .unit, [])], none⟩ [])
    -- the value invariant's fixed words
    (hFix : ∀ a w, (a, w) ∈ Fix → a < 2 ^ 64 ∧ ¬ hello1Λ.heap.contains a ∧ ¬ hello1Λ.data.contains a)
    -- the source parameters at the setup start
    (hP : P.hooks = SrcSem.SrcHooks.none) (hinit : P.init (Scc.Sem.SrcSem.setupStart P.cap meW))
    (_hinitC : ∀ c, P.init c → ∃ meW, c = Scc.Sem.SrcSem.setupStart P.cap meW)
    (hrd : ∀ w, rd w)
    -- the producer: the post-allocation family, the pre-allocation segment, the per-pair facts
    (h1 : ∀ l b n, hello1Λ.static l = none → AllocLand ar.heap ar.cells b n →
      SegInvS (W1 l b n) (TakeK (labT Spike.Lib.X64.Flow.Ret0.StackTake.siteL) rS) p (upd hello1Λ.static l b)
        (msOfA hello1Λ (T.marks hello1Asm hello1Λ) rd (FixG Fix hello1M0) (fun s _ => own s) ar
          (fun _ _ _ _ _ => False) (upd hello1Λ.static l b) (updN lsize l n)) (inv1 l b n))
    (h0 : SegInvS W0 (TakeK (labT Spike.Lib.X64.Flow.Ret0.StackTake.siteL) rS) p hello1Λ.static
      (msOfA hello1Λ (T.marks hello1Asm hello1Λ) rd (FixG Fix hello1M0) (fun s _ => own s) ar (Ih lsize inv0 inv1)
        hello1Λ.static lsize) inv0)
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
  hello1_correctKL' hB hpa hd hst hFix hP hinit (startOk_setupStart P.cap meW) hrd h1 h0 hW0 hW1 hab0 hsafe

-- No axioms beyond Lean's.
/--
info: 'Spike.Test.X64Hello1CorrectA.hello1_correctKLS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hello1_correctKLS

end Spike.Test.X64Hello1CorrectA
