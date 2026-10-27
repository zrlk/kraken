/-
**`hello1.w`'s two levels on AArch64 at their segments**
(`Spike/Lib/A64Hello1Levels.lean`, `Spike/Test/A64Hello1LevelsA.lean`):
`hello1_correctKLS_levels`'s `h0W` and `h1W` from the levels' segments
(`hello1_setup_pre_closedWS`, `hello1_post_closedWS`), the post-allocation
level's start `P1A` the allocator's landing (`landJ`) at `wc_rodata`'s
`.sp0`, and the pre-allocation level's allocation fragment from it.

The level before reaches the allocation fragment `Ih lsize ⊥ inv1` only at
`rodata`'s allocation: there the landing's base and words are the arena's
object of two bytes (`rd_land`) and the landing state is at `.sp0` of
`landJ` (`land_post`), so in `P1A` and in `inv1` by `hP1`. The landing's
invariant does not depend on the fragment (`landJ_xa`).

- `okA`, `landJ_xa`: the allocator's call premises and the landing do not
  depend on the memory side's allocation fragment.
- `allocLand_of_land`: `rd_land`'s base and count fit the arena.
- `P1A`: the level after's start for the fresh label `l` at `b` of `n`
  words, at the landing of the level before's memory side.
- `PreP`: cut A's premises (`SetupPreP`) but the allocation fragment's.
- `hxa_pre`: `SetupPreP.hxa` at `Ih lsize ⊥ inv1` from `P1A` in `inv1`.
- `h0W_of`, `h1W_of`: `hello1_correctKLS_levels`'s `h0W` and `h1W` forms.
- `hello1_correctKLS_levelsB`: `hello1_correctKLS_levels` at them.
-/
import Spike.Test.A64Hello1LevelsA

namespace Spike.Test.A64Hello1LevelsB

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Arena FragS OutS KOutS SegWS MemSide Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Hello1
open Spike.Lib.A64.Flow.Ret0 (TakeK LimOk MainG limA)
open Spike.Lib.A64.Alloc (Call Ea)
open Spike.Lib.A64.Rt (MainE swFSL)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.Hello1RodataSrc (τ8)
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Test.A64ArenaHello1 (ar off_bytes2 units_bytes2)
open Spike.Test.A64Hello1CorrectA (Ih)
open Spike.Test.A64Hello1LevelsA (hello1_correctKLS_levels)
open SccCode (hello1Asm hello1Λ hello1Prog hello1Secs)

/-! ## The landing at any allocation fragment -/

section Land

variable {Λ : Scc.Sem.Layout} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {own : OwnS}
  {ar : Arena} {I I' : InvS} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}

/-- **The allocator's call premises do not depend on the allocation
fragment** (`Call.OK` reads none of `msOfA`'s `xa`). -/
theorem okA {lab : Label → Int64} {q : Call} (h : q.OK (msOfA Λ μ rd G own ar I lbl lsize fs) lab) :
    q.OK (msOfA Λ μ rd G own ar I' lbl lsize fs) lab :=
  ⟨h.term, h.ev, h.num, h.hold, h.n_lt, h.ctr, h.heap, h.room, h.cells, h.units, h.off, h.accs, h.rt, h.mp,
    h.grow, h.hdr⟩

/-- **The landing does not depend on the allocation fragment**: the call
`q` rebuilt at the other fragment (`okA`), the rest unchanged. -/
theorem landJ_xa {lab : Label → Int64} {R : Region} {J : AS → Spike.Lib.Ctl → Prop} {l : WeakMem.AllocLabel} {b w : Nat}
    {σC σ : AS} {c : Spike.Lib.Ctl} (h : landJ (msOfA Λ μ rd G own ar I lbl lsize fs) lab R J l b w σC σ c) :
    landJ (msOfA Λ μ rd G own ar I' lbl lsize fs) lab R J l b w σC σ c :=
  let ⟨q, σx, σ', c1, h1, h2, h3, h4⟩ := h
  ⟨⟨q.1, okA q.2⟩, σx, σ', c1, h1, h2, h3, h4⟩

end Land

/-- **`rd_land`'s base and count fit the arena**: two bytes of `τ8` at an
old count whose object is within the cells. -/
theorem allocLand_of_land {b old : Nat} (hb : b = ar.heap + 16 * old + ar.off 2 τ8)
    (hold : old + ar.units 2 τ8 ≤ ar.cells) : AllocLand ar.heap ar.cells b 2 := by
  change b = ar.heap + 16 * old + ar.off 2 (.lanes false .w8) at hb
  change old + ar.units 2 (.lanes false .w8) ≤ ar.cells at hold
  rw [off_bytes2] at hb
  rw [units_bytes2] at hold
  exact ⟨by omega, by omega, by omega⟩

/-! ## The levels' starts and premises -/

section Levels

variable {p : Prog} {K : State → State → Prop} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : OwnS} {lsize : Lsize} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {rT : Scc.Sem.Range} {tcb top : BitVec 64} {c0 : Spike.Lib.Ctl} {L : Int} {e : Expr} {env : TermRun.Env}

/-- **The level after's start** for the fresh label `l` at `b` of `n`
words: for some aligned base `v` of a well-formed region of depth `L` and
caller's state `m0`, `σC` at `wc_rodata`'s call, `wc_rodata`'s `.sp0` under
`rodata`'s frame `setupFrame e env`, its invariant the landing (`landJ`) of
the level before's memory side (no allocation fragment, the static
placement) from `rodata`'s allocation (`rdJ'`). -/
def P1A (μ : Marks) (rd : TermRun.Word → Prop) (G : Loc → Val → Prop) (own : OwnS) (lsize : Lsize)
    (exe : _root_.Executable) (endPc : Int64) (rT : Scc.Sem.Range) (tcb top : BitVec 64) (c0 : Spike.Lib.Ctl) (L : Int)
    (e : Expr) (env : TermRun.Env) (l : WeakMem.AllocLabel) (b n : Nat) : FragS isaLSE2 :=
  fun s c fs => ∃ v : BitVec 64, v.toNat % 16 = 0 ∧ (swR v (-L) 0).OK ∧ ∃ m0 σC,
    (At exe endPc (mR (swR v (-L) 0)) (mF (swR v (-L) 0) (swFSL L rT top (limA (UInt64.ofBitVec tcb)) v) m0 σC)
      (pN (_root_.Executable.labels exe).label
        (landJ (msOfA hello1Λ μ rd G own ar (fun _ _ _ _ _ => False) hello1Λ.static lsize [setupFrame e env])
          (_root_.Executable.labels exe).label (swR v (-L) 0) (rdJ' ⟨top, UInt64.ofBitVec tcb, c0⟩) l b n σC)
        (fun _ _ => False) (fun _ _ => False) (fun _ _ => False) (fun _ _ => False) .s0)).at
      [setupFrame e env] s c fs

/-- **Cut A's premises but the allocation fragment's** (`SetupPreP` without
`hxa`, which `hxa_pre` gives). -/
structure PreP (W : FragS isaLSE2) (K : State → State → Prop) (ms : List TermRun.Frame → MemSide isaLSE2)
    (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop) (fs1 : List TermRun.Frame)
    (J' : AS → Spike.Lib.Ctl → Prop) : Prop where
  hW : MainPreW (fun s c => W s c fs1) K exe endPc R F (ms fs1) J'
  hlimM : ∀ σ c, J' σ c → LimOk (ms fs1) F exe endPc (tcbA σ.regs 8)
    (σ.regs.SP.toBitVec - (80 : Int64).toBitVec)
  hlimR : ∀ σ c, J' σ c → LimOk (ms fs1) F exe endPc (tcbA σ.regs 8)
    (σ.regs.SP.toBitVec - (80 : Int64).toBitVec - (48 : Int64).toBitVec)
  hq : ∀ σ c, J' σ c → ∃ q : Call, q.OK (ms fs1) (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
    q.h = 257#64 ∧ q.k = 2#64 ∧ q.u (ms fs1) = 3#64
  hmem : ∀ q : Call, q.OK (ms fs1) (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
    (a = BitVec.ofNat 64 (ms fs1).ctr ∨
      ∃ o, o + (ms fs1).units q.n q.τ ≤ (ms fs1).cells ∧ a.toNat = q.hdrAt (ms fs1) o) →
    ∀ m, F m → Mem.loadInt m.dmem a 8 = none

omit [Kraken.Executable.ValidLayout exe] in
/-- **Cut A's allocation fragment at `Ih lsize ⊥ inv1`**: at a landing of
`rodata`'s allocation (`rd_land`: two words at an object of the arena) the
landing state is in the level after's start (`land_post`, `landJ_xa`), so
in `inv1` (`hP1`), so in `Ih`'s post-allocation branch. -/
theorem hxa_pre {W : FragS isaLSE2} {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    (hP1 : ∀ l b n, hello1Λ.static l = none → AllocLand ar.heap ar.cells b n →
      ∀ s c fs, P1A μ rd G own lsize exe endPc rT tcb top c0 L e env l b n s c fs → inv1 l b n s c fs)
    {v : BitVec 64} (h16 : v.toNat % 16 = 0) (hok : (swR v (-L) 0).OK)
    (hP : PreP W K (msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize) exe
      endPc (swR v (-L) 0) (swFSL L rT top (limA (UInt64.ofBitVec tcb)) v) [setupFrame e env]
      (rdJ' ⟨top, UInt64.ofBitVec tcb, c0⟩)) :
    SetupPreP W K hello1Λ.static
      (msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize) exe endPc
      (swR v (-L) 0) (swFSL L rT top (limA (UInt64.ofBitVec tcb)) v) [setupFrame e env]
      (rdJ' ⟨top, UInt64.ofBitVec tcb, c0⟩) := by
  refine ⟨hP.hW, hP.hlimM, hP.hlimR, hP.hq, hP.hmem, ?_⟩
  intro m0 σC q F' hFF hkeep l b w s c hl hAt
  obtain ⟨-, -, -, -, σx, -, hF', hJ⟩ := id hAt
  obtain ⟨mC, σ', c1, -, h1, h2, -⟩ := hkeep _ hF'
  obtain ⟨old, hb, hold, rfl⟩ := rd_land h1 h2 hJ
  have hAL := allocLand_of_land hb hold
  have hpost := land_post (J1 := fun _ _ => False) (J2 := fun _ _ => False) (J3 := fun _ _ => False)
    (J4 := fun _ _ => False) hFF hkeep hAt
  obtain ⟨g1, g2, g3, g4, σ, hA, hF, hJp⟩ := hpost
  refine ⟨hAL, .inr ⟨l, b, 2, hl, hAL, rfl, rfl, hP1 l b 2 hl hAL s c _ ⟨v, h16, hok, m0, σC, ?_, rfl⟩⟩⟩
  exact ⟨g1, g2, g3, g4, σ, hA, hF, landJ_xa hJp⟩

/-- **The level before at `Ih lsize ⊥ inv1`** (`h0W`'s form): for every
`inv1` containing the level after's starts `P1A`,
`hello1_setup_pre_closedWS` with cut A's allocation fragment from
`hxa_pre`. The start's segment `hD`, cut A's other premises `hPre` and the
heap abort's obligations `hsH` are at every such fragment. -/
theorem h0W_of {W0 P0 : FragS isaLSE2}
    (hp : Lays exe hello1Prog) (hend : endPc = endOf exe hello1Prog) (hL : setupL ≤ L)
    (hfit : (limA (UInt64.ofBitVec tcb)).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (UInt64.ofBitVec tcb)).toNat : Int) + 8 ≤ top.toNat + -L ∨
      (top.toNat : Int) + 0 ≤ (limA (UInt64.ofBitVec tcb)).toNat)
    (hfitS : rT.lo + rT.size ≤ 2 ^ 64) (hc0 : c0 = ⟨setupCall e, env, none⟩)
    (hd : p.find? (·.name == "rodata") = Spike.Lib.Hello1Src.hello1Src[1]?)
    (hu : TermRun.evalAt env (.var "u") = some (.unit, []))
    (hD : ∀ inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2, SegWS W0 K p hello1Λ.static
      (msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize) P0
      ((MainE exe endPc rT tcb top c0 L).at []))
    (hWe : ∀ s c, MainE exe endPc rT tcb top c0 L s c → W0 s c [])
    (hPre : ∀ inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2, ∀ v : BitVec 64, v.toNat % 16 = 0 →
      (swR v (-L) 0).OK →
      PreP W0 K (msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize) exe
        endPc (swR v (-L) 0) (swFSL L rT top (limA (UInt64.ofBitVec tcb)) v) [setupFrame e env]
        (rdJ' ⟨top, UInt64.ofBitVec tcb, c0⟩))
    (hsH : ∀ inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2, ∀ v : BitVec 64, v.toNat % 16 = 0 →
      (swR v (-L) 0).OK →
      HAbStub W0 K p hello1Λ.static
        (msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize) exe endPc
        (swR v (-L) 0) (swFSL L rT top (limA (UInt64.ofBitVec tcb)) v) (setupFrame e env)
        (mRdJ0 (mNC (_root_.Executable.labels exe).label (rdJ' ⟨top, UInt64.ofBitVec tcb, c0⟩)).J)) :
    ∀ inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2,
      (∀ l b n, hello1Λ.static l = none → AllocLand ar.heap ar.cells b n →
        ∀ s c fs, P1A μ rd G own lsize exe endPc rT tcb top c0 L e env l b n s c fs → inv1 l b n s c fs) →
      SegWS W0 K p hello1Λ.static
        (msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize) P0
        (fun _ _ _ => False) := fun inv1 hP1 =>
  hello1_setup_pre_closedWS hp hend hL (fun _ => rfl) hfit hout hfitS hc0 rfl hd hu (hD inv1) hWe
    (fun v h16 hok => hxa_pre hP1 h16 hok (hPre inv1 v h16 hok)) (hsH inv1)

/-- **The level after for the fresh label `l` at `b` of `n` words**
(`h1W`'s form): `hello1_post_closedWS` from `P1A` under `rodata`'s frame,
its start invariant the landing (`Jp`). Cut B's premises `hPost` (`J1` …
`Jw` free per landing) and `print`'s abort's obligations `hsW` are per
landing. -/
theorem h1W_of {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    (hp : Lays exe hello1Prog) (hend : endPc = endOf exe hello1Prog) (hL : setupL ≤ L)
    (hfit : (limA (UInt64.ofBitVec tcb)).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (UInt64.ofBitVec tcb)).toNat : Int) + 8 ≤ top.toNat + -L ∨
      (top.toNat : Int) + 0 ≤ (limA (UInt64.ofBitVec tcb)).toNat)
    (hfitS : rT.lo + rT.size ≤ 2 ^ 64)
    {J1 J2 J3 J4 Jr Jw : WeakMem.AllocLabel → Nat → Nat → BitVec 64 → MachineData → AS → AS → Spike.Lib.Ctl → Prop}
    (hPost : ∀ l b n, hello1Λ.static l = none → AllocLand ar.heap ar.cells b n →
      ∀ v : BitVec 64, v.toNat % 16 = 0 → (swR v (-L) 0).OK → ∀ m0 σC,
      SetupPostP (W1 l b n) K p (upd hello1Λ.static l b)
        (msOfA hello1Λ μ rd G own ar (fun _ _ _ _ _ => False) (upd hello1Λ.static l b) (updN lsize l n)) exe endPc
        (swR v (-L) 0) (swFSL L rT top (limA (UInt64.ofBitVec tcb)) v) (setupFrame e env) m0 σC
        (landJ (msOfA hello1Λ μ rd G own ar (fun _ _ _ _ _ => False) hello1Λ.static lsize [setupFrame e env])
          (_root_.Executable.labels exe).label (swR v (-L) 0) (rdJ' ⟨top, UInt64.ofBitVec tcb, c0⟩) l b n σC)
        (J1 l b n v m0 σC) (J2 l b n v m0 σC) (J3 l b n v m0 σC) (J4 l b n v m0 σC) (Jr l b n v m0 σC)
        (Jw l b n v m0 σC))
    (hsW : ∀ l b n, hello1Λ.static l = none → AllocLand ar.heap ar.cells b n →
      ∀ v : BitVec 64, v.toNat % 16 = 0 → (swR v (-L) 0).OK →
      MAbStub (W1 l b n) K p (upd hello1Λ.static l b)
        (msOfA hello1Λ μ rd G own ar (fun _ _ _ _ _ => False) (upd hello1Λ.static l b) (updN lsize l n)) exe endPc
        (swR v (-L) 0) (swFSL L rT top (limA (UInt64.ofBitVec tcb)) v) []) :
    ∀ l b n, hello1Λ.static l = none → AllocLand ar.heap ar.cells b n →
      SegWS (W1 l b n) K p (upd hello1Λ.static l b)
        (msOfA hello1Λ μ rd G own ar (fun _ _ _ _ _ => False) (upd hello1Λ.static l b) (updN lsize l n))
        (P1A μ rd G own lsize exe endPc rT tcb top c0 L e env l b n) (fun _ _ _ => False) := fun l b n hl hAL =>
  (hello1_post_closedWS hp hend (show 288 ≤ L by simp only [setupL] at hL; omega) rfl rfl hfit hout hfitS
    (Jp := fun v _ σC => landJ
      (msOfA hello1Λ μ rd G own ar (fun _ _ _ _ _ => False) hello1Λ.static lsize [setupFrame e env])
      (_root_.Executable.labels exe).label (swR v (-L) 0) (rdJ' ⟨top, UInt64.ofBitVec tcb, c0⟩) l b n σC)
    (hPost l b n hl hAL) (hsW l b n hl hAL)).mono_pre fun _ _ _ h => h

end Levels

/-! ## Correctness from the levels' segments -/

open Spike.Lib.A64.Flow.Hello1.Inst in
open Spike.Test.A64Hello1Load in
/-- **`hello1.w` is correct on AArch64 from its two levels' segments**
(`hello1_correctKLS_levels` at `h0W_of`, `h1W_of`): the level after's start
`P1A` the allocator's landing at `wc_rodata`'s `.sp0`; the start's segment,
cut A's and cut B's premises and the abort tails' obligations at the
levels' `W0`, `W1`. `rT` is the stack range of the start's switch, `rS`
`TakeK`'s. -/
theorem hello1_correctKLS_levelsB {p : Prog} {rd : TermRun.Word → Prop} {Fix : List (Nat × Val)}
    {lsize : Lsize} {rS : Range} {W0 P0 : FragS isaLSE2} {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {meW : TermRun.Word} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {rT : Scc.Sem.Range} {tcb top : BitVec 64} {c0 : Spike.Lib.Ctl} {L : Int} {e : Expr} {env : TermRun.Env}
    (hp : Lays exe hello1Prog) (hend : endPc = endOf exe hello1Prog) (hL : setupL ≤ L)
    (hfit : (limA (UInt64.ofBitVec tcb)).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (UInt64.ofBitVec tcb)).toNat : Int) + 8 ≤ top.toNat + -L ∨
      (top.toNat : Int) + 0 ≤ (limA (UInt64.ofBitVec tcb)).toNat)
    (hfitS : rT.lo + rT.size ≤ 2 ^ 64) (hc0 : c0 = ⟨setupCall e, env, none⟩)
    (hd : p.find? (·.name == "rodata") = Spike.Lib.Hello1Src.hello1Src[1]?)
    (hu : TermRun.evalAt env (.var "u") = some (.unit, []))
    (hD : ∀ inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2,
      SegWS W0 (TakeK (labT Spike.Lib.A64.Flow.Ret0.StackTake.siteL) rS) p hello1Λ.static
        (msOfA hello1Λ (T.marks hello1Asm hello1Λ) rd (FixG Fix hello1M0) (fun s _ => own s) ar
          (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize) P0 ((MainE exe endPc rT tcb top c0 L).at []))
    (hWe : ∀ s c, MainE exe endPc rT tcb top c0 L s c → W0 s c [])
    (hPre : ∀ inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2, ∀ v : BitVec 64, v.toNat % 16 = 0 →
      (swR v (-L) 0).OK →
      PreP W0 (TakeK (labT Spike.Lib.A64.Flow.Ret0.StackTake.siteL) rS)
        (msOfA hello1Λ (T.marks hello1Asm hello1Λ) rd (FixG Fix hello1M0) (fun s _ => own s) ar
          (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize) exe
        endPc (swR v (-L) 0) (swFSL L rT top (limA (UInt64.ofBitVec tcb)) v) [setupFrame e env]
        (rdJ' ⟨top, UInt64.ofBitVec tcb, c0⟩))
    (hsH : ∀ inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2, ∀ v : BitVec 64, v.toNat % 16 = 0 →
      (swR v (-L) 0).OK →
      HAbStub W0 (TakeK (labT Spike.Lib.A64.Flow.Ret0.StackTake.siteL) rS) p hello1Λ.static
        (msOfA hello1Λ (T.marks hello1Asm hello1Λ) rd (FixG Fix hello1M0) (fun s _ => own s) ar
          (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize) exe endPc
        (swR v (-L) 0) (swFSL L rT top (limA (UInt64.ofBitVec tcb)) v) (setupFrame e env)
        (mRdJ0 (mNC (_root_.Executable.labels exe).label (rdJ' ⟨top, UInt64.ofBitVec tcb, c0⟩)).J))
    {J1 J2 J3 J4 Jr Jw : WeakMem.AllocLabel → Nat → Nat → BitVec 64 → MachineData → AS → AS → Spike.Lib.Ctl → Prop}
    (hPost : ∀ l b n, hello1Λ.static l = none → AllocLand ar.heap ar.cells b n →
      ∀ v : BitVec 64, v.toNat % 16 = 0 → (swR v (-L) 0).OK → ∀ m0 σC,
      SetupPostP (W1 l b n) (TakeK (labT Spike.Lib.A64.Flow.Ret0.StackTake.siteL) rS) p (upd hello1Λ.static l b)
        (msOfA hello1Λ (T.marks hello1Asm hello1Λ) rd (FixG Fix hello1M0) (fun s _ => own s) ar
          (fun _ _ _ _ _ => False) (upd hello1Λ.static l b) (updN lsize l n)) exe endPc
        (swR v (-L) 0) (swFSL L rT top (limA (UInt64.ofBitVec tcb)) v) (setupFrame e env) m0 σC
        (landJ (msOfA hello1Λ (T.marks hello1Asm hello1Λ) rd (FixG Fix hello1M0) (fun s _ => own s) ar
            (fun _ _ _ _ _ => False) hello1Λ.static lsize [setupFrame e env])
          (_root_.Executable.labels exe).label (swR v (-L) 0) (rdJ' ⟨top, UInt64.ofBitVec tcb, c0⟩) l b n σC)
        (J1 l b n v m0 σC) (J2 l b n v m0 σC) (J3 l b n v m0 σC) (J4 l b n v m0 σC) (Jr l b n v m0 σC)
        (Jw l b n v m0 σC))
    (hsW : ∀ l b n, hello1Λ.static l = none → AllocLand ar.heap ar.cells b n →
      ∀ v : BitVec 64, v.toNat % 16 = 0 → (swR v (-L) 0).OK →
      MAbStub (W1 l b n) (TakeK (labT Spike.Lib.A64.Flow.Ret0.StackTake.siteL) rS) p (upd hello1Λ.static l b)
        (msOfA hello1Λ (T.marks hello1Asm hello1Λ) rd (FixG Fix hello1M0) (fun s _ => own s) ar
          (fun _ _ _ _ _ => False) (upd hello1Λ.static l b) (updN lsize l n)) exe endPc
        (swR v (-L) 0) (swFSL L rT top (limA (UInt64.ofBitVec tcb)) v) [])
    (hst : P0 (threadAt Entry.linux hello1Λ.code.lo hello1Prog (loadSyms hello1Λ hello1Secs.rodata))
      ⟨Scc.Sem.SrcSem.setupTerm, [("me", .ptr .pub .void, [meW]), ("u", .unit, [])], none⟩ []) :
    ∃ (inv0 : FragS isaLSE2) (inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2),
      (∀ s c fs, P0 s c fs → inv0 s c fs) ∧
      (∀ l b n, hello1Λ.static l = none → AllocLand ar.heap ar.cells b n →
        ∀ s c fs, P1A (T.marks hello1Asm hello1Λ) rd (FixG Fix hello1M0) (fun s _ => own s) lsize exe endPc rT
          tcb top c0 L e env l b n s c fs → inv1 l b n s c fs) ∧
      (∀ inv, SegInvS W0 (TakeK (labT Spike.Lib.A64.Flow.Ret0.StackTake.siteL) rS) p hello1Λ.static
        (msOfA hello1Λ (T.marks hello1Asm hello1Λ) rd (FixG Fix hello1M0) (fun s _ => own s) ar
          (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize) inv →
        ∀ s c fs, inv s c fs → inv0 s c fs) ∧
      ∀ (P : SrcSem.SrcParams) (B : Budget) (Dt Ab : State → Prop), B.cells = ar.cells →
        textProgram hello1Asm = .ok hello1Prog → dataSections hello1Asm = some hello1Secs →
        (∀ a w, (a, w) ∈ Fix → a < 2 ^ 64 ∧ ¬ hello1Λ.heap.contains a ∧ ¬ hello1Λ.data.contains a) →
        P.hooks = SrcSem.SrcHooks.none → P.init (Scc.Sem.SrcSem.setupStart P.cap meW) →
        (∀ c, P.init c → ∃ meW, c = Scc.Sem.SrcSem.setupStart P.cap meW) →
        (∀ w, rd w) →
        (∀ s c fs, inv0 s c fs → W0 s c fs →
          SFactsA hello1Λ (T.marks hello1Asm hello1Λ) p rd (FixG Fix hello1M0) (fun s _ => own s) rS Tk ar
            (Ih lsize inv0 inv1) hello1Λ.static lsize s c fs Dt Ab) →
        (∀ l b n s c fs, hello1Λ.static l = none → AllocLand ar.heap ar.cells b n → W1 l b n s c fs →
          SFactsA hello1Λ (T.marks hello1Asm hello1Λ) p rd (FixG Fix hello1M0) (fun s _ => own s) rS Tk ar
            (Ih lsize inv0 inv1) (upd hello1Λ.static l b) (updN lsize l n) s c fs Dt Ab) →
        ¬ Ab (threadAt Entry.linux hello1Λ.code.lo hello1Prog (loadSyms hello1Λ hello1Secs.rodata)) →
        SrcSafeS P p (Ih lsize inv0 inv1) →
        Correct T (SrcSem.source P p) hello1Λ B hello1Asm :=
  hello1_correctKLS_levels (h1W_of hp hend hL hfit hout hfitS hPost hsW)
    (h0W_of hp hend hL hfit hout hfitS hc0 hd hu hD hWe hPre hsH) hst

-- No axioms beyond Lean's.

/--
info: 'Spike.Test.A64Hello1LevelsB.landJ_xa' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms landJ_xa

/--
info: 'Spike.Test.A64Hello1LevelsB.hxa_pre' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hxa_pre

/--
info: 'Spike.Test.A64Hello1LevelsB.h0W_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms h0W_of

/--
info: 'Spike.Test.A64Hello1LevelsB.h1W_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms h1W_of

/--
info: 'Spike.Test.A64Hello1LevelsB.hello1_correctKLS_levelsB' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hello1_correctKLS_levelsB

end Spike.Test.A64Hello1LevelsB
