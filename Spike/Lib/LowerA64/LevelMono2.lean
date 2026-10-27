/-
**The nodes and frame conditions at a larger level** (AArch64): a node's
invariant, a callee's frame condition or the frames' placement, stated at
the level `(lbl, lsize)`, holds at any level above it (`LvlLe`,
`Spike/Lib/Src/LevelMono2.lean`), in particular at a fresh allocation's
(`lvlLe_upd`). The twin of `Spike/Lib/LowerX64/LevelMono2.lean`.

- `bodyN2_mono`, `pendN2_mono`, `abortN2_mono`, `RetJ2.mono`, `retN2_mono`,
  `retNB_mono`, `csN2_mono`, `retCN2_mono`, `exN2_mono`: the nodes' invariants
  (`csN2`'s and `retCN2`'s facts `Q` weakened alongside);
- `CalleeF2.mono`: the callee's frame condition;
- `wordPlaceRep_mono_lbl`, `PlacedS.mono_lbl`, `FramesPlaced.mono_lbl`,
  `FramesPlacedInI.mono_lbl`: the frames' placement at more placed labels.
-/
import Spike.Lib.Src.LevelMono2
import Spike.Lib.LowerA64.CallC2
import Spike.Lib.A64FramesPlacedI

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.Form (NodeJE SEnv)
open Spike.Lib.LowerNode

variable {p : Prog} {lbl lbl' : WeakMem.AllocLabel → Option Nat} {lsize lsize' : WeakMem.AllocLabel → Nat}
  {σ : AS} {c : Ctl}

/-! ## The nodes -/

/-- **A body node at a larger level.** -/
theorem bodyN2_mono (hv : LvlLe lbl lsize lbl' lsize') {i : Expr → String → Nat → Option Nat} {cx : FnCtx}
    {fp ra : BitVec 64} {c0 : Ctl} {pc : Int64} {t : Expr} {s : SEnv} {lits : List (String × Scc.Lower.LitV)}
    {cs bufs : List (String × Nat)} (h : (bodyN2 p lbl lsize i cx fp ra c0 pc t s lits cs bufs).J σ c) :
    (bodyN2 p lbl' lsize' i cx fp ra c0 pc t s lits cs bufs).J σ c :=
  let ⟨⟨L, sm, B, hj⟩, hf, hr, hs⟩ := h
  ⟨⟨L, sm, B, hj.mono hv⟩, hf, hr, hs.mono_lbl hv.1⟩

/-- **A pending store at a larger level.** -/
theorem pendN2_mono (hv : LvlLe lbl lsize lbl' lsize') {i : Expr → String → Nat → Option Nat} {cx : FnCtx}
    {fp ra : BitVec 64} {c0 : Ctl} {pc : Int64} {t : Expr} {s : SEnv} {lits : List (String × Scc.Lower.LitV)}
    {cs bufs : List (String × Nat)} {k : Int} (h : (pendN2 p lbl lsize i cx fp ra c0 pc t s lits cs bufs k).J σ c) :
    (pendN2 p lbl' lsize' i cx fp ra c0 pc t s lits cs bufs k).J σ c :=
  let ⟨⟨L, sm, B, hj⟩, hf, hr, hs⟩ := h
  ⟨⟨L, sm, B, hj.mono hv⟩, hf, hr, hs.mono_lbl hv.1⟩

/-- **The overflow abort label at more placed labels.** -/
theorem abortN2_mono (hl : ∀ l b, lbl l = some b → lbl' l = some b) {i : Expr → String → Nat → Option Nat}
    {T : Expr → Prop} {cx : FnCtx} {lab : Label → Int64} {fp ra : BitVec 64} {c0 : Ctl}
    (h : (abortN2 i T p lbl cx lab fp ra c0).J σ c) : (abortN2 i T p lbl' cx lab fp ra c0).J σ c :=
  let ⟨⟨⟨s, lits, ha, he, hi, ht⟩, hf⟩, hr⟩ := h
  ⟨⟨⟨s, lits, ha.mono_lbl hl, he, hi, ht⟩, hf⟩, hr⟩

/-- **The return's exit at more placed labels.** -/
theorem RetJ2.mono (hl : ∀ l b, lbl l = some b → lbl' l = some b) {fp ra : BitVec 64}
    (h : RetJ2 lbl fp ra σ c) : RetJ2 lbl' fp ra σ c :=
  let ⟨a, t, ws, ht, hh, he, hn, hv, h29, h30⟩ := h
  ⟨a, t, ws, ht, hh, he, hn, fun j hj hr => Scc.Sem.MemRel.valRep_mono hl (hv j hj hr), h29, h30⟩

/-- **The return's exit node at more placed labels.** -/
theorem retN2_mono (hl : ∀ l b, lbl l = some b → lbl' l = some b) {fp ra : BitVec 64} {c0 : Ctl}
    (h : (retN2 p lbl fp ra c0).J σ c) : (retN2 p lbl' fp ra c0).J σ c :=
  ⟨h.1.mono hl, h.2⟩

/-- **The return's exit with `RetL` at more placed labels.** -/
theorem retNB_mono (hl : ∀ l b, lbl l = some b → lbl' l = some b) {fp ra : BitVec 64} {c0 : Ctl} {ty : Ty}
    (h : (retNB p lbl fp ra c0 ty).J σ c) : (retNB p lbl' fp ra c0 ty).J σ c :=
  ⟨⟨h.1.1.mono hl, h.1.2⟩, h.2⟩

/-- **A call-site node at more placed labels**, its facts `Q` weakened. -/
theorem csN2_mono (hl : ∀ l b, lbl l = some b → lbl' l = some b) {cx : FnCtx} {fp ra : BitVec 64}
    {tp : UInt64} {Q Q' Rn : Ctl → Prop} (hQ : ∀ c, Q c → Q' c) {pc : Int64} {t : Expr} {s : SEnv}
    {P : AS → Prop} (h : (csN2 lbl cx fp ra tp Q Rn pc t s P).J σ c) :
    (csN2 lbl' cx fp ra tp Q' Rn pc t s P).J σ c :=
  let ⟨hj, hq, hf, hr, htp, hp⟩ := h
  ⟨Spike.Lib.Form.NodeJE.mono_lbl hl hj, hQ c hq, hf, hr, htp, hp⟩

/-- **Back from the callee at more placed labels**, its facts `Q`
weakened. -/
theorem retCN2_mono (hl : ∀ l b, lbl l = some b → lbl' l = some b) {cx : FnCtx} {fp ra : BitVec 64}
    {tp : UInt64} {c0 : Ctl} {fs : List TermRun.Frame} {Q Q' : Ctl → Prop} (hQ : ∀ c, Q c → Q' c) {pc : Int64}
    {e : Expr} {s : SEnv} {off : Int} (h : (retCN2 p lbl cx fp ra tp c0 fs Q pc e s off).J σ c) :
    (retCN2 p lbl' cx fp ra tp c0 fs Q' pc e s off).J σ c :=
  let ⟨hj, hq, hf, hr, htp⟩ := h
  ⟨Spike.Lib.Form.NodeJE.mono_lbl hl hj, hQ c hq, hf, hr, htp⟩

/-- **The callee's exit at more placed labels.** -/
theorem exN2_mono (hl : ∀ l b, lbl l = some b → lbl' l = some b) {tp : UInt64} {fs : List TermRun.Frame}
    {q : CallG} {frm : TermRun.Frame} {c0' : Ctl} (h : (exN2 p lbl tp fs q frm c0').J σ c) :
    (exN2 p lbl' tp fs q frm c0').J σ c :=
  ⟨h.1, retNB_mono hl h.2.1, h.2.2⟩

/-! ## The callee's frame condition -/

/-- **The callee's frame condition at a larger level.** -/
theorem CalleeF2.mono (hv : LvlLe lbl lsize lbl' lsize') {cx : FnCtx} {R : Region} {F : MachineData → Prop}
    {D : Int} {fp ra : BitVec 64} {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {q : CallG}
    {frm : TermRun.Frame} {F' : MachineData → Prop} (h : CalleeF2 p lbl lsize cx R F D fp ra i T q frm F') :
    CalleeF2 p lbl' lsize' cx R F D fp ra i T q frm F' := fun m hm =>
  let ⟨hF, hc, mC, σC, c, t, s, ha, hk, hct, ht, hj, ⟨lits, cs, bufs, he⟩, hf, hfv, hreg, hi⟩ := h m hm
  ⟨hF, hc, mC, σC, c, t, s, ha, hk, hct, ht, Spike.Lib.Form.NodeJE.mono_lbl hv.1 hj,
    ⟨lits, cs, bufs, he.mono hv.2⟩, hf, hfv, hreg, hi⟩

end Spike.Lib.LowerA64

/-! ## The frames' placement at more placed labels -/

namespace Spike.Lib.A64ConsumerS

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer

variable {Λ : Scc.Sem.Layout} {lbl lbl' : Lbl} {s : State} {c : Ctl} {fs : List TermRun.Frame}

/-- **A word place's representation at more placed labels.** -/
theorem wordPlaceRep_mono_lbl {M : ExtMachine} (hl : ∀ l b, lbl l = some b → lbl' l = some b)
    {st : M.I.State} {wp : WordPlace M.I.RegId} {x : WeakMem.Val} (h : WordPlaceRep M lbl st wp x) :
    WordPlaceRep M lbl' st wp x := by
  cases wp with
  | one pl =>
    obtain ⟨v, hv, hr⟩ := h
    exact ⟨v, hv, MemRel.valRep_mono hl hr⟩
  | loc pb po =>
    obtain ⟨vb, vo, hb, ho, hr⟩ := h
    refine ⟨vb, vo, hb, ho, ?_⟩
    cases x with
    | loc a g => exact ⟨hr.1, hl _ _ hr.2.1, hr.2.2⟩
    | _ => exact hr
  | imm n => exact MemRel.valRep_mono hl h

/-- **Every frame placed at more placed labels.** -/
theorem PlacedS.mono_lbl (hl : ∀ l b, lbl l = some b → lbl' l = some b) (h : PlacedS Λ lbl s c fs) :
    PlacedS Λ lbl' s c fs :=
  let ⟨envm, hrep, htot, himm⟩ := h
  ⟨envm, fun d env hd x ty ws hx k wd wp hwd hwp => wordPlaceRep_mono_lbl hl (hrep d env hd x ty ws hx k wd wp hwd hwp),
    htot, himm⟩

/-- **The suspended frames placed at more placed labels.** -/
theorem FramesPlaced.mono_lbl (hl : ∀ l b, lbl l = some b → lbl' l = some b) (h : FramesPlaced Λ lbl s fs) :
    FramesPlaced Λ lbl' s fs :=
  let ⟨envm, hrep, htot, himm⟩ := h
  ⟨envm, fun d f hf x ty ws hx k wd wp hwd hwp => wordPlaceRep_mono_lbl hl (hrep d f hf x ty ws hx k wd wp hwd hwp),
    htot, himm⟩

/-- **The suspended frames placed in slots or immediates at more placed
labels.** -/
theorem FramesPlacedInI.mono_lbl {A : Nat → Prop} (hl : ∀ l b, lbl l = some b → lbl' l = some b)
    (h : FramesPlacedInI Λ lbl s fs A) : FramesPlacedInI Λ lbl' s fs A :=
  let ⟨envm, hrep, htot, hin, himm⟩ := h
  ⟨envm, fun d f hf x ty ws hx k wd wp hwd hwp => wordPlaceRep_mono_lbl hl (hrep d f hf x ty ws hx k wd wp hwd hwp),
    htot, hin, himm⟩

end Spike.Lib.A64ConsumerS

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.bodyN2_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.bodyN2_mono

/-- info: 'Spike.Lib.LowerA64.CalleeF2.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.CalleeF2.mono

/-- info: 'Spike.Lib.A64ConsumerS.PlacedS.mono_lbl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64ConsumerS.PlacedS.mono_lbl
