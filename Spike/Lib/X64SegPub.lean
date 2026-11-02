/-
**The source's publication as a stutter on x86-64** (no AArch64 twin): the
segment-side half of the publication that `NodesA.out`'s `PubOut` disjunct
admits (the consumer-side half: `X64ConsumerA.instr_stepA`,
`instr_stepAH`, `core_stepA` through `pub_preA`, and `preJA_pub` in
`Spike/Lib/X64ConsumerAPubKeep.lean`).

Where x86-64 differs from AArch64: AArch64's `wc_rodata` has a `dmb ishst`
after its two exchanges, a fence node at which the source takes its
publication (`Out.fence`, `FenceRun.pub` under `MemSide.pub`). x86-64 lowers
that fence to a comment (no instruction under TSO), so there is no fence
node; the source publishes where the target takes an ordinary instruction,
as a source-only step before that instruction's row.

- `pubStep_of_publish`, `pubStep_of_intoRgn`: a control at `let x = publish a
  in e` (resp. `intoRgn r a`) with no hold, `a` evaluating to a type the
  publication retypes, takes the publication (`PubStep .st`).
- `out_of_pub`: a row past the publication, at a control of the fragment,
  is `NodesA.out`'s (`PubOut`), off a system call where the arena admits it.
- `pubOff`, `pub_order`: the node of hello's publication, `.Lwc_rodata.x15 +
  62` (`rpB4`'s first instruction), is after both of `wc_rodata`'s stores
  (`.x15 + 29` and `.x15 + 58`, `rpIn`) and before its `ret` (`rpB4`'s last
  instruction), with no store in between.
-/
import Spike.Lib.X64ConsumerA
import Spike.Lib.X64HelloRodata

namespace Spike.Lib.X64SegPub

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.X64.Parser Spike.Lib Spike.Lib.X64
open Scc.Sem Scc.Sem.X64
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA

/-! ## The publication step -/

/-- **A control at a `publish` takes the publication** (`PubStep .st`): no
hold, the published atom evaluating to a type `pubTy` retypes. -/
theorem pubStep_of_publish {c : Ctl} {x : String} {a : At} {e : Expr} {t t' : Ty} {ws : List TermRun.Word}
    (ht : c.term = .let_ x (.publish a) e) (hh : c.hold = none) (hev : TermRun.evalAt c.env a = some (t, ws))
    (hty : pubTy t = some t') :
    PubStep .st c ⟨e, (x, t', ws) :: c.env, none⟩ :=
  ⟨.inl rfl, hh, x, a, e, t, t', ws, .inl ⟨ht, hty⟩, hev, rfl⟩

/-- **A control at an `intoRgn` takes the publication** (`PubStep .st`): no
hold, the moved atom evaluating to a type `rgnTy` retypes. -/
theorem pubStep_of_intoRgn {c : Ctl} {x : String} {r : _} {a : At} {e : Expr} {t t' : Ty}
    {ws : List TermRun.Word} (ht : c.term = .let_ x (.intoRgn r a) e) (hh : c.hold = none)
    (hev : TermRun.evalAt c.env a = some (t, ws)) (hty : rgnTy t = some t') :
    PubStep .st c ⟨e, (x, t', ws) :: c.env, none⟩ :=
  ⟨.inl rfl, hh, x, a, e, t, t', ws, .inr ⟨r, ht, hty⟩, hev, rfl⟩

/-! ## The row past the publication -/

variable {Λ : Scc.Sem.Layout} {p : Prog} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : OwnS} {ar : Arena} {I : InvS} {ab : Option (State → Prop)}

/-- **A row past the publication is `NodesA.out`'s**: off a system call,
where the arena admits the publication, a control `c` publishing into a
control `c₁` of the fragment at the same frames, with a row from `c₁`. -/
theorem out_of_pub {lbl : Lbl} {lsize : Lsize} {s : State} {c c₁ : Ctl} {fs : List TermRun.Frame}
    (hns : abi.atSys s = false) (hp : ar.pub) (hps : PubStep .st c c₁) (hI₁ : I lbl lsize s c₁ fs)
    (h : OutS p lbl (msOfAX Λ μ p rd G own ar I ab lbl lsize) (Pend p (I lbl lsize)) s c₁ fs) :
    OutS p lbl (msOfAX Λ μ p rd G own ar I ab lbl lsize) (Pend p (I lbl lsize)) s c fs ∨
      PubOut Λ p μ rd G own ar I ab lbl lsize s c fs :=
  .inr ⟨hns, hp, c₁, hps, hI₁, h⟩

/-- Past the publication, the row's start is `PubPre`'s second case. -/
theorem pubPre_of_pub {lbl : Lbl} {lsize : Lsize} {s : State} {c c₁ : Ctl} {fs : List TermRun.Frame}
    (hns : abi.atSys s = false) (hp : ar.pub) (hps : PubStep .st c c₁) (hI₁ : I lbl lsize s c₁ fs) :
    PubPre ar I lbl lsize s c c₁ fs :=
  .inr ⟨hns, hp, hps, hI₁⟩

/-! ## Where hello publishes -/

open Spike.Lib.X64.Flow.Hello1 (rpB4)
open Spike.Lib.X64.Flow.HelloRd (rpIn)

/-- **The node of hello's publication**: `.Lwc_rodata.x15 + 62`, the first
instruction of `wc_rodata`'s last block (`rpB4`). -/
abbrev pubOff : Nat := 62

/-- **Hello's publication is ordered after both stores and before the
return**: in `helloCells`, `.x15`'s blocks are `rpIn`'s (the first store at
`+29`, of 3 bytes; the second at `+58`, of 4 bytes; `rpB4` at `pubOff`), so
both stores end at or before `pubOff`, the second right before it; `rpB4`
holds neither store, and its last instruction is the `ret`. -/
theorem pub_order :
    rpIn SccCode.helloCells = true ∧ 29 + 3 ≤ pubOff ∧ 58 + 4 = pubOff ∧
      (∀ d ∈ rpB4, d.1 ≠ stDir .rcx 0 .rax ∧ d.1 ≠ stDir .rcx 8 .rax) ∧
      (rpB4.drop (rpB4.length - 1)).map Prod.fst = parse("ret") := by
  refine ⟨Spike.Lib.X64.Flow.HelloRd.hello_rpIn, by decide, by decide, ?_, by decide⟩
  decide

end Spike.Lib.X64SegPub

/-- info: 'Spike.Lib.X64SegPub.pubStep_of_publish' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64SegPub.pubStep_of_publish

/-- info: 'Spike.Lib.X64SegPub.pubStep_of_intoRgn' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64SegPub.pubStep_of_intoRgn

/-- info: 'Spike.Lib.X64SegPub.out_of_pub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64SegPub.out_of_pub

/-- info: 'Spike.Lib.X64SegPub.pubPre_of_pub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64SegPub.pubPre_of_pub

/-- info: 'Spike.Lib.X64SegPub.pub_order' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64SegPub.pub_order
