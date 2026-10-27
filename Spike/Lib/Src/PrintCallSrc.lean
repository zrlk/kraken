/-
**The output extern's declarations in an `Accepted2` program**
(ISA-neutral): the source block a call of `print` runs.

`decl2` (`Scc/Lower/Spec2.lean`) asks the extern to be textually
`printExtD` (`declIs`) and block names to be distinct, so in a program
with the extern (`hasPrint`) the block named `print` is `printExtD`; its
loop by name is `printLoopD` (`printL_of_ext`, `SrcNum.lean`).

- `printLD_eq`, `printBody_eq`, `sliceTy_eq`: `Spike/Lib/PrintSrc.lean`'s
  copies of the model are `Scc/PrintModel.lean`'s;
- `mem_of_nodup_name`: distinct names pick one block;
- `printExt_mem`, `printDecl_of_accepted2`: the block named `print` is
  `printExtD`; `printL_of_accepted2`: its loop is `PrintSrc.printLD`;
- the source's runs at a call of `print` (`FrameRun`, the frame pushed
  returning into `x` and then `e`): `printCall_enter` (a nonempty slice:
  the call and `print`'s body to the loop's top, `PrintC … 0`),
  `printCall_empty` (an empty slice: the call, `print`'s body to `ret ()`
  and the return, `x` bound to `()`), `printCall_exit` (the loop done,
  `PrintC … (printN n m)`: `printL` to `ret ()` and the return).
-/
import Spike.Lib.Src.SrcNum
import Spike.Lib.SegS

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc.Lower (Accepted2 hasPrint decl2 setupOf shapeOf)
open Spike.Lib (FrameStep FrameRun)

theorem printLD_eq : Spike.Lib.PrintSrc.printLD = Scc.Frontend.printLoopD := rfl

theorem printBody_eq : Spike.Lib.PrintSrc.printBody = Scc.Frontend.printBody := rfl

theorem sliceTy_eq : Spike.Lib.Hello1Src.sliceTy = Scc.Frontend.ownSliceTy := rfl

/-- **Distinct names pick one block.** -/
theorem mem_of_nodup_name : ∀ {p : Prog}, (p.map (·.name)).Nodup → ∀ {d d' : Decl}, d ∈ p → d' ∈ p →
    d.name = d'.name → d = d'
  | [], _, _, _, hd, _, _ => absurd hd List.not_mem_nil
  | q :: ps, hnd, d, d', hd, hd', hn => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp hd with e | hd <;> rcases List.mem_cons.mp hd' with e' | hd'
    · rw [e, e']
    · exact absurd ⟨d', hd', by rw [← hn, e]⟩ hnd.1
    · exact absurd ⟨d, hd, by rw [hn, e']⟩ hnd.1
    · exact mem_of_nodup_name hnd.2 hd hd' hn

/-- **The extern is a block** of an `Accepted2` program with the extern. -/
theorem printExt_mem {p : Prog} (hacc : Accepted2 p = true) (hP : hasPrint p = true) :
    Scc.Frontend.printExtD ∈ p := by
  obtain ⟨d, hd, hpe⟩ := List.any_eq_true.1 hP
  obtain ⟨hds, -⟩ := accepted2_parts hacc
  obtain ⟨E, hE, -⟩ := decl2_of_decls2' hds d hd
  unfold decl2 at hE
  simp only [hpe, ite_true, Bool.and_eq_true] at hE
  rw [← Scc.Frontend.declIs_eq hE.1]
  exact hd

/-- **The block named `print`** of an `Accepted2` program with the extern
is `printExtD`. -/
theorem printDecl_of_accepted2 {p : Prog} (hacc : Accepted2 p = true) (hP : hasPrint p = true) :
    p.find? (·.name == "print") = some Scc.Frontend.printExtD := by
  have hm := printExt_mem hacc hP
  have hnd : (p.map (·.name)).Nodup := by
    simp only [Accepted2, Bool.and_eq_true, decide_eq_true_eq] at hacc
    exact hacc.1.1.1.1.1.1.1.1.1
  cases h : p.find? (·.name == "print") with
  | none => exact absurd (List.find?_eq_none.1 h _ hm) (by decide)
  | some d =>
    obtain ⟨hd, hn⟩ := find_name h
    rw [mem_of_nodup_name hnd hd hm (by rw [hn]; rfl)]

/-- **The extern's loop by name** is `PrintSrc.printLD`. -/
theorem printL_of_accepted2 {p : Prog} (hacc : Accepted2 p = true)
    (hset : ∀ s, setupOf p = some s → Compat s (shapeOf s) = true) (hP : hasPrint p = true) :
    p.find? (·.name == "printL") = some Spike.Lib.PrintSrc.printLD :=
  printL_of_ext hacc hset (printExt_mem hacc hP)

/-! ## The source's runs at a call of `print` -/

open Spike.Lib.PrintSrc (PrintC printN printLD printArgs topEnv print_entry_run printC_entry print_done_run)

/-- The frame a call `let x = print(a) in e` pushes from `c`. -/
def printFrame (x : String) (e : Expr) (c : Ctl) : TermRun.Frame := ⟨x, e, c.env, [], .unit⟩

/-- The top of `printL` at word 0, byte 0 (`print_entry_run`'s end). -/
def printTop0 (pw wn : TermRun.Word) (m : Nat) : Ctl :=
  ⟨Spike.Lib.PrintSrc.printLBody, topEnv (printArgs pw wn 0 (m - 1) 0 0), none⟩

variable {p : Prog}

/-- **The call of `print`** pushes `printFrame` and enters `printExtD`'s
body at the slice's words. -/
theorem printCall_step {c : Ctl} {fs : List TermRun.Frame} {x : String} {is : List String} {a : At} {e : Expr}
    {t : Ty} {ws : List TermRun.Word} (hp : p.find? (·.name == "print") = some Scc.Frontend.printExtD)
    (ht : c.term = .let_ x (.call "print" is a []) e) (ha : TermRun.evalAt c.env a = some (t, ws)) :
    FrameStep p (c, fs) (⟨Spike.Lib.PrintSrc.printBody, [("a", Spike.Lib.Hello1Src.sliceTy, ws)], none⟩,
      printFrame x e c :: fs) :=
  FrameStep.call ht hp ha

/-- **A nonempty slice**: the call and `print`'s body run to the top of
`printL` at word 0, byte 0, there `PrintC … 0`. -/
theorem printCall_enter {c : Ctl} {fs : List TermRun.Frame} {x : String} {is : List String} {a : At} {e : Expr}
    {t : Ty} {pw wm wn : TermRun.Word} {n m : Nat}
    (hp : p.find? (·.name == "print") = some Scc.Frontend.printExtD) (hL : p.find? (·.name == "printL") = some printLD)
    (ht : c.term = .let_ x (.call "print" is a []) e) (ha : TermRun.evalAt c.env a = some (t, [pw, wm, wn]))
    (hwm : wm.val = .num m) (hm0 : m ≠ 0) (hwn : wn.val = .num n) :
    FrameRun p (c, fs) (printTop0 pw wn m, printFrame x e c :: fs) ∧ PrintC pw wn n m 0 (printTop0 pw wn m) :=
  ⟨.step (printCall_step hp ht ha) (FrameRun.ofLocalS (print_entry_run hL hwm hm0) _), printC_entry hwn hm0⟩

/-- **`ret ()` into the frame of a call of `print`** binds `x` to `()`. -/
theorem printCall_ret {c : Ctl} {x : String} {e : Expr} {c0 : Ctl} {fs : List TermRun.Frame}
    (ht : c.term = .ret .unit) :
    FrameStep p (c, printFrame x e c0 :: fs) (⟨e, (x, .unit, []) :: c0.env, none⟩, fs) :=
  FrameStep.ret (t := .unit) ht rfl rfl

/-- **An empty slice**: the call, `print`'s body to `ret ()` (`m = 0`) and
the return, `x` bound to `()`. -/
theorem printCall_empty {c : Ctl} {fs : List TermRun.Frame} {x : String} {is : List String} {a : At} {e : Expr}
    {t : Ty} {pw wm wn : TermRun.Word}
    (hp : p.find? (·.name == "print") = some Scc.Frontend.printExtD)
    (ht : c.term = .let_ x (.call "print" is a []) e) (ha : TermRun.evalAt c.env a = some (t, [pw, wm, wn]))
    (hwm : wm.val = .num 0) :
    FrameRun p (c, fs) (⟨e, (x, .unit, []) :: c.env, none⟩, fs) := by
  have hr : ∃ env, LocalRunS p ⟨Spike.Lib.PrintSrc.printBody, [("a", Spike.Lib.Hello1Src.sliceTy, [pw, wm, wn])], none⟩
      ⟨.ret .unit, env, none⟩ :=
    ⟨_, .step (localStepS_split rfl rfl rfl) <| .step (localStepS_split rfl rfl rfl) <|
      .single (localStepS_ifeq_eq rfl rfl rfl hwm rfl)⟩
  obtain ⟨env, hr⟩ := hr
  exact .step (printCall_step hp ht ha) ((FrameRun.ofLocalS hr _).trans (.single (printCall_ret rfl)))

/-- **The loop done**: from `PrintC … (printN n m)` in a call of `print`,
`printL` runs to `ret ()` and returns, `x` bound to `()`. -/
theorem printCall_exit {c c0 : Ctl} {fs : List TermRun.Frame} {x : String} {e : Expr} {pw wn : TermRun.Word}
    {n m : Nat} (h : PrintC pw wn n m (printN n m) c) :
    FrameRun p (c, printFrame x e c0 :: fs) (⟨e, (x, .unit, []) :: c0.env, none⟩, fs) := by
  obtain ⟨env, hr⟩ := print_done_run (p := p) h
  exact (FrameRun.ofLocalS hr _).trans (.single (printCall_ret rfl))

/-- info: 'Spike.Lib.LowerNode.printDecl_of_accepted2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms printDecl_of_accepted2

/-- info: 'Spike.Lib.LowerNode.printCall_enter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms printCall_enter

/-- info: 'Spike.Lib.LowerNode.printCall_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms printCall_empty

/-- info: 'Spike.Lib.LowerNode.printCall_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms printCall_exit

end Spike.Lib.LowerNode
