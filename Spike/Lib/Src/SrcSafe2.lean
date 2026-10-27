import Spike.Lib.Src.SrcB
import Spike.Lib.Seg
import Spike.Test.Hello1MainSrc

/-!
**The source safety of an `Accepted2` program** (`SrcSafeS`, both ISAs),
from the starts before the setup block, with no hook.

- `blocks_of_decls2`: every block of an `Accepted2` program is the output
  extern, its loop, or a `body2` body from no buffer;
- `blocksB_of_accepted2`, `progNoS_acq_of_accepted2`: so every block is E or
  W from no buffer (`BlocksB`), and none has an acquire load, a release store
  or a spawn;
- `cfgB_setupStart`: the starts keep the invariant;
- `CfgB.xchg`: an exchange site of a thread has a message at its cell;
- `reach_cfgB_accepted2`: every reachable configuration keeps the invariant;
- `hello1o_accepted2`: `hello1L.w`'s program is `Accepted2`.

The source safety itself is per ISA (`SrcSafe2A`, `SrcSafe2X`).
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm A9NoSpawn TermRun Scc.Sem
open Scc.Lower (body2 unbuf constOf Accepted2 decl2 decls2)

/-! ## The blocks of an `Accepted2` program -/

/-- **A block of `decl2`**: the extern, its loop, or a `body2` body from no buffer. -/
theorem block_of_decl2 {E : List String} {s : Option Ty} {x : Bool} {d : Decl} (h : decl2 E s x d = true) :
    (d = Scc.Frontend.printExtD ∨ d = Scc.Frontend.printLoopD) ∨
      ∃ cx scope, body2 cx [] [] scope d.body = true := by
  unfold decl2 at h
  split at h
  · simp only [Bool.and_eq_true] at h
    exact Or.inl (Or.inl (Scc.Frontend.declIs_eq h.1))
  · split at h
    · exact Or.inl (Or.inr (Scc.Frontend.declIs_eq h))
    · split at h
      · simp only [Scc.Lower.main2, Bool.and_eq_true] at h
        exact Or.inr ⟨_, _, h.2⟩
      · split at h
        · split at h
          · simp only [Scc.Lower.setup2, Bool.and_eq_true] at h
            exact Or.inr ⟨_, _, h.2⟩
          · simp only [Scc.Lower.plain2, Bool.and_eq_true] at h
            exact Or.inr ⟨_, _, h.2⟩
        · simp only [Scc.Lower.plain2, Bool.and_eq_true] at h
          exact Or.inr ⟨_, _, h.2⟩

theorem blocks_of_accepted2 {p : Prog} (hp : Accepted2 p = true) :
    ∀ d ∈ p, (d = Scc.Frontend.printExtD ∨ d = Scc.Frontend.printLoopD) ∨
      ∃ cx scope, body2 cx [] [] scope d.body = true := by
  intro d hd
  simp only [Accepted2, Bool.and_eq_true] at hp
  obtain ⟨E, hE⟩ := decl2_of_decls2 hp.1.1.1.1.1.1.1.2 d hd
  exact block_of_decl2 hE

theorem printExt_noX : NoS XOp Scc.Frontend.printExtD.body := by
  simp [Scc.Frontend.printExtD, Scc.Frontend.printBody, NoS, XOp]

theorem printLoop_noX : NoS XOp Scc.Frontend.printLoopD.body := by
  simp [Scc.Frontend.printLoopD, Scc.Frontend.printLBody, Scc.Frontend.printAdv, Scc.Frontend.printNext, NoS,
    XOp]

theorem printExt_noAcq : NoS AcqOp Scc.Frontend.printExtD.body := by
  simp [Scc.Frontend.printExtD, Scc.Frontend.printBody, NoS, AcqOp]

theorem printLoop_noAcq : NoS AcqOp Scc.Frontend.printLoopD.body := by
  simp [Scc.Frontend.printLoopD, Scc.Frontend.printLBody, Scc.Frontend.printAdv, Scc.Frontend.printNext, NoS,
    AcqOp]

/-- **An `Accepted2` body has no acquire load, release store nor spawn.** -/
theorem noS_acq_of_body2 : ∀ (e : Expr) {cx : Scc.Lower.Cx2} {cs bufs : List (String × Nat)}
    {scope : List String}, body2 cx cs bufs scope e = true → NoS AcqOp e := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro cx cs bufs scope h
    refine ⟨fun ha => ?_, ?_⟩
    · cases op <;> simp only [AcqOp] at ha <;> simp [body2] at h
    · cases op
      case newBuf n τ =>
        simp only [body2, Bool.and_eq_true] at h
        obtain ⟨-, hm⟩ := h
        split at hm
        · simp only [Bool.and_eq_true] at hm
          exact ih hm.2
        · simp at hm
      case xchgAt b i v =>
        cases b <;> cases i <;> simp only [body2, Bool.and_eq_true, Bool.false_eq_true] at h
        exact ih h.2
      all_goals first
        | (simp [body2] at h; done)
        | (simp only [body2, Bool.and_eq_true] at h; exact ih h.2)
  | split a x y e ih =>
    intro cx cs bufs scope h
    simp only [body2, Bool.and_eq_true] at h
    exact ih h.2
  | unpack a i x e ih =>
    intro cx cs bufs scope h
    simp only [body2, Bool.and_eq_true] at h
    exact ih h.2
  | ifeq a b yes no ihy ihn =>
    intro cx cs bufs scope h
    simp only [body2, Bool.and_eq_true] at h
    exact ⟨ihy h.1.2, ihn h.2⟩
  | ret a => intro _ _ _ _ _; trivial
  | _ => intro _ _ _ _ h; simp [body2] at h

/-- **Every block of an `Accepted2` program is E or W from no buffer.** -/
theorem blocksB_of_accepted2 {p : Prog} (hp : Accepted2 p = true) : BlocksB p := by
  intro d hd
  rcases blocks_of_accepted2 hp d hd with (rfl | rfl) | h
  · exact Or.inl printExt_noX
  · exact Or.inl printLoop_noX
  · exact Or.inr h

/-- **No block of an `Accepted2` program has an acquire load, a release store or a spawn.** -/
theorem progNoS_acq_of_accepted2 {p : Prog} (hp : Accepted2 p = true) : ProgNoS AcqOp p := by
  intro d hd
  rcases blocks_of_accepted2 hp d hd with (rfl | rfl) | ⟨cx, scope, h⟩
  · exact printExt_noAcq
  · exact printLoop_noAcq
  · exact noS_acq_of_body2 _ h

/-! ## The starts -/

theorem cfgB_setupStart {cap : Nat} {c : Cfg} (h : ∃ meW, c = Scc.Sem.SrcSem.setupStart cap meW) :
    CfgB c := by
  obtain ⟨meW, rfl⟩ := h
  intro j th hj
  have : j = 0 := by
    rcases j with _ | j
    · rfl
    · simp [Scc.Sem.SrcSem.setupStart] at hj
  subst this
  simp only [Scc.Sem.SrcSem.setupStart, List.getElem?_toArray, List.getElem?_cons_zero,
    Option.some.injEq] at hj
  subst hj
  exact ⟨Or.inr (by simp [Scc.Sem.SrcSem.setupTerm, NoS, XOp]), by simp⟩

/-! ## The exchange's cell -/

/-- **The cell of an exchange site has a message**, at a W frame: `body2`
admits only `xchgAt` on a buffer of `bufs` at a literal below its count. -/
theorem WB.xchgSite_cell {sm : WeakMem.Memory} {c : Ctl} (h : WB sm c.term c.env) {x : String}
    {sa : WeakMem.Address} {u : Ty} {v : At} {e : Expr} (hs : XchgSite c x sa u v e) : HasCell sm sa := by
  obtain ⟨cx, cs, bufs, scope, hb, ⟨⟨_, hB⟩, -⟩, -⟩ := h
  rcases hs.2 with ⟨a, t, pw, μ, ht, -⟩ | ⟨b', i', t, pw, ti, iws, μ, sb, k, ht, heb, hpw, -, hei, hk, rfl⟩
  · rw [ht] at hb; simp [body2] at hb
  · rw [ht] at hb
    cases b' with
    | var b =>
      cases i' with
      | lit i =>
        simp only [body2, Bool.and_eq_true] at hb
        obtain ⟨⟨⟨-, hn⟩, -⟩, -⟩ := hb
        cases hl : bufs.lookup b with
        | none => rw [hl] at hn; simp at hn
        | some n =>
          rw [hl] at hn
          simp only [decide_eq_true_eq] at hn
          obtain ⟨t0, u0, lbl, he, -, -, -, hc, -⟩ := hB b n hl
          simp only [TermRun.evalAt, he, Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at heb
          obtain ⟨-, rfl⟩ := heb
          simp only [TermRun.evalAt, Option.some.injEq, Prod.mk.injEq] at hei
          obtain ⟨-, rfl⟩ := hei
          simp only [TermRun.numOf, TermRun.cst, Promises.TVal.mk0, Option.some.injEq] at hk
          subst hk
          simp only [TermRun.cst, Promises.TVal.mk0, WeakMem.Val.loc.injEq, and_true] at hpw
          subst hpw
          have ho : TermRun.offs ⟨lbl, 0⟩ i = ⟨lbl, i⟩ := by simp [TermRun.offs]
          rw [ho]
          exact hc i hn
      | _ => simp [body2] at hb
    | _ => simp [body2] at hb

/-- **An exchange site of a thread has a message at its cell.** -/
theorem CfgB.xchg {c : Cfg} (h : CfgB c) {i : Nat} {th : TTh} (hi : c.ths[i]? = some th)
    {hd : Option (Nat × Word)} {x : String} {sa : WeakMem.Address} {u : Ty} {v : At} {e : Expr}
    (hs : XchgSite ⟨th.term, th.env, hd⟩ x sa u v e) : HasCell c.mem sa := by
  rcases (h i th hi).1 with hw | hn
  · exact WB.xchgSite_cell (c := ⟨th.term, th.env, hd⟩) hw hs
  · exfalso
    rcases hs.2 with ⟨a, t, pw, μ, ht, -⟩ | ⟨b', i', t, pw, ti, iws, μ, sb, k, ht, -⟩ <;>
      (change th.term = _ at ht; rw [ht] at hn; exact hn.1 trivial)

/-! ## Every reachable configuration of an `Accepted2` program -/

/-- **Every reachable configuration of an `Accepted2` program**, from the
starts before the setup block with no hook, keeps the invariant and is free of
`AcqOp`. -/
theorem reach_cfgB_accepted2 {P : SrcSem.SrcParams} {p : Prog} (hacc : Accepted2 p = true)
    (hH : P.hooks = SrcSem.SrcHooks.none ∨ SrcOutProto.UsesWc P p)
    (hinit : ∀ c, P.init c → ∃ meW, c = Scc.Sem.SrcSem.setupStart P.cap meW) {tr : List Ev} {s : Cfg}
    (h : (SrcSem.source P p).Reach tr s) : CfgB s ∧ CfgNoS AcqOp s :=
  reach_cfgB (blocksB_of_accepted2 hacc) (progNoS_acq_of_accepted2 hacc) hH
    (fun c hc => ⟨cfgB_setupStart (hinit c hc), setupInit_noAcq (hinit c hc)⟩) h

/-! ## `hello1L.w` -/

set_option maxRecDepth 100000 in
/-- `hello1L.w`'s program is `Accepted2`. -/
theorem hello1o_accepted2 : Accepted2 Spike.Test.Hello1MainSrc.hello1o = true := by decide

end Spike.Lib.LowerNode
