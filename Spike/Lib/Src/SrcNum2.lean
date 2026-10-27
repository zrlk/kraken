import Spike.Lib.Src.SrcNum
import Spike.Lib.Src.NumQLower
import WeakCore.TermK2aLoad
import Scc.Sem.SrcOutProto

/-!
**The source's memory holds numbers** along a run of an `Accepted2`
program: the writes and new messages of a thread step under `ThN` are
numbers (`thN_sw`, `thN_new`), and a one-word exchange reads a message that
is no promise after the step (`xchgAt_reads`), so a number (`MemNP`). The
extern's loop loads only cells with messages (`thN_hcell`: no run from a W
frame or the start's reaches its load, `BodyOK.run`; the extern's frames
carry `LdOK`), so `srcNumS_of_accepted2` needs no cell premise;
`srcNumS_hello1` instantiates it at `hello1L.w`'s program.
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm A9NoSpawn TermRun Scc.Sem
open TermCert (MemExt)
open TermFul (promsOf promsOf_some PWF)
open TermExtStep (extCfg_ths_ne extCfg_mem extCfg_size extCfg_pairs)

section mem

open Scc.Lower (LitV litAt opLit shapeOf params2 litWalk2 litWalks2 simpleTy body2 unbuf constOf bindC elem2 atom1
  mentions termKey2 argShape atKey Accepted2 decl2 setupOf hasPrint mainArgOk)
open Scc.Sem.SrcSem (setupTerm setupStart)

/-! ### The operations -/

/-- The operations that write no memory. -/
def keepOp : Op → Bool
  | .atom _ | .nameI _ | .add _ _ | .sub _ _ | .pair _ _ | .pack _ _ _ | .asLanes _ _ _ | .lane _ _
  | .loadAt _ _ | .ext _ _ => true
  | _ => false

theorem evalOp_keep {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {op : Op}
    (hk : keepOp op = true) (h : (s', t, ws) ∈ evalOp g env σs s op) : s'.mem = s.mem := by
  cases op <;> simp only [keepOp, Bool.false_eq_true] at hk
  case loadAt b i =>
    simp only [evalOp] at h
    repeat' split at h
    all_goals try (simp at h; done)
    simp only [List.mem_map] at h
    obtain ⟨⟨s1, old⟩, h1, he⟩ := h
    cases he
    exact (TermFul.loadUnits_keep _ _ _ _ h1).1
  case ext => simp [evalOp] at h
  all_goals
    simp only [evalOp, ol, Option.mem_toList, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.map_eq_some_iff, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    grind

/-- **An exchange's decomposition**: a load of the element's units, then a
store of the operand's words there. -/
theorem evalOp_xchgAt_inv {g : G} {env : Env} {σs : List Ty} {s s' : St} {b i v : At} {t : Ty}
    {ws : List Word} (h : (s', t, ws) ∈ evalOp g env σs s (.xchgAt b i v)) :
    ∃ pw a' us xs s1, accs t = some us ∧ (s1, ws) ∈ loadUnits g.arch pw a' false us 0 s ∧
      s' ∈ storeUnits g.k g.arch pw a' false us xs 0 s1 := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals try (simp at h; done)
  simp only [List.mem_flatMap, List.mem_map] at h
  obtain ⟨⟨s1, old⟩, h1, s2, h2, he⟩ := h
  cases he
  exact ⟨_, _, _, _, _, by assumption, h1, h2⟩

/-- **A one-word exchange reads a message that is no promise after it**, the
promises after it above its coherence (as certification gives,
`certified_promAbove`): its coherence before the store is below them, or the
store pushed a message above every old one. -/
theorem xchgAt_reads {g : G} {env : Env} {σs : List Ty} {s s' : St} {b i v : At} {t : Ty} {ws : List Word}
    (h : (s', t, ws) ∈ evalOp g env σs s (.xchgAt b i v)) (hu : accs t = some [.one])
    (hc : ∀ t' m, t' ∈ s'.promises → s.mem[t']? = some m → s'.vs.coh m.loc < t') :
    ∃ w t' m, ws = [w] ∧ s.mem[t']? = some m ∧ w.val = m.val ∧ t' ∉ s'.promises := by
  obtain ⟨pw, a', us, xs, s1, hus, h1, h2⟩ := evalOp_xchgAt_inv h
  rw [hu] at hus; cases hus
  have k1 : s1.mem = s.mem := (TermFul.loadUnits_keep _ _ _ _ h1).1
  rcases xs with _ | ⟨w0, xs⟩
  · simp [storeUnits] at h2
  simp only [storeUnits, List.mem_flatMap, List.mem_singleton] at h2
  obtain ⟨⟨mem', th⟩, hst, rfl⟩ := h2
  obtain ⟨t0, hcase, hcoh, -, -⟩ := TermStep.stepStore_casesC hst
  have hP : ∀ t' m, t' ∈ th.promises → s.mem[t']? = some m → s1.vs.coh m.loc < t' := by
    intro t' m ht hm
    have h3 := hc t' m ht hm
    simp only [hcoh, mth] at h3
    split at h3
    · rename_i hl
      rcases hcase with ⟨-, ht0, -⟩ | ⟨-, -, -, hlt, -⟩
      · have h4 : t' < s.mem.size := (Array.getElem?_eq_some_iff.mp hm).1
        rw [ht0, k1] at h3; exact absurd (Nat.lt_trans h3 h4) (Nat.lt_irrefl _)
      · simp only [mth] at hlt; rw [hl]; exact Nat.lt_trans hlt h3
    · exact h3
  have hr := TermK2aLoad.loadUnits_readsR [.one] 0 s (s1, ws) h1 th.promises hP
  simp only [TermK2aLoad.ReadsR, Acc.size] at hr
  obtain ⟨hr1, hr2⟩ := hr
  rcases ws with _ | ⟨w, _ | ⟨w', ws⟩⟩
  · simp [TermK2aLoad.UnitReadR] at hr1
  · obtain ⟨t', m, hm, -, hv, -, hn⟩ := hr1
    exact ⟨w, t', m, rfl, hm, hv, hn⟩
  · simp at hr2

/-! ### The frames' operations -/

/-- **The operation of a `let` the invariant allows**: a W frame's, a pure
one (the extern's), a call, or the start's pair. -/
theorem thN_letOp {p : Prog} (hacc : Accepted2 p = true) {mem : WeakMem.Memory} {th : TTh} (hT : ThN p mem th)
    {x : String} {op : Op} {e : Expr} (hterm : th.term = .let_ x op e) :
    (∃ R, WN p mem R (.let_ x op e) th.env) ∨ pureOp op = true ∨ (∃ g is a ts, op = .call g is a ts) ∨
      ∃ a b, op = .pair a b := by
  obtain ⟨-, R, hF, -⟩ := hT
  rcases hF with ⟨hW, -⟩ | ⟨hE, -⟩ | ⟨hSM | hM, -⟩
  · rw [hterm] at hW; exact Or.inl ⟨R, hW⟩
  · rw [hterm] at hE; simp only [PureE, Bool.and_eq_true] at hE; exact Or.inr (Or.inl hE.1)
  · rcases setupN_cases hSM with h | h | h <;> rw [hterm] at h
    · rw [setupTerm_eq] at h; cases h; exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl⟩))
    · rw [setupRest] at h; cases h; exact Or.inr (Or.inr (Or.inr ⟨_, _, rfl⟩))
    · cases h
  · obtain ⟨_, _, _, _, hsp⟩ := mainN_split hacc hM
    rw [hterm] at hsp; cases hsp

/-- **A W frame's stores**: an exchange of a leaf (`numQ`) into a buffer of
one-word elements. -/
theorem wN_units {p : Prog} {mem : WeakMem.Memory} {R : Ty} {x : String} {op : Op} {e : Expr} {env : Env}
    (hW : WN p mem R (.let_ x op e) env) {g : G} {s : St} {pw : Word} {b : WeakMem.Address} {rel : Bool}
    {us : List Acc} {ws : List Word} (hU : TermFul.UnitsOp g env s op pw b rel us ws) :
    us = [.one] ∧ ∀ w ∈ ws, NumW w := by
  obtain ⟨cx, cs, bufs, scope, lits, X, hb, hsc, hB, hC, hN, hX, hG, -⟩ := hW
  have hq := (hG _ (List.mem_cons_self ..)).1
  cases op with
  | xchgAt bb i v =>
    simp only [TermFul.UnitsOp] at hU
    obtain ⟨-, t, t1, t2, iws, μ, u, j, a0, hbb, -, hv, hbe, -, -, hus, -⟩ := hU
    cases bb with
    | var bb' =>
      cases i with
      | lit ii =>
        simp only [body2, Bool.and_eq_true] at hb
        obtain ⟨⟨⟨-, hn⟩, hv1⟩, -⟩ := hb
        cases hl : bufs.lookup bb' with
        | none => rw [hl] at hn; simp at hn
        | some n =>
          obtain ⟨⟨_, hB0⟩, -⟩ := id hB
          obtain ⟨t0, u0, lbl, he0, hbe0, he2, -⟩ := hB0 bb' n hl
          simp only [TermRun.evalAt, he0, Option.some.injEq, Prod.mk.injEq] at hbb
          obtain ⟨rfl, -⟩ := hbb
          rw [hbe0, Option.some.injEq, Prod.mk.injEq] at hbe
          obtain ⟨-, rfl⟩ := hbe
          rw [accs_elem2 he2, Option.some.injEq] at hus
          refine ⟨hus.symm, ?_⟩
          have hm : litMask (litAt lits v) = [true] := by simpa [numQ, xchgLeafQ] using hq
          have hbv := hN.evalAt (inLits_of_atom1' hsc hv1) (fun z hz hxz => by
            have h1 := hX z hxz; subst hz; simp [mentions, termKey2, atKey] at h1) hv
          have hl1 := hbv.2.2.1
          rw [← litMask_length, hm] at hl1
          rcases ws with _ | ⟨w0, _ | _⟩ <;> simp at hl1
          intro w hw
          simp only [List.mem_singleton] at hw; subst hw
          exact hbv.one hm
      | _ => simp [body2] at hb
    | _ => simp [body2] at hb
  | _ =>
    first
      | (simp [body2] at hb; done)
      | (simp [TermFul.UnitsOp] at hU; done)

/-- **A thread's single-word writes are numbers** under `ThN`. -/
theorem thN_sw {p : Prog} (hacc : Accepted2 p = true) {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts}
    {th : TTh} (hT : ThN p mem th) {l : WeakMem.Address} {v : WeakMem.Val}
    (h : TermFul.SW g mem pairs th l v) : ∃ n, v = .num n := by
  rcases h with ⟨x, op, e, hterm, hO⟩ | ⟨acq, rel, w, e, v', tn, ok, fail, -, -, -, -, -, -, -, -, hterm, -⟩
  · rcases hO with ⟨pw, b, rel, us, ws, j, w, hU, -, hw, -, rfl⟩ |
        ⟨o, acq, rel, a, v', -, -, -, -, -, -, hop, -⟩
    · have hall : ∀ w ∈ ws, NumW w := by
        rcases thN_letOp hacc hT hterm with ⟨R, hW⟩ | hk | hk | ⟨a, b, rfl⟩
        · exact (wN_units hW hU).2
        · cases op <;> simp [pureOp] at hk <;> simp [TermFul.UnitsOp] at hU
        · obtain ⟨_, _, _, _, rfl⟩ := hk; simp [TermFul.UnitsOp] at hU
        · simp [TermFul.UnitsOp] at hU
      exact hall w (List.mem_of_getElem? hw)
    · subst hop
      rcases thN_letOp hacc hT hterm with ⟨R, ⟨_, _, _, _, _, _, hb, -⟩⟩ | hk | hk | ⟨a, b, hk⟩
      · simp [body2] at hb
      · simp [pureOp] at hk
      · obtain ⟨_, _, _, _, hk⟩ := hk; cases hk
      · cases hk
  · rcases thN_shape hacc hT with ⟨cx, cs, bufs, scope, hb⟩ | hE | h | h | h | ⟨a, x, y, e1, h⟩ <;>
      rw [hterm] at * <;> first | (simp [body2] at hb; done) | (simp [PureE] at hE; done) | cases h

/-- **`newBuf`'s outcome**, with its zero words. -/
theorem evalOp_newBuf_inv' {g : G} {env : Env} {σs : List Ty} {s s' : St} {n : At} {τ : Ty} {t : Ty}
    {ws : List Word} (h : (s', t, ws) ∈ evalOp g env σs s (.newBuf n τ)) :
    ∃ k us lbl, accs (close σs τ) = some us ∧
      s' = (allocBuf lbl (k * nWords us)
        (if zeroableIn [] [] (close σs τ) then zeroWords (close σs τ) else none) s).1 := by
  simp only [evalOp, ol, Option.mem_toList] at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨⟨ta, wn⟩, hn, k, hk, us, hus, h⟩ := h
  exact ⟨k, us, _, hus, h.1.symm⟩

/-- **A W frame's new messages are numbers**: an exchange's operand (a
leaf), a new buffer's zeros. -/
theorem wN_new {p : Prog} {g : G} {mem : WeakMem.Memory} {R : Ty} {x : String} {op : Op} {e : Expr} {env : Env}
    (hW : WN p mem R (.let_ x op e) env) {s s' : St} {t : Ty} {ws : List Word}
    (hev : (s', t, ws) ∈ evalOp g env [] s op) (hc : Robust.isCallOp op = false) :
    ∀ k m, s.mem.size ≤ k → s'.mem[k]? = some m → ∃ n, m.val = .num n := by
  intro k m hk hm
  have hkeep : keepOp op = true → False := fun h => by
    rw [evalOp_keep h hev] at hm
    have := (Array.getElem?_eq_some_iff.mp hm).1; omega
  have hW' := hW
  obtain ⟨cx, cs, bufs, scope, lits, X, hb, -⟩ := hW'
  cases op with
  | xchgAt bb i v =>
    rcases TermUndefLow.evalOp_xchgAt_newV hev k m hk hm with
      ⟨pw, b, rel, us, ws', j, hU, -, hr⟩ | ⟨_, _, _, _, _, _, _, _, _, _, hop, -⟩ | ⟨_, _, _, _, _, _, _, hop, -⟩
    · obtain ⟨rfl, hall⟩ := wN_units hW hU
      rcases hr with ⟨-, w, hw, hv⟩ | ⟨i, hi, -⟩ | ⟨jj, -, i, hi, -⟩
      · obtain ⟨n, hn⟩ := hall w (List.mem_of_getElem? hw)
        exact ⟨n, hv.trans hn⟩
      · rcases i with _ | i <;> simp at hi
      · rcases i with _ | i <;> simp at hi
    · cases hop
    · cases hop
  | newBuf n τ =>
    obtain ⟨k', us, lbl, hus, rfl⟩ := evalOp_newBuf_inv' hev
    simp only [body2, Bool.and_eq_true] at hb
    have he2 := hb.1.2
    rw [close_nil', zero_elem2 he2] at hm
    obtain ⟨i, rfl⟩ : ∃ i, k = s.mem.size + i := ⟨k - s.mem.size, by omega⟩
    by_cases hi : i < k' * nWords us
    · rw [Scc.Sem.allocBuf_mem_new _ _ _ _ hi, Option.some.injEq] at hm
      subst hm
      obtain ⟨v, hv, -⟩ := allocBufVal_num he2 i
      exact ⟨v, hv⟩
    · have := (Array.getElem?_eq_some_iff.mp hm).1
      rw [Scc.Sem.allocBuf_mem_size] at this; omega
  | call _ _ _ _ => simp [Robust.isCallOp] at hc
  | atom _ => exact (hkeep rfl).elim
  | nameI _ => exact (hkeep rfl).elim
  | add _ _ => exact (hkeep rfl).elim
  | sub _ _ => exact (hkeep rfl).elim
  | pair _ _ => exact (hkeep rfl).elim
  | pack _ _ _ => exact (hkeep rfl).elim
  | asLanes _ _ _ => exact (hkeep rfl).elim
  | _ => simp [body2] at hb

/-- **A thread step's new messages are numbers** under `ThN`. -/
theorem thN_new {p : Prog} (hacc : Accepted2 p = true) {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts}
    {th : TTh} (hT : ThN p mem th) {r : WeakMem.Memory × List WeakMem.Ts × TTh} (hr : r ∈ tstep g mem pairs th) :
    ∀ k m, mem.size ≤ k → r.1[k]? = some m → ∃ n, m.val = .num n := by
  intro k m hk hm
  have hsame : r.1 = mem → False := fun h => by
    rw [h] at hm; have := (Array.getElem?_eq_some_iff.mp hm).1; omega
  have bad : ∀ (hb : ∀ cx cs bufs scope, body2 cx cs bufs scope th.term = false) (hE : PureE th.term = false)
      (h1 : th.term ≠ setupTerm) (h2 : th.term ≠ setupRest) (h3 : th.term ≠ .tail "main" [] (.var "a"))
      (h4 : ∀ a x y e, th.term ≠ .split a x y e), False := by
    intro hb hE h1 h2 h3 h4
    rcases thN_shape hacc hT with ⟨cx, cs, bufs, scope, h⟩ | h | h | h | h | ⟨a, x, y, e, h⟩
    · rw [hb] at h; cases h
    · rw [hE] at h; cases h
    · exact h1 h
    · exact h2 h
    · exact h3 h
    · exact h4 a x y e h
  obtain ⟨m', pr', th'⟩ := r
  simp only at hm hsame ⊢
  cases hterm : th.term with
  | let_ x op e =>
    cases op
    case call f is a ts =>
      simp only [tstep, hterm, ol, Option.mem_toList, Option.map_eq_some_iff, Prod.mk.injEq] at hr
      obtain ⟨th1, -, rfl, -, -⟩ := hr
      exact (hsame rfl).elim
    case callc f a =>
      exact (bad (fun _ _ _ _ => by rw [hterm]; rfl) (by rw [hterm]; rfl) (by rw [hterm, setupTerm_eq]; simp)
        (by rw [hterm, setupRest]; simp) (by rw [hterm]; simp) (fun _ _ _ _ => by rw [hterm]; simp)).elim
    all_goals
      simp only [tstep, hterm, List.mem_map, Prod.mk.injEq] at hr
      obtain ⟨⟨s', t, ws⟩, hev, rfl, -, -⟩ := hr
      rcases thN_letOp hacc hT hterm with ⟨R, hW⟩ | hk' | hk' | ⟨a, b, hk'⟩
      · rw [hT.1] at hev
        exact wN_new hW hev (by simp [Robust.isCallOp]) k m hk hm
      · exact (hsame (evalOp_keep (by revert hk'; simp [pureOp, keepOp]) hev)).elim
      · obtain ⟨_, _, _, _, hk'⟩ := hk'; cases hk'
      · cases hk' <;> exact (hsame (evalOp_keep rfl hev)).elim
  | _ =>
    first
      | (exact (bad (fun _ _ _ _ => by rw [hterm]; rfl) (by rw [hterm]; rfl) (by rw [hterm, setupTerm_eq]; simp)
          (by rw [hterm, setupRest]; simp) (by rw [hterm]; simp) (fun _ _ _ _ => by rw [hterm]; simp)).elim)
      | (simp only [tstep, hterm] at hr
         repeat' split at hr
         all_goals first
           | (simp at hr; done)
           | (simp only [List.mem_singleton, Prod.mk.injEq] at hr; exact (hsame hr.1).elim)
           | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff, Prod.mk.injEq] at hr
              obtain ⟨_, -, h, -, -⟩ := hr; exact (hsame h.symm).elim))

end mem

/-! ## The loads a frame reaches -/

section loads

open Scc.Lower (shapeOf body2 Accepted2 setupOf)
open Scc.Sem.SrcSem (setupTerm)

/-- **A frame no run takes to the extern's load**: a `body2` body or the
start's three terms. -/
def BodyOK (t : Expr) : Prop :=
  (∃ cx cs bufs scope, body2 cx cs bufs scope t = true) ∨ t = setupTerm ∨ t = setupRest ∨
    t = .tail "main" [] (.var "a")

/-- A `body2` `let`'s body is `body2`. -/
theorem body2_let {cx : Scc.Lower.Cx2} {cs bufs : List (String × Nat)} {scope : List String} {x : String}
    {op : Op} {e : Expr} (hb : body2 cx cs bufs scope (.let_ x op e) = true) :
    ∃ cs' bufs', body2 cx cs' bufs' (x :: scope) e = true := by
  cases op with
  | newBuf n τ =>
    simp only [body2, Bool.and_eq_true] at hb
    obtain ⟨-, hm⟩ := hb
    split at hm
    · simp only [Bool.and_eq_true] at hm; exact ⟨_, _, hm.2⟩
    · cases hm
  | xchgAt b i v =>
    cases b <;> cases i <;> simp only [body2, Bool.and_eq_true, Bool.false_eq_true] at hb <;> exact ⟨_, _, hb.2⟩
  | _ => simp only [body2, Bool.and_eq_true, Bool.false_eq_true] at hb <;> exact ⟨_, _, hb.2⟩

/-- `main`'s body is `body2`. -/
theorem main_body2 {p : Prog} (hacc : Accepted2 p = true)
    (hset : ∀ s, setupOf p = some s → Compat s (shapeOf s) = true) {d : Decl}
    (hf : p.find? (·.name == "main") = some d) : ∃ cx cs bufs scope, body2 cx cs bufs scope d.body = true := by
  obtain ⟨hd, hname⟩ := find_name hf
  rcases block_kind hacc hset hd with ⟨h | h, -⟩ | h
  · subst h; exact absurd hname (by decide)
  · subst h; exact absurd hname (by decide)
  · obtain ⟨cx, hb, -⟩ := h.body; exact ⟨cx, _, _, _, hb⟩

/-- **A frame step keeps `BodyOK`.** -/
theorem BodyOK.step {p : Prog} (hacc : Accepted2 p = true)
    (hset : ∀ s, setupOf p = some s → Compat s (shapeOf s) = true) {t : Expr} {env : Env} {c1 : Expr × Env}
    (h : BodyOK t) (hs : TStepE p (t, env) c1) : BodyOK c1.1 := by
  rcases h with ⟨cx, cs, bufs, scope, hb⟩ | rfl | rfl | rfl
  · cases t with
    | let_ x op e =>
      have hc : ∀ f is a ts, op ≠ .call f is a ts := by
        rintro f is a ts rfl; exact tstepE_call hs
      have hcc : ∀ f a, op ≠ .callc f a := by
        rintro f a rfl; simp [body2] at hb
      obtain ⟨t, ws, rfl, -⟩ := tstepE_let hs hc hcc
      obtain ⟨cs', bufs', hb'⟩ := body2_let hb
      exact Or.inl ⟨cx, cs', bufs', _, hb'⟩
    | split a x y e =>
      obtain ⟨_, _, _, _, -, -, rfl⟩ := tstepE_split hs
      simp only [body2, Bool.and_eq_true] at hb
      exact Or.inl ⟨cx, _, _, _, hb.2⟩
    | unpack a i x e =>
      rw [tstepE_unpack hs]
      simp only [body2, Bool.and_eq_true] at hb
      exact Or.inl ⟨cx, _, _, _, hb.2⟩
    | ifeq a b yes no =>
      simp only [body2, Bool.and_eq_true] at hb
      rcases (tstepE_ifeq hs).2.1 with h | h <;> rw [h]
      · exact Or.inl ⟨cx, _, _, _, hb.1.2⟩
      · exact Or.inl ⟨cx, _, _, _, hb.2⟩
    | ret a => exact absurd hs tstepE_ret
    | _ => simp [body2] at hb
  · rw [setupTerm_eq] at hs; exact absurd hs tstepE_call
  · obtain ⟨t, ws, rfl, -⟩ := tstepE_let hs (by intros; simp) (by intros; simp)
    exact Or.inr (Or.inr (Or.inr rfl))
  · obtain ⟨d, t, ws, hf, -, rfl⟩ := tstepE_tail hs
    exact Or.inl (main_body2 hacc hset hf)

/-- **No run from a `BodyOK` frame reaches the extern's load.** -/
theorem BodyOK.run {p : Prog} (hacc : Accepted2 p = true)
    (hset : ∀ s, setupOf p = some s → Compat s (shapeOf s) = true) :
    ∀ {n : Nat} {c c' : Expr × Env}, TRunE p n c c' → BodyOK c.1 → c'.1 ≠ printLoadE
  | _, _, _, .refl _, h => by
    rintro he
    rw [he] at h
    rcases h with ⟨_, _, _, _, hb⟩ | h | h | h
    · simp [printLoadE, body2] at hb
    · rw [setupTerm_eq] at h; simp [printLoadE] at h
    · simp [printLoadE, setupRest] at h
    · simp [printLoadE] at h
  | _, (t, env), _, .step hs hr, h => BodyOK.run hacc hset hr (h.step hacc hset hs)

/-- **The loads thread 0's local runs reach read cells with messages**: none
from a W frame or the start's (`BodyOK.run`), the extern's by `LdOK`. -/
theorem thN_hcell {p : Prog} (hacc : Accepted2 p = true)
    (hset : ∀ s, setupOf p = some s → Compat s (shapeOf s) = true) {mem : WeakMem.Memory} {th : TTh}
    (hT : ThN p mem th) {c1 : Ctl} (ht : c1.term = th.term) (he : c1.env = th.env) {c' : Ctl}
    {l : WeakMem.AllocLabel} {j : Nat} (hr : LocalRun p c1 c') (hld : PrintLd c' l j) : HasCell mem ⟨l, j⟩ := by
  obtain ⟨n, hrn⟩ := localRun_trunE hr
  rw [ht, he] at hrn
  obtain ⟨-, R, hF, -⟩ := hT
  have bad : BodyOK th.term → HasCell mem ⟨l, j⟩ := fun h => absurd hld.1 (BodyOK.run hacc hset hrn h)
  rcases hF with ⟨⟨cx, cs, bufs, scope, -, -, hb, -⟩, -⟩ | ⟨-, -, -, hL⟩ | ⟨hSM | hM, -⟩
  · exact bad (Or.inl ⟨cx, cs, bufs, scope, hb⟩)
  · exact hL n _ l j hrn hld
  · exact bad (Or.inr (setupN_cases hSM))
  · obtain ⟨s, d, -, -, -, hf, hb, -⟩ := hM
    rw [hb] at bad
    exact bad (Or.inl (main_body2 hacc hset hf))

end loads

/-! ## Along the source's runs -/

section reach

open Scc.Lower (LitV litAt shapeOf params2 litWalk2 litWalks2 body2 Accepted2 setupOf)
open Scc.Sem.SrcSem (setupTerm setupStart)
open Scc.Sem.SrcSem
open Scc.Sem.MemRel (SLatest)

/-- **The walk's facts at every block** from `numQ` on the program's walk
and `Accepted2` (`layoutOk2`, `callsOk2`; the setup result not a bare
locative by `hloc_of_accepted2`). -/
theorem goodBlocks_of {p : Prog} (hacc : Accepted2 p = true) (hn : ∀ q ∈ litWalks2 p, numQ q = true) :
    GoodBlocks p := by
  refine ⟨fun d hd q hq => ?_, Spike.Lib.LowerNode.hloc_of_accepted2 hacc⟩
  have hq' : q ∈ litWalks2 p := List.mem_flatMap.2 ⟨d, hd, hq⟩
  obtain ⟨-, -, hlay, hcalls, -⟩ := accepted2_parts hacc
  rw [layoutOk2_eq] at hlay
  exact ⟨hn q hq', List.all_eq_true.1 hlay q hq', (callsOk2_parts hcalls hd hq).1, (callsOk2_parts hcalls hd hq).2⟩

/-- **The invariant of the source's runs**: `MemNP`, promise
well-formedness, thread 0 under `ThN`. -/
def InvN (p : Prog) (c : Cfg) : Prop :=
  MemNP c ∧ TermFul.PWFall c ∧ ∃ th, c.ths[0]? = some th ∧ ThN p c.mem th

theorem ThN.mono {p : Prog} {mem mem' : WeakMem.Memory} {th th' : TTh} (h : ThN p mem th) (hm : MemExt mem mem')
    (ht : th'.term = th.term) (he : th'.env = th.env) (hσ : th'.σs = th.σs) (hs : th'.stack = th.stack) :
    ThN p mem' th' := by
  obtain ⟨hσ0, R, hF, hS⟩ := h
  exact ⟨hσ.trans hσ0, R, hF.mono hm ht he hs, by rw [hs]; exact hS.mono hm⟩

theorem memExt_push (M : WeakMem.Memory) (x : WeakMem.Msg) : MemExt M (M.push x) := by
  intro k m hk
  have := (Array.getElem?_eq_some_iff.mp hk).1
  rw [Array.getElem?_push]; split
  · omega
  · exact hk

/-- **The start keeps the invariant**: no message, `setupTerm` with no frame. -/
theorem invN_init {p : Prog} {s : Ty} (hs : setupOf p = some s) (cap : Nat) (meW : Word) :
    InvN p (setupStart cap meW) := by
  refine ⟨⟨rfl, fun k m hk _ => by simp [setupStart] at hk⟩,
    fun i => ⟨fun q hq => by simp [setupStart] at hq, fun t ht => ?_⟩, _, rfl,
    rfl, .unit, Or.inr (Or.inr ⟨Or.inl (Or.inl ⟨s, hs, ⟨_, _, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩), rfl⟩), trivial⟩
  rcases i with _ | i <;> simp [promsOf, setupStart] at ht

/-- **Thread 0 after an extern step**: at the site's body, the result bound,
every other field kept but the allocation count and the thread box. -/
theorem extCfg_th0 {c : Cfg} {th : TTh} (hth : c.ths[0]? = some th) (x : String) (n : ExtName) (e : Expr)
    (ws rs : List Word) : ∃ th' t ws', (extCfg c 0 th x n e ws rs).ths[0]? = some th' ∧ th'.term = e ∧
      th'.env = (x, t, ws') :: th.env ∧ th'.σs = th.σs ∧ th'.stack = th.stack ∧ th'.promises = th.promises := by
  have hi : 0 < c.ths.size := (Array.getElem?_eq_some_iff.mp hth).1
  refine ⟨(extCfg c 0 th x n e ws rs).ths[0]'(by rw [TermExtStep.extCfg_size]; exact hi), ?_⟩
  cases n <;> cases htl : th.tidLbl <;> simp [extCfg, curCfg, htl, Array.set!, hi]

/-- **An extern site keeps the thread invariant**: only the extern's frames
have one (`body2` and the start have none). -/
theorem thN_ext {p : Prog} (hacc : Accepted2 p = true) {mem : WeakMem.Memory} {th th' : TTh} (hT : ThN p mem th)
    {x : String} {n : ExtName} {a : At} {e : Expr} (hterm : th.term = .let_ x (.ext n a) e) {t : Ty}
    {ws : List Word} (ht : th'.term = e) (he : th'.env = (x, t, ws) :: th.env) (hσ : th'.σs = th.σs)
    (hs : th'.stack = th.stack) : ThN p mem th' := by
  obtain ⟨hσ0, R, hF, hS⟩ := hT
  refine ⟨hσ.trans hσ0, R, ?_, by rw [hs]; exact hS⟩
  rcases hF with ⟨⟨_, _, _, _, _, _, hb, -⟩, -⟩ | ⟨hE, hRu, hP, hL⟩ | ⟨hSM | hM, -⟩
  · rw [hterm] at hb; simp [body2] at hb
  · have hTS : TStepE p (th.term, th.env) (th'.term, th'.env) :=
      Or.inr ⟨x, n, a, e, t, ws, hterm, by rw [ht, he]⟩
    rw [hterm] at hE; simp only [PureE, Bool.and_eq_true] at hE
    exact Or.inr (Or.inl ⟨by rw [ht]; exact hE.2, hRu, hP, hL.step hTS⟩)
  · rcases setupN_cases hSM with h | h | h <;> rw [hterm] at h <;> simp [setupTerm_eq, setupRest] at h
  · obtain ⟨_, _, _, _, hsp⟩ := mainN_split hacc hM
    rw [hterm] at hsp; cases hsp

/-- **An extern step keeps the invariant**: the memory, the pairs and every
thread's promises are kept (`extCfg`). -/
theorem invN_ext {p : Prog} (hacc : Accepted2 p = true) {c : Cfg} {th : TTh} (hN : MemNP c) (hW : TermFul.PWFall c)
    (hth : c.ths[0]? = some th) (hT : ThN p c.mem th) {x : String} {n : ExtName} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.ext n a) e) (ws rs : List Word) : InvN p (extCfg c 0 th x n e ws rs) := by
  obtain ⟨th', t, ws', h0, ht, he, hσ, hs, hp⟩ := extCfg_th0 hth x n e ws rs
  have hpr : ∀ j, promsOf (extCfg c 0 th x n e ws rs) j = promsOf c j := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [promsOf_some h0, promsOf_some hth, hp]
    · simp only [promsOf]; rw [extCfg_ths_ne c th x n e ws rs (by omega)]
  have hm := extCfg_mem c 0 th x n e ws rs
  refine ⟨⟨by rw [extCfg_size]; exact hN.1, fun k m hk hn => hN.2 k m (by rw [← hm]; exact hk)
    (by rw [← hpr]; exact hn)⟩, fun j => ⟨fun q hq => ?_, fun q hq => ?_⟩, th', h0, ?_⟩
  · rw [extCfg_pairs] at hq; rw [hm]; exact (hW j).1 q hq
  · rw [hpr] at hq; rw [hm, extCfg_pairs]; exact (hW j).2 q hq
  · rw [hm]; exact thN_ext hacc hT hterm ht he hσ hs

/-- **A permit grant keeps the invariant**: the memory, the pairs and every
thread's promises are kept (`setPermit` changes one thread's permit only). -/
theorem invN_setPermit {p : Prog} {c : Cfg} (hI : InvN p c) (j : Nat) (v : WeakMem.Ts) :
    InvN p (setPermit c j v) := by
  obtain ⟨hN, hW, th, hth, hT⟩ := hI
  unfold setPermit
  split
  · rename_i th1 h1
    have hj : j = 0 := by have := (Array.getElem?_eq_some_iff.mp h1).1; have := hN.1; omega
    subst hj; rw [hth] at h1; cases h1
    have hi : 0 < c.ths.size := (Array.getElem?_eq_some_iff.mp hth).1
    have h0 : (c.ths.set! 0 { th with permit := some (max (th.permit.getD 0) v) })[0]? =
        some { th with permit := some (max (th.permit.getD 0) v) } := by simp [Array.set!, hi]
    have hpr : ∀ k, promsOf { c with ths := c.ths.set! 0 { th with permit := some (max (th.permit.getD 0) v) } } k =
        promsOf c k := by
      intro k
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp only [promsOf]; rw [h0, hth]; rfl
      · simp only [promsOf]; rw [TermFul.set_other (by omega)]
    exact ⟨⟨by simp [hN.1], fun k m hk hn => hN.2 k m hk (by rw [← hpr]; exact hn)⟩,
      fun k => ⟨(hW k).1, fun t ht => (hW k).2 t (by rw [← hpr]; exact ht)⟩, _, h0, hT⟩
  · exact ⟨hN, hW, th, hth, hT⟩

/-- **A wake keeps the invariant** (`invN_setPermit`, or no change). -/
theorem invN_wake {p : Prog} {c : Cfg} (hI : InvN p c) (i : Nat) (v : WeakMem.Ts) (n : ExtName) (ws : List Word) :
    InvN p (wake c i v n ws) := by
  unfold wake
  split <;> (try split) <;> first | exact invN_setPermit hI _ _ | exact hI

/-- **A source step keeps the invariant**: a promise (promised, `ThN`
unchanged), a thread step (`memNP_thread` with `thN_sw`, `thN_new`;
`tstep_thN`, an exchange reading a number by `xchgAt_reads`), no spawn
(`ThN`'s terms spawn nothing), an extern step (none with `SrcHooks.none`;
`invN_ext` with WeakCore's hook). -/
theorem invN_step {P : SrcParams} {p : Prog} (hacc : Accepted2 p = true)
    (hset : ∀ s, setupOf p = some s → Compat s (shapeOf s) = true) (hgood : GoodBlocks p)
    (hH : P.hooks = SrcHooks.none ∨ SrcOutProto.UsesWc P p)
    {c c' : Cfg} {i : Nat} {es : List Ev} (h : (source P p).step i c es c')
    (hI : InvN p c) : InvN p c' := by
  obtain ⟨hN, hW, th, hth, hT⟩ := hI
  obtain ⟨-, hs, -⟩ := h
  rcases hs with (⟨hts, hcert⟩ | ⟨a, v, w, hi, hw, hc, rfl⟩) | hs | hs
  · -- a thread step
    have hW' := TermFul.step_pwfAll (StepBy.step (.inl ⟨hts, hcert⟩)) hW
    obtain ⟨th0, r, hth0, hr, e1, -, e3, -⟩ := TermFul.threadSteps_inv hts
    have hi0 : i = 0 := by have := (Array.getElem?_eq_some_iff.mp hth0).1; have := hN.1; omega
    subst hi0
    rw [hth] at hth0; cases hth0
    have hgrow := (TermFul.tstep_grow hr).1
    have hpw : ∀ t, t ∈ th.promises → t < c.mem.size ∧ t ∉ c.pairs :=
      fun t ht => (hW 0).2 t (by rw [promsOf_some hth]; exact ht)
    refine ⟨memNP_thread hN (hW 0) hts (fun th' h' l v hsw => by rw [hth] at h'; cases h'; exact thN_sw hacc hT hsw)
      (fun th' r' h' hr' => by rw [hth] at h'; cases h'; exact thN_new hacc hT hr'), hW', r.2.2, e3, ?_⟩
    rw [e1]
    refine tstep_thN hacc hset hgood rfl hT hr hgrow ?_
    intro x b i' v' e s' t ws hterm hev hsm hvs hps hu
    have hc : ∀ t' m, t' ∈ s'.promises → (stOf c.mem c.pairs th).mem[t']? = some m → s'.vs.coh m.loc < t' := by
      intro t' m ht' hm
      rw [hps] at ht'; rw [hvs]
      exact TermCert.certified_promAbove hcert e3 ht' (by rw [e1]; exact hgrow t' m hm)
    obtain ⟨w, t', m, rfl, hm, hv, hn⟩ := xchgAt_reads hev hu hc
    refine ⟨w, rfl, ?_⟩
    rw [hps] at hn
    by_cases hp : t' ∈ th.promises
    · obtain ⟨m', hm', hsw, -⟩ :=
        (TermFul.tstep_fulfil (fun t ht => (hpw t ht).1) (fun t ht => (hpw t ht).2) hr).2 t' hp hn
      obtain ⟨n, hn'⟩ := thN_sw hacc hT hsw
      have : some m' = some m := hm'.symm.trans hm
      cases this
      exact ⟨n, hv.trans hn'⟩
    · obtain ⟨n, hn'⟩ := hN.2 t' m hm (by rw [promsOf_some hth]; exact hp)
      exact ⟨n, hv.trans hn'⟩
  · -- a promise
    have hW' := TermFul.step_pwfAll (StepBy.step (.inr ⟨a, v, w, hi, hw, hc, rfl⟩)) hW
    have hi0 : i = 0 := by have := hN.1; omega
    subst hi0
    refine ⟨memNP_prom hN hi, hW', { th with promises := th.promises ++ [c.mem.size] }, ?_, ?_⟩
    · simp only [promise, hth]; exact TermCert.arr_set hth
    · have e1 : (promise c 0 a v w).mem = c.mem.push ⟨a, v, w⟩ := by simp [promise, hth]
      rw [e1]
      exact hT.mono (memExt_push _ _) rfl rfl rfl rfl
  · -- no spawn
    obtain ⟨x, f, a, T, ts, e, th', rt, ws, h1, h2, -⟩ := hs
    have hi0 : i = 0 := by have := (Array.getElem?_eq_some_iff.mp h1).1; have := hN.1; omega
    subst hi0
    rw [hth] at h1; cases h1
    rcases thN_letOp hacc hT h2 with ⟨R, ⟨_, _, _, _, _, _, hb, -⟩⟩ | hk | ⟨_, _, _, _, hk⟩ | ⟨_, _, hk⟩
    · simp [body2] at hb
    · simp [pureOp] at hk
    · cases hk
    · cases hk
  · -- an extern step
    rcases hH with hH | hH <;> rw [hH] at hs
    · exact hs.elim
    obtain ⟨x, n, a, e, th1, rt, ws, rs, h1, hterm, -, -, -, -, rfl⟩ := hs
    have hi0 : i = 0 := by have := (Array.getElem?_eq_some_iff.mp h1).1; have := hN.1; omega
    subst hi0
    rw [hth] at h1; cases h1
    exact invN_wake (invN_ext hacc hN hW hth hT hterm ws rs) _ _ _ _

theorem invN_run {P : SrcParams} {p : Prog} (hacc : Accepted2 p = true)
    (hset : ∀ s, setupOf p = some s → Compat s (shapeOf s) = true) (hgood : GoodBlocks p)
    (hH : P.hooks = SrcHooks.none ∨ SrcOutProto.UsesWc P p)
    {c c' : Cfg} {tr : List Ev} (h : (source P p).Run c tr c') (hI : InvN p c) :
    InvN p c' := by
  induction h with
  | refl => exact hI
  | step hs _ ih =>
    obtain ⟨i, hs⟩ := hs
    exact ih (invN_step hacc hset hgood hH hs hI)

/-- **Every reachable configuration keeps the invariant** (from the start
before the setup block). -/
theorem invN_reach {P : SrcParams} {p : Prog} (hacc : Accepted2 p = true)
    (hset : ∀ s, setupOf p = some s → Compat s (shapeOf s) = true) (hgood : GoodBlocks p)
    {s0 : Ty} (hsetup : setupOf p = some s0) (hinit : ∀ c, P.init c → ∃ meW, c = setupStart P.cap meW)
    (hH : P.hooks = SrcHooks.none ∨ SrcOutProto.UsesWc P p)
    {tr : List Ev} {s : Cfg} (h : (source P p).Reach tr s) : InvN p s := by
  obtain ⟨c0, h0, hrun⟩ := h
  obtain ⟨meW, rfl⟩ := hinit c0 h0
  exact invN_run hacc hset hgood hH hrun (invN_init hsetup P.cap meW)

/-! ## The printed cells -/

/-- **`SrcNumS` with the thread's promises empty** (ISA-neutral; no frame
run premise): every local run from thread 0's control to a load `Ld` marks
finds the source's latest message at the cell a number. -/
def SrcNumSP (P : SrcParams) (p : Prog) (Ld : Ctl → WeakMem.AllocLabel → Nat → Prop) : Prop :=
  ∀ tr s th, (source P p).Reach tr s → s.ths[0]? = some th → th.promises = [] → ∀ c1 : Ctl,
    c1.term = th.term → c1.env = th.env → ∀ c' l j, LocalRun p c1 c' → Ld c' l j →
      ∃ (k : Nat) (m : WeakMem.Msg) (n : Nat), SLatest s.mem ⟨l, j⟩ k ∧ s.mem[k]? = some m ∧ m.val = .num n

/-- **The printed cells of an `Accepted2` program hold numbers**, given that
a marked load's cell exists (`hcell`): every message of a reachable
configuration that thread 0 has not promised is a number (`invN_reach`). -/
theorem srcNumS_of_accepted2' {P : SrcParams} {p : Prog} {Ld : Ctl → WeakMem.AllocLabel → Nat → Prop}
    (hacc : Accepted2 p = true) (hn : ∀ q ∈ litWalks2 p, numQ q = true)
    (hset : ∀ s, setupOf p = some s → Compat s (shapeOf s) = true) {s0 : Ty} (hsetup : setupOf p = some s0)
    (hinit : ∀ c, P.init c → ∃ meW, c = setupStart P.cap meW) (hH : P.hooks = SrcHooks.none ∨ SrcOutProto.UsesWc P p)
    (hcell : ∀ tr s th, (source P p).Reach tr s → s.ths[0]? = some th → ∀ c1 : Ctl, c1.term = th.term →
      c1.env = th.env → ∀ c' l j, LocalRun p c1 c' → Ld c' l j → HasCell s.mem ⟨l, j⟩) :
    SrcNumSP P p Ld := by
  intro tr s th hr hth hp c1 ht he c' l j hl hld
  obtain ⟨hN, -, -⟩ := invN_reach hacc hset (goodBlocks_of hacc hn) hsetup hinit hH hr
  exact hN.latest hth hp (hcell tr s th hr hth c1 ht he c' l j hl hld)

/-- **The printed cells of an `Accepted2` program hold numbers**: the
extern's loop loads only cells with messages (`thN_hcell`). -/
theorem srcNumS_of_accepted2 {P : SrcParams} {p : Prog} (hacc : Accepted2 p = true)
    (hn : ∀ q ∈ litWalks2 p, numQ q = true) (hset : ∀ s, setupOf p = some s → Compat s (shapeOf s) = true)
    {s0 : Ty} (hsetup : setupOf p = some s0)
    (hinit : ∀ c, P.init c → ∃ meW, c = setupStart P.cap meW)
    (hH : P.hooks = SrcHooks.none ∨ SrcOutProto.UsesWc P p) : SrcNumSP P p PrintLd := by
  refine srcNumS_of_accepted2' hacc hn hset hsetup hinit hH fun tr s th hr hth c1 ht he c' l j hl hld => ?_
  obtain ⟨-, -, th0, h0, hT⟩ := invN_reach hacc hset (goodBlocks_of hacc hn) hsetup hinit hH hr
  rw [hth] at h0; cases h0
  exact thN_hcell hacc hset hT ht he hl hld

end reach

/-! ## `hello1o` (`hello1.w` with the output extern linked) -/

namespace Hello1N

open Scc.Lower (shapeOf litWalks2 setupOf)
open Scc.Sem.SrcSem (setupStart)
open Scc.Sem.SrcSem

theorem hn : ∀ q ∈ litWalks2 Spike.Test.Hello1MainSrc.hello1o, numQ q = true := by decide

/-- `hello1o` has the output extern (`Print2X`/`Print2A`'s `hext`). -/
theorem ext : Scc.Lower.hasPrint Spike.Test.Hello1MainSrc.hello1o = true := by decide

theorem setup : ∃ s0, setupOf Spike.Test.Hello1MainSrc.hello1o = some s0 ∧ shapeOf s0 ≠ .loc ∧
    Compat s0 (shapeOf s0) = true :=
  ⟨_, rfl, by decide, by decide⟩

end Hello1N

section hello1

open Scc.Sem.SrcSem
open Scc.Sem.SrcSem (setupStart)

/-- **`hello1o`'s printed cells hold numbers**, from the start, with no
extern or with WeakCore's output hook. -/
theorem srcNumS_hello1 {P : SrcParams} (hinit : ∀ c, P.init c → ∃ meW, c = setupStart P.cap meW)
    (hH : P.hooks = SrcHooks.none ∨ SrcOutProto.UsesWc P Spike.Test.Hello1MainSrc.hello1o) :
    SrcNumSP P Spike.Test.Hello1MainSrc.hello1o PrintLd := by
  obtain ⟨s0, hs, -, hc⟩ := Hello1N.setup
  exact srcNumS_of_accepted2 hello1o_accepted2 Hello1N.hn (fun s h => by rw [hs] at h; cases h; exact hc) hs
    hinit hH

/-- **The print loop's element load at `PrintSrc.loadC`** (byte `k`) is `PrintLd` at word
`k / 8` of the buffer's label: the trigger `srcNumS_hello1` covers is the consumer's load. -/
theorem printLd_loadC {pw wn : Word} {m k : Nat} {l : WeakMem.AllocLabel} (hpw : pw.val = .loc ⟨l, 0⟩ 0) :
    PrintLd (Spike.Lib.PrintSrc.loadC pw wn m k) l (k / 8) :=
  ⟨rfl, ⟨Spike.Lib.PrintSrc.bufTy, pw, by simp [Spike.Lib.PrintSrc.loadC, Spike.Lib.PrintSrc.loadEnv, lookupE], hpw⟩,
    ⟨.intS (.var 1), cst (.num (k / 8)), by simp [Spike.Lib.PrintSrc.loadC, Spike.Lib.PrintSrc.loadEnv, lookupE], rfl⟩⟩

end hello1

end Spike.Lib.LowerNode
