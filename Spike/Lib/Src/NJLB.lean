import Spike.Lib.Src.SliceL
import Spike.Lib.AllocSrc
import Spike.Lib.OvfAbort
import Spike.Lib.FormE

/-!
**The node invariant with buffers and slices** (ISA-neutral). `NJL` with
`countsOk2`'s facts in the source: `EnvB` (every binding of the walk has its
layout's slices, `EnvSl`; the body's buffers are bound to locatives of labels
in `L` with their first cells written, `SBufs`; the known values are bound to
their numbers, `SCs`) and `MemB` (the messages at labels of `L` hold numbers,
`HeapLit`; every label is below the next one, `LabelsIn`). The walk's known
values and buffers `cs`, `bufs` move as `countsB` moves them (`csAfter`,
`bufsAfter`), so each construct's conclusion is `countsB`'s next state.

- `EnvB`, `MemB`: `.mono`, `.cons` (a binding of a `let` other than
  `newBuf`), `.split`, `.splitLeaf`, `.unpack`, `.entry`, `.call`, `.ret`,
  `.newBuf` (with `MemB`: the new buffer at the next label), `.xchgAt` (with
  `MemB`: the stored number pushed at a label of `L`);
- `NJB`, per construct as `NJL` but at `NodeJE` (the types up to a
  buffer's literal lengths, `Spike/Lib/FormE.lean`, so a node may follow a
  `newBuf`): code-free `NJB.atom`, `.nameI`, `.pair` (`pairOk`), `.pack`,
  `.asLanes`, `.split`, `.unpack`; checked arithmetic and `if`: `NJB.ops`,
  `.add_ok`, `.sub_ok`, `.ifeq`; `plLen_eraseLen`, `compat_eraseLen`;
- `WordsSmall`, `EnvSmall.cons`, `EnvSmall.evalAt`: every number of the
  environment fits in 64 bits (`EnvSmall`, the overflow abort's budget), kept
  by each construct (`NJB` carries it).

Not here: the steps of `newBuf` and `xchgAt` (not local steps; their nodes
use `EnvB.newBuf`, `EnvB.xchgAt` on the source step's environment and
memory), and calls (`EnvB.call`, `EnvB.ret` on the frames).
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Spike.Lib
open Spike.Lib.Form (opdVal NodeJ NodeJE SEnv sevalAt lookupS WordPl WordsRep WordRep SRep SRepE)
open Scc.Sem (ValRep)
open Scc.Lower (LitV litAt unbuf constOf pairOk csAfter bufsAfter shapeOf params2 elem2)

/-! ## Dropping a name -/

theorem SBufs.unbuf {env : TermRun.Env} {bufs : List (String × Nat)} {L : WeakMem.AllocLabel → Prop}
    {sm : WeakMem.Memory} {lsize : WeakMem.AllocLabel → Nat} (h : SBufs env bufs L sm lsize) (i : String) :
    SBufs env (unbuf i bufs) L sm lsize := by
  intro b n hb
  rw [lookup_unbuf] at hb
  split at hb
  · cases hb
  · exact h b n hb

theorem SCs.unbuf {env : TermRun.Env} {cs : List (String × Nat)} (h : SCs env cs) (i : String) :
    SCs env (unbuf i cs) := by
  intro y k hy
  rw [lookup_unbuf] at hy
  split at hy
  · cases hy
  · exact h y k hy

/-- **Every `let` but `newBuf` drops its name from the buffers.** -/
theorem bufsAfter_of_ne {x : String} {cs bufs : List (String × Nat)} {op : Op} (hnb : ∀ n τ, op ≠ .newBuf n τ) :
    bufsAfter x cs bufs op = unbuf x bufs := by
  cases op <;> first | exact absurd rfl (hnb _ _) | rfl

/-! ## The environment and the memory -/

/-- **`countsOk2`'s facts in a source environment**: the walk's slices, the
body's buffers (within the labels' sizes `lsize`), the known values. -/
def EnvB (lits : List (String × LitV)) (cs bufs : List (String × Nat)) (L : WeakMem.AllocLabel → Prop)
    (sm : WeakMem.Memory) (lsize : WeakMem.AllocLabel → Nat) (env : TermRun.Env) : Prop :=
  EnvSl (SlP L sm) lits env ∧ SBufs env bufs L sm lsize ∧ SCs env cs

/-- **The source memory against the labels `L`**: numbers at `L`'s labels,
every label below `B`. -/
def MemB (L : WeakMem.AllocLabel → Prop) (sm : WeakMem.Memory) (B : Nat) : Prop :=
  HeapLit sm L ∧ LabelsIn sm L B

theorem memB_empty (B : Nat) : MemB (fun _ => False) #[] B :=
  ⟨heapLit_empty _, labelsIn_empty B⟩

namespace EnvB

variable {lits : List (String × LitV)} {cs bufs : List (String × Nat)} {L : WeakMem.AllocLabel → Prop}
  {sm : WeakMem.Memory} {lsize : WeakMem.AllocLabel → Nat} {env : TermRun.Env}

/-- **More labels, a grown memory and larger sizes at `L`'s labels keep the
facts** (a suspended frame's, across its callee). -/
theorem mono {L' : WeakMem.AllocLabel → Prop} {sm' : WeakMem.Memory} {lsize' : WeakMem.AllocLabel → Nat}
    (h : EnvB lits cs bufs L sm lsize env) (hL : ∀ l, L l → L' l) (hm : ∀ sa, HasCell sm sa → HasCell sm' sa)
    (hz : ∀ l, L l → lsize l ≤ lsize' l) : EnvB lits cs bufs L' sm' lsize' env :=
  ⟨h.1.mono fun _ _ => SlP.mono hL hm, h.2.1.mono hL hm hz, h.2.2⟩

/-- **`let x = op`, `op` not `newBuf`**: `x`'s words at layout `V` with
`V`'s slices; an atom or a `nameI` copies its operand's words. -/
theorem cons (h : EnvB lits cs bufs L sm lsize env) {x : String} {op : Op} {t : Ty} {ws : List TermRun.Word}
    {V : LitV} (hs : SliceL (SlP L sm) V ws)
    (hop : ∀ a, (op = .atom a ∨ op = .nameI a) → ∃ t', TermRun.evalAt env a = some (t', ws))
    (hnb : ∀ n τ, op ≠ .newBuf n τ) :
    EnvB ((x, V) :: lits) (csAfter x cs op) (bufsAfter x cs bufs op) L sm lsize ((x, t, ws) :: env) := by
  rw [bufsAfter_of_ne hnb]
  exact ⟨h.1.cons hs, h.2.1.cons x t ws, h.2.2.after x op t ws hop⟩

/-- **`let (x, y) = a`** of a pair layout. -/
theorem split (h : EnvB lits cs bufs L sm lsize env) {a : At} {t u v : Ty} {ws : List TermRun.Word} {l r : LitV}
    {k : Nat} {x y : String} (he : TermRun.evalAt env a = some (t, ws)) (hl : litAt lits a = .node l r)
    (hk : k = l.words.length) :
    EnvB ((y, r) :: (x, l) :: lits) (unbuf y (unbuf x cs)) (unbuf y (unbuf x bufs)) L sm lsize
      ((y, v, ws.drop k) :: (x, u, ws.take k) :: env) :=
  ⟨h.1.split he hl hk, (h.2.1.cons x u _).cons y v _, (h.2.2.cons x u _).cons y v _⟩

/-- **`let (x, y) = a`** of another layout. -/
theorem splitLeaf (h : EnvB lits cs bufs L sm lsize env) {u v : Ty} {w1 w2 : List TermRun.Word} {x y : String} :
    EnvB ((y, .leaf none) :: (x, .leaf none) :: lits) (unbuf y (unbuf x cs)) (unbuf y (unbuf x bufs)) L sm lsize
      ((y, v, w2) :: (x, u, w1) :: env) :=
  ⟨h.1.splitLeaf, (h.2.1.cons x u _).cons y v _, (h.2.2.cons x u _).cons y v _⟩

/-- **An index unpack**: `x` at the package's layout. -/
theorem unpack (h : EnvB lits cs bufs L sm lsize env) {a : At} {t b : Ty} {ws : List TermRun.Word} {i x : String}
    (he : TermRun.evalAt env a = some (t, ws)) :
    EnvB ((x, litAt lits a) :: lits) (unbuf x (unbuf i cs)) (unbuf x (unbuf i bufs)) L sm lsize ((x, b, ws) :: env) :=
  ⟨h.1.cons (h.1.evalAt he), (h.2.1.unbuf i).cons x b ws, (h.2.2.unbuf i).cons x b ws⟩

/-- **A block's entry** (`countsOk2_decl`: no known value, no buffer). -/
theorem entry {d : Decl} {ws : List TermRun.Word} (hs : SliceL (SlP L sm) (shapeOf d.argTy) ws) :
    EnvB ((params2 d).map (·, shapeOf d.argTy)) [] [] L sm lsize ((d.arg, d.argTy, ws) :: env) :=
  ⟨envSl_entry hs, sBufs_nil _ _ _ _, SCs.nil _⟩

/-- **A call that passes `callsOk2`**: the callee's entry. -/
theorem call (h : EnvB lits cs bufs L sm lsize env) {a : At} {d : Decl} {t : Ty} {ws : List TermRun.Word}
    (he : TermRun.evalAt env a = some (t, ws)) (hcall : (litAt lits a).erase = shapeOf d.argTy) :
    EnvB ((params2 d).map (·, shapeOf d.argTy)) [] [] L sm lsize [(d.arg, d.argTy, ws)] :=
  entry ((h.1.evalAt he).of_erase hcall)

/-- **A return that passes `callsOk2`**: the caller's frame (its facts at
the current labels and memory, `mono`) extended by the result, as `countsB`
after a call (`csAfter`, `bufsAfter` of a call drop the name). -/
theorem ret {lc : List (String × LitV)} {fr : TermRun.Frame} {a : At} {t : Ty} {ws : List TermRun.Word}
    (h : EnvSl (SlP L sm) lc env) (he : TermRun.evalAt env a = some (t, ws))
    (hret : (litAt lc a).erase = shapeOf fr.ty) (hf : EnvB lits cs bufs L sm lsize fr.env) :
    EnvB ((fr.x, shapeOf fr.ty) :: lits) (unbuf fr.x cs) (unbuf fr.x bufs) L sm lsize ((fr.x, fr.ty, ws) :: fr.env) :=
  ⟨envSl_ret h he hret hf.1, hf.2.1.cons _ _ _, hf.2.2.cons _ _ _⟩

/-- **`let x = newBuf n τ`** of an `elem2` element (`src_newBuf_stepZ`'s
binding and memory), one thread's `k`-th label: the buffer joins `bufs` with
its known count, its label joins `L`, the bound moves to `b + (k + 1)`; the
sizes `lsize'` no smaller at `L`'s labels, holding the count at the new
label. -/
theorem newBuf {s : TermRun.St} {b k : Nat} (h : EnvB lits cs bufs L s.mem lsize env) (hm : MemB L s.mem (b + k))
    {x : String} {n : At} {τ : Ty} {σs : List Ty} {ta : Ty} {ws : List TermRun.Word} {kk : Nat}
    {us : List TermRun.Acc} (hn : TermRun.evalAt env n = some (ta, ws)) (hk : TermRun.numOf ws = some kk)
    (he2 : elem2 τ = true) (hus : TermRun.accs (TermRun.close σs τ) = some us) (ini : Nat)
    {lsize' : WeakMem.AllocLabel → Nat} (hz : ∀ l, L l → lsize l ≤ lsize' l)
    (hkz : kk ≤ lsize' (TermRun.freshLabel b 1 0 k)) :
    EnvB ((x, .loc) :: lits) (csAfter x cs (.newBuf n τ)) (bufsAfter x cs bufs (.newBuf n τ))
        (fun l => L l ∨ l = TermRun.freshLabel b 1 0 k)
        (TermRun.allocBuf (TermRun.freshLabel b 1 0 k) (kk * TermRun.nWords us)
          (AllocSrc.newBufZero (TermRun.close σs τ)) s).1.mem lsize'
        ((x, .refine (.loc .own (.array (.lit kk) (TermRun.close σs τ))) (.ini (.lit ini)),
          [TermRun.cst (.loc ⟨TermRun.freshLabel b 1 0 k, 0⟩ 0)]) :: env) ∧
      MemB (fun l => L l ∨ l = TermRun.freshLabel b 1 0 k)
        (TermRun.allocBuf (TermRun.freshLabel b 1 0 k) (kk * TermRun.nWords us)
          (AllocSrc.newBufZero (TermRun.close σs τ)) s).1.mem (b + (k + 1)) := by
  obtain ⟨hF, -⟩ := hm.2.fresh
  have hcm : ∀ sa, HasCell s.mem sa → HasCell (TermRun.allocBuf (TermRun.freshLabel b 1 0 k)
      (kk * TermRun.nWords us) (AllocSrc.newBufZero (TermRun.close σs τ)) s).1.mem sa :=
    fun sa hc => hc.allocBuf _ _ _
  have hL : ∀ l, L l → L l ∨ l = TermRun.freshLabel b 1 0 k := fun _ hl => Or.inl hl
  have hH := heapLit_allocBuf_elem2 (n := kk * TermRun.nWords us) hm.1 hF (elem2_close (σs := σs) he2)
  refine ⟨⟨(h.1.mono fun _ _ => SlP.mono hL hcm).cons (SliceL.loc _), ?_, h.2.2.cons x _ _⟩,
    hH, hm.2.allocBuf _ _⟩
  cases hc : constOf cs n with
  | none =>
    simp only [bufsAfter, hc]
    exact (h.2.1.mono hL hcm hz).cons x _ _
  | some k' =>
    obtain ⟨w, rfl, hw⟩ := h.2.2.constOf hc hn
    simp only [TermRun.numOf, hw, Option.some.injEq] at hk
    subst hk
    simp only [bufsAfter, hc]
    exact sBufs_newBuf h.2.1 x he2 hus _ hz hkz

/-- **`let x = xchgAt b i v`** (`src_xchgAt_step`'s binding and memory): the
old word at `.leaf none`, the stored number pushed at a label of `L`. -/
theorem xchgAt {B : Nat} (h : EnvB lits cs bufs L sm lsize env) (hm : MemB L sm B) {x : String} {bv i v : At}
    {u : Ty} {sa : WeakMem.Address} {k : Nat} {wo wv : TermRun.Word} (hw : IsNum wv) (hl : L sa.label)
    (mv : WeakMem.Ts) :
    EnvB ((x, .leaf none) :: lits) (csAfter x cs (.xchgAt bv i v)) (bufsAfter x cs bufs (.xchgAt bv i v)) L
        (sm.push ⟨TermRun.offs sa k, wv.val, mv⟩) lsize ((x, u, [wo]) :: env) ∧
      MemB L (sm.push ⟨TermRun.offs sa k, wv.val, mv⟩) B :=
  ⟨(h.mono (fun _ hl => hl) (fun _ hc => hc.push _) fun _ _ => Nat.le_refl _).cons (SliceL.leaf _ _)
      (by rintro _ (h | h) <;> cases h)
      (by intro _ _ h; cases h),
    heapLit_xchgAt hm.1 hw mv, hm.2.push (m := ⟨TermRun.offs sa k, wv.val, mv⟩) hl⟩

end EnvB

/-! ## Small numbers -/

/-- **Every number among the words fits in 64 bits.** -/
def WordsSmall (ws : List TermRun.Word) : Prop :=
  ∀ w ∈ ws, ∀ n, w.val = .num n → n < 2 ^ 64

theorem WordsSmall.append {ws us : List TermRun.Word} (h : WordsSmall ws) (h' : WordsSmall us) :
    WordsSmall (ws ++ us) := by
  intro w hw
  rcases List.mem_append.1 hw with hw | hw
  · exact h w hw
  · exact h' w hw

theorem WordsSmall.take {ws : List TermRun.Word} (h : WordsSmall ws) (k : Nat) : WordsSmall (ws.take k) :=
  fun w hw => h w (List.mem_of_mem_take hw)

theorem WordsSmall.drop {ws : List TermRun.Word} (h : WordsSmall ws) (k : Nat) : WordsSmall (ws.drop k) :=
  fun w hw => h w (List.mem_of_mem_drop hw)

/-- One number word. -/
theorem WordsSmall.isNum {w : TermRun.Word} (h : IsNum w) : WordsSmall [w] := by
  intro w' hw' m hm
  simp only [List.mem_singleton] at hw'
  subst hw'
  obtain ⟨n, hn, hlt⟩ := h
  rw [hn, WeakMem.Val.num.injEq] at hm
  omega

/-- One word whose number (if any) is below `2^64`. -/
theorem WordsSmall.num {n : Nat} (hn : n < 2 ^ 64) : WordsSmall [TermRun.cst (.num n)] := by
  intro w hw m hm
  simp only [List.mem_singleton] at hw
  subst hw
  simp only [TermRun.cst, Promises.TVal.mk0, WeakMem.Val.num.injEq] at hm
  omega

theorem EnvSmall.cons {env : TermRun.Env} (h : EnvSmall env) {x : String} {t : Ty} {ws : List TermRun.Word}
    (hw : WordsSmall ws) : EnvSmall ((x, t, ws) :: env) := by
  intro b hb
  rcases List.mem_cons.1 hb with rfl | hb
  · exact hw
  · exact h b hb

/-- **An atom's words are small**, a literal below `2^64` as `sevalAt`
places it. -/
theorem EnvSmall.evalAt {env : TermRun.Env} (h : EnvSmall env) {s : Spike.Lib.Form.SEnv} {a : At} {t t' : Ty}
    {pls : List Spike.Lib.Form.WordPl} {ws : List TermRun.Word} (hs : Spike.Lib.Form.sevalAt s a = some (t', pls))
    (he : TermRun.evalAt env a = some (t, ws)) : WordsSmall ws := by
  cases a with
  | var x =>
    simp only [TermRun.evalAt, TermRun.lookupE, Option.map_eq_some_iff] at he
    obtain ⟨b, hb, hbe⟩ := he
    have := h b (List.mem_of_find?_eq_some hb)
    rw [hbe] at this
    exact this
  | lit n =>
    simp only [Spike.Lib.Form.sevalAt] at hs
    split at hs
    · rename_i hn
      simp only [TermRun.evalAt, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact WordsSmall.num hn
    · cases hs
  | unit =>
    simp only [TermRun.evalAt, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    intro w hw; cases hw

/-! ## The node invariant -/

section NJB

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {rs : Scc.IR.Reg → Option Int}

/-- **The node invariant with buffers and slices**: `NJL` with `EnvB` at the
walk's `lits`, `cs`, `bufs` and `MemB` for the source memory `sm` (local
steps keep the memory); every number of the source environment fits in
64 bits (`EnvSmall`); the node invariant up to a buffer's literal lengths
(`NodeJE`). -/
def NJB (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (rs : Scc.IR.Reg → Option Int)
    (lits : List (String × LitV)) (cs bufs : List (String × Nat)) (L : WeakMem.AllocLabel → Prop)
    (sm : WeakMem.Memory) (lsize : WeakMem.AllocLabel → Nat) (B : Nat) (t : Expr) (s : SEnv)
    (sl : Int → BitVec 64) (c : Ctl) : Prop :=
  ∃ c', LocalRun p c c' ∧ NodeJE lbl rs t s sl c' ∧ EnvLit lits c'.env ∧ EnvB lits cs bufs L sm lsize c'.env ∧
    MemB L sm B ∧ EnvSmall c'.env

variable {lits : List (String × LitV)} {cs bufs : List (String × Nat)} {L : WeakMem.AllocLabel → Prop}
  {sm : WeakMem.Memory} {lsize : WeakMem.AllocLabel → Nat} {B : Nat}

/-- **The erasure keeps the placements' count.** -/
theorem plLen_eraseLen (t : Ty) : plLen t.eraseLen = plLen t := by
  unfold Ty.eraseLen
  split
  · rename_i a b
    simp only [plLen, plLen_eraseLen a, plLen_eraseLen b]
  · rfl
  · rfl

/-- **The erasure keeps the layout's shape.** -/
theorem compat_eraseLen (t : Ty) (L : LitV) : Compat t.eraseLen L = Compat t L := by
  unfold Ty.eraseLen
  split
  · rename_i a b
    cases L <;> simp only [Compat, compat_eraseLen a, compat_eraseLen b]
  · cases L <;> rfl
  · rfl

/-- Two types equal up to the erasure have the same layout's shape. -/
theorem compat_of_eraseLen {t t' : Ty} {L : LitV} (h : t'.eraseLen = t.eraseLen) : Compat t' L = Compat t L := by
  rw [← compat_eraseLen t', h, compat_eraseLen]

/-- Two types equal up to the erasure have the same placements' count. -/
theorem plLen_of_eraseLen {t t' : Ty} (h : t'.eraseLen = t.eraseLen) : plLen t' = plLen t := by
  rw [← plLen_eraseLen t', h, plLen_eraseLen]

theorem NJB.of_nodeJ {t : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} (h : NodeJ lbl rs t s sl c)
    (hn : EnvLit lits c.env) (hb : EnvB lits cs bufs L sm lsize c.env) (hm : MemB L sm B) (hs : EnvSmall c.env) :
    NJB p lbl rs lits cs bufs L sm lsize B t s sl c :=
  ⟨c, .refl c, h.toE, hn, hb, hm, hs⟩

theorem NJB.of_nodeJE {t : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} (h : NodeJE lbl rs t s sl c)
    (hn : EnvLit lits c.env) (hb : EnvB lits cs bufs L sm lsize c.env) (hm : MemB L sm B) (hs : EnvSmall c.env) :
    NJB p lbl rs lits cs bufs L sm lsize B t s sl c :=
  ⟨c, .refl c, h, hn, hb, hm, hs⟩

theorem NJB.pre {t : Expr} {s : SEnv} {sl : Int → BitVec 64} {c c0 : Ctl} (h0 : LocalRun p c0 c)
    (h : NJB p lbl rs lits cs bufs L sm lsize B t s sl c) : NJB p lbl rs lits cs bufs L sm lsize B t s sl c0 :=
  let ⟨c', hr, hj, hn, hb, hm, hs⟩ := h
  ⟨c', h0.trans hr, hj, hn, hb, hm, hs⟩

/-! ### Code-free forms -/

theorem NJB.atom {x : String} {a : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {t : Ty}
    {pls : List WordPl} (h : NJB p lbl rs lits cs bufs L sm lsize B (.let_ x (.atom a) e) s sl c)
    (ha : sevalAt s a = some (t, pls)) (hsc : InLits lits a) :
    NJB p lbl rs ((x, litAt lits a) :: lits) (csAfter x cs (.atom a)) (bufsAfter x cs bufs (.atom a)) L sm lsize B e
      ((x, t, pls) :: s) sl c := by
  obtain ⟨c1, hr, hj, hn, hb, hm, hS⟩ := h
  obtain ⟨t1, ws, he, hE, hw⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) ha
  obtain ⟨hr2, hj2⟩ := hj.step (Spike.Lib.Form.localStep_atom hj.1 he) hE hw (fun _ _ _ _ _ _ => rfl)
  obtain ⟨hc, hl⟩ := hn.evalAt hsc ha he
  refine ⟨_, hr.trans hr2, hj2, hn.cons hc hl, hb.cons (hb.1.evalAt he) ?_ (by intro _ _ h; cases h), hm,
    EnvSmall.cons hS (EnvSmall.evalAt hS ha he)⟩
  rintro a' (h | h) <;> cases h
  exact ⟨_, he⟩

theorem NJB.nameI {x : String} {a : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {t : Ty}
    {pls : List WordPl} (h : NJB p lbl rs lits cs bufs L sm lsize B (.let_ x (.nameI a) e) s sl c)
    (ha : sevalAt s a = some (t, pls)) (hsc : InLits lits a) :
    NJB p lbl rs ((x, litAt lits a) :: lits) (csAfter x cs (.nameI a)) (bufsAfter x cs bufs (.nameI a)) L sm lsize B e
      ((x, t, pls) :: s) sl c := by
  obtain ⟨c1, hr, hj, hn, hb, hm, hS⟩ := h
  obtain ⟨t1, ws, he, hE, hw⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) ha
  obtain ⟨hr2, hj2⟩ := hj.step (Spike.Lib.Form.localStep_nameI hj.1 he) hE hw (fun _ _ _ _ _ _ => rfl)
  obtain ⟨hc, hl⟩ := hn.evalAt hsc ha he
  refine ⟨_, hr.trans hr2, hj2, hn.cons hc hl, hb.cons (hb.1.evalAt he) ?_ (by intro _ _ h; cases h), hm,
    EnvSmall.cons hS (EnvSmall.evalAt hS ha he)⟩
  rintro a' (h | h) <;> cases h
  exact ⟨_, he⟩

/-- **A pair that passes `pairOk`** (`countsB_let`): its slices. -/
theorem NJB.pair {x : String} {a b : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {t u : Ty}
    {pa pb : List WordPl} (h : NJB p lbl rs lits cs bufs L sm lsize B (.let_ x (.pair a b) e) s sl c)
    (ha : sevalAt s a = some (t, pa)) (hb : sevalAt s b = some (u, pb)) (hla : plLen t = some pa.length)
    (hsa : InLits lits a) (hsb : InLits lits b) (hp : pairOk cs bufs lits (.pair a b) = true)
    (hbn : ∀ y n, a = .var y → bufs.lookup y = some n → n < 2 ^ 28) :
    NJB p lbl rs ((x, .node (litAt lits a) (litAt lits b)) :: lits) (csAfter x cs (.pair a b))
      (bufsAfter x cs bufs (.pair a b)) L sm lsize B e ((x, .prod t u, pa ++ pb) :: s) sl c := by
  obtain ⟨c1, hr, hj, hn, hB, hm, hS⟩ := h
  obtain ⟨t1, ws, he, hE, hw⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) ha
  obtain ⟨u1, us, he', hE', hw'⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) hb
  obtain ⟨hr2, hj2⟩ :=
    hj.step (Spike.Lib.Form.localStep_pair hj.1 he he') (ty := .prod t u) (by simp only [Ty.eraseLen, hE, hE'])
      (hw.append hw') (fun _ _ _ _ _ _ => rfl)
  obtain ⟨hca, hla'⟩ := hn.evalAt hsa ha he
  obtain ⟨hcb, hlb⟩ := hn.evalAt hsb hb he'
  have hlen : ws.length = (litAt lits a).words.length := by
    have := compat_plLen _ _ hca
    rw [plLen_of_eraseLen hE, hla] at this
    rw [hw.length]; exact Option.some.inj this
  refine ⟨_, hr.trans hr2, hj2, hn.cons (by simp [Compat, hca, hcb]) (hla'.pair hlb hlen), ?_, hm,
    EnvSmall.cons hS ((EnvSmall.evalAt hS ha he).append (EnvSmall.evalAt hS hb he'))⟩
  exact hB.cons (sliceL_pairOp hp hB.1 hB.2.1 hbn hB.2.2 he he' hlen) (by rintro _ (h | h) <;> cases h)
    (by intro _ _ h; cases h)

theorem NJB.pack {x w : String} {a : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {t τ : Ty}
    {pls : List WordPl} (h : NJB p lbl rs lits cs bufs L sm lsize B (.let_ x (.pack a w τ) e) s sl c)
    (ha : sevalAt s a = some (t, pls)) (hsc : InLits lits a) (hτ : Compat τ (litAt lits a) = true) :
    NJB p lbl rs ((x, litAt lits a) :: lits) (csAfter x cs (.pack a w τ)) (bufsAfter x cs bufs (.pack a w τ)) L sm lsize
      B e ((x, τ, pls) :: s) sl c := by
  obtain ⟨c1, hr, hj, hn, hb, hm, hS⟩ := h
  obtain ⟨t1, ws, he, hE, hw⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) ha
  have hst := Spike.Lib.Form.localStep_pack (p := p) hj.1 he
  rw [close_nil] at hst
  obtain ⟨hr2, hj2⟩ := hj.step hst rfl hw (fun _ _ _ _ _ _ => rfl)
  exact ⟨_, hr.trans hr2, hj2, hn.cons hτ (hn.evalAt hsc ha he).2,
    hb.cons (hb.1.evalAt he) (by rintro _ (h | h) <;> cases h) (by intro _ _ h; cases h), hm,
    EnvSmall.cons hS (EnvSmall.evalAt hS ha he)⟩

theorem NJB.asLanes {x : String} {sg : Bool} {w : Wd} {n : Nat} {e : Expr} {s : SEnv} {sl : Int → BitVec 64}
    {c : Ctl} (h : NJB p lbl rs lits cs bufs L sm lsize B (.let_ x (.asLanes sg w (.lit n)) e) s sl c)
    (hn : n < 2 ^ 64) :
    NJB p lbl rs ((x, .leaf (litAt lits (.lit n)).one) :: lits) (csAfter x cs (.asLanes sg w (.lit n)))
      (bufsAfter x cs bufs (.asLanes sg w (.lit n))) L sm lsize B e
      ((x, .lanes sg w, [.one (.imm (UInt64.ofNat n))]) :: s) sl c := by
  obtain ⟨c1, hr, hj, hnum, hb, hm, hS⟩ := h
  have hst := Spike.Lib.Form.localStep_asLanes (p := p) (n := n) hj.1 rfl
    (by simp [TermRun.numOf, TermRun.cst, Promises.TVal.mk0])
  have hw : WordsRep lbl (opdVal rs sl) [TermRun.cst (.num (n % TermRun.W64))] [.one (.imm (UInt64.ofNat n))] := by
    refine ⟨⟨n, ?_, ?_⟩, trivial⟩
    · rw [Spike.Lib.Form.opdVal_imm]; simp [Nat.mod_eq_of_lt hn]
    · simp [TermRun.cst, Promises.TVal.mk0, ValRep, TermRun.W64, Nat.mod_eq_of_lt hn, hn]
  obtain ⟨hr3, hj3⟩ := hj.step hst rfl hw (fun _ _ _ _ _ _ => rfl)
  refine ⟨_, hr.trans hr3, hj3, hnum.cons rfl (NumL.of_all fun w' hw' => ?_),
    hb.cons (SliceL.leaf _ _) (by rintro _ (h | h) <;> cases h) (by intro _ _ h; cases h), hm,
    EnvSmall.cons hS (WordsSmall.num (Nat.lt_of_le_of_lt (Nat.mod_le _ _) hn))⟩
  simp only [List.mem_singleton] at hw'
  subst hw'
  exact ⟨n % TermRun.W64, by simp [TermRun.cst, Promises.TVal.mk0], Nat.lt_of_le_of_lt (Nat.mod_le _ _) hn⟩

/-- **`let (x, y) = a`** of a pair layout (`countsB_split`). -/
theorem NJB.split {a : At} {x y : String} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {u v : Ty}
    {pls : List WordPl} {us : List TermRun.Acc} {l r : LitV}
    (h : NJB p lbl rs lits cs bufs L sm lsize B (.split a x y e) s sl c)
    (ha : sevalAt s a = some (.prod u v, pls)) (hu : TermRun.accs u = some us)
    (hk : plLen u = some (TermRun.nWords us)) (hsc : InLits lits a) (hl : litAt lits a = .node l r) :
    NJB p lbl rs ((y, r) :: (x, l) :: lits) (unbuf y (unbuf x cs)) (unbuf y (unbuf x bufs)) L sm lsize B e
      ((y, v, pls.drop (TermRun.nWords us)) :: (x, u, pls.take (TermRun.nWords us)) :: s) sl c := by
  obtain ⟨c1, hr, hj, hn, hb, hm, hS⟩ := h
  obtain ⟨t1, ws, he, hE, hw⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) ha
  obtain ⟨u1, v1, rfl, hu1, hv1⟩ := Spike.Lib.Form.eraseLen_eq_prod hE
  have hu' : TermRun.accs u1 = some us := by
    rw [← Spike.Lib.Form.accs_eraseLen, hu1, Spike.Lib.Form.accs_eraseLen]; exact hu
  have hst := Spike.Lib.Form.localStep_split (p := p) (y := y) hj.1 he hu'
  obtain ⟨hc, hnl⟩ := hn.evalAt hsc ha he
  rw [hl] at hc hnl
  simp only [Compat, Bool.and_eq_true] at hc
  have hkl : TermRun.nWords us = l.words.length := by
    have := compat_plLen _ _ hc.1
    rw [plLen_of_eraseLen hu1, hk] at this; exact Option.some.inj this
  obtain ⟨h1, h2⟩ := hnl.split
  rw [← hkl] at h1 h2
  exact ⟨_, hr.trans (.single hst), ⟨rfl, rfl, (hj.2.2.bind _ hu1 (hw.take _)).bind _ hv1 (hw.drop _)⟩,
    (hn.cons hc.1 h1).cons hc.2 h2, hb.split he hl hkl, hm,
    EnvSmall.cons (EnvSmall.cons hS ((EnvSmall.evalAt hS ha he).take _)) ((EnvSmall.evalAt hS ha he).drop _)⟩

/-- **An index unpack** (`countsB_unpack`). -/
theorem NJB.unpack {a : At} {i x : String} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {b : Ty}
    {pls : List WordPl} (h : NJB p lbl rs lits cs bufs L sm lsize B (.unpack a i x e) s sl c)
    (ha : sevalAt s a = some (.iex b, pls)) (hsc : InLits lits a) :
    NJB p lbl rs ((x, litAt lits a) :: lits) (unbuf x (unbuf i cs)) (unbuf x (unbuf i bufs)) L sm lsize B e
      ((x, b, pls) :: s) sl c := by
  obtain ⟨c1, hr, hj, hn, hb, hm, hS⟩ := h
  obtain ⟨t1, ws, he, hE, hw⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) ha
  obtain rfl := Spike.Lib.Form.eraseLen_eq_iex hE
  have hst := Spike.Lib.Form.localStep_unpack (p := p) (i := i) hj.1 he
  obtain ⟨hc, hnl⟩ := hn.evalAt hsc ha he
  simp only [Compat, Bool.and_eq_true] at hc
  exact ⟨_, hr.trans (.single hst), ⟨rfl, rfl, hj.2.2.bind _ rfl hw⟩, hn.cons hc.2 hnl, hb.unpack he, hm,
    EnvSmall.cons hS (EnvSmall.evalAt hS ha he)⟩

/-! ### Checked arithmetic and the `if` -/

theorem NJB.ops {t : Expr} {a b : At} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {ta tb : Ty}
    {pa pb : Scc.IR.Operand} {va vb : Nat} (h : NJB p lbl rs lits cs bufs L sm lsize B t s sl c)
    (ha : sevalAt s a = some (ta, [.one pa])) (hb : sevalAt s b = some (tb, [.one pb]))
    (hsa : InLits lits a) (hsb : InLits lits b)
    (hma : litMask (litAt lits a) = [true]) (hmb : litMask (litAt lits b) = [true])
    (hva : opdVal rs sl pa = some va) (hvb : opdVal rs sl pb = some vb) :
    ∃ c1 wa wb ta' tb', LocalRun p c c1 ∧ NodeJE lbl rs t s sl c1 ∧ EnvLit lits c1.env ∧
      EnvB lits cs bufs L sm lsize c1.env ∧ MemB L sm B ∧ EnvSmall c1.env ∧ TermRun.evalAt c1.env a = some (ta', [wa]) ∧
      TermRun.evalAt c1.env b = some (tb', [wb]) ∧
      ValRep lbl wa.val va ∧ ValRep lbl wb.val vb ∧ wa.val = .num va ∧ wb.val = .num vb ∧
      va < 2 ^ 64 ∧ vb < 2 ^ 64 := by
  obtain ⟨c1, hr, hj, hn, hB, hm, hS⟩ := h
  obtain ⟨ta', wsa, hea, -, hwa⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) ha
  obtain ⟨tb', wsb, heb, -, hwb⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) hb
  have hna := (hn.evalAt hsa ha hea).2
  have hnb := (hn.evalAt hsb hb heb).2
  match wsa, wsb, hwa, hwb, hna, hnb with
  | [wa], [wb], ⟨⟨v, hv, hra⟩, _⟩, ⟨⟨u, hu, hrb⟩, _⟩, hna, hnb =>
    rw [hva] at hv; rw [hvb] at hu
    cases hv; cases hu
    obtain ⟨n, hn1, hn2⟩ := hna.one hma
    obtain ⟨m, hm1, hm2⟩ := hnb.one hmb
    have e1 := hra; rw [hn1] at e1
    have e2 := hrb; rw [hm1] at e2
    rw [valRep_num e1] at hra ⊢; rw [valRep_num e2] at hrb ⊢
    exact ⟨c1, wa, wb, ta', tb', hr, hj, hn, hB, hm, hS, hea, heb, hra, hrb, hn1, hm1, hn2, hm2⟩

theorem NJB.add_ok {x : String} {a b : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {ta tb : Ty}
    {pa pb : Scc.IR.Operand} {va vb : Nat} (h : NJB p lbl rs lits cs bufs L sm lsize B (.let_ x (.add a b) e) s sl c)
    (ha : sevalAt s a = some (ta, [.one pa])) (hb : sevalAt s b = some (tb, [.one pb]))
    (hsa : InLits lits a) (hsb : InLits lits b)
    (hma : litMask (litAt lits a) = [true]) (hmb : litMask (litAt lits b) = [true])
    (hva : opdVal rs sl pa = some va) (hvb : opdVal rs sl pb = some vb) (hlt : va + vb < 2 ^ 64)
    {d : Scc.IR.Reg} {k : Int} (hd : rs d = some k)
    (hfr : ∀ q ∈ s, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, ∀ r k', o = .reg r → rs r = some k' → k' ≠ k)
    {v : BitVec 64} (hv : v.toNat = va + vb) :
    NJB p lbl rs ((x, .leaf none) :: lits) (csAfter x cs (.add a b)) (bufsAfter x cs bufs (.add a b)) L sm lsize B e
      ((x, .int, [.one (.reg d)]) :: s) (upd sl k v) c := by
  obtain ⟨c1, wa, wb, _, _, hr, hj, hn, hB, hm, hS, hea, heb, hra, hrb, hna, hnb, -, -⟩ :=
    h.ops ha hb hsa hsb hma hmb hva hvb
  have hst := localStep_add (p := p) hj.1 hea heb
  refine ⟨_, hr.trans (.single hst), (hj.step hst rfl ?_ ?_).2, hn.cons rfl (NumL.of_all fun w hw => ?_),
    hB.cons (SliceL.leaf _ _) (by rintro _ (h | h) <;> cases h) (by intro _ _ h; cases h), hm,
    EnvSmall.cons hS ?_⟩
  · refine ⟨⟨va + vb, ?_, Scc.Sem.valRep_addW hra hrb hlt⟩, trivial⟩
    simp [opdVal, hd, upd_apply, hv]
  · intro q hq pl hpl o ho
    exact Spike.Lib.Form.opdVal_upd fun r k' hor hr' => by
      simp [upd_apply, hfr q hq pl hpl o ho r k' hor hr']
  · simp only [List.mem_singleton] at hw
    subst hw
    exact ⟨va + vb, by simp [TermRun.addW, hna, hnb, TermRun.cst]; rfl, hlt⟩
  · have : TermRun.addW wa wb = TermRun.cst (.num (va + vb)) := by simp [TermRun.addW, hna, hnb]
    rw [this]; exact WordsSmall.num hlt

theorem NJB.sub_ok {x : String} {a b : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {ta tb : Ty}
    {pa pb : Scc.IR.Operand} {va vb : Nat} (h : NJB p lbl rs lits cs bufs L sm lsize B (.let_ x (.sub a b) e) s sl c)
    (ha : sevalAt s a = some (ta, [.one pa])) (hb : sevalAt s b = some (tb, [.one pb]))
    (hsa : InLits lits a) (hsb : InLits lits b)
    (hma : litMask (litAt lits a) = [true]) (hmb : litMask (litAt lits b) = [true])
    (hva : opdVal rs sl pa = some va) (hvb : opdVal rs sl pb = some vb)
    {d : Scc.IR.Reg} {k : Int} (hd : rs d = some k)
    (hfr : ∀ q ∈ s, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, ∀ r k', o = .reg r → rs r = some k' → k' ≠ k)
    {v : BitVec 64} (hv : v.toNat = va - vb) :
    NJB p lbl rs ((x, .leaf none) :: lits) (csAfter x cs (.sub a b)) (bufsAfter x cs bufs (.sub a b)) L sm lsize B e
      ((x, .int, [.one (.reg d)]) :: s) (upd sl k v) c := by
  obtain ⟨c1, wa, wb, _, _, hr, hj, hn, hB, hm, hS, hea, heb, hra, hrb, hna, hnb, hlta, -⟩ :=
    h.ops ha hb hsa hsb hma hmb hva hvb
  have hst := localStep_sub (p := p) hj.1 hea heb
  refine ⟨_, hr.trans (.single hst), (hj.step hst rfl ?_ ?_).2, hn.cons rfl (NumL.of_all fun w hw => ?_),
    hB.cons (SliceL.leaf _ _) (by rintro _ (h | h) <;> cases h) (by intro _ _ h; cases h), hm,
    EnvSmall.cons hS ?_⟩
  · refine ⟨⟨va - vb, ?_, Scc.Sem.valRep_subW hra hrb⟩, trivial⟩
    simp [opdVal, hd, upd_apply, hv]
  · intro q hq pl hpl o ho
    exact Spike.Lib.Form.opdVal_upd fun r k' hor hr' => by
      simp [upd_apply, hfr q hq pl hpl o ho r k' hor hr']
  · simp only [List.mem_singleton] at hw
    subst hw
    exact ⟨va - vb, by simp [TermRun.subW, hna, hnb, TermRun.cst]; rfl, by omega⟩
  · have : TermRun.subW wa wb = TermRun.cst (.num (va - vb)) := by simp [TermRun.subW, hna, hnb]
    rw [this]; exact WordsSmall.num (by omega)

/-- **The `if`** (`countsB_ifeq`: both branches from the same state). -/
theorem NJB.ifeq {a b : At} {yes no : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {ta tb : Ty}
    {pa pb : Scc.IR.Operand} {va vb : Nat} (h : NJB p lbl rs lits cs bufs L sm lsize B (.ifeq a b yes no) s sl c)
    (ha : sevalAt s a = some (ta, [.one pa])) (hb : sevalAt s b = some (tb, [.one pb]))
    (hsa : InLits lits a) (hsb : InLits lits b)
    (hma : litMask (litAt lits a) = [true]) (hmb : litMask (litAt lits b) = [true])
    (hva : opdVal rs sl pa = some va) (hvb : opdVal rs sl pb = some vb) :
    NJB p lbl rs lits cs bufs L sm lsize B (if va = vb then yes else no) s sl c := by
  obtain ⟨c1, wa, wb, _, _, hr, hj, hn, hB, hm, hS, hea, heb, -, -, hna, hnb, -, -⟩ :=
    h.ops ha hb hsa hsb hma hmb hva hvb
  have hst := localStep_ifeq (p := p) hj.1 hea heb hna hnb
  exact ⟨_, hr.trans (.single hst), ⟨rfl, rfl, hj.2.2⟩, hn, hB, hm, hS⟩

end NJB

end Spike.Lib.LowerNode
