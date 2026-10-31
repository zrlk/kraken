import Spike.Lib.Src.SrcSafe2
import Spike.Lib.Src.XchgLeaf
import Spike.Lib.Src.NJLBS
import Spike.Lib.Src.HeapLit
import Spike.Lib.PrintSrc
import Spike.Lib.Src.SrcNumE
import WeakCore.TermUndefLow

/-!
**The source's printed cells hold numbers** (ISA-neutral): `SrcNumSP`, the
`SrcNumS` premise with the thread's promises empty, for `Accepted2` programs.

Part (a), the memory: `MemNP` (one thread; every message the thread has not
promised holds a number) is kept by promise steps, and by thread steps whose
single-word writes and new messages hold numbers (`memNP_thread`); with no
promise every cell's latest message is a number (`MemNP.latest`).
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm A9NoSpawn TermRun Scc.Sem
open TermCert (MemExt)
open TermFul (promsOf promsOf_some PWF)
open Scc.Sem.MemRel (SLatest)

/-- **The memory's numbers**: one thread, and every message it has not
promised holds a number. -/
def MemNP (c : Cfg) : Prop :=
  c.ths.size = 1 ∧ ∀ k m, c.mem[k]? = some m → k ∉ promsOf c 0 → ∃ n, m.val = .num n

theorem memExt_get {M M' : WeakMem.Memory} (h : MemExt M M') {k : Nat} (hk : k < M.size) :
    M'[k]? = M[k]? := by
  have h0 : M[k]? = some M[k] := by simp [hk]
  rw [h0]; exact h k _ h0

/-- **A promise step keeps `MemNP`**: the new message is promised. -/
theorem memNP_prom {c : Cfg} {i : Nat} {a : WeakMem.Address} {v : WeakMem.Val} {w : WeakMem.Ts}
    (h : MemNP c) (hi : i < c.ths.size) : MemNP (promise c i a v w) := by
  have hi0 : i = 0 := by have := h.1; omega
  subst hi0
  obtain ⟨th, hth⟩ : ∃ th, c.ths[0]? = some th := ⟨c.ths[0], by simp [hi]⟩
  have e1 : (promise c 0 a v w).mem = c.mem.push ⟨a, v, w⟩ := by simp [promise, hth]
  have hx : (promise c 0 a v w).ths[0]? = some { th with promises := th.promises ++ [c.mem.size] } := by
    simp only [promise, hth]; exact TermCert.arr_set hth
  refine ⟨?_, fun k m hk hn => ?_⟩
  · simp [promise, h.1]
  · rw [promsOf_some hx] at hn
    rw [e1, Array.getElem?_push] at hk
    split at hk
    · exact absurd (List.mem_append_right _ (List.mem_singleton.mpr (by assumption))) hn
    · exact h.2 k m hk fun h' => hn (List.mem_append_left _ (by rw [promsOf_some hth] at h'; exact h'))

/-- **A thread step keeps `MemNP`** when its single-word writes (`SW`) and
its new messages hold numbers. -/
theorem memNP_thread {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {c c' : Cfg} {i : Nat}
    (h : MemNP c) (hw : PWF c 0) (hs : c' ∈ threadSteps p k arch c i)
    (hsw : ∀ th, c.ths[i]? = some th → ∀ l v, TermFul.SW (gOf p k arch c i) c.mem c.pairs th l v →
      ∃ n, v = .num n)
    (hnew : ∀ th r, c.ths[i]? = some th → r ∈ tstep (gOf p k arch c i) c.mem c.pairs th →
      ∀ t m, c.mem.size ≤ t → r.1[t]? = some m → ∃ n, m.val = .num n) : MemNP c' := by
  obtain ⟨th, r, hth, hr, e1, -, e3, e4⟩ := TermFul.threadSteps_inv hs
  have hi0 : i = 0 := by
    have := (Array.getElem?_eq_some_iff.mp hth).1; have := h.1; omega
  subst hi0
  refine ⟨e4 ▸ h.1, fun t m hk hn => ?_⟩
  rw [promsOf_some e3] at hn
  rw [e1] at hk
  by_cases hlt : t < c.mem.size
  · rw [memExt_get (TermFul.tstep_grow hr).1 hlt] at hk
    by_cases hp : t ∈ th.promises
    · have hw2 : ∀ t, t ∈ th.promises → t < c.mem.size ∧ t ∉ c.pairs :=
        fun t ht => hw.2 t (by rw [promsOf_some hth]; exact ht)
      obtain ⟨m', hm', hsw', -⟩ :=
        (TermFul.tstep_fulfil (fun t ht => (hw2 t ht).1) (fun t ht => (hw2 t ht).2) hr).2 t hp hn
      rw [hk] at hm'; cases hm'
      exact hsw th hth _ _ hsw'
    · exact h.2 t m hk (by rw [promsOf_some hth]; exact hp)
  · exact hnew th r hth hr t m (Nat.le_of_not_lt hlt) hk

/-- **With no promise, a cell's latest message is a number.** -/
theorem MemNP.latest {c : Cfg} {th : TTh} (h : MemNP c) (hth : c.ths[0]? = some th) (hp : th.promises = [])
    {sa : WeakMem.Address} (hc : HasCell c.mem sa) :
    ∃ (j : Nat) (m : WeakMem.Msg) (n : Nat), SLatest c.mem sa j ∧ c.mem[j]? = some m ∧ m.val = .num n := by
  obtain ⟨j, hj⟩ := Spike.Lib.Consumer1.exists_sLatest hc
  obtain ⟨m, hm, -⟩ := hj.1
  obtain ⟨n, hn⟩ := h.2 j m hm (by rw [promsOf_some hth, hp]; exact List.not_mem_nil)
  exact ⟨j, m, n, hj, hm, hn⟩


/-! ## Numbers along the walk (any size: the source's `+` does not wrap) -/

section walk

open Scc.Lower (LitV litAt shapeOf params2 litWalk2 litWalks2 simpleTy)

/-- **A word holding a number** (of any size). -/
def NumW (w : Word) : Prop := ∃ n, w.val = .num n

/-- **The words at a layout's leaves are numbers** (`NumL` without the bound). -/
def NumLN (L : LitV) (ws : List Word) : Prop :=
  ∀ (i : Nat) w, ws[i]? = some w → (litMask L)[i]? = some true → NumW w

namespace NumLN

theorem nil (L : LitV) : NumLN L [] := fun _ _ h => by simp at h

theorem pair {la lb : LitV} {wa wb : List Word} (ha : NumLN la wa) (hb : NumLN lb wb)
    (hl : wa.length = la.words.length) : NumLN (.node la lb) (wa ++ wb) := by
  intro i w hw hi
  have hlen : (litMask la).length = wa.length := by rw [litMask_length, hl]
  simp only [litMask] at hi
  by_cases hi' : i < wa.length
  · rw [List.getElem?_append_left hi'] at hw
    rw [List.getElem?_append_left (by omega)] at hi
    exact ha i w hw hi
  · rw [List.getElem?_append_right (by omega)] at hw
    rw [List.getElem?_append_right (by omega), hlen] at hi
    exact hb _ w hw hi

theorem split {l r : LitV} {ws : List Word} (h : NumLN (.node l r) ws) :
    NumLN l (ws.take l.words.length) ∧ NumLN r (ws.drop l.words.length) := by
  have hlen := litMask_length l
  constructor
  · intro i w hw hi
    have hik : i < l.words.length := by
      rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hi).1
    rw [List.getElem?_take, ite_eq_left_iff.mpr (fun h => absurd hik h)] at hw
    exact h i w hw (by simp only [litMask]; rw [List.getElem?_append_left (by omega)]; exact hi)
  · intro i w hw hi
    rw [List.getElem?_drop] at hw
    exact h _ w hw (by simp only [litMask]; rw [List.getElem?_append_right (by omega), hlen]; simpa using hi)

theorem one {L : LitV} {w : Word} (h : NumLN L [w]) (hm : litMask L = [true]) : NumW w :=
  h 0 w rfl (by rw [hm]; rfl)

theorem of_erase {L M : LitV} {ws : List Word} (h : NumLN L ws) (he : L.erase = M) : NumLN M ws := by
  intro i w hw hi
  rw [← he, litMask_erase] at hi
  exact h i w hw hi

theorem of_all {L : LitV} {ws : List Word} (h : ∀ w ∈ ws, NumW w) : NumLN L ws :=
  fun _ w hw _ => h w (List.mem_of_getElem? hw)

end NumLN

theorem words_length_erase (L : LitV) : L.erase.words.length = L.words.length := by
  rw [← litMask_length, ← litMask_length, litMask_erase]

/-- **A binding against its layout**: the type has the layout (`Compat`) and
a runtime layout (`simpleTy`), one word per layout word, numbers at leaves. -/
def BindN (t : Ty) (L : LitV) (ws : List Word) : Prop :=
  Compat t L = true ∧ simpleTy t = true ∧ ws.length = L.words.length ∧ NumLN L ws

namespace BindN

theorem pair {t u : Ty} {la lb : LitV} {wa wb : List Word} (ha : BindN t la wa) (hb : BindN u lb wb) :
    BindN (.prod t u) (.node la lb) (wa ++ wb) :=
  ⟨by simp [Compat, ha.1, hb.1], by simp [simpleTy, ha.2.1, hb.2.1],
    by simp [LitV.words, ha.2.2.1, hb.2.2.1], ha.2.2.2.pair hb.2.2.2 ha.2.2.1⟩

/-- A pair type's layout is a node. -/
theorem node_of_prod {u w : Ty} {L : LitV} {ws : List Word} (h : BindN (.prod u w) L ws) :
    ∃ l r, L = .node l r := by
  have hc := h.1
  cases L <;> simp [Compat] at hc
  exact ⟨_, _, rfl⟩

/-- **A pair's parts**, split as `TermRun.tstep` splits (`accs`). -/
theorem split {u w : Ty} {l r : LitV} {ws : List Word} {us : List Acc} (h : BindN (.prod u w) (.node l r) ws)
    (hu : accs u = some us) :
    BindN u l (ws.take (nWords us)) ∧ BindN w r (ws.drop (nWords us)) := by
  obtain ⟨hc, hs, hl, hn⟩ := h
  simp only [Compat, Bool.and_eq_true] at hc
  simp only [simpleTy, Bool.and_eq_true] at hs
  have hk : nWords us = l.words.length := by
    have := accs_simple u hs.1 _ (compat_plLen u l hc.1)
    rw [hu] at this; exact Option.some.inj this
  simp only [LitV.words, List.length_append] at hl
  obtain ⟨h1, h2⟩ := hn.split
  rw [hk]
  exact ⟨⟨hc.1, hs.1, by simp [hl], h1⟩, ⟨hc.2, hs.2, by simp [hl], h2⟩⟩

theorem unpack {b : Ty} {L : LitV} {ws : List Word} (h : BindN (.iex b) L ws) : BindN b L ws := by
  obtain ⟨hc, hs, hl, hn⟩ := h
  simp only [Compat, Bool.and_eq_true] at hc
  exact ⟨hc.2, hs, hl, hn⟩

/-- **Across a call or a return**: at the declared layout `shapeOf T`. -/
theorem decl {t T : Ty} {L : LitV} {ws : List Word} (h : BindN t L ws) (he : L.erase = shapeOf T)
    (hc : Compat T (shapeOf T) = true) (hs : simpleTy T = true) : BindN T (shapeOf T) ws :=
  ⟨hc, hs, by rw [h.2.2.1, ← he, words_length_erase], h.2.2.2.of_erase he⟩

theorem one {t : Ty} {L : LitV} {w : Word} (h : BindN t L [w]) (hm : litMask L = [true]) : NumW w :=
  h.2.2.2.one hm

end BindN

/-- **An environment against the walk's bindings**, but the names of `X`
(never read: `main`'s parameter and its thread word). -/
def EnvN (X : String → Prop) (lits : List (String × LitV)) (env : Env) : Prop :=
  ∀ x L, lits.lookup x = some L → ¬ X x → ∃ t ws, lookupE env x = some (t, ws) ∧ BindN t L ws

theorem EnvN.cons {X : String → Prop} {lits : List (String × LitV)} {env : Env} (h : EnvN X lits env)
    {x : String} {L : LitV} {t : Ty} {ws : List Word} (hb : BindN t L ws) :
    EnvN (fun z => z ≠ x ∧ X z) ((x, L) :: lits) ((x, t, ws) :: env) := by
  intro y M hy hX
  rw [lookup_cons_name] at hy
  rw [lookupE_cons]
  split at hy
  · cases hy; rename_i hyx; exact ⟨t, ws, by simp [hyx], hb⟩
  · rename_i hyx; simp only [hyx, ite_false]; exact h y M hy fun hx => hX ⟨hyx, hx⟩

theorem EnvN.anti {X Y : String → Prop} {lits : List (String × LitV)} {env : Env} (h : EnvN X lits env)
    (hXY : ∀ z, X z → Y z) : EnvN Y lits env :=
  fun x L hx hy => h x L hx fun hX => hy (hXY x hX)

/-- **An atom's words**, the atom bound in the walk and not of `X`. -/
theorem EnvN.evalAt {X : String → Prop} {lits : List (String × LitV)} {env : Env} (h : EnvN X lits env)
    {a : At} {t : Ty} {ws : List Word} (hsc : InLits lits a) (hX : ∀ z, a = .var z → ¬ X z)
    (he : TermRun.evalAt env a = some (t, ws)) : BindN t (litAt lits a) ws := by
  cases a with
  | var x =>
    obtain ⟨L, hL⟩ := Option.isSome_iff_exists.1 (hsc x rfl)
    obtain ⟨t0, ws0, he0, hb⟩ := h x L hL (hX x rfl)
    simp only [TermRun.evalAt, he0, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    simp only [litAt, hL, Option.getD_some]
    exact hb
  | lit n =>
    simp only [TermRun.evalAt, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨rfl, rfl, rfl, NumLN.of_all fun w hw => ?_⟩
    simp only [List.mem_singleton] at hw; subst hw
    exact ⟨n, by simp [cst, Promises.TVal.mk0]⟩
  | unit =>
    simp only [TermRun.evalAt, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨rfl, rfl, rfl, NumLN.nil _⟩

/-- **A block's entry**: its parameter at its declared layout. -/
theorem envN_entry {X : String → Prop} {d : Decl} {ws : List Word} (hb : BindN d.argTy (shapeOf d.argTy) ws) :
    EnvN X ((params2 d).map (·, shapeOf d.argTy)) [(d.arg, d.argTy, ws)] := by
  intro y M hy _
  unfold params2 at hy
  split at hy
  · cases hy
  · simp only [List.map_cons, List.map_nil, lookup_cons_name, List.lookup_nil] at hy
    split at hy
    · cases hy; rename_i hyx; exact ⟨d.argTy, ws, by rw [lookupE_cons]; simp [hyx], hb⟩
    · cases hy

end walk

/-! ## The frames -/

section frames

open Scc.Lower (LitV litAt opLit shapeOf params2 litWalk2 litWalks2 simpleTy body2 unbuf constOf bindC elem2 atom1
  mentions termKey2 argShape)

/-- **The numbers a lowered body keeps** at a point of the walk: `xchgLeafQ`,
and both operands of `+` and `-` at a leaf. -/
def numQ (q : Expr × List (String × LitV)) : Bool :=
  xchgLeafQ q && match q.1 with
    | .let_ _ (.add a b) _ | .let_ _ (.sub a b) _ => litMask (litAt q.2 a) == [true] && litMask (litAt q.2 b) == [true]
    | _ => true

/-- **The lowering gives `numQ` at every `let`**: `+` and `-` take one-word
operands (`evalOne`, `post_evalOne_leaf`), and `xchgLeafQ`. -/
theorem letQ_numQ (cx : Scc.Lower.Ctx) : LetQ cx numQ := by
  intro cx2 cs bufs scope env lits x op e hb hR hB
  have hx := letQ_xchgLeaf cx cx2 cs bufs scope env lits x op e hb hR hB
  cases op with
  | add a b =>
    simp only [body2, Bool.and_eq_true] at hb
    simp only [Scc.Lower.lowerOp]
    refine Post.bind (post_evalOne_leaf hR hb.1.1 "+") fun _ ha =>
      Post.bind (post_evalOne_leaf hR hb.1.2 "+") fun _ hb' => Post.bind' fun _ => Post.bind' fun _ => Post.pure ?_
    simp [numQ, xchgLeafQ, ha, hb']
  | sub a b =>
    simp only [body2, Bool.and_eq_true] at hb
    simp only [Scc.Lower.lowerOp]
    refine Post.bind (post_evalOne_leaf hR hb.1.1 "-") fun _ ha =>
      Post.bind (post_evalOne_leaf hR hb.1.2 "-") fun _ hb' => Post.bind' fun _ => Post.bind' fun _ => Post.pure ?_
    simp [numQ, xchgLeafQ, ha, hb']
  | _ => exact Post.mono hx fun _ h => by simp [numQ, h]

theorem otherQ_numQ : OtherQ numQ := by
  intro ⟨e, lits⟩ h
  simp only [numQ, otherQ_xchgLeaf _ h, Bool.true_and]
  split
  · exact absurd rfl (h _ _ _)
  · exact absurd rfl (h _ _ _)
  · rfl

theorem numQ_printExt {p : Prog} :
    ∀ q ∈ litWalk2 p ((params2 Scc.Frontend.printExtD).map (·, shapeOf Scc.Frontend.printExtD.argTy))
      Scc.Frontend.printExtD.body, numQ q = true := by
  exact List.all_eq_true.1 rfl

theorem numQ_printLoop {p : Prog} :
    ∀ q ∈ litWalk2 p ((params2 Scc.Frontend.printLoopD).map (·, shapeOf Scc.Frontend.printLoopD.argTy))
      Scc.Frontend.printLoopD.body, numQ q = true := by
  exact List.all_eq_true.1 rfl

/-- **Every point of an `Accepted2` program's walk has `numQ`** when its
lowering succeeds (`lowerWithMarks`, the frontend's externs): the premise
`hn` of `srcNumS_of_accepted2` from the compiler's success. -/
theorem numQ_of_lowerWithMarks {p : Prog} (hp : Scc.Lower.Accepted2 p = true) {cfg : Scc.Config}
    {c : Scc.Frontend.Checked} (hcp : c.prog = p) (hce : c.externs = Scc.Frontend.externs p)
    {x} (h : Scc.Lower.lowerWithMarks cfg c = .ok x) :
    ∀ q ∈ litWalks2 p, numQ q = true :=
  walkQ_of_lowerWithMarks letQ_numQ otherQ_numQ numQ_printExt numQ_printLoop hp hcp hce h

/-- **The facts the program gives at a point of a block's walk**, `R` the
block's result type: `numQ`, `layQ`, and `callsOk2`'s layouts. -/
def GoodQ (p : Prog) (R : Ty) (q : Expr × List (String × LitV)) : Prop :=
  numQ q = true ∧ layQ q = true ∧
    (∀ x g is a ts e, q.1 = .let_ x (.call g is a ts) e → (litAt q.2 a).erase = argShape p g) ∧
    (∀ a, q.1 = .ret a → (litAt q.2 a).erase = shapeOf R)

/-- **A frame at a point of an `Accepted2` body** (result type `R`): `body2`,
its scope bound in the walk, its buffers and known values, the walk's
bindings but `X`'s (never mentioned), the program's facts at every later
point, `countsOk2` from here with every binding's slices (`EnvSl`), and the
extern's loop excluded from the callees. -/
def WN (p : Prog) (mem : WeakMem.Memory) (R : Ty) (e : Expr) (env : Env) : Prop :=
  ∃ (cx : Scc.Lower.Cx2) (cs bufs : List (String × Nat)) (scope : List String) (lits : List (String × LitV))
    (X : String → Prop), body2 cx cs bufs scope e = true ∧ (∀ z ∈ scope, (lits.lookup z).isSome = true) ∧
    SBufsA env bufs LAll mem ∧ SCs env cs ∧ EnvN X lits env ∧ (∀ z, X z → mentions z e = false) ∧
    (∀ q ∈ litWalk2 p lits e, GoodQ p R q) ∧ Scc.Lower.countsB p cs bufs lits e = true ∧
    EnvSl (SlP LAll mem) lits env ∧ (Scc.Lower.hasPrint p = true → cx.excl.contains "printL" = true)

/-- A memory's slices are a larger memory's. -/
theorem SliceL.memExt {mem mem' : WeakMem.Memory} (hm : MemExt mem mem') {V : LitV} {ws : List Word}
    (h : SliceL (SlP LAll mem) V ws) : SliceL (SlP LAll mem') V ws :=
  h.mono fun _ _ h => SlP.mono (fun _ h => h) (fun _ => hasCell_of_memExt hm) h

theorem EnvSl.memExt {mem mem' : WeakMem.Memory} (hm : MemExt mem mem') {lits : List (String × LitV)} {env : Env}
    (h : EnvSl (SlP LAll mem) lits env) : EnvSl (SlP LAll mem') lits env :=
  h.mono fun _ _ h => SlP.mono (fun _ h => h) (fun _ => hasCell_of_memExt hm) h

theorem WN.mono {p : Prog} {mem mem' : WeakMem.Memory} {R : Ty} {e : Expr} {env : Env} (h : WN p mem R e env)
    (hm : MemExt mem mem') : WN p mem' R e env := by
  obtain ⟨cx, cs, bufs, scope, lits, X, hb, hsc, hB, hC, hN, hX, hG, hK, hS, hL⟩ := h
  exact ⟨cx, cs, bufs, scope, lits, X, hb, hsc, hB.mono (fun _ h => h) (fun _ => hasCell_of_memExt hm), hC, hN,
    hX, hG, hK, hS.memExt hm, hL⟩

/-- **A `body2` `let` mentions what its body mentions.** -/
theorem mentions_let {cx : Scc.Lower.Cx2} {cs bufs : List (String × Nat)} {scope : List String} {x z : String}
    {op : Op} {e : Expr} (hb : body2 cx cs bufs scope (.let_ x op e) = true) (h : mentions z (.let_ x op e) = false) :
    mentions z e = false := by
  unfold mentions at *
  cases op <;> (try simp only [body2, Bool.false_eq_true] at hb) <;> simp_all [termKey2]

/-- An operand in the scope is bound in the walk. -/
theorem inLits_of_atom1' {scope : List String} {lits : List (String × LitV)}
    (hsc : ∀ z ∈ scope, (lits.lookup z).isSome = true) {a : At} (h : atom1 scope a = true) : InLits lits a :=
  fun z hz => hsc z (atom1_var h z hz)

end frames

/-! ## One step of a W frame -/

section wstep

open Scc.Lower (LitV litAt opLit shapeOf params2 litWalk2 litWalks2 simpleTy body2 unbuf constOf bindC elem2 atom1
  mentions termKey2 argShape atKey)

theorem evalOp_xchgAt_ty {g : G} {env : Env} {σs : List Ty} {s s' : St} {b i v : At} {t : Ty} {ws : List Word}
    (h : (s', t, ws) ∈ evalOp g env σs s (.xchgAt b i v)) :
    ∃ tb pw μ, TermRun.evalAt env b = some (tb, [pw]) ∧ bufElem tb = some (μ, t) := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals try (simp at h; done)
  simp only [List.mem_flatMap, List.mem_map] at h
  obtain ⟨_, _, _, _, h⟩ := h
  cases h
  exact ⟨_, _, _, by assumption, by assumption⟩

theorem compat_elem2 {u : Ty} (h : elem2 u = true) (o : Option Nat) :
    Compat u (.leaf o) = true ∧ simpleTy u = true := by
  cases u <;> simp [elem2] at h <;> exact ⟨rfl, rfl⟩

variable {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh} {R : Ty}

/-- **A `let` of an `Accepted2` operation** (not a call) keeps the frame W,
when an exchange's old word is a number (`hrd`). -/
theorem wN_let (_hp : g.p = p) {x : String} {op : Op} {e : Expr} {env : Env}
    (hW : WN p mem R (.let_ x op e) env) (hc : Robust.isCallOp op = false) {s' : St} {t : Ty} {ws : List Word}
    (hev : (s', t, ws) ∈ evalOp g env [] (stOf mem pairs th) op) (hm : MemExt mem s'.mem)
    (hrd : ∀ b i v, op = .xchgAt b i v → accs t = some [.one] → ∃ w, ws = [w] ∧ NumW w) :
    WN p s'.mem R e ((x, t, ws) :: env) := by
  obtain ⟨cx, cs, bufs, scope, lits, X, hb, hsc, hB, hC, hN, hX, hG, hK, hS, hXL⟩ := hW
  obtain ⟨hpo, hK'⟩ := countsB_let hK
  have slm : ∀ {V : LitV} {ws : List Word}, SliceL (SlP LAll mem) V ws → SliceL (SlP LAll s'.mem) V ws :=
    fun h => h.memExt hm
  have hG0 := hG _ (List.mem_cons_self ..)
  have hG' : ∀ q ∈ litWalk2 p ((x, opLit p lits op) :: lits) e, GoodQ p R q :=
    fun q hq => hG q (List.mem_cons_of_mem _ hq)
  have hX' : ∀ z, (z ≠ x ∧ X z) → mentions z e = false := fun z hz => mentions_let hb (hX z hz.2)
  have hsc' : ∀ z ∈ x :: scope, (((x, opLit p lits op) :: lits).lookup z).isSome = true := by
    intro z hz
    rw [lookup_cons_name]
    split
    · rfl
    · rename_i hzx
      exact hsc z ((List.mem_cons.1 hz).resolve_left hzx)
  have hmx : ∀ z, X z → mentions z (.let_ x op e) = false := hX
  -- assemble the frame from the binding's facts
  have fin : ∀ (cs' bufs' : List (String × Nat)), body2 cx cs' bufs' (x :: scope) e = true →
      SBufsA ((x, t, ws) :: env) bufs' LAll s'.mem → SCs ((x, t, ws) :: env) cs' →
      BindN t (opLit p lits op) ws → Scc.Lower.countsB p cs' bufs' ((x, opLit p lits op) :: lits) e = true →
      SliceL (SlP LAll s'.mem) (opLit p lits op) ws → WN p s'.mem R e ((x, t, ws) :: env) :=
    fun cs' bufs' hb' hB' hC' hbind hK1 hsl =>
      ⟨cx, cs', bufs', x :: scope, (x, opLit p lits op) :: lits, fun z => z ≠ x ∧ X z, hb', hsc', hB', hC',
        hN.cons hbind, hX', hG', hK1, (hS.memExt hm).cons hsl, hXL⟩
  have hBm : SBufsA ((x, t, ws) :: env) (unbuf x bufs) LAll s'.mem :=
    (hB.cons x t ws).mono (fun _ h => h) (fun _ => hasCell_of_memExt hm)
  -- an operand's facts
  have opd : ∀ a ta wa, atom1 scope a = true → (∀ z, a = .var z → mentions z (.let_ x op e) = true) →
      TermRun.evalAt env a = some (ta, wa) → BindN ta (litAt lits a) wa :=
    fun a ta wa h1 hmen he => hN.evalAt (inLits_of_atom1' hsc h1)
      (fun z hz hxz => by have h1 := hmen z hz; rw [hmx z hxz] at h1; cases h1) he
  cases op with
  | atom a =>
    simp only [body2, Bool.and_eq_true] at hb
    simp only [evalOp, ol, Option.mem_toList, Option.map_eq_some_iff, Prod.mk.injEq] at hev
    obtain ⟨⟨t0, w0⟩, he, rfl, rfl, rfl⟩ := hev
    refine fin _ _ hb.2 hBm (hC.after x (.atom a) _ _ fun a' h => ?_) ?_ hK' (slm (hS.evalAt he))
    · rcases h with h | h <;> cases h; exact ⟨_, he⟩
    · exact opd a _ _ hb.1 (fun z hz => by subst hz; simp [mentions, termKey2, atKey]) he
  | nameI a =>
    simp only [body2, Bool.and_eq_true] at hb
    simp only [evalOp, ol, Option.mem_toList, Option.map_eq_some_iff, Prod.mk.injEq] at hev
    obtain ⟨⟨t0, w0⟩, he, rfl, rfl, rfl⟩ := hev
    refine fin _ _ hb.2 hBm (hC.after x (.nameI a) _ _ fun a' h => ?_) ?_ hK' (slm (hS.evalAt he))
    · rcases h with h | h <;> cases h; exact ⟨_, he⟩
    · exact opd a _ _ hb.1 (fun z hz => by subst hz; simp [mentions, termKey2, atKey]) he
  | add a b =>
    simp only [body2, Bool.and_eq_true] at hb
    have hq := hG0.1
    simp only [numQ, xchgLeafQ, Bool.and_eq_true, beq_iff_eq, Bool.true_and] at hq
    simp only [evalOp, ol, Option.mem_toList, Option.bind_eq_bind, Option.bind_eq_some_iff] at hev
    obtain ⟨⟨ta, wa⟩, hea, ⟨tb, wb⟩, heb, hr⟩ := hev
    rcases wa with _ | ⟨xa, _ | _⟩ <;> rcases wb with _ | ⟨yb, _ | _⟩ <;> simp at hr
    obtain ⟨rfl, rfl, rfl⟩ := hr
    have na := (opd a _ _ hb.1.1 (fun z hz => by subst hz; simp [mentions, termKey2, atKey]) hea).one hq.1
    have nb := (opd b _ _ hb.1.2 (fun z hz => by subst hz; simp [mentions, termKey2, atKey]) heb).one hq.2
    obtain ⟨n, hn⟩ := na
    obtain ⟨m, hm'⟩ := nb
    refine fin _ _ hb.2 hBm (hC.cons x _ _) ⟨rfl, rfl, rfl, NumLN.of_all fun w hw => ?_⟩ hK' trivial
    simp only [List.mem_singleton] at hw; subst hw
    exact ⟨n + m, by simp [addW, hn, hm', cst, Promises.TVal.mk0]⟩
  | sub a b =>
    simp only [body2, Bool.and_eq_true] at hb
    have hq := hG0.1
    simp only [numQ, xchgLeafQ, Bool.and_eq_true, beq_iff_eq, Bool.true_and] at hq
    simp only [evalOp, ol, Option.mem_toList, Option.bind_eq_bind, Option.bind_eq_some_iff] at hev
    obtain ⟨⟨ta, wa⟩, hea, ⟨tb, wb⟩, heb, hr⟩ := hev
    rcases wa with _ | ⟨xa, _ | _⟩ <;> rcases wb with _ | ⟨yb, _ | _⟩ <;> simp at hr
    obtain ⟨rfl, rfl, rfl⟩ := hr
    have na := (opd a _ _ hb.1.1 (fun z hz => by subst hz; simp [mentions, termKey2, atKey]) hea).one hq.1
    have nb := (opd b _ _ hb.1.2 (fun z hz => by subst hz; simp [mentions, termKey2, atKey]) heb).one hq.2
    obtain ⟨n, hn⟩ := na
    obtain ⟨m, hm'⟩ := nb
    refine fin _ _ hb.2 hBm (hC.cons x _ _) ⟨rfl, rfl, rfl, NumLN.of_all fun w hw => ?_⟩ hK' trivial
    simp only [List.mem_singleton] at hw; subst hw
    exact ⟨n - m, by simp [subW, hn, hm', cst, Promises.TVal.mk0]⟩
  | pair a b =>
    simp only [body2, Bool.and_eq_true] at hb
    simp only [evalOp, ol, Option.mem_toList, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, Prod.mk.injEq] at hev
    obtain ⟨⟨ta, wa⟩, hea, ⟨tb, wb⟩, heb, -, rfl, rfl⟩ := hev
    have ha := opd a _ _ hb.1.1 (fun z hz => by subst hz; simp [mentions, termKey2, atKey]) hea
    have hb2 := opd b _ _ hb.1.2 (fun z hz => by subst hz; simp [mentions, termKey2, atKey]) heb
    exact fin _ _ hb.2 hBm (hC.cons x _ _) (ha.pair hb2) hK'
      (slm (hB.1.elim fun _ hB' => sliceL_pairOp hpo hS hB' (fun y n _ hl => hB.2 y n hl) hC hea heb ha.2.2.1))
  | pack a w τ =>
    simp only [body2, Bool.and_eq_true] at hb
    have hL := hG0.2.1
    have hcτ := compat_pack_of_layQ hL
    simp only [layQ, Bool.and_eq_true] at hL
    simp only [evalOp, ol, Option.mem_toList, Option.map_eq_some_iff, Prod.mk.injEq] at hev
    obtain ⟨⟨t0, w0⟩, he, -, rfl, rfl⟩ := hev
    have ha := opd a _ _ hb.1 (fun z hz => by subst hz; simp [mentions, termKey2, atKey]) he
    refine fin _ _ hb.2 hBm (hC.cons x _ _) ?_ hK' (slm (hS.evalAt he))
    rw [show TermRun.close [] τ = τ from TermStep.substTs_nil' τ 0 0]
    exact ⟨hcτ, hL.1.2, ha.2.2⟩
  | asLanes sg w a =>
    simp only [body2, Bool.and_eq_true] at hb
    simp only [evalOp, ol, Option.mem_toList, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, Prod.mk.injEq] at hev
    obtain ⟨_, _, n, -, -, rfl, rfl⟩ := hev
    refine fin _ _ hb.2 hBm (hC.cons x _ _) ⟨rfl, rfl, rfl, NumLN.of_all fun w' hw => ?_⟩ hK' trivial
    simp only [List.mem_singleton] at hw; subst hw
    exact ⟨n % W64, by simp [cst, Promises.TVal.mk0]⟩
  | xchgAt b i v =>
    cases b with
    | var bb =>
      cases i with
      | lit ii =>
        simp only [body2, Bool.and_eq_true] at hb
        obtain ⟨⟨⟨-, hn⟩, -⟩, hb'⟩ := hb
        cases hl : bufs.lookup bb with
        | none => rw [hl] at hn; simp at hn
        | some n =>
          obtain ⟨⟨_, hB0⟩, -⟩ := id hB
          obtain ⟨t0, u0, lbl, he0, hbe, he2, -⟩ := hB0 bb n hl
          obtain ⟨tb, pw, μ, heb, hbt⟩ := evalOp_xchgAt_ty hev
          simp only [TermRun.evalAt, he0, Option.some.injEq, Prod.mk.injEq] at heb
          obtain ⟨rfl, -⟩ := heb
          rw [hbe, Option.some.injEq, Prod.mk.injEq] at hbt
          obtain ⟨-, rfl⟩ := hbt
          obtain ⟨w, rfl, hw⟩ := hrd _ _ _ rfl (accs_elem2 he2)
          have hc := compat_elem2 he2 none
          refine fin _ _ hb' hBm (hC.cons x _ _) ⟨hc.1, hc.2, rfl, NumLN.of_all fun w' hw' => ?_⟩ hK' trivial
          simp only [List.mem_singleton] at hw'; subst hw'; exact hw
      | _ => simp [body2] at hb
    | _ => simp [body2] at hb
  | newBuf n τ =>
    obtain ⟨ta, wn, k, us, z, ini, hn, hk, hus, rfl, rfl, rfl⟩ := evalOp_newBuf_inv hev
    simp only [body2, Bool.and_eq_true] at hb
    obtain ⟨⟨⟨-, -⟩, he2⟩, hmt⟩ := hb
    cases hco : constOf cs n with
    | none => rw [hco] at hmt; simp at hmt
    | some k' =>
      rw [hco] at hmt
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hmt
      obtain ⟨w, rfl, hw⟩ := hC.constOf hco hn
      simp only [numOf, hw, Option.some.injEq] at hk
      subst hk
      simp only [Scc.Lower.bufsAfter, hco] at hK'
      refine fin _ _ hmt.2
        ((sBufsA_newBuf (s := stOf mem pairs th) hB x he2 hus z hmt.1.2).mono (fun _ _ => trivial) (fun _ h => h))
        (hC.cons x _ _) ⟨rfl, rfl, rfl, fun i w hw hi => ?_⟩ hK' trivial
      simp only [opLit, litMask] at hi
      rcases i with _ | i <;> simp at hi
  | call _ _ _ _ => simp [Robust.isCallOp] at hc
  | _ => simp [body2] at hb

end wstep

/-! ## The blocks and the thread -/

section thread

open Scc.Lower (LitV litAt opLit shapeOf params2 litWalk2 litWalks2 simpleTy body2 unbuf constOf bindC elem2 atom1
  mentions termKey2 argShape atKey Accepted2 decl2 setupOf hasPrint mainArgOk)
open Scc.Sem.SrcSem (setupTerm setupStart)

/-- **What entering a W block needs**: its body from no buffer and its
parameter in scope (the extern's loop excluded from its callees), its types
with their layouts, not the loop's name, `countsOk2` from its parameter. -/
structure BlockW (p : Prog) (d : Decl) : Prop where
  body : ∃ cx, body2 cx [] [] (params2 d) d.body = true ∧ (hasPrint p = true → cx.excl.contains "printL" = true)
  arg : Compat d.argTy (shapeOf d.argTy) = true ∧ simpleTy d.argTy = true
  ret : Compat d.retTy (shapeOf d.retTy) = true ∧ simpleTy d.retTy = true
  notL : hasPrint p = true → d.name ≠ "printL"
  cnt : Scc.Lower.countsB p [] [] ((params2 d).map (·, shapeOf d.argTy)) d.body = true

theorem reserved_printL {p : Prog} (s : Option Ty) (h : hasPrint p = true) :
    (Scc.Lower.reserved s (hasPrint p)).contains "printL" = true := by
  simp [Scc.Lower.reserved, h]

theorem accepted2_parts {p : Prog} (hacc : Accepted2 p = true) :
    Scc.Lower.decls2 [] (setupOf p) (hasPrint p) p = true ∧ Scc.Lower.setupPresent p = true ∧
      Scc.Lower.layoutOk2 p = true ∧ Scc.Lower.callsOk2 p = true ∧ Scc.Lower.setupArgOk2 p = true := by
  simp only [Accepted2, Bool.and_eq_true] at hacc
  exact ⟨hacc.1.1.1.1.1.1.1.2, hacc.1.1.1.1.1.1.2, hacc.1.1.1.1.2, hacc.1.1.2, hacc.2⟩

/-- **A block of an `Accepted2` program** is the extern or its loop (and the
program has the extern), or a W block. -/
theorem block_kind {p : Prog} (hacc : Accepted2 p = true)
    (hset : ∀ s, setupOf p = some s → Compat s (shapeOf s) = true) {d : Decl} (hd : d ∈ p) :
    ((d = Scc.Frontend.printExtD ∨ d = Scc.Frontend.printLoopD) ∧ hasPrint p = true) ∨ BlockW p d := by
  obtain ⟨hds, -⟩ := accepted2_parts hacc
  have hcnt : Scc.Lower.countsOk2 p = true := by
    simp only [Accepted2, Bool.and_eq_true] at hacc; exact hacc.1.2
  obtain ⟨E, hE⟩ := decl2_of_decls2 hds d hd
  unfold decl2 at hE
  split at hE
  · rename_i hpe
    simp only [Bool.and_eq_true] at hE
    exact Or.inl ⟨Or.inl (Scc.Frontend.declIs_eq hE.1), List.any_eq_true.2 ⟨d, hd, hpe⟩⟩
  · rename_i hpe
    split at hE
    · rename_i hx
      simp only [Bool.and_eq_true, beq_iff_eq] at hx
      exact Or.inl ⟨Or.inr (Scc.Frontend.declIs_eq hE), hx.1⟩
    · rename_i hx
      have notL : hasPrint p = true → d.name ≠ "printL" := fun h1 h2 => hx (by simp [h1, h2])
      have cnt := countsOk2_decl hcnt hd (by simpa using hpe) (fun h => hx (by simp [h.1, h.2]))
      have rsv := reserved_printL (p := p) (setupOf p)
      split at hE
      · rename_i hm
        simp only [Scc.Lower.main2, Bool.and_eq_true, beq_iff_eq] at hE
        obtain ⟨⟨⟨⟨-, -⟩, hr⟩, ha⟩, hb⟩ := hE
        refine Or.inr ⟨⟨_, hb, rsv⟩, ?_, by rw [hr]; exact ⟨rfl, rfl⟩, notL, cnt⟩
        cases hs : setupOf p with
        | none => rw [hs] at ha; simp only [beq_iff_eq] at ha; rw [ha]; exact ⟨rfl, rfl⟩
        | some s =>
          rw [hs] at ha; simp only [beq_iff_eq] at ha; rw [ha]
          have hsim := setup_simple (accepted2_parts hacc).1 (accepted2_parts hacc).2.1 s hs
          exact ⟨by simp [Compat, shapeOf, hset s hs], by simp [simpleTy, hsim]⟩
      · split at hE
        · rename_i s hs
          split at hE
          · simp only [Scc.Lower.setup2, Bool.and_eq_true, beq_iff_eq] at hE
            obtain ⟨⟨⟨⟨⟨⟨-, -⟩, ha⟩, hr⟩, -⟩, hsim⟩, hb⟩ := hE
            refine Or.inr ⟨⟨_, by unfold params2; rw [ha]; exact hb, rsv⟩, by rw [ha]; exact ⟨rfl, rfl⟩,
              by rw [hr]; exact ⟨hset s hs, hsim.1⟩, notL, cnt⟩
          · simp only [Scc.Lower.plain2, Bool.and_eq_true, beq_iff_eq] at hE
            obtain ⟨⟨⟨⟨-, -⟩, hr⟩, ha⟩, hb⟩ := hE
            exact Or.inr ⟨⟨_, hb, rsv⟩, by rw [ha]; exact ⟨rfl, rfl⟩, by rw [hr]; exact ⟨rfl, rfl⟩, notL, cnt⟩
        · simp only [Scc.Lower.plain2, Bool.and_eq_true, beq_iff_eq] at hE
          obtain ⟨⟨⟨⟨-, -⟩, hr⟩, ha⟩, hb⟩ := hE
          exact Or.inr ⟨⟨_, hb, rsv⟩, by rw [ha]; exact ⟨rfl, rfl⟩, by rw [hr]; exact ⟨rfl, rfl⟩, notL, cnt⟩


theorem close_nil' (τ : Ty) : close [] τ = τ := TermStep.substTs_nil' τ 0 0

/-- The start's continuation once `rodata` returns. -/
def setupRest : Expr := .let_ "a" (.pair (.var "r") (.var "me")) (.tail "main" [] (.var "a"))

theorem setupTerm_eq : setupTerm = .let_ "r" (.call "rodata" [] (.var "u")) setupRest := rfl

/-- The operations of the extern and its loop: none writes. -/
def pureOp : Op → Bool
  | .atom _ | .nameI _ | .add _ _ | .sub _ _ | .pair _ _ | .lane _ _ | .loadAt _ _ | .ext _ _ => true
  | _ => false

/-- **A frame of the extern or its loop** (E): pure `let`s, `split`s, `if`s,
`ret ()`, and a tail call of the loop. -/
def PureE : Expr → Bool
  | .let_ _ op e => pureOp op && PureE e
  | .split _ _ _ e => PureE e
  | .ifeq _ _ y n => PureE y && PureE n
  | .ret .unit => true
  | .tail f _ _ ts => f == "printL" && ts.isEmpty
  | _ => false

theorem pureE_printExt : PureE Scc.Frontend.printExtD.body = true := by decide
theorem pureE_printLoop : PureE Scc.Frontend.printLoopD.body = true := by decide

/-- A result type with its layout. -/
def RetOK (R : Ty) : Prop := Compat R (shapeOf R) = true ∧ simpleTy R = true

/-- **The start's frame before `main`**: with a setup block, at
`setupTerm`, after `rodata` returned its result (with its slices), or at the
tail call of `main` with the pair; without one, at `mainStart`'s tail call of
`main` on `()`. -/
def SetupN (p : Prog) (mem : WeakMem.Memory) (e : Expr) (env : Env) : Prop :=
  (∃ s, setupOf p = some s ∧ (∃ tm wm, lookupE env "me" = some (tm, wm)) ∧
    ((e = setupTerm ∧ lookupE env "u" = some (.unit, [])) ∨
     (∃ wr, e = setupRest ∧ lookupE env "r" = some (s, wr) ∧ BindN s (shapeOf s) wr ∧
        SliceL (SlP LAll mem) (shapeOf s) wr) ∨
     (∃ tm wr wm, e = .tail "main" [] (.var "a") ∧ lookupE env "a" = some (.prod s tm, wr ++ wm) ∧
        BindN s (shapeOf s) wr ∧ SliceL (SlP LAll mem) (shapeOf s) wr))) ∨
  (setupOf p = none ∧ e = .tail "main" [] (.var "a") ∧ lookupE env "a" = some (.unit, []))

/-- **`main` entered from the start**: its parameter the setup result and the
thread word (`wm`, any word). -/
def MainN (p : Prog) (mem : WeakMem.Memory) (e : Expr) (env : Env) : Prop :=
  ∃ s d wr wm, setupOf p = some s ∧ p.find? (·.name == "main") = some d ∧ e = d.body ∧
    env = [(d.arg, d.argTy, wr ++ wm)] ∧ BindN s (shapeOf s) wr ∧ SliceL (SlP LAll mem) (shapeOf s) wr

theorem SetupN.mono {p : Prog} {mem mem' : WeakMem.Memory} (hm : MemExt mem mem') {e : Expr} {env : Env}
    (h : SetupN p mem e env) : SetupN p mem' e env := by
  obtain ⟨s, hs, hme, h | ⟨wr, h1, h2, h3, h4⟩ | ⟨tm, wr, wm, h1, h2, h3, h4⟩⟩ | hU := h
  · exact Or.inl ⟨s, hs, hme, Or.inl h⟩
  · exact Or.inl ⟨s, hs, hme, Or.inr (Or.inl ⟨wr, h1, h2, h3, h4.memExt hm⟩)⟩
  · exact Or.inl ⟨s, hs, hme, Or.inr (Or.inr ⟨tm, wr, wm, h1, h2, h3, h4.memExt hm⟩)⟩
  · exact Or.inr hU

theorem MainN.mono {p : Prog} {mem mem' : WeakMem.Memory} (hm : MemExt mem mem') {e : Expr} {env : Env}
    (h : MainN p mem e env) : MainN p mem' e env :=
  let ⟨s, d, wr, wm, h1, h2, h3, h4, h5, h6⟩ := h
  ⟨s, d, wr, wm, h1, h2, h3, h4, h5, h6.memExt hm⟩

/-- **A suspended W frame**: at its call, of a block `d'` whose result type
the frame expects. -/
def SusW (p : Prog) (mem : WeakMem.Memory) (fr : Frame) (R' : Ty) : Prop :=
  fr.σs = [] ∧ RetOK R' ∧ ∃ g is a ts d', p.find? (·.name == g) = some d' ∧ fr.ty = d'.retTy ∧
    WN p mem R' (.let_ fr.x (.call g is a ts) fr.body) fr.env

/-- **The start's frame suspended at `rodata`.** -/
def SusS (p : Prog) (fr : Frame) : Prop :=
  fr.σs = [] ∧ ∃ s, setupOf p = some s ∧ fr.x = "r" ∧ fr.body = setupRest ∧ fr.ty = s ∧
    ∃ tm wm, lookupE fr.env "me" = some (tm, wm)

/-- **The suspended frames**, each expecting the result type of the frame
above it; the start's frame only at the bottom. -/
def StackN (p : Prog) (mem : WeakMem.Memory) : Ty → List Frame → Prop
  | _, [] => True
  | R, fr :: rest => fr.ty = R ∧ ((∃ R', SusW p mem fr R' ∧ StackN p mem R' rest) ∨ (SusS p fr ∧ rest = []))

/-- **The current frame**, of result type `R`: W, E (its loads reading
written cells, `LdOK`), or the start's frames (with nothing suspended). -/
def FrN (p : Prog) (mem : WeakMem.Memory) (R : Ty) (th : TTh) : Prop :=
  (WN p mem R th.term th.env ∧ RetOK R) ∨
    (PureE th.term = true ∧ R = .unit ∧ hasPrint p = true ∧ LdOK p mem (th.term, th.env)) ∨
    ((SetupN p mem th.term th.env ∨ MainN p mem th.term th.env) ∧ th.stack = [])

/-- **The thread invariant.** -/
def ThN (p : Prog) (mem : WeakMem.Memory) (th : TTh) : Prop :=
  th.σs = [] ∧ ∃ R, FrN p mem R th ∧ StackN p mem R th.stack

theorem StackN.mono {p : Prog} {mem mem' : WeakMem.Memory} (hm : MemExt mem mem') :
    ∀ {R : Ty} {st : List Frame}, StackN p mem R st → StackN p mem' R st
  | _, [], _ => trivial
  | _, _ :: _, ⟨hty, h⟩ => ⟨hty, h.imp (fun ⟨R', ⟨hσ, hR, g, is, a, ts, d', hf, ht, hW⟩, hs⟩ =>
      ⟨R', ⟨hσ, hR, g, is, a, ts, d', hf, ht, hW.mono hm⟩, StackN.mono hm hs⟩) id⟩

theorem FrN.mono {p : Prog} {mem mem' : WeakMem.Memory} (hm : MemExt mem mem') {R : Ty} {th th' : TTh}
    (h : FrN p mem R th) (ht : th'.term = th.term) (he : th'.env = th.env) (hs : th'.stack = th.stack) :
    FrN p mem' R th' := by
  rcases h with ⟨hW, hR⟩ | ⟨hE, hRu, hP, hL⟩ | ⟨hSM, hst⟩
  · exact Or.inl ⟨by rw [ht, he]; exact hW.mono hm, hR⟩
  · exact Or.inr (Or.inl ⟨by rw [ht]; exact hE, hRu, hP, by rw [ht, he]; exact hL.mono hm⟩)
  · exact Or.inr (Or.inr ⟨by rw [ht, he]; exact hSM.imp (·.mono hm) (·.mono hm), by rw [hs]; exact hst⟩)

/-- The walk's facts at every point of every block; the setup result no
locative. -/
def GoodBlocks (p : Prog) : Prop :=
  (∀ d ∈ p, ∀ q ∈ litWalk2 p ((params2 d).map (·, shapeOf d.argTy)) d.body, GoodQ p d.retTy q) ∧
    ∀ s, setupOf p = some s → shapeOf s ≠ .loc

/-- **A W block's entry.** -/
theorem wN_entry {p : Prog} (hgood : GoodBlocks p) {d : Decl} (hd : d ∈ p) (hW : BlockW p d)
    (mem : WeakMem.Memory) {ws : List Word} (hb : BindN d.argTy (shapeOf d.argTy) ws)
    (hs : SliceL (SlP LAll mem) (shapeOf d.argTy) ws) :
    WN p mem d.retTy d.body [(d.arg, d.argTy, ws)] := by
  obtain ⟨cx, hbody, hxl⟩ := hW.body
  refine ⟨cx, [], [], params2 d, (params2 d).map (·, shapeOf d.argTy), fun _ => False, hbody, ?_,
    sBufsA_nil _ _ _, SCs.nil _, envN_entry hb, fun _ h => h.elim, hgood.1 d hd, hW.cnt, envSl_entry hs, hxl⟩
  intro z hz
  unfold params2 at hz ⊢
  split at hz
  · cases hz
  · rename_i h; simp only [List.mem_singleton] at hz; subst hz; simp [h]


/-! ### Blocks by name -/

theorem find_name {p : Prog} {g : String} {d : Decl} (h : p.find? (·.name == g) = some d) :
    d ∈ p ∧ d.name = g :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- **A callee** is the extern or its loop (pure, no result) or a W block. -/
theorem callee_kind {p : Prog} (hacc : Accepted2 p = true)
    (hset : ∀ s, setupOf p = some s → Compat s (shapeOf s) = true) {g : String} {d : Decl}
    (hf : p.find? (·.name == g) = some d) :
    (PureE d.body = true ∧ d.retTy = .unit ∧ hasPrint p = true) ∨ BlockW p d := by
  rcases block_kind hacc hset (find_name hf).1 with ⟨h | h, hP⟩ | h
  · subst h; exact Or.inl ⟨pureE_printExt, rfl, hP⟩
  · subst h; exact Or.inl ⟨pureE_printLoop, rfl, hP⟩
  · exact Or.inr h

/-- **The loop by name** is `printLoopD`. -/
theorem printL_find {p : Prog} (hacc : Accepted2 p = true)
    (hset : ∀ s, setupOf p = some s → Compat s (shapeOf s) = true) (hP : hasPrint p = true) {d : Decl}
    (hf : p.find? (·.name == "printL") = some d) : d = Scc.Frontend.printLoopD := by
  obtain ⟨hd, hname⟩ := find_name hf
  rcases block_kind hacc hset hd with ⟨h | h, -⟩ | h
  · subst h; exact absurd hname (by decide)
  · exact h
  · exact absurd hname (h.notL hP)

/-- **`decls2`'s earlier names**: given ones, or of the program's blocks. -/
theorem decl2_of_decls2' {s : Option Ty} {x : Bool} :
    ∀ {E : List String} {p : Prog}, Scc.Lower.decls2 E s x p = true → ∀ d ∈ p,
      ∃ E', decl2 E' s x d = true ∧ ∀ n ∈ E', n ∈ E ∨ ∃ d' ∈ p, d'.name = n
  | _, [], _, d, hd => absurd hd List.not_mem_nil
  | E, d' :: ds, h, d, hd => by
    simp only [Scc.Lower.decls2, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hd with rfl | hd
    · exact ⟨E, h.1, fun n hn => Or.inl hn⟩
    · obtain ⟨E', h1, h2⟩ := decl2_of_decls2' h.2 d hd
      refine ⟨E', h1, fun n hn => ?_⟩
      rcases h2 n hn with h | ⟨d'', hd'', rfl⟩
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inr ⟨d', List.mem_cons_self .., rfl⟩
        · exact Or.inl h
      · exact Or.inr ⟨d'', List.mem_cons_of_mem _ hd'', rfl⟩

/-- **The extern's loop by name**, the extern a block (`decl2` asks for the
loop before it). -/
theorem printL_of_ext {p : Prog} (hacc : Accepted2 p = true)
    (hset : ∀ s, setupOf p = some s → Compat s (shapeOf s) = true) (hd : Scc.Frontend.printExtD ∈ p) :
    p.find? (·.name == "printL") = some Scc.Frontend.printLoopD := by
  obtain ⟨hds, -⟩ := accepted2_parts hacc
  obtain ⟨E, hE, hEn⟩ := decl2_of_decls2' hds _ hd
  have hP : hasPrint p = true := List.any_eq_true.2 ⟨_, hd, by decide⟩
  unfold decl2 at hE
  simp only [show Scc.Lower.isPrintExt Scc.Frontend.printExtD = true by decide, ite_true,
    Bool.and_eq_true] at hE
  have hm : "printL" ∈ E := by simpa using hE.2
  rcases hEn _ hm with h | ⟨d', hd', hn⟩
  · cases h
  · cases h : p.find? (·.name == "printL") with
    | none => exact absurd (List.find?_eq_none.1 h d' hd') (by simp [hn])
    | some d'' => rw [printL_find hacc hset hP h]

/-- **The setup block**: with a setup result `s`, `rodata` is a W block
from `()` to `s`. -/
theorem rodata_find {p : Prog} (hacc : Accepted2 p = true)
    (hset : ∀ s, setupOf p = some s → Compat s (shapeOf s) = true) {s : Ty} (hs : setupOf p = some s) :
    ∃ d, p.find? (·.name == "rodata") = some d ∧ d.argTy = .unit ∧ d.retTy = s ∧ BlockW p d := by
  obtain ⟨hds, hsp, -⟩ := accepted2_parts hacc
  have hany : p.any (·.name == "rodata") = true := by
    simpa [Scc.Lower.setupPresent, hs] using hsp
  obtain ⟨d, hf⟩ : ∃ d, p.find? (·.name == "rodata") = some d := by
    cases h : p.find? (·.name == "rodata") with
    | some d => exact ⟨d, rfl⟩
    | none =>
      obtain ⟨d0, hd0, hn0⟩ := List.any_eq_true.1 hany
      exact absurd hn0 (by simpa using List.find?_eq_none.1 h d0 hd0)
  obtain ⟨hd, hname⟩ := find_name hf
  have hBW : BlockW p d := by
    rcases block_kind hacc hset hd with ⟨h | h, -⟩ | h
    · subst h; exact absurd hname (by decide)
    · subst h; exact absurd hname (by decide)
    · exact h
  obtain ⟨E, hE⟩ := decl2_of_decls2 hds d hd
  unfold decl2 at hE
  split at hE
  · simp only [Bool.and_eq_true] at hE
    have := Scc.Frontend.declIs_eq hE.1; subst this; exact absurd hname (by decide)
  · split at hE
    · rename_i hx; simp [hname] at hx
    · split at hE
      · rename_i hm; simp [hname] at hm
      · split at hE
        · rename_i s' hs'
          rw [hs] at hs'; cases hs'
          simp only [hname, beq_self_eq_true, ↓reduceIte, Scc.Lower.setup2, Bool.and_eq_true, beq_iff_eq] at hE
          obtain ⟨⟨⟨⟨⟨⟨-, -⟩, ha⟩, hr⟩, -⟩, -⟩, -⟩ := hE
          exact ⟨d, hf, ha, hr, hBW⟩
        · rename_i hs'; rw [hs] at hs'; cases hs'

theorem bindN_unit : BindN .unit (shapeOf .unit) [] := ⟨rfl, rfl, rfl, NumLN.nil _⟩

/-- **Without a setup block, `main` takes `()`** (`main2`). -/
theorem main_argTy_none {p : Prog} (hacc : Accepted2 p = true) (hs : setupOf p = none) {d : Decl}
    (hf : p.find? (·.name == "main") = some d) : d.argTy = .unit := by
  obtain ⟨hds, -⟩ := accepted2_parts hacc
  obtain ⟨hd, hname⟩ := find_name hf
  obtain ⟨E, hE⟩ := decl2_of_decls2 hds d hd
  rw [hs] at hE
  have hpe : Scc.Lower.isPrintExt d = false := by simp [Scc.Lower.isPrintExt, hname]
  unfold decl2 at hE
  have hnp : ¬ (hasPrint p = true ∧ "main" = "printL") := by simp
  simp only [hpe, hname, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, Scc.Lower.main2, Bool.and_eq_true,
    beq_iff_eq, hnp] at hE
  exact hE.1.2

/-! ### A W frame's other steps -/

theorem scope_cons {scope : List String} {lits : List (String × LitV)}
    (h : ∀ z ∈ scope, (lits.lookup z).isSome = true) (x : String) (L : LitV) :
    ∀ z ∈ x :: scope, (((x, L) :: lits).lookup z).isSome = true := by
  intro z hz
  rw [lookup_cons_name]
  split
  · rfl
  · rename_i hzx; exact h z ((List.mem_cons.1 hz).resolve_left hzx)

/-- **`let (x, y) = a`** in a W frame, as `tstep` splits. -/
theorem wN_split {p : Prog} {mem : WeakMem.Memory} {R : Ty} {a : At} {x y : String} {e : Expr} {env : Env}
    (hW : WN p mem R (.split a x y e) env) {u w : Ty} {ws : List Word} {us : List Acc}
    (he : TermRun.evalAt env a = some (.prod u w, ws)) (hu : accs u = some us) :
    WN p mem R e ((y, w, ws.drop (nWords us)) :: (x, u, ws.take (nWords us)) :: env) := by
  obtain ⟨cx, cs, bufs, scope, lits, X, hb, hsc, hB, hC, hN, hX, hG, hK, hS, hXL⟩ := hW
  simp only [body2, Bool.and_eq_true] at hb
  have hba : BindN (.prod u w) (litAt lits a) ws :=
    hN.evalAt (inLits_of_atom1' hsc hb.1) (fun z hz hxz => by
      have h1 := hX z hxz; subst hz; simp [mentions, termKey2, atKey] at h1) he
  obtain ⟨l, r, hl⟩ := hba.node_of_prod
  rw [hl] at hba
  have hk : nWords us = l.words.length := by
    obtain ⟨hc, hs, -, -⟩ := hba
    simp only [Compat, simpleTy, Bool.and_eq_true] at hc hs
    have := accs_simple u hs.1 _ (compat_plLen u l hc.1)
    rw [hu] at this; exact Option.some.inj this
  obtain ⟨h1, h2⟩ := hba.split hu
  have hwalk : litWalk2 p lits (.split a x y e) =
      (.split a x y e, lits) :: litWalk2 p ((y, r) :: (x, l) :: lits) e := by
    rw [litWalk2, hl]
  refine ⟨cx, _, _, y :: x :: scope, (y, r) :: (x, l) :: lits, fun z => z ≠ y ∧ (z ≠ x ∧ X z), hb.2,
    scope_cons (scope_cons hsc x l) y r, (hB.cons x _ _).cons y _ _, (hC.cons x _ _).cons y _ _,
    (hN.cons h1).cons h2, fun z hz => ?_, fun q hq => hG q (by rw [hwalk]; exact List.mem_cons_of_mem _ hq),
    countsB_split hl hK, hS.split he hl hk, hXL⟩
  have h := hX z hz.2.2
  revert h
  simp (config := { contextual := true }) [mentions, termKey2]

/-- **An index unpack** in a W frame. -/
theorem wN_unpack {p : Prog} {mem : WeakMem.Memory} {R : Ty} {a : At} {i x : String} {e : Expr} {env : Env}
    (hW : WN p mem R (.unpack a i x e) env) {b : Ty} {ws : List Word}
    (he : TermRun.evalAt env a = some (.iex b, ws)) :
    WN p mem R e ((x, b, ws) :: env) := by
  obtain ⟨cx, cs, bufs, scope, lits, X, hb, hsc, hB, hC, hN, hX, hG, hK, hS, hXL⟩ := hW
  simp only [body2, Bool.and_eq_true] at hb
  have hba : BindN (.iex b) (litAt lits a) ws :=
    hN.evalAt (inLits_of_atom1' hsc hb.1) (fun z hz hxz => by
      have h1 := hX z hxz; subst hz; simp [mentions, termKey2, atKey] at h1) he
  refine ⟨cx, _, _, x :: scope, (x, litAt lits a) :: lits, fun z => z ≠ x ∧ X z, hb.2,
    scope_cons hsc x _, (hB.unbuf i).cons x _ _, (hC.unbuf i).cons x _ _, hN.cons hba.unpack, fun z hz => ?_,
    fun q hq => hG q (by rw [litWalk2]; exact List.mem_cons_of_mem _ hq), countsB_unpack hK,
    hS.cons (hS.evalAt he), hXL⟩
  have h := hX z hz.2
  revert h
  simp (config := { contextual := true }) [mentions, termKey2]

/-- **An `if`** in a W frame: either branch, the same environment. -/
theorem wN_ifeq {p : Prog} {mem : WeakMem.Memory} {R : Ty} {a b : At} {yes no : Expr} {env : Env}
    (hW : WN p mem R (.ifeq a b yes no) env) : WN p mem R yes env ∧ WN p mem R no env := by
  obtain ⟨cx, cs, bufs, scope, lits, X, hb, hsc, hB, hC, hN, hX, hG, hK, hS, hXL⟩ := hW
  simp only [body2, Bool.and_eq_true] at hb
  refine ⟨⟨cx, cs, bufs, scope, lits, X, hb.1.2, hsc, hB, hC, hN, fun z hz => ?_, fun q hq => hG q ?_,
      (countsB_ifeq hK).1, hS, hXL⟩,
    ⟨cx, cs, bufs, scope, lits, X, hb.2, hsc, hB, hC, hN, fun z hz => ?_, fun q hq => hG q ?_,
      (countsB_ifeq hK).2, hS, hXL⟩⟩
  · have h := hX z hz; revert h; simp (config := { contextual := true }) [mentions, termKey2]
  · rw [litWalk2]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hq)
  · have h := hX z hz; revert h; simp (config := { contextual := true }) [mentions, termKey2]
  · rw [litWalk2]; exact List.mem_cons_of_mem _ (List.mem_append_right _ hq)

/-- **A W frame's result** at its block's result layout (`callsOk2`'s
return check), with its slices. -/
theorem wN_ret {p : Prog} {mem : WeakMem.Memory} {R : Ty} {a : At} {env : Env} (hW : WN p mem R (.ret a) env)
    (hR : RetOK R) {t : Ty} {ws : List Word} (he : TermRun.evalAt env a = some (t, ws)) :
    BindN R (shapeOf R) ws ∧ SliceL (SlP LAll mem) (shapeOf R) ws := by
  obtain ⟨cx, cs, bufs, scope, lits, X, hb, hsc, hB, hC, hN, hX, hG, -, hS, -⟩ := hW
  simp only [body2] at hb
  have hba : BindN t (litAt lits a) ws :=
    hN.evalAt (inLits_of_atom1' hsc hb) (fun z hz hxz => by
      have h1 := hX z hxz; subst hz; simp [mentions, termKey2, atKey] at h1) he
  have hr := (hG (.ret a, lits) (by simp [litWalk2])).2.2.2 a rfl
  exact ⟨hba.decl hr hR.1 hR.2, (hS.evalAt he).of_erase hr⟩

/-- **A W frame's call**: the argument's words at the callee's parameter
layout (`callsOk2`'s call check), with its slices. -/
theorem wN_call_arg {p : Prog} {mem : WeakMem.Memory} {R : Ty} {x g : String} {is : List String} {a : At}
    {ts : List Ty} {e : Expr} {env : Env} (hW : WN p mem R (.let_ x (.call g is a ts) e) env) {d' : Decl}
    (hf : p.find? (·.name == g) = some d') (hA : RetOK d'.argTy) {t : Ty} {ws : List Word}
    (he : TermRun.evalAt env a = some (t, ws)) :
    BindN d'.argTy (shapeOf d'.argTy) ws ∧ SliceL (SlP LAll mem) (shapeOf d'.argTy) ws := by
  obtain ⟨cx, cs, bufs, scope, lits, X, hb, hsc, hB, hC, hN, hX, hG, -, hS, -⟩ := hW
  simp only [body2, Bool.and_eq_true] at hb
  have hba : BindN t (litAt lits a) ws :=
    hN.evalAt (inLits_of_atom1' hsc hb.1.2) (fun z hz hxz => by
      have h1 := hX z hxz; subst hz; simp [mentions, termKey2, atKey] at h1) he
  have hc := (hG _ (List.mem_cons_self ..)).2.2.1 x g is a ts e rfl
  rw [argShape_of_find hf] at hc
  exact ⟨hba.decl hc hA.1 hA.2, (hS.evalAt he).of_erase hc⟩

/-- **Back from a W frame's call**: the result bound at the callee's result
layout, the walk's binding of the call (`retShape`). -/
theorem wN_after_call {p : Prog} {mem : WeakMem.Memory} {R : Ty} {x g : String} {is : List String} {a : At}
    {ts : List Ty} {e : Expr} {env : Env} (hW : WN p mem R (.let_ x (.call g is a ts) e) env) {d' : Decl}
    (hf : p.find? (·.name == g) = some d') {ws : List Word} (hr : BindN d'.retTy (shapeOf d'.retTy) ws)
    (hsl : SliceL (SlP LAll mem) (shapeOf d'.retTy) ws) :
    WN p mem R e ((x, d'.retTy, ws) :: env) := by
  obtain ⟨cx, cs, bufs, scope, lits, X, hb, hsc, hB, hC, hN, hX, hG, hK, hS, hXL⟩ := hW
  have hb' := hb
  simp only [body2, Bool.and_eq_true] at hb'
  have hop : Scc.Lower.opLit p lits (.call g is a ts) = shapeOf d'.retTy := by
    simp only [Scc.Lower.opLit]; exact retShape_of_find hf
  have hK' := (countsB_let hK).2
  rw [hop] at hK'
  refine ⟨cx, _, _, x :: scope, (x, shapeOf d'.retTy) :: lits, fun z => z ≠ x ∧ X z, hb'.2,
    scope_cons hsc x _, hB.cons x _ _, hC.cons x _ _, hN.cons hr, fun z hz => mentions_let hb (hX z hz.2),
    fun q hq => hG q ?_, hK', hS.cons hsl, hXL⟩
  rw [litWalk2, hop]; exact List.mem_cons_of_mem _ hq

/-! ### Returning into a suspended frame -/

/-- **A return pops the top frame**: the result at the frame's type's layout
resumes a W frame after its call, or the start's frame after `rodata`. -/
theorem thN_pop {p : Prog} {mem : WeakMem.Memory} {R : Ty} {fr : Frame} {rest : List Frame} {ws : List Word}
    (hS : StackN p mem R (fr :: rest)) (hb : BindN R (shapeOf R) ws) (hsl : SliceL (SlP LAll mem) (shapeOf R) ws)
    {th' : TTh} (ht : th'.term = fr.body)
    (he : th'.env = (fr.x, fr.ty, ws) :: fr.env) (hσ : th'.σs = fr.σs) (hs : th'.stack = rest) :
    ThN p mem th' := by
  obtain ⟨hty, ⟨R', ⟨hσ0, hR', g, is, a, ts, d', hf, hty', hW⟩, hrest⟩ |
    ⟨⟨hσ0, s, hs0, hx, hbody, htys, tm, wm, hme⟩, hnil⟩⟩ := hS
  · subst hty
    rw [hty'] at hb hsl
    have hW' := wN_after_call hW hf hb hsl
    rw [← hty'] at hW'
    refine ⟨hσ.trans hσ0, R', Or.inl ⟨by rw [ht, he]; exact hW', hR'⟩, by rw [hs]; exact hrest⟩
  · subst hty
    refine ⟨hσ.trans hσ0, .unit, Or.inr (Or.inr ⟨Or.inl (Or.inl ⟨s, hs0, ⟨tm, wm, ?_⟩,
      Or.inr (Or.inl ⟨ws, ?_, ?_, ?_, ?_⟩)⟩), by rw [hs, hnil]⟩), by rw [hs, hnil]; trivial⟩
    · rw [he, lookupE_cons, hx]; simpa using hme
    · rw [ht, hbody]
    · rw [he, lookupE_cons, hx, htys]; simp
    · rw [← htys]; exact hb
    · rw [← htys]; exact hsl

/-! ### `main` from the start -/

/-- **`main`'s first step from the start**: the split of its parameter
binds the setup result (`x`) and the thread word (`y`, never mentioned, as
the parameter itself: `mainArgOk`). -/
theorem wN_main {p : Prog} (hacc : Accepted2 p = true)
    (hset : ∀ s, setupOf p = some s → Compat s (shapeOf s) = true) (hgood : GoodBlocks p) (mem : WeakMem.Memory)
    {e : Expr} {env : Env} (hM : MainN p mem e env) {a : At} {x y : String} {e1 : Expr} (hE : e = .split a x y e1)
    {u w : Ty} {ws : List Word} {us : List Acc} (he : TermRun.evalAt env a = some (.prod u w, ws))
    (hu : accs u = some us) :
    ∃ R, WN p mem R e1 ((y, w, ws.drop (nWords us)) :: (x, u, ws.take (nWords us)) :: env) ∧ RetOK R := by
  obtain ⟨s, d, wr, wm, hs, hf, rfl, rfl, hbs, hss⟩ := hM
  obtain ⟨hd, hname⟩ := find_name hf
  have harg : d.argTy = .prod s (.ptr .pub .void) := by
    have hs' := hs
    simp only [Scc.Lower.setupOf, hf] at hs'
    split at hs'
    · rename_i h; cases hs'; exact h
    · cases hs'
  have hm : mainArgOk d = true := by
    have h := (accepted2_parts hacc).2.2.2.2
    simp only [Scc.Lower.setupArgOk2, hs, List.all_eq_true] at h
    simpa [hname] using h d hd
  have hBW : BlockW p d := by
    rcases block_kind hacc hset hd with ⟨h | h, -⟩ | h
    · subst h; exact absurd hname (by decide)
    · subst h; exact absurd hname (by decide)
    · exact h
  obtain ⟨cx, hb, hxl⟩ := hBW.body
  unfold mainArgOk at hm
  split at hm
  · rename_i a' x' y' e' hbody
    rw [hbody] at hE hb
    cases hE
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, Bool.not_eq_true'] at hm
    obtain ⟨⟨⟨rfl, -⟩, hmy⟩, hma⟩ := hm
    have hp2 : params2 d = [d.arg] := by simp [params2, harg]
    simp only [TermRun.evalAt, lookupE_cons, ite_true, Option.some.injEq, Prod.mk.injEq, harg] at he
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
    have hsim : simpleTy u = true := by
      have h2 := hBW.arg.2
      simp only [harg, simpleTy, Bool.and_eq_true] at h2
      exact h2.1
    have hn : nWords us = wr.length := by
      have := accs_simple u hsim _ (compat_plLen u _ hbs.1)
      rw [hu] at this; rw [Option.some.inj this, hbs.2.2.1]
    rw [hn, List.take_left, List.drop_left]
    simp only [body2, Bool.and_eq_true] at hb
    have hl0 : litAt ((params2 d).map (·, shapeOf d.argTy)) (.var d.arg) =
        .node (shapeOf u) (shapeOf (.ptr .pub .void)) := by
      simp [hp2, litAt, harg, shapeOf]
    have hwalk : litWalk2 p ((params2 d).map (·, shapeOf d.argTy)) (.split (.var d.arg) x y e1) =
        (.split (.var d.arg) x y e1, (params2 d).map (·, shapeOf d.argTy)) ::
          litWalk2 p ((y, shapeOf (.ptr .pub .void)) :: (x, shapeOf u) ::
            (params2 d).map (·, shapeOf d.argTy)) e1 := by
      rw [litWalk2, hl0]
    have hK0 := hBW.cnt
    rw [hbody] at hK0
    have hsa : SliceL (SlP LAll mem) (shapeOf d.argTy) (wr ++ wm) := by
      rw [harg]
      exact SliceL.pair (lb := shapeOf (.ptr .pub .void)) hss trivial hbs.2.2.1 (fun h => absurd h (hgood.2 _ hs))
    refine ⟨d.retTy, ⟨cx, _, _, y :: x :: params2 d, (y, shapeOf (.ptr .pub .void)) :: (x, shapeOf u) ::
      (params2 d).map (·, shapeOf d.argTy), fun z => z = y ∨ z = d.arg, hb.2,
      scope_cons (scope_cons (fun z hz => by simp [hp2] at hz; subst hz; simp [hp2]) x _) y _,
      ((sBufsA_nil _ _ _).cons x _ _).cons y _ _, ((SCs.nil _).cons x _ _).cons y _ _, ?_, ?_,
      fun q hq => hgood.1 d hd q (by rw [hbody, hwalk]; exact List.mem_cons_of_mem _ hq), countsB_split hl0 hK0,
      ((envSl_entry hsa).cons hss).cons trivial, hxl⟩, hBW.ret⟩
    · intro z L hz hnX
      simp only [not_or] at hnX
      rw [lookup_cons_name, lookup_cons_name] at hz
      simp only [hnX.1, ↓reduceIte] at hz
      split at hz
      · rename_i hzx
        cases hz
        refine ⟨u, wr, ?_, hbs⟩
        subst hzx
        simp only [lookupE_cons, hnX.1, ↓reduceIte]
      · simp [hp2, lookup_cons_name, hnX.2] at hz
    · rintro z (rfl | rfl)
      · exact hmy
      · exact hma
  · simp at hm

/-! ### A call -/

/-- **`main`'s body starts with a split** (`mainArgOk`). -/
theorem mainN_split {p : Prog} (hacc : Accepted2 p = true) {mem : WeakMem.Memory} {e : Expr} {env : Env}
    (hM : MainN p mem e env) :
    ∃ a x y e1, e = .split a x y e1 := by
  obtain ⟨s, d, wr, wm, hs, hf, rfl, -, -⟩ := hM
  obtain ⟨hd, hname⟩ := find_name hf
  have hm : mainArgOk d = true := by
    have h := (accepted2_parts hacc).2.2.2.2
    simp only [Scc.Lower.setupArgOk2, hs, List.all_eq_true] at h
    simpa [hname] using h d hd
  unfold mainArgOk at hm
  split at hm
  · rename_i a x y e1 hb; exact ⟨_, _, _, _, hb⟩
  · simp at hm

/-- **A call's outcome**: the callee's body, its parameter bound, the frame
pushed. -/
theorem call_step_inv {g : G} {th th' : TTh} {f : String} {ts : List Ty} {x : String} {e : Expr} {a : At}
    (h : ((callFrame g th f ts x e).bind fun fr => enter g { th with stack := fr :: th.stack } f ts a) = some th') :
    ∃ d t ws, g.p.find? (·.name == f) = some d ∧ TermRun.evalAt th.env a = some (t, ws) ∧
      th'.term = d.body ∧ th'.env = [(d.arg, close (ts.map (close th.σs)).reverse d.argTy, ws)] ∧
      th'.σs = (ts.map (close th.σs)).reverse ∧
      th'.stack = ⟨x, e, th.env, th.σs, close (ts.map (close th.σs)).reverse d.retTy⟩ :: th.stack := by
  simp only [callFrame, enter, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨fr, ⟨d, hd, rfl⟩, d', hd', ⟨t, ws⟩, he, rfl⟩ := h
  rw [hd] at hd'; cases hd'
  exact ⟨d, t, ws, hd, he, rfl, rfl, rfl, rfl⟩

theorem retOK_ownSlice : RetOK Scc.Frontend.ownSliceTy := ⟨rfl, rfl⟩

/-- **The extern's entry** on an operand at its layout with its slices: its
loads read written cells (`ldOK_print`). -/
theorem ldOK_ext {p : Prog} {mem : WeakMem.Memory}
    (hf : p.find? (·.name == "printL") = some Scc.Frontend.printLoopD) {ws : List Word}
    (hb : BindN Scc.Frontend.ownSliceTy (shapeOf Scc.Frontend.ownSliceTy) ws)
    (hsl : SliceL (SlP LAll mem) (shapeOf Scc.Frontend.ownSliceTy) ws) :
    LdOK p mem (Scc.Frontend.printExtD.body,
      [(Scc.Frontend.printExtD.arg, Scc.Frontend.printExtD.argTy, ws)]) := by
  have hlen := hb.2.2.1
  rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | _⟩⟩⟩ <;>
    simp [shapeOf, Scc.Frontend.ownSliceTy, LitV.words] at hlen
  have h2 : SliceL (SlP LAll mem) (.node (.node .loc (.leaf none)) (.leaf none)) [w0, w1, w2] := by
    simpa only [Scc.Frontend.ownSliceTy, shapeOf] using hsl
  obtain ⟨l, m, h3, h4, hP⟩ := h2.2.1.1 rfl
  have := ldOK_print (rest := [w2]) hf (l := l) (m := m) (by simpa [LitV.words] using h3)
    (by simpa [LitV.words] using h4) hP.2.1
  rw [close_nil'] at this
  exact this

/-- **A call keeps the thread invariant**: a W frame enters a W block or the
extern (suspending itself, the extern's loads reading its operand's buffer),
the start enters `rodata`. -/
theorem thN_call {p : Prog} (hacc : Accepted2 p = true)
    (hset : ∀ s, setupOf p = some s → Compat s (shapeOf s) = true) (hgood : GoodBlocks p) {g : G} (hp : g.p = p)
    {mem : WeakMem.Memory} {th th' : TTh} (hT : ThN p mem th) {x f : String} {is : List String} {a : At}
    {ts : List Ty} {e : Expr} (hterm : th.term = .let_ x (.call f is a ts) e)
    (h : ((callFrame g th f ts x e).bind fun fr => enter g { th with stack := fr :: th.stack } f ts a) = some th') :
    ThN p mem th' := by
  obtain ⟨d, t, ws, hf, he, ht', henv', hσ', hst'⟩ := call_step_inv h
  rw [hp] at hf
  obtain ⟨hσ, R, hF, hS⟩ := hT
  rw [hσ] at henv' hσ' hst'
  rcases hF with ⟨hW, hR⟩ | ⟨hE, -, -⟩ | ⟨hSM, hnil⟩
  · -- a W frame: `body2` calls take no type argument
    rw [hterm] at hW
    have hts : ts = [] := by
      obtain ⟨cx, cs, bufs, scope, lits, X, hb, -⟩ := hW
      simp only [body2, Bool.and_eq_true] at hb
      have := hb.1.1
      split at this <;> simp_all
    subst hts
    simp only [List.map_nil, List.reverse_nil, close_nil'] at henv' hσ' hst'
    have hsus : StackN p mem d.retTy ({ x, body := e, env := th.env, σs := [], ty := d.retTy } :: th.stack) :=
      ⟨rfl, Or.inl ⟨R, ⟨rfl, hR, f, is, a, [], d, hf, rfl, hW⟩, hS⟩⟩
    refine ⟨hσ', d.retTy, ?_, by rw [hst']; exact hsus⟩
    rcases block_kind hacc hset (find_name hf).1 with ⟨hd | hd, hP⟩ | hBW
    · -- the extern: its loads read its operand's buffer
      subst hd
      obtain ⟨hb, hsl⟩ := wN_call_arg hW hf retOK_ownSlice he
      refine Or.inr (Or.inl ⟨by rw [ht']; exact pureE_printExt, rfl, hP, ?_⟩)
      rw [ht', henv']
      exact ldOK_ext (printL_of_ext hacc hset (find_name hf).1) hb hsl
    · -- the loop: no `body2` call of it
      subst hd
      have hname : f = "printL" := (find_name hf).2.symm
      subst hname
      obtain ⟨cx, cs, bufs, scope, lits, X, hb, -, -, -, -, -, -, -, -, hxl⟩ := hW
      simp [body2, Scc.Lower.callee2] at hb
      exact absurd (by simpa using hxl hP) hb.1.1.1.2
    · obtain ⟨hb, hsl⟩ := wN_call_arg hW hf hBW.arg he
      exact Or.inl ⟨by rw [ht', henv']; exact wN_entry hgood (find_name hf).1 hBW mem hb hsl, hBW.ret⟩
  · rw [hterm] at hE; simp [PureE, pureOp] at hE
  · rcases hSM with (⟨s, hs, ⟨tm, wm, hme⟩, ⟨hst, hu⟩ | ⟨wr, hst, -⟩ | ⟨tm', wr, wm', hst, -⟩⟩ | ⟨-, hst, -⟩) | hM
    · -- the start calls `rodata`
      rw [hterm, setupTerm_eq] at hst
      simp only [Expr.let_.injEq, Op.call.injEq] at hst
      obtain ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩ := hst
      obtain ⟨d0, hf0, harg, hret, hBW⟩ := rodata_find hacc hset hs
      rw [hf] at hf0; cases hf0
      simp only [List.map_nil, List.reverse_nil, close_nil'] at henv' hσ' hst'
      simp only [TermRun.evalAt, hu, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      refine ⟨hσ', d.retTy, Or.inl ⟨?_, hBW.ret⟩, ?_⟩
      · rw [ht', henv']
        exact wN_entry hgood (find_name hf).1 hBW mem (by rw [harg]; exact bindN_unit) (by rw [harg]; trivial)
      · rw [hst', hnil]
        exact ⟨rfl, Or.inr ⟨⟨rfl, s, hs, rfl, rfl, hret, tm, wm, hme⟩, rfl⟩⟩
    · rw [hterm, setupRest] at hst; simp at hst
    · rw [hterm] at hst; cases hst
    · rw [hterm] at hst; cases hst
    · obtain ⟨_, _, _, _, hsp⟩ := mainN_split hacc hM
      rw [hterm] at hsp; cases hsp

/-! ### A `let` but a call -/

/-- **A `let` but a call keeps the thread invariant**: a W frame by
`wN_let`, the extern's pure `let`s, the start's pair of `rodata`'s result
with the thread word. -/
theorem thN_let {p : Prog} (hacc : Accepted2 p = true) {g : G} (hp : g.p = p) {mem : WeakMem.Memory}
    {pairs : List WeakMem.Ts} {th th' : TTh}
    (hT : ThN p mem th) {x : String} {op : Op} {e : Expr} (hterm : th.term = .let_ x op e)
    (hc : Robust.isCallOp op = false) {s' : St} {t : Ty} {ws : List Word}
    (hev : (s', t, ws) ∈ evalOp g th.env th.σs (stOf mem pairs th) op) (hm : MemExt mem s'.mem)
    (hrd : ∀ b i v, op = .xchgAt b i v → accs t = some [.one] → ∃ w, ws = [w] ∧ NumW w)
    (ht : th'.term = e) (he : th'.env = (x, t, ws) :: th.env) (hσ : th'.σs = th.σs) (hs : th'.stack = th.stack)
    (hTS : TStepE p (th.term, th.env) (th'.term, th'.env)) :
    ThN p s'.mem th' := by
  obtain ⟨hσ0, R, hF, hS⟩ := hT
  refine ⟨hσ.trans hσ0, R, ?_, by rw [hs]; exact hS.mono hm⟩
  rcases hF with ⟨hW, hR⟩ | ⟨hE, hRu, hP, hL⟩ | ⟨hSM, hnil⟩
  · rw [hterm] at hW
    rw [hσ0] at hev
    exact Or.inl ⟨by rw [ht, he]; exact wN_let hp hW hc hev hm hrd, hR⟩
  · rw [hterm] at hE
    simp only [PureE, Bool.and_eq_true] at hE
    exact Or.inr (Or.inl ⟨by rw [ht]; exact hE.2, hRu, hP, (hL.step hTS).mono hm⟩)
  · refine Or.inr (Or.inr ⟨?_, by rw [hs]; exact hnil⟩)
    rcases hSM with (⟨s, hs0, ⟨tm, wm, hme⟩, ⟨hst, -⟩ | ⟨wr, hst, hr, hbr, hsr⟩ | ⟨-, -, -, hst, -⟩⟩ |
      ⟨-, hst, -⟩) | hM
    · rw [hterm, setupTerm_eq] at hst
      simp only [Expr.let_.injEq] at hst
      obtain ⟨-, rfl, -⟩ := hst
      simp [Robust.isCallOp] at hc
    · rw [hterm, setupRest] at hst
      simp only [Expr.let_.injEq] at hst
      obtain ⟨rfl, rfl, rfl⟩ := hst
      simp only [evalOp, ol, Option.mem_toList, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at hev
      obtain ⟨⟨ta, wa⟩, hea, ⟨tb, wb⟩, heb, -, rfl, rfl⟩ := hev
      simp only [TermRun.evalAt, hr, hme, Option.some.injEq, Prod.mk.injEq] at hea heb
      obtain ⟨rfl, rfl⟩ := hea
      obtain ⟨rfl, rfl⟩ := heb
      refine Or.inl (Or.inl ⟨s, hs0, ⟨tm, wm, ?_⟩, Or.inr (Or.inr ⟨tm, wr, wm, by rw [ht], ?_, hbr, hsr.memExt hm⟩)⟩)
      · rw [he, lookupE_cons]; simpa using hme
      · rw [he, lookupE_cons]; simp
    · rw [hterm] at hst; cases hst
    · rw [hterm] at hst; cases hst
    · obtain ⟨_, _, _, _, hsp⟩ := mainN_split hacc hM
      rw [hterm] at hsp; cases hsp

/-! ### The other steps -/

theorem setupN_cases {p : Prog} {mem : WeakMem.Memory} {e : Expr} {env : Env} (h : SetupN p mem e env) :
    e = setupTerm ∨ e = setupRest ∨ e = .tail "main" [] (.var "a") := by
  obtain ⟨-, -, -, ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, -, h, -⟩⟩ | ⟨-, h, -⟩ := h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inr h)

/-- **`let (x, y) = a`** keeps the thread invariant (as `tstep` splits). -/
theorem thN_split {p : Prog} (hacc : Accepted2 p = true)
    (hset : ∀ s, setupOf p = some s → Compat s (shapeOf s) = true) (hgood : GoodBlocks p)
    {mem : WeakMem.Memory} {th th' : TTh} (hT : ThN p mem th) {a : At} {x y : String} {e : Expr}
    (hterm : th.term = .split a x y e) {u w : Ty} {ws : List Word} {us : List Acc}
    (hev : TermRun.evalAt th.env a = some (.prod u w, ws)) (hu : accs u = some us) (ht : th'.term = e)
    (he : th'.env = (y, w, ws.drop (nWords us)) :: (x, u, ws.take (nWords us)) :: th.env)
    (hσ : th'.σs = th.σs) (hs : th'.stack = th.stack) (hTS : TStepE p (th.term, th.env) (th'.term, th'.env)) :
    ThN p mem th' := by
  obtain ⟨hσ0, R, hF, hS⟩ := hT
  rcases hF with ⟨hW, hR⟩ | ⟨hE, hRu, hP, hL⟩ | ⟨hSM | hM, hnil⟩
  · rw [hterm] at hW
    exact ⟨hσ.trans hσ0, R, Or.inl ⟨by rw [ht, he]; exact wN_split hW hev hu, hR⟩, by rw [hs]; exact hS⟩
  · rw [hterm] at hE
    exact ⟨hσ.trans hσ0, R, Or.inr (Or.inl ⟨by rw [ht]; exact hE, hRu, hP, hL.step hTS⟩), by rw [hs]; exact hS⟩
  · rcases setupN_cases hSM with h | h | h <;> rw [hterm] at h <;> cases h
  · obtain ⟨R', hW, hR'⟩ := wN_main hacc hset hgood mem hM hterm hev hu
    exact ⟨hσ.trans hσ0, R', Or.inl ⟨by rw [ht, he]; exact hW, hR'⟩, by rw [hs, hnil]; trivial⟩

/-- **An index unpack** keeps the thread invariant. -/
theorem thN_unpack {p : Prog} (hacc : Accepted2 p = true) {mem : WeakMem.Memory} {th th' : TTh}
    (hT : ThN p mem th) {a : At} {i x : String} {e : Expr} (hterm : th.term = .unpack a i x e) {b : Ty}
    {ws : List Word} (hev : TermRun.evalAt th.env a = some (.iex b, ws)) (ht : th'.term = e)
    (he : th'.env = (x, b, ws) :: th.env) (hσ : th'.σs = th.σs) (hs : th'.stack = th.stack) : ThN p mem th' := by
  obtain ⟨hσ0, R, hF, hS⟩ := hT
  rcases hF with ⟨hW, hR⟩ | ⟨hE, -, -⟩ | ⟨hSM | hM, -⟩
  · rw [hterm] at hW
    exact ⟨hσ.trans hσ0, R, Or.inl ⟨by rw [ht, he]; exact wN_unpack hW hev, hR⟩, by rw [hs]; exact hS⟩
  · rw [hterm] at hE; simp [PureE] at hE
  · rcases setupN_cases hSM with h | h | h <;> rw [hterm] at h <;> cases h
  · obtain ⟨_, _, _, _, hsp⟩ := mainN_split hacc hM
    rw [hterm] at hsp; cases hsp

/-- **An `if`** keeps the thread invariant, either branch. -/
theorem thN_ifeq {p : Prog} (hacc : Accepted2 p = true) {mem : WeakMem.Memory} {th th' : TTh}
    (hT : ThN p mem th) {a b : At} {yes no : Expr} (hterm : th.term = .ifeq a b yes no)
    (ht : th'.term = yes ∨ th'.term = no) (he : th'.env = th.env) (hσ : th'.σs = th.σs)
    (hs : th'.stack = th.stack) (hTS : TStepE p (th.term, th.env) (th'.term, th'.env)) : ThN p mem th' := by
  obtain ⟨hσ0, R, hF, hS⟩ := hT
  refine ⟨hσ.trans hσ0, R, ?_, by rw [hs]; exact hS⟩
  rcases hF with ⟨hW, hR⟩ | ⟨hE, hRu, hP, hL⟩ | ⟨hSM | hM, -⟩
  · rw [hterm] at hW
    obtain ⟨hy, hn⟩ := wN_ifeq hW
    rcases ht with ht | ht
    · exact Or.inl ⟨by rw [ht, he]; exact hy, hR⟩
    · exact Or.inl ⟨by rw [ht, he]; exact hn, hR⟩
  · rw [hterm] at hE
    simp only [PureE, Bool.and_eq_true] at hE
    rcases ht with ht | ht
    · exact Or.inr (Or.inl ⟨by rw [ht]; exact hE.1, hRu, hP, hL.step hTS⟩)
    · exact Or.inr (Or.inl ⟨by rw [ht]; exact hE.2, hRu, hP, hL.step hTS⟩)
  · rcases setupN_cases hSM with h | h | h <;> rw [hterm] at h <;> cases h
  · obtain ⟨_, _, _, _, hsp⟩ := mainN_split hacc hM
    rw [hterm] at hsp; cases hsp

/-- **A return into a suspended frame** keeps the thread invariant. -/
theorem thN_ret {p : Prog} {mem : WeakMem.Memory} {th th' : TTh} (hT : ThN p mem th) {a : At}
    (hterm : th.term = .ret a) {fr : Frame} {rest : List Frame} (hst : th.stack = fr :: rest) {t : Ty}
    {ws : List Word} (hev : TermRun.evalAt th.env a = some (t, ws)) (ht : th'.term = fr.body)
    (he : th'.env = (fr.x, fr.ty, ws) :: fr.env) (hσ : th'.σs = fr.σs) (hs : th'.stack = rest) :
    ThN p mem th' := by
  obtain ⟨-, R, hF, hS⟩ := hT
  rw [hst] at hS
  rcases hF with ⟨hW, hR⟩ | ⟨hE, hRu, -⟩ | ⟨-, hnil⟩
  · rw [hterm] at hW
    exact thN_pop hS (wN_ret hW hR hev).1 (wN_ret hW hR hev).2 ht he hσ hs
  · rw [hterm] at hE
    cases a <;> simp [PureE] at hE
    simp only [TermRun.evalAt, Option.some.injEq, Prod.mk.injEq] at hev
    obtain ⟨-, rfl⟩ := hev
    subst hRu
    exact thN_pop hS bindN_unit trivial ht he hσ hs
  · rw [hst] at hnil; cases hnil

/-- **Entering a block by a tail call**: its body, its parameter bound. -/
theorem enter_step_inv {g : G} {th th' : TTh} {f : String} {ts : List Ty} {a : At}
    (h : enter g th f ts a = some th') :
    ∃ d t ws, g.p.find? (·.name == f) = some d ∧ TermRun.evalAt th.env a = some (t, ws) ∧
      th'.term = d.body ∧ th'.env = [(d.arg, close (ts.map (close th.σs)).reverse d.argTy, ws)] ∧
      th'.σs = (ts.map (close th.σs)).reverse ∧ th'.stack = th.stack := by
  simp only [enter, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨d, hd, ⟨t, ws⟩, he, rfl⟩ := h
  exact ⟨d, t, ws, hd, he, rfl, rfl, rfl, rfl⟩

/-- **A tail call** keeps the thread invariant: the extern's loop, or the
start's call of `main` (on the pair, or a W block on `()` without a setup
block). -/
theorem thN_tail {p : Prog} (hacc : Accepted2 p = true)
    (hset : ∀ s, setupOf p = some s → Compat s (shapeOf s) = true) (hgood : GoodBlocks p) {g : G} (hp : g.p = p)
    {mem : WeakMem.Memory} {th th' : TTh} (hT : ThN p mem th) {f : String} {is : List String} {a : At}
    {ts : List Ty} (hterm : th.term = .tail f is a ts) (h : enter g th f ts a = some th')
    (hTS : TStepE p (th.term, th.env) (th'.term, th'.env)) : ThN p mem th' := by
  obtain ⟨d, t, ws, hf, hev, ht, he, hσ', hs⟩ := enter_step_inv h
  rw [hp] at hf
  obtain ⟨hσ0, R, hF, hS⟩ := hT
  rw [hσ0] at he hσ'
  rcases hF with ⟨hW, -⟩ | ⟨hE, hRu, hP, hL⟩ | ⟨hSM | hM, hnil⟩
  · obtain ⟨cx, cs, bufs, scope, lits, X, hb, -⟩ := hW
    rw [hterm] at hb; simp [body2] at hb
  · rw [hterm] at hE
    simp only [PureE, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hE
    obtain ⟨rfl, rfl⟩ := hE
    have hd := printL_find hacc hset hP hf
    subst hd
    simp only [List.map_nil, List.reverse_nil] at hσ'
    exact ⟨hσ', R, Or.inr (Or.inl ⟨by rw [ht]; exact pureE_printLoop, hRu, hP, hL.step hTS⟩), by rw [hs]; exact hS⟩
  · rcases hSM with ⟨s, hs0, -, ⟨hst, -⟩ | ⟨-, hst, -⟩ | ⟨tm, wr, wm, hst, ha, hbr, hsr⟩⟩ | ⟨hs0, hst, ha⟩
    · rw [hterm, setupTerm_eq] at hst; cases hst
    · rw [hterm, setupRest] at hst; cases hst
    · rw [hterm] at hst
      simp only [Expr.tail.injEq] at hst
      obtain ⟨rfl, -, rfl, rfl⟩ := hst
      simp only [TermRun.evalAt, ha, Option.some.injEq, Prod.mk.injEq] at hev
      obtain ⟨-, rfl⟩ := hev
      simp only [List.map_nil, List.reverse_nil, close_nil'] at he hσ'
      exact ⟨hσ', R, Or.inr (Or.inr ⟨Or.inr ⟨s, d, wr, wm, hs0, hf, ht, he, hbr, hsr⟩, by rw [hs, hnil]⟩), by
        rw [hs, hnil]; trivial⟩
    · -- no setup block: `main` is a W block entered on `()`
      rw [hterm] at hst
      simp only [Expr.tail.injEq] at hst
      obtain ⟨rfl, -, rfl, rfl⟩ := hst
      simp only [TermRun.evalAt, ha, Option.some.injEq, Prod.mk.injEq] at hev
      obtain ⟨-, rfl⟩ := hev
      simp only [List.map_nil, List.reverse_nil, close_nil'] at he hσ'
      obtain ⟨hd, hname⟩ := find_name hf
      have harg := main_argTy_none hacc hs0 hf
      have hBW : BlockW p d := by
        rcases block_kind hacc hset hd with ⟨h | h, -⟩ | h
        · subst h; exact absurd hname (by decide)
        · subst h; exact absurd hname (by decide)
        · exact h
      have hWN := wN_entry hgood hd hBW mem (ws := []) (by rw [harg]; exact bindN_unit) (by rw [harg]; trivial)
      exact ⟨hσ', d.retTy, Or.inl ⟨by rw [ht, he]; exact hWN, hBW.ret⟩, by rw [hs, hnil]; trivial⟩
  · obtain ⟨_, _, _, _, hsp⟩ := mainN_split hacc hM
    rw [hterm] at hsp; cases hsp

/-! ### One step of the thread -/

/-- **The terms the invariant allows**: a `body2` body, the extern's, the
start's three, or `main`'s split. -/
theorem thN_shape {p : Prog} (hacc : Accepted2 p = true) {mem : WeakMem.Memory} {th : TTh} (hT : ThN p mem th) :
    (∃ cx cs bufs scope, body2 cx cs bufs scope th.term = true) ∨ PureE th.term = true ∨
      th.term = setupTerm ∨ th.term = setupRest ∨ th.term = .tail "main" [] (.var "a") ∨
      ∃ a x y e, th.term = .split a x y e := by
  obtain ⟨-, R, hF, -⟩ := hT
  rcases hF with ⟨⟨cx, cs, bufs, scope, -, -, hb, -⟩, -⟩ | ⟨hE, -⟩ | ⟨hSM | hM, -⟩
  · exact Or.inl ⟨cx, cs, bufs, scope, hb⟩
  · exact Or.inr (Or.inl hE)
  · rcases setupN_cases hSM with h | h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (mainN_split hacc hM)))))

/-- **One thread step keeps the thread invariant** (`tstep`), given that the
memory grows and that a one-word exchange reads a number. -/
theorem tstep_thN {p : Prog} (hacc : Accepted2 p = true)
    (hset : ∀ s, setupOf p = some s → Compat s (shapeOf s) = true) (hgood : GoodBlocks p) {g : G} (hp : g.p = p)
    {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh} (hT : ThN p mem th)
    {r : WeakMem.Memory × List WeakMem.Ts × TTh} (hr : r ∈ tstep g mem pairs th) (hm : MemExt mem r.1)
    (hrd : ∀ x b i v e s' t ws, th.term = .let_ x (.xchgAt b i v) e →
      (s', t, ws) ∈ evalOp g th.env th.σs (stOf mem pairs th) (.xchgAt b i v) → s'.mem = r.1 →
      s'.vs = r.2.2.vs → s'.promises = r.2.2.promises → accs t = some [.one] → ∃ w, ws = [w] ∧ NumW w) :
    ThN p r.1 r.2.2 := by
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
  have hTS : NoRC th.term → TStepE p (th.term, th.env) (r.2.2.term, r.2.2.env) :=
    fun hn => Or.inl ⟨g, mem, pairs, th, r, hp, rfl, rfl, hn, hr, rfl, rfl⟩
  obtain ⟨m', pr', th'⟩ := r
  simp only at hm hrd hTS ⊢
  cases hterm : th.term with
  | let_ x op e =>
    cases op
    case call f is a ts =>
      simp only [tstep, hterm, ol, Option.mem_toList, Option.map_eq_some_iff, Prod.mk.injEq] at hr
      obtain ⟨th1, h1, rfl, rfl, rfl⟩ := hr
      exact thN_call hacc hset hgood hp hT hterm h1
    case callc f a =>
      exact (bad (fun _ _ _ _ => by rw [hterm]; rfl) (by rw [hterm]; rfl) (by rw [hterm, setupTerm_eq]; simp)
        (by rw [hterm, setupRest]; simp) (by rw [hterm]; simp) (fun _ _ _ _ => by rw [hterm]; simp)).elim
    case new a T =>
      obtain ⟨s', t, ws, hev, tys, hr'⟩ := TermRun.tstep_new_mem hterm hr
      simp only [Prod.mk.injEq] at hr'
      obtain ⟨rfl, rfl, rfl⟩ := hr'
      exact thN_let hacc hp hT hterm rfl hev hm (fun b' i' v' hop _ => by cases hop) rfl rfl rfl rfl
        (hTS (by rw [hterm]; exact ⟨fun _ h => (by cases h), fun _ _ _ _ _ _ h => (by cases h)⟩))
    all_goals
      simp only [tstep, hterm, List.mem_map, Prod.mk.injEq] at hr
      obtain ⟨⟨s', t, ws⟩, hev, rfl, rfl, rfl⟩ := hr
      exact thN_let hacc hp hT hterm rfl hev hm
        (fun b' i' v' hop hu => by cases hop <;> exact hrd _ _ _ _ _ _ _ _ hterm hev rfl rfl rfl hu) rfl rfl rfl rfl
        (hTS (by rw [hterm]; exact ⟨fun _ h => (by cases h), fun _ _ _ _ _ _ h => (by cases h)⟩))
  | split a x y e =>
    simp only [tstep, hterm] at hr
    split at hr <;> try (simp at hr; done)
    split at hr <;> try (simp at hr; done)
    simp only [List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl, rfl⟩ := hr
    exact thN_split hacc hset hgood hT hterm (by assumption) (by assumption) rfl rfl rfl rfl
      (hTS (by rw [hterm]; exact ⟨fun _ h => (by cases h), fun _ _ _ _ _ _ h => (by cases h)⟩))
  | unpack a i x e =>
    simp only [tstep, hterm] at hr
    split at hr <;> try (simp at hr; done)
    simp only [List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl, rfl⟩ := hr
    exact thN_unpack hacc hT hterm (by assumption) rfl rfl rfl rfl
  | ifeq a b yes no =>
    simp only [tstep, hterm] at hr
    split at hr <;> try (simp at hr; done)
    split at hr <;> try (simp at hr; done)
    all_goals
      simp only [List.mem_singleton, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl, rfl⟩ := hr
      exact thN_ifeq hacc hT hterm (by dsimp only; split <;> simp) rfl rfl rfl
        (hTS (by rw [hterm]; exact ⟨fun _ h => (by cases h), fun _ _ _ _ _ _ h => (by cases h)⟩))
  | ret a =>
    simp only [tstep, hterm] at hr
    split at hr <;> try (simp at hr; done)
    simp only [List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl, rfl⟩ := hr
    exact thN_ret hT hterm (by assumption) (by assumption) rfl rfl rfl rfl
  | tail f is a ts =>
    simp only [tstep, hterm, ol, Option.mem_toList, Option.map_eq_some_iff, Prod.mk.injEq] at hr
    obtain ⟨th1, h1, rfl, rfl, rfl⟩ := hr
    exact thN_tail hacc hset hgood hp hT hterm h1
      (hTS (by rw [hterm]; exact ⟨fun _ h => (by cases h), fun _ _ _ _ _ _ h => (by cases h)⟩))
  | _ =>
    exact (bad (fun _ _ _ _ => by rw [hterm]; rfl) (by rw [hterm]; rfl) (by rw [hterm, setupTerm_eq]; simp)
      (by rw [hterm, setupRest]; simp) (by rw [hterm]; simp) (fun _ _ _ _ => by rw [hterm]; simp)).elim

end thread

end Spike.Lib.LowerNode
