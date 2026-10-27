import Spike.Lib.Src.NoAcq
import Spike.Lib.Src.NJLB

/-!
**The source's exchange cells are written** (ISA-neutral): a source-reach
invariant for the `xchg` side of the source safety (`SrcSafeS.xchg`). Every
frame of every thread is either

- (W) at a point of an `Accepted2` body (`body2` with its known values `cs`
  and buffers `bufs`), its environment binding each buffer of `bufs` to a
  label whose first cells have messages (`SBufsA`) and each known value to its
  number (`SCs`); or
- (E) free of exchanges (`NoS XOp`): the start's wrapper, the output extern
  and its loop.

A suspended frame is W after its call's result (`unbuf` of the result's name)
or E. Entering a block gives a W frame with no buffer, or an E frame
(`BlocksB`). Nothing about values or types is tracked: an exchange's cell
needs only its buffer's binding and `body2`'s index bound.

- `XOp`, `WB`, `FrB`, `SusB`, `ThB`, `CfgB`: the invariant; `.mono` in the
  memory;
- `BlocksB p`: every block is E or a `body2` body from no buffer;
- `tstep_thB`: one step of a thread; `reach_cfgB`: every reachable
  configuration (with `CfgNoS AcqOp`, which excludes spawns);
- `WB.xchgSite_cell`, `CfgB.xchg`: an exchange site's cell has a message.
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm A9NoSpawn TermRun Scc.Sem
open Scc.Lower (body2 unbuf constOf bindC elem2 atom1)

/-- **The exchanges**: of a cell and of a buffer's slot. -/
def XOp : Op → Prop
  | .xchg .. | .xchgAt .. => True
  | _ => False

/-- Every label (the invariant does not restrict the buffers' labels). -/
abbrev LAll : WeakMem.AllocLabel → Prop := fun _ => True

/-- **A frame at a point of an `Accepted2` body** with its buffers written. -/
def WB (mem : WeakMem.Memory) (e : Expr) (env : Env) : Prop :=
  ∃ cx cs bufs scope, body2 cx cs bufs scope e = true ∧ SBufsA env bufs LAll mem ∧ SCs env cs

/-- **A current frame**: W or free of exchanges. -/
def FrB (mem : WeakMem.Memory) (e : Expr) (env : Env) : Prop := WB mem e env ∨ NoS XOp e

/-- **A suspended frame**: W once its call's result is bound, or free of
exchanges. -/
def SusB (mem : WeakMem.Memory) (fr : Frame) : Prop :=
  (∃ cx cs bufs scope, body2 cx (unbuf fr.x cs) (unbuf fr.x bufs) (fr.x :: scope) fr.body = true ∧
    SBufsA fr.env bufs LAll mem ∧ SCs fr.env cs) ∨ NoS XOp fr.body

/-- **A thread**: its current frame and every suspended one. -/
def ThB (mem : WeakMem.Memory) (th : TTh) : Prop := FrB mem th.term th.env ∧ ∀ fr ∈ th.stack, SusB mem fr

/-- **A configuration**: every thread at the configuration's memory. -/
def CfgB (c : Cfg) : Prop := ∀ (i : Nat) (th : TTh), c.ths[i]? = some th → ThB c.mem th

/-- **Every block is E or an `Accepted2` body from no buffer.** -/
def BlocksB (p : Prog) : Prop :=
  ∀ d ∈ p, NoS XOp d.body ∨ ∃ cx scope, body2 cx [] [] scope d.body = true

/-! ## Memory growth -/

section mono

variable {mem mem' : WeakMem.Memory} (hm : ∀ sa, HasCell mem sa → HasCell mem' sa)
include hm

theorem WB.mono {e : Expr} {env : Env} (h : WB mem e env) : WB mem' e env :=
  let ⟨cx, cs, bufs, scope, hb, hB, hC⟩ := h
  ⟨cx, cs, bufs, scope, hb, hB.mono (fun _ h => h) hm, hC⟩

theorem FrB.mono {e : Expr} {env : Env} (h : FrB mem e env) : FrB mem' e env :=
  h.imp (WB.mono hm) id

theorem SusB.mono {fr : Frame} (h : SusB mem fr) : SusB mem' fr :=
  h.imp (fun ⟨cx, cs, bufs, scope, hb, hB, hC⟩ => ⟨cx, cs, bufs, scope, hb, hB.mono (fun _ h => h) hm, hC⟩) id

theorem ThB.mono {th : TTh} (h : ThB mem th) : ThB mem' th :=
  ⟨h.1.mono hm, fun fr hf => (h.2 fr hf).mono hm⟩

end mono

theorem hasCell_of_memExt {mem mem' : WeakMem.Memory} (h : TermCert.MemExt mem mem') {sa : WeakMem.Address}
    (hc : HasCell mem sa) : HasCell mem' sa :=
  let ⟨k, m, hk, hl⟩ := hc
  ⟨k, m, h k m hk, hl⟩

/-! ## Terms free of exchanges -/

theorem NoS.sub {bad : Op → Prop} {e s : Expr} (h : NoS bad e) (hs : s ∈ Robust.subs e) : NoS bad s := by
  cases e <;> simp only [Robust.subs, List.mem_cons, List.not_mem_nil, or_false] at hs <;>
    simp only [NoS] at h <;> first | (subst hs; first | exact h | exact h.2) | (rcases hs with rfl | rfl <;>
      first | exact h.1 | exact h.2) | exact absurd hs (by simp)

/-! ## Entering a block -/

theorem enter_inv {g : G} {th th' : TTh} {f : String} {ts : List Ty} {a : At} (h : enter g th f ts a = some th') :
    ∃ d ∈ g.p, th'.term = d.body ∧ (∃ t ws, th'.env = [(d.arg, t, ws)]) ∧ th'.stack = th.stack := by
  simp only [enter, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨d, hd, ⟨t, ws⟩, -, rfl⟩ := h
  exact ⟨d, List.mem_of_find?_eq_some hd, rfl, ⟨_, _, rfl⟩, rfl⟩

/-- **A block's entry is a current frame.** -/
theorem frB_entry {p : Prog} (hp : BlocksB p) {d : Decl} (hd : d ∈ p) (mem : WeakMem.Memory) (env : Env) :
    FrB mem d.body env := by
  rcases hp d hd with h | ⟨cx, scope, hb⟩
  · exact Or.inr h
  · exact Or.inl ⟨cx, [], [], scope, hb, sBufsA_nil _ _ _, SCs.nil _⟩

/-! ## One step of a frame -/

section step

variable {mem mem' : WeakMem.Memory} {cx : Scc.Lower.Cx2} {cs bufs : List (String × Nat)} {scope : List String}
  {env : Env} {x : String} {t : Ty} {ws : List Word} {e : Expr}

/-- **`let x = op`** that drops `x` from the known values and buffers. -/
theorem wB_let (hm : TermCert.MemExt mem mem') (hb : body2 cx (unbuf x cs) (unbuf x bufs) (x :: scope) e = true)
    (hB : SBufsA env bufs LAll mem) (hC : SCs env cs) : WB mem' e ((x, t, ws) :: env) :=
  ⟨cx, _, _, _, hb, (hB.cons x t ws).mono (fun _ h => h) (fun _ => hasCell_of_memExt hm), hC.cons x t ws⟩

/-- **`let x = a`** (or `nameI a`): `x` known when `a` is. -/
theorem wB_letC {a : At} (hm : TermCert.MemExt mem mem')
    (hb : body2 cx (bindC x (constOf cs a) cs) (unbuf x bufs) (x :: scope) e = true)
    (hB : SBufsA env bufs LAll mem) (hC : SCs env cs) (he : ∃ t', evalAt env a = some (t', ws)) :
    WB mem' e ((x, t, ws) :: env) :=
  ⟨cx, _, _, _, hb, (hB.cons x t ws).mono (fun _ h => h) (fun _ => hasCell_of_memExt hm),
    hC.after x (.atom a) t ws fun a' h => by
      rcases h with h | h <;> cases h
      exact he⟩

/-- **A return** into a suspended frame. -/
theorem frB_ret {fr : Frame} (hf : SusB mem fr) : FrB mem fr.body ((fr.x, t, ws) :: fr.env) := by
  rcases hf with ⟨cx, cs, bufs, scope, hb, hB, hC⟩ | hn
  · exact Or.inl ⟨cx, _, _, _, hb, hB.cons _ _ _, hC.cons _ _ _⟩
  · exact Or.inr hn

end step

theorem evalOp_atom_inv {g : G} {env : Env} {σs : List Ty} {s s' : St} {a : At} {t : Ty} {ws : List Word}
    (h : (s', t, ws) ∈ evalOp g env σs s (.atom a)) : ∃ t', evalAt env a = some (t', ws) := by
  simp only [evalOp, ol, Option.mem_toList, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨t0, w0⟩, he, -, rfl, rfl⟩ := h
  exact ⟨_, he⟩

theorem evalOp_nameI_inv {g : G} {env : Env} {σs : List Ty} {s s' : St} {a : At} {t : Ty} {ws : List Word}
    (h : (s', t, ws) ∈ evalOp g env σs s (.nameI a)) : ∃ t', evalAt env a = some (t', ws) := by
  simp only [evalOp, ol, Option.mem_toList, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨t0, w0⟩, he, -, rfl, rfl⟩ := h
  exact ⟨_, he⟩

theorem evalOp_newBuf_inv {g : G} {env : Env} {σs : List Ty} {s s' : St} {n : At} {τ : Ty} {t : Ty}
    {ws : List Word} (h : (s', t, ws) ∈ evalOp g env σs s (.newBuf n τ)) :
    ∃ ta wn k us z ini, evalAt env n = some (ta, wn) ∧ numOf wn = some k ∧ accs (close σs τ) = some us ∧
      s' = (allocBuf (freshLabel g.lbase g.n g.i s.nalloc) (k * nWords us) z s).1 ∧
      t = .refine (.loc .own (.array (.lit k) (close σs τ))) (.ini (.lit ini)) ∧
      ws = [cst (.loc ⟨freshLabel g.lbase g.n g.i s.nalloc, 0⟩ 0)] := by
  simp only [evalOp, ol, Option.mem_toList] at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨⟨ta, wn⟩, hn, k, hk, us, hus, h⟩ := h
  exact ⟨ta, wn, k, us, _, _, hn, hk, hus, h.1.symm, h.2.1.symm, h.2.2.symm⟩

theorem callFrame_inv {g : G} {th : TTh} {f : String} {ts : List Ty} {x : String} {e : Expr} {fr : Frame}
    (h : callFrame g th f ts x e = some fr) : fr.x = x ∧ fr.body = e ∧ fr.env = th.env := by
  simp only [callFrame, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨d, -, rfl⟩ := h
  exact ⟨rfl, rfl, rfl⟩

/-- **The frame a call suspends.** -/
theorem susB_call {mem : WeakMem.Memory} {x : String} {op : Op} {e : Expr} {env : Env} {fr : Frame}
    (h : FrB mem (.let_ x op e) env) (hop : Robust.isCallOp op = true) (hx : fr.x = x) (hb : fr.body = e)
    (he : fr.env = env) : SusB mem fr := by
  rcases h with ⟨cx, cs, bufs, scope, hb2, hB, hC⟩ | hn
  · left
    refine ⟨cx, cs, bufs, scope, ?_, by rw [he]; exact hB, by rw [he]; exact hC⟩
    rw [hx, hb]
    cases op <;> simp [Robust.isCallOp] at hop <;> simp only [body2, Bool.and_eq_true, Bool.false_eq_true] at hb2
    exact hb2.2
  · right; rw [hb]; exact hn.2

theorem thB_of {mem mem' : WeakMem.Memory} {th th' : TTh} (hm : TermCert.MemExt mem mem') (hT : ThB mem th)
    (hf : FrB mem' th'.term th'.env) (hs : th'.stack = th.stack) : ThB mem' th' :=
  ⟨hf, fun fr hfr => (hT.2 fr (hs ▸ hfr)).mono fun _ => hasCell_of_memExt hm⟩

/-- **A block entered with a frame pushed.** -/
theorem thB_enter {p : Prog} (hp : BlocksB p) {mem : WeakMem.Memory} {th th' : TTh} {d : Decl} (hd : d ∈ p)
    {fr : Frame} (hterm : th'.term = d.body) (hst : th'.stack = fr :: th.stack) (hS : SusB mem fr)
    (hT : ThB mem th) : ThB mem th' := by
  refine ⟨by rw [hterm]; exact frB_entry hp hd _ _, fun fr' hf => ?_⟩
  rw [hst] at hf
  rcases List.mem_cons.1 hf with rfl | hf
  · exact hS
  · exact hT.2 fr' hf

/-- **A straight step of a frame free of exchanges.** -/
theorem thB_E {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {r : WeakMem.Memory × List WeakMem.Ts × TTh} (hT : ThB mem th) (hs : TermLocal.straight th.term = true)
    (hn : NoS XOp th.term) (hr : r ∈ tstep g mem pairs th) : ThB r.1 r.2.2 :=
  let h := TermLocal.tstep_shape hs hr
  thB_of (TermFul.tstep_grow hr).1 hT (Or.inr (NoS.sub hn h.1)) h.2.1

/-! ## One step of a thread -/

section tstep

variable {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
  {r : WeakMem.Memory × List WeakMem.Ts × TTh}

/-- **A call** (`call`, `callc`): the continuation is suspended, the callee entered. -/
theorem thB_call (hp : BlocksB g.p) (hT : ThB mem th) {x : String} {op : Op} {e : Expr}
    (hterm : th.term = .let_ x op e) (hc : Robust.isCallOp op = true) (hr : r ∈ tstep g mem pairs th) :
    ThB r.1 r.2.2 := by
  have hF := hT.1
  rw [hterm] at hF
  cases op <;> simp [Robust.isCallOp] at hc
  · simp only [tstep, hterm, ol, Option.mem_toList, Option.map_eq_some_iff, Option.bind_eq_some_iff] at hr
    obtain ⟨th', ⟨fr, hfr, hen⟩, rfl⟩ := hr
    obtain ⟨d, hd, ht', -, hst⟩ := enter_inv hen
    obtain ⟨hx, hb, he⟩ := callFrame_inv hfr
    exact thB_enter hp hd ht' hst (susB_call hF rfl hx hb he) hT
  · simp only [tstep, hterm] at hr
    repeat' split at hr
    all_goals try (simp at hr; done)
    simp only [ol, Option.mem_toList, Option.map_eq_some_iff, Option.bind_eq_some_iff] at hr
    obtain ⟨th', ⟨fr, hfr, hen⟩, rfl⟩ := hr
    obtain ⟨d, hd, ht', -, hst⟩ := enter_inv hen
    obtain ⟨hx, hb, he⟩ := callFrame_inv hfr
    exact thB_enter hp hd ht' hst (susB_call hF rfl hx hb he) hT

/-- **Any other `let`**: an `Accepted2` operation keeps the frame W. -/
theorem thB_let (hT : ThB mem th) {x : String} {op : Op} {e : Expr} (hterm : th.term = .let_ x op e)
    (hc : Robust.isCallOp op = false) (hr : r ∈ tstep g mem pairs th) : ThB r.1 r.2.2 := by
  have hm := (TermFul.tstep_grow hr).1
  rw [TermLocal.tstep_let_gen hterm hc] at hr
  simp only [List.mem_map] at hr
  obtain ⟨⟨s', t, ws⟩, hev, rfl⟩ := hr
  refine thB_of hm hT ?_ rfl
  show FrB s'.mem e ((x, t, ws) :: th.env)
  replace hm : TermCert.MemExt mem s'.mem := hm
  have hF := hT.1
  rw [hterm] at hF
  rcases hF with hF | hn
  case inr => exact Or.inr hn.2
  obtain ⟨cx, cs, bufs, scope, hb, hB, hC⟩ := hF
  left
  cases op with
  | atom a =>
    simp only [body2, Bool.and_eq_true] at hb
    exact wB_letC hm hb.2 hB hC (evalOp_atom_inv hev)
  | nameI a =>
    simp only [body2, Bool.and_eq_true] at hb
    exact wB_letC hm hb.2 hB hC (evalOp_nameI_inv hev)
  | add a b | sub a b | pair a b | asLanes _ _ a | pack a _ _ =>
    simp only [body2, Bool.and_eq_true] at hb
    exact wB_let hm hb.2 hB hC
  | xchgAt b i v =>
    cases b <;> cases i <;> simp only [body2, Bool.and_eq_true, Bool.false_eq_true] at hb
    exact wB_let hm hb.2 hB hC
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
      exact ⟨cx, _, _, _, hmt.2,
        (sBufsA_newBuf (s := stOf mem pairs th) hB x he2 hus z hmt.1.2).mono (fun _ _ => trivial) (fun _ h => h),
        hC.cons x _ _⟩
  | call _ _ _ _ | callc _ _ => simp [Robust.isCallOp] at hc
  | _ => simp [body2] at hb

/-- **A return**: the suspended frame resumes. -/
theorem thB_ret (hT : ThB mem th) {a : At} (hterm : th.term = .ret a) (hr : r ∈ tstep g mem pairs th) :
    ThB r.1 r.2.2 := by
  cases hs : th.stack with
  | nil => simp [tstep, hterm, hs] at hr
  | cons f rest =>
    cases ha : evalAt th.env a with
    | none => simp [tstep, hterm, hs, ha] at hr
    | some p =>
      obtain ⟨t, ws⟩ := p
      simp only [tstep, hterm, hs, ha, List.mem_singleton] at hr
      subst hr
      exact ⟨frB_ret (hT.2 f (by simp [hs])), fun fr hf => hT.2 fr (by rw [hs]; simp [hf])⟩

/-- **A tail call**: the callee entered, the stack kept. -/
theorem thB_tail (hp : BlocksB g.p) (hT : ThB mem th) {f : String} {is : List String} {a : At} {ts : List Ty}
    (hterm : th.term = .tail f is a ts) (hr : r ∈ tstep g mem pairs th) : ThB r.1 r.2.2 := by
  simp only [tstep, hterm, ol, Option.mem_toList, Option.map_eq_some_iff] at hr
  obtain ⟨th', hen, rfl⟩ := hr
  obtain ⟨d, hd, ht', -, hst⟩ := enter_inv hen
  exact ⟨by rw [ht']; exact frB_entry hp hd _ _, fun fr hf => hT.2 fr (hst ▸ hf)⟩

/-- **One step of a thread keeps it.** -/
theorem tstep_thB (hp : BlocksB g.p) (hT : ThB mem th) (hr : r ∈ tstep g mem pairs th) : ThB r.1 r.2.2 := by
  have hF := hT.1
  cases hterm : th.term with
  | let_ x op e =>
    cases hc : Robust.isCallOp op with
    | true => exact thB_call hp hT hterm hc hr
    | false => exact thB_let hT hterm hc hr
  | ret a => exact thB_ret hT hterm hr
  | tail f is a ts => exact thB_tail hp hT hterm hr
  | split a x y e =>
    rw [hterm] at hF
    simp only [tstep, hterm] at hr
    repeat' split at hr
    all_goals try (simp at hr; done)
    simp only [List.mem_singleton] at hr
    subst hr
    refine thB_of (TermCert.MemExt.rfl' _) hT ?_ rfl
    rcases hF with ⟨cx, cs, bufs, scope, hb, hB, hC⟩ | hn
    · simp only [body2, Bool.and_eq_true] at hb
      exact Or.inl ⟨cx, _, _, _, hb.2, (hB.cons x _ _).cons y _ _, (hC.cons x _ _).cons y _ _⟩
    · exact Or.inr hn
  | unpack a i x e =>
    rw [hterm] at hF
    simp only [tstep, hterm] at hr
    repeat' split at hr
    all_goals try (simp at hr; done)
    simp only [List.mem_singleton] at hr
    subst hr
    refine thB_of (TermCert.MemExt.rfl' _) hT ?_ rfl
    rcases hF with ⟨cx, cs, bufs, scope, hb, hB, hC⟩ | hn
    · simp only [body2, Bool.and_eq_true] at hb
      exact Or.inl ⟨cx, _, _, _, hb.2, (hB.unbuf i).cons x _ _, (hC.unbuf i).cons x _ _⟩
    · exact Or.inr hn
  | ifeq a b yes no =>
    rw [hterm] at hF
    simp only [tstep, hterm] at hr
    repeat' split at hr
    all_goals try (simp at hr; done)
    all_goals
      simp only [List.mem_singleton] at hr
      subst hr
      refine thB_of (TermCert.MemExt.rfl' _) hT ?_ rfl
      rcases hF with ⟨cx, cs, bufs, scope, hb, hB, hC⟩ | hn
      · simp only [body2, Bool.and_eq_true] at hb
        first
          | exact Or.inl ⟨cx, cs, bufs, scope, hb.1.2, hB, hC⟩
          | exact Or.inl ⟨cx, cs, bufs, scope, hb.2, hB, hC⟩
      · first
          | exact Or.inr hn.1
          | exact Or.inr hn.2
  | _ =>
    rw [hterm] at hF
    rcases hF with ⟨_, _, _, _, hb, -⟩ | hn
    · simp [body2] at hb
    · exact thB_E hT (by rw [hterm]; rfl) (hterm ▸ hn) hr

end tstep

/-! ## Every reachable configuration -/

theorem cfgB_thread {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {c c' : Cfg} {i : Nat}
    (hp : BlocksB p) (hc : CfgB c) (h : c' ∈ threadSteps p k arch c i) : CfgB c' := by
  unfold threadSteps at h
  cases hth : c.ths[i]? with
  | none => rw [hth] at h; cases h
  | some th =>
    rw [hth] at h
    simp only [List.mem_map] at h
    obtain ⟨⟨mem', pairs', th'⟩, hr, rfl⟩ := h
    have hm := (TermFul.tstep_grow hr).1
    intro j th0 hj
    rcases getElem?_set!_or hj with rfl | hj
    · exact tstep_thB (g := gOf p k arch c i) hp (hc i th hth) hr
    · exact (hc j th0 hj).mono fun _ => hasCell_of_memExt hm

theorem cfgB_prom {c : Cfg} {i : Nat} {a : WeakMem.Address} {v : WeakMem.Val} {w : WeakMem.Ts}
    (hc : CfgB c) : CfgB (promise c i a v w) := by
  unfold promise
  cases hth : c.ths[i]? with
  | none => exact hc
  | some th =>
    intro j th0 hj
    have hm : ∀ sa, HasCell c.mem sa → HasCell (c.mem.push ⟨a, v, w⟩) sa := fun _ h => h.push _
    rcases getElem?_set!_or hj with rfl | hj
    · exact ⟨(hc i th hth).1.mono hm, fun fr hf => ((hc i th hth).2 fr hf).mono hm⟩
    · exact (hc j th0 hj).mono hm

/-- **An extern step keeps the invariant**: its site is in an E frame
(`body2` has no extern), so its body is E; the stack and the memory are kept. -/
theorem cfgB_ext {c : Cfg} {i : Nat} {th : TTh} (hth : c.ths[i]? = some th) {x : String} {n : ExtName}
    {a : At} {e : Expr} (hterm : th.term = .let_ x (.ext n a) e) (hc : CfgB c) (ws rs : List Word) :
    CfgB (extCfg c i th x n e ws rs) := by
  have hT := hc i th hth
  have he : FrB c.mem e ((x, (n.sig.2 : Ty), rs) :: th.env) := by
    rcases hT.1 with ⟨cx, cs, bufs, scope, hb, -⟩ | hn
    · rw [hterm] at hb; simp [body2] at hb
    · rw [hterm] at hn; exact Or.inr hn.2
  have hE : NoS XOp e := by
    rcases hT.1 with ⟨cx, cs, bufs, scope, hb, -⟩ | hn
    · rw [hterm] at hb; simp [body2] at hb
    · rw [hterm] at hn; exact hn.2
  have key : ∀ {th' : TTh} (j : Nat) (th0 : TTh), (c.ths.set! i th')[j]? = some th0 →
      th'.term = e → th'.stack = th.stack → ThB c.mem th0 := by
    intro th' j th0 hj ht hs
    rcases getElem?_set!_or hj with rfl | hj
    · exact ⟨Or.inr (ht ▸ hE), hs ▸ hT.2⟩
    · exact hc j th0 hj
  intro j th0 hj
  rw [TermExtStep.extCfg_mem]
  cases n with
  | current =>
      cases hl : th.tidLbl with
      | some l => simp only [extCfg, curCfg, hl] at hj; exact key j th0 hj rfl rfl
      | none => simp only [extCfg, curCfg, hl] at hj; exact key j th0 hj rfl rfl
  | _ => exact key j th0 hj rfl rfl

/-- **A wake keeps the invariant** (it changes only permits). -/
theorem cfgB_wake {c : Cfg} (i : Nat) (v : WeakMem.Ts) (n : ExtName) (ws : List Word) (hc : CfgB c) :
    CfgB (wake c i v n ws) := fun j th0 hj => by
  rw [TermExtStep.wake_mem]
  rcases TermExtStep.wake_get c i v n ws j with h | ⟨th, u, h1, h2⟩
  · rw [h] at hj; exact hc j th0 hj
  · rw [h2] at hj; cases hj; exact hc j th h1

/-- **Every reachable source configuration keeps the invariant** (and is free
of `AcqOp`, which excludes spawns), with no hook or WeakCore's (`UsesWc`:
`cfgB_ext`, `cfgB_wake`). -/
theorem reach_cfgB {P : SrcSem.SrcParams} {p : Prog} (hb : BlocksB p) (hp : ProgNoS AcqOp p)
    (hH : P.hooks = SrcSem.SrcHooks.none ∨ SrcOutProto.UsesWc P p)
    (hinit : ∀ c, P.init c → CfgB c ∧ CfgNoS AcqOp c) {tr : List Ev}
    {s : Cfg} (h : (SrcSem.source P p).Reach tr s) : CfgB s ∧ CfgNoS AcqOp s := by
  obtain ⟨s0, h0, hr⟩ := h
  have H := hinit s0 h0
  clear h0
  induction hr with
  | refl => exact H
  | step hs _ ih =>
    obtain ⟨i, -, hs, -⟩ := hs
    apply ih
    rcases hs with hs | hs | hs
    · rcases hs with ⟨hs, -⟩ | ⟨a, v, w, -, -, -, rfl⟩
      · exact ⟨cfgB_thread hb H.1 hs, cfgNoS_thread_acq hp H.2 hs⟩
      · exact ⟨cfgB_prom H.1, cfgNoS_prom_acq H.2⟩
    · exact (no_spawnBy_acq H.2 hs).elim
    · rcases hH with hH | hH <;> rw [hH] at hs
      · exact hs.elim
      obtain ⟨x, n, a, e, th1, rt, ws, rs, h1, hterm, -, -, -, -, rfl⟩ := hs
      exact ⟨cfgB_wake _ _ _ _ (cfgB_ext h1 hterm H.1 ws rs), cfgNoS_wakeB _ _ _ _ (cfgNoS_extB h1 hterm H.2 ws rs)⟩

end Spike.Lib.LowerNode
