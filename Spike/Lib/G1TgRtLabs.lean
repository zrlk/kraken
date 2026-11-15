/-
**The global labels of the runtime's IR functions** (ISA-neutral): every
function of the runtime (`Scc.Lower.Inv.rtFuncs`) is named `scc_rt_…`, and
every label its instructions place besides the emitter's own (a system
call's trap label, a site's label; `instLabs`) is one of the runtime's
sites or abort exits, also named `scc_rt_…` (`RtName`). So no label of the
runtime's code is a user function's (`.L<digits>_wc_…`), on either ISA.

The runtime's functions are built in the builder monad `B`
(`Scc/Lower/Builder.lean`); the proof is an invariant of the builder's
state (`SGood`: every instruction of the finished and the open block has
its labels `RtLab`), preserved by every action the runtime uses (`Pres`),
checked at each `emit` of a labelled instruction.

- `instLabs`, `RtLab`, `RtName`: the labels an instruction places, the
  runtime's global labels, a `scc_rt_` name;
- `Pres`, its combinators and the builder's actions;
- `buildFunc_ok`: a built function's name and blocks;
- `rtFuncs_names`: every runtime function's name and global labels are
  `scc_rt_` names.
-/
import Scc.Lower.InvProg

namespace Spike.Lib.RtLabs

open Scc Scc.IR Scc.Lower Scc.Lower.Inv

/-! ## The labels -/

/-- **The global labels an instruction places**: a system call's trap label
and a site's label (the emitter places the rest, under its own names). -/
def instLabs : Inst → List Label
  | .syscall _ _ _ (some l) => [l]
  | .site l _ => [l]
  | _ => []

/-- **A global label of the runtime**: a stack site or an abort exit. -/
def RtLab (l : Label) : Prop :=
  l = Names.takeSite ∨ l = Names.releaseSite ∨ ∃ k, l = Names.abortExit k

/-- **A `scc_rt_` name.** -/
def RtName (l : String) : Prop := ∃ r, l = "scc_rt_" ++ r

theorem rtLab_take : RtLab Names.takeSite := Or.inl rfl
theorem rtLab_release : RtLab Names.releaseSite := Or.inr (Or.inl rfl)
theorem rtLab_exit (k : AbortKind) : RtLab (Names.abortExit k) := Or.inr (Or.inr ⟨k, rfl⟩)

theorem RtLab.rtName {l : Label} (h : RtLab l) : RtName l := by
  rcases h with rfl | rfl | ⟨k, rfl⟩
  · exact ⟨"take_site", rfl⟩
  · exact ⟨"release_site", rfl⟩
  · refine ⟨"abort_" ++ k.name ++ "_exit", ?_⟩
    show "scc_rt_abort_" ++ k.name ++ "_exit" = "scc_rt_" ++ ("abort_" ++ k.name ++ "_exit")
    rw [← String.append_assoc, ← String.append_assoc]
    rfl

/-- An instruction's labels are the runtime's. -/
def InstOk (i : Inst) : Prop := ∀ l ∈ instLabs i, RtLab l

theorem instOk_of_nil {i : Inst} (h : instLabs i = []) : InstOk i := by
  intro l hl; rw [h] at hl; simp at hl

theorem instOk_site (args : List Operand) (l : Label) (h : RtLab l) : InstOk (.site l args) := by
  intro l' hl'
  simp only [instLabs, List.mem_singleton] at hl'
  subst hl'; exact h

theorem instOk_syscall_none (d : Reg) (nr : Sys) (args : List Operand) : InstOk (.syscall d nr args none) :=
  instOk_of_nil rfl

theorem instOk_syscall_some (d : Reg) (nr : Sys) (args : List Operand) {l : Label} (h : RtLab l) :
    InstOk (.syscall d nr args (some l)) := by
  intro l' hl'
  simp only [instLabs, List.mem_singleton] at hl'
  subst hl'; exact h

/-! ## The builder's invariant -/

/-- **The builder's state is good**: every instruction of its finished
blocks and of its open block is `InstOk`. -/
def SGood (s : BState) : Prop :=
  (∀ b ∈ s.blocks.toList, ∀ i ∈ b.insts, InstOk i) ∧
  ∀ l is, s.cur = some (l, is) → ∀ i ∈ is.toList, InstOk i

/-- **An action preserves the invariant.** -/
structure Pres {α : Type} (x : B α) : Prop where
  out : ∀ (s : BState) (a : α) (s' : BState), x s = .ok (a, s') → SGood s → SGood s'

/-- A successful bind of the builder, taken apart. -/
theorem bind_inv {α β : Type} {x : B α} {f : α → B β} {s s'' : BState} {b : β}
    (h : (x >>= f) s = .ok (b, s'')) : ∃ a s', x s = .ok (a, s') ∧ f a s' = .ok (b, s'') := by
  simp only [bind, StateT.bind] at h
  cases hx : x s with
  | error e => rw [hx] at h; cases h
  | ok r =>
    rw [hx] at h
    exact ⟨r.1, r.2, rfl, h⟩

namespace Pres

theorem pure' {α : Type} (a : α) : Pres (pure a : B α) := by
  refine ⟨fun s b s' h hs => ?_⟩
  cases h
  exact hs

theorem bind' {α β : Type} {x : B α} {f : α → B β} (hx : Pres x) (hf : ∀ a, Pres (f a)) : Pres (x >>= f) := by
  refine ⟨fun s b s'' h hs => ?_⟩
  obtain ⟨a, s', h1, h2⟩ := bind_inv h
  exact (hf a).out s' b s'' h2 (hx.out s a s' h1 hs)

theorem throw' {α : Type} (e : String) : Pres (throw e : B α) := by
  refine ⟨fun s a s' h => ?_⟩
  cases h

theorem get' : Pres (get : B BState) := by
  refine ⟨fun s a s' h hs => ?_⟩
  cases h
  exact hs

theorem ite' {α : Type} {c : Prop} [Decidable c] {x y : B α} (hx : Pres x) (hy : Pres y) :
    Pres (if c then x else y) := by
  split
  · exact hx
  · exact hy

theorem forIn' {β σ : Type} (f : β → σ → B (ForInStep σ)) (hf : ∀ b st, Pres (f b st)) :
    ∀ (l : List β) (init : σ), Pres (forIn l init f)
  | [], init => by simpa using pure' init
  | b :: l, init => by
    rw [List.forIn_cons]
    refine bind' (hf b init) fun r => ?_
    cases r with
    | done st => exact pure' st
    | yield st => exact forIn' f hf l st

theorem mapM' {β γ : Type} (f : β → B γ) (hf : ∀ b, Pres (f b)) : ∀ l : List β, Pres (l.mapM f)
  | [] => by simpa using pure' ([] : List γ)
  | b :: l => by
    rw [List.mapM_cons]
    exact bind' (hf b) fun c => bind' (mapM' f hf l) fun cs => pure' _

/-- An action leaving the blocks and the open block alone. -/
theorem of_keep {α : Type} {x : B α}
    (h : ∀ s a s', x s = .ok (a, s') → s'.blocks = s.blocks ∧ s'.cur = s.cur) : Pres x :=
  ⟨fun s a s' e hs => by
    obtain ⟨h1, h2⟩ := h s a s' e
    exact ⟨by rw [h1]; exact hs.1, by rw [h2]; exact hs.2⟩⟩

end Pres

/-! ## The builder's actions -/

theorem modify_run (f : BState → BState) (s : BState) : (modify f : B Unit) s = .ok ((), f s) := rfl

theorem fresh_pres (hint : String) : Pres (fresh hint) :=
  Pres.of_keep fun s a s' h => by
    simp only [fresh, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, pure,
      StateT.pure, Except.pure, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨rfl, rfl⟩

theorem freshLabel_pres (hint : String) : Pres (freshLabel hint) :=
  Pres.of_keep fun s a s' h => by
    simp only [freshLabel, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, pure,
      StateT.pure, Except.pure, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨rfl, rfl⟩

theorem markAt_pres (n : Node) (p : Point) : Pres (markAt n p) :=
  Pres.of_keep fun s a s' h => by
    rw [markAt, modify_run] at h
    cases h
    exact ⟨rfl, rfl⟩

theorem setHere_pres (p : Point) : Pres (setHere p) :=
  Pres.of_keep fun s a s' h => by
    rw [setHere, modify_run] at h
    cases h
    exact ⟨rfl, rfl⟩

theorem markHeap_pres (r : Reg) : Pres (markHeap r) :=
  Pres.of_keep fun s a s' h => by
    rw [markHeap, modify_run] at h
    cases h
    split <;> exact ⟨rfl, rfl⟩

theorem markScalar_pres (r : Reg) : Pres (markScalar r) :=
  Pres.of_keep fun s a s' h => by
    rw [markScalar, modify_run] at h
    cases h
    split <;> exact ⟨rfl, rfl⟩

theorem markBits_pres (ds : List Reg) (bs : List Bool) : Pres (Runtime.markBits ds bs) :=
  Pres.of_keep fun s a s' h => by
    rw [Runtime.markBits, modify_run] at h
    cases h
    exact ⟨rfl, rfl⟩

/-- `emit`'s first step: the instruction appended to the open block. -/
theorem emit_modify_pres (i : Inst) (hi : InstOk i) :
    Pres (modify fun s : BState => match s.cur with
      | some (l, is) => { s with cur := some (l, is.push i) }
      | none => { s with cur := some (s!"dead{s.next}", #[i]), next := s.next + 1 }) := by
  refine ⟨fun s a s' h hs => ?_⟩
  rw [modify_run] at h
  cases h
  refine ⟨fun b hb => ?_, fun l is hc => ?_⟩
  · split at hb <;> exact hs.1 b hb
  · split at hc
    · rename_i l0 is0 h0
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨hl, his⟩ := hc
      subst hl
      subst his
      intro j hj
      rw [Array.toList_push, List.mem_append, List.mem_singleton] at hj
      rcases hj with hj | rfl
      · exact hs.2 l0 is0 h0 j hj
      · exact hi
    · simp only [Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨-, his⟩ := hc
      subst his
      intro j hj
      simp only [List.mem_singleton] at hj
      subst hj
      exact hi

/-- `emit` of an instruction with the runtime's labels. -/
theorem emit_pres (i : Inst) (hi : InstOk i) : Pres (emit i) := by
  unfold emit
  refine Pres.bind' (emit_modify_pres i hi) fun _ => ?_
  split
  · refine Pres.bind' Pres.get' fun s => ?_
    split
    · exact markAt_pres _ _
    · exact Pres.pure' _
  · exact Pres.pure' _

theorem terminate_pres (t : Term) : Pres (terminate t) := by
  refine ⟨fun s a s' h hs => ?_⟩
  rw [terminate, modify_run] at h
  cases h
  split
  · next l is hc =>
    refine ⟨fun b hb => ?_, fun l' is' hc' => ?_⟩
    · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hb
      rcases hb with hb | rfl
      · exact hs.1 b hb
      · exact hs.2 l is hc
    · cases hc'
  · exact hs

/-- `startBlock`'s opening of the block. -/
theorem open_pres (l : Label) : Pres (modify fun s : BState => { s with cur := some (l, #[]) }) := by
  refine ⟨fun s a s' h hs => ?_⟩
  rw [modify_run] at h
  cases h
  refine ⟨hs.1, fun l' is' hc => ?_⟩
  simp only [Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨-, rfl⟩ := hc
  simp

theorem startBlock_pres (l : Label) : Pres (startBlock l) := by
  unfold startBlock
  dsimp only
  refine Pres.bind' Pres.get' fun s => ?_
  split
  · refine Pres.bind' (terminate_pres _) fun _ => Pres.bind' (open_pres l) fun _ => Pres.bind' Pres.get' fun s => ?_
    split
    · exact markAt_pres _ _
    · exact Pres.pure' _
  · refine Pres.bind' (open_pres l) fun _ => Pres.bind' Pres.get' fun s => ?_
    split
    · exact markAt_pres _ _
    · exact Pres.pure' _

/-! ## The runtime's helpers -/

theorem binR_pres (op : BinOp) (a b : Operand) (hint : String) : Pres (binR op a b hint) := by
  unfold binR
  exact Pres.bind' (fresh_pres _) fun d => Pres.bind' (emit_pres _ (instOk_of_nil rfl)) fun _ => Pres.pure' _

theorem inReg_pres (o : Operand) (hint : String) : Pres (inReg o hint) := by
  unfold inReg
  split
  · exact Pres.pure' _
  · exact Pres.bind' (fresh_pres _) fun d => Pres.bind' (emit_pres _ (instOk_of_nil rfl)) fun _ => Pres.pure' _

theorem needSome_pres {α : Type} (o : Option α) (msg : String) : Pres (needSome o msg) := by
  unfold needSome
  split
  · exact Pres.pure' _
  · exact Pres.throw' _

theorem header_pres (o : ObjLayout) (k : Obj.HeaderKind) (n m : Nat) : Pres (header o k n m) := by
  unfold header
  split
  · exact Pres.pure' _
  · exact Pres.throw' _

/-- One step of a `Pres` proof of a runtime action. -/
macro "pres_step" : tactic => `(tactic| first
  | (with_reducible exact Pres.pure' _) | (with_reducible exact Pres.throw' _) | (with_reducible exact Pres.get')
  | (with_reducible exact fresh_pres _) | (with_reducible exact freshLabel_pres _)
  | (with_reducible exact markAt_pres _ _) | (with_reducible exact setHere_pres _)
  | (with_reducible exact markHeap_pres _) | (with_reducible exact markScalar_pres _)
  | (with_reducible exact markBits_pres _ _)
  | (with_reducible exact terminate_pres _) | (with_reducible exact startBlock_pres _)
  | (with_reducible exact binR_pres _ _ _ _) | (with_reducible exact inReg_pres _ _)
  | (with_reducible exact needSome_pres _ _) | (with_reducible exact header_pres _ _ _ _)
  | (with_reducible exact emit_pres _ (instOk_of_nil rfl))
  | (with_reducible exact emit_pres _ (instOk_site _ _ rtLab_take))
  | (with_reducible exact emit_pres _ (instOk_site _ _ rtLab_release))
  | (with_reducible exact emit_pres _ (instOk_syscall_some _ _ _ (rtLab_exit _)))
  | (with_reducible apply Pres.bind') | (with_reducible apply Pres.forIn') | (with_reducible apply Pres.mapM')
  | (with_reducible apply Pres.ite')
  | (intro _) | (split))

/-- `Pres` of a runtime action, step by step. -/
macro "pres_tac" : tactic => `(tactic| repeat pres_step)

theorem abortWith_pres (k : AbortKind) : Pres (Runtime.abortWith k) := by
  unfold Runtime.abortWith; pres_tac

theorem tcbLayout_pres (o : ObjLayout) (T : CoreLang.Ty) : Pres (tcbLayout o T) := by
  unfold tcbLayout; pres_tac

theorem markWords_pres (t : CoreLang.Ty) (ws : List Operand) : Pres (markWords t ws) := by
  unfold markWords; pres_tac

theorem classOf_pres (lay : Layout) (size : Operand) : Pres (Runtime.classOf lay size) := by
  unfold Runtime.classOf; pres_tac

theorem lockPool_pres : Pres Runtime.lockPool := by
  unfold Runtime.lockPool; pres_tac

theorem unlockPool_pres : Pres Runtime.unlockPool := by
  unfold Runtime.unlockPool; pres_tac

theorem finish_pres (o : ObjLayout) (s m : Operand) : Pres (Runtime.allocF.finish o s m) := by
  unfold Runtime.allocF.finish; pres_tac

/-- One step of a `Pres` proof of a runtime function's body. -/
macro "pres_fn_step" : tactic => `(tactic| first
  | (with_reducible exact abortWith_pres _) | (with_reducible exact tcbLayout_pres _ _)
  | (with_reducible exact markWords_pres _ _) | (with_reducible exact classOf_pres _ _)
  | (with_reducible exact lockPool_pres) | (with_reducible exact unlockPool_pres)
  | (with_reducible exact finish_pres _ _ _)
  | pres_step)

macro "pres_fn_tac" : tactic => `(tactic| repeat pres_fn_step)

/-! ## A built function -/

/-- The blocks of a finished builder state. -/
def finalBlocks (s : BState) : List Block :=
  (match s.cur with
    | some (l, is) => s.blocks.push ⟨l, is.toList, .unreachable⟩
    | none => s.blocks).toList

/-- **A built function**: its body ran, it is named as asked and its blocks
are the state's. -/
theorem buildFunc_ok {name : Sym} {params : List Reg} {cs : Bool} {body : B Unit} {f : Func}
    (h : buildFunc name params cs body = .ok f) :
    ∃ s, body {} = .ok ((), s) ∧ f.name = name ∧ f.blocks = finalBlocks s := by
  unfold buildFunc buildFuncMarks at h
  simp only [StateT.run, Functor.map, Except.map, bind, Except.bind] at h
  cases hb : body {} with
  | error e => rw [hb] at h; cases h
  | ok r =>
    obtain ⟨⟨⟩, s⟩ := r
    rw [hb] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨s, rfl, rfl, rfl⟩

/-- The empty state is good. -/
theorem sGood_empty : SGood {} := by
  refine ⟨fun b hb => by simp at hb, fun l is hc => ?_⟩
  simp only [Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨-, rfl⟩ := hc
  simp

/-- **Every instruction of a built function has the runtime's labels** when
its body preserves the invariant. -/
theorem instOk_of_buildFunc {name : Sym} {params : List Reg} {cs : Bool} {body : B Unit} {f : Func}
    (h : buildFunc name params cs body = .ok f) (hp : Pres body) :
    f.name = name ∧ ∀ b ∈ f.blocks, ∀ i ∈ b.insts, InstOk i := by
  obtain ⟨s, hs, hn, hb⟩ := buildFunc_ok h
  have hg := hp.out _ _ _ hs sGood_empty
  refine ⟨hn, fun b hb' => ?_⟩
  rw [hb] at hb'
  unfold finalBlocks at hb'
  split at hb'
  · next l is hc =>
    rw [Array.toList_push, List.mem_append, List.mem_singleton] at hb'
    rcases hb' with hb' | rfl
    · exact hg.1 b hb'
    · exact hg.2 l is hc
  · exact hg.1 b hb'

/-! ## The runtime's functions -/

/-- A function's name and global labels are `scc_rt_` names. -/
def FnRt (f : Func) : Prop :=
  RtName f.name ∧ ∀ b ∈ f.blocks, ∀ i ∈ b.insts, ∀ l ∈ instLabs i, RtName l

theorem fnRt_of {name : Sym} {params : List Reg} {cs : Bool} {body : B Unit} {f : Func}
    (h : buildFunc name params cs body = .ok f) (hp : Pres body) (hn : RtName name) : FnRt f := by
  obtain ⟨hname, hi⟩ := instOk_of_buildFunc h hp
  exact ⟨hname ▸ hn, fun b hb i hi' l hl => (hi b hb i hi' l hl).rtName⟩

theorem startF_rt {lay : Layout} {f : Func} (h : Runtime.startF lay = .ok f) : FnRt f :=
  fnRt_of h (by (try dsimp only); pres_fn_tac) ⟨"start", rfl⟩

theorem mainThreadF_rt {e : Frontend.Entry} {sw : Nat} {m : List Bool} {f : Func}
    (h : Runtime.mainThreadF e sw m = .ok f) : FnRt f :=
  fnRt_of h (by (try dsimp only); pres_fn_tac) ⟨"main", rfl⟩

/-- A successful `Except` bind from its parts. -/
theorem ok_bind' {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} (h : (x >>= f) = .ok b) :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem allocF_rt {lay : Layout} {name region cursor : Sym} {bytes : Nat} {kind : AbortKind} {counter : Bool}
    {f : Func} (h : Runtime.allocF lay name region cursor bytes kind counter = .ok f) (hn : RtName name) :
    FnRt f := by
  unfold Runtime.allocF at h
  dsimp only at h
  split at h
  · obtain ⟨_, h', -⟩ := ok_bind' h
    cases h'
  · exact fnRt_of h (by (try dsimp only); pres_fn_tac) hn

theorem threadReserveF_rt {lay : Layout} {f : Func} (h : Runtime.threadReserveF lay = .ok f) : FnRt f :=
  fnRt_of h (by (try dsimp only); pres_fn_tac) ⟨"thread_reserve", rfl⟩

theorem threadInitF_rt {lay : Layout} {f : Func} (h : Runtime.threadInitF lay = .ok f) : FnRt f :=
  fnRt_of h (by (try dsimp only); pres_fn_tac) ⟨"thread_init", rfl⟩

theorem stackTakeF_rt {lay : Layout} {f : Func} (h : Runtime.stackTakeF lay = .ok f) : FnRt f :=
  fnRt_of h (by (try dsimp only); pres_fn_tac) ⟨"stack_take", rfl⟩

theorem stackReleaseF_rt {lay : Layout} {f : Func} (h : Runtime.stackReleaseF lay = .ok f) : FnRt f :=
  fnRt_of h (by (try dsimp only); pres_fn_tac) ⟨"stack_release", rfl⟩

theorem growF_rt {lay : Layout} {f : Func} (h : Runtime.growF lay = .ok f) : FnRt f :=
  fnRt_of h (by (try dsimp only); pres_fn_tac) ⟨"grow", rfl⟩

theorem printF_rt {fence : Bool} {f : Func} (h : Runtime.printF fence = .ok f) : FnRt f :=
  fnRt_of h (by (try dsimp only); pres_fn_tac) ⟨"print", rfl⟩

theorem parkF_rt {f : Func} (h : Runtime.parkF = .ok f) : FnRt f :=
  fnRt_of h (by (try dsimp only); pres_fn_tac) ⟨"park", rfl⟩

theorem unparkF_rt {f : Func} (h : Runtime.unparkF = .ok f) : FnRt f :=
  fnRt_of h (by (try dsimp only); pres_fn_tac) ⟨"unpark", rfl⟩

theorem abortF_rt {f : Func} (h : Runtime.abortF = .ok f) : FnRt f :=
  fnRt_of h (by (try dsimp only); pres_fn_tac) ⟨"abort", rfl⟩

theorem abortKindF_rt {k : AbortKind} {f : Func} (h : Runtime.abortKindF k = .ok f) : FnRt f :=
  fnRt_of h (by (try dsimp only); pres_fn_tac) ⟨"abort_" ++ k.name, by
    show "scc_rt_abort_" ++ k.name = "scc_rt_" ++ ("abort_" ++ k.name)
    rw [← String.append_assoc]
    rfl⟩

/-- A member of a successful `mapM id` comes from a successful element. -/
theorem mem_of_mapM_id {α : Type} : ∀ {l : List (Except String α)} {rs : List α}, l.mapM id = .ok rs →
    ∀ r ∈ rs, ∃ x ∈ l, x = .ok r
  | [], rs, h, r, hr => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp at hr
  | x :: l, rs, h, r, hr => by
    rw [List.mapM_cons] at h
    cases hx : x with
    | error e => rw [hx] at h; cases h
    | ok a =>
      rw [hx] at h
      cases hl : l.mapM id with
      | error e => simp [hl, bind, Except.bind, id] at h
      | ok as =>
        simp only [hl, id, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        rcases List.mem_cons.mp hr with rfl | hr
        · exact ⟨_, List.mem_cons_self .., rfl⟩
        · obtain ⟨y, hy, hy'⟩ := mem_of_mapM_id hl r hr
          exact ⟨y, List.mem_cons_of_mem _ hy, hy'⟩

/-- **Every runtime function's name and global labels are `scc_rt_`
names.** -/
theorem rtFuncs_names {arch : Arch} {lay : Layout} {e : Frontend.Entry} {sw : Nat} {m : List Bool}
    {rt : List Func} (h : rtFuncs arch lay e sw m = .ok rt) : ∀ f ∈ rt, FnRt f := by
  intro f hf
  unfold rtFuncs at h
  obtain ⟨x, hx, hxf⟩ := mem_of_mapM_id h f hf
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, List.mem_map] at hx
  -- `rw`, not `subst`: substituting the function's body is costly
  rcases hx with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) | ⟨k, -, h1⟩
  all_goals first | rw [h1] at hxf | rw [← h1] at hxf
  · exact startF_rt hxf
  · exact mainThreadF_rt hxf
  · exact allocF_rt hxf ⟨"alloc", rfl⟩
  · exact allocF_rt hxf ⟨"alloc_tcb", rfl⟩
  · exact threadReserveF_rt hxf
  · exact threadInitF_rt hxf
  · exact stackTakeF_rt hxf
  · exact stackReleaseF_rt hxf
  · exact growF_rt hxf
  · exact printF_rt hxf
  · exact parkF_rt hxf
  · exact unparkF_rt hxf
  · exact abortF_rt hxf
  · exact abortKindF_rt hxf

end Spike.Lib.RtLabs

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.RtLabs.rtFuncs_names' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.RtLabs.rtFuncs_names
