/-
Wide promises: a thread whose every write is one word wide cannot certify a
promise of a message of another width.

Kraken fulfils an outstanding promise `p` only by a write of exactly the
promised message (`Lower.mem_writeSuccs_iff`: `mem.get? p = some ⟨l, v, tid⟩`
for the write's location `l`). If every store and RMW of the code the
thread runs (`cexec`) is to an 8-byte location (`Wide8Tree`), a promise
of a message of another width stays outstanding along every solo run, and
the thread is not certifiable. With it, a certified promise step keeps
every target message one word wide (`MemRel.Narrow`), which the read side
of the memory relation needs (`Scc/Sem/Rows1.lean`, `Inv1.promise_cert`).

- `Wide8Tree`, `Wide8Code`: every write event of a tree, or of every tree
  `cexec` yields, is to an 8-byte location.
- `Ctx.HasWide`: `p` outstanding with a message of another width.
- `runTree_hasWide`, `stepOneWith_hasWide`, `threadNPC_hasWide`: the
  property survives a context run, an instruction and a solo run.
- `not_certOkC_of_wide`, `certOkC_prom_narrow`: a certifiable thread's
  outstanding promises are of one-word messages.
- `Wide8CodeOn P`, `TreeLeaf`, `WideInv`: the same on the states satisfying
  an invariant `P` that every leaf of every tree `cexec` yields from a
  `P` state keeps (`certOkC_prom_narrow_on`); a certification semantics
  writes words only on the code the compiler emits, not on every state.
- `WriteTree G`, `WriteCode G`, `WriteCodeOn G P`, `Ctx.HasBad G`,
  `certOkC_prom_good`, `certOkC_prom_good_on`: the same for any predicate
  `G` of a write's location and value; `Fit64`, `Fit64Tree`, `Fit64Code`,
  `Fit64CodeOn`: with `G` "the value fits in 64 bits"
  (`Scc/Sem/Fits.lean`).
-/
import Scc.Sem.Ext
import Scc.Sem.MemRel
import Kraken.Promising.AcqFloor
import Kraken.Promising.Lower.Events

namespace Scc.Sem

open Kraken Kraken.Promising

/-- **Every write event of the tree is to an 8-byte location** (stores and
RMWs; loads and fences are unconstrained). -/
def Wide8Tree {σ : Type} : EvTree σ → Prop
  | .done _ => True
  | .fault _ => True
  | .choose _ k => ∀ i, Wide8Tree (k i)
  | .load _ _ _ ret => ∀ v, Wide8Tree (ret v)
  | .store _ _ l _ ret => l.bytes = 8 ∧ ∀ b, Wide8Tree (ret b)
  | .rmw _ _ l _ ret => l.bytes = 8 ∧ ∀ v, Wide8Tree (ret v)
  | .fence _ ret => ∀ u, Wide8Tree (ret u)

/-- **Every tree the code yields writes words only.** -/
def Wide8Code {I : ISA} (cexec : I.State → Option (EvTree I.State)) : Prop :=
  ∀ st tree, cexec st = some tree → Wide8Tree tree

/-- Promise `p` is outstanding in `c`, of a message whose location is not
8 bytes wide. -/
def Ctx.HasWide (p : Time) (c : Ctx) : Prop :=
  p ∈ c.prom ∧ ∃ w, c.mem.get? p = some w ∧ w.loc.bytes ≠ 8

section Rules

variable (A : Arch) (tid : Nat)

theorem Ctx.HasWide.of_eq {p : Time} {c c' : Ctx} (hm : c'.mem = c.mem) (hp : c'.prom = c.prom)
    (h : Ctx.HasWide p c) : Ctx.HasWide p c' := by
  rw [Ctx.HasWide, hm, hp]; exact h

theorem fence_hasWide {p : Time} {c : Ctx} (k : FenceKind) (h : Ctx.HasWide p c) :
    Ctx.HasWide p (fenceStep c k) :=
  h.of_eq (fenceStep_mem c k) (fenceStep_fields c k).2.2.2.2.1

theorem fenceOpt_hasWide {p : Time} {c : Ctx} (b : Bool) (h : Ctx.HasWide p c) :
    Ctx.HasWide p (if b then fenceStep c .sy else c) := by
  cases b
  · exact h
  · exact fence_hasWide .sy h

theorem read_hasWide {iv : InstrViews} {p : Time} {c : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool}
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl l noRet) (h : Ctx.HasWide p c) :
    Ctx.HasWide p x.2.2 := by
  obtain ⟨-, -, -, he⟩ := readSuccs_shape A iv hx
  exact h.of_eq (by rw [he]) (readSuccs_prom A iv hx)

/-- **A write to an 8-byte location keeps a wide promise outstanding**: a
fulfilment of `p` would need `p`'s message at the write's location. -/
theorem write_hasWide {xr : View} {p : Time} {c c' : Ctx} {iv' : InstrViews} {k : StoreKind} {xcl : Bool}
    {l : Loc} {v : Val} {tr : Option Time} {extra : View} (hl : l.bytes = 8)
    (h : c' ∈ writeSuccs A tid iv' c k xcl l v tr extra xr) (hw : Ctx.HasWide p c) : Ctx.HasWide p c' := by
  obtain ⟨hp, w, hg, hb⟩ := hw
  rcases (Lower.mem_writeSuccs_iff A tid iv').mp h with ⟨t, -, hgt, -, rfl⟩ | ⟨-, rfl⟩
  · have hne : p ≠ t := by
      rintro rfl; rw [hg] at hgt; cases hgt; exact hb hl
    exact ⟨(List.mem_erase_of_ne hne).mpr hp, w, hg, hb⟩
  · have hle := Scc.Sem.Memory.le_last_of_get? hg
    have hle' : @LE.le Nat instLENat p c.mem.last := hle
    have hne : p ≠ c.mem.last + 1 := fun he => by rw [he] at hle'; exact Nat.not_succ_le_self _ hle'
    refine ⟨?_, w, ?_, hb⟩
    · show p ∈ (c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1)
      exact (List.mem_erase_of_ne hne).mpr (List.mem_append_left _ hp)
    · show (c.mem.append _).1.get? p = some w
      rw [Scc.Sem.Memory.get?_append_le hle]; exact hg

theorem rmwPost_hasWide {p : Time} {c : Ctx} (k : RmwKind) (noRet : Bool) (l : Loc) (h : Ctx.HasWide p c) :
    Ctx.HasWide p (rmwPost A k noRet l c) := by
  refine h.of_eq ?_ ?_ <;> unfold rmwPost <;> split <;> rfl

/-- **A run of a word-writing tree keeps a wide promise outstanding.** -/
theorem runTree_hasWide (iv : InstrViews) {σ : Type} (tree : EvTree σ) (hW : Wide8Tree tree) :
    ∀ (c : Ctx) (s : σ) (c' : Ctx), .ok (s, c') ∈ runTree A tid iv c tree →
      ∀ p, Ctx.HasWide p c → Ctx.HasWide p c' := by
  induction tree with
  | done s =>
    intro c s' c' h p hp
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact hp
  | fault m => intro c s c' h; simp [runTree] at h
  | choose n k ih =>
    intro c s c' h p hp
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, -, h⟩ := h
    exact ih i (hW i) c s c' h p hp
  | load k xcl l ret ih =>
    intro c s c' h p hp
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨x, hx, h⟩ := h
    exact ih x.2.1 (hW x.2.1) x.2.2 s c' h p (read_hasWide A hx hp)
  | store k xcl l v ret ih =>
    intro c s c' h p hp
    obtain ⟨hl, hW⟩ := hW
    simp only [runTree, List.mem_append] at h
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨-, c0, hc0, h⟩ := h
      exact ih true (hW true) c0 s c' h p (write_hasWide A tid hl hc0 hp)
    · rw [List.mem_ite_nil_right] at h
      exact ih false (hW false) _ s c' h.2 p (hp.of_eq rfl rfl)
  | fence k ret ih =>
    intro c s c' h p hp
    simp only [runTree] at h
    exact ih () (hW ()) _ s c' h p (fence_hasWide k hp)
  | rmw k noRet l op ret ih =>
    intro c s c' h p hp
    obtain ⟨hl, hW⟩ := hW
    simp only [runTree] at h
    have h1 := fenceOpt_hasWide A.rmwFence hp
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at h h1
    rw [List.mem_flatMap] at h
    obtain ⟨⟨tr, old, c2⟩, h2, h⟩ := h
    have h12 := read_hasWide A h2 h1
    simp only at h
    split at h
    · exact ih old (hW old) _ s c' h p (fenceOpt_hasWide A.rmwFence h12)
    · rw [List.mem_flatMap] at h
      obtain ⟨c3, hc3, h⟩ := h
      change .ok (s, c') ∈ runTree A tid iv
        (if A.rmwFence then fenceStep (rmwPost A k noRet l c3) .sy else rmwPost A k noRet l c3) (ret old) at h
      exact ih old (hW old) _ s c' h p
        (fenceOpt_hasWide A.rmwFence (rmwPost_hasWide A k noRet l (write_hasWide A tid hl hc3 h12)))

end Rules

/-- **One instruction of word-writing code keeps a wide promise
outstanding.** -/
theorem stepOneWith_hasWide {I : ISA} (A : Arch) {cs : CertSem I}
    (hW : Wide8Code cs.exec) {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Kraken.Promising.Outcome I))}
    (hstep : cs.step A t tid mem = some outs) {o : Kraken.Promising.Outcome I}
    (ho : .ok o ∈ outs) {p : Time} (h : p ∈ t.prom ∧ ∃ w, mem.get? p = some w ∧ w.loc.bytes ≠ 8) :
    p ∈ o.thread.prom ∧ ∃ w, o.mem.get? p = some w ∧ w.loc.bytes ≠ 8 := by
  unfold CertSem.step stepOneWithD at hstep
  cases hex : cs.exec t.st with
  | none => rw [hex] at hstep; cases hstep
  | some tree =>
    rw [hex] at hstep
    have hstep' : _ = outs := Option.some.inj hstep
    subst hstep'
    rw [List.mem_flatMap] at ho
    obtain ⟨r, hr, ho⟩ := ho
    cases r with
    | error m => simp at ho
    | ok q =>
      obtain ⟨st, c'⟩ := q
      simp only [List.mem_map, Except.ok.injEq] at ho
      obtain ⟨th, hth, rfl⟩ := ho
      have hd := runTree_hasWide A tid _ tree (hW _ _ hex) _ st c' hr p h
      exact ⟨(finishInstr_relKey hth).1 ▸ hd.1, hd.2⟩

/-- **A solo run of word-writing code keeps a wide promise outstanding.** -/
theorem threadNPC_hasWide {I : ISA} (A : Arch) {cs : CertSem I}
    (hW : Wide8Code cs.exec) {tid : Nat} {x y : Thread I × Memory} (hr : ThreadNPC A cs tid x y) {p : Time}
    (h : p ∈ x.1.prom ∧ ∃ w, x.2.get? p = some w ∧ w.loc.bytes ≠ 8) :
    p ∈ y.1.prom ∧ ∃ w, y.2.get? p = some w ∧ w.loc.bytes ≠ 8 := by
  induction hr with
  | refl => exact h
  | step hs _ ih =>
    obtain ⟨outs, o, hso, ho, rfl⟩ := hs
    exact ih (stepOneWith_hasWide A hW hso ho h)

/-- **A thread of word-writing code holding a promise of another width is
not certifiable.** -/
theorem not_certOkC_of_wide {I : ISA} (A : Arch) {cs : CertSem I}
    (hW : Wide8Code cs.exec) (tid : Nat) {t : Thread I} {mem : Memory} {p : Time} (hp : p ∈ t.prom)
    {w : Msg} (hg : mem.get? p = some w) (hb : w.loc.bytes ≠ 8) : ¬ CertOkC A cs tid t mem := by
  rintro ⟨t', mem', hr, he⟩
  have := (threadNPC_hasWide A hW hr (x := (t, mem)) ⟨hp, w, hg, hb⟩).1
  rw [he] at this; cases this

/-- **Every outstanding promise of a certifiable thread of word-writing
code is of a one-word message.** -/
theorem certOkC_prom_narrow {I : ISA} {A : Arch} {cs : CertSem I}
    (hW : Wide8Code cs.exec) {tid : Nat} {t : Thread I} {mem : Memory} (hc : CertOkC A cs tid t mem)
    {p : Time} (hp : p ∈ t.prom) {w : Msg} (hg : mem.get? p = some w) : w.loc.bytes = 8 :=
  Classical.byContradiction fun hb => not_certOkC_of_wide A hW tid hp hg hb hc

/-! ## Word-writing code on an invariant

A certification semantics writes words only from the states the emitted
program can reach (declarations and code wide), not from every state. The
statements below take an invariant `P` of thread states, kept by every
leaf of the tree `cexec` yields from a `P` state (`WideInv`). -/

/-- `s` is the state at some leaf of the tree, along any path (any choice,
read value and store outcome). -/
def TreeLeaf {σ : Type} : EvTree σ → σ → Prop
  | .done s, s' => s' = s
  | .fault _, _ => False
  | .choose _ k, s => ∃ i, TreeLeaf (k i) s
  | .load _ _ _ ret, s => ∃ v, TreeLeaf (ret v) s
  | .store _ _ _ _ ret, s => ∃ b, TreeLeaf (ret b) s
  | .rmw _ _ _ _ ret, s => ∃ v, TreeLeaf (ret v) s
  | .fence _ ret, s => ∃ u, TreeLeaf (ret u) s

/-- **Every tree `cexec` yields from a `P` state writes words only.** -/
def Wide8CodeOn {I : ISA} (P : I.State → Prop) (cexec : I.State → Option (EvTree I.State)) : Prop :=
  ∀ st tree, P st → cexec st = some tree → Wide8Tree tree

/-- **`P` is kept by one instruction of `cexec`**: every leaf of the tree
yielded from a `P` state is a `P` state. -/
def WideInv {I : ISA} (P : I.State → Prop) (cexec : I.State → Option (EvTree I.State)) : Prop :=
  ∀ st tree s, P st → cexec st = some tree → TreeLeaf tree s → P s

theorem Wide8CodeOn.of_code {I : ISA} {cexec : I.State → Option (EvTree I.State)} (P : I.State → Prop)
    (h : Wide8Code cexec) : Wide8CodeOn P cexec :=
  fun st tree _ he => h st tree he

/-- A successful run of a tree ends at one of its leaves. -/
theorem runTree_treeLeaf (A : Arch) (tid : Nat) (iv : InstrViews) {σ : Type} (tree : EvTree σ) :
    ∀ (c : Ctx) (s : σ) (c' : Ctx), .ok (s, c') ∈ runTree A tid iv c tree → TreeLeaf tree s := by
  induction tree with
  | done s =>
    intro c s' c' h
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.1
  | fault m => intro c s c' h; simp [runTree] at h
  | choose n k ih =>
    intro c s c' h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, -, h⟩ := h
    exact ⟨i, ih i c s c' h⟩
  | load k xcl l ret ih =>
    intro c s c' h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨x, -, h⟩ := h
    exact ⟨x.2.1, ih x.2.1 _ s c' h⟩
  | store k xcl l v ret ih =>
    intro c s c' h
    simp only [runTree, List.mem_append] at h
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨-, c0, -, h⟩ := h
      exact ⟨true, ih true c0 s c' h⟩
    · rw [List.mem_ite_nil_right] at h
      exact ⟨false, ih false _ s c' h.2⟩
  | fence k ret ih =>
    intro c s c' h
    simp only [runTree] at h
    exact ⟨(), ih () _ s c' h⟩
  | rmw k noRet l op ret ih =>
    intro c s c' h
    simp only [runTree] at h
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at h
    rw [List.mem_flatMap] at h
    obtain ⟨⟨tr, old, c2⟩, -, h⟩ := h
    simp only at h
    split at h
    · exact ⟨old, ih old _ s c' h⟩
    · rw [List.mem_flatMap] at h
      obtain ⟨c3, -, h⟩ := h
      exact ⟨old, ih old _ s c' h⟩

/-- **One instruction under `cexec` keeps `P`** and, from a `P` state,
keeps a wide promise outstanding. -/
theorem stepOneWith_hasWide_on {I : ISA} (A : Arch) {P : I.State → Prop}
    {cs : CertSem I} (hW : Wide8CodeOn P cs.exec) (hP : WideInv P cs.exec)
    {t : Thread I} {tid : Nat} {mem : Memory} {outs : List (Except String (Kraken.Promising.Outcome I))}
    (hstep : cs.step A t tid mem = some outs) {o : Kraken.Promising.Outcome I}
    (ho : .ok o ∈ outs) (hst : P t.st) {p : Time}
    (h : p ∈ t.prom ∧ ∃ w, mem.get? p = some w ∧ w.loc.bytes ≠ 8) :
    P o.thread.st ∧ p ∈ o.thread.prom ∧ ∃ w, o.mem.get? p = some w ∧ w.loc.bytes ≠ 8 := by
  unfold CertSem.step stepOneWithD at hstep
  cases hex : cs.exec t.st with
  | none => rw [hex] at hstep; cases hstep
  | some tree =>
    rw [hex] at hstep
    have hstep' : _ = outs := Option.some.inj hstep
    subst hstep'
    rw [List.mem_flatMap] at ho
    obtain ⟨r, hr, ho⟩ := ho
    cases r with
    | error m => simp at ho
    | ok q =>
      obtain ⟨st, c'⟩ := q
      simp only [List.mem_map, Except.ok.injEq] at ho
      obtain ⟨th, hth, rfl⟩ := ho
      have hd := runTree_hasWide A tid _ tree (hW _ _ hst hex) _ st c' hr p h
      refine ⟨?_, (finishInstr_relKey hth).1 ▸ hd.1, hd.2⟩
      show P th.st
      rw [finishInstr_st hth]
      exact hP _ _ _ hst hex (runTree_treeLeaf A tid _ tree _ st c' hr)

/-- **A solo run from a `P` state keeps a wide promise outstanding.** -/
theorem threadNPC_hasWide_on {I : ISA} (A : Arch) {P : I.State → Prop}
    {cs : CertSem I} (hW : Wide8CodeOn P cs.exec) (hP : WideInv P cs.exec)
    {tid : Nat} {x y : Thread I × Memory} (hr : ThreadNPC A cs tid x y) (hst : P x.1.st) {p : Time}
    (h : p ∈ x.1.prom ∧ ∃ w, x.2.get? p = some w ∧ w.loc.bytes ≠ 8) :
    p ∈ y.1.prom ∧ ∃ w, y.2.get? p = some w ∧ w.loc.bytes ≠ 8 := by
  induction hr with
  | refl => exact h
  | step hs _ ih =>
    obtain ⟨outs, o, hso, ho, rfl⟩ := hs
    have h' := stepOneWith_hasWide_on A hW hP hso ho hst h
    exact ih h'.1 h'.2

/-- **A thread at a `P` state holding a promise of another width is not
certifiable.** -/
theorem not_certOkC_of_wide_on {I : ISA} (A : Arch) {P : I.State → Prop}
    {cs : CertSem I} (hW : Wide8CodeOn P cs.exec) (hP : WideInv P cs.exec)
    (tid : Nat) {t : Thread I} {mem : Memory} (hst : P t.st) {p : Time} (hp : p ∈ t.prom)
    {w : Msg} (hg : mem.get? p = some w) (hb : w.loc.bytes ≠ 8) : ¬ CertOkC A cs tid t mem := by
  rintro ⟨t', mem', hr, he⟩
  have := (threadNPC_hasWide_on A hW hP hr (x := (t, mem)) hst ⟨hp, w, hg, hb⟩).1
  rw [he] at this; cases this

/-- **Every outstanding promise of a certifiable thread at a `P` state is
of a one-word message.** -/
theorem certOkC_prom_narrow_on {I : ISA} {A : Arch} {P : I.State → Prop}
    {cs : CertSem I} (hW : Wide8CodeOn P cs.exec) (hP : WideInv P cs.exec)
    {tid : Nat} {t : Thread I} {mem : Memory} (hst : P t.st) (hc : CertOkC A cs tid t mem)
    {p : Time} (hp : p ∈ t.prom) {w : Msg} (hg : mem.get? p = some w) : w.loc.bytes = 8 :=
  Classical.byContradiction fun hb => not_certOkC_of_wide_on A hW hP tid hst hp hg hb hc

/-! ## Writes of a given shape

The statements above for any predicate `G` of a write's location and value
in place of "8 bytes wide": a tree whose every write satisfies `G`
(`WriteTree G`) cannot fulfil a promise of a message that does not
(`Ctx.HasBad G`), so a certifiable thread's outstanding promises satisfy `G`
(`certOkC_prom_good`, `certOkC_prom_good_on`). With `Fit64` (the value
fits in 64 bits) it is what keeps every target message a 64-bit value
(`Scc/Sem/Fits.lean`). -/

/-- **Every write event of the tree satisfies `G`**: a store's location and
value; for an RMW, the location with every value its operation may write. -/
def WriteTree (G : Loc → Val → Prop) {σ : Type} : EvTree σ → Prop
  | .done _ => True
  | .fault _ => True
  | .choose _ k => ∀ i, WriteTree G (k i)
  | .load _ _ _ ret => ∀ v, WriteTree G (ret v)
  | .store _ _ l v ret => G l v ∧ ∀ b, WriteTree G (ret b)
  | .rmw _ _ l op ret => (∀ old v, op old = some v → G l v) ∧ ∀ v, WriteTree G (ret v)
  | .fence _ ret => ∀ u, WriteTree G (ret u)

/-- **Every tree the code yields writes as `G` says.** -/
def WriteCode {I : ISA} (G : Loc → Val → Prop) (cexec : I.State → Option (EvTree I.State)) : Prop :=
  ∀ st tree, cexec st = some tree → WriteTree G tree

/-- **Every tree `cexec` yields from a `P` state writes as `G` says.** -/
def WriteCodeOn {I : ISA} (G : Loc → Val → Prop) (P : I.State → Prop)
    (cexec : I.State → Option (EvTree I.State)) : Prop :=
  ∀ st tree, P st → cexec st = some tree → WriteTree G tree

theorem WriteCodeOn.of_code {I : ISA} {G : Loc → Val → Prop} {cexec : I.State → Option (EvTree I.State)}
    (P : I.State → Prop) (h : WriteCode G cexec) : WriteCodeOn G P cexec :=
  fun st tree _ he => h st tree he

/-- A word-writing tree writes as "8 bytes wide" says (the converse fails
only for an RMW whose operation never writes). -/
theorem Wide8Tree.writeTree {σ : Type} : ∀ {t : EvTree σ}, Wide8Tree t → WriteTree (fun l _ => l.bytes = 8) t
  | .done _, _ => trivial
  | .fault _, _ => trivial
  | .choose _ _, h => fun i => (h i).writeTree
  | .load _ _ _ _, h => fun v => (h v).writeTree
  | .store _ _ _ _ _, h => ⟨h.1, fun b => (h.2 b).writeTree⟩
  | .rmw _ _ _ _ _, h => ⟨fun _ _ _ => h.1, fun v => (h.2 v).writeTree⟩
  | .fence _ _, h => fun u => (h u).writeTree

/-- Promise `p` is outstanding in `c`, of a message that does not satisfy
`G`. -/
def Ctx.HasBad (G : Loc → Val → Prop) (p : Time) (c : Ctx) : Prop :=
  p ∈ c.prom ∧ ∃ w, c.mem.get? p = some w ∧ ¬ G w.loc w.val

section RulesG

variable (A : Arch) (tid : Nat) {G : Loc → Val → Prop}

theorem Ctx.HasBad.of_eq {p : Time} {c c' : Ctx} (hm : c'.mem = c.mem) (hp : c'.prom = c.prom)
    (h : Ctx.HasBad G p c) : Ctx.HasBad G p c' := by
  rw [Ctx.HasBad, hm, hp]; exact h

theorem fence_hasBad {p : Time} {c : Ctx} (k : FenceKind) (h : Ctx.HasBad G p c) :
    Ctx.HasBad G p (fenceStep c k) :=
  h.of_eq (fenceStep_mem c k) (fenceStep_fields c k).2.2.2.2.1

theorem fenceOpt_hasBad {p : Time} {c : Ctx} (b : Bool) (h : Ctx.HasBad G p c) :
    Ctx.HasBad G p (if b then fenceStep c .sy else c) := by
  cases b
  · exact h
  · exact fence_hasBad .sy h

theorem read_hasBad {iv : InstrViews} {p : Time} {c : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool}
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl l noRet) (h : Ctx.HasBad G p c) :
    Ctx.HasBad G p x.2.2 := by
  obtain ⟨-, -, -, he⟩ := readSuccs_shape A iv hx
  exact h.of_eq (by rw [he]) (readSuccs_prom A iv hx)

/-- **A write satisfying `G` keeps a bad promise outstanding**: a fulfilment
of `p` would need `p`'s message to be the write's. -/
theorem write_hasBad {xr : View} {p : Time} {c c' : Ctx} {iv' : InstrViews} {k : StoreKind} {xcl : Bool}
    {l : Loc} {v : Val} {tr : Option Time} {extra : View} (hl : G l v)
    (h : c' ∈ writeSuccs A tid iv' c k xcl l v tr extra xr) (hw : Ctx.HasBad G p c) : Ctx.HasBad G p c' := by
  obtain ⟨hp, w, hg, hb⟩ := hw
  rcases (Lower.mem_writeSuccs_iff A tid iv').mp h with ⟨t, -, hgt, -, rfl⟩ | ⟨-, rfl⟩
  · have hne : p ≠ t := by
      rintro rfl; rw [hg] at hgt; cases hgt; exact hb hl
    exact ⟨(List.mem_erase_of_ne hne).mpr hp, w, hg, hb⟩
  · have hle := Scc.Sem.Memory.le_last_of_get? hg
    have hle' : @LE.le Nat instLENat p c.mem.last := hle
    have hne : p ≠ c.mem.last + 1 := fun he => by rw [he] at hle'; exact Nat.not_succ_le_self _ hle'
    refine ⟨?_, w, ?_, hb⟩
    · show p ∈ (c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1)
      exact (List.mem_erase_of_ne hne).mpr (List.mem_append_left _ hp)
    · show (c.mem.append _).1.get? p = some w
      rw [Scc.Sem.Memory.get?_append_le hle]; exact hg

theorem rmwPost_hasBad {p : Time} {c : Ctx} (k : RmwKind) (noRet : Bool) (l : Loc) (h : Ctx.HasBad G p c) :
    Ctx.HasBad G p (rmwPost A k noRet l c) := by
  refine h.of_eq ?_ ?_ <;> unfold rmwPost <;> split <;> rfl

/-- **A run of a tree whose writes satisfy `G` keeps a bad promise
outstanding.** -/
theorem runTree_hasBad (iv : InstrViews) {σ : Type} (tree : EvTree σ) (hW : WriteTree G tree) :
    ∀ (c : Ctx) (s : σ) (c' : Ctx), .ok (s, c') ∈ runTree A tid iv c tree →
      ∀ p, Ctx.HasBad G p c → Ctx.HasBad G p c' := by
  induction tree with
  | done s =>
    intro c s' c' h p hp
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact hp
  | fault m => intro c s c' h; simp [runTree] at h
  | choose n k ih =>
    intro c s c' h p hp
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, -, h⟩ := h
    exact ih i (hW i) c s c' h p hp
  | load k xcl l ret ih =>
    intro c s c' h p hp
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨x, hx, h⟩ := h
    exact ih x.2.1 (hW x.2.1) x.2.2 s c' h p (read_hasBad A hx hp)
  | store k xcl l v ret ih =>
    intro c s c' h p hp
    obtain ⟨hl, hW⟩ := hW
    simp only [runTree, List.mem_append] at h
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨-, c0, hc0, h⟩ := h
      exact ih true (hW true) c0 s c' h p (write_hasBad A tid hl hc0 hp)
    · rw [List.mem_ite_nil_right] at h
      exact ih false (hW false) _ s c' h.2 p (hp.of_eq rfl rfl)
  | fence k ret ih =>
    intro c s c' h p hp
    simp only [runTree] at h
    exact ih () (hW ()) _ s c' h p (fence_hasBad k hp)
  | rmw k noRet l op ret ih =>
    intro c s c' h p hp
    obtain ⟨hl, hW⟩ := hW
    simp only [runTree] at h
    have h1 := fenceOpt_hasBad A.rmwFence hp
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at h h1
    rw [List.mem_flatMap] at h
    obtain ⟨⟨tr, old, c2⟩, h2, h⟩ := h
    have h12 := read_hasBad A h2 h1
    simp only at h
    split at h
    · exact ih old (hW old) _ s c' h p (fenceOpt_hasBad A.rmwFence h12)
    · rename_i new hnew
      rw [List.mem_flatMap] at h
      obtain ⟨c3, hc3, h⟩ := h
      change .ok (s, c') ∈ runTree A tid iv
        (if A.rmwFence then fenceStep (rmwPost A k noRet l c3) .sy else rmwPost A k noRet l c3) (ret old) at h
      exact ih old (hW old) _ s c' h p
        (fenceOpt_hasBad A.rmwFence (rmwPost_hasBad A k noRet l (write_hasBad A tid (hl old new hnew) hc3 h12)))

end RulesG

/-- **One instruction of code writing as `G` says, from a `P` state, keeps
`P`** (when the instructions keep it) **and a bad promise outstanding.** -/
theorem stepOneWith_hasBad_on {I : ISA} (A : Arch) {G : Loc → Val → Prop} {P : I.State → Prop}
    {cs : CertSem I} (hW : WriteCodeOn G P cs.exec) (hP : WideInv P cs.exec)
    {t : Thread I} {tid : Nat} {mem : Memory} {outs : List (Except String (Kraken.Promising.Outcome I))}
    (hstep : cs.step A t tid mem = some outs) {o : Kraken.Promising.Outcome I}
    (ho : .ok o ∈ outs) (hst : P t.st) {p : Time}
    (h : p ∈ t.prom ∧ ∃ w, mem.get? p = some w ∧ ¬ G w.loc w.val) :
    P o.thread.st ∧ p ∈ o.thread.prom ∧ ∃ w, o.mem.get? p = some w ∧ ¬ G w.loc w.val := by
  unfold CertSem.step stepOneWithD at hstep
  cases hex : cs.exec t.st with
  | none => rw [hex] at hstep; cases hstep
  | some tree =>
    rw [hex] at hstep
    have hstep' : _ = outs := Option.some.inj hstep
    subst hstep'
    rw [List.mem_flatMap] at ho
    obtain ⟨r, hr, ho⟩ := ho
    cases r with
    | error m => simp at ho
    | ok q =>
      obtain ⟨st, c'⟩ := q
      simp only [List.mem_map, Except.ok.injEq] at ho
      obtain ⟨th, hth, rfl⟩ := ho
      have hd := runTree_hasBad A tid _ tree (hW _ _ hst hex) _ st c' hr p h
      refine ⟨?_, (finishInstr_relKey hth).1 ▸ hd.1, hd.2⟩
      show P th.st
      rw [finishInstr_st hth]
      exact hP _ _ _ hst hex (runTree_treeLeaf A tid _ tree _ st c' hr)

/-- **A solo run from a `P` state keeps a bad promise outstanding.** -/
theorem threadNPC_hasBad_on {I : ISA} (A : Arch) {G : Loc → Val → Prop} {P : I.State → Prop}
    {cs : CertSem I} (hW : WriteCodeOn G P cs.exec) (hP : WideInv P cs.exec)
    {tid : Nat} {x y : Thread I × Memory} (hr : ThreadNPC A cs tid x y) (hst : P x.1.st) {p : Time}
    (h : p ∈ x.1.prom ∧ ∃ w, x.2.get? p = some w ∧ ¬ G w.loc w.val) :
    p ∈ y.1.prom ∧ ∃ w, y.2.get? p = some w ∧ ¬ G w.loc w.val := by
  induction hr with
  | refl => exact h
  | step hs _ ih =>
    obtain ⟨outs, o, hso, ho, rfl⟩ := hs
    have h' := stepOneWith_hasBad_on A hW hP hso ho hst h
    exact ih h'.1 h'.2

/-- **A thread at a `P` state holding a bad promise is not certifiable.** -/
theorem not_certOkC_of_bad_on {I : ISA} (A : Arch) {G : Loc → Val → Prop} {P : I.State → Prop}
    {cs : CertSem I} (hW : WriteCodeOn G P cs.exec) (hP : WideInv P cs.exec)
    (tid : Nat) {t : Thread I} {mem : Memory} (hst : P t.st) {p : Time} (hp : p ∈ t.prom)
    {w : Msg} (hg : mem.get? p = some w) (hb : ¬ G w.loc w.val) : ¬ CertOkC A cs tid t mem := by
  rintro ⟨t', mem', hr, he⟩
  have := (threadNPC_hasBad_on A hW hP hr (x := (t, mem)) hst ⟨hp, w, hg, hb⟩).1
  rw [he] at this; cases this

/-- **Every outstanding promise of a certifiable thread at a `P` state
satisfies `G`.** -/
theorem certOkC_prom_good_on {I : ISA} {A : Arch} {G : Loc → Val → Prop} {P : I.State → Prop}
    {cs : CertSem I} (hW : WriteCodeOn G P cs.exec) (hP : WideInv P cs.exec)
    {tid : Nat} {t : Thread I} {mem : Memory} (hst : P t.st) (hc : CertOkC A cs tid t mem)
    {p : Time} (hp : p ∈ t.prom) {w : Msg} (hg : mem.get? p = some w) : G w.loc w.val :=
  Classical.byContradiction fun hb => not_certOkC_of_bad_on A hW hP tid hst hp hg hb hc

/-- **Every outstanding promise of a certifiable thread of code writing as
`G` says satisfies `G`.** -/
theorem certOkC_prom_good {I : ISA} {A : Arch} {G : Loc → Val → Prop}
    {cs : CertSem I} (hW : WriteCode G cs.exec) {tid : Nat} {t : Thread I}
    {mem : Memory} (hc : CertOkC A cs tid t mem) {p : Time} (hp : p ∈ t.prom) {w : Msg}
    (hg : mem.get? p = some w) : G w.loc w.val :=
  certOkC_prom_good_on (P := fun _ => True) (WriteCodeOn.of_code _ hW) (fun _ _ _ _ _ _ => trivial)
    trivial hc hp hg

/-! ## Writes of 64-bit values -/

/-- A write of a value that fits in 64 bits (`Val` is 128 bits wide). -/
def Fit64 (_ : Loc) (v : Val) : Prop := v.toNat < 2 ^ 64

/-- **Every write event of the tree is of a 64-bit value.** -/
abbrev Fit64Tree {σ : Type} (t : EvTree σ) : Prop := WriteTree Fit64 t

/-- **Every tree the code yields writes 64-bit values only.** -/
abbrev Fit64Code {I : ISA} (cexec : I.State → Option (EvTree I.State)) : Prop := WriteCode Fit64 cexec

/-- **Every tree `cexec` yields from a `P` state writes 64-bit values
only.** -/
abbrev Fit64CodeOn {I : ISA} (P : I.State → Prop) (cexec : I.State → Option (EvTree I.State)) : Prop :=
  WriteCodeOn Fit64 P cexec

/-- A 64-bit value widened to `Val` fits in 64 bits. -/
theorem fit64_setWidth (l : Loc) (x : BitVec 64) : Fit64 l (x.setWidth 128) := by
  show (x.setWidth 128).toNat < 2 ^ 64
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) (by decide)))]
  exact x.isLt

end Scc.Sem
