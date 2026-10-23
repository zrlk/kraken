/-
**The target side of the one-thread memory relation** (`Scc/DESIGN.md` §8,
M1): a plain or acquire 8-byte read by the thread that makes every write
reads the latest write of its word (`MemRel.TLatest`), which `MemRel.latest`
needs.

The thread invariant is `CohCovers t.views tm` with `t.prom = []`: the
thread's coherence view of every location is at least the timestamp of
every message to it. Kraken's `read` rule offers only timestamps with no
write to the location between them and `max νpre (coh l)`, so under the
invariant only the latest write (or the initial write, with none) is
readable (`tlatest_of_read`, `readSuccs_tlatest`, `stepOne_load_tlatest`).

Preservation, for every instruction of the thread (its loads, stores,
read-modify-writes and fences, runtime writes included, since those are
instructions of the thread too): `stepOne_coh` (memory may grow, by the
thread's own appends only: with no outstanding promise a store appends at
`last + 1` and raises its coherence view there). The kernel's steps leave
memory alone and only raise coherence views: `readByte_coh` (the byte read
of a `write` buffer is a plain load, `readByte_tlatest`), `retThread_coh`.

With outstanding promises (`Scc/DESIGN.md` §9.0), the last section: the
cover `CohCoversP` exempts the thread's outstanding promises, a read sees
the latest write not promised (`TLatestP`, `stepOne_load_tlatestP`), and
every instruction and promise step keeps the cover (`stepOne_cohP`,
`stepSemC_cohP`), with no hypothesis on the promises.

Not covered (M2): other threads' writes and promises, `clone`.
-/
import Scc.Sem.MemRel
import Scc.Sem.Kernel
import Kraken.Promising.AcqFloor

namespace Scc.Sem

open Kraken Kraken.Promising

/-- **The thread's coherence views cover memory**: every message's timestamp
is at most the thread's coherence view of its location. -/
def CohCovers (vs : Views) (mem : Memory) : Prop :=
  ∀ k w, mem.get? k = some w → k ≤ vs.getCoh w.loc

namespace CohCovers

/-- With no message (the loaded memory), any views cover it. -/
theorem empty (vs : Views) (init : List (Loc × Val)) : CohCovers vs ⟨init, #[]⟩ := by
  intro k w hk; simp [Memory.get?] at hk

/-- Raising coherence views keeps the cover. -/
theorem mono {vs vs' : Views} {mem : Memory} (h : CohCovers vs mem) (hle : ∀ l, vs.getCoh l ≤ vs'.getCoh l) :
    CohCovers vs' mem := fun k w hk => Nat.le_trans (h k w hk) (hle w.loc)

/-- An append at `last + 1` with the coherence view of its location raised
there keeps the cover. -/
theorem append {vs vs' : Views} {mem : Memory} {w : Msg} (h : CohCovers vs mem)
    (hle : ∀ l, vs.getCoh l ≤ vs'.getCoh l) (hw : mem.last + 1 ≤ vs'.getCoh w.loc) :
    CohCovers vs' (mem.append w).1 := by
  intro k w' hk
  by_cases he : k = mem.last + 1
  · subst he; rw [Memory.get?_append_new] at hk; cases hk; exact hw
  · have hle' : k ≤ mem.last := by
      have h1 := Memory.le_last_of_get? hk
      simp only [Memory.last, Memory.append, Array.size_push] at h1 he
      have h2 : (k : Nat) ≤ mem.msgs.size + 1 := h1
      have h3 : (k : Nat) ≠ mem.msgs.size + 1 := he
      show (k : Nat) ≤ mem.msgs.size
      rcases Nat.lt_or_ge k (mem.msgs.size + 1) with h4 | h4
      · exact Nat.le_of_lt_succ h4
      · exact absurd (Nat.le_antisymm h2 h4) h3
    rw [Memory.get?_append_le hle'] at hk
    exact Nat.le_trans (h k w' hk) (hle _)

end CohCovers

/-- **Under the cover, a readable timestamp is the latest write of the
word**: a write to the word's location at `t` (or the initial write) with
no write to it in `(t, bound]`, `bound` at least the coherence view. -/
theorem tlatest_of_read {vs : Views} {tm : Memory} (hc : CohCovers vs tm) {a t bound : Nat} {v : Val}
    (hr : tm.read? (wordLoc a) t = some v) (hw : tm.writeIn (wordLoc a) t bound = false)
    (hb : vs.getCoh (wordLoc a) ≤ bound) : MemRel.TLatest tm a t := by
  refine ⟨?_, ?_⟩
  · rcases Nat.eq_zero_or_pos t with h0 | hpos
    · exact .inl h0
    · have ht0 : t ≠ 0 := by omega
      unfold Memory.read? at hr
      simp only [ht0, ↓reduceIte] at hr
      cases hg : tm.get? t with
      | none => rw [hg] at hr; cases hr
      | some w =>
        rw [hg] at hr
        by_cases hl : w.loc = wordLoc a
        · exact .inr ⟨w, rfl, hl⟩
        · simp [hl] at hr
  · intro k'' w hlt hg hl
    have hk := hc k'' w hg
    rw [hl] at hk
    unfold Memory.writeIn at hw
    rw [List.any_eq_false] at hw
    have hlt' : @LT.lt Nat instLTNat t k'' := hlt
    have hk' : @LE.le Nat instLENat k'' (vs.getCoh (wordLoc a)) := hk
    have hb' : @LE.le Nat instLENat (vs.getCoh (wordLoc a)) bound := hb
    have := hw (k'' - t - 1) (List.mem_range.mpr (by omega))
    rw [show t + (k'' - t - 1) + 1 = k'' by omega, hg] at this
    simp [hl] at this

section Rules
variable (A : Arch) (tid : Nat) (iv : InstrViews)

/-- **Kraken's `read` rule reads the latest write** of a word under the
cover. -/
theorem readSuccs_tlatest {c : Ctx} {k : LoadKind} {xcl : Bool} {a : Nat} {noRet : Bool}
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl (wordLoc a) noRet) (hc : CohCovers c.views c.mem) :
    MemRel.TLatest c.mem a x.1 ∧ c.mem.read? (wordLoc a) x.1 = some x.2.1 := by
  obtain ⟨t, v, rfl, -, hv, hw, -⟩ := (mem_readSuccs A).mp hx
  exact ⟨tlatest_of_read hc hv hw (Nat.le_max_right _ _), hv⟩

/-- The invariant across a context step: no outstanding promise and the
cover, before and after. -/
def CohStep (c c' : Ctx) : Prop :=
  c.prom = [] → CohCovers c.views c.mem → c'.prom = [] ∧ CohCovers c'.views c'.mem

/-- A context step that keeps memory and promises and raises no coherence
view less. -/
theorem cohStep_of_eq {c c' : Ctx} (hm : c'.mem = c.mem) (hp : c'.prom = c.prom)
    (hle : ∀ l, c.views.getCoh l ≤ c'.views.getCoh l) : CohStep c c' := fun h0 h1 =>
  ⟨hp.trans h0, hm ▸ h1.mono hle⟩

/-- `setCoh` raises every coherence view. -/
theorem getCoh_le_setCoh (vs : Views) (l l' : Loc) (t : View) : vs.getCoh l' ≤ (vs.setCoh l t).getCoh l' := by
  rw [Views.getCoh_setCoh]
  by_cases h : l' = l
  · subst h; simp only [↓reduceIte]; exact Nat.le_max_left _ _
  · simp [h]

/-- A read keeps the invariant. -/
theorem readSuccs_coh {c : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool}
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl l noRet) : CohStep c x.2.2 := by
  obtain ⟨v, -, -, h⟩ := readSuccs_shape A iv hx
  refine cohStep_of_eq (by rw [h]) (readSuccs_prom A iv hx) ?_
  intro l'; rw [h]; exact getCoh_le_setCoh _ _ _ _

/-- A write keeps the invariant: with no promise it is a "promise now" at
`last + 1`, fulfilled at once, and raises the coherence view there. -/
theorem writeSuccs_coh {xr : View} {c : Ctx} {iv' : InstrViews} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val}
    {tr : Option Time} {extra : View} {c' : Ctx} (h : c' ∈ writeSuccs A tid iv' c k xcl l v tr extra xr) :
    CohStep c c' := by
  intro h0 h1
  unfold writeSuccs at h
  rw [List.mem_append, List.mem_filterMap] at h
  rcases h with ⟨t, ht, -⟩ | h
  · rw [h0] at ht; cases ht
  · split at h
    rename_i mem' t hok
    rw [List.mem_ite_nil_right, List.mem_singleton] at h
    obtain ⟨-, rfl⟩ := h
    simp only [Memory.append, Prod.mk.injEq] at hok
    obtain ⟨rfl, rfl⟩ := hok
    refine ⟨by simp [afterWrite, h0], ?_⟩
    show CohCovers _ (c.mem.append _).1
    refine h1.append (fun l' => getCoh_le_setCoh _ _ _ _) ?_
    show c.mem.msgs.size + 1 ≤ (c.views.setCoh l (c.mem.msgs.size + 1)).getCoh l
    rw [Views.getCoh_setCoh]; simp only [↓reduceIte]; exact Nat.le_max_right _ _

/-- A fence keeps the invariant. -/
theorem fenceStep_coh (c : Ctx) (k : FenceKind) : CohStep c (fenceStep c k) :=
  cohStep_of_eq (fenceStep_mem c k) (fenceStep_fields c k).2.2.2.2.1 (fun l => by cases k <;> exact Nat.le_refl _)

/-- The end of an RMW keeps the invariant. -/
theorem rmwPost_coh (c : Ctx) (k : RmwKind) (noRet : Bool) (l : Loc) : CohStep c (rmwPost A k noRet l c) := by
  refine cohStep_of_eq ?_ ?_ ?_ <;> unfold rmwPost <;> split <;> first | rfl | (intro; exact Nat.le_refl _)

/-- Every run of an instruction's event tree keeps the invariant. -/
theorem runTree_coh {σ : Type} (tree : EvTree σ) :
    ∀ (c : Ctx) (s : σ) (c' : Ctx), .ok (s, c') ∈ runTree A tid iv c tree → CohStep c c' :=
  runTree_preserves A tid iv CohStep (fun _ h0 h1 => ⟨h0, h1⟩)
    (fun _ _ _ h₁ h₂ h0 h1 => let r := h₁ h0 h1; h₂ r.1 r.2)
    (fun _ _ _ _ _ _ hx => readSuccs_coh A iv hx) (fun _ _ _ _ _ _ _ _ _ _ h => writeSuccs_coh A tid h)
    fenceStep_coh (fun _ _ => cohStep_of_eq rfl rfl (fun _ => Nat.le_refl _))
    (fun c k noRet l => rmwPost_coh A c k noRet l) tree

end Rules

/-- **One instruction of the thread keeps the invariant**: no outstanding
promise, and the cover of the new memory by the new views. -/
theorem stepOne_coh {I : ISA} (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) (hp : t.prom = []) (hc : CohCovers t.views mem) :
    o.thread.prom = [] ∧ CohCovers o.thread.views o.mem := by
  unfold stepOne at hstep
  cases hex : I.exec t.st with
  | none => rw [hex] at hstep; cases hstep
  | some tree =>
    rw [hex] at hstep
    have hstep' : _ = outs := Option.some.inj hstep
    subst hstep'
    rw [List.mem_flatMap] at ho
    obtain ⟨r, hr, ho⟩ := ho
    cases r with
    | error m => simp at ho
    | ok p =>
      obtain ⟨st, c'⟩ := p
      simp only [List.mem_map, Except.ok.injEq] at ho
      obtain ⟨th, hth, rfl⟩ := ho
      obtain ⟨hp', hc'⟩ := runTree_coh A tid _ tree _ st c' hr hp hc
      obtain ⟨e1, e2⟩ := finishInstr_relKey hth
      have e3 : th.views.coh = c'.views.coh := by have := congrArg Views.coh e2; exact this
      refine ⟨e1.trans hp', fun k w hk => ?_⟩
      have := hc' k w hk
      unfold Views.getCoh at this ⊢
      rw [e3]; exact this

/-- **A load of the thread reads the latest write of its word**: an
instruction that is one 8-byte load of `wordLoc a`, run by a thread with no
promise whose views cover memory, leaves memory alone and continues with a
value read at the latest write of `a`. -/
theorem stepOne_load_tlatest {I : ISA} (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {kl : LoadKind} {xcl : Bool} {a : Nat} {g : Val → I.State}
    (hex : I.exec t.st = some (.load kl xcl (wordLoc a) fun v => .done (g v)))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) (hc : CohCovers t.views mem) :
    o.mem = mem ∧ ∃ ts v, o.thread.st = g v ∧ MemRel.TLatest mem a ts ∧ mem.read? (wordLoc a) ts = some v := by
  obtain ⟨st, c', hr, hth, hm⟩ := (Lower.stepOne_ok_iff A tid hex).mp ⟨outs, o, hstep, ho, rfl, rfl⟩
  rw [Lower.run_load_iff] at hr
  obtain ⟨ts, v, hx, rfl⟩ := hr
  obtain ⟨hl, hv⟩ := readSuccs_tlatest A _ hx hc
  have hmem : c'.mem = mem := by
    obtain ⟨-, -, -, h⟩ := readSuccs_shape A _ hx
    have := congrArg Ctx.mem h; exact this
  exact ⟨hm.trans hmem, ts, v, finishInstr_st hth, hl, hv⟩

/-- **A store of the thread appends one message**: an instruction that is
one plain (non-exclusive) store of `v` to `wordLoc a`, run by a thread with
no promise, appends `⟨wordLoc a, v, tid⟩` at `last + 1` and keeps no
promise (the shape `MemRel.store` takes). -/
theorem stepOne_store_append {I : ISA} (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {kr : StoreKind} {a : Nat} {v : Val} {s : I.State}
    (hex : I.exec t.st = some (.store kr false (wordLoc a) v fun _ => .done s))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) (hp : t.prom = []) :
    o.mem = (mem.append ⟨wordLoc a, v, tid⟩).1 ∧ o.thread.st = s ∧ o.thread.prom = [] := by
  obtain ⟨st, c', hr, hth, hm⟩ := (Lower.stepOne_ok_iff A tid hex).mp ⟨outs, o, hstep, ho, rfl, rfl⟩
  rw [Lower.run_store_iff] at hr
  obtain ⟨rfl, hw⟩ := hr
  unfold writeSuccs at hw
  rw [List.mem_append, List.mem_filterMap] at hw
  rcases hw with ⟨t0, ht0, -⟩ | hw
  · have : (Live.TicketStep.ctx0 tid t mem).prom = [] := hp
    rw [this] at ht0; cases ht0
  · split at hw
    rename_i mem' t1 hok
    rw [List.mem_ite_nil_right, List.mem_singleton] at hw
    obtain ⟨-, rfl⟩ := hw
    simp only [Memory.append, Prod.mk.injEq] at hok
    obtain ⟨rfl, rfl⟩ := hok
    refine ⟨hm, finishInstr_st hth, ?_⟩
    rw [(finishInstr_relKey hth).1]
    show ((Live.TicketStep.ctx0 tid t mem).prom ++ [mem.msgs.size + 1]).erase (mem.msgs.size + 1) = []
    have : (Live.TicketStep.ctx0 tid t mem).prom = [] := hp
    rw [this]; simp

/-! ## The kernel's steps -/

section Kernel

variable {I : ISA} (K : Kernel.Abi I)

/-- Returning from a system call keeps the views. -/
theorem retThread_views (t : Thread I) (r : BitVec 64) : (Kernel.retThread K t r).views = t.views := by
  unfold Kernel.retThread
  suffices h : ∀ (regs : List I.RegId) (u : Thread I),
      (regs.foldl (fun t reg => t.setRegView reg 0 0) u).views = u.views from h _ _
  intro regs
  induction regs with
  | nil => intro u; rfl
  | cons r rs ih => intro u; simp only [List.foldl_cons]; rw [ih]; rfl

/-- **The kernel's byte read of a `write` buffer keeps the cover** (it is a
plain load, or reads private memory). -/
theorem readByte_coh {A : Arch} {t t' : Thread I} {mem : Memory} {a rd : Nat} {b : Fin 256}
    (h : Kernel.readByte K A t mem a rd = some (b, t')) (hc : CohCovers t.views mem) : CohCovers t'.views mem := by
  unfold Kernel.readByte at h
  split at h
  · cases h; exact hc
  · split at h
    · rename_i x v c' hx
      cases h
      have hm := List.mem_of_getElem? hx
      obtain ⟨-, -, -, he⟩ := readSuccs_shape A _ hm
      refine hc.mono fun l => ?_
      have hv := congrArg (fun c : Ctx => c.views.getCoh l) he
      simp only at hv
      show t.views.getCoh l ≤ c'.views.getCoh l
      rw [hv]; exact getCoh_le_setCoh _ _ _ _
    · cases h

/-- **The kernel's byte read of shared memory is of the latest write** of
the word containing it: unless the byte is in the thread's private memory,
it is byte `a % 8` of a value read at the latest write of the word at
`a - a % 8`. -/
theorem readByte_tlatest {A : Arch} {t t' : Thread I} {mem : Memory} {a rd : Nat} {b : Fin 256}
    (h : Kernel.readByte K A t mem a rd = some (b, t')) (hc : CohCovers t.views mem) :
    (t' = t ∧ ∃ x, (K.dmem t.st).loadBytes (BitVec.ofNat 64 a) 1 = some [x]) ∨
      ∃ ts v, MemRel.TLatest mem (a - a % 8) ts ∧ mem.read? (wordLoc (a - a % 8)) ts = some v ∧
        b = Kernel.byteOf v (a % 8) := by
  unfold Kernel.readByte at h
  split at h
  · rename_i x hx; cases h; exact .inl ⟨rfl, x, hx⟩
  · split at h
    · rename_i x v c' hx
      cases h
      have hm := List.mem_of_getElem? hx
      obtain ⟨hl, hv⟩ := readSuccs_tlatest A _ (a := a - a % 8) hm hc
      exact .inr ⟨x, v, hl, hv, rfl⟩
    · cases h

end Kernel

/-- **The thread's step in the machine keeps the invariant**: an instruction
step of the existing machine (`InstrSemC`) of thread `tid` with no promise
whose views cover memory. -/
theorem instrSemC_coh {I : ISA} {A : Arch} {cs : CertSem I} {tid : Nat}
    {c c' : Config I} {t : Thread I} (h : InstrSemC A cs tid c c') (ht : c.threads[tid]? = some t)
    (hp : t.prom = []) (hc : CohCovers t.views c.mem) :
    ∃ t', c'.threads[tid]? = some t' ∧ t'.prom = [] ∧ CohCovers t'.views c'.mem := by
  obtain ⟨t0, outs, o, ht0, hs, ho, -, rfl⟩ := h
  rw [ht] at ht0; cases ht0
  obtain ⟨hp', hc'⟩ := stepOne_coh A hs ho hp hc
  exact ⟨o.thread, ExtMachine.withThread_self ht, hp', hc'⟩

/-! ## With outstanding promises

The thread may hold promises (`Scc/DESIGN.md` §9.0). The invariant drops
`prom = []` and covers only the messages that are not outstanding promises
(`CohCoversP`): every such message is at most the coherence view of its
location. A promised message may lie above it; once fulfilled, the write
raises the coherence view to it. Under this cover a read sees the latest
write of its word that is not an outstanding promise (`TLatestP`), since
Kraken's `read` rule excludes the thread's own promises and every other
later write to the word is at most the bound.

Preservation needs no hypothesis on the promises: a read keeps memory and
promises and raises views; a fulfilment keeps memory, removes the timestamp
from `prom` and raises the coherence view of its location to it; an append
("promise now") adds the message and raises the coherence view there; a
promise step (`Live.Sem.promThread`) adds a message that is promised. With
no promise, `CohCoversP` is `CohCovers` and `TLatestP` is `MemRel.TLatest`. -/

/-- **The thread's coherence views cover the messages it has not promised**:
every message that is not an outstanding promise is at most the coherence
view of its location. -/
def CohCoversP (vs : Views) (prom : List Time) (mem : Memory) : Prop :=
  ∀ k w, mem.get? k = some w → k ∉ prom → k ≤ vs.getCoh w.loc

namespace CohCoversP

/-- With no promise, the cover of `CohCovers`. -/
theorem nil_iff {vs : Views} {mem : Memory} : CohCoversP vs [] mem ↔ CohCovers vs mem :=
  ⟨fun h k w hk => h k w hk (List.not_mem_nil), fun h k w hk _ => h k w hk⟩

/-- The promise-free cover covers whatever is promised. -/
theorem of_cohCovers {vs : Views} {mem : Memory} (h : CohCovers vs mem) (prom : List Time) :
    CohCoversP vs prom mem := fun k w hk _ => h k w hk

/-- Raising coherence views keeps the cover. -/
theorem mono {vs vs' : Views} {prom : List Time} {mem : Memory} (h : CohCoversP vs prom mem)
    (hle : ∀ l, vs.getCoh l ≤ vs'.getCoh l) : CohCoversP vs' prom mem :=
  fun k w hk hp => Nat.le_trans (h k w hk hp) (hle w.loc)

/-- A message at a timestamp other than `last + 1` of an appended memory is
an old one. -/
theorem get?_append_ne {mem : Memory} {w w' : Msg} {k : Nat} (hk : (mem.append w).1.get? k = some w')
    (hne : k ≠ mem.last + 1) : mem.get? k = some w' := by
  have hle' : k ≤ mem.last := by
    have h1 := Memory.le_last_of_get? hk
    simp only [Memory.last, Memory.append, Array.size_push] at h1 hne
    have h2 : (k : Nat) ≤ mem.msgs.size + 1 := h1
    have h3 : (k : Nat) ≠ mem.msgs.size + 1 := hne
    show (k : Nat) ≤ mem.msgs.size
    omega
  rwa [Memory.get?_append_le hle'] at hk

/-- **A promise step keeps the cover**: the appended message is promised. -/
theorem promise {vs : Views} {prom : List Time} {mem : Memory} (h : CohCoversP vs prom mem) (w : Msg) :
    CohCoversP vs (prom ++ [(mem.append w).2]) (mem.append w).1 := by
  intro k w' hk hp
  by_cases he : k = mem.last + 1
  · exact absurd (List.mem_append_right _ (List.mem_singleton.mpr (by rw [he]; rfl))) hp
  · exact h k w' (get?_append_ne hk he) fun hm => hp (List.mem_append_left _ hm)

end CohCoversP

/-- **`k'` is the latest write of the word at `a` not outstanding as a
promise** of `prom`: the initial write (`0`) or a message there not in
`prom`, every later message there being in `prom`. -/
def TLatestP (tm : Memory) (prom : List Time) (a k' : Nat) : Prop :=
  (k' = 0 ∨ ∃ w, tm.get? k' = some w ∧ w.loc = wordLoc a ∧ k' ∉ prom) ∧
    ∀ k'' w, k' < k'' → tm.get? k'' = some w → w.loc = wordLoc a → k'' ∈ prom

/-- With no promise, `TLatestP` is `MemRel.TLatest`. -/
theorem TLatestP.nil_iff {tm : Memory} {a k' : Nat} : TLatestP tm [] a k' ↔ MemRel.TLatest tm a k' := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1.imp_right fun ⟨w, hg, hl, _⟩ => ⟨w, hg, hl⟩, fun k'' w hlt hg hl => ?_⟩
    exact absurd (h2 k'' w hlt hg hl) List.not_mem_nil
  · rintro ⟨h1, h2⟩
    refine ⟨h1.imp_right fun ⟨w, hg, hl⟩ => ⟨w, hg, hl, List.not_mem_nil⟩, fun k'' w hlt hg hl => ?_⟩
    exact absurd hl (h2 k'' w hlt hg)

/-- **Under the cover, a readable timestamp not promised is the latest
write of the word not promised**: a write to the word's location at `t`
(or the initial write), `t` not in `prom`, with no write to it in
`(t, bound]`, `bound` at least the coherence view. -/
theorem tlatestP_of_read {vs : Views} {prom : List Time} {tm : Memory} (hc : CohCoversP vs prom tm)
    {a t bound : Nat} {v : Val} (hr : tm.read? (wordLoc a) t = some v) (hw : tm.writeIn (wordLoc a) t bound = false)
    (hb : vs.getCoh (wordLoc a) ≤ bound) (hp : t ∉ prom) : TLatestP tm prom a t := by
  refine ⟨?_, ?_⟩
  · rcases Nat.eq_zero_or_pos t with h0 | hpos
    · exact .inl h0
    · have ht0 : t ≠ 0 := by omega
      unfold Memory.read? at hr
      simp only [ht0, ↓reduceIte] at hr
      cases hg : tm.get? t with
      | none => rw [hg] at hr; cases hr
      | some w =>
        rw [hg] at hr
        by_cases hl : w.loc = wordLoc a
        · exact .inr ⟨w, rfl, hl, hp⟩
        · simp [hl] at hr
  · intro k'' w hlt hg hl
    refine Classical.byContradiction fun hnp => ?_
    have hk := hc k'' w hg hnp
    rw [hl] at hk
    unfold Memory.writeIn at hw
    rw [List.any_eq_false] at hw
    have hlt' : @LT.lt Nat instLTNat t k'' := hlt
    have hk' : @LE.le Nat instLENat k'' (vs.getCoh (wordLoc a)) := hk
    have hb' : @LE.le Nat instLENat (vs.getCoh (wordLoc a)) bound := hb
    have := hw (k'' - t - 1) (List.mem_range.mpr (by omega))
    rw [show t + (k'' - t - 1) + 1 = k'' by omega, hg] at this
    simp [hl] at this

section RulesP
variable (A : Arch) (tid : Nat) (iv : InstrViews)

/-- **Kraken's `read` rule reads the latest write not promised** of a word
under the cover. -/
theorem readSuccs_tlatestP {c : Ctx} {k : LoadKind} {xcl : Bool} {a : Nat} {noRet : Bool}
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl (wordLoc a) noRet)
    (hc : CohCoversP c.views c.prom c.mem) :
    TLatestP c.mem c.prom a x.1 ∧ c.mem.read? (wordLoc a) x.1 = some x.2.1 := by
  obtain ⟨t, v, rfl, -, hv, hw, hp⟩ := (mem_readSuccs A).mp hx
  refine ⟨tlatestP_of_read hc hv hw (Nat.le_max_right _ _) ?_, hv⟩
  intro hm
  have : c.prom.contains t = true := List.elem_eq_true_of_mem hm
  rw [this] at hp; cases hp

/-- The cover across a context step. -/
def CohStepP (c c' : Ctx) : Prop :=
  CohCoversP c.views c.prom c.mem → CohCoversP c'.views c'.prom c'.mem

/-- A context step that keeps memory and promises and raises no coherence
view less. -/
theorem cohStepP_of_eq {c c' : Ctx} (hm : c'.mem = c.mem) (hp : c'.prom = c.prom)
    (hle : ∀ l, c.views.getCoh l ≤ c'.views.getCoh l) : CohStepP c c' := fun h1 => by
  rw [hm, hp]; exact h1.mono hle

/-- A read keeps the cover. -/
theorem readSuccs_cohP {c : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool}
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl l noRet) : CohStepP c x.2.2 := by
  obtain ⟨v, -, -, h⟩ := readSuccs_shape A iv hx
  refine cohStepP_of_eq (by rw [h]) (readSuccs_prom A iv hx) ?_
  intro l'; rw [h]; exact getCoh_le_setCoh _ _ _ _

/-- **A write keeps the cover**, promises or not: a fulfilment removes its
timestamp from the promises and raises the coherence view of its location
to it; an append adds the message and raises the view there. -/
theorem writeSuccs_cohP {xr : View} {c : Ctx} {iv' : InstrViews} {k : StoreKind} {xcl : Bool} {l : Loc}
    {v : Val} {tr : Option Time} {extra : View} {c' : Ctx} (h : c' ∈ writeSuccs A tid iv' c k xcl l v tr extra xr) :
    CohStepP c c' := by
  intro h1
  rcases (Lower.mem_writeSuccs_iff A tid iv').mp h with ⟨t, -, hg, -, rfl⟩ | ⟨-, rfl⟩
  · intro k' w hk hp
    show k' ≤ (c.views.setCoh l t).getCoh w.loc
    rw [Views.getCoh_setCoh]
    have hk' : c.mem.get? k' = some w := hk
    by_cases he : k' = t
    · subst he
      rw [hg] at hk'; cases hk'
      simp only [↓reduceIte]; exact Nat.le_max_right _ _
    · have hp' : k' ∉ c.prom := fun hm => hp (by
        show k' ∈ c.prom.erase t
        exact (List.mem_erase_of_ne he).mpr hm)
      have := h1 k' w hk' hp'
      split
      · rename_i hl; rw [hl] at this; exact Nat.le_trans this (Nat.le_max_left _ _)
      · exact this
  · intro k' w hk hp
    show k' ≤ (c.views.setCoh l (c.mem.last + 1)).getCoh w.loc
    rw [Views.getCoh_setCoh]
    have hk' : (c.mem.append { loc := l, val := v, tid }).1.get? k' = some w := hk
    by_cases he : k' = c.mem.last + 1
    · subst he
      rw [Memory.get?_append_new] at hk'; cases hk'
      simp only [↓reduceIte]; exact Nat.le_max_right _ _
    · have hold := CohCoversP.get?_append_ne hk' he
      have hp' : k' ∉ c.prom := fun hm => hp (by
        show k' ∈ (c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1)
        exact (List.mem_erase_of_ne he).mpr (List.mem_append_left _ hm))
      have := h1 k' w hold hp'
      split
      · rename_i hl; rw [hl] at this; exact Nat.le_trans this (Nat.le_max_left _ _)
      · exact this

/-- A fence keeps the cover. -/
theorem fenceStep_cohP (c : Ctx) (k : FenceKind) : CohStepP c (fenceStep c k) :=
  cohStepP_of_eq (fenceStep_mem c k) (fenceStep_fields c k).2.2.2.2.1 (fun l => by cases k <;> exact Nat.le_refl _)

/-- The end of an RMW keeps the cover. -/
theorem rmwPost_cohP (c : Ctx) (k : RmwKind) (noRet : Bool) (l : Loc) : CohStepP c (rmwPost A k noRet l c) := by
  refine cohStepP_of_eq ?_ ?_ ?_ <;> unfold rmwPost <;> split <;> first | rfl | (intro; exact Nat.le_refl _)

/-- Every run of an instruction's event tree keeps the cover. -/
theorem runTree_cohP {σ : Type} (tree : EvTree σ) :
    ∀ (c : Ctx) (s : σ) (c' : Ctx), .ok (s, c') ∈ runTree A tid iv c tree → CohStepP c c' :=
  runTree_preserves A tid iv CohStepP (fun _ h => h)
    (fun _ _ _ h₁ h₂ h => h₂ (h₁ h))
    (fun _ _ _ _ _ _ hx => readSuccs_cohP A iv hx) (fun _ _ _ _ _ _ _ _ _ _ h => writeSuccs_cohP A tid h)
    fenceStep_cohP (fun _ _ => cohStepP_of_eq rfl rfl (fun _ => Nat.le_refl _))
    (fun c k noRet l => rmwPost_cohP A c k noRet l) tree

end RulesP

/-- **One instruction of the thread keeps the cover**, with or without
outstanding promises. -/
theorem stepOne_cohP {I : ISA} (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) (hc : CohCoversP t.views t.prom mem) :
    CohCoversP o.thread.views o.thread.prom o.mem := by
  unfold stepOne at hstep
  cases hex : I.exec t.st with
  | none => rw [hex] at hstep; cases hstep
  | some tree =>
    rw [hex] at hstep
    have hstep' : _ = outs := Option.some.inj hstep
    subst hstep'
    rw [List.mem_flatMap] at ho
    obtain ⟨r, hr, ho⟩ := ho
    cases r with
    | error m => simp at ho
    | ok p =>
      obtain ⟨st, c'⟩ := p
      simp only [List.mem_map, Except.ok.injEq] at ho
      obtain ⟨th, hth, rfl⟩ := ho
      have hc' := runTree_cohP A tid _ tree _ st c' hr hc
      obtain ⟨e1, e2⟩ := finishInstr_relKey hth
      have e3 : th.views.coh = c'.views.coh := by have := congrArg Views.coh e2; exact this
      intro k w hk hp
      rw [e1] at hp
      have := hc' k w hk hp
      unfold Views.getCoh at this ⊢
      rw [e3]; exact this

/-- **A load of the thread reads the latest write not promised** of its
word: an instruction that is one 8-byte load of `wordLoc a`, run by a thread
whose views cover the messages it has not promised, leaves memory alone and
continues with a value read at that write. -/
theorem stepOne_load_tlatestP {I : ISA} (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {kl : LoadKind} {xcl : Bool} {a : Nat} {g : Val → I.State}
    (hex : I.exec t.st = some (.load kl xcl (wordLoc a) fun v => .done (g v)))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) (hc : CohCoversP t.views t.prom mem) :
    o.mem = mem ∧ ∃ ts v, o.thread.st = g v ∧ TLatestP mem t.prom a ts ∧ mem.read? (wordLoc a) ts = some v := by
  obtain ⟨st, c', hr, hth, hm⟩ := (Lower.stepOne_ok_iff A tid hex).mp ⟨outs, o, hstep, ho, rfl, rfl⟩
  rw [Lower.run_load_iff] at hr
  obtain ⟨ts, v, hx, rfl⟩ := hr
  obtain ⟨hl, hv⟩ := readSuccs_tlatestP A _ hx hc
  have hmem : c'.mem = mem := by
    obtain ⟨-, -, -, h⟩ := readSuccs_shape A _ hx
    have := congrArg Ctx.mem h; exact this
  exact ⟨hm.trans hmem, ts, v, finishInstr_st hth, hl, hv⟩

/-- **The thread's step in the machine keeps the cover**: an instruction
step (`InstrSemC`) or a promise step (`PromSemC`) of thread `tid`, with or
without outstanding promises. -/
theorem stepSemC_cohP {I : ISA} {A : Arch} {cs : CertSem I} {tid : Nat}
    {c c' : Config I} {t : Thread I} (h : StepSemC A cs tid c c') (ht : c.threads[tid]? = some t)
    (hc : CohCoversP t.views t.prom c.mem) :
    ∃ t', c'.threads[tid]? = some t' ∧ CohCoversP t'.views t'.prom c'.mem := by
  rcases h with ⟨t0, outs, o, ht0, hs, ho, -, rfl⟩ | ⟨t0, w, ht0, -, -, rfl⟩
  · rw [ht] at ht0; cases ht0
    exact ⟨o.thread, ExtMachine.withThread_self ht, stepOne_cohP A hs ho hc⟩
  · rw [ht] at ht0; cases ht0
    exact ⟨_, ExtMachine.withThread_self ht, hc.promise w⟩

end Scc.Sem
