/-
**The abstract-stack history law of a Treiber
stack**, pure combinatorics. No Kraken semantics, no EnvG,
no imports: generic in the node type `α` (with the null `nil`), the payload
type `D`, the thread ids `τ`, and the number of nodes and threads.

**The model.** The modification order of the stack's `top` is a list of CAS
write events (`Ev`), each adjacent to the message it overwrote (`cur pre`,
the value written by the last event of the prefix, `nil` for the initial
message):
- `push w n d`: thread `w` writes node `n ≠ nil`, whose frozen link word holds
  the overwritten value (`link n = cur pre`) and whose frozen payload word holds
  `d` (`data n = d`);
- `pop w r`: thread `w`'s CAS read `r = cur pre ≠ nil` and writes `r`'s link
  (`Ev.val`).
`OK link data nil es` asks this of every event of `es` (`Ev.ok`). Nodes are not
reused: the pushed nodes are distinct (`(pushes es).Nodup`).

**The abstract stack** `stk es` (push conses, pop drops the head) is the
linearisation. `inv` shows that along any `OK` chain `top` holds the stack's
head, consecutive stack nodes are linked, and the bottom node links to `nil`.

**The law** (`pop_reads_pushed`): every popped value `r` is non-null, was pushed
earlier by some thread with payload `d = data r`, and was not popped in between.
Also:
- `pops_nodup`: no node is popped twice;
- `pops_sub_pushes`: every popped node was pushed;
- `length_stk`: the stack's size is `#pushes − #pops`;
- `cur_ne_nil`: `top` is non-null whenever more pushes than pops precede it.
  This gives the client's "no thread finds the stack empty".

**Use** (Treiber2K, `k` nodes per thread): the final clean erasure gives the
events from `top`'s messages in push/pop form (`Treiber2Final.msg_form`) and
the frozen link and data words (`slot_read`). This file then replaces the
two-thread case analysis `Treiber2Hist.hist_core`, for every `k` and every
number of threads.
-/

namespace Kraken.Promising.Lower.StackHistory

variable {τ α D : Type}

/-- A write event of `top`'s modification order. -/
inductive Ev (τ α D : Type) where
  /-- Thread `w` pushes node `n` with payload `d`. -/
  | push (w : τ) (n : α) (d : D)
  /-- Thread `w` pops the node `r` it read. -/
  | pop (w : τ) (r : α)

namespace Ev

/-- The value an event writes to `top`. -/
def val (link : α → α) : Ev τ α D → α
  | push _ n _ => n
  | pop _ r => link r

/-- The event's obligation at the overwritten value `c`. -/
def ok (link : α → α) (data : α → D) (nil : α) (c : α) : Ev τ α D → Prop
  | push _ n d => n ≠ nil ∧ link n = c ∧ data n = d
  | pop _ r => r ≠ nil ∧ r = c

/-- The pushed node, if any. -/
def pushed? : Ev τ α D → Option α
  | push _ n _ => some n
  | pop _ _ => none

/-- The popped node, if any. -/
def popped? : Ev τ α D → Option α
  | push _ _ _ => none
  | pop _ r => some r

/-- The abstract-stack step. -/
def step : List α → Ev τ α D → List α
  | S, push _ n _ => n :: S
  | S, pop _ _ => S.tail

end Ev

variable (link : α → α) (data : α → D) (nil : α)

/-- The value of `top` after the events (`nil` initially). -/
def cur (es : List (Ev τ α D)) : α := es.foldl (fun _ e => e.val link) nil

/-- The abstract stack after the events. -/
def stk (es : List (Ev τ α D)) : List α := es.foldl Ev.step []

/-- The pushed nodes. -/
def pushes (es : List (Ev τ α D)) : List α := es.filterMap Ev.pushed?

/-- The popped nodes. -/
def pops (es : List (Ev τ α D)) : List α := es.filterMap Ev.popped?

/-- **A valid chain**: every event meets its obligation at the value it
overwrote (adjacency). -/
def OK (es : List (Ev τ α D)) : Prop :=
  ∀ pre e post, es = pre ++ e :: post → e.ok link data nil (cur link nil pre)

/-- The stack's link structure: each node links to the next, the bottom one
to `nil`. -/
def Linked : List α → Prop
  | [] => True
  | a :: t => link a = t.headD nil ∧ Linked t

/-- **The invariant**: `top` is the stack's head (or `nil`), the stack is
linked, and holds no `nil`. -/
def Inv (S : List α) (c : α) : Prop := c = S.headD nil ∧ Linked link nil S ∧ nil ∉ S

variable {link data nil}

theorem cur_snoc (es : List (Ev τ α D)) (e : Ev τ α D) : cur link nil (es ++ [e]) = e.val link := by
  simp [cur, List.foldl_append]

theorem stk_snoc (es : List (Ev τ α D)) (e : Ev τ α D) : stk (es ++ [e]) = Ev.step (stk es) e := by
  simp [stk, List.foldl_append]

theorem pushes_snoc (es : List (Ev τ α D)) (e : Ev τ α D) :
    pushes (es ++ [e]) = pushes es ++ e.pushed?.toList := by
  cases e <;> simp [pushes, Ev.pushed?]

theorem pops_snoc (es : List (Ev τ α D)) (e : Ev τ α D) :
    pops (es ++ [e]) = pops es ++ e.popped?.toList := by
  cases e <;> simp [pops, Ev.popped?]

theorem OK.prefix {es post : List (Ev τ α D)} (h : OK link data nil (es ++ post)) : OK link data nil es :=
  fun pre e post' he => h pre e (post' ++ post) (by simp [he])

theorem OK.last {es : List (Ev τ α D)} {e : Ev τ α D} (h : OK link data nil (es ++ [e])) :
    e.ok link data nil (cur link nil es) :=
  h es e [] rfl

/-- The facts carried along a chain. -/
structure Facts (es : List (Ev τ α D)) : Prop where
  inv : Inv link nil (stk es) (cur link nil es)
  nodup : (stk es).Nodup
  src : ∀ x ∈ stk es, ∃ pre1 pre2 w d, es = pre1 ++ Ev.push w x d :: pre2 ∧ x ∉ pops pre2
  len : (stk es).length + (pops es).length = (pushes es).length
  popsNodup : (pops es).Nodup
  popsOut : ∀ x ∈ pops es, x ∉ stk es
  popsIn : ∀ x ∈ pops es, x ∈ pushes es

theorem facts_nil : Facts (link := link) (nil := nil) ([] : List (Ev τ α D)) :=
  ⟨⟨rfl, trivial, by simp [stk]⟩, by simp [stk], by simp [stk], by simp [stk, pops, pushes],
    by simp [pops], by simp [pops], by simp [pops]⟩

theorem mem_pushes_of_src {es : List (Ev τ α D)} {x : α}
    (h : ∃ pre1 pre2 w d, es = pre1 ++ Ev.push w x d :: pre2 ∧ x ∉ pops pre2) : x ∈ pushes es := by
  obtain ⟨pre1, pre2, w, d, rfl, -⟩ := h
  simp [pushes, List.filterMap_append, Ev.pushed?]

/-- **The invariant step.** -/
theorem facts_snoc {es : List (Ev τ α D)} {e : Ev τ α D} (hF : Facts (link := link) (nil := nil) es)
    (hok : e.ok link data nil (cur link nil es)) (hnd : (pushes (es ++ [e])).Nodup) :
    Facts (link := link) (nil := nil) (es ++ [e]) := by
  obtain ⟨⟨hc, hl, hnil⟩, hS, hsrc, hlen, hpn, hpo, hpi⟩ := hF
  rw [pushes_snoc] at hnd
  cases e with
  | push w n d =>
    obtain ⟨hn, hln, -⟩ := hok
    simp only [Ev.pushed?, Option.toList_some, List.nodup_append, List.mem_singleton] at hnd
    obtain ⟨-, -, hfresh⟩ := hnd
    have hnS : n ∉ stk es := fun h => hfresh n (mem_pushes_of_src (hsrc n h)) n rfl rfl
    have hnP : n ∉ pops es := fun h => hfresh n (hpi n h) n rfl rfl
    constructor <;> simp only [stk_snoc, cur_snoc, pops_snoc, pushes_snoc, Ev.step, Ev.val, Ev.popped?,
      Ev.pushed?, Option.toList_none, Option.toList_some, List.append_nil, Inv, Linked]
    · simp only [List.mem_cons, not_or]; exact ⟨rfl, ⟨by rw [hln, hc], hl⟩, Ne.symm hn, hnil⟩
    · exact List.nodup_cons.2 ⟨hnS, hS⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨es, [], w, d, rfl, by simp [pops]⟩
      · obtain ⟨pre1, pre2, w', d', rfl, hx2⟩ := hsrc x hx
        refine ⟨pre1, pre2 ++ [Ev.push w n d], w', d', by simp, ?_⟩
        rw [pops_snoc]; simpa [Ev.popped?] using hx2
    · (try simp at hlen ⊢); omega
    · exact hpn
    · intro x hx
      simp only [List.mem_cons, not_or]
      exact ⟨fun h => hnP (h ▸ hx), hpo x hx⟩
    · intro x hx; simp [hpi x hx]
  | pop w r =>
    obtain ⟨hr, hrc⟩ := hok
    obtain ⟨a, t, hat⟩ : ∃ a t, stk es = a :: t := by
      cases h : stk es with
      | nil => rw [h] at hc; exact absurd (hrc.trans hc) (by simpa using hr)
      | cons a t => exact ⟨a, t, rfl⟩
    rw [hat] at hc hl hnil hS hlen
    have hra : r = a := hrc.trans hc
    subst hra
    obtain ⟨hlink, hlt⟩ := hl
    obtain ⟨hrt, htn⟩ := List.nodup_cons.1 hS
    have hrP : r ∉ pops es := fun h => hpo r h (by rw [hat]; exact List.mem_cons_self ..)
    constructor <;> simp only [stk_snoc, cur_snoc, pops_snoc, pushes_snoc, hat, Ev.step, Ev.val, Ev.popped?,
      Ev.pushed?, Option.toList_none, Option.toList_some, List.append_nil, List.tail_cons, Inv]
    · exact ⟨hlink, hlt, fun h => hnil (List.mem_cons_of_mem _ h)⟩
    · exact htn
    · intro x hx
      obtain ⟨pre1, pre2, w', d', rfl, hx2⟩ := hsrc x (by rw [hat]; exact List.mem_cons_of_mem _ hx)
      refine ⟨pre1, pre2 ++ [Ev.pop w r], w', d', by simp, ?_⟩
      rw [pops_snoc]
      simp only [Ev.popped?, Option.toList_some, List.mem_append, List.mem_singleton, not_or]
      exact ⟨hx2, fun h => hrt (h ▸ hx)⟩
    · (try simp at hlen ⊢); omega
    · exact List.nodup_append.2 ⟨hpn, List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩, fun x hx y hy => by
        rw [List.mem_singleton] at hy; subst hy; exact fun h => hrP (h ▸ hx)⟩
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact fun h => hpo x hx (by rw [hat]; exact List.mem_cons_of_mem _ h)
      · rw [List.mem_singleton] at hx; subst hx; exact hrt
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hpi x hx
      · rw [List.mem_singleton] at hx; rw [hx]
        exact mem_pushes_of_src (hsrc r (by rw [hat]; exact List.mem_cons_self ..))

/-- **The facts hold along every valid chain without node reuse.** -/
theorem facts {es : List (Ev τ α D)} (h : OK link data nil es) (hnd : (pushes es).Nodup) :
    Facts (link := link) (nil := nil) es := by
  induction hn : es.length generalizing es with
  | zero => rw [List.length_eq_zero_iff.1 hn]; exact facts_nil
  | succ k ih =>
    obtain ⟨es', e, rfl⟩ : ∃ es' e, es = es' ++ [e] := by
      rcases List.eq_nil_or_concat es with h0 | ⟨es', e, he⟩
      · subst h0; simp at hn
      · exact ⟨es', e, by simpa using he⟩
    have hnd' : (pushes es').Nodup := by
      rw [pushes_snoc] at hnd; exact (List.nodup_append.1 hnd).1
    exact facts_snoc (ih h.prefix hnd' (by simpa using hn)) h.last hnd

/-- **`inv`**: along a valid chain, `top` is the abstract stack's head, the
stack is linked, and holds no `nil`. -/
theorem inv {es : List (Ev τ α D)} (h : OK link data nil es) (hnd : (pushes es).Nodup) :
    Inv link nil (stk es) (cur link nil es) :=
  (facts h hnd).inv

/-- **The history law**: a pop's value `r` is non-null, was pushed earlier
(by some thread `w'`, with payload `data r = d`), and was not popped since. -/
theorem pop_reads_pushed {pre post : List (Ev τ α D)} {w : τ} {r : α}
    (h : OK link data nil (pre ++ Ev.pop w r :: post)) (hnd : (pushes (pre ++ Ev.pop w r :: post)).Nodup) :
    r ≠ nil ∧ r ∈ stk pre ∧
      ∃ pre1 pre2 w' d, pre = pre1 ++ Ev.push w' r d :: pre2 ∧ r ∉ pops pre2 ∧ data r = d := by
  have hpre : OK link data nil pre := OK.prefix (post := Ev.pop w r :: post) h
  have hnd' : (pushes pre).Nodup := by
    rw [pushes, List.filterMap_append] at hnd; exact (List.nodup_append.1 hnd).1
  have F := facts hpre hnd'
  obtain ⟨hr, hrc⟩ : r ≠ nil ∧ r = cur link nil pre := h pre _ post rfl
  have hmem : r ∈ stk pre := by
    obtain ⟨hc, -, -⟩ := F.inv
    cases hS : stk pre with
    | nil => rw [hS] at hc; exact absurd (hrc.trans hc) hr
    | cons a t => rw [hS] at hc; rw [hrc.trans hc]; exact List.mem_cons_self ..
  obtain ⟨pre1, pre2, w', d, rfl, hr2⟩ := F.src r hmem
  have hpush := h pre1 (Ev.push w' r d) (pre2 ++ Ev.pop w r :: post) (by simp)
  exact ⟨hr, hmem, pre1, pre2, w', d, rfl, hr2, hpush.2.2⟩

/-- **No node is popped twice.** -/
theorem pops_nodup {es : List (Ev τ α D)} (h : OK link data nil es) (hnd : (pushes es).Nodup) :
    (pops es).Nodup :=
  (facts h hnd).popsNodup

/-- **Every popped node was pushed.** -/
theorem pops_sub_pushes {es : List (Ev τ α D)} (h : OK link data nil es) (hnd : (pushes es).Nodup) :
    ∀ x ∈ pops es, x ∈ pushes es :=
  (facts h hnd).popsIn

/-- **The stack's size** is `#pushes − #pops`. -/
theorem length_stk {es : List (Ev τ α D)} (h : OK link data nil es) (hnd : (pushes es).Nodup) :
    (stk es).length + (pops es).length = (pushes es).length :=
  (facts h hnd).len

/-- **Non-emptiness**: after more pushes than pops, `top` is not `nil`. -/
theorem cur_ne_nil {es : List (Ev τ α D)} (h : OK link data nil es) (hnd : (pushes es).Nodup)
    (hlt : (pops es).length < (pushes es).length) : cur link nil es ≠ nil := by
  have F := facts h hnd
  obtain ⟨hc, -, hnil⟩ := F.inv
  have hlen := F.len
  cases hS : stk es with
  | nil => rw [hS] at hlen; simp at hlen; omega
  | cons a t =>
    rw [hS] at hc hnil
    rw [hc]
    exact fun h => hnil (h ▸ List.mem_cons_self ..)

end Kraken.Promising.Lower.StackHistory
