/-
**Layer L, part 1: the counting extension.**
ISA-neutral; memory, ghost and thread-list facts only.

`TicketInv D` (`SLR/LoadClaim.lean`) protects the dispenser but does not
bound the value an `ldadda` on `next` (`D.x`) reads, which the hand-out
(`EraseT.rmwHand`: `old < D.N`) and the absence of wraparound need. The
extension here counts:

- `xCount D mem n`: the number of messages to `x` at timestamps `1..n`;
- `CountInv D c`: `x`'s initial value is `0`; every message to `x` at `ts`
  has value `xCount mem ts` (**ranks**); its writer is a thread of `c`; no
  two messages to `x` have the same writer (**distinct writers**); at most
  `D.N` threads. It depends on the configuration only through its memory and
  its number of threads. (That a thread's own message to `x` is a promise
  until the thread has accessed `x` is not part of it: at an RMW it is the
  machine invariant's `ownCoh` with the thread's `coh x = 0`.)
- `TX D g c := TicketInv D g c ∧ CountInv D c`, the extension `X` of the
  ticket program's erasure (`modelX I (TX D)`).
- `XFresh D mem w`: the promise obligation (`PromiseFresh'`): a promise to
  `x` writes `xCount mem |M| + 1` and its writer has no message to `x` yet.
  `CountInv.fresh`: it implies `D.Fresh` (the obligation of `TicketInv`).
- `tx_promiseLaw`: `XPromiseLaw (TX D) (XFresh D)`, the law
  `theorem1IIPureX'` needs.

Preservation lemmas for the link (`EnvG/TicketLink.lean`):
`CountInv.append` / `CountInv.same` (a write, a fulfilment, a promise),
`TicketInv.grow` (a ghost step keeping claims, acquire table and update ids,
growing `u`: stores, prepays, pending marks), `TicketInv.takeFold` (the
iterated take), and the ticket bound `CountInv.xFresh_of_atomic` (an RMW on
`x` by a thread with no message to `x` reads a value `< D.N`, and its write
is `XFresh`) / `CountInv.old_lt_fulfil` (the same when the RMW fulfils its
thread's promise).
-/
import Kraken.Promising.SLR.TicketRule
import Kraken.Promising.SLR.EnvG.TakeAll

namespace Kraken.Promising.SLR

variable {I : ISA}

/-- `omega` on `Time`/`View`/`PredId` (abbreviations of `Nat`). -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View, PredId] at *); omega))

namespace Dispenser

variable {D : Dispenser}

/-! ## Counting the messages to `x` -/

/-- `ts` holds a message to `x`. -/
def xAt (D : Dispenser) (mem : Memory) (ts : Time) : Bool :=
  match mem.get? ts with
  | some w => decide (w.loc = D.x)
  | none => false

theorem xAt_iff {mem : Memory} {ts : Time} : D.xAt mem ts = true ↔ ∃ w, mem.get? ts = some w ∧ w.loc = D.x := by
  unfold xAt; split <;> simp_all

/-- The number of messages to `x` at timestamps `1..n`. -/
def xCount (D : Dispenser) (mem : Memory) (n : Nat) : Nat :=
  ((List.range n).filter fun i => D.xAt mem (i + 1)).length

theorem xCount_succ (mem : Memory) (n : Nat) :
    D.xCount mem (n + 1) = D.xCount mem n + (if D.xAt mem (n + 1) then 1 else 0) := by
  unfold xCount
  rw [List.range_succ, List.filter_append, List.length_append]
  cases h : D.xAt mem (n + 1) <;> simp [h]

theorem xCount_mono (mem : Memory) {n m : Nat} (h : n ≤ m) : D.xCount mem n ≤ D.xCount mem m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    rw [← Nat.add_assoc, xCount_succ]
    have := ih (Nat.le_add_right _ _)
    omega

theorem xCount_lt_of_xAt (mem : Memory) {n m : Nat} (h : n < m) (hx : D.xAt mem m = true) :
    D.xCount mem n < D.xCount mem m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [xCount_succ]
  simp only [hx, ↓reduceIte]
  have := xCount_mono (D := D) mem (show n ≤ k by omega)
  omega

theorem xCount_prefix {mem mem' : Memory} (hp : mem.Prefix mem') {n : Nat} (hn : n ≤ mem.last) :
    D.xCount mem' n = D.xCount mem n := by
  unfold xCount
  congr 1
  refine List.filter_congr fun i hi => ?_
  have : i + 1 ≤ mem.last := by have := List.mem_range.mp hi; omega_t
  unfold xAt; rw [hp.get? this]

/-- No message to `x` in `(a, b]`: the count does not change. -/
theorem xCount_flat {mem : Memory} {a b : Nat} (hab : a ≤ b) (h : ∀ ts, a < ts → ts ≤ b → D.xAt mem ts = false) :
    D.xCount mem b = D.xCount mem a := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← Nat.add_assoc, xCount_succ, h (a + k + 1) (by omega) (by omega),
      ih (Nat.le_add_right _ _) fun ts h1 h2 => h ts h1 (by omega)]
    rfl

theorem xAt_append_last (mem : Memory) (w : Msg) : D.xAt (mem.append w).1 (mem.last + 1) = decide (w.loc = D.x) := by
  unfold xAt; rw [Memory.get?_append_last]

/-- The messages of an appended memory: an old one or the new one. -/
theorem get?_append_cases {mem : Memory} {w w' : Msg} {ts : Time} (h : (mem.append w).1.get? ts = some w') :
    (ts ≤ mem.last ∧ mem.get? ts = some w') ∨ (ts = mem.last + 1 ∧ w' = w) :=
  Memory.get?_append_eq_some mem w h

/-! ## A pigeonhole on writers -/

theorem nodup_map_of_inj {α β : Type} (f : α → β) :
    ∀ {L : List α}, L.Nodup → (∀ a ∈ L, ∀ b ∈ L, f a = f b → a = b) → (L.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: L, h, hi => by
    rw [List.nodup_cons] at h
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_map_of_inj f h.2 fun x hx y hy =>
      hi x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)⟩
    obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
    exact h.1 ((hi b (List.mem_cons_of_mem _ hb) a (List.mem_cons_self ..) he) ▸ hb)

/-- The writer of the message at `ts` (`0` if none). -/
def tidAt (mem : Memory) (ts : Time) : Nat := ((mem.get? ts).map (·.tid)).getD 0

/-- **Pigeonhole**: if the messages to `x` at `1..n` have pairwise distinct
writers below `S`, none of them `j₀ < S`, there are at most `S - 1`. -/
theorem xCount_le_of_writers {mem : Memory} {n S j₀ : Nat} (hj : j₀ < S)
    (hw : ∀ ts w, 1 ≤ ts → ts ≤ n → mem.get? ts = some w → w.loc = D.x → w.tid < S ∧ w.tid ≠ j₀)
    (hd : ∀ ts ts' w w', mem.get? ts = some w → mem.get? ts' = some w' → w.loc = D.x → w'.loc = D.x →
      w.tid = w'.tid → ts = ts') :
    D.xCount mem n ≤ S - 1 := by
  unfold xCount
  generalize hL : (List.range n).filter (fun i => D.xAt mem (i + 1)) = L
  have hmem : ∀ i ∈ L, i < n ∧ ∃ w, mem.get? (i + 1) = some w ∧ w.loc = D.x := fun i hi => by
    rw [← hL] at hi
    obtain ⟨h1, h2⟩ := List.mem_filter.mp hi
    exact ⟨List.mem_range.mp h1, xAt_iff.mp h2⟩
  have hnd : L.Nodup := hL ▸ List.Nodup.sublist (List.filter_sublist) List.nodup_range
  have hinj : ∀ a ∈ L, ∀ b ∈ L, tidAt mem (a + 1) = tidAt mem (b + 1) → a = b := by
    intro a ha b hb he
    obtain ⟨-, wa, hwa, hla⟩ := hmem a ha
    obtain ⟨-, wb, hwb, hlb⟩ := hmem b hb
    have he' : wa.tid = wb.tid := by simpa only [tidAt, hwa, hwb, Option.map_some, Option.getD_some] using he
    have := hd _ _ _ _ hwa hwb hla hlb he'
    omega_t
  have hsub : L.map (fun i => tidAt mem (i + 1)) ⊆ (List.range S).erase j₀ := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hk
    obtain ⟨hin, w, hw', hl⟩ := hmem i hi
    have hi1 : i + 1 ≤ n := hin
    obtain ⟨h1, h2⟩ := hw (i + 1) w (Nat.le_add_left _ _) hi1 hw' hl
    simp only [tidAt, hw', Option.map_some, Option.getD_some]
    exact (List.mem_erase_of_ne h2).mpr (List.mem_range.mpr h1)
  have := (nodup_map_of_inj _ hnd hinj).length_le_of_subset hsub
  rw [List.length_map, List.length_erase_of_mem (List.mem_range.mpr hj), List.length_range] at this
  exact this

/-! ## The counting invariant -/

/-- **The counting invariant** of the ticket counter `x` (see the module
docstring). -/
structure CountInv (D : Dispenser) (c : Config I) : Prop where
  init : c.mem.initVal D.x = 0
  rank : ∀ ts w, c.mem.get? ts = some w → w.loc = D.x → w.val.toNat = D.xCount c.mem ts
  wlt : ∀ ts w, c.mem.get? ts = some w → w.loc = D.x → w.tid < c.threads.size
  wdist : ∀ ts ts' w w', c.mem.get? ts = some w → c.mem.get? ts' = some w' → w.loc = D.x → w'.loc = D.x →
    w.tid = w'.tid → ts = ts'
  sz : c.threads.size ≤ D.N

/-- **The ticket program's extension**: the dispenser invariant and the
counting invariant. -/
def TX (D : Dispenser) (g : Ghost) (c : Config I) : Prop := D.TicketInv g c ∧ D.CountInv c

/-- **The promise obligation of `TX`**: a write to `x` is the next rank and
its writer has no message to `x` yet. -/
def XFresh (D : Dispenser) (mem : Memory) (w : Msg) : Prop :=
  w.loc = D.x → w.val.toNat = D.xCount mem mem.last + 1 ∧
    ∀ ts w', mem.get? ts = some w' → w'.loc = D.x → w'.tid ≠ w.tid

theorem read?_x_zero {mem : Memory} {v : Val} (h0 : mem.initVal D.x = 0) (h : mem.read? D.x 0 = some v) :
    v.toNat = 0 := by
  unfold Memory.read? at h
  simp only [↓reduceIte, Option.some.injEq] at h
  rw [← h, h0]; rfl

/-- The value read from `x` at `tr` is its rank. -/
theorem CountInv.read_rank {c : Config I} (h : D.CountInv c) {tr : Time} {v : Val}
    (hrd : c.mem.read? D.x tr = some v) : v.toNat = D.xCount c.mem tr := by
  by_cases h0 : tr = 0
  · subst h0; rw [read?_x_zero h.init hrd]; rfl
  · obtain ⟨w, hw, hl, rfl⟩ := read?_get? hrd h0
    exact h.rank tr w hw hl

/-- **Ranks give `MonoX`.** -/
theorem CountInv.monoX {c : Config I} (h : D.CountInv c) : D.MonoX c.mem := by
  intro ts₁ ts₂ v₁ v₂ hlt h₁ h₂
  have h0 : ts₂ ≠ 0 := by omega_t
  obtain ⟨w₂, hw₂, hl₂, rfl⟩ := read?_get? h₂ h0
  rw [h.read_rank h₁, h.rank ts₂ w₂ hw₂ hl₂]
  exact xCount_lt_of_xAt c.mem hlt (xAt_iff.mpr ⟨w₂, hw₂, hl₂⟩)

/-- **`XFresh` gives `D.Fresh`** (the next rank is above every value). -/
theorem CountInv.fresh {c : Config I} (h : D.CountInv c) {w : Msg} (hf : D.XFresh c.mem w) : D.Fresh c.mem w := by
  intro hl ts v hv
  rw [(hf hl).1, h.read_rank hv]
  have : ts ≤ c.mem.last := lc_read?_le_last hv
  have := xCount_mono (D := D) c.mem this
  omega

/-- **`CountInv` after an append** (a write or a promise of `w`). -/
theorem CountInv.append {c c' : Config I} (h : D.CountInv c) {w : Msg} (hm : c'.mem = (c.mem.append w).1)
    (hf : D.XFresh c.mem w) (hsz : c'.threads.size = c.threads.size) (hwlt : w.loc = D.x → w.tid < c.threads.size) :
    D.CountInv c' := by
  have hp := Memory.Prefix.append c.mem w
  refine ⟨by rw [hm, hp.initVal]; exact h.init, fun ts w' hw' hl => ?_, fun ts w' hw' hl => ?_,
    fun ts ts' w₁ w₂ h₁ h₂ hl₁ hl₂ he => ?_, hsz ▸ h.sz⟩ <;> (try rw [hm] at *)
  · rcases get?_append_cases hw' with ⟨hle, hg⟩ | ⟨rfl, rfl⟩
    · rw [xCount_prefix hp hle]; exact h.rank ts w' hg hl
    · rw [(hf hl).1, xCount_succ, xAt_append_last, decide_eq_true hl, xCount_prefix hp (Nat.le_refl _)]
      rfl
  · rw [hsz]
    rcases get?_append_cases hw' with ⟨-, hg⟩ | ⟨-, rfl⟩
    · exact h.wlt ts w' hg hl
    · exact hwlt hl
  · rcases get?_append_cases h₁ with ⟨-, hg₁⟩ | ⟨rfl, rfl⟩ <;>
      rcases get?_append_cases h₂ with ⟨-, hg₂⟩ | ⟨rfl, rfl⟩
    · exact h.wdist ts ts' w₁ w₂ hg₁ hg₂ hl₁ hl₂ he
    · exact absurd he ((hf hl₂).2 ts w₁ hg₁ hl₁)
    · exact absurd he.symm ((hf hl₁).2 ts' w₂ hg₂ hl₂)
    · rfl

/-- **`CountInv` with the memory unchanged** (a fulfilment, a load, a
fence). -/
theorem CountInv.same {c c' : Config I} (h : D.CountInv c) (hm : c'.mem = c.mem)
    (hsz : c'.threads.size = c.threads.size) : D.CountInv c' :=
  ⟨hm ▸ h.init, hm ▸ h.rank, fun ts w' hw' hl => hsz ▸ h.wlt ts w' (hm ▸ hw') hl, hm ▸ h.wdist, hsz ▸ h.sz⟩

/-- **`TX` depends on the configuration only through its memory and its
number of threads.** -/
theorem TX.congr {g : Ghost} {c c' : Config I} (h : D.TX g c) (hm : c'.mem = c.mem)
    (hsz : c'.threads.size = c.threads.size) : D.TX g c' :=
  ⟨ticketInv_mem hm.symm h.1, h.2.same hm hsz⟩

/-! ## The ticket bound -/

/-- **The ticket bound at a read**: a value read from `x` at `tr`, when
thread `j₀` of `c` has no message to `x` at or below `tr`, is its rank and
below `D.N`. -/
theorem CountInv.old_lt {c : Config I} (h : D.CountInv c) {tr : Time} {old : Val}
    (hrd : c.mem.read? D.x tr = some old) {j₀ : Nat} (hj : j₀ < c.threads.size)
    (hown : ∀ ts w, ts ≤ tr → c.mem.get? ts = some w → w.loc = D.x → w.tid ≠ j₀) :
    old.toNat < D.N ∧ old.toNat = D.xCount c.mem tr := by
  have hr := h.read_rank hrd
  refine ⟨?_, hr⟩
  have := xCount_le_of_writers (D := D) (mem := c.mem) (n := tr) hj
    (fun ts w _ hle hw hl => ⟨h.wlt ts w hw hl, hown ts w hle hw hl⟩) h.wdist
  have := h.sz
  omega

/-- **An appending RMW on `x` by a thread with no message to `x`** (read
`(x, tr)` of `old`, atomic up to `|M| + 1`, writing `old + 1`): the read is
below `D.N` and the write is `XFresh`. -/
theorem CountInv.xFresh_of_atomic {c : Config I} (h : D.CountInv c) {tid : Nat} {tr : Time} {old new : Val}
    (hrd : c.mem.read? D.x tr = some old) (hat : c.mem.atomic D.x tid tr (c.mem.last + 1) = true)
    (hown : ∀ ts w, c.mem.get? ts = some w → w.loc = D.x → w.tid ≠ tid) (hj : tid < c.threads.size)
    (hnew : new.toNat = old.toNat + 1) : old.toNat < D.N ∧ D.XFresh c.mem ⟨D.x, new, tid⟩ := by
  obtain ⟨hlt, hr⟩ := h.old_lt hrd hj fun ts w _ hw hl => hown ts w hw hl
  refine ⟨hlt, fun _ => ⟨?_, fun ts w hw hl => hown ts w hw hl⟩⟩
  have htr := lc_read?_le_last hrd
  have hflat : D.xCount c.mem c.mem.last = D.xCount c.mem tr := by
    refine xCount_flat htr fun ts h1 h2 => ?_
    cases hx : D.xAt c.mem ts with
    | false => rfl
    | true =>
      obtain ⟨w, hw, hl⟩ := xAt_iff.mp hx
      exact absurd (atomic_between hat hrd h1 (by omega_t) hw hl) (hown ts w hw hl)
  show new.toNat = _
  omega

/-- **The ticket bound when the RMW fulfils its thread's promise** `tw` (a
message to `x` of thread `tid`, so its only one): the read `tr < tw` is
below `D.N`. -/
theorem CountInv.old_lt_fulfil {c : Config I} (h : D.CountInv c) {tid : Nat} {tr tw : Time} {old new : Val}
    (hrd : c.mem.read? D.x tr = some old) (htr : tr < tw) (hget : c.mem.get? tw = some ⟨D.x, new, tid⟩)
    (hj : tid < c.threads.size) : old.toNat < D.N :=
  (h.old_lt hrd hj fun ts w hle hw hl he => by
    have := h.wdist ts tw w ⟨D.x, new, tid⟩ hw hget hl rfl he
    omega_t).1

/-! ## The dispenser invariant across ghost steps -/

/-- **`TicketInv` across a ghost step that keeps the claims, the acquire
table and the update ids and grows `u`** (stores, prepays, pending marks),
with the memory growing by a prefix that keeps `MonoX`. -/
theorem TicketInv.grow {rF : Nat → Res} {g g' : Ghost} {T : Nat → Prop} {c c' : Config I} (E : Erase rF g T c)
    (h : D.TicketInv g c) (hp : c.mem.Prefix c'.mem) (hmono : D.MonoX c'.mem) (hcl : g'.claims = g.claims)
    (htab : g'.acqTab = g.acqTab) (hupd : g'.upd = g.upd) (hu : ∀ s ∈ g.u, s ∈ g'.u) : D.TicketInv g' c' := by
  refine ⟨h.disp.frame (fun s hs _ => hu s hs) (fun n => ?_) (fun h' => hupd ▸ h') (fun h' => by
    unfold Ghost.Claimed; rw [hcl]; exact h') (by unfold Ghost.acqPred; rw [htab]), hmono⟩
  unfold Handed; rw [hcl]
  exact handed_prefix hp (claims_le E) n

/-- **The iterated take keeps `TicketInv`** (`TicketInv.take` along the
fold; the thread exempt from validity, as `takeFold_spec`). -/
theorem TicketInv.takeFold {rF : Nat → Res} {T : Nat → Prop} {c : Config I} {tid : Nat} {l : Loc} {tr : Time}
    (hn : tid < c.threads.size) (hT : T tid) (n₀ : Nat) :
    ∀ (ids : List PredId) (a : EnvG.TakeAcc), ids.Nodup → (∀ ι ∈ ids, 1 ≤ a.r.acq l ι ∧ ι < n₀) →
      n₀ ≤ a.g.acqTab.length → Erase (setRes rF tid a.r) a.g T c → D.TicketInv a.g c →
      D.TicketInv (ids.foldl (EnvG.takeStep l tr) a).g c
  | [], _, _, _, _, _, h => h
  | ι :: ids, a, hnd, hids, hn₀, E, h => by
    rw [List.nodup_cons] at hnd
    simp only [List.foldl_cons]
    obtain ⟨hι, hιn⟩ := hids ι (List.mem_cons_self ..)
    cases hsl : EnvG.slotAt a.g (l, tr) ι with
    | none =>
      have e : EnvG.takeStep l tr a ι = a := by unfold EnvG.takeStep; rw [hsl]
      rw [e]
      exact TicketInv.takeFold hn hT n₀ ids a hnd.2 (fun j hj => hids j (List.mem_cons_of_mem _ hj)) hn₀ E h
    | some s =>
      obtain ⟨hs, hk, hid⟩ := EnvG.slotAt_some hsl
      have hs' : (⟨(l, tr), ι, s.res⟩ : Slot) ∈ a.g.u := by
        obtain ⟨k, j, R⟩ := s
        simp only at hk hid
        subst hk hid
        exact hs
      have e : EnvG.takeStep l tr a ι =
          ⟨takeRes a.r l ι a.g.acqTab.length s.res, takeGhost a.g l ι tr, a.ren ++ [(ι, a.g.acqTab.length)]⟩ := by
        unfold EnvG.takeStep; rw [hsl]
      rw [e]
      have E1 := Erase.take E hn hT hι hs'
      have h1 := TicketInv.take E hn hι hs' h
      have hids' : ∀ j ∈ ids, 1 ≤ (takeRes a.r l ι a.g.acqTab.length s.res).acq l j ∧ j < n₀ := by
        intro j hj
        obtain ⟨h1, h2⟩ := hids j (List.mem_cons_of_mem _ hj)
        have hne1 : j ≠ ι := fun e => hnd.1 (e ▸ hj)
        have hne2 : j ≠ a.g.acqTab.length := fun e => by
          have := Nat.lt_of_lt_of_le hιn hn₀; omega_t
        exact ⟨Nat.le_trans h1 (EnvG.takeRes_acq_ge hne1 hne2), h2⟩
      have hn₀' : n₀ ≤ (takeGhost a.g l ι tr).acqTab.length := by rw [takeGhost_length]; omega
      exact TicketInv.takeFold hn hT n₀ ids
        ⟨takeRes a.r l ι a.g.acqTab.length s.res, takeGhost a.g l ι tr, a.ren ++ [(ι, a.g.acqTab.length)]⟩ hnd.2 hids'
        hn₀' E1 h1

/-- **`TicketInv` after the iterated take of an acquire load.** -/
theorem TicketInv.takeAll {rF : Nat → Res} {T : Nat → Prop} {c : Config I} {tid : Nat} {l : Loc} {tr : Time}
    {r : Res} {g : Ghost} (hn : tid < c.threads.size) (hT : T tid) (E : Erase (setRes rF tid r) g T c)
    (h : D.TicketInv g c) : D.TicketInv (EnvG.takeAll l tr r g).g c :=
  TicketInv.takeFold hn hT g.acqTab.length
    (g.acqIds r.acq l) ⟨r, g, []⟩ (EnvG.acqIds_nodup _ _ _)
    (fun _ hι => ⟨Nat.le_of_eq (EnvG.mem_acqIds hι).1.symm, (EnvG.mem_acqIds hι).2⟩) (Nat.le_refl _) E h

/-! ## The promise law -/

/-- **The promise law of `TX`** (`XPromiseLaw`, the input of
`theorem1IIPureX'`): a promise whose message is `XFresh` keeps `TX`. -/
theorem tx_promiseLaw (D : Dispenser) : XPromiseLaw (I := I) D.TX D.XFresh := by
  intro rF g T c tid t w E ht hX hf
  have hn := lt_size_of_get? ht
  exact ⟨hX.1.promise E ht (hX.2.fresh hf), hX.2.append rfl hf (Config.withThread_size ..) (fun _ => hn)⟩

end Dispenser

#print axioms Dispenser.xCount_le_of_writers
#print axioms Dispenser.CountInv.append
#print axioms Dispenser.CountInv.xFresh_of_atomic
#print axioms Dispenser.TicketInv.takeAll
#print axioms Dispenser.tx_promiseLaw

/-! ## No new message to `x` (from `SLR/DispenserRun.lean` and
`SLR/DispenserFresh.lean`; same names) -/

namespace SingleRmw

/-- `m'` extends `m` with no new message to `x`. -/
def XSame (x : Loc) (m m' : Memory) : Prop :=
  m.Prefix m' ∧ ∀ ts w, m'.get? ts = some w → w.loc = x → m.get? ts = some w

theorem XSame.refl (x : Loc) (m : Memory) : XSame x m m := ⟨Memory.Prefix.refl m, fun _ _ h _ => h⟩

theorem XSame.trans {x : Loc} {m m' m'' : Memory} (h₁ : XSame x m m') (h₂ : XSame x m' m'') : XSame x m m'' :=
  ⟨h₁.1.trans h₂.1, fun ts w h hl => h₁.2 ts w (h₂.2 ts w h hl) hl⟩

/-- Appending a message not to `x`. -/
theorem XSame.append {x : Loc} (m : Memory) {w : Msg} (hw : w.loc ≠ x) : XSame x m (m.append w).1 := by
  refine ⟨Memory.Prefix.append m w, fun ts w' h hl => ?_⟩
  rcases Dispenser.get?_append_cases h with ⟨-, hg⟩ | ⟨-, rfl⟩
  · exact hg
  · exact absurd hl hw

/-- `XSame` keeps a message of the old memory. -/
theorem XSame.get? {x : Loc} {m m' : Memory} (h : XSame x m m') {ts : Time} {w : Msg} (hw : m.get? ts = some w) :
    m'.get? ts = some w := by
  rw [h.1.get? (m.last_le_of_get?_eq_some hw)]; exact hw

end SingleRmw

open SingleRmw in
/-- `CountInv` transfers to a memory with no new message to `x`. -/
theorem Dispenser.CountInv.xsame {D : Dispenser} {c c' : Config I}
    (h : D.CountInv c) (hx : XSame D.x c.mem c'.mem) (hsz : c'.threads.size = c.threads.size) : D.CountInv c' := by
  refine ⟨by rw [hx.1.initVal]; exact h.init, fun ts w hw hl => ?_, fun ts w hw hl => ?_,
    fun ts ts' w w' h₁ h₂ hl₁ hl₂ he => h.wdist ts ts' w w' (hx.2 ts w h₁ hl₁) (hx.2 ts' w' h₂ hl₂) hl₁ hl₂ he,
    hsz ▸ h.sz⟩
  · have hg := hx.2 ts w hw hl
    rw [Dispenser.xCount_prefix hx.1 (c.mem.last_le_of_get?_eq_some hg)]
    exact h.rank ts w hg hl
  · rw [hsz]; exact h.wlt ts w (hx.2 ts w hw hl) hl

end Kraken.Promising.SLR
