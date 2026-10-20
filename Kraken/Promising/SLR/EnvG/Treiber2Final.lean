/-
Part 3: **the final clean erasure of the
two-thread Treiber stack** gives the history layer's hypotheses
(`EnvG/Treiber2Hist.lean`). ISA-neutral.

Each thread ends in `Done` (`DoneR`): it holds its acquire id of `top`, and
either popped (`DonePop`: its `ldar`, `ldr` and `casal` reads and its
`casal`'s write, as message facts of the final memory) or read `0` and kept
its pop token (`DoneCbz`).

At a final configuration (no outstanding promise) with a clean erasure:

- every non-initial message of `top` has an id-`0` slot in push or pop form
  of its writer (`msg_form`; thread `0` holds id `0`);
- a thread has at most one push-form and one pop-form message
  (`Erase.q_add_le_one_slots` on the node's link, resp. the pop token), and
  none in pop form while it keeps its token (`Erase.q_add_le_one_slot`);
- so a thread's push message is in push form, its pop message in pop form
  (`push_form`, `pop_form`), and these are all of `top`'s messages
  (`msg_cases`);
- the link word (and the data word) of a pushed node holds, at every read
  whose window covers the push, the frozen value (`slot_read`: the push form
  holds the word whole, so its maximal write is the latest of all messages,
  `total_max_of_slot`, `Erase.writes`).

`final_values`: the two threads' `X10` are the two nodes.
-/
import Kraken.Promising.SLR.EnvG.Treiber2Hist
import Kraken.Promising.SLR.EnvG.Treiber2Ghost
import Kraken.Promising.SLR.EnvG.Seen

namespace Kraken.Promising.SLR.EnvG.Treiber2

open Kraken Kraken.Promising
open Kraken.Promising.SLR.EnvG.Treiber (read?_of_get? get?_of_read? initVal_eq)

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

-- An acquire id held at least once by a thread is held once in the total
-- (`TreiberCommon.total_acq_of_ge`; an alias).
hoist_alias [Kraken.Promising.SLR.EnvG.TreiberCommon.total_acq_of_ge ↦ Kraken.Promising.SLR.EnvG.Treiber2.total_acq_of_ge']

/-! ## The ghost facts -/

/-- **The ghost facts** the threads rely on: the release predicates of
`ghost₀`, an acquire table extending `[predA, Pred.top]`. -/
def GW (P : Params) (g : Ghost) : Prop :=
  g.rel = (ghost₀ P).rel ∧ (ghost₀ P).acqTab <+: g.acqTab

namespace GW

variable {P : Params} {g g' : Ghost}

theorem mono (h : GW P g) (hle : g.Le g') : GW P g' :=
  ⟨hle.rel.trans h.1, h.2.trans hle.acqTab⟩

theorem rel_top (h : GW P g) : g.rel P.top = relTop P := by rw [h.1]; exact ghost₀_rel_top P

theorem rel_ne (h : GW P g) {x : Loc} (hx : x ≠ P.top) : g.rel x = Pred.emp := by rw [h.1]; exact ghost₀_rel_ne hx

theorem acqPred_zero (h : GW P g) : g.acqPred 0 = predA P :=
  Ghost.acqPred_of_prefix h.2 (by simp [ghost₀])

theorem impure (h : GW P g) (v : Val) : ¬ Pred.Pure (g.rel P.top) v := by
  rw [h.rel_top]; exact relTop_not_pure P v

end GW

theorem ghost₀_gw (P : Params) : GW P (ghost₀ P) := ⟨rfl, List.prefix_refl _⟩

/-! ## The threads' final facts -/

/-- **A popping thread's final facts** in memory `m` (`v` its `X10`): its
push message `Pw`; its `ldar` read `tr0 ≥ Pw` and its `casal` read
`tr ≥ tr0`, both of 64-bit value `v ≠ 0`; the `casal`'s write `Q > tr` of
the value `x4`, with only its own messages of `top` strictly between; its
`ldr` of `[v + 8]` read `u` (`x4` its 64 bits) with no write to `[v + 8]`
after it up to `tr0`. -/
def DonePopAt (P : Params) (w : Nat) (m : Memory) (v : BitVec 64) (Pw tr0 : Time) : Prop :=
  ∃ (tr Q : Time) (y0 y1 : Val) (x4 : BitVec 64) (tl : Time) (u : Val),
    m.get? Pw = some ⟨P.top, P.nv w, w⟩ ∧ Pw ≤ tr0 ∧ tr0 ≤ tr ∧ tr < Q ∧
    m.read? P.top tr0 = some y0 ∧ BitVec.setWidth 64 y0 = v ∧
    m.read? P.top tr = some y1 ∧ BitVec.setWidth 64 y1 = v ∧ v ≠ 0 ∧
    (∀ p wm, tr < p → p < Q → m.get? p = some wm → wm.loc = P.top → wm.tid = w) ∧
    m.get? Q = some ⟨P.top, BitVec.setWidth 128 x4, w⟩ ∧
    m.read? ⟨v + 8, 8⟩ tl = some u ∧ BitVec.setWidth 64 u = x4 ∧
    (∀ p wm, tl < p → p ≤ tr0 → m.get? p = some wm → wm.loc ≠ ⟨v + 8, 8⟩)

/-- `DonePopAt` at some push message and `ldar` read. -/
def DonePop (P : Params) (w : Nat) (m : Memory) (v : BitVec 64) : Prop :=
  ∃ Pw tr0 : Time, DonePopAt P w m v Pw tr0

/-- **A thread that found the stack empty**: it keeps its pop token; its
push message `Pw`, and its `ldar` read a 64-bit `0` at `r ≥ Pw`. -/
def DoneCbz (P : Params) (w : Nat) (m : Memory) (R : Res) : Prop :=
  1 ≤ (R.wr (P.pt w)).q ∧ ∃ (Pw r : Time) (y0 : Val), m.get? Pw = some ⟨P.top, P.nv w, w⟩ ∧ Pw ≤ r ∧
    m.read? P.top r = some y0 ∧ BitVec.setWidth 64 y0 = 0

/-- **Thread `w` done** with resource `R` and `X10 = v`: its acquire id of
`top`, `top` initially `0`, and a pop or an empty stack. -/
def DoneR (P : Params) (w : Nat) (m : Memory) (R : Res) (v : BitVec 64) : Prop :=
  1 ≤ R.acq P.top w ∧ m.initVal P.top = 0 ∧ (DonePop P w m v ∨ DoneCbz P w m R)

/-! ## Forms of `top`'s messages -/

section Forms

variable {P : Params} {rF : Nat → Res} {g : Ghost} {TT : Nat → Prop} {c : Config I}

/-- **Every non-initial message of `top` has an id-`0` slot in push or pop
form of its writer.** -/
theorem msg_form (E : Erase rF g TT c) (hW : GW P g) (htot : (total rF g c).acq P.top 0 = 1) {V : Time}
    {v : Val} {w : Nat} (hV : c.mem.get? V = some ⟨P.top, v, w⟩) :
    ∃ s ∈ g.u, s.key = (P.top, V) ∧ w < 2 ∧ (PushF P w v c.mem V s.res ∨ PopF P w c.mem V s.res) := by
  have hrd : c.mem.read? (P.top, V).1 (P.top, V).2 = some v := read?_of_get? hV
  obtain ⟨s, hs, hk, -, hP⟩ := slot_of_held E htot hrd (hW.impure v)
  rw [hW.acqPred_zero] at hP
  have hV0 : V ≠ 0 := by rintro rfl; simp [Memory.get?] at hV
  obtain ⟨w', hw', hg, hf⟩ := hP hV0
  rw [hV] at hg
  cases hg
  exact ⟨s, hs, hk, hw', hf⟩

theorem slot_ne_of_key {s s' : Slot} {V V' : Time} (hk : s.key = (P.top, V)) (hk' : s'.key = (P.top, V'))
    (hne : V ≠ V') : s' ≠ s := by
  rintro rfl; rw [hk] at hk'; cases hk'; exact hne rfl

/-- At most one push form per thread. -/
theorem push_unique (E : Erase rF g TT c) {s s' : Slot} (hs : s ∈ g.u) (hs' : s' ∈ g.u) {V V' : Time}
    (hk : s.key = (P.top, V)) (hk' : s'.key = (P.top, V')) {w : Nat} {v v' : Val}
    (h : PushF P w v c.mem V s.res) (h' : PushF P w v' c.mem V' s'.res) : V = V' := by
  refine Classical.byContradiction fun hne => ?_
  have := E.q_add_le_one_slots hs hs' (slot_ne_of_key hk hk' hne) (P.nd w)
  rw [h.2.1, h'.2.1] at this
  grind

/-- At most one pop form per thread. -/
theorem pop_unique (E : Erase rF g TT c) {s s' : Slot} (hs : s ∈ g.u) (hs' : s' ∈ g.u) {V V' : Time}
    (hk : s.key = (P.top, V)) (hk' : s'.key = (P.top, V')) {w : Nat}
    (h : PopF P w c.mem V s.res) (h' : PopF P w c.mem V' s'.res) : V = V' := by
  refine Classical.byContradiction fun hne => ?_
  have := E.q_add_le_one_slots hs hs' (slot_ne_of_key hk hk' hne) (P.pt w)
  have := h.1; have := h'.1
  grind

/-- No pop form while a thread keeps the pop token. -/
theorem pop_kept (E : Erase rF g TT c) {i : Nat} (hi : i < c.threads.size) {w : Nat}
    (hq : 1 ≤ ((rF i).wr (P.pt w)).q) {s : Slot} (hs : s ∈ g.u) {V : Time} (h : PopF P w c.mem V s.res) : False := by
  have := E.q_add_le_one_slot hi hs (P.pt w)
  have := h.1
  grind

/-- **A word frozen in a slot** (the link `nd w` or the data word `dd w` of a
pushed node): a read of it whose window `(tl, B]` covers the slot's maximal
write reads the frozen value. -/
theorem slot_read (E : Erase rF g TT c) (hno : ∀ ts, ¬ Outstanding c ts) {s : Slot} (hs : s ∈ g.u) {l : Loc}
    {y : Val} {t : Time} (hq : (s.res.wr l).q = 1) (hX : (s.res.wr l).X (y, t))
    (hmax : ∀ p, (s.res.wr l).X p → p.2 ≤ t) {tl B : Time} {u : Val}
    (hrd : c.mem.read? l tl = some u)
    (hwin : ∀ p wm, tl < p → p ≤ B → c.mem.get? p = some wm → wm.loc ≠ l) (htB : t ≤ B) : u = y := by
  obtain ⟨hpos, hXt, hmt⟩ := total_max_of_slot E hs hq hX hmax
  have hw := E.writes l (.inl hpos)
  have hset : ∀ ts, Settled c g ts := fun ts => .inl (hno ts)
  -- the frozen write is a message (or the initial one)
  have hrt : c.mem.read? l t = some y := by
    rcases (hw (y, t)).mp hXt with ⟨h0, h1⟩ | ⟨wm, hg, hl, hv, -⟩
    · simp only at h0 h1; subst h0; subst h1; simp [Memory.read?]
    · simp only at hg hv; rw [← hl, ← hv]; exact read?_of_get? hg
  -- the read is at most the frozen write
  have htl : tl ≤ t := by
    by_cases h0 : tl = 0
    · omega_t
    · obtain ⟨wm, hg, hl, hv⟩ := get?_of_read? h0 hrd
      exact hmt (u, tl) ((hw (u, tl)).mpr (.inr ⟨wm, hg, hl, hv, hset tl⟩))
  -- and not below it
  have hte : tl = t := by
    refine Classical.byContradiction fun hne => ?_
    have hlt : tl < t := by omega_t
    have ht0 : t ≠ 0 := by omega_t
    obtain ⟨wm, hg, hl, -⟩ := get?_of_read? ht0 hrt
    exact hwin t wm hlt htB hg hl
  subst hte
  rw [hrd] at hrt
  exact Option.some.inj hrt

end Forms

/-! ## From the final facts to the history -/

/-- **A thread's final data as a side** (`y` still free): the message facts
of `DonePop` / `DoneCbz` on the side's fields. -/
structure RawSide (P : Params) (w : Nat) (m : Memory) (R : Res) (X : Side) : Prop where
  pm : m.get? X.p = some ⟨P.top, P.nv w, w⟩
  n : X.n = P.n w
  pop : X.popped → X.p ≤ X.tr0 ∧ X.tr0 ≤ X.tr ∧ X.tr < X.q ∧
    (∃ y0, m.read? P.top X.tr0 = some y0 ∧ BitVec.setWidth 64 y0 = X.v) ∧
    (∃ y1, m.read? P.top X.tr = some y1 ∧ BitVec.setWidth 64 y1 = X.v) ∧ X.v ≠ 0 ∧
    (∀ p wm, X.tr < p → p < X.q → m.get? p = some wm → wm.loc = P.top → wm.tid = w) ∧
    m.get? X.q = some ⟨P.top, BitVec.setWidth 128 X.x4, w⟩ ∧
    ∃ tl u, m.read? ⟨X.v + 8, 8⟩ tl = some u ∧ BitVec.setWidth 64 u = X.x4 ∧
      ∀ p wm, tl < p → p ≤ X.tr0 → m.get? p = some wm → wm.loc ≠ ⟨X.v + 8, 8⟩
  cbz : ¬ X.popped → 1 ≤ (R.wr (P.pt w)).q ∧ ∃ r y0, X.p ≤ r ∧ m.read? P.top r = some y0 ∧
    BitVec.setWidth 64 y0 = 0

theorem rawSide_of_done {P : Params} {w : Nat} {m : Memory} {R : Res} {v : BitVec 64}
    (h : DonePop P w m v ∨ DoneCbz P w m R) : ∃ X, RawSide P w m R X ∧ (X.popped → X.v = v) := by
  rcases h with ⟨Pw, tr0, tr, Q, y0, y1, x4, tl, u, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ |
    ⟨hq, Pw, r, y0, h1, h2, h3, h4⟩
  · refine ⟨⟨Pw, P.n w, 0, True, Q, tr0, tr, v, x4⟩, ⟨h1, rfl, fun _ => ⟨h2, h3, h4, ⟨y0, h5, h6⟩, ⟨y1, h7, h8⟩,
      h9, h10, h11, tl, u, h12, h13, h14⟩, fun h => absurd trivial h⟩, fun _ => rfl⟩
  · exact ⟨⟨Pw, P.n w, 0, False, 0, 0, 0, 0, 0⟩, ⟨h1, rfl, fun h => h.elim, fun _ => ⟨hq, r, y0, h2, h3, h4⟩⟩,
      fun h => h.elim⟩

section Final

variable {P : Params} {rF : Nat → Res} {g : Ghost} {TT : Nat → Prop} {c : Config I}

theorem sw64_nv (P : Params) (w : Nat) : BitVec.setWidth 64 (P.nv w) = P.n w := by
  simp [Params.nv]

theorem get?_ne_zero {m : Memory} {V : Time} {wm : Msg} (h : m.get? V = some wm) : V ≠ 0 := by
  rintro rfl; simp [Memory.get?] at h

/-- A side's push message is in push form; its pop message, if any, in pop
form. -/
theorem forms_of_raw (E : Erase rF g TT c) (hW : GW P g) (htot : (total rF g c).acq P.top 0 = 1) {w i : Nat}
    (hi : i < c.threads.size) {X : Side} (hX : RawSide P w c.mem (rF i) X) :
    (∃ s ∈ g.u, s.key = (P.top, X.p) ∧ PushF P w (P.nv w) c.mem X.p s.res) ∧
      (X.popped → ∃ s ∈ g.u, s.key = (P.top, X.q) ∧ PopF P w c.mem X.q s.res) := by
  obtain ⟨s, hs, hk, -, hf⟩ := msg_form E hW htot hX.pm
  -- a pop-form push message has an earlier own message of value `nv w`
  have hpush : PushF P w (P.nv w) c.mem X.p s.res := by
    rcases hf with hf | hf
    · exact hf
    · exfalso
      obtain ⟨P', hP', hg'⟩ := hf.2
      obtain ⟨s', hs', hk', -, hf'⟩ := msg_form E hW htot hg'
      have hne : P' ≠ X.p := by omega_t
      rcases hf' with hf' | hf'
      · -- the earlier one is the push form: the pop message is a third
        by_cases hp : X.popped
        · obtain ⟨h0, h1, h2, -, -, -, -, h3, -⟩ := hX.pop hp
          obtain ⟨s'', hs'', hk'', -, hf''⟩ := msg_form E hW htot h3
          rcases hf'' with hf'' | hf''
          · have := push_unique E hs' hs'' hk' hk'' hf' hf''
            omega_t
          · have := pop_unique E hs hs'' hk hk'' hf hf''; omega_t
        · exact pop_kept E hi (hX.cbz hp).1 hs hf
      · exact hne (pop_unique E hs' hs hk' hk hf' hf)
  refine ⟨⟨s, hs, hk, hpush⟩, fun hp => ?_⟩
  obtain ⟨h0, h1, h2, -, -, -, -, h3, -⟩ := hX.pop hp
  obtain ⟨s'', hs'', hk'', -, hf''⟩ := msg_form E hW htot h3
  rcases hf'' with hf'' | hf''
  · have := push_unique E hs hs'' hk hk'' hpush hf''; omega_t
  · exact ⟨s'', hs'', hk'', hf''⟩

/-- **`top`'s messages by thread `w`** are its push and its pop. -/
theorem own_msg (E : Erase rF g TT c) (hW : GW P g) (htot : (total rF g c).acq P.top 0 = 1) {w i : Nat}
    (hi : i < c.threads.size) {X : Side} (hX : RawSide P w c.mem (rF i) X) {V : Time} {v : Val}
    (hV : c.mem.get? V = some ⟨P.top, v, w⟩) : V = X.p ∨ (X.popped ∧ V = X.q) := by
  obtain ⟨⟨s, hs, hk, hpush⟩, hpop⟩ := forms_of_raw E hW htot hi hX
  obtain ⟨s', hs', hk', -, hf⟩ := msg_form E hW htot hV
  rcases hf with hf | hf
  · exact .inl (push_unique E hs' hs hk' hk hf hpush)
  · by_cases hp : X.popped
    · obtain ⟨s'', hs'', hk'', hf''⟩ := hpop hp
      exact .inr ⟨hp, pop_unique E hs' hs'' hk' hk'' hf hf''⟩
    · exact (pop_kept E hi (hX.cbz hp).1 hs' hf).elim

theorem RawSide.setY {P : Params} {w : Nat} {m : Memory} {R : Res} {X : Side} (h : RawSide P w m R X) (y : BitVec 64) :
    RawSide P w m R { X with y := y } :=
  ⟨h.pm, h.n, h.pop, h.cbz⟩

/-- **The history of `top` at the final clean erasure**, with the sides'
links fixed by their push forms. -/
theorem final_core (E : Erase rF g TT c) (hW : GW P g) (hL : TLocs P) (hno : ∀ ts, ¬ Outstanding c ts)
    {i0 i1 : Nat} (hi0 : i0 < c.threads.size) (hi1 : i1 < c.threads.size)
    (htot : (total rF g c).acq P.top 0 = 1) (hT0 : c.mem.initVal P.top = 0) {A B : Side}
    (hA : RawSide P 0 c.mem (rF i0) A) (hB : RawSide P 1 c.mem (rF i1) B)
    {sA sB : Slot} (hsA : sA ∈ g.u) (hsB : sB ∈ g.u) {yA yB yA' yB' : Val} {tA tB trA trB : Time}
    (hqdA : (sA.res.wr (P.nd 0)).q = 1) (hXA : (sA.res.wr (P.nd 0)).X (yA, tA))
    (hmA : ∀ p, (sA.res.wr (P.nd 0)).X p → p.2 ≤ tA) (htA : tA < A.p) (htrA : trA < A.p)
    (hrA : c.mem.read? P.top trA = some yA') (hyA : BitVec.setWidth 64 yA' = BitVec.setWidth 64 yA)
    (hnA : NoTopIn P c.mem trA A.p) (hAy : A.y = BitVec.setWidth 64 yA)
    (hqdB : (sB.res.wr (P.nd 1)).q = 1) (hXB : (sB.res.wr (P.nd 1)).X (yB, tB))
    (hmB : ∀ p, (sB.res.wr (P.nd 1)).X p → p.2 ≤ tB) (htB : tB < B.p) (htrB : trB < B.p)
    (hrB : c.mem.read? P.top trB = some yB') (hyB : BitVec.setWidth 64 yB' = BitVec.setWidth 64 yB)
    (hnB : NoTopIn P c.mem trB B.p) (hBy : B.y = BitVec.setWidth 64 yB) :
    ∃ val, HistOK val A B := by
  let val : Nat → BitVec 64 := fun u => BitVec.setWidth 64 ((c.mem.read? P.top u).getD 0)
  have hval : ∀ {u y}, c.mem.read? P.top u = some y → val u = BitVec.setWidth 64 y := fun h => by
    simp only [val, h, Option.getD_some]
  have hTm : ∀ u, T A B u → u = 0 ∨ ∃ wm, c.mem.get? u = some wm ∧ wm.loc = P.top := by
    intro u hu
    rcases hu with h | h | h | ⟨hp, h⟩ | ⟨hp, h⟩
    · exact .inl h
    · exact .inr ⟨_, h ▸ hA.pm, rfl⟩
    · exact .inr ⟨_, h ▸ hB.pm, rfl⟩
    · obtain ⟨-, -, -, -, -, -, -, h3, -⟩ := hA.pop hp; exact .inr ⟨_, h ▸ h3, rfl⟩
    · obtain ⟨-, -, -, -, -, -, -, h3, -⟩ := hB.pop hp; exact .inr ⟨_, h ▸ h3, rfl⟩
  have hmT : ∀ u wm, c.mem.get? u = some wm → wm.loc = P.top → T A B u := by
    intro u wm hg hl
    obtain ⟨s, -, -, hw2, -⟩ := msg_form E hW htot (show c.mem.get? u = some ⟨P.top, wm.val, wm.tid⟩ by
      rw [hg, ← hl])
    have hg' : c.mem.get? u = some ⟨P.top, wm.val, wm.tid⟩ := by rw [hg, ← hl]
    rcases (show wm.tid = 0 ∨ wm.tid = 1 by omega) with ht | ht
    · rw [ht] at hg'
      rcases own_msg E hW htot hi0 hA hg' with h | ⟨hp, h⟩
      · exact .inr (.inl h)
      · exact .inr (.inr (.inr (.inl ⟨hp, h⟩)))
    · rw [ht] at hg'
      rcases own_msg E hW htot hi1 hB hg' with h | ⟨hp, h⟩
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr (.inr ⟨hp, h⟩)))
  have hrT : ∀ u y, c.mem.read? P.top u = some y → T A B u := by
    intro u y h
    by_cases h0 : u = 0
    · exact .inl h0
    · obtain ⟨wm, hg, hl, -⟩ := get?_of_read? h0 h
      exact hmT u wm hg hl
  have hno' : ∀ u, T A B u → ∀ a b, NoTopIn P c.mem a b → a < u → u < b → False := by
    intro u hu a b hn h1 h2
    rcases hTm u hu with h | ⟨wm, hg, hl⟩
    · omega_t
    · exact hn u wm h1 h2 hg hl
  -- the side facts
  have side : ∀ (w i : Nat) (X : Side) (y y' : Val) (tX trX : Time), w < 2 → i < c.threads.size →
      RawSide P w c.mem (rF i) X → X.y = BitVec.setWidth 64 y →
      trX < X.p → c.mem.read? P.top trX = some y' → BitVec.setWidth 64 y' = BitVec.setWidth 64 y →
      NoTopIn P c.mem trX X.p → SideOK val A B X := by
    intro w i X y y' tX trX hw hi hX hy htr hr hyy hn
    refine ⟨Nat.pos_of_ne_zero (get?_ne_zero hX.pm), by rw [hval (read?_of_get? hX.pm), hX.n]; exact sw64_nv P w,
      ⟨trX, htr, hrT _ _ hr, by rw [hval hr, hyy, hy], fun u hu h1 h2 => hno' u hu _ _ hn h1 h2⟩, fun hp => ?_,
      fun hp => ?_⟩
    · obtain ⟨h0, h1, h2, ⟨y0, h3, h4⟩, ⟨y1, h5, h6⟩, h7, h8, h9, tl, u, h10, h11, h12⟩ := hX.pop hp
      refine ⟨h0, h1, h2, hrT _ _ h3, hrT _ _ h5, by rw [hval h3, h4], by rw [hval h5, h6], h7, ?_, ?_, ?_, ?_⟩
      · intro u' hu' h1' h2'
        rcases hTm u' hu' with h | ⟨wm, hg, hl⟩
        · omega_t
        · have ht := h8 u' wm h1' h2' hg hl
          have hg' : c.mem.get? u' = some ⟨P.top, wm.val, w⟩ := by rw [hg, ← hl, ← ht]
          rcases own_msg E hW htot hi hX hg' with h | ⟨-, h⟩ <;> omega_t
      · rw [hval (read?_of_get? h9)]; simp
      · intro hv hle
        rw [hAy]
        rw [← h11]; congr 1
        have hl : (⟨X.v + 8, 8⟩ : Loc) = P.nd 0 := by rw [hv, show A.n = P.n 0 from hA.n]; rfl
        rw [hl] at h10 h12
        have hle' : A.p ≤ X.tr0 := hle
        exact slot_read E hno hsA hqdA hXA hmA h10 h12 (by omega_t)
      · intro hv hle
        rw [hBy]
        rw [← h11]; congr 1
        have hl : (⟨X.v + 8, 8⟩ : Loc) = P.nd 1 := by rw [hv, show B.n = P.n 1 from hB.n]; rfl
        rw [hl] at h10 h12
        have hle' : B.p ≤ X.tr0 := hle
        exact slot_read E hno hsB hqdB hXB hmB h10 h12 (by omega_t)
    · obtain ⟨-, r, y0, h1, h2, h3⟩ := hX.cbz hp
      exact ⟨r, hrT _ _ h2, h1, by rw [hval h2, h3]⟩
  have hne : ∀ {u u' : Time} {v v' : Val}, c.mem.get? u = some ⟨P.top, v, 0⟩ →
      c.mem.get? u' = some ⟨P.top, v', 1⟩ → u ≠ u' := by
    intro u u' v v' h h' he
    rw [he, h'] at h
    cases h
  have H : HistOK val A B := by
    refine ⟨by rw [hval (show c.mem.read? P.top 0 = some (c.mem.initVal P.top) by simp [Memory.read?]), hT0]; rfl,
      ?_, by rw [hA.n]; exact hL.n_nz 0 (by decide), by rw [hB.n]; exact hL.n_nz 1 (by decide), hne hA.pm hB.pm, fun ha hb => ?_, fun ha => ?_,
      fun hb => ?_, side 0 i0 A yA yA' tA trA (by decide) hi0 hA hAy htrA hrA hyA hnA,
      side 1 i1 B yB yB' tB trB (by decide) hi1 hB hBy htrB hrB hyB hnB⟩
    · rw [hA.n, hB.n]; exact hL.n_ne
    · exact hne (hA.pop ha).2.2.2.2.2.2.2.1 (hB.pop hb).2.2.2.2.2.2.2.1
    · exact hne (hA.pop ha).2.2.2.2.2.2.2.1 hB.pm
    · exact Ne.symm (hne hA.pm (hB.pop hb).2.2.2.2.2.2.2.1)
  exact ⟨val, H⟩

/-- **The values the two threads popped.** -/
theorem final_values (E : Erase rF g TT c) (hW : GW P g) (hL : TLocs P) (hno : ∀ ts, ¬ Outstanding c ts)
    {i0 i1 : Nat} (hi0 : i0 < c.threads.size) (hi1 : i1 < c.threads.size) {v0 v1 : BitVec 64}
    (h0 : DoneR P 0 c.mem (rF i0) v0) (h1 : DoneR P 1 c.mem (rF i1) v1) :
    (v0 = P.n 0 ∧ v1 = P.n 1) ∨ (v0 = P.n 1 ∧ v1 = P.n 0) := by
  have htot : (total rF g c).acq P.top 0 = 1 := total_acq_of_ge' E hi0 h0.1
  have hT0 : c.mem.initVal P.top = 0 := h0.2.1
  obtain ⟨A0, hA, hAv⟩ := rawSide_of_done h0.2.2
  obtain ⟨B0, hB, hBv⟩ := rawSide_of_done h1.2.2
  obtain ⟨⟨sA, hsA, -, hpA⟩, -⟩ := forms_of_raw E hW htot hi0 hA
  obtain ⟨⟨sB, hsB, -, hpB⟩, -⟩ := forms_of_raw E hW htot hi1 hB
  obtain ⟨-, hqdA, -, ⟨yA, tA, hXA, hmA, htA, trA, yA', htrA, hrA, hyA, hnA⟩, -⟩ := hpA
  obtain ⟨-, hqdB, -, ⟨yB, tB, hXB, hmB, htB, trB, yB', htrB, hrB, hyB, hnB⟩, -⟩ := hpB
  obtain ⟨val, H⟩ := final_core (A := { A0 with y := BitVec.setWidth 64 yA })
    (B := { B0 with y := BitVec.setWidth 64 yB }) E hW hL hno hi0 hi1 htot hT0 (hA.setY _) (hB.setY _) hsA hsB
    hqdA hXA hmA htA htrA hrA hyA hnA rfl hqdB hXB hmB htB htrB hrB hyB hnB rfl
  obtain ⟨hpa, hpb, hv⟩ := hist_ok H
  have e0 : A0.v = v0 := hAv hpa
  have e1 : B0.v = v1 := hBv hpb
  have n0 : A0.n = P.n 0 := hA.n
  have n1 : B0.n = P.n 1 := hB.n
  rw [← e0, ← e1, ← n0, ← n1]
  exact hv

end Final

end Kraken.Promising.SLR.EnvG.Treiber2
