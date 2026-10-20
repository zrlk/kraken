/-
**The protocol environment of
`ticketlock2.kl` and its per-thread context invariant.** ISA-neutral.

The worker of `Kraken/Examples/LockFree/X64/ticketlock2.kl` takes a ticket
with `lock xaddl` on `next` (`x`), spins on `owner` (`o`) until it holds its
ticket, increments `counter` (`c`) by a load and a store, and releases with
an unlocked `incl (owner)` (a load and a store). The unlocked release is not
an atomic increment, so the proof does not go through a dispenser of `owner`:
it tracks, per thread, the timestamps of its accesses in the Promising memory
(route B).

- `tk2Env x o c`: the thread's protocol as an environment. Its state
  `TkSt` is a phase `k` (`0` before the ticket, `1` spinning with ticket `t`,
  `2` holding the lock, `3` after reading `e` from the counter, `4` after
  writing `e + 1`, `5` after reading `u` from the owner, `6` after writing
  `u + 1`) and the values `t e u` read so far (low words, `lo`).
- `Hist`, `Lv`, `Facts`: the timestamps of the thread's accesses and what
  the memory and the thread's views say about them, phase by phase (each
  phase adds the facts `Lv k` of its access; `Facts` also has the forwarding
  conditions the reads need).
- `Rec`, `Bk`: the thread's recorded writes (the RMW's write, the counter
  store, the owner store, by phase), and the bookkeeping of its own messages
  (each is an outstanding promise or a recorded write, never both).
- `Fr M0 i`: the frame of one instruction (the memory extends `M0`, every
  new message is the thread's).
- **`runSim`**: the per-access obligations `RunSim` (`EnvG/TicketX2Run.lean`)
  of `tk2Env` under `Arch.tso` for `JC M0 = JTk ∧ Fr M0`, with
  `Bk.write` for the fulfil and fresh-write cases (the message written has
  the store's value by the step semantics, `writeSuccs_spec`, and becomes a
  recorded write).
-/
import Kraken.Promising.SLR.EnvG.TicketX2Run

namespace Kraken.Promising.SLR.EnvG.TicketX2

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvSpike

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-! ## The environment -/

/-- The low word of a value. -/
abbrev lo (v : Val) : BitVec 32 := v.setWidth 32

/-- A low word plus one, as a value (what `lock xaddl $1` and `incl` write). -/
abbrev inc (u : BitVec 32) : Val := (u + 1).setWidth 128

/-- The protocol state of a thread: its phase and the words read so far. -/
structure TkSt where
  k : Nat
  t : BitVec 32
  e : BitVec 32
  u : BitVec 32

/-- The initial protocol state. -/
def TkSt.start : TkSt := ⟨0, 0, 0, 0⟩

/-- The protocol state after a load of `v`: in the spin, phase `2` if `v`
is the ticket; the counter's value in phase `2`; the owner's in phase `4`. -/
def TkSt.onLoad (g : TkSt) (v : Val) : TkSt :=
  if g.k = 1 then (if lo v = g.t then { g with k := 2 } else g)
  else if g.k = 2 then { g with k := 3, e := lo v }
  else { g with k := 5, u := lo v }

/-- **The protocol environment of the `ticketlock2` worker** on `next = x`,
`owner = o`, `counter = c` (4-byte words): one RMW on `x` writing the low
word plus one in phase `0`; plain loads of `o` in phases `1` and `4` and of
`c` in phase `2`; plain stores of `e + 1` to `c` in phase `3` and of `u + 1`
to `o` in phase `5`; fences anywhere, changing nothing. -/
def tk2Env (x o c : BitVec 64) : SharedEnv where
  State := TkSt
  ok a g := match a with
    | .rmw _ addr n op => g.k = 0 ∧ addr = x ∧ n = 4 ∧ ∀ old, op old = some (inc (lo old))
    | .load k xcl addr n => k = .plain ∧ xcl = false ∧ n = 4 ∧
        (((g.k = 1 ∨ g.k = 4) ∧ addr = o) ∨ (g.k = 2 ∧ addr = c))
    | .store k xcl addr n v => k = .plain ∧ xcl = false ∧ n = 4 ∧
        ((g.k = 3 ∧ addr = c ∧ v = inc g.e) ∨ (g.k = 5 ∧ addr = o ∧ v = inc g.u))
    | .fence _ => True
  step a g r g' := match a, r with
    | .rmw .., old => g' = { g with k := 1, t := lo old }
    | .load .., v => g' = g.onLoad v
    | .store .., _ => g' = { g with k := g.k + 1 }
    | .fence _, _ => g' = g

variable {x o c : BitVec 64}

instance : (tk2Env x o c).Skips := ⟨fun _ _ => ⟨trivial, fun _ h => h⟩⟩

@[simp] theorem tk2Env_ok_load {k : LoadKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {g : TkSt} :
    (tk2Env x o c).ok (.load k xcl addr n) g ↔ k = .plain ∧ xcl = false ∧ n = 4 ∧
      (((g.k = 1 ∨ g.k = 4) ∧ addr = o) ∨ (g.k = 2 ∧ addr = c)) := Iff.rfl

@[simp] theorem tk2Env_ok_store {k : StoreKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {v : Val} {g : TkSt} :
    (tk2Env x o c).ok (.store k xcl addr n v) g ↔ k = .plain ∧ xcl = false ∧ n = 4 ∧
      ((g.k = 3 ∧ addr = c ∧ v = inc g.e) ∨ (g.k = 5 ∧ addr = o ∧ v = inc g.u)) := Iff.rfl

@[simp] theorem tk2Env_ok_rmw {k : RmwKind} {addr : BitVec 64} {n : Nat} {op : Val → Option Val} {g : TkSt} :
    (tk2Env x o c).ok (.rmw k addr n op) g ↔ g.k = 0 ∧ addr = x ∧ n = 4 ∧ ∀ old, op old = some (inc (lo old)) :=
  Iff.rfl

@[simp] theorem tk2Env_step_load {k : LoadKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {v : Val} {g g' : TkSt} :
    (tk2Env x o c).step (.load k xcl addr n) g v g' ↔ g' = g.onLoad v := Iff.rfl

@[simp] theorem tk2Env_step_store {k : StoreKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {v : Val} {r : Bool}
    {g g' : TkSt} : (tk2Env x o c).step (.store k xcl addr n v) g r g' ↔ g' = { g with k := g.k + 1 } := Iff.rfl

@[simp] theorem tk2Env_step_rmw {k : RmwKind} {addr : BitVec 64} {n : Nat} {op : Val → Option Val} {old : Val}
    {g g' : TkSt} : (tk2Env x o c).step (.rmw k addr n op) g old g' ↔ g' = { g with k := 1, t := lo old } := Iff.rfl

/-! ## The per-thread invariant -/

/-- The timestamps of a thread's accesses: the RMW's read `a` and write
`a'`, the spin's last read `s`, the counter's read `r` and write `w`, the
owner's read `q` and write `o'`. -/
structure Hist where
  a : Time
  a' : Time
  s : Time
  r : Time
  w : Time
  q : Time
  o' : Time

/-- **The facts of phase `n`** about thread `i`'s accesses in memory `M`
with views `V`. -/
def Lv (x o c : BitVec 64) (i : Nat) (M : Memory) (V : Views) (g : TkSt) (h : Hist) : Nat → Prop
  | 1 => (∃ v, M.read? ⟨x, 4⟩ h.a = some v ∧ lo v = g.t) ∧ M.get? h.a' = some ⟨⟨x, 4⟩, inc g.t, i⟩ ∧
      h.a < h.a' ∧ ∀ ts m, h.a < ts → ts < h.a' → M.get? ts = some m → m.loc = ⟨x, 4⟩ → m.tid = i
  | 2 => (∃ v, M.read? ⟨o, 4⟩ h.s = some v ∧ lo v = g.t) ∧ h.s ≤ V.vrNew ∧ h.s ≤ V.vrOld ∧
      h.s ≤ V.getCoh ⟨o, 4⟩
  | 3 => (∃ v, M.read? ⟨c, 4⟩ h.r = some v ∧ lo v = g.e) ∧ NoWriteInX M ⟨c, 4⟩ h.r h.s ∧ h.s ≤ M.last ∧
      h.r ≤ V.getCoh ⟨c, 4⟩
  | 4 => M.get? h.w = some ⟨⟨c, 4⟩, inc g.e, i⟩ ∧ h.r < h.w ∧ h.s < h.w ∧ h.w ≤ V.vwOld
  | 5 => (∃ v, M.read? ⟨o, 4⟩ h.q = some v ∧ lo v = g.u) ∧ h.s ≤ h.q ∧ h.q ≤ V.getCoh ⟨o, 4⟩
  | 6 => M.get? h.o' = some ⟨⟨o, 4⟩, inc g.u, i⟩ ∧ h.q < h.o' ∧ h.w < h.o'
  | _ => True

/-- The facts of every phase reached, and no forwarding from `o` before the
owner's store nor from `c` before the counter's. -/
def Facts (x o c : BitVec 64) (i : Nat) (M : Memory) (V : Views) (g : TkSt) (h : Hist) : Prop :=
  (∀ n, n ≤ g.k → Lv x o c i M V g h n) ∧ (g.k ≤ 4 → V.getFwd ⟨o, 4⟩ = none) ∧
    (g.k ≤ 2 → V.getFwd ⟨c, 4⟩ = none)

/-- The thread's recorded writes, by phase. -/
def Rec (g : TkSt) (h : Hist) (ts : Time) : Prop :=
  (1 ≤ g.k ∧ ts = h.a') ∨ (4 ≤ g.k ∧ ts = h.w) ∨ (6 ≤ g.k ∧ ts = h.o')

/-- **The bookkeeping of thread `i`'s messages**: its promises are distinct
messages of its own; each of its messages is an outstanding promise or a
recorded write, and no recorded write is outstanding. -/
structure Bk (i : Nat) (M : Memory) (P : List Time) (g : TkSt) (h : Hist) : Prop where
  nodup : P.Nodup
  prom : ∀ ts ∈ P, ∃ m, M.get? ts = some m ∧ m.tid = i
  own : ∀ ts m, M.get? ts = some m → m.tid = i → ts ∈ P ∨ Rec g h ts
  recNP : ∀ ts, Rec g h ts → ts ∉ P

/-- **The per-thread invariant**: some history with the phase's facts and
the bookkeeping. -/
def JTk (x o c : BitVec 64) (i : Nat) (g : TkSt) (V : Views) (P : List Time) (M : Memory) : Prop :=
  ∃ h, Facts x o c i M V g h ∧ Bk i M P g h

/-- The frame of one instruction of thread `i` from memory `M0`. -/
def Fr (i : Nat) (M0 M : Memory) : Prop :=
  M0.Prefix M ∧ ∀ ts m, M0.last < ts → M.get? ts = some m → m.tid = i

/-- The context invariant of one instruction from memory `M0`. -/
def JC (x o c : BitVec 64) (i : Nat) (M0 : Memory) (g : TkSt) (cx : Ctx) : Prop :=
  JTk x o c i g cx.views cx.prom cx.mem ∧ Fr i M0 cx.mem

/-! ## Stability -/

variable {i : Nat}

theorem get?_down {M M' : Memory} (hp : M.Prefix M') {ts : Time} (hts : ts ≤ M.last) {m : Msg}
    (hg : M'.get? ts = some m) : M.get? ts = some m := by
  rwa [hp.get? hts] at hg

theorem Lv_mono {M M' : Memory} {V V' : Views} {g : TkSt} {h : Hist} (hp : M.Prefix M') (hv : VLe V V') :
    ∀ n, Lv x o c i M V g h n → Lv x o c i M' V' g h n
  | 0, _ => trivial
  | 1, ⟨⟨v, hr, hv'⟩, h2, h3, h4⟩ =>
    ⟨⟨v, read?_prefix hp hr, hv'⟩, get?_prefix hp h2, h3, fun ts m h1 h2' hg hl =>
      h4 ts m h1 h2' (get?_down hp (Nat.le_trans (Nat.le_of_lt h2') (Memory.last_le_of_get?_eq_some M h2)) hg) hl⟩
  | 2, ⟨⟨v, hr, hv'⟩, h2, h3, h4⟩ =>
    ⟨⟨v, read?_prefix hp hr, hv'⟩, Nat.le_trans h2 hv.vrNew, Nat.le_trans h3 hv.vrOld, Nat.le_trans h4 (hv.coh _)⟩
  | 3, ⟨⟨v, hr, hv'⟩, h2, h3, h4⟩ =>
    ⟨⟨v, read?_prefix hp hr, hv'⟩, h2.prefix hp h3, Nat.le_trans h3 hp.last_le, Nat.le_trans h4 (hv.coh _)⟩
  | 4, ⟨h1, h2, h3, h4⟩ => ⟨get?_prefix hp h1, h2, h3, Nat.le_trans h4 hv.vwOld⟩
  | 5, ⟨⟨v, hr, hv'⟩, h2, h3⟩ => ⟨⟨v, read?_prefix hp hr, hv'⟩, h2, Nat.le_trans h3 (hv.coh _)⟩
  | 6, ⟨h1, h2⟩ => ⟨get?_prefix hp h1, h2⟩
  | _ + 7, _ => trivial

/-- The facts survive memory extension and view growth with the forwarding
of `o` and `c` unchanged. -/
theorem Facts.mono {M M' : Memory} {V V' : Views} {g : TkSt} {h : Hist} (hF : Facts x o c i M V g h)
    (hp : M.Prefix M') (hv : VLe V V') (hfo : V'.getFwd ⟨o, 4⟩ = V.getFwd ⟨o, 4⟩)
    (hfc : V'.getFwd ⟨c, 4⟩ = V.getFwd ⟨c, 4⟩) : Facts x o c i M' V' g h :=
  ⟨fun n hn => Lv_mono hp hv n (hF.1 n hn), fun hk => hfo ▸ hF.2.1 hk, fun hk => hfc ▸ hF.2.2 hk⟩

/-- **The next phase**: the facts of the phases reached survive (the new
state and history agree on them), and the new phase's facts hold. -/
theorem Facts.next {M M' : Memory} {V V' : Views} {g g' : TkSt} {h h' : Hist} (hF : Facts x o c i M V g h)
    (hp : M.Prefix M') (hv : VLe V V') (hk : g'.k = g.k + 1)
    (hlow : ∀ n, n ≤ g.k → Lv x o c i M' V' g' h' n = Lv x o c i M' V' g h n)
    (hnew : Lv x o c i M' V' g' h' (g.k + 1)) (hfo : g'.k ≤ 4 → V'.getFwd ⟨o, 4⟩ = none)
    (hfc : g'.k ≤ 2 → V'.getFwd ⟨c, 4⟩ = none) : Facts x o c i M' V' g' h' := by
  refine ⟨fun n hn => ?_, hfo, hfc⟩
  by_cases hle : n ≤ g.k
  · rw [hlow n hle]; exact Lv_mono hp hv n (hF.1 n hle)
  · obtain rfl : n = g.k + 1 := by omega
    exact hnew

/-- The bookkeeping with the same recorded writes. -/
theorem Bk.congr {M : Memory} {P : List Time} {g g' : TkSt} {h h' : Hist} (hB : Bk i M P g h)
    (hrec : ∀ ts, Rec g' h' ts ↔ Rec g h ts) : Bk i M P g' h' :=
  ⟨hB.nodup, hB.prom, fun ts m hg ht => (hB.own ts m hg ht).imp id (hrec ts).mpr,
    fun ts hr => hB.recNP ts ((hrec ts).mp hr)⟩

/-- **The bookkeeping across one write of thread `i`** at timestamp `w`
(`writeSuccs_spec`): the message at `w` is the thread's; either `w` was an
outstanding promise and leaves the promises (fulfil), or `w` is fresh at the
end of the memory; in both cases `w` becomes a recorded write. -/
theorem Bk.write {M M' : Memory} {P P' : List Time} {g g' : TkSt} {h h' : Hist} {w : Time} {l : Loc} {v : Val}
    (hB : Bk i M P g h) (hp : M.Prefix M') (hw : M'.get? w = some ⟨l, v, i⟩)
    (hnew : ∀ ts, M.last < ts → ts ≤ M'.last → ts = w)
    (hP : (w ∈ P ∧ P' = P.erase w) ∨ (w = M.last + 1 ∧ P' = (P ++ [w]).erase w))
    (hrec : ∀ ts, Rec g' h' ts ↔ Rec g h ts ∨ ts = w) : Bk i M' P' g' h' := by
  have hPle : ∀ ts ∈ P, ts ≤ M.last := fun ts hts => by
    obtain ⟨m, hm, -⟩ := hB.prom ts hts; exact Memory.last_le_of_get?_eq_some M hm
  -- the new promises: those of `P` but `w`, and `w` is not among them
  have hP' : P' = P.erase w ∧ (w ∈ P ∨ w ∉ P) := by
    rcases hP with ⟨hw, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨rfl, .inl hw⟩
    · have hn : M.last + 1 ∉ P := fun hm => by have := hPle _ hm; omega_t
      refine ⟨?_, .inr hn⟩
      rw [List.erase_append_right _ hn]
      simp [List.erase_of_not_mem hn]
  obtain ⟨rfl, -⟩ := hP'
  have hmem : ∀ ts, ts ∈ P.erase w ↔ ts ≠ w ∧ ts ∈ P := fun ts => hB.nodup.mem_erase_iff
  refine ⟨hB.nodup.erase w, fun ts hts => ?_, fun ts m hg ht => ?_, fun ts hr => ?_⟩
  · obtain ⟨m, hm, hmt⟩ := hB.prom ts ((hmem ts).mp hts).2
    exact ⟨m, get?_prefix hp hm, hmt⟩
  · by_cases hts : ts ≤ M.last
    · rcases hB.own ts m (get?_down hp hts hg) ht with hin | hr
      · by_cases hne : ts = w
        · exact .inr ((hrec ts).mpr (.inr hne))
        · exact .inl ((hmem ts).mpr ⟨hne, hin⟩)
      · exact .inr ((hrec ts).mpr (.inl hr))
    · exact .inr ((hrec ts).mpr (.inr (hnew ts (by omega_t) (Memory.last_le_of_get?_eq_some M' hg))))
  · intro hin
    rcases (hrec ts).mp hr with hr | rfl
    · exact hB.recNP ts hr ((hmem ts).mp hin).2
    · exact ((hmem ts).mp hin).1 rfl

/-- The frame across a write of thread `i` at `w`. -/
theorem Fr.write {M0 M M' : Memory} {w : Time} {l : Loc} {v : Val} (hF : Fr i M0 M) (hp : M.Prefix M')
    (hw : M'.get? w = some ⟨l, v, i⟩) (hnew : ∀ ts, M.last < ts → ts ≤ M'.last → ts = w) : Fr i M0 M' := by
  refine ⟨hF.1.trans hp, fun ts m h0 hg => ?_⟩
  by_cases hts : ts ≤ M.last
  · exact hF.2 ts m h0 (get?_down hp hts hg)
  · obtain rfl := hnew ts (by omega_t) (Memory.last_le_of_get?_eq_some M' hg)
    rw [hw] at hg; cases hg; rfl

/-! ## One access -/

/-- A read at a timestamp `s` that is a write to `l` (or the initial one),
with no write to `l` in `(q, b]` and `s ≤ b`, is at most `q`. -/
theorem le_of_read_noWrite {M : Memory} {l : Loc} {s q b : Time} {v : Val} (hs : M.read? l s = some v)
    (hn : NoWriteInX M l q b) (hsb : s ≤ b) : s ≤ q := by
  refine Nat.le_of_not_lt fun hlt => ?_
  unfold Memory.read? at hs
  split at hs
  · omega_t
  split at hs
  · rename_i w hw
    split at hs
    · rename_i hl
      exact hn s w hlt hsb hw (by simpa using hl)
    · cases hs
  · cases hs

theorem tso_load : Arch.tso.loadKind .plain = .acqPc := rfl
theorem tso_store : Arch.tso.storeKind .plain = .rel := rfl

/-- A write's pre-view under `Arch.tso` for a plain store bounds `vrOld` and
`vwOld`. -/
theorem writePre_tso {iv : InstrViews} {cx : Ctx} {extra : View} :
    cx.views.vrOld ≤ writePre Arch.tso iv cx .plain extra ∧ cx.views.vwOld ≤ writePre Arch.tso iv cx .plain extra := by
  unfold writePre
  simp only [show (Arch.tso.storeKind StoreKind.plain == StoreKind.rel) = true from rfl, ite_true]
  constructor <;> omega_t

theorem writeSuccs_vle {A : Arch} {tid : Nat} {iv : InstrViews} {c c' : Ctx} {k : StoreKind} {xcl : Bool}
    {l : Loc} {v : Val} {tr : Option Time} {extra : View} (hk : A.storeKind k ≠ .nt)
    (hc : c' ∈ writeSuccs A tid iv c k xcl l v tr extra) : VLe c.views c'.views := by
  obtain ⟨w, -, -, -, -, -, -, hcoh, hro, hrn, hwo, -⟩ := writeSuccs_spec A tid iv hc
  refine ⟨hrn ▸ Nat.le_refl _, hro ▸ Nat.le_refl _, ?_, fun l' => ?_⟩
  · rw [hwo hk]; omega_t
  · rw [hcoh]; exact getCoh_le_setCoh _ _ _ _

theorem getFwd_of_fwdb {V V' : Views} (h : V'.fwdb = V.fwdb) (l : Loc) : V'.getFwd l = V.getFwd l := by
  simp only [Views.getFwd, h]

theorem getCoh_setCoh_self (V : Views) (l : Loc) (t : View) : t ≤ (V.setCoh l t).getCoh l := by
  rw [Views.getCoh_setCoh]; simp only [ite_true]; omega_t

/-- The lower phases' facts do not see the new phase's state and history
fields. -/
local macro "rec_tac" : tactic =>
  `(tactic| (simp only [Rec]; constructor <;> intro hh <;> omega_t))

local macro "lv_low" : tactic =>
  `(tactic| (intro n hn; rcases n with _ | _ | _ | _ | _ | _ | n <;> first | rfl | omega))

theorem loc_ne {a b : BitVec 64} (h : a ≠ b) : (⟨a, 4⟩ : Loc) ≠ ⟨b, 4⟩ := fun e => h (congrArg Loc.addr e)

/-- **The per-access obligations of `tk2Env` under `Arch.tso`** for the
context invariant `JC M0` of thread `i`: each access the protocol permits,
run by the machine, keeps `JTk` at the protocol's answer and the frame. -/
theorem runSim (hxo : x ≠ o) (hxc : x ≠ c) (hoc : o ≠ c) (M0 : Memory) :
    RunSim Arch.tso i (tk2Env x o c) (JC x o c i M0) where
  load := by
    intro k xcl addr n g iv cx hok hJ y hy
    obtain ⟨rfl, rfl, hn4, hcase⟩ := hok
    subst n
    obtain ⟨⟨h, hF, hB⟩, hFr⟩ := hJ
    obtain ⟨hr, hnw, -, hmem, hprom, ν, hν, hcoh, hro, hrn, -, hfw⟩ := readSuccs_spec Arch.tso iv hy
    have hvle := readSuccs_vle Arch.tso iv hy
    have hfo := getFwd_of_fwdb hfw ⟨o, 4⟩
    have hfc := getFwd_of_fwdb hfw ⟨c, 4⟩
    simp only [tso_load, LoadKind.isAcquire, ite_true, Bool.false_eq_true, ite_false] at hro hrn
    refine ⟨g.onLoad y.2.1, rfl, ?_, by rw [hmem]; exact hFr⟩
    show JTk x o c i _ y.2.2.views y.2.2.prom y.2.2.mem
    rw [hmem, hprom]
    have hp := Memory.Prefix.refl cx.mem
    rcases hcase with ⟨hk | hk, ha⟩ | ⟨hk, ha⟩ <;> subst addr
    · by_cases hv : lo y.2.1 = g.t
      · have hg : g.onLoad y.2.1 = { g with k := 2 } := by
          simp (config := { decide := true }) only [TkSt.onLoad, hk, hv, ↓reduceIte]
        rw [hg]
        have hs : y.1 ≤ ν := hν (hF.2.1 (by omega))
        refine ⟨{ h with s := y.1 }, hF.next hp hvle (by simp [hk]) (by lv_low) ?_
          (fun _ => hfo.trans (hF.2.1 (by omega))) (fun _ => hfc.trans (hF.2.2 (by omega))),
          hB.congr (fun ts => by rec_tac)⟩
        rw [hk]
        exact ⟨⟨_, hr, hv⟩, by rw [hrn]; omega_t, by rw [hro]; omega_t,
          by rw [hcoh]; exact Nat.le_trans hs (getCoh_setCoh_self _ _ _)⟩
      · have hg : g.onLoad y.2.1 = g := by
          simp (config := { decide := true }) only [TkSt.onLoad, hk, hv, ↓reduceIte]; try rfl
        rw [hg]
        exact ⟨h, hF.mono hp hvle hfo hfc, hB⟩
    · have hg : g.onLoad y.2.1 = { g with k := 5, u := lo y.2.1 } := by
        simp (config := { decide := true }) only [TkSt.onLoad, hk, ↓reduceIte]
      rw [hg]
      have hs : y.1 ≤ ν := hν (hF.2.1 (by omega))
      obtain ⟨⟨v2, hs2, -⟩, -, -, hso⟩ := hF.1 2 (by omega)
      refine ⟨{ h with q := y.1 }, hF.next hp hvle (by simp [hk]) (by lv_low) ?_
        (fun h' => absurd h' (by simp)) (fun h' => absurd h' (by simp)),
        hB.congr (fun ts => by rec_tac)⟩
      rw [hk]
      exact ⟨⟨_, hr, rfl⟩, le_of_read_noWrite hs2 hnw (by omega_t),
        by rw [hcoh]; exact Nat.le_trans hs (getCoh_setCoh_self _ _ _)⟩
    · have hg : g.onLoad y.2.1 = { g with k := 3, e := lo y.2.1 } := by
        simp (config := { decide := true }) only [TkSt.onLoad, hk, ↓reduceIte]
      rw [hg]
      have hs : y.1 ≤ ν := hν (hF.2.2 (by omega))
      obtain ⟨⟨v2, hs2, -⟩, hsn, -, -⟩ := hF.1 2 (by omega)
      refine ⟨{ h with r := y.1 }, hF.next hp hvle (by simp [hk]) (by lv_low) ?_
        (fun _ => hfo.trans (hF.2.1 (by omega))) (fun h' => absurd h' (by simp)),
        hB.congr (fun ts => by rec_tac)⟩
      rw [hk]
      exact ⟨⟨_, hr, rfl⟩, hnw.mono (by omega_t), read?_le_last hs2,
        by rw [hcoh]; exact Nat.le_trans hs (getCoh_setCoh_self _ _ _)⟩
  store := by
    intro k xcl addr n v g iv cx hok hJ
    obtain ⟨rfl, rfl, hn4, hcase⟩ := hok
    subst n
    refine ⟨fun c' hc' => ?_, fun h => absurd h (by simp)⟩
    obtain ⟨⟨h, hF, hB⟩, hFr⟩ := hJ
    obtain ⟨w, hlt, -, hget, hpre, hnew, hP, hcoh, -, -, hwo, hfw⟩ := writeSuccs_spec Arch.tso i iv hc'
    have hvle := writeSuccs_vle (by decide) hc'
    have hwo' := hwo (by decide)
    have hwp := writePre_tso (iv := iv) (cx := cx) (extra := 0)
    refine ⟨{ g with k := g.k + 1 }, rfl, ?_, hFr.write hpre hget hnew⟩
    rcases hcase with ⟨hk, ha, rfl⟩ | ⟨hk, ha, rfl⟩ <;> subst addr
    · obtain ⟨-, -, hso, -⟩ := hF.1 2 (by omega)
      obtain ⟨-, -, -, hrc⟩ := hF.1 3 (by omega)
      refine ⟨{ h with w := w }, hF.next hpre hvle rfl (by lv_low) ?_
        (fun _ => (hfw _ (loc_ne hoc)).trans (hF.2.1 (by omega))) (fun h' => absurd h' (by simp [hk])),
        hB.write hpre hget hnew hP (fun ts => by rec_tac)⟩
      rw [hk]
      exact ⟨hget, by omega_t, by omega_t, by rw [hwo']; omega_t⟩
    · obtain ⟨-, -, -, hww⟩ := hF.1 4 (by omega)
      obtain ⟨-, -, hqo⟩ := hF.1 5 (by omega)
      refine ⟨{ h with o' := w }, hF.next hpre hvle rfl (by lv_low) ?_
        (fun h' => absurd h' (by simp [hk])) (fun h' => absurd h' (by simp [hk])),
        hB.write hpre hget hnew hP (fun ts => by rec_tac)⟩
      rw [hk]
      exact ⟨hget, by omega_t, by omega_t⟩
  fence := by
    intro k g cx _ hJ
    obtain ⟨⟨h, hF, hB⟩, hFr⟩ := hJ
    obtain ⟨hm, hpr⟩ := fenceStep_mem_prom cx k
    refine ⟨g, rfl, ⟨h, ?_, ?_⟩, ?_⟩
    · rw [hm]
      exact hF.mono (Memory.Prefix.refl _) (fenceStep_vle cx k) (getFwd_of_fwdb (fenceStep_fwdb cx k) _)
        (getFwd_of_fwdb (fenceStep_fwdb cx k) _)
    · rw [hm, hpr]; exact hB
    · rw [hm]; exact hFr
  rmw := by
    intro k noRet addr n op g iv cx hok hJ y hy
    obtain ⟨hk0, ha, hn4, hop⟩ := hok
    subst addr n
    refine ⟨fun hn => absurd (hop _) (by rw [hn]; simp), fun new hnew c' hc' => ?_⟩
    have hnv : new = inc (lo y.2.1) := by rw [hop] at hnew; exact (Option.some.inj hnew).symm
    subst hnv
    obtain ⟨⟨h, hF, hB⟩, hFr⟩ := hJ
    obtain ⟨hm0, hp0⟩ := fenceOptCtx_memProm Arch.tso cx
    obtain ⟨hr, -, -, hmem, hprom, -, -, -, -, -, -, hfw1⟩ := readSuccs_spec Arch.tso iv hy
    obtain ⟨w, -, hat, hget, hpre, hnew, hP, -, -, -, -, hfw2⟩ := writeSuccs_spec Arch.tso i iv hc'
    obtain ⟨hm3, hp3⟩ := rmwAfter_mem_prom Arch.tso k noRet ⟨x, 4⟩ c'
    have hvle : VLe cx.views (rmwAfter Arch.tso k noRet ⟨x, 4⟩ c').views :=
      ((fenceOptCtx_vle Arch.tso cx).trans (readSuccs_vle Arch.tso iv hy)).trans
        ((writeSuccs_vle (by cases k <;> decide) hc').trans (rmwAfter_vle Arch.tso k noRet ⟨x, 4⟩ c'))
    have hfw : ∀ l, l ≠ ⟨x, 4⟩ → (rmwAfter Arch.tso k noRet ⟨x, 4⟩ c').views.getFwd l = cx.views.getFwd l :=
      fun l hl => by
        rw [getFwd_of_fwdb (rmwAfter_fwdb Arch.tso k noRet ⟨x, 4⟩ c') l, hfw2 l hl, getFwd_of_fwdb hfw1 l,
          getFwd_of_fwdb (fenceOptCtx_fwdb Arch.tso cx) l]
    have hM : y.2.2.mem = cx.mem := hmem.trans hm0
    have hPr : y.2.2.prom = cx.prom := hprom.trans hp0
    rw [hM] at hpre hnew hat
    rw [hm0] at hr
    rw [hM, hPr] at hP
    refine ⟨{ g with k := 1, t := lo y.2.1 }, rfl, ?_, by rw [hm3]; exact hFr.write hpre hget hnew⟩
    show JTk x o c i _ (rmwAfter Arch.tso k noRet ⟨x, 4⟩ c').views (rmwAfter Arch.tso k noRet ⟨x, 4⟩ c').prom
      (rmwAfter Arch.tso k noRet ⟨x, 4⟩ c').mem
    rw [hm3, hp3]
    refine ⟨{ h with a := y.1, a' := w }, hF.next hpre hvle (by simp [hk0]) (by lv_low) ?_
      (fun _ => (hfw _ (loc_ne (Ne.symm hxo))).trans (hF.2.1 (by omega)))
      (fun _ => (hfw _ (loc_ne (Ne.symm hxc))).trans (hF.2.2 (by omega))),
      hB.write hpre hget hnew hP (fun ts => by rec_tac)⟩
    rw [hk0]
    refine ⟨⟨_, read?_prefix hpre hr, rfl⟩, hget, (hat _ rfl).1, fun ts m h1 h2 hg hl => ?_⟩
    have hts : ts ≤ cx.mem.last := Nat.le_of_not_lt fun hlt =>
      absurd (hnew ts hlt (Memory.last_le_of_get?_eq_some _ hg)) (by omega_t)
    exact Memory.atomic_elim (hat _ rfl).2 hr ts m h1 h2 (get?_down hpre hts hg) hl

end Kraken.Promising.SLR.EnvG.TicketX2

#print axioms Kraken.Promising.SLR.EnvG.TicketX2.runSim
#print axioms Kraken.Promising.SLR.EnvG.TicketX2.Bk.write
