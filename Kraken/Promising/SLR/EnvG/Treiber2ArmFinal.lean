/-
Part 3: **the final clean erasure of
`treiber2_arm.kl`** gives the (unchanged) history layer's hypotheses
(`Treiber2.HistOK`, `EnvG/Treiber2Hist.lean`). ISA-neutral.

`treiber2`'s final layer (`EnvG/Treiber2Final.lean`) reads the forms of
`top`'s messages off their slots (`PushF`/`PopF` of the release predicate).
Here `top` carries nothing (`EnvG/Treiber2ArmGhost.lean`), so every fact is
the writer's own, kept in its resource and its final facts (`SideA`):

- its half of `top` and its write set of `top`: the initial message, its push
  `X.p` and, if it popped, its pop `X.q` (`wset`);
- its node's link and data word whole, with their maximal writes below its
  push (`KeptA`); the push `casl`'s read `tr` with only own messages of `top`
  strictly between `tr` and the push (`OwnIn`, from the RMW's atomicity);
- its pop facts (as `Treiber2.RawSide`) or its empty-stack read.

At a final configuration (no outstanding promise, the two threads the only
ones):

- the two halves make all of `top`, so every message of `top` is in one of
  the two write sets (`OwnWrites.msg_mem_pair`): `top`'s messages are the
  sides' `T` times;
- a message's writer tells which side it is (`own_side`), so `OwnIn` gives
  the adjacency of the push and the pop;
- a pushed node's link and data word, kept whole by their owner, are read at
  their frozen value by every read whose window covers the push
  (`OwnWrites.thread_read`).

`final_values_dataA`: the two threads' `X10` are the two nodes and each `X11`
the data word of the node it popped.
-/
import Kraken.Promising.SLR.EnvG.Treiber2ArmGhost
import Kraken.Promising.SLR.EnvG.Treiber2ArmOwn
import Kraken.Promising.SLR.EnvG.Treiber2Final

namespace Kraken.Promising.SLR.EnvG.Treiber2Arm

open Kraken Kraken.Promising
open Kraken.Promising.SLR.EnvG.Treiber2
open Kraken.Promising.SLR.EnvG.TreiberCommon (read?_of_get? get?_of_read?)
open Kraken.Promising.SLR.EnvG.OwnWrites (msg_mem_pair thread_read)

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-! ## Final facts -/

/-- **Only thread `w`'s messages of `top` strictly between `a` and `b`.** -/
def OwnIn (P : Params) (w : Nat) (m : Memory) (a b : Time) : Prop :=
  ∀ p wm, a < p → p < b → m.get? p = some wm → wm.loc = P.top → wm.tid = w

theorem OwnIn.mono {P : Params} {w : Nat} {m m' : Memory} (h : m.Prefix m') {a b : Time} (hb : b ≤ m.last)
    (hn : OwnIn P w m a b) : OwnIn P w m' a b := fun p wm h1 h2 hw =>
  hn p wm h1 h2 (Memory.get?_of_prefix_le h.2 (by omega_t) hw)

/-- **What a pusher keeps** at its push message `Pw` (link value `y`, 64
bits): the message; its node's link whole, its maximal write `(y', t)` below
`Pw` with `y'`'s 64 bits `y`; the push's read `tr < Pw` of a value with 64 bits
`y`, only own messages of `top` strictly between; its data word whole, its
maximal write below `Pw` with `D w`. -/
def KeptA (P : Params) (w : Nat) (m : Memory) (R : Res) (Pw : Time) (y : BitVec 64) : Prop :=
  m.get? Pw = some ⟨P.top, P.nv w, w⟩ ∧ (R.wr (P.nd w)).q = 1 ∧
    (∃ y' t, (R.wr (P.nd w)).X (y', t) ∧ (∀ p, (R.wr (P.nd w)).X p → p.2 ≤ t) ∧ t < Pw ∧
      BitVec.setWidth 64 y' = y) ∧
    (∃ tr y', tr < Pw ∧ m.read? P.top tr = some y' ∧ BitVec.setWidth 64 y' = y ∧ OwnIn P w m tr Pw) ∧
    (R.wr (P.dd w)).q = 1 ∧
    ∃ d t, (R.wr (P.dd w)).X (d, t) ∧ (∀ p, (R.wr (P.dd w)).X p → p.2 ≤ t) ∧ t < Pw ∧ P.D w d

theorem KeptA.mono {P : Params} {w : Nat} {m m' : Memory} (h : m.Prefix m') {R : Res} {Pw : Time} {y : BitVec 64}
    (hk : KeptA P w m R Pw y) : KeptA P w m' R Pw y := by
  obtain ⟨h1, h2, h3, ⟨tr, y', h4, h5, h6, h7⟩, h8, h9⟩ := hk
  have hle := m.last_le_of_get?_eq_some h1
  exact ⟨Memory.get?_of_prefix h.2 h1, h2, h3, ⟨tr, y', h4, read?_mono h h5, h6, h7.mono h hle⟩, h8, h9⟩

/-- `KeptA` only looks at the link and the data word. -/
theorem KeptA.congr {P : Params} {w : Nat} {m : Memory} {R R' : Res} {Pw : Time} {y : BitVec 64}
    (hk : KeptA P w m R Pw y) (hn : R'.wr (P.nd w) = R.wr (P.nd w)) (hd : R'.wr (P.dd w) = R.wr (P.dd w)) :
    KeptA P w m R' Pw y := by
  unfold KeptA; rw [hn, hd]; exact hk

/-- **A thread's final facts as a side.** -/
structure SideA (P : Params) (w : Nat) (m : Memory) (R : Res) (X : Side) : Prop where
  n : X.n = P.n w
  half : (R.wr P.top).q = 1 / 2
  wset : ∀ p, (R.wr P.top).X p → p.2 = 0 ∨ p.2 = X.p ∨ (X.popped ∧ p.2 = X.q)
  kept : KeptA P w m R X.p X.y
  pop : X.popped → X.p ≤ X.tr0 ∧ X.tr0 ≤ X.tr ∧ X.tr < X.q ∧
    (∃ y0, m.read? P.top X.tr0 = some y0 ∧ BitVec.setWidth 64 y0 = X.v) ∧
    (∃ y1, m.read? P.top X.tr = some y1 ∧ BitVec.setWidth 64 y1 = X.v) ∧ X.v ≠ 0 ∧
    (∀ p wm, X.tr < p → p < X.q → m.get? p = some wm → wm.loc = P.top → wm.tid = w) ∧
    m.get? X.q = some ⟨P.top, BitVec.setWidth 128 X.x4, w⟩ ∧
    ∃ tl u, m.read? ⟨X.v + 8, 8⟩ tl = some u ∧ BitVec.setWidth 64 u = X.x4 ∧
      ∀ p wm, tl < p → p ≤ X.tr0 → m.get? p = some wm → wm.loc ≠ ⟨X.v + 8, 8⟩
  cbz : ¬ X.popped → ∃ r y0, X.p ≤ r ∧ m.read? P.top r = some y0 ∧ BitVec.setWidth 64 y0 = 0

theorem SideA.mono {P : Params} {w : Nat} {m m' : Memory} (h : m.Prefix m') {R : Res} {X : Side}
    (hs : SideA P w m R X) : SideA P w m' R X := by
  refine ⟨hs.n, hs.half, hs.wset, hs.kept.mono h, fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨h1, h2, h3, ⟨y0, h4, h5⟩, ⟨y1, h6, h7⟩, h8, h9, h10, tl, u, h11, h12, h13⟩ := hs.pop hp
    have hQ := m.last_le_of_get?_eq_some h10
    exact ⟨h1, h2, h3, ⟨y0, read?_mono h h4, h5⟩, ⟨y1, read?_mono h h6, h7⟩, h8,
      fun p wm a b hg => h9 p wm a b (Memory.get?_of_prefix_le h.2 (by omega_t) hg),
      Memory.get?_of_prefix h.2 h10, tl, u, read?_mono h h11, h12,
      fun p wm a b hg => h13 p wm a b (Memory.get?_of_prefix_le h.2 (by omega_t) hg)⟩
  · obtain ⟨r, y0, h1, h2, h3⟩ := hs.cbz hp
    exact ⟨r, y0, h1, read?_mono h h2, h3⟩

/-- **Thread `w` done** with resource `R`, `X10 = v`, `X11 = x11`: its
acquire id of `top`, `top` initially `0`, its side and, if it popped, the
popped node `v` and the data read `x11` (zero-extended 32 bits) whose window
reaches its `ldar` read. -/
def DoneRA (P : Params) (w : Nat) (m : Memory) (R : Res) (v x11 : BitVec 64) : Prop :=
  1 ≤ R.acq P.top w ∧ m.initVal P.top = 0 ∧ ∃ X, SideA P w m R X ∧ (X.popped → X.v = v ∧
    ∃ tl u, m.read? ⟨v, 4⟩ tl = some u ∧ BitVec.setWidth 64 (BitVec.setWidth 32 u) = x11 ∧
      ∀ p wm, tl < p → p ≤ X.tr0 → m.get? p = some wm → wm.loc ≠ ⟨v, 4⟩)

theorem DoneRA.mono {P : Params} {w : Nat} {m m' : Memory} (h : m.Prefix m') {R : Res} {v x : BitVec 64}
    (hd : DoneRA P w m R v x) : DoneRA P w m' R v x := by
  obtain ⟨h1, h2, X, hX, hp⟩ := hd
  refine ⟨h1, by rw [TreiberCommon.initVal_eq (m := m) (by first | exact h.1 | exact h.1.symm)]; exact h2, X, hX.mono h, fun hpp => ?_⟩
  obtain ⟨hv, tl, u, hr, hx, hw⟩ := hp hpp
  have hle : X.tr0 ≤ m.last := by
    obtain ⟨-, -, -, ⟨y0, h4, -⟩, -⟩ := hX.pop hpp
    exact TreiberCommon.read?_le_last h4
  exact ⟨hv, tl, u, read?_mono h hr, hx, fun p wm a b hg => hw p wm a b (Memory.get?_of_prefix_le h.2 (by omega_t) hg)⟩

/-! ## The history at the final erasure -/

/-- The data word of `d`'s zero-extended 32 bits (`Treiber2.x32`). -/
abbrev x32A (d : Val) : BitVec 64 := BitVec.setWidth 64 (BitVec.setWidth 32 d)

section Final

variable {P : Params} {rF : Nat → Res} {g : Ghost} {TT : Nat → Prop} {c : Config I}

/-- **The history of `top` at the final clean erasure** from the two
threads' sides. -/
theorem final_coreA (E : Erase rF g TT c) (hL : TLocs P) (hno : ∀ ts, ¬ Outstanding c ts)
    {i0 i1 : Nat} (hi0 : i0 < c.threads.size) (hi1 : i1 < c.threads.size) (h01 : i0 ≠ i1)
    (hall : ∀ k, k < c.threads.size → k = i0 ∨ k = i1) (hT0 : c.mem.initVal P.top = 0) {A B : Side}
    (hA : SideA P 0 c.mem (rF i0) A) (hB : SideA P 1 c.mem (rF i1) B) : ∃ val, HistOK val A B := by
  let val : Nat → BitVec 64 := fun u => BitVec.setWidth 64 ((c.mem.read? P.top u).getD 0)
  have hval : ∀ {u y}, c.mem.read? P.top u = some y → val u = BitVec.setWidth 64 y := fun h => by
    simp only [val, h, Option.getD_some]
  have hq : ((rF i0).wr P.top).q + ((rF i1).wr P.top).q = 1 := by rw [hA.half, hB.half]; grind
  have hpmA := hA.kept.1
  have hpmB := hB.kept.1
  have hqA : A.popped → c.mem.get? A.q = some ⟨P.top, BitVec.setWidth 128 A.x4, 0⟩ :=
    fun hp => (hA.pop hp).2.2.2.2.2.2.2.1
  have hqB : B.popped → c.mem.get? B.q = some ⟨P.top, BitVec.setWidth 128 B.x4, 1⟩ :=
    fun hp => (hB.pop hp).2.2.2.2.2.2.2.1
  have hTm : ∀ u, T A B u → u = 0 ∨ ∃ wm, c.mem.get? u = some wm ∧ wm.loc = P.top := by
    intro u hu
    rcases hu with h | h | h | ⟨hp, h⟩ | ⟨hp, h⟩
    · exact .inl h
    · exact .inr ⟨_, h ▸ hpmA, rfl⟩
    · exact .inr ⟨_, h ▸ hpmB, rfl⟩
    · exact .inr ⟨_, h ▸ hqA hp, rfl⟩
    · exact .inr ⟨_, h ▸ hqB hp, rfl⟩
  have hmT : ∀ u wm, c.mem.get? u = some wm → wm.loc = P.top → T A B u := by
    intro u wm hg hl
    rcases msg_mem_pair E hno hi0 hi1 h01 hall hq hg hl with h | h
    · rcases hA.wset _ h with h0 | h0 | ⟨hp, h0⟩
      · exact .inl h0
      · exact .inr (.inl h0)
      · exact .inr (.inr (.inr (.inl ⟨hp, h0⟩)))
    · rcases hB.wset _ h with h0 | h0 | ⟨hp, h0⟩
      · exact .inl h0
      · exact .inr (.inr (.inl h0))
      · exact .inr (.inr (.inr (.inr ⟨hp, h0⟩)))
  have hrT : ∀ u y, c.mem.read? P.top u = some y → T A B u := by
    intro u y h
    by_cases h0 : u = 0
    · exact .inl h0
    · obtain ⟨wm, hg, hl, -⟩ := get?_of_read? h0 h
      exact hmT u wm hg hl
  -- the writer of a message of `top` tells its side
  have own_side : ∀ u wm, T A B u → c.mem.get? u = some wm →
      (wm.tid = 0 → u = A.p ∨ (A.popped ∧ u = A.q)) ∧ (wm.tid = 1 → u = B.p ∨ (B.popped ∧ u = B.q)) := by
    intro u wm hu hg
    rcases hu with h | h | h | ⟨hp, h⟩ | ⟨hp, h⟩
    · subst h; exact absurd hg (by simp [Memory.get?])
    · subst h; rw [hpmA] at hg; cases hg
      exact ⟨fun _ => .inl rfl, fun h => by simp at h⟩
    · subst h; rw [hpmB] at hg; cases hg
      exact ⟨fun h => by simp at h, fun _ => .inl rfl⟩
    · subst h; rw [hqA hp] at hg; cases hg
      exact ⟨fun _ => .inr ⟨hp, rfl⟩, fun h => by simp at h⟩
    · subst h; rw [hqB hp] at hg; cases hg
      exact ⟨fun h => by simp at h, fun _ => .inr ⟨hp, rfl⟩⟩
  -- a node read whose window covers its push reads the frozen link
  have node : ∀ (w i : Nat) (Y : Side), i < c.threads.size → SideA P w c.mem (rF i) Y →
      ∀ {tl B' : Time} {u : Val}, c.mem.read? (P.nd w) tl = some u →
      (∀ p wm, tl < p → p ≤ B' → c.mem.get? p = some wm → wm.loc ≠ P.nd w) → Y.p ≤ B' →
      BitVec.setWidth 64 u = Y.y := by
    intro w i Y hi hY tl B' u hr hw hle
    obtain ⟨-, hlq, ⟨y', t, hX, hm, ht, hy⟩, -⟩ := hY.kept
    rw [thread_read E hno hi hlq hX hm hr hw (by omega_t), hy]
  -- the side facts
  have side : ∀ (w i : Nat) (X : Side), i < c.threads.size → SideA P w c.mem (rF i) X →
      (∀ u wm, T A B u → c.mem.get? u = some wm → wm.loc = P.top → wm.tid = w →
        u = X.p ∨ (X.popped ∧ u = X.q)) → SideOK val A B X := by
    intro w i X hi hX hown
    obtain ⟨hpm, -, -, ⟨tr, y', htr, hr, hyy, hoi⟩, -⟩ := hX.kept
    have hqlt : X.popped → X.p < X.q := fun hp => by
      obtain ⟨h0, h1, h2, -⟩ := hX.pop hp; omega_t
    refine ⟨Nat.pos_of_ne_zero (get?_ne_zero hpm), by rw [hval (read?_of_get? hpm), hX.n]; exact sw64_nv P w,
      ⟨tr, htr, hrT _ _ hr, by rw [hval hr, hyy], fun u hu h1 h2 => ?_⟩, fun hp => ?_, fun hp => ?_⟩
    · rcases hTm u hu with h | ⟨wm, hg, hl⟩
      · omega_t
      · rcases hown u wm hu hg hl (hoi u wm h1 h2 hg hl) with h | ⟨hp, h⟩
        · omega_t
        · have := hqlt hp; omega_t
    · obtain ⟨h0, h1, h2, ⟨y0, h3, h4⟩, ⟨y1, h5, h6⟩, h7, h8, h9, tl, u, h10, h11, h12⟩ := hX.pop hp
      refine ⟨h0, h1, h2, hrT _ _ h3, hrT _ _ h5, by rw [hval h3, h4], by rw [hval h5, h6], h7, ?_, ?_, ?_, ?_⟩
      · intro u' hu' h1' h2'
        rcases hTm u' hu' with h | ⟨wm, hg, hl⟩
        · omega_t
        · rcases hown u' wm hu' hg hl (h8 u' wm h1' h2' hg hl) with h | ⟨-, h⟩ <;> omega_t
      · rw [hval (read?_of_get? h9)]; simp
      · intro hv hle
        have hl : (⟨X.v + 8, 8⟩ : Loc) = P.nd 0 := by rw [hv, hA.n]; rfl
        rw [hl] at h10 h12
        rw [← h11]; exact node 0 i0 A hi0 hA h10 h12 hle
      · intro hv hle
        have hl : (⟨X.v + 8, 8⟩ : Loc) = P.nd 1 := by rw [hv, hB.n]; rfl
        rw [hl] at h10 h12
        rw [← h11]; exact node 1 i1 B hi1 hB h10 h12 hle
    · obtain ⟨r, y0, h1, h2, h3⟩ := hX.cbz hp
      exact ⟨r, hrT _ _ h2, h1, by rw [hval h2, h3]⟩
  have hne : ∀ {u u' : Time} {v v' : Val}, c.mem.get? u = some ⟨P.top, v, 0⟩ →
      c.mem.get? u' = some ⟨P.top, v', 1⟩ → u ≠ u' := by
    intro u u' v v' h h' he
    rw [he, h'] at h
    cases h
  refine ⟨val, by rw [hval (show c.mem.read? P.top 0 = some (c.mem.initVal P.top) by simp [Memory.read?]), hT0]; rfl,
    by rw [hA.n, hB.n]; exact hL.n_ne, by rw [hA.n]; exact hL.n_nz 0 (by decide),
    by rw [hB.n]; exact hL.n_nz 1 (by decide), hne hpmA hpmB, fun ha hb => hne (hqA ha) (hqB hb),
    fun ha => hne (hqA ha) hpmB, fun hb => Ne.symm (hne hpmA (hqB hb)),
    side 0 i0 A hi0 hA fun u wm hu hg _ ht => (own_side u wm hu hg).1 ht,
    side 1 i1 B hi1 hB fun u wm hu hg _ ht => (own_side u wm hu hg).2 ht⟩

/-- **The values and data the two threads popped** (`Treiber2.final_values_data`
for `treiber2_arm`): their `X10` are the two nodes, and each `X11` the data
word (`D`) of the node it popped. -/
theorem final_values_dataA (E : Erase rF g TT c) (hL : TLocs P) (hno : ∀ ts, ¬ Outstanding c ts)
    {i0 i1 : Nat} (hi0 : i0 < c.threads.size) (hi1 : i1 < c.threads.size) (h01 : i0 ≠ i1)
    (hall : ∀ k, k < c.threads.size → k = i0 ∨ k = i1) {v0 v1 x0 x1 : BitVec 64}
    (h0 : DoneRA P 0 c.mem (rF i0) v0 x0) (h1 : DoneRA P 1 c.mem (rF i1) v1 x1) :
    (v0 = P.n 0 ∧ v1 = P.n 1 ∧ (∃ d, P.D 0 d ∧ x32A d = x0) ∧ ∃ d, P.D 1 d ∧ x32A d = x1) ∨
      (v0 = P.n 1 ∧ v1 = P.n 0 ∧ (∃ d, P.D 1 d ∧ x32A d = x0) ∧ ∃ d, P.D 0 d ∧ x32A d = x1) := by
  obtain ⟨-, hT0, A, hA, hAv⟩ := h0
  obtain ⟨-, -, B, hB, hBv⟩ := h1
  obtain ⟨val, H⟩ := final_coreA E hL hno hi0 hi1 h01 hall hT0 hA hB
  obtain ⟨hpa, hpb, hv⟩ := hist_ok H
  obtain ⟨e0, tl0, u0, hr0, hx0, hw0⟩ := hAv hpa
  obtain ⟨e1, tl1, u1, hr1, hx1, hw1⟩ := hBv hpb
  -- a data read of node `w'` whose window reaches its push reads its data
  have rd : ∀ (w' i : Nat) (Y : Side), i < c.threads.size → SideA P w' c.mem (rF i) Y →
      ∀ {tl tr0 : Time} {u : Val} {v : BitVec 64}, v = P.n w' → c.mem.read? ⟨v, 4⟩ tl = some u →
      (∀ p wm, tl < p → p ≤ tr0 → c.mem.get? p = some wm → wm.loc ≠ ⟨v, 4⟩) → Y.p ≤ tr0 →
      ∃ d, P.D w' d ∧ x32A d = x32A u := by
    intro w' i Y hi hY tl tr0 u v hv hr hw hle
    subst hv
    obtain ⟨-, -, -, -, hdq, d, t, hX, hm, ht, hD⟩ := hY.kept
    exact ⟨d, hD, by rw [thread_read E hno hi hdq hX hm hr hw (by omega_t)]⟩
  have le0A := (hA.pop hpa).1
  have le0B := (hB.pop hpb).1
  rcases hv with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have ha' : v0 = P.n 0 := by rw [← e0, ha, hA.n]
    have hb' : v1 = P.n 1 := by rw [← e1, hb, hB.n]
    refine .inl ⟨ha', hb', ?_, ?_⟩
    · obtain ⟨d, hD, hd⟩ := rd 0 i0 A hi0 hA ha' hr0 hw0 le0A
      exact ⟨d, hD, by rw [hd]; exact hx0⟩
    · obtain ⟨d, hD, hd⟩ := rd 1 i1 B hi1 hB hb' hr1 hw1 le0B
      exact ⟨d, hD, by rw [hd]; exact hx1⟩
  · have ha' : v0 = P.n 1 := by rw [← e0, ha, hB.n]
    have hb' : v1 = P.n 0 := by rw [← e1, hb, hA.n]
    have t0 : B.p ≤ A.tr0 := hist_time H hpa ha
    have t1 : A.p ≤ B.tr0 := hist_time H.swap hpb hb
    refine .inr ⟨ha', hb', ?_, ?_⟩
    · obtain ⟨d, hD, hd⟩ := rd 1 i1 B hi1 hB ha' hr0 hw0 t0
      exact ⟨d, hD, by rw [hd]; exact hx0⟩
    · obtain ⟨d, hD, hd⟩ := rd 0 i0 A hi0 hA hb' hr1 hw1 t1
      exact ⟨d, hD, by rw [hd]; exact hx1⟩

end Final

end Kraken.Promising.SLR.EnvG.Treiber2Arm
