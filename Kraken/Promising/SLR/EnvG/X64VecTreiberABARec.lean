/-
**`treiber_aba_tagged.kl`, part 3: the records the
runs keep** (`EnvGCAdj isa Arch.tso w plan0`).

What the final configuration needs of a thread's run is a record of its
`head` accesses and node accesses, in terms of the thread's snapshot
memory (which only grows: every record is stable along `Tr`, `*.mono`):

- `NoW m l lo hi`: no message of `l` in `(lo, hi]`;
- `NodeRd S m K p tm x`: the node load `movq (%rax),%rbx` at `p` gave `x`:
  `p` is in the private stack range `S`, or it read the message of
  `⟨p, 8⟩` at `tl ≤ K` with value `u` (`x` its low 64 bits) and no write of
  `⟨p, 8⟩` lies in `(tl, tm]`, `tm` the preceding `head` load (TSO: the node
  load's window covers `vrNew`, which the `head` load raised to `tm`);
- `PopR P S w m K v x tr W`: a successful pop of thread `w`: the `head` load
  at `tm` and the `cmpxchg16b` read at `tr` returned `v`, the node load is
  `NodeRd … (lo v) tm x`, and the write `W` (by `w`, atomic after `tr`)
  installed `{x, hi v + 1}`;
- the per-label predicates of the two threads' tables: `A0`, `Done0`
  (thread `0`), `A1`, `R1`, `R2`, `R3`, `Mid1`, `Push1`, `Done1` (thread `1`).

Step facts added to `X64VecTreiberABAVC.lean`'s: `ReadAt.noW` (a read's
window), `readBound_ge`, the `vwOld` order of the node store before
`cmpxchg16b` (`st_vwOld`, `cas_vwOld`), `Com.fence`.
-/
import Kraken.Promising.SLR.EnvG.X64VecTreiberABAVC
import Kraken.Promising.SLR.EnvG.X64VecStack

namespace Kraken.Promising.X64.EnvG.VecABA

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.SLR.EnvG.TreiberCommon (read?_of_get? get?_of_read? initVal_eq read?_mono read?_le_last)

/-- `omega` on `Time`/`View` (abbreviations of `Nat`). -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-! ## Windows -/

/-- No message of `l` in `(lo, hi]`. -/
def NoW (m : Memory) (l : Loc) (lo hi : Time) : Prop :=
  ∀ t wm, lo < t → t ≤ hi → m.get? t = some wm → wm.loc ≠ l

theorem NoW.mono {m m' : Memory} (h : m.Prefix m') {l : Loc} {lo hi : Time} (hhi : hi ≤ m.last)
    (hw : NoW m l lo hi) : NoW m' l lo hi := fun t wm h1 h2 hg =>
  hw t wm h1 h2 (Memory.get?_of_prefix_le h.2 (by omega_t) hg)

theorem NoW.le {m : Memory} {l : Loc} {lo hi hi' : Time} (hw : NoW m l lo hi) (hle : hi' ≤ hi) : NoW m l lo hi' :=
  fun t wm h1 h2 hg => hw t wm h1 (Nat.le_trans h2 hle) hg

/-- A read's window. -/
theorem ReadAt.noW {A : Arch} {tid : Nat} {vs : Views} {c : Config isa} {k : LoadKind} {l : Loc} {tr : Time}
    {v : Val} (h : ReadAt A tid vs c k l tr v) : NoW c.mem l tr (readBound A vs k l) := by
  intro t wm h1 h2 hg hl
  have := (Memory.writeIn_iff _ _ _ _).mpr ⟨t, wm, h1, h2, hg, hl⟩
  rw [h.window] at this; cases this

theorem readBound_ge (A : Arch) (vs : Views) (k : LoadKind) (l : Loc) :
    vs.vrNew ≤ readBound A vs k l ∧ vs.getCoh l ≤ readBound A vs k l := by
  unfold readBound; constructor <;> omega_t

/-- A message of `l`, or `0`, at or below the window's top is at or below the
read. -/
theorem NoW.le_of {m : Memory} {l : Loc} {tr hi t : Time} (hw : NoW m l tr hi) (ht : t ≤ hi)
    (hm : t = 0 ∨ ∃ wm, m.get? t = some wm ∧ wm.loc = l) : t ≤ tr := by
  rcases hm with rfl | ⟨wm, hg, hl⟩
  · exact Nat.zero_le _
  · exact Nat.le_of_not_lt fun hlt => hw t wm hlt ht hg hl

/-- What `read?` says of a timestamp: `0`, or a message of the location. -/
theorem read?_cases {m : Memory} {l : Loc} {t : Time} {v : Val} (h : m.read? l t = some v) :
    (t = 0 ∧ v = m.initVal l) ∨ (t ≠ 0 ∧ ∃ tid, m.get? t = some ⟨l, v, tid⟩) := by
  by_cases h0 : t = 0
  · subst h0; simp [Memory.read?] at h; exact .inl ⟨rfl, h.symm⟩
  · obtain ⟨w, hw, hl, hv⟩ := get?_of_read? h0 h
    refine .inr ⟨h0, w.tid, ?_⟩
    rw [hw]; cases w; simp_all

theorem read?_msg {m : Memory} {l : Loc} {t : Time} {v : Val} (h : m.read? l t = some v) :
    t = 0 ∨ ∃ wm, m.get? t = some wm ∧ wm.loc = l := by
  rcases read?_cases h with ⟨rfl, -⟩ | ⟨-, tid, hg⟩
  · exact .inl rfl
  · exact .inr ⟨_, hg, rfl⟩

theorem get?_le_last {m : Memory} {t : Time} {wm : Msg} (h : m.get? t = some wm) : t ≤ m.last := by
  have := read?_le_last (read?_of_get? h)
  exact this

/-! ## Stability of the common facts -/


theorem Com.fence {P : Params} {w : Nat} {σ σ' : EStateX} (h : Com P w σ) (hf : FenceLe σ σ') : Com P w σ' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨by rw [hf.g]; exact h1, by rw [hf.r]; exact h2, by rw [hf.snap]; exact h3, fun x f hx => ?_, fun f hx => ?_⟩
  · rw [hf.getFwd] at hx; rw [hf.getCoh]; exact h4 x f hx
  · rw [hf.getFwd] at hx; exact Nat.le_trans (h5 f hx) hf.vrNew

/-! ## Thread steps with their reads -/

/-- **The `head` load** (`movdqa (head)`): the common facts and the resource
are kept; the read `tm` is at or below `vrNew` and `coh head`, and at or
above every message of `head` at or below the old `coh head`. -/
theorem hd_ld {P : Params} {w : Nat} {σ σ' : EStateX} (hc : Com P w σ) {v : Val}
    (hs : (EW w).step (.load .plain false P.h 16) σ v σ') :
    Com P w σ' ∧ Tr σ σ' ∧ σ'.r = σ.r ∧ ∃ tm, σ'.snap.mem.read? P.hd tm = some v ∧ tm ≤ σ'.vs.vrNew ∧
      tm ≤ σ'.vs.getCoh P.hd ∧
      ∀ t, t ≤ σ.vs.getCoh P.hd → (t = 0 ∨ ∃ wm, σ'.snap.mem.get? t = some wm ∧ wm.loc = P.hd) → t ≤ tm := by
  obtain ⟨hc', htr, hr, tm, hrd, hcoh, hvr⟩ := ld_step hc hs
  exact ⟨hc', htr, hr, tm, hrd.val, hvr rfl, hcoh, fun t ht hm =>
    (ReadAt.noW hrd).le_of (Nat.le_trans ht (readBound_ge _ _ _ _).2) hm⟩

/-- **The node load** (`movq (%rax),%rbx`, shared): the read `tl` is at or
below `coh`, and no message of the node lies in `(tl, tm]` for any `tm` at
or below `vrNew` before the load. -/
theorem nd_ld {P : Params} {w : Nat} {σ σ' : EStateX} (hc : Com P w σ) {p : BitVec 64} {u : Val}
    (hs : (EW w).step (.load .plain false p 8) σ u σ') {tm : Time} (htm : tm ≤ σ.vs.vrNew) :
    Com P w σ' ∧ Tr σ σ' ∧ σ'.r = σ.r ∧ ∃ tl, σ'.snap.mem.read? (nd p) tl = some u ∧
      tl ≤ σ'.vs.getCoh (nd p) ∧ NoW σ'.snap.mem (nd p) tl tm := by
  obtain ⟨hc', htr, hr, tl, hrd, hcoh, -⟩ := ld_step hc hs
  exact ⟨hc', htr, hr, tl, hrd.val, hcoh, (ReadAt.noW hrd).le (Nat.le_trans htm (readBound_ge _ _ _ _).1)⟩

/-! ## Records -/

/-- **The node load** `movq (%rax),%rbx` at `p` gave `x`: `p` is in the
private stack range `S`, or it read the message of `⟨p, 8⟩` at `tl ≤ K`
(value `u`, `x` its low 64 bits) with no message of `⟨p, 8⟩` in `(tl, tm]`. -/
def NodeRd (S : BitVec 64 → Prop) (m : Memory) (K : Time) (p : BitVec 64) (tm : Time) (x : BitVec 64) : Prop :=
  S p ∨ ∃ tl u, m.read? (nd p) tl = some u ∧ x = BitVec.setWidth 64 u ∧ tl ≤ K ∧ NoW m (nd p) tl tm

theorem NodeRd.mono {S : BitVec 64 → Prop} {m m' : Memory} (h : m.Prefix m') {K K' : Time} (hK : K ≤ K')
    {p : BitVec 64} {tm : Time} {x : BitVec 64} (htm : tm ≤ m.last) (hn : NodeRd S m K p tm x) :
    NodeRd S m' K' p tm x :=
  hn.imp_right fun ⟨tl, u, h1, h2, h3, h4⟩ => ⟨tl, u, read?_mono h h1, h2, Nat.le_trans h3 hK, h4.mono h htm⟩

/-- **A successful pop** of thread `w`: the `head` load at `tm` and the
`cmpxchg16b` read at `tr` returned `v`, the node load gave `x`, and the
write `W` of `w`, atomic after `tr`, installed `{x, hi v + 1}`. -/
structure PopR (P : Params) (S : BitVec 64 → Prop) (w : Nat) (m : Memory) (K : Time) (v : Val) (x : BitVec 64)
    (tm tr W : Time) : Prop where
  rdm : m.read? P.hd tm = some v
  rd : m.read? P.hd tr = some v
  lt : tr < W
  wr : m.get? W = some ⟨P.hd, (hi v + 1) ++ x, w⟩
  atm : AtomicT m P.hd tr W w
  node : NodeRd S m K (lo v) tm x
  tmr : tm ≤ tr

theorem PopR.mono {P : Params} {S : BitVec 64 → Prop} {w : Nat} {m m' : Memory} (h : m.Prefix m') {K K' : Time}
    (hK : K ≤ K') {v : Val} {x : BitVec 64} {tm tr W : Time} (hp : PopR P S w m K v x tm tr W) :
    PopR P S w m' K' v x tm tr W :=
  ⟨read?_mono h hp.rdm, read?_mono h hp.rd, hp.lt, Memory.get?_of_prefix h.2 hp.wr,
    hp.atm.mono h (by have := get?_le_last hp.wr; omega_t), hp.node.mono h hK (read?_le_last hp.rdm), hp.tmr⟩

/-! ## The pop -/

/-- **A pop's run** (both threads): the `head` load, the node load (from the
stack or shared), the `cmpxchg16b` with accumulator `v` and replacement
`{x, hi v + 1}`, with silent steps between. It fails with the resource
unchanged, or succeeds with a `PopR`, the write joining the resource; its
read is at or above every message of `head` at or below the starting
`coh head`. -/
theorem pop_run {P : Params} {S : BitVec 64 → Prop} {w : Nat} {σ0 σ1 σ2 σ3 σ4 σ5 : EStateX} {v old : Val}
    {x : BitVec 64} (hc : Com P w σ0) (hld : (EW w).step (.load .plain false P.h 16) σ0 v σ1)
    (hf1 : FenceLe σ1 σ2)
    (hn : (S (lo v) ∧ σ3 = σ2) ∨ ∃ u, (EW w).step (.load .plain false (lo v) 8) σ2 u σ3 ∧ x = BitVec.setWidth 64 u)
    (hf2 : FenceLe σ3 σ4) (hcas : (EW w).step (.rmw .acqRel P.h 16 (cas16 v ((hi v + 1) ++ x))) σ4 old σ5) :
    Com P w σ5 ∧ Tr σ0 σ5 ∧
      ((old ≠ v ∧ σ5.r = σ0.r) ∨
        (old = v ∧ ∃ tm tr W C, PopR P S w σ5.snap.mem (σ5.vs.getCoh (nd (lo v))) v x tm tr W ∧
          σ5.r = (σ0.r.addW P.hd ((hi v + 1) ++ x, W)).op C ∧
          (∀ t, t ≤ σ0.vs.getCoh P.hd → (t = 0 ∨ ∃ wm, σ0.snap.mem.get? t = some wm ∧ wm.loc = P.hd) → t ≤ tr) ∧
          W ≤ σ5.vs.getCoh P.hd)) := by
  obtain ⟨hc1, htr1, hr1, tm, hrdm, htmv, htmc, -⟩ := hd_ld hc hld
  have hc2 := hc1.fence hf1
  have htr2 := htr1.trans (Tr.ofFence hf1)
  have hr2 : σ2.r = σ0.r := hf1.r.trans hr1
  obtain ⟨hc3, htr3, hr3, hrdm3, hnode, htmc3⟩ : Com P w σ3 ∧ Tr σ0 σ3 ∧ σ3.r = σ0.r ∧
      σ3.snap.mem.read? P.hd tm = some v ∧ NodeRd S σ3.snap.mem (σ3.vs.getCoh (nd (lo v))) (lo v) tm x ∧
      tm ≤ σ3.vs.getCoh P.hd := by
    rcases hn with ⟨hS, rfl⟩ | ⟨u, hs, rfl⟩
    · exact ⟨hc2, htr2, hr2, by rw [hf1.snap]; exact hrdm, .inl hS, by rw [hf1.getCoh]; exact htmc⟩
    · obtain ⟨hc3, htr23, hr3, tl, hrd, hcoh, hnw⟩ := nd_ld hc2 hs (Nat.le_trans htmv hf1.vrNew)
      exact ⟨hc3, htr2.trans htr23, hr3.trans hr2, read?_mono htr23.pre (by rw [hf1.snap]; exact hrdm),
        .inr ⟨tl, u, hrd, rfl, hcoh, hnw⟩, Nat.le_trans (by rw [hf1.getCoh]; exact htmc) (htr23.coh _)⟩
  have hc4 := hc3.fence hf2
  have htr4 := htr3.trans (Tr.ofFence hf2)
  have hr4 : σ4.r = σ0.r := hf2.r.trans hr3
  obtain ⟨hc5, htr45, tr, hrd, hown, hbr⟩ := cas_step hc4 hcas
  refine ⟨hc5, htr4.trans htr45, ?_⟩
  rcases hbr with ⟨hnone, hr5⟩ | ⟨new, tw, C, hop, htrw, hg, hat, -, htwc, hr5, -⟩
  · exact .inl ⟨cas16_none hnone, hr5.trans hr4⟩
  · obtain ⟨hov, rfl⟩ := cas16_some hop
    subst hov
    have h35 := (Tr.ofFence hf2).trans htr45
    refine .inr ⟨rfl, tm, tr, tw, C, ⟨read?_mono h35.pre hrdm3, hrd, htrw, hg, hat,
      hnode.mono h35.pre (h35.coh _) (read?_le_last hrdm3), ?_⟩, by rw [hr5, hr4], fun t ht hm => ?_, htwc⟩
    · rcases read?_msg hrdm3 with h0 | ⟨wm, hg', hl⟩
      · rw [h0]; exact Nat.zero_le _
      · exact hown tm wm (Memory.get?_of_prefix (Tr.ofFence hf2).pre.2 hg') hl
          (Nat.le_trans htmc3 ((Tr.ofFence hf2).coh _))
    rcases hm with rfl | ⟨wm, hg', hl⟩
    · exact Nat.zero_le _
    · exact hown t wm (Memory.get?_of_prefix htr4.pre.2 hg') hl (Nat.le_trans ht (htr4.coh _))

theorem FenceLe.coh_eq {σ σ' : EStateX} (hf : FenceLe σ σ') : σ'.vs.getCoh = σ.vs.getCoh := funext hf.getCoh

/-! ## Thread `0` -/

/-- Thread `0` at `p0`: the common facts, no write yet. -/
def A0 (P : Params) (σ : EStateX) : Prop := Com P 0 σ ∧ ExH P σ.r (fun _ => False)

/-- Thread `0` at `done`: its pop (`r12 = lo v`, `r13` the node value), the
write set of `head` its write. -/
def Done0 (P : Params) (S : BitVec 64 → Prop) (σ : EStateX) (r12 r13 : BitVec 64) : Prop :=
  Com P 0 σ ∧ ∃ v K tm tr W, r12 = lo v ∧ PopR P S 0 σ.snap.mem K v r13 tm tr W ∧
    ExH P σ.r (· = ((hi v + 1) ++ r13, W))

section Thread0

variable {P : Params} {S : BitVec 64 → Prop} {σ σ' : EStateX}

theorem A0.fence (h : A0 P σ) (hf : FenceLe σ σ') : A0 P σ' := ⟨h.1.fence hf, by rw [hf.r]; exact h.2⟩

theorem Done0.fence {r12 r13 : BitVec 64} (h : Done0 P S σ r12 r13) (hf : FenceLe σ σ') : Done0 P S σ' r12 r13 := by
  obtain ⟨hc, v, K, tm, tr, W, h1, h2, h3⟩ := h
  exact ⟨hc.fence hf, v, K, tm, tr, W, h1, by rw [hf.snap]; exact h2, by rw [hf.r]; exact h3⟩

/-- The `head` load keeps `A0` (the empty-stack retry). -/
theorem A0.ld {v : Val} (h : A0 P σ) (hld : (EW 0).step (.load .plain false P.h 16) σ v σ') : A0 P σ' := by
  obtain ⟨hc, -, hr, -⟩ := hd_ld h.1 hld
  exact ⟨hc, by rw [hr]; exact h.2⟩

/-- **Thread `0`'s pop**: a failed `cmpxchg16b` keeps `A0`, a successful one
gives `Done0`. -/
theorem A0.pop {σ0 σ1 σ2 σ3 σ4 σ5 : EStateX} {v old : Val} {x : BitVec 64} (h : A0 P σ0)
    (hld : (EW 0).step (.load .plain false P.h 16) σ0 v σ1) (hf1 : FenceLe σ1 σ2)
    (hn : (S (lo v) ∧ σ3 = σ2) ∨ ∃ u, (EW 0).step (.load .plain false (lo v) 8) σ2 u σ3 ∧ x = BitVec.setWidth 64 u)
    (hf2 : FenceLe σ3 σ4) (hcas : (EW 0).step (.rmw .acqRel P.h 16 (cas16 v ((hi v + 1) ++ x))) σ4 old σ5) :
    (old ≠ v ∧ A0 P σ5) ∨ (old = v ∧ Done0 P S σ5 (lo v) x) := by
  obtain ⟨hc5, -, hbr⟩ := pop_run h.1 hld hf1 hn hf2 hcas
  rcases hbr with ⟨hne, hr⟩ | ⟨heq, tm, tr, W, C, hp, hr, -, -⟩
  · exact .inl ⟨hne, hc5, by rw [hr]; exact h.2⟩
  · refine .inr ⟨heq, hc5, v, _, tm, tr, W, rfl, hp, ?_⟩
    rw [hr]
    exact (h.2.cas h.1.2.1.1 _ W C).mono fun p hp => hp.resolve_left id

end Thread0

/-! ## Thread `1` -/

/-- Thread `1` at `p1`/`p1pop1`: the common facts, no write yet. -/
def A1 (P : Params) (σ : EStateX) : Prop :=
  Com P 1 σ ∧ ExH P σ.r (fun _ => False) ∧ ExN σ.r (fun _ _ => False)

/-- **The first pop's record**: empty (`r12 = 0`, the `head` load at `T1`
read a null pointer), or a pop of `r12 ≠ 0` writing `n1` at `T1`. -/
def R1 (P : Params) (S : BitVec 64 → Prop) (m : Memory) (K : Loc → Time) (r12 : BitVec 64) (T1 : Time)
    (n1 : Val) : Prop :=
  (r12 = 0 ∧ ∃ v, m.read? P.hd T1 = some v ∧ lo v = 0) ∨
    (r12 ≠ 0 ∧ ∃ v tm tr x, r12 = lo v ∧ n1 = (hi v + 1) ++ x ∧ PopR P S 1 m (K (nd (lo v))) v x tm tr T1)

/-- **The second pop's record**: empty (`r13 = 0`), or a pop of `r13 ≠ 0`
writing `n2` at `W2`, its read at or above `T1`. -/
def R2 (P : Params) (S : BitVec 64 → Prop) (m : Memory) (K : Loc → Time) (r13 : BitVec 64) (T1 W2 : Time)
    (n2 : Val) : Prop :=
  (r13 = 0 ∧ W2 = 0) ∨
    (r13 ≠ 0 ∧ ∃ v tm tr x, r13 = lo v ∧ n2 = (hi v + 1) ++ x ∧ PopR P S 1 m (K (nd (lo v))) v x tm tr W2 ∧
      T1 ≤ tr)

/-- **The push's record**: the `cmpxchg16b` read `v` at `tr` (at or above
`W2`) and wrote `n3 = {r12, hi v + 1}` at `W3`, atomic; the node store
before it went to the stack, or is the message `Tn < W3` of `⟨r12, 8⟩` with
value `lo v`. -/
def R3 (P : Params) (S : BitVec 64 → Prop) (m : Memory) (r12 : BitVec 64) (W2 W3 : Time) (n3 : Val) (Tn : Time) :
    Prop :=
  ∃ v tr, n3 = (hi v + 1) ++ r12 ∧ m.read? P.hd tr = some v ∧ tr < W3 ∧ m.get? W3 = some ⟨P.hd, n3, 1⟩ ∧
    AtomicT m P.hd tr W3 1 ∧ W2 ≤ tr ∧ (S r12 ∨ (m.get? Tn = some ⟨nd r12, BitVec.setWidth 128 (lo v), 1⟩ ∧ Tn < W3))

/-- Thread `1`'s `head` writes: the first pop's (if any), `(n2, W2)` and
`(n3, W3)` (a `0` timestamp standing for none). -/
def H1 (r12 : BitVec 64) (T1 : Time) (n1 : Val) (W2 : Time) (n2 : Val) (W3 : Time) (n3 : Val) (p : Val × Time) :
    Prop :=
  (r12 ≠ 0 ∧ p = (n1, T1)) ∨ p = (n2, W2) ∨ p = (n3, W3)

/-- Thread `1` at `p1pop2`. -/
def Mid1a (P : Params) (S : BitVec 64 → Prop) (σ : EStateX) (r12 : BitVec 64) : Prop :=
  Com P 1 σ ∧ ∃ T1 n1, R1 P S σ.snap.mem σ.vs.getCoh r12 T1 n1 ∧ T1 ≤ σ.vs.getCoh P.hd ∧
    ExH P σ.r (H1 r12 T1 n1 0 0 0 0) ∧ ExN σ.r (fun _ _ => False)

/-- Thread `1` at `p1push`. -/
def Mid1b (P : Params) (S : BitVec 64 → Prop) (σ : EStateX) (r12 r13 : BitVec 64) : Prop :=
  Com P 1 σ ∧ ∃ T1 n1 W2 n2, R1 P S σ.snap.mem σ.vs.getCoh r12 T1 n1 ∧
    R2 P S σ.snap.mem σ.vs.getCoh r13 T1 W2 n2 ∧ W2 ≤ σ.vs.getCoh P.hd ∧
    ExH P σ.r (H1 r12 T1 n1 W2 n2 0 0) ∧ ExN σ.r (fun _ _ => False)

/-- Thread `1` at `p1push1`: the node bounds `K` fixed at the push's entry;
its node stores so far are to `⟨r12, 8⟩`, above `K`. -/
def Push1 (P : Params) (S : BitVec 64 → Prop) (σ : EStateX) (r12 r13 : BitVec 64) : Prop :=
  Com P 1 σ ∧ r12 ≠ 0 ∧ ∃ (T1 : Time) (n1 : Val) (W2 : Time) (n2 : Val) (K : Loc → Time), R1 P S σ.snap.mem K r12 T1 n1 ∧
    R2 P S σ.snap.mem K r13 T1 W2 n2 ∧ W2 ≤ σ.vs.getCoh P.hd ∧ (∀ x, K x ≤ σ.vs.getCoh x) ∧
    ExH P σ.r (H1 r12 T1 n1 W2 n2 0 0) ∧ ExN σ.r (fun x t => K x < t ∧ x = nd r12 ∧ t ≤ σ.vs.getCoh x)

/-- Thread `1` at `done`. -/
def Done1 (P : Params) (S : BitVec 64 → Prop) (σ : EStateX) (r12 r13 : BitVec 64) : Prop :=
  Com P 1 σ ∧ ∃ (T1 : Time) (n1 : Val) (W2 : Time) (n2 : Val) (K : Loc → Time), R1 P S σ.snap.mem K r12 T1 n1 ∧ R2 P S σ.snap.mem K r13 T1 W2 n2 ∧
    ((r12 = 0 ∧ ExH P σ.r (H1 r12 T1 n1 W2 n2 0 0) ∧ ExN σ.r (fun _ _ => False)) ∨
      (r12 ≠ 0 ∧ ∃ W3 n3 Tn, R3 P S σ.snap.mem r12 W2 W3 n3 Tn ∧ ExH P σ.r (H1 r12 T1 n1 W2 n2 W3 n3) ∧
        ExN σ.r (fun x t => K x < t ∧ x = nd r12 ∧ t ≤ Tn)))

section Thread1

variable {P : Params} {S : BitVec 64 → Prop}

/-- `ExH.mono`, a mapped pair allowed to be an initial one. -/
theorem ExH.mono0 {r : Res} {T T' : Val × Time → Prop} (h : ExH P r T) (hT : ∀ p, T p → p.2 = 0 ∨ T' p) :
    ExH P r T' := fun hq p hp => (h hq p hp).elim .inl (hT p)

theorem R1.mono {m m' : Memory} (h : m.Prefix m') {K K' : Loc → Time} (hK : ∀ x, K x ≤ K' x) {r12 : BitVec 64}
    {T1 : Time} {n1 : Val} (hr : R1 P S m K r12 T1 n1) : R1 P S m' K' r12 T1 n1 := by
  rcases hr with ⟨h0, v, hv, hl⟩ | ⟨h0, v, tm, tr, x, e1, e2, hp⟩
  · exact .inl ⟨h0, v, read?_mono h hv, hl⟩
  · exact .inr ⟨h0, v, tm, tr, x, e1, e2, hp.mono h (hK _)⟩

theorem R2.mono {m m' : Memory} (h : m.Prefix m') {K K' : Loc → Time} (hK : ∀ x, K x ≤ K' x) {r13 : BitVec 64}
    {T1 W2 : Time} {n2 : Val} (hr : R2 P S m K r13 T1 W2 n2) : R2 P S m' K' r13 T1 W2 n2 := by
  rcases hr with h0 | ⟨h0, v, tm, tr, x, e1, e2, hp, hle⟩
  · exact .inl h0
  · exact .inr ⟨h0, v, tm, tr, x, e1, e2, hp.mono h (hK _), hle⟩

theorem R3.mono {m m' : Memory} (h : m.Prefix m') {r12 : BitVec 64} {W2 W3 : Time} {n3 : Val} {Tn : Time}
    (hr : R3 P S m r12 W2 W3 n3 Tn) : R3 P S m' r12 W2 W3 n3 Tn := by
  obtain ⟨v, tr, e, hrd, hlt, hg, hat, hle, hn⟩ := hr
  exact ⟨v, tr, e, read?_mono h hrd, hlt, Memory.get?_of_prefix h.2 hg,
    hat.mono h (by have := get?_le_last hg; omega_t), hle,
    hn.imp_right fun ⟨h1, h2⟩ => ⟨Memory.get?_of_prefix h.2 h1, h2⟩⟩

/-- `T1` is `0` or a message of `head`. -/
theorem R1.msg {m : Memory} {K : Loc → Time} {r12 : BitVec 64} {T1 : Time} {n1 : Val} (hr : R1 P S m K r12 T1 n1) :
    T1 = 0 ∨ ∃ wm, m.get? T1 = some wm ∧ wm.loc = P.hd := by
  rcases hr with ⟨-, v, hv, -⟩ | ⟨-, v, tm, tr, x, -, -, hp⟩
  · exact read?_msg hv
  · exact .inr ⟨_, hp.wr, rfl⟩

theorem R2.msg {m : Memory} {K : Loc → Time} {r13 : BitVec 64} {T1 W2 : Time} {n2 : Val}
    (hr : R2 P S m K r13 T1 W2 n2) : W2 = 0 ∨ ∃ wm, m.get? W2 = some wm ∧ wm.loc = P.hd := by
  rcases hr with ⟨-, h⟩ | ⟨-, v, tm, tr, x, -, -, hp, -⟩
  · exact .inl h
  · exact .inr ⟨_, hp.wr, rfl⟩

variable {σ σ' : EStateX}

theorem A1.fence (h : A1 P σ) (hf : FenceLe σ σ') : A1 P σ' :=
  ⟨h.1.fence hf, by rw [hf.r]; exact h.2.1, by rw [hf.r]; exact h.2.2⟩

theorem Mid1a.fence {r12 : BitVec 64} (h : Mid1a P S σ r12) (hf : FenceLe σ σ') : Mid1a P S σ' r12 := by
  obtain ⟨hc, rest⟩ := h
  refine ⟨hc.fence hf, ?_⟩
  rw [hf.snap, hf.r, FenceLe.coh_eq hf]; exact rest

theorem Mid1b.fence {r12 r13 : BitVec 64} (h : Mid1b P S σ r12 r13) (hf : FenceLe σ σ') : Mid1b P S σ' r12 r13 := by
  obtain ⟨hc, rest⟩ := h
  refine ⟨hc.fence hf, ?_⟩
  rw [hf.snap, hf.r, FenceLe.coh_eq hf]; exact rest

theorem Push1.fence {r12 r13 : BitVec 64} (h : Push1 P S σ r12 r13) (hf : FenceLe σ σ') : Push1 P S σ' r12 r13 := by
  obtain ⟨hc, rest⟩ := h
  refine ⟨hc.fence hf, ?_⟩
  rw [hf.snap, hf.r, FenceLe.coh_eq hf]; exact rest

theorem Done1.fence {r12 r13 : BitVec 64} (h : Done1 P S σ r12 r13) (hf : FenceLe σ σ') : Done1 P S σ' r12 r13 := by
  obtain ⟨hc, rest⟩ := h
  refine ⟨hc.fence hf, ?_⟩
  rw [hf.snap, hf.r]; exact rest

/-- **The first pop finds the stack empty.** -/
theorem A1.empty {v : Val} (h : A1 P σ) (hld : (EW 1).step (.load .plain false P.h 16) σ v σ') (hv : lo v = 0) :
    Mid1a P S σ' 0 := by
  obtain ⟨hc, -, hr, tm, hrd, -, hcoh, -⟩ := hd_ld h.1 hld
  refine ⟨hc, tm, 0, .inl ⟨rfl, v, hrd, hv⟩, hcoh, ?_, by rw [hr]; exact h.2.2⟩
  rw [hr]; exact h.2.1.mono fun _ h => h.elim

/-- **The first pop's `cmpxchg16b`**: failed, back to `p1pop1`; succeeded,
on to `p1pop2` with `r12 = lo v`. -/
theorem A1.pop {σ0 σ1 σ2 σ3 σ4 σ5 : EStateX} {v old : Val} {x : BitVec 64} (h : A1 P σ0) (hv : lo v ≠ 0)
    (hld : (EW 1).step (.load .plain false P.h 16) σ0 v σ1) (hf1 : FenceLe σ1 σ2)
    (hn : (S (lo v) ∧ σ3 = σ2) ∨ ∃ u, (EW 1).step (.load .plain false (lo v) 8) σ2 u σ3 ∧ x = BitVec.setWidth 64 u)
    (hf2 : FenceLe σ3 σ4) (hcas : (EW 1).step (.rmw .acqRel P.h 16 (cas16 v ((hi v + 1) ++ x))) σ4 old σ5) :
    (old ≠ v ∧ A1 P σ5) ∨ (old = v ∧ Mid1a P S σ5 (lo v)) := by
  obtain ⟨hc5, -, hbr⟩ := pop_run h.1 hld hf1 hn hf2 hcas
  rcases hbr with ⟨hne, hr⟩ | ⟨heq, tm, tr, W, C, hp, hr, -, hW⟩
  · exact .inl ⟨hne, hc5, by rw [hr]; exact h.2.1, by rw [hr]; exact h.2.2⟩
  · refine .inr ⟨heq, hc5, W, _, .inr ⟨hv, v, tm, tr, x, rfl, rfl, hp⟩, hW, ?_, ?_⟩
    · rw [hr]
      exact (h.2.1.cas h.1.2.1.1 _ W C).mono fun p hp => .inl ⟨hv, hp.resolve_left id⟩
    · rw [hr]; exact h.2.2.cas (fun _ hx => h.1.2.1.nd_ge hx) _ W C

/-- **The second pop finds the stack empty.** -/
theorem Mid1a.empty {v : Val} {r12 : BitVec 64} (h : Mid1a P S σ r12)
    (hld : (EW 1).step (.load .plain false P.h 16) σ v σ') : Mid1b P S σ' r12 0 := by
  obtain ⟨hc, T1, n1, hr1, -, hx, hn⟩ := h
  obtain ⟨hc', htr, hr, -⟩ := hd_ld hc hld
  refine ⟨hc', T1, n1, 0, 0, hr1.mono htr.pre htr.coh, .inl ⟨rfl, rfl⟩, Nat.zero_le _, ?_, by rw [hr]; exact hn⟩
  rw [hr]; exact hx

/-- **The second pop's `cmpxchg16b`**: failed, back to `p1pop2`; succeeded,
on to `p1push` with `r13 = lo v`. -/
theorem Mid1a.pop {σ0 σ1 σ2 σ3 σ4 σ5 : EStateX} {v old : Val} {x r12 : BitVec 64} (h : Mid1a P S σ0 r12)
    (hv : lo v ≠ 0) (hld : (EW 1).step (.load .plain false P.h 16) σ0 v σ1) (hf1 : FenceLe σ1 σ2)
    (hn : (S (lo v) ∧ σ3 = σ2) ∨ ∃ u, (EW 1).step (.load .plain false (lo v) 8) σ2 u σ3 ∧ x = BitVec.setWidth 64 u)
    (hf2 : FenceLe σ3 σ4) (hcas : (EW 1).step (.rmw .acqRel P.h 16 (cas16 v ((hi v + 1) ++ x))) σ4 old σ5) :
    (old ≠ v ∧ Mid1a P S σ5 r12) ∨ (old = v ∧ Mid1b P S σ5 r12 (lo v)) := by
  obtain ⟨hc0, T1, n1, hr1, hT1, hx, hnn⟩ := h
  obtain ⟨hc5, htr, hbr⟩ := pop_run hc0 hld hf1 hn hf2 hcas
  rcases hbr with ⟨hne, hr⟩ | ⟨heq, tm, tr, W, C, hp, hr, hown, hW⟩
  · exact .inl ⟨hne, hc5, T1, n1, hr1.mono htr.pre htr.coh, Nat.le_trans hT1 (htr.coh _), by rw [hr]; exact hx,
      by rw [hr]; exact hnn⟩
  · refine .inr ⟨heq, hc5, T1, n1, W, _, hr1.mono htr.pre htr.coh,
      .inr ⟨hv, v, tm, tr, x, rfl, rfl, hp, hown T1 hT1 hr1.msg⟩, hW, ?_, ?_⟩
    · rw [hr]
      refine (hx.cas hc0.2.1.1 _ W C).mono fun p hp => ?_
      rcases hp with (h1 | h2 | h3) | h4
      · exact .inl h1
      · exact .inr (.inr (by rw [h2]))
      · exact .inr (.inr h3)
      · exact .inr (.inl h4)
    · rw [hr]; exact hnn.cas (fun _ hx => hc0.2.1.nd_ge hx) _ W C

/-- **No push** (`r12 = 0`): done. -/
theorem Mid1b.done {r12 r13 : BitVec 64} (h : Mid1b P S σ r12 r13) (h0 : r12 = 0) : Done1 P S σ r12 r13 := by
  obtain ⟨hc, T1, n1, W2, n2, hr1, hr2, -, hx, hn⟩ := h
  exact ⟨hc, T1, n1, W2, n2, _, hr1, hr2, .inl ⟨h0, hx, hn⟩⟩

/-- **On to the push** (`r12 ≠ 0`): the node bounds are fixed at `coh`. -/
theorem Mid1b.push {r12 r13 : BitVec 64} (h : Mid1b P S σ r12 r13) (h0 : r12 ≠ 0) : Push1 P S σ r12 r13 := by
  obtain ⟨hc, T1, n1, W2, n2, hr1, hr2, hW, hx, hn⟩ := h
  exact ⟨hc, h0, T1, n1, W2, n2, _, hr1, hr2, hW, fun _ => Nat.le_refl _, hx, hn.mono fun _ _ h => h.elim⟩

/-- **The push's run**: the `head` load, the node store (to the stack or
shared), the `cmpxchg16b` with accumulator `v` and replacement
`{r12, hi v + 1}`. Failed, back to `p1push1`; succeeded, done. -/
theorem Push1.run {σ0 σ1 σ2 σ3 σ4 σ5 : EStateX} {v old : Val} {r12 r13 : BitVec 64} (h : Push1 P S σ0 r12 r13)
    (hld : (EW 1).step (.load .plain false P.h 16) σ0 v σ1) (hf1 : FenceLe σ1 σ2)
    (hst : (S r12 ∧ σ3 = σ2) ∨ ∃ b, (EW 1).step (.store .plain false r12 8 (BitVec.setWidth 128 (lo v))) σ2 b σ3)
    (hf2 : FenceLe σ3 σ4) (hcas : (EW 1).step (.rmw .acqRel P.h 16 (cas16 v ((hi v + 1) ++ r12))) σ4 old σ5) :
    (old ≠ v ∧ Push1 P S σ5 r12 r13) ∨ (old = v ∧ Done1 P S σ5 r12 r13) := by
  obtain ⟨hc0, h0, T1, n1, W2, n2, K, hr1, hr2, hW2, hK, hx, hn⟩ := h
  obtain ⟨hc1, htr1, hr1', -⟩ := hd_ld hc0 hld
  have hc2 := hc1.fence hf1
  have htr2 := htr1.trans (Tr.ofFence hf1)
  have hr2' : σ2.r = σ0.r := hf1.r.trans hr1'
  -- the node store
  obtain ⟨hc3, htr23, hx3, hst3⟩ : Com P 1 σ3 ∧ Tr σ2 σ3 ∧ ExH P σ3.r (H1 r12 T1 n1 W2 n2 0 0) ∧
      ((S r12 ∧ ExN σ3.r (fun x t => K x < t ∧ x = nd r12 ∧ t ≤ σ3.vs.getCoh x)) ∨
        ∃ tn, σ3.snap.mem.get? tn = some ⟨nd r12, BitVec.setWidth 128 (lo v), 1⟩ ∧ tn ≤ σ3.vs.vwOld ∧
          tn ≤ σ3.vs.getCoh (nd r12) ∧ ExN σ3.r (fun x t => K x < t ∧ x = nd r12 ∧ t ≤ tn)) := by
    have hx2 : ExH P σ2.r (H1 r12 T1 n1 W2 n2 0 0) := by rw [hr2']; exact hx
    have hn2 : ExN σ2.r (fun x t => K x < t ∧ x = nd r12 ∧ t ≤ σ2.vs.getCoh x) := by
      rw [hr2']; exact hn.mono fun x t ⟨a, b, c⟩ => ⟨a, b, Nat.le_trans c (htr2.coh x)⟩
    rcases hst with ⟨hS, rfl⟩ | ⟨b, hs⟩
    · exact ⟨hc2, Tr.refl _, hx2, .inl ⟨hS, hn2⟩⟩
    · obtain ⟨hc3, htr23, tw, hr3, hg, hlt, hle, hvw⟩ := st_step hc2 hs
      refine ⟨hc3, htr23, by rw [hr3]; exact hx2.addW_nd _ _, .inr ⟨tw, hg, hvw, hle, ?_⟩⟩
      rw [hr3]
      refine (hn2.store (nd r12) _ tw).mono fun x t h => ?_
      rcases h with ⟨a, rfl, c⟩ | ⟨rfl, rfl⟩
      · exact ⟨a, rfl, by omega_t⟩
      · exact ⟨Nat.lt_of_le_of_lt (Nat.le_trans (hK _) (htr2.coh _)) hlt, rfl, Nat.le_refl _⟩
  have hc4 := hc3.fence hf2
  have htr34 := Tr.ofFence hf2
  have hr4 : σ4.r = σ3.r := hf2.r
  obtain ⟨hc5, htr45, tr, hrd, hown, hbr⟩ := cas_step hc4 hcas
  have htr35 := htr34.trans htr45
  have htr05 : Tr σ0 σ5 := htr2.trans (htr23.trans htr35)
  have hn5 : ExN σ3.r (fun x t => K x < t ∧ x = nd r12 ∧ t ≤ σ5.vs.getCoh x) := by
    rcases hst3 with ⟨-, hn3⟩ | ⟨tn, -, -, htn, hn3⟩
    · exact hn3.mono fun x t ⟨a, b, c⟩ => ⟨a, b, Nat.le_trans c (htr35.coh x)⟩
    · exact hn3.mono fun x t ⟨a, b, c⟩ => ⟨a, b, by subst b; exact Nat.le_trans c (Nat.le_trans htn (htr35.coh _))⟩
  rcases hbr with ⟨hnone, hr5⟩ | ⟨new, tw, C, hop, htrw, hg, hat, -, -, hr5, hvw⟩
  · refine .inl ⟨cas16_none hnone, hc5, h0, T1, n1, W2, n2, K, hr1.mono htr05.pre (fun _ => Nat.le_refl _),
      hr2.mono htr05.pre (fun _ => Nat.le_refl _), Nat.le_trans hW2 (htr05.coh _),
      fun x => Nat.le_trans (hK x) (htr05.coh x), by rw [hr5, hr4]; exact hx3, by rw [hr5, hr4]; exact hn5⟩
  · obtain ⟨hov, rfl⟩ := cas16_some hop
    subst hov
    have htr04 : Tr σ0 σ4 := htr2.trans (htr23.trans htr34)
    have hW2tr : W2 ≤ tr := by
      rcases hr2.msg with h0' | ⟨wm, hg', hl⟩
      · rw [h0']; exact Nat.zero_le _
      · exact hown W2 wm (Memory.get?_of_prefix htr04.pre.2 hg') hl (Nat.le_trans hW2 (htr04.coh _))
    obtain ⟨Tn, hsto, hnT⟩ : ∃ Tn, (S r12 ∨ (σ5.snap.mem.get? Tn =
        some ⟨nd r12, BitVec.setWidth 128 (lo old), 1⟩ ∧ Tn < tw)) ∧
        ExN σ3.r (fun x t => K x < t ∧ x = nd r12 ∧ t ≤ Tn) := by
      rcases hst3 with ⟨hS, -⟩ | ⟨tn, hg', hvw', -, hn3⟩
      · exact ⟨σ5.vs.getCoh (nd r12), .inl hS, hn5.mono fun x t ⟨a, b, c⟩ => ⟨a, b, by subst b; exact c⟩⟩
      · exact ⟨tn, .inr ⟨Memory.get?_of_prefix htr35.pre.2 hg', by have := htr34.vw; omega_t⟩, hn3⟩
    refine .inr ⟨rfl, hc5, T1, n1, W2, n2, K, hr1.mono htr05.pre (fun _ => Nat.le_refl _),
      hr2.mono htr05.pre (fun _ => Nat.le_refl _), .inr ⟨h0, tw, _, Tn, ⟨old, tr, rfl, hrd, htrw, hg, hat, hW2tr, hsto⟩,
        ?_, ?_⟩⟩
    · rw [hr5, hr4]
      refine ExH.mono0 (hx3.cas hc3.2.1.1 _ tw C) fun p hp => ?_
      rcases hp with (h1 | h2 | h3) | h4
      · exact .inr (.inl h1)
      · exact .inr (.inr (.inl h2))
      · exact .inl (by rw [h3])
      · exact .inr (.inr (.inr h4))
    · rw [hr5, hr4]; exact hnT.cas (fun _ hx => hc3.2.1.nd_ge hx) _ tw C

end Thread1

end Kraken.Promising.X64.EnvG.VecABA
