/-
**hello.w: rodata's buffer at main's `spawn`, from the start** (`VBufR`,
`helloSrc_frzL`; hello's `X64SpawnFlag.VFlag` twin, the discharge of
`HelloPreA.clonePreH_of`'s `hbuf`).

Before the spawn, hello's source has one thread, main, at one of the stages
of `X64HelloPreTerm` (`HAt`). `newBuf` (stage 3) pushes one message to each of
the buffer's words `⟨lbB, i⟩`, coherence there at it; from then on, until
lane `i`'s exchange, every later message there is one of main's promises
(`LaneU`). The exchange (stages 5, 7) stores `bufV i` there: it appends, or
fulfils a promise above coherence, hence above every earlier message, so
again every later message there is a promise (`LaneV`). Nothing else
touches the buffer's words: the other lane's exchange is to the other word,
the box's `new` (stage 18) only to the box's label, a promise step adds a
promise; and from the box's `new` on, the stored message is not the last
one. At the spawn main has no promises, so the stored messages are the
latest at their words (`BufAtSpawn`).

- `LaneU`, `LaneV`, `Lanes`: the buffer's words before and after their
  stores, by stage; `LGrow`: memory and promises grow without a new message
  at a word that is not a promise.
- `lanes_step`, `lanes_promise`: a step at stage `k` (effect `Eff k`) and a
  promise step keep `Lanes`.
- `VBufR`, `vbufR_init`, `vbufR_step`, `vbufR_run`: main's stage with
  `Lanes`, along source runs (vacuous once there are two threads).
- `pre1T_vbufR`: any hello `Pre1T` strengthened by `VBufR`.
- `helloSrc_frzL`: at `spawnTermH` with main promise-free, `BufAtSpawn` at
  the slice's label (`clonePreH_of`'s `hbuf`).

x86-64 twin of `Spike/Lib/HelloVBuf.lean` (same names, namespaces with the `X64` prefix).

**Where this differs from AArch64**: the source-run part is A64's over the x86-64 copies of hello's source
modules; `BufAtSpawn` is `X64HelloInst`'s and `slTy` `X64HelloSplit`'s; `Pre1T` is x86-64's
(`X64WakePreTi`, over the program `p`).
-/
import Spike.Lib.X64HelloPreTerm
import Spike.Lib.X64HelloClonePreHOf
import Spike.Lib.X64WakePreInv

namespace Spike.Lib.X64HelloVBuf

open CoreLang CoreTerm TermRun
open WeakMem (Address Ts Arch)
open Scc.Sem Scc.Sem.SrcSem
open Scc.Sem.MemRel (SLatest)
open Spike.Lib.X64HelloSrc (helloSrc helloS hello_start)
open Spike.Lib.X64HelloRodataSrc
open Spike.Lib.X64HelloMainPreSrc
open Spike.Lib.X64HelloPreTerm
open Spike.Lib.X64HelloSplit (slTy)
open Spike.Lib.X64HelloInst (BufAtSpawn)

/-! ## The buffer's words -/

/-- **Lane `i` before its store**: a message at `⟨lbB, i⟩` at or below
coherence there, every later message there among the promises `P`. -/
def LaneU (mem : WeakMem.Memory) (P : List Ts) (coh : Address → Ts) (i : Nat) : Prop :=
  ∃ u m, mem[u]? = some m ∧ m.loc = ⟨lbB, i⟩ ∧ u ≤ coh ⟨lbB, i⟩ ∧
    ∀ (k : Nat) m, u < k → mem[k]? = some m → m.loc = ⟨lbB, i⟩ → k ∈ P

/-- **Lane `i` after its store**: a message at `⟨lbB, i⟩` holding `bufV i`,
every later message there among the promises `P`; not the last message when
`b`. -/
def LaneV (mem : WeakMem.Memory) (P : List Ts) (i : Nat) (b : Prop) : Prop :=
  ∃ j m, mem[j]? = some m ∧ m.loc = ⟨lbB, i⟩ ∧ m.val = .num (bufV i) ∧
    (∀ (k : Nat) m, j < k → mem[k]? = some m → m.loc = ⟨lbB, i⟩ → k ∈ P) ∧ (b → j + 1 < mem.size)

/-- **The buffer's words at stage `k`**: lane 0 stored past stage 5, lane 1
past stage 7, neither the last message past the box's `new` (stage 18). -/
def Lanes (mem : WeakMem.Memory) (P : List Ts) (coh : Address → Ts) (k : Nat) : Prop :=
  (4 ≤ k → k ≤ 5 → LaneU mem P coh 0) ∧ (4 ≤ k → k ≤ 7 → LaneU mem P coh 1) ∧
    (6 ≤ k → LaneV mem P 0 (19 ≤ k)) ∧ (8 ≤ k → LaneV mem P 1 (19 ≤ k))

/-- **Growth at address `a`**: `mem'` extends `mem`, a new message at `a` is
a promise of `P'`, and a promise of `P` stays one or is a message elsewhere. -/
def LGrow (a : Address) (mem : WeakMem.Memory) (P : List Ts) (mem' : WeakMem.Memory) (P' : List Ts) : Prop :=
  (∀ k < mem.size, mem'[k]? = mem[k]?) ∧ (∀ (k : Nat) m, mem.size ≤ k → mem'[k]? = some m → m.loc = a → k ∈ P') ∧
    ∀ k ∈ P, k ∈ P' ∨ ∃ m, mem'[k]? = some m ∧ m.loc ≠ a

section Grow

variable {a : Address} {mem mem' : WeakMem.Memory} {P P' : List Ts} {i : Nat}

theorem LGrow.later {j : Nat} (hg : LGrow a mem P mem' P')
    (hl : ∀ (k : Nat) m, j < k → mem[k]? = some m → m.loc = a → k ∈ P) :
    ∀ (k : Nat) m, j < k → mem'[k]? = some m → m.loc = a → k ∈ P' := by
  intro k m hk hm ha
  rcases Nat.lt_or_ge k mem.size with h | h
  · rw [hg.1 k h] at hm
    rcases hg.2.2 k (hl k m hk hm ha) with h' | ⟨m', hm', hne⟩
    · exact h'
    · rw [hg.1 k h, hm] at hm'
      cases hm'
      exact absurd ha hne
  · exact hg.2.1 k m h hm ha

theorem laneU_grow {coh coh' : Address → Ts} (h : LaneU mem P coh i) (hg : LGrow ⟨lbB, i⟩ mem P mem' P')
    (hc : coh ⟨lbB, i⟩ ≤ coh' ⟨lbB, i⟩) : LaneU mem' P' coh' i := by
  obtain ⟨u, m, hm, hl, hu, hlat⟩ := h
  exact ⟨u, m, by rw [hg.1 u (TermLiveProps.lt_of_get hm)]; exact hm, hl, Nat.le_trans hu hc, hg.later hlat⟩

theorem laneV_grow {b b' : Prop} (h : LaneV mem P i b) (hg : LGrow ⟨lbB, i⟩ mem P mem' P')
    (hb : b' → (b ∧ mem.size ≤ mem'.size) ∨ mem.size < mem'.size) : LaneV mem' P' i b' := by
  obtain ⟨j, m, hm, hl, hv, hlat, hj⟩ := h
  have hjs := TermLiveProps.lt_of_get hm
  refine ⟨j, m, by rw [hg.1 j hjs]; exact hm, hl, hv, hg.later hlat, fun h' => ?_⟩
  rcases hb h' with ⟨h'', hs⟩ | h''
  · have := hj h''
    omega
  · omega

theorem laneV_imp {b b' : Prop} (h : LaneV mem P i b) (hb : b' → b) : LaneV mem P i b' := by
  obtain ⟨j, m, hm, hl, hv, hlat, hj⟩ := h
  exact ⟨j, m, hm, hl, hv, hlat, fun h' => hj (hb h')⟩

/-- A promise step grows memory by a promise. -/
theorem lgrow_push {x : WeakMem.Msg} : LGrow a mem P (mem.push x) (P ++ [mem.size]) := by
  refine ⟨fun k hk => TermMem.push_lt hk, fun k m hk hm _ => ?_, fun k hk => .inl (List.mem_append_left _ hk)⟩
  have := TermLiveProps.lt_of_get hm
  simp only [Array.size_push] at this
  obtain rfl : k = mem.size := by omega
  simp

/-- Lane `i`'s exchange grows memory without a message at another word. -/
theorem lgrow_lane {th th' : TTh} {i' : Nat} (hi : i ≠ i') (he : LaneE i mem th mem' th') :
    LGrow ⟨lbB, i'⟩ mem th.promises mem' th'.promises := by
  obtain ⟨⟨t, (⟨⟨v, rfl⟩, rfl, hp⟩ | ⟨rfl, ht, hp, -, m, hm, hl, -⟩)⟩, -⟩ := he
  · refine ⟨fun k hk => TermMem.push_lt hk, fun k m hk hm ha => ?_, fun k hk => .inl (hp ▸ hk)⟩
    have := TermLiveProps.lt_of_get hm
    simp only [Array.size_push] at this
    obtain rfl : k = mem.size := by omega
    rw [Array.getElem?_push_size] at hm
    cases hm
    simp at ha
    exact absurd ha hi
  · refine ⟨fun _ _ => rfl, fun k m hk hm _ => absurd (TermLiveProps.lt_of_get hm) (by omega), fun k hk => ?_⟩
    rw [hp]
    by_cases hkt : k = t
    · subst hkt
      exact .inr ⟨m, hm, by rw [hl]; simpa using hi⟩
    · exact .inl ((List.mem_erase_of_ne hkt).mpr hk)

/-- The box's `new` grows memory without a message to the buffer. -/
theorem lgrow_box {th th' : TTh} (he : BoxE mem th mem' th') :
    LGrow ⟨lbB, i⟩ mem th.promises mem' th'.promises := by
  obtain ⟨-, hpre, hnew, hpr, -⟩ := he
  refine ⟨hpre, fun k m hk hm ha => ?_, fun k hk => (hpr k hk).imp id fun ⟨m, hm, hl⟩ => ⟨m, hm, fun ha => ?_⟩⟩
  · have := hnew k m hk hm
    rw [ha] at this
    exact ((by decide : ¬ (2 : Nat) = 4) this).elim
  · rw [ha] at hl
    exact (by decide : ¬ (2 : Nat) = 4) hl

/-- `newBuf` starts lane `i`. -/
theorem laneU_newBuf {th th' : TTh} (he : NewBufE mem th mem' th') (hi : i < 2) :
    LaneU mem' th'.promises th'.vs.coh i := by
  obtain ⟨hsz, -, hm, hc, -⟩ := he
  obtain ⟨m, hmi, hl⟩ := hm i hi
  refine ⟨mem.size + i, m, hmi, hl, Nat.le_of_eq (hc i hi).symm, fun k m' hk hm' hl' => ?_⟩
  exfalso
  have := TermLiveProps.lt_of_get hm'
  obtain ⟨m1, hm1, hl1⟩ := hm 1 (by decide)
  have hk' : mem.size + i < k := hk
  obtain rfl : k = mem.size + 1 := by rw [hsz] at this; omega
  rw [hm1] at hm'
  cases hm'
  rw [hl1] at hl'
  simp only [WeakMem.Address.mk.injEq, true_and] at hl'
  simp only [WeakMem.Offset] at hl'
  omega

/-- Lane `i`'s exchange stores it. -/
theorem laneV_lane {th th' : TTh} {b : Prop} (h : LaneU mem th.promises th.vs.coh i)
    (he : LaneE i mem th mem' th') (hb : ¬ b) : LaneV mem' th'.promises i b := by
  obtain ⟨u, mu, hmu, hlu, hu, hlat⟩ := h
  obtain ⟨⟨t, (⟨⟨v, rfl⟩, rfl, hp⟩ | ⟨rfl, ht, hp, hct, m, hm, hl, hv⟩)⟩, -⟩ := he
  · refine ⟨mem.size, _, Array.getElem?_push_size, rfl, rfl, fun k m hk hm _ => ?_, fun h => (hb h).elim⟩
    have := TermLiveProps.lt_of_get hm
    simp only [Array.size_push] at this
    omega
  · refine ⟨t, m, hm, hl, hv, fun k m' hk hm' hl' => ?_, fun h => (hb h).elim⟩
    rw [hp]
    have hu' : u < k := Nat.lt_of_le_of_lt hu (Nat.lt_trans hct hk)
    exact (List.mem_erase_of_ne (by omega)).mpr (hlat k m' hu' hm' hl')

end Grow

/-! ## Along main's stages -/

section Stages

variable {mem mem' : WeakMem.Memory} {th th' : TTh} {k : Nat}

theorem lanes_zero {P : List Ts} {coh : Address → Ts} : Lanes mem P coh 0 :=
  ⟨fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide),
    fun h => absurd h (by decide)⟩

/-- A step at a stage other than 3, 5, 7, 18 keeps memory, promises and coherence. -/
theorem eff_other (h3 : k ≠ 3) (h5 : k ≠ 5) (h7 : k ≠ 7) (h18 : k ≠ 18) (he : Eff k mem th mem' th') :
    mem' = mem ∧ th'.promises = th.promises ∧ th'.vs.coh = th.vs.coh := by
  unfold Eff at he
  split at he
  · exact absurd rfl h3
  · exact absurd rfl h5
  · exact absurd rfl h7
  · exact absurd rfl h18
  · exact he

/-- **A step at stage `k` keeps `Lanes`** (into stage `k + 1`). -/
theorem lanes_step (h : Lanes mem th.promises th.vs.coh k) (he : Eff k mem th mem' th') :
    Lanes mem' th'.promises th'.vs.coh (k + 1) := by
  by_cases h3 : k = 3
  · subst h3
    exact ⟨fun _ _ => laneU_newBuf he (by decide), fun _ _ => laneU_newBuf he (by decide),
      fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
  by_cases h5 : k = 5
  · subst h5
    exact ⟨fun _ h => absurd h (by decide),
      fun _ _ => laneU_grow (h.2.1 (by decide) (by decide)) (lgrow_lane (by decide) he) (he.2 _ (by decide)),
      fun _ => laneV_lane (h.1 (by decide) (by decide)) he (by decide), fun h => absurd h (by decide)⟩
  by_cases h7 : k = 7
  · subst h7
    exact ⟨fun _ h => absurd h (by decide), fun _ h => absurd h (by decide),
      fun _ => laneV_grow (h.2.2.1 (by decide)) (lgrow_lane (by decide) he) (fun h => absurd h (by decide)),
      fun _ => laneV_lane (h.2.1 (by decide) (by decide)) he (by decide)⟩
  by_cases h18 : k = 18
  · subst h18
    exact ⟨fun _ h => absurd h (by decide), fun _ h => absurd h (by decide),
      fun _ => laneV_grow (h.2.2.1 (by decide)) (lgrow_box he) (fun _ => .inr he.1),
      fun _ => laneV_grow (h.2.2.2 (by decide)) (lgrow_box he) (fun _ => .inr he.1)⟩
  obtain ⟨rfl, hp, hc⟩ := eff_other h3 h5 h7 h18 he
  rw [hp, hc]
  exact ⟨fun a b => h.1 (by omega) (by omega), fun a b => h.2.1 (by omega) (by omega),
    fun a => laneV_imp (h.2.2.1 (by omega)) (fun h' => by omega),
    fun a => laneV_imp (h.2.2.2 (by omega)) (fun h' => by omega)⟩

/-- **A promise step keeps `Lanes`.** -/
theorem lanes_promise {P : List Ts} {coh : Address → Ts} {x : WeakMem.Msg} (h : Lanes mem P coh k) :
    Lanes (mem.push x) (P ++ [mem.size]) coh k :=
  ⟨fun a b => laneU_grow (h.1 a b) lgrow_push (Nat.le_refl _),
    fun a b => laneU_grow (h.2.1 a b) lgrow_push (Nat.le_refl _),
    fun a => laneV_grow (h.2.2.1 a) lgrow_push (fun hb => .inl ⟨hb, by simp⟩),
    fun a => laneV_grow (h.2.2.2 a) lgrow_push (fun hb => .inl ⟨hb, by simp⟩)⟩

/-- No stage is at an extern call. -/
theorem hat_not_ext {wo0 wo1 : Word} (h : HAt th k wo0 wo1) {x : String} {n : ExtName} {a : At} {e : Expr}
    (ht : th.term = .let_ x (.ext n a) e) : False := by
  obtain ⟨hk, hterm, -⟩ := h
  rw [hterm] at ht
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _
  | 14, _ | 15, _ | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ =>
    simp [hc, Scc.Sem.SrcSem.setupTerm, rdC0, rdBody, eM, rdCN, eB, rdCA, eW0, rdC1, eO0, rdC2, eW1, rdC3, eO1,
      rdC4, eS, rdC5, eN, eSm, eSl0, ePack, rdRet, eRet, SrcCalls.setupCont, mainC, mainBodyH, zTerm, c0H,
      newTerm, boxTermH, p0Term, pTerm, spawnTermH] at ht
  | _ + 23, hk => omega

/-- Only stage 22 is at `spawnTermH`. -/
theorem hat_spawnTerm {wo0 wo1 : Word} (h : HAt th k wo0 wo1) (ht : th.term = spawnTermH) : k = 22 := by
  obtain ⟨hk, hterm, -⟩ := h
  rw [hterm] at ht
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _
  | 14, _ | 15, _ | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ =>
    simp [hc, Scc.Sem.SrcSem.setupTerm, rdC0, rdBody, eM, rdCN, eB, rdCA, eW0, rdC1, eO0, rdC2, eW1, rdC3, eO1,
      rdC4, eS, rdC5, eN, eSm, eSl0, ePack, rdRet, eRet, SrcCalls.setupCont, mainC, mainBodyH, zTerm, c0H,
      newTerm, boxTermH, p0Term, pTerm, spawnTermH] at ht
  | 22, _ => rfl
  | _ + 23, hk => omega

end Stages

/-! ## Along source runs -/

/-- **The pre-spawn buffer invariant**: with one thread, main is at a stage
`k` of `HAt` (label base 0, capacity 2) with `Lanes` at its promises and
coherence. -/
def VBufR (s : Cfg) : Prop :=
  s.ths.size = 1 → ∃ th0 k wo0 wo1, s.ths[0]? = some th0 ∧ s.lbase = 0 ∧ s.cap = 2 ∧ HAt th0 k wo0 wo1 ∧
    Lanes s.mem th0.promises th0.vs.coh k

theorem set!_self {α : Type} {a : Array α} {i : Nat} {y : α} (h : a[i]? = some y) (x : α) :
    (a.set! i x)[i]? = some x := by
  have hi : i < a.size := (Array.getElem?_eq_some_iff.mp h).1
  simp [Array.set!_eq_setIfInBounds, hi]

theorem vbufR_init {arch : Arch} {s : Cfg} (h : (helloS arch).init s) : VBufR s := by
  have h' : s = Spike.Lib.X64WakeT1.setupStartT 2 := by
    change Spike.Lib.X64WakeT1.progInitT helloSrc 2 s at h
    rw [hello_start] at h
    exact h
  subst h'
  intro _
  exact ⟨_, 0, meW, meW, rfl, rfl, rfl, hat_start, lanes_zero⟩

/-- **One source step keeps `VBufR`.** -/
theorem vbufR_step {arch : Arch} {i : Nat} {s s' : Cfg} {es : List Ev} (h : (helloS arch).step i s es s')
    (hv : VBufR s) : VBufR s' := by
  intro h1'
  obtain ⟨-, hs, -⟩ := h
  rcases hs with hs | hs | hs
  · have h1 : s.ths.size = 1 := stepBy_size hs ▸ h1'
    obtain ⟨th0, k, wo0, wo1, h0, hb, hcap, hat, hl⟩ := hv h1
    rcases hs with ⟨hm, -⟩ | ⟨a, v, w, hi', -, -, rfl⟩
    · unfold TermRun.threadSteps at hm
      split at hm
      · simp at hm
      · rename_i th hth
        obtain rfl : i = 0 := by have := (Array.getElem?_eq_some_iff.mp hth).1; omega
        rw [h0] at hth
        cases hth
        obtain ⟨⟨mem, pairs, th'⟩, hr, rfl⟩ := List.mem_map.mp hm
        have hn : s.n = 2 := by simp [Cfg.n, hcap, h1]
        obtain ⟨wo0', wo1', hat', he⟩ := hat_tstep rfl hb hn rfl hat hr
        exact ⟨th', k + 1, wo0', wo1', set!_self h0 _, hb, hcap, hat', lanes_step hl he⟩
    · obtain rfl : i = 0 := by omega
      unfold TermRun.promise
      rw [h0]
      exact ⟨_, k, wo0, wo1, set!_self h0 _, hb, hcap, hat, lanes_promise hl⟩
  · have := (spawnBy_size hs).1
    obtain ⟨x, f, a, T, ts, e, th, rt, ws, hth, -⟩ := hs
    have := (Array.getElem?_eq_some_iff.mp hth).1
    omega
  · obtain ⟨x, n, a, e, th, rt, ws, rs, hth, hterm, -, -, -, -, rfl⟩ := hs
    have h1 : s.ths.size = 1 := by rwa [TermExtStep.wake_size, TermExtStep.extCfg_size] at h1'
    obtain ⟨th0, k, wo0, wo1, h0, -, -, hat, -⟩ := hv h1
    obtain rfl : i = 0 := by have := (Array.getElem?_eq_some_iff.mp hth).1; omega
    rw [h0] at hth
    cases hth
    exact (hat_not_ext hat hterm).elim

/-- **`VBufR` along source runs.** -/
theorem vbufR_run {arch : Arch} {s s' : Cfg} {tr : List Ev} (h : (helloS arch).Run s tr s') (hv : VBufR s) :
    VBufR s' := by
  induction h with
  | refl => exact hv
  | step hs _ ih =>
    obtain ⟨i, hs⟩ := hs
    exact ih (vbufR_step hs hv)

open Kraken.Promising Kraken.Promising.X64 Scc.Sem.X64 Spike.Lib.X64WakeT1 Spike.Lib.X64WakePreTi in
/-- **`Pre1T` with `VBufR`** (any hello `Pre1T`). -/
theorem pre1T_vbufR {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {B : Budget} {asm : Asm} {E : Entry}
    {R1 : Spike.Lib.X64WakeA64.Cfg → TermRun.Cfg → Prop} {Ab Ac : Kraken.Promising.X64.State → Prop}
    (O : Pre1T arch Λ B asm E R1 Ab Ac helloSrc) :
    Pre1T arch Λ B asm E (fun d s => R1 d s ∧ VBufR s) Ab Ac helloSrc :=
  Spike.Lib.X64WakePreInv.Pre1T.invSrc O VBufR (fun _ h => vbufR_init h) (fun _ _ _ hr hv => vbufR_run hr hv)

/-! ## At the spawn -/

/-- With no promise, a stored lane is the latest message at its word. -/
theorem slatest_of_laneV {mem : WeakMem.Memory} {i : Nat} {b : Prop} (h : LaneV mem [] i b) (hb : b) :
    ∃ j m, SLatest mem ⟨lbB, i⟩ j ∧ mem[j]? = some m ∧ m.val = .num (bufV i) ∧ j + 1 < mem.size := by
  obtain ⟨j, m, hm, hl, hv, hlat, hj⟩ := h
  exact ⟨j, m, ⟨⟨m, hm, hl⟩, fun k m' hk hm' hl' => by simpa using hlat k m' hk hm' hl'⟩, hm, hv, hj hb⟩

/-- **Rodata's buffer at main's `spawn`** (`clonePreH_of`'s `hbuf`): along
source runs (`VBufR`), with main the only thread, promise-free, at
`spawnTermH`, the slice's label `lb` holds `bufW 0`, `bufW 1` as its words'
latest messages, neither the last message. -/
theorem helloSrc_frzL {s : Cfg} {th0 : TTh} {l : WeakMem.AllocLabel} {ws : List Word} {lb : WeakMem.AllocLabel}
    {hd : Option (Nat × Word)} (hv : VBufR s) (hs : s.ths = #[th0]) (hp : th0.promises = [])
    (hS : SpawnSrcH l ws ⟨th0.term, th0.env, hd⟩) (hh : ws.head? = some (cst (.loc ⟨lb, 0⟩ 0))) :
    BufAtSpawn s lb := by
  obtain ⟨th, k, wo0, wo1, h0, -, -, hat, hl⟩ := hv (by rw [hs]; rfl)
  rw [hs] at h0
  obtain rfl : th0 = th := by simpa using h0
  obtain rfl := hat_spawnTerm hat hS.1
  have hsl := hS.2.2.2.2.1
  change evalAt th0.env (.var "sl") = some (slTy, ws) at hsl
  rw [hat.2.2.1] at hsl
  simp [hc, envP0, envC, envO, c0H, envS, evalAt, lookupE] at hsl
  subst hsl
  simp [cst, Promises.TVal.mk0] at hh
  subst hh
  rw [hp] at hl
  intro i hi
  obtain rfl | rfl : i = 0 ∨ i = 1 := by simp only [WeakMem.Offset] at hi ⊢; omega
  · exact slatest_of_laneV (hl.2.2.1 (by decide)) (by decide)
  · exact slatest_of_laneV (hl.2.2.2 (by decide)) (by decide)

/-- info: 'Spike.Lib.X64HelloVBuf.pre1T_vbufR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pre1T_vbufR

/-- info: 'Spike.Lib.X64HelloVBuf.helloSrc_frzL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms helloSrc_frzL

end Spike.Lib.X64HelloVBuf
