/-
**Source steps on buffers** under WeakCore's hook (`SrcSem.source P p`,
`UsesWc`): a buffer allocation and an exchange into a buffer element, as
steps of thread 0 at any stack depth, for any program. Their trace is
`main`'s exit at the configuration they land in (empty unless the
continuation is `main`'s `ret`).

- `step_source_exit`: a thread step of thread 0 that keeps the event list and
  leaves no promise, before `main` has returned, with an exit-free trace, is
  a source step whose trace is `main`'s exit where it lands.
- `bufZero`, `allocCfg`, `newBuf_src`: `let x = newBuf a τ in e` allocates
  `k · nWords us` words at the thread's next fresh label with the zero words
  of `τ` (`bufZero`, the same as `AllocSrc.newBufZero` on a closed type) and
  binds `x` to the label's locative.
- `xchgCfg`, `xchgAt_src`: `let o = xchg b[i] v in e` on a buffer of
  one-word elements reads the latest message `j` of element `i` and appends
  `v`'s word there, binding `o` to the old word.
- `laneStore_src`: `let w = asLanes sg wd K in let o = xchg b[i] w in e`:
  the lane word `K` (below `2^64`) stored into element `i` of a lanes buffer,
  as a source run.
-/
import Spike.Lib.SrcCalls

namespace Spike.Lib.SrcBuf

open CoreLang CoreTerm TermRun
open Scc.Sem Scc.Sem.SrcSem Scc.Sem.SrcOutProto
open Spike.Lib Spike.Lib.PrintSrc Spike.Lib.SrcCalls
open Scc.Sem.MemRel (SLatest)

variable {P : SrcParams} {p : Prog}

/-- **A thread step of thread 0 as a source step**: keeping the event list,
leaving thread 0 no promise, before `main` has returned and with an
exit-free trace, its trace is `main`'s exit at the configuration it lands
in. -/
theorem step_source_exit (hP : UsesWc P p) {s s' : Cfg} (h : s' ∈ threadSteps p P.k P.arch s 0)
    (hp : noPromises s' 0 = true) (htr : s'.trace = s.trace) (hex : mainExit s = [])
    (hx : ∀ c, Event.exit c ∉ s.trace) :
    (source P p).step 0 s (mainExit s') s' := by
  refine ⟨hex, .inl (.inl ⟨h, ⟨_, .refl _, hp⟩⟩), ?_⟩
  have hx' := noExit_hook hP hx
  have htr' : P.hooks.trace s' = P.hooks.trace s := by rw [hP]; simp [wcHooks, traceOf, htr]
  simp only [srcObs, hex, List.append_nil]
  rw [htr', cutAtExit_append _ hx', cutAtExit_noExit hx', cutAtExit_mainExit, List.drop_left]

/-! ## A buffer allocation -/

/-- The zero words `newBuf` gives a buffer of (closed) element type `τ`:
`zeroWords τ` when `τ` is `Zeroable`, else none (each word born `undef`). -/
def bufZero (τ : Ty) : Option (List WeakMem.Val) :=
  if zeroableIn [] [] τ then zeroWords τ else none

/-- The label of thread 0's next allocation (`th.nalloc` so far). -/
def newLbl (s : Cfg) (th : TTh) : WeakMem.AllocLabel := freshLabel s.lbase s.n 0 th.nalloc

/-- Configuration `s` after thread 0 (`th` before, `th'` after) allocates `n`
words of element type `τ` at its next label. -/
def allocCfg (s : Cfg) (th th' : TTh) (n : Nat) (τ : Ty) : Cfg :=
  { s with mem := (allocBuf (newLbl s th) n (bufZero τ) (stOf s.mem s.pairs th)).1.mem, ths := s.ths.set! 0 th' }

/-- The type `newBuf` binds: an owned array of `k` elements of `τ`, `k` of
them initialised when there are zero words, else none. -/
def bufTy (k : Nat) (τ : Ty) : Ty :=
  .refine (.loc .own (.array (.lit k) τ)) (.ini (.lit (if (bufZero τ).isSome then k else 0)))

/-- **`let x = newBuf a τ in e`** of thread 0, any frames below, no type
variables, no promises, `a` the number `k`, `τ`'s accesses `us`: one source
step allocating `k · nWords us` words at the thread's next label with
`bufZero τ`, binding `x` to the label's locative at `bufTy k τ`; memory grows
by the buffer, the event list is kept. -/
theorem newBuf_src (hP : UsesWc P p) {s : Cfg} {th : TTh} {x : String} {a : At} {τ : Ty} {e : Expr} {ta : Ty}
    {ws : List Word} {k : Nat} {us : List Acc}
    (hi : s.ths[0]? = some th) (ht : th.term = .let_ x (.newBuf a τ) e) (hσ : th.σs = []) (hp : th.promises = [])
    (hea : evalAt th.env a = some (ta, ws)) (hk : numOf ws = some k) (hus : accs τ = some us)
    (hx : ∀ c, Event.exit c ∉ s.trace) :
    ∃ th', th'.term = e ∧ th'.env = (x, bufTy k τ, [cst (.loc ⟨newLbl s th, 0⟩ 0)]) :: th.env ∧ th'.σs = [] ∧
      th'.stack = th.stack ∧ th'.promises = [] ∧ th'.nalloc = th.nalloc + 1 ∧
      (source P p).step 0 s (mainExit (allocCfg s th th' (k * nWords us) τ)) (allocCfg s th th' (k * nWords us) τ) := by
  have hus' : accs (close th.σs τ) = some us := by rw [hσ, close_nil]; exact hus
  let th' := withS { th with term := e, env := (x, bufTy k τ, [cst (.loc ⟨newLbl s th, 0⟩ 0)]) :: th.env }
    (allocBuf (newLbl s th) (k * nWords us) (bufZero τ) (stOf s.mem s.pairs th)).1
  have h : ((allocBuf (newLbl s th) (k * nWords us) (bufZero τ) (stOf s.mem s.pairs th)).1.mem, s.pairs, th') ∈
      tstep (gOf p P.k P.arch s 0) s.mem s.pairs th := by
    simp only [tstep, ht, evalOp, hea, hus', ol, List.mem_map]
    refine ⟨((allocBuf (newLbl s th) (k * nWords us) (bufZero τ) (stOf s.mem s.pairs th)).1, bufTy k τ,
      [cst (.loc ⟨newLbl s th, 0⟩ 0)]), ?_, rfl⟩
    simp only [hk, hσ, close_nil, Option.toList, Option.bind, bind, pure, List.mem_singleton]; rfl
  have hp' : th'.promises = [] := hp
  have hlt : 0 < s.ths.size := (Array.getElem?_eq_some_iff.mp hi).1
  refine ⟨th', rfl, rfl, hσ, rfl, hp', rfl, ?_⟩
  exact step_source_exit hP (Spike.Lib.SrcMem.mem_threadSteps hi h) (by simp [noPromises, allocCfg, hlt, hp'])
    rfl
    (mainExit_of_not_ret hi (fun a h => by rw [ht] at h; cases h)) hx

/-! ## An exchange into a buffer element -/

/-- Configuration `s` after thread 0 becomes `th'`, appending the message
`⟨sa, v, mv⟩`. -/
def xchgCfg (s : Cfg) (th' : TTh) (sa : WeakMem.Address) (v : WeakMem.Val) (mv : WeakMem.Ts) : Cfg :=
  { s with mem := s.mem.push ⟨sa, v, mv⟩, ths := s.ths.set! 0 th' }

/-- **`let o = xchg b[i] v in e`** of thread 0, any frames below, no
promises: `b` a locative to `sa` of a buffer of one-word elements `u`, `i`
the number `kk`, `v` one word `wv`, and `j` the latest message `m` at element
`kk`: one source step appending `wv`'s value at element `kk` and binding `o`
to `m`'s word; the event list is kept. -/
theorem xchgAt_src (hP : UsesWc P p) {s : Cfg} {th : TTh} {o : String} {b i v : At} {e : Expr} {t ti tv : Ty}
    {pw : Word} {iws : List Word} {wv : Word} {μ : Mode} {u : Ty} {sa : WeakMem.Address} {kk j : Nat}
    {m : WeakMem.Msg}
    (hi : s.ths[0]? = some th) (ht : th.term = .let_ o (.xchgAt b i v) e) (hp : th.promises = [])
    (heb : evalAt th.env b = some (t, [pw])) (hei : evalAt th.env i = some (ti, iws))
    (hev : evalAt th.env v = some (tv, [wv])) (hpw : pw.val = .loc sa 0) (hbuf : bufElem t = some (μ, u))
    (hu : accs u = some [.one]) (hk : numOf iws = some kk)
    (hj : SLatest s.mem (offs sa kk) j) (hm : s.mem[j]? = some m) (hx : ∀ c, Event.exit c ∉ s.trace) :
    ∃ th' mv, th'.term = e ∧ th'.env = (o, u, [⟨m.val, m.view, j⟩]) :: th.env ∧ th'.σs = th.σs ∧
      th'.stack = th.stack ∧ th'.promises = [] ∧
      (source P p).step 0 s (mainExit (xchgCfg s th' (offs sa kk) wv.val mv))
        (xchgCfg s th' (offs sa kk) wv.val mv) := by
  obtain ⟨th', mv, h, ht', he', hp', hσ', hst'⟩ := Spike.Lib.SrcMem.src_xchgAt_step_cfg (p := p) (k := P.k)
    (arch := P.arch) hi ht heb hei hev hpw hbuf hu hk hp hj hm
  have hlt : 0 < s.ths.size := (Array.getElem?_eq_some_iff.mp hi).1
  refine ⟨th', mv, ht', he', hσ', hst', hp', ?_⟩
  exact step_source_exit hP h (by simp [noPromises, xchgCfg, hlt, hp']) rfl
    (mainExit_of_not_ret hi (fun a h => by rw [ht] at h; cases h)) hx

/-! ## A lane-word store -/

/-- **A lane-word store into element `i` of a buffer**: thread 0 at `let w =
asLanes sg wd K in let o = xchg b[i] w in e`, any frames below, no type
variables, no promises, `b` (not `w`) a locative to `sa` of a buffer of
lanes `sg wd`, `K < 2^64`, and `j` the latest message `m` at element `i`:
a source run appending the number `K` at element `i`, with `w` bound to `K`
and `o` to `m`'s word; the event list is kept. -/
theorem laneStore_src (hP : UsesWc P p) {s : Cfg} {th : TTh} {w o b : String} {sg : Bool} {wd : Wd} {K i : Nat}
    {e : Expr} {t : Ty} {pw : Word} {μ : Mode} {sa : WeakMem.Address} {j : Nat} {m : WeakMem.Msg}
    (hi : s.ths[0]? = some th)
    (ht : th.term = .let_ w (.asLanes sg wd (.lit K)) (.let_ o (.xchgAt (.var b) (.lit i) (.var w)) e))
    (hσ : th.σs = []) (hp : th.promises = []) (hwb : b ≠ w) (heb : evalAt th.env (.var b) = some (t, [pw]))
    (hpw : pw.val = .loc sa 0) (hbuf : bufElem t = some (μ, .lanes sg wd)) (hK : K < 2 ^ 64)
    (hj : SLatest s.mem (offs sa i) j) (hm : s.mem[j]? = some m) (hx : ∀ c, Event.exit c ∉ s.trace) :
    ∃ th' mv, th'.term = e ∧
      th'.env = (o, .lanes sg wd, [⟨m.val, m.view, j⟩]) :: (w, .lanes sg wd, [cst (.num K)]) :: th.env ∧
      th'.σs = [] ∧ th'.stack = th.stack ∧ th'.promises = [] ∧
      (source P p).Run s (mainExit (xchgCfg s th' (offs sa i) (.num K) mv))
        (xchgCfg s th' (offs sa i) (.num K) mv) := by
  have hmod : K % W64 = K := Nat.mod_eq_of_lt hK
  have l1 := localStepS_asLanes (p := p) (c := ⟨th.term, th.env, none⟩) (n := K) ht rfl rfl
  rw [hmod] at l1
  let th1 : TTh := { th with term := .let_ o (.xchgAt (.var b) (.lit i) (.var w)) e,
                             env := (w, .lanes sg wd, [cst (.num K)]) :: th.env }
  have h1 := l1.2 (gOf p P.k P.arch s 0) s.mem s.pairs th rfl rfl rfl hσ
  have hT := traceThs_wc hP
  have st1 := tstep_source hT hi h1 hp (mainExit_of_not_ret hi (fun a h => by rw [ht] at h; cases h))
    (mainExit_of_not_ret (set0 hi) (fun a h => by cases h))
  have hi1 : ({ s with ths := s.ths.set! 0 th1 } : Cfg).ths[0]? = some th1 := set0 hi
  have heb1 : evalAt th1.env (.var b) = some (t, [pw]) := by
    have : (w == b) = false := by simp [Ne.symm hwb]
    simpa [th1, evalAt, lookupE, List.find?, this] using heb
  have hev1 : evalAt th1.env (.var w) = some (.lanes sg wd, [cst (.num K)]) := by
    simp [th1, evalAt, lookupE, List.find?]
  obtain ⟨th', mv, ht', he', hσ', hst', hp', st2⟩ := xchgAt_src (p := p) (s := { s with ths := s.ths.set! 0 th1 })
    hP hi1 rfl hp heb1 rfl hev1 hpw hbuf rfl rfl hj hm hx
  refine ⟨th', mv, ht', he', hσ'.trans hσ, hst', hp', ?_⟩
  have R := (run_one st1).trans (run_one st2)
  simp only [xchgCfg, set!_set!, List.nil_append] at R
  exact R

end Spike.Lib.SrcBuf
