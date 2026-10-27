/-
**The levels of an `Accepted2` program's run at every reachable placement**
(AArch64; the twin of `Spike/Lib/LowerX64/Levels2.lean`): from a segment
per reachable placement `L`, `ls` from a start `P L ls`, under the memory
side over *any* family `J` containing the starts (`hlev`), the family `inv`
of `nodes2_of_segInW2`'s `hseg` (`Spike/Lib/LowerA64/HN2.lean`): one
invariant per reachable placement, each closed under the memory side over
`IN ar L0 ls0 inv` itself, containing its start.

The family is the greatest post-fixed point (`gfpN`) of the one-step
operator `LevF` (a pair at a reachable placement inside `W`, its rows
landing in the family's pending runs under the memory side over the
family, its outside moves into the family); `LevF` is monotone as the
memory side's allocation fragment and `W` are (`levF_mono`). The starts
are in it: the segments `hlev` gives at the family `gfpN` with the starts
added, together with `gfpN`, are post-fixed (`starts_le_gfpN`). The
construction generalises `Spike/Test/A64Hello1LevelsA.lean`'s two levels
(`exists_invs`) to any number of allocations.

- `msOfAX_with_xa`, `msOfAX_xa_mono`: `msOfAX` at two families differs only
  in `xa`, monotone in the family;
- `W2.mono`: `W2` at a larger family (`WrOkA.mono`, `PendA.mono`);
- `LevF`, `gfpN`, `levF_mono`, `gfpN_post`, `le_gfpN`, `starts_le_gfpN`;
- `segInvN_of_levels`: the family with its segments;
- `nodes2_of_levels`: `nodes2_of_segInW2` at the family, from segments
  inside `W2` over any family containing the starts;
- `StartsN`: the starts, the program's start at `L0`, `ls0` and every
  allocation's landing one allocation past a reachable placement;
  `xa_of_landN`: a landing is in `msOfAX`'s allocation fragment over any
  family containing the starts (the allocator's `hxa`);
- `segWS_startsN`, `nodes2_of_starts`: the levels' segments from the
  start's and the landings', and the node obligations from them;
- `SelfN`, `StartsS`, `Sg2`: the pairs carrying their own segment at every
  family containing `StartsN` (as the counter's add's held landing), the
  starts with them; `selfN_of`, `selfN_mem`, `segWS_selfN`,
  `nodes2_of_startsS`: such a pair is in every family containing
  `StartsS`, and the node obligations from segments at those families.
-/
import Spike.Lib.LowerA64.HN2

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Pend)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow.Ret0 (TakeK)
open Spike.Lib.AllocReach (Reach IN)

variable {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : Own} {ar : Arena} {L0 : Lbl} {ls0 : Lsize} {rS : Range} {Tk : State → Prop} {a : Int64}
  {Dt Ab : State → Prop} {ab : Option (State → Prop)} {K : State → State → Prop}

/-! ## Monotonicity in the family -/

/-- `msOfAX` at two families differs only in `xa`. -/
theorem msOfAX_with_xa {own' : OwnS} {I I' : InvS} {L : Lbl} {ls : Lsize} (fs : List TermRun.Frame) :
    msOfAX Λ μ p rd G own' ar I' ab L ls fs =
      { msOfAX Λ μ p rd G own' ar I ab L ls fs with xa := (msOfAX Λ μ p rd G own' ar I' ab L ls fs).xa } := by
  cases ab <;> rfl

/-- `msOfAX`'s `xa` is monotone in the family. -/
theorem msOfAX_xa_mono {own' : OwnS} {I I' : InvS} {L : Lbl} {ls : Lsize}
    (hI : ∀ lbl lsize s c fs, I lbl lsize s c fs → I' lbl lsize s c fs) (fs : List TermRun.Frame)
    {l : WeakMem.AllocLabel} {b n : Nat} {s : State} {c : Ctl}
    (h : (msOfAX Λ μ p rd G own' ar I ab L ls fs).xa l b n s c) :
    (msOfAX Λ μ p rd G own' ar I' ab L ls fs).xa l b n s c := by
  cases ab <;> exact ⟨h.1, hI _ _ _ _ _ h.2⟩

/-- **`PendA` at a larger family.** -/
theorem _root_.Spike.Lib.A64ConsumerA.PendA.mono {I I' : InvS} {L : Lbl} {ls : Lsize} {s : State} {c : Ctl}
    {fs : List TermRun.Frame}
    (hI : ∀ lbl lsize s c fs, I lbl lsize s c fs → I' lbl lsize s c fs) (h : PendA p I L ls s c fs) :
    PendA p I' L ls s c fs :=
  ⟨h.1, h.2.mono fun _ _ _ h => hI _ _ _ _ _ h⟩

/-- **The arena's write obligation at a larger family** (the counter's add
lands in the larger pending runs; `msOfA`'s fields `CtrRow` reads do not
depend on the family). -/
theorem _root_.Spike.Lib.A64ConsumerA.WrOkA.mono_fam {own' : OwnS} {I I' : InvS} {L : Lbl} {ls : Lsize}
    {fs : List TermRun.Frame}
    {s : State} {c : Ctl} (hI : ∀ lbl lsize s c fs, I lbl lsize s c fs → I' lbl lsize s c fs)
    (h : WrOkA ar L ls (msOfA Λ μ rd G own' ar I L ls fs) (fun s' c'' => PendA p I L ls s' c'' fs) s c) :
    WrOkA ar L ls (msOfA Λ μ rd G own' ar I' L ls fs) (fun s' c'' => PendA p I' L ls s' c'' fs) s c := by
  refine ⟨h.arena, fun hL => ?_⟩
  obtain ⟨k, op, g, x, a, τ, e, ta, ws, n, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h.ctr hL
  exact ⟨k, op, g, x, a, τ, e, ta, ws, n, h1, h2, h3, h4, h5, h6, h7, h8,
    fun old ha hb hc => (h9 old ha hb hc).imp id (PendA.mono hI)⟩

/-- **`W2` at a larger family.** -/
theorem W2.mono {I I' : InvS} {L : Lbl} {ls : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (hI : ∀ lbl lsize s c fs, I lbl lsize s c fs → I' lbl lsize s c fs)
    (h : W2 Λ μ p rd G own rS Tk ar I Dt Ab L ls s c fs) : W2 Λ μ p rd G own rS Tk ar I' Dt Ab L ls s c fs :=
  ⟨h.st, h.ab, h.noRet, h.run, h.place, fun c' fs' hr hs => (h.wr c' fs' hr hs).mono_fam hI, h.abort,
    h.svc1⟩

/-! ## The greatest family -/

/-- **One step of the family**: a pair at a reachable placement, inside
`W J` there, whose rows (off `K`) land in `J`'s pending runs under the
memory side over `IN … J`, and whose outside moves land in `J`. -/
def LevF (Λ : Scc.Sem.Layout) (μ : Marks) (p : Prog) (rd : TermRun.Word → Prop) (G : Loc → Val → Prop)
    (own' : OwnS) (ar : Arena) (L0 : Lbl) (ls0 : Lsize) (ab : Option (State → Prop))
    (K : State → State → Prop) (W : InvS → InvS) (J : InvS) : InvS := fun L ls s c fs =>
  Reach ar L0 ls0 L ls ∧ W J L ls s c fs ∧
    ((∀ s', ¬ K s s') → OutS p L (msOfAX Λ μ p rd G own' ar (IN ar L0 ls0 J) ab L ls) (Pend p (J L ls)) s c fs) ∧
    KOutS K p (J L ls) s c fs

/-- **The greatest family**: the pairs of some post-fixed family of `LevF`. -/
def gfpN (Λ : Scc.Sem.Layout) (μ : Marks) (p : Prog) (rd : TermRun.Word → Prop) (G : Loc → Val → Prop)
    (own' : OwnS) (ar : Arena) (L0 : Lbl) (ls0 : Lsize) (ab : Option (State → Prop))
    (K : State → State → Prop) (W : InvS → InvS) : InvS := fun L ls s c fs =>
  ∃ J : InvS, (∀ L ls s c fs, J L ls s c fs → LevF Λ μ p rd G own' ar L0 ls0 ab K W J L ls s c fs) ∧
    J L ls s c fs

variable {own' : OwnS} {W : InvS → InvS}

/-- **`LevF` is monotone**, given `W` is. -/
theorem levF_mono (hW : ∀ J J', (∀ L ls s c fs, J L ls s c fs → J' L ls s c fs) →
      ∀ L ls s c fs, W J L ls s c fs → W J' L ls s c fs)
    {J J' : InvS} (hJ : ∀ L ls s c fs, J L ls s c fs → J' L ls s c fs) {L : Lbl} {ls : Lsize} {s : State}
    {c : Ctl} {fs : List TermRun.Frame} (h : LevF Λ μ p rd G own' ar L0 ls0 ab K W J L ls s c fs) :
    LevF Λ μ p rd G own' ar L0 ls0 ab K W J' L ls s c fs := by
  obtain ⟨hR, hw, hout, hk⟩ := h
  have hIN : ∀ lbl lsize s c fs, IN ar L0 ls0 J lbl lsize s c fs → IN ar L0 ls0 J' lbl lsize s c fs :=
    fun _ _ _ _ _ ⟨hr, hj⟩ => ⟨hr, hJ _ _ _ _ _ hj⟩
  refine ⟨hR, hW J J' hJ L ls s c fs hw, fun hK => ?_, hk.mono fun _ _ _ h => hJ _ _ _ _ _ h⟩
  exact OutS.mono_xa ((hout hK).mono fun _ _ _ h => h.mono fun _ _ _ h => hJ _ _ _ _ _ h)
    (fun fs => msOfAX_with_xa fs) fun fs _ _ _ _ _ h => msOfAX_xa_mono hIN fs h

/-- **A post-fixed family is in `gfpN`.** -/
theorem le_gfpN {J : InvS} (hJ : ∀ L ls s c fs, J L ls s c fs → LevF Λ μ p rd G own' ar L0 ls0 ab K W J L ls s c fs)
    {L : Lbl} {ls : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame} (h : J L ls s c fs) :
    gfpN Λ μ p rd G own' ar L0 ls0 ab K W L ls s c fs :=
  ⟨J, hJ, h⟩

/-- **`gfpN` is post-fixed.** -/
theorem gfpN_post (hW : ∀ J J', (∀ L ls s c fs, J L ls s c fs → J' L ls s c fs) →
      ∀ L ls s c fs, W J L ls s c fs → W J' L ls s c fs)
    {L : Lbl} {ls : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (h : gfpN Λ μ p rd G own' ar L0 ls0 ab K W L ls s c fs) :
    LevF Λ μ p rd G own' ar L0 ls0 ab K W (gfpN Λ μ p rd G own' ar L0 ls0 ab K W) L ls s c fs :=
  let ⟨_, hJ, hj⟩ := h
  levF_mono hW (fun _ _ _ _ _ h => le_gfpN hJ h) (hJ _ _ _ _ _ hj)

/-- **The starts are in `gfpN`**: from a segment at every reachable
placement from its start, under the memory side over any family containing
the starts, inside `W` at that family. -/
theorem starts_le_gfpN {P : InvS}
    (hW : ∀ J J', (∀ L ls s c fs, J L ls s c fs → J' L ls s c fs) →
      ∀ L ls s c fs, W J L ls s c fs → W J' L ls s c fs)
    (hlev : ∀ J : InvS, (∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs, P L ls s c fs → J L ls s c fs) →
      ∀ L ls, Reach ar L0 ls0 L ls →
        SegWS (W J L ls) K p L (msOfAX Λ μ p rd G own' ar (IN ar L0 ls0 J) ab L ls) (P L ls) fun _ _ _ => False)
    {L : Lbl} {ls : Lsize} (hR : Reach ar L0 ls0 L ls) {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (hP : P L ls s c fs) : gfpN Λ μ p rd G own' ar L0 ls0 ab K W L ls s c fs := by
  -- the family `gfpN` with the starts added, and the segments at it
  let J0 : InvS := fun L ls s c fs => gfpN Λ μ p rd G own' ar L0 ls0 ab K W L ls s c fs ∨
    (Reach ar L0 ls0 L ls ∧ P L ls s c fs)
  have hP0 : ∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs, P L ls s c fs → J0 L ls s c fs :=
    fun _ _ hR _ _ _ hP => .inr ⟨hR, hP⟩
  let H : InvS := fun L ls s c fs => gfpN Λ μ p rd G own' ar L0 ls0 ab K W L ls s c fs ∨
    (Reach ar L0 ls0 L ls ∧ ∃ inv : FragS isaLSE2, (∀ s c fs, P L ls s c fs → inv s c fs) ∧
      (∀ s c fs, inv s c fs → W J0 L ls s c fs) ∧
      (∀ s c fs, inv s c fs →
        ((∀ s', ¬ K s s') → OutS p L (msOfAX Λ μ p rd G own' ar (IN ar L0 ls0 J0) ab L ls)
          (Pend p fun s c fs => inv s c fs ∨ False) s c fs) ∧
        KOutS K p (fun s c fs => inv s c fs ∨ False) s c fs) ∧ inv s c fs)
  have hJ0H : ∀ L ls s c fs, J0 L ls s c fs → H L ls s c fs := by
    rintro L ls s c fs (hg | ⟨hR, hP⟩)
    · exact .inl hg
    · obtain ⟨inv, hPi, hiW, hcl⟩ := hlev J0 hP0 L ls hR
      exact .inr ⟨hR, inv, hPi, hiW, hcl, hPi _ _ _ hP⟩
  have hH : ∀ L ls s c fs, H L ls s c fs → LevF Λ μ p rd G own' ar L0 ls0 ab K W H L ls s c fs := by
    rintro L ls s c fs (hg | ⟨hR, inv, hPi, hiW, hcl, hi⟩)
    · exact levF_mono hW (fun _ _ _ _ _ h => .inl h) (gfpN_post hW hg)
    · have hinvH : ∀ s c fs, (inv s c fs ∨ False) → H L ls s c fs :=
        fun s c fs h => .inr ⟨hR, inv, hPi, hiW, hcl, h.elim id False.elim⟩
      have hIN : ∀ lbl lsize s c fs, IN ar L0 ls0 J0 lbl lsize s c fs → IN ar L0 ls0 H lbl lsize s c fs :=
        fun _ _ _ _ _ ⟨hr, hj⟩ => ⟨hr, hJ0H _ _ _ _ _ hj⟩
      obtain ⟨hout, hk⟩ := hcl s c fs hi
      refine ⟨hR, hW J0 H hJ0H L ls s c fs (hiW s c fs hi), fun hK => ?_, hk.mono hinvH⟩
      exact OutS.mono_xa ((hout hK).mono fun _ _ _ h => h.mono hinvH) (fun fs => msOfAX_with_xa fs)
        fun fs _ _ _ _ _ h => msOfAX_xa_mono hIN fs h
  exact le_gfpN hH (hJ0H L ls s c fs (.inr ⟨hR, hP⟩))

/-- **The family of the levels**: from a segment at every reachable
placement from its start `P L ls`, under the memory side over any family
containing the starts, inside `W` at that family (`W` monotone in the
family), a family `inv` containing the starts, each level a segment with
its invariant explicit under the memory side over `IN … inv` itself. -/
theorem segInvN_of_levels {P : InvS}
    (hW : ∀ J J', (∀ L ls s c fs, J L ls s c fs → J' L ls s c fs) →
      ∀ L ls s c fs, W J L ls s c fs → W J' L ls s c fs)
    (hlev : ∀ J : InvS, (∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs, P L ls s c fs → J L ls s c fs) →
      ∀ L ls, Reach ar L0 ls0 L ls →
        SegWS (W J L ls) K p L (msOfAX Λ μ p rd G own' ar (IN ar L0 ls0 J) ab L ls) (P L ls) fun _ _ _ => False) :
    ∃ inv : InvS, (∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs, P L ls s c fs → inv L ls s c fs) ∧
      ∀ L ls, Reach ar L0 ls0 L ls →
        SegInvS (W inv L ls) K p L (msOfAX Λ μ p rd G own' ar (IN ar L0 ls0 inv) ab L ls) (inv L ls) := by
  refine ⟨gfpN Λ μ p rd G own' ar L0 ls0 ab K W, fun L ls hR s c fs hP => starts_le_gfpN hW hlev hR hP,
    fun L ls _ s c fs hi => ?_⟩
  obtain ⟨-, hw, hout, hk⟩ := gfpN_post hW hi
  exact ⟨hw, hout, hk⟩

/-! ## The starts: the program's start and the allocations' landings -/

/-- **The starts of the levels**: the program's start `S0` at `L0`, `ls0`,
and at every placement one allocation past a reachable one (a fresh `l` at
`b` with `n` bytes the arena hands out), the allocation's landing pairs
`E L ls l b n` (as the allocator's `Ea` node gives them). -/
def StartsN (ar : Arena) (L0 : Lbl) (ls0 : Lsize) (S0 : FragS isaLSE2)
    (E : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) : InvS := fun L' ls' s c fs =>
  (L' = L0 ∧ ls' = ls0 ∧ S0 s c fs) ∨
    ∃ L ls l b n, Reach ar L0 ls0 L ls ∧ L l = none ∧ Spike.Lib.HeapLand.AllocLand ar.heap ar.cells b n ∧
      L' = AllocReach.upd L l b ∧ ls' = AllocReach.updN ls l n ∧ E L ls l b n s c fs

/-- **The allocation fragment at a landing**: at a reachable placement, a
fresh label's landing pair `E L ls l b n` where the arena hands out `b`, `n`
is in `msOfAX`'s allocation fragment over `IN … J` for every family `J`
containing the starts (`hP`): the allocator's `hxa`. -/
theorem xa_of_landN {own' : OwnS} {S0 : FragS isaLSE2}
    {E : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {J : InvS} {L : Lbl} {ls : Lsize}
    (hP : ∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs, StartsN ar L0 ls0 S0 E L ls s c fs → J L ls s c fs)
    (hR : Reach ar L0 ls0 L ls) {l : WeakMem.AllocLabel} {b n : Nat} (hl : L l = none)
    (hAL : Spike.Lib.HeapLand.AllocLand ar.heap ar.cells b n) {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (hE : E L ls l b n s c fs) : (msOfAX Λ μ p rd G own' ar (IN ar L0 ls0 J) ab L ls fs).xa l b n s c := by
  have hR' : Reach ar L0 ls0 (AllocReach.upd L l b) (AllocReach.updN ls l n) := .step hR hl hAL
  have hJ := hP _ _ hR' s c fs (.inr ⟨L, ls, l, b, n, hR, hl, hAL, rfl, rfl, hE⟩)
  cases ab <;> exact ⟨hAL, hR', hJ⟩

/-- **The levels' segments from the start's and the landings'**: at a
family `J` containing the starts `StartsN … S0 E`, the start's segment at
`L0`, `ls0` (`h0`) and, at every placement one allocation past a reachable
one, the landing's (`h1`) give the segment from `StartsN` at every
reachable placement (`hlev` of `segInvN_of_levels`). -/
theorem segWS_startsN {own' : OwnS} {S0 : FragS isaLSE2}
    {E : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {W : Lbl → Lsize → FragS isaLSE2} {J : InvS}
    (h0 : SegWS (W L0 ls0) K p L0 (msOfAX Λ μ p rd G own' ar (IN ar L0 ls0 J) ab L0 ls0) S0 fun _ _ _ => False)
    (h1 : ∀ L ls l b n, Reach ar L0 ls0 L ls → L l = none → Spike.Lib.HeapLand.AllocLand ar.heap ar.cells b n →
      SegWS (W (AllocReach.upd L l b) (AllocReach.updN ls l n)) K p (AllocReach.upd L l b)
        (msOfAX Λ μ p rd G own' ar (IN ar L0 ls0 J) ab (AllocReach.upd L l b) (AllocReach.updN ls l n))
        (E L ls l b n) fun _ _ _ => False)
    {L' : Lbl} {ls' : Lsize} :
    SegWS (W L' ls') K p L' (msOfAX Λ μ p rd G own' ar (IN ar L0 ls0 J) ab L' ls')
      (StartsN ar L0 ls0 S0 E L' ls') fun _ _ _ => False := by
  refine SegWS.or_pre ?_ ?_
  · by_cases he : L' = L0 ∧ ls' = ls0
    · obtain ⟨rfl, rfl⟩ := he
      exact h0.mono_pre fun _ _ _ h => h.2.2
    · exact SegWS.empty fun _ _ _ h => he ⟨h.1, h.2.1⟩
  · refine (SegWS.exists_pre fun (q : (Lbl × Lsize) × WeakMem.AllocLabel × Nat × Nat) =>
      (show SegWS (W L' ls') K p L' (msOfAX Λ μ p rd G own' ar (IN ar L0 ls0 J) ab L' ls')
        (fun s c fs => Reach ar L0 ls0 q.1.1 q.1.2 ∧ q.1.1 q.2.1 = none ∧
          Spike.Lib.HeapLand.AllocLand ar.heap ar.cells q.2.2.1 q.2.2.2 ∧
          L' = AllocReach.upd q.1.1 q.2.1 q.2.2.1 ∧ ls' = AllocReach.updN q.1.2 q.2.1 q.2.2.2 ∧
          E q.1.1 q.1.2 q.2.1 q.2.2.1 q.2.2.2 s c fs) fun _ _ _ => False from ?_)).mono_pre ?_
    · obtain ⟨⟨L, ls⟩, l, b, n⟩ := q
      by_cases hq : Reach ar L0 ls0 L ls ∧ L l = none ∧ Spike.Lib.HeapLand.AllocLand ar.heap ar.cells b n ∧
          L' = AllocReach.upd L l b ∧ ls' = AllocReach.updN ls l n
      · obtain ⟨hR, hl, hAL, rfl, rfl⟩ := hq
        exact (h1 L ls l b n hR hl hAL).mono_pre fun _ _ _ h => h.2.2.2.2.2
      · exact SegWS.empty fun _ _ _ h => hq ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩
    · rintro s c fs ⟨L, ls, l, b, n, h⟩
      exact ⟨((L, ls), l, b, n), h⟩

/-! ## The consumer's node obligations from the levels -/

/-- **The consumer's node obligations from a segment at every reachable
placement inside `W2`**: as `nodes2_of_segInW2` (`Spike/Lib/LowerA64/HN2.lean`)
at the family `segInvN_of_levels` gives, its levels' segments asked at any
family `J` containing the starts `P` (`hlev`), inside `W2` over `IN … J`.
The family contains the starts. -/
theorem nodes2_of_levels {P : InvS} {Q : SrcSem.SrcParams}
    (hlev : ∀ J : InvS, (∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs, P L ls s c fs → J L ls s c fs) →
      ∀ L ls, Reach ar L0 ls0 L ls →
        SegWS (fun s c fs => W2 Λ μ p rd G own rS Tk ar (IN ar L0 ls0 J) Dt Ab L ls s c fs) (TakeK a rS) p L
          (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab L ls) (P L ls) fun _ _ _ => False)
    (hμ : μ.site .take = some a.toBitVec.toNat) :
    ∃ inv : InvS, (∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs, P L ls s c fs → inv L ls s c fs) ∧
      NodesA Λ p μ rd G (fun s _ => own s) ar (IN ar L0 ls0 inv) ab ∧
      TakePathS Λ p μ (IN ar L0 ls0 inv) rS Tk ∧ AbortPathS μ (IN ar L0 ls0 inv) Ab ar.cells ar.ctr ∧
      WriteNoPromA Λ Q p G (fun s _ => own s) (IN ar L0 ls0 inv) rS Tk μ ar ∧
      Svc1S (IN ar L0 ls0 inv) := by
  have hW : ∀ J J' : InvS, (∀ L ls s c fs, J L ls s c fs → J' L ls s c fs) →
      ∀ L ls s c fs, W2 Λ μ p rd G own rS Tk ar (IN ar L0 ls0 J) Dt Ab L ls s c fs →
        W2 Λ μ p rd G own rS Tk ar (IN ar L0 ls0 J') Dt Ab L ls s c fs :=
    fun _ _ hJ _ _ _ _ _ h => h.mono fun _ _ _ _ _ ⟨hr, hj⟩ => ⟨hr, hJ _ _ _ _ _ hj⟩
  obtain ⟨inv, hP, hseg⟩ := segInvN_of_levels (W := fun J L ls s c fs =>
    W2 Λ μ p rd G own rS Tk ar (IN ar L0 ls0 J) Dt Ab L ls s c fs) hW hlev
  exact ⟨inv, hP, nodes2_of_segInW2 hseg hμ⟩

/--
info: 'Spike.Lib.LowerA64.nodes2_of_levels' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms nodes2_of_levels

/-- **The consumer's node obligations from the start's and the landings'
segments inside `W2`** (`nodes2_of_levels` at the starts `StartsN … S0 E`,
`segWS_startsN`): at every family `J` containing the starts, the start's
segment at `L0`, `ls0` (`h0`) and every landing's one allocation past a
reachable placement (`h1`), inside `W2` over `IN … J`. The family contains
the start. -/
theorem nodes2_of_starts {S0 : FragS isaLSE2} {E : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {Q : SrcSem.SrcParams}
    (h0 : ∀ J : InvS, (∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs, StartsN ar L0 ls0 S0 E L ls s c fs →
        J L ls s c fs) →
      SegWS (fun s c fs => W2 Λ μ p rd G own rS Tk ar (IN ar L0 ls0 J) Dt Ab L0 ls0 s c fs) (TakeK a rS) p L0
        (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab L0 ls0) S0 fun _ _ _ => False)
    (h1 : ∀ J : InvS, (∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs, StartsN ar L0 ls0 S0 E L ls s c fs →
        J L ls s c fs) →
      ∀ L ls l b n, Reach ar L0 ls0 L ls → L l = none → Spike.Lib.HeapLand.AllocLand ar.heap ar.cells b n →
        SegWS (fun s c fs => W2 Λ μ p rd G own rS Tk ar (IN ar L0 ls0 J) Dt Ab (AllocReach.upd L l b)
            (AllocReach.updN ls l n) s c fs) (TakeK a rS) p (AllocReach.upd L l b)
          (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab (AllocReach.upd L l b)
            (AllocReach.updN ls l n))
          (E L ls l b n) fun _ _ _ => False)
    (hμ : μ.site .take = some a.toBitVec.toNat) :
    ∃ inv : InvS, (∀ s c fs, S0 s c fs → inv L0 ls0 s c fs) ∧
      NodesA Λ p μ rd G (fun s _ => own s) ar (IN ar L0 ls0 inv) ab ∧
      TakePathS Λ p μ (IN ar L0 ls0 inv) rS Tk ∧ AbortPathS μ (IN ar L0 ls0 inv) Ab ar.cells ar.ctr ∧
      WriteNoPromA Λ Q p G (fun s _ => own s) (IN ar L0 ls0 inv) rS Tk μ ar ∧
      Svc1S (IN ar L0 ls0 inv) := by
  obtain ⟨inv, hP, hN⟩ := nodes2_of_levels (P := StartsN ar L0 ls0 S0 E) (Q := Q)
    (fun J hJ L ls _ => segWS_startsN (W := fun L ls s c fs =>
      W2 Λ μ p rd G own rS Tk ar (IN ar L0 ls0 J) Dt Ab L ls s c fs) (h0 J hJ) (h1 J hJ)) hμ
  exact ⟨inv, fun s c fs h => hP L0 ls0 .base s c fs (.inl ⟨rfl, rfl, h⟩), hN⟩

/--
info: 'Spike.Lib.LowerA64.nodes2_of_starts' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms nodes2_of_starts

/-! ## The self-segment starts -/

/-- **The pairs carrying their own segment** (the segments `Sg J L ls Q`
from `Q` at the family `J`): at a reachable placement `L`, `ls`, a pair
from which, at every family `J` containing the starts `P`, the segment
from that pair alone holds. A pair a start's segment reaches only through
a row landing elsewhere (the counter's add, holding the old count) is
one: its own segment is the start's tail, at every such family. -/
def SelfN (ar : Arena) (L0 : Lbl) (ls0 : Lsize) (Sg : InvS → Lbl → Lsize → FragS isaLSE2 → Prop) (P : InvS) :
    InvS := fun L ls s c fs =>
  Reach ar L0 ls0 L ls ∧ ∀ J : InvS, (∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs, P L ls s c fs → J L ls s c fs) →
    Sg J L ls fun s' c' fs' => s' = s ∧ c' = c ∧ fs' = fs

/-- **The starts with the self-segment pairs**: `StartsN`'s, and the pairs
carrying their own segment (`SelfN`) over them. -/
def StartsS (ar : Arena) (L0 : Lbl) (ls0 : Lsize) (Sg : InvS → Lbl → Lsize → FragS isaLSE2 → Prop)
    (S0 : FragS isaLSE2) (E : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) : InvS :=
  fun L ls s c fs => StartsN ar L0 ls0 S0 E L ls s c fs ∨ SelfN ar L0 ls0 Sg (StartsN ar L0 ls0 S0 E) L ls s c fs

/-- **The segments of the levels inside `W2`** from `Q` at the family `J`
and the placement `L`, `ls` (`nodes2_of_startsS`'s `Sg`). -/
def Sg2 (Λ : Scc.Sem.Layout) (μ : Marks) (p : Prog) (rd : TermRun.Word → Prop) (G : Loc → Val → Prop) (own : Own)
    (rS : Range) (Tk : State → Prop) (ar : Arena) (L0 : Lbl) (ls0 : Lsize) (Dt Ab : State → Prop) (a : Int64)
    (ab : Option (State → Prop)) : InvS → Lbl → Lsize → FragS isaLSE2 → Prop := fun J L ls Q =>
  SegWS (fun s c fs => W2 Λ μ p rd G own rS Tk ar (IN ar L0 ls0 J) Dt Ab L ls s c fs) (TakeK a rS) p L
    (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab L ls) Q fun _ _ _ => False

variable {Sg : InvS → Lbl → Lsize → FragS isaLSE2 → Prop}

/-- A family containing `StartsS` contains `StartsN`. -/
theorem startsN_of_startsS {S0 : FragS isaLSE2} {E : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {J : InvS}
    (hJ : ∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs, StartsS ar L0 ls0 Sg S0 E L ls s c fs → J L ls s c fs) :
    ∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs, StartsN ar L0 ls0 S0 E L ls s c fs → J L ls s c fs :=
  fun L ls hR s c fs h => hJ L ls hR s c fs (.inl h)

/-- **A pair carrying its own segment is in every family containing
`StartsS`.** -/
theorem selfN_mem {S0 : FragS isaLSE2} {E : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {J : InvS}
    (hJ : ∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs, StartsS ar L0 ls0 Sg S0 E L ls s c fs → J L ls s c fs)
    {L : Lbl} {ls : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (h : SelfN ar L0 ls0 Sg (StartsN ar L0 ls0 S0 E) L ls s c fs) : J L ls s c fs :=
  hJ L ls h.1 s c fs (.inr h)

/-- **A pair carrying its own segment from a segment holding it**: at a
reachable placement, a segment `Sg J L ls Q` at every family containing
`P` from an entry `Q` holding the pair, `Sg` antitone in its entry
(`hSg`). -/
theorem selfN_of {P : InvS}
    (hSg : ∀ J L ls (Q Q' : FragS isaLSE2), (∀ s c fs, Q' s c fs → Q s c fs) → Sg J L ls Q → Sg J L ls Q')
    {L : Lbl} {ls : Lsize} (hR : Reach ar L0 ls0 L ls) {Q : FragS isaLSE2}
    (hQ : ∀ J : InvS, (∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs, P L ls s c fs → J L ls s c fs) → Sg J L ls Q)
    {s : State} {c : Ctl} {fs : List TermRun.Frame} (hq : Q s c fs) : SelfN ar L0 ls0 Sg P L ls s c fs :=
  ⟨hR, fun J hJ => hSg J L ls Q _ (fun _ _ _ ⟨h1, h2, h3⟩ => h1 ▸ h2 ▸ h3 ▸ hq) (hQ J hJ)⟩

/-- **The segment from the self-segment pairs** at a family `J`
containing their starts `P`: the union of their own segments, at the
segments `SegWS (W J L ls) K p L (msOfAX … (IN … J) ab L ls)`. -/
theorem segWS_selfN {own' : OwnS} {W : InvS → Lbl → Lsize → FragS isaLSE2} {P J : InvS} {L : Lbl} {ls : Lsize}
    (hJ : ∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs, P L ls s c fs → J L ls s c fs) :
    SegWS (W J L ls) K p L (msOfAX Λ μ p rd G own' ar (IN ar L0 ls0 J) ab L ls)
      (SelfN ar L0 ls0 (fun J L ls Q => SegWS (W J L ls) K p L
        (msOfAX Λ μ p rd G own' ar (IN ar L0 ls0 J) ab L ls) Q fun _ _ _ => False) P L ls) fun _ _ _ => False := by
  refine (SegWS.exists_pre fun (q : State × Ctl × List TermRun.Frame) =>
    (show SegWS (W J L ls) K p L (msOfAX Λ μ p rd G own' ar (IN ar L0 ls0 J) ab L ls)
      (fun s c fs => SelfN ar L0 ls0 (fun J L ls Q => SegWS (W J L ls) K p L
          (msOfAX Λ μ p rd G own' ar (IN ar L0 ls0 J) ab L ls) Q fun _ _ _ => False) P L ls q.1 q.2.1 q.2.2 ∧
        s = q.1 ∧ c = q.2.1 ∧ fs = q.2.2) fun _ _ _ => False from ?_)).mono_pre ?_
  · obtain ⟨s0, c0, fs0⟩ := q
    by_cases hq : SelfN ar L0 ls0 (fun J L ls Q => SegWS (W J L ls) K p L
        (msOfAX Λ μ p rd G own' ar (IN ar L0 ls0 J) ab L ls) Q fun _ _ _ => False) P L ls s0 c0 fs0
    · exact (hq.2 J hJ).mono_pre fun _ _ _ h => h.2
    · exact SegWS.empty fun _ _ _ h => hq h.1
  · intro s c fs h
    exact ⟨(s, c, fs), h, rfl, rfl, rfl⟩

/-- **The consumer's node obligations from the start's and the landings'
segments inside `W2`, with the self-segment pairs** (`nodes2_of_levels`
at the starts `StartsS … (Sg2 …) S0 E`): as `nodes2_of_starts`, the
segments asked at every family containing `StartsS`, so a pair carrying
its own segment (`SelfN`, as the counter's add's held landing) is in the
family. -/
theorem nodes2_of_startsS {S0 : FragS isaLSE2}
    {E : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {Q : SrcSem.SrcParams}
    (h0 : ∀ J : InvS, (∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs,
        StartsS ar L0 ls0 (Sg2 Λ μ p rd G own rS Tk ar L0 ls0 Dt Ab a ab) S0 E L ls s c fs → J L ls s c fs) →
      Sg2 Λ μ p rd G own rS Tk ar L0 ls0 Dt Ab a ab J L0 ls0 S0)
    (h1 : ∀ J : InvS, (∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs,
        StartsS ar L0 ls0 (Sg2 Λ μ p rd G own rS Tk ar L0 ls0 Dt Ab a ab) S0 E L ls s c fs → J L ls s c fs) →
      ∀ L ls l b n, Reach ar L0 ls0 L ls → L l = none → Spike.Lib.HeapLand.AllocLand ar.heap ar.cells b n →
        Sg2 Λ μ p rd G own rS Tk ar L0 ls0 Dt Ab a ab J (AllocReach.upd L l b) (AllocReach.updN ls l n)
          (E L ls l b n))
    (hμ : μ.site .take = some a.toBitVec.toNat) :
    ∃ inv : InvS, (∀ s c fs, S0 s c fs → inv L0 ls0 s c fs) ∧
      NodesA Λ p μ rd G (fun s _ => own s) ar (IN ar L0 ls0 inv) ab ∧
      TakePathS Λ p μ (IN ar L0 ls0 inv) rS Tk ∧ AbortPathS μ (IN ar L0 ls0 inv) Ab ar.cells ar.ctr ∧
      WriteNoPromA Λ Q p G (fun s _ => own s) (IN ar L0 ls0 inv) rS Tk μ ar ∧
      Svc1S (IN ar L0 ls0 inv) := by
  obtain ⟨inv, hP, hN⟩ := nodes2_of_levels
    (P := StartsS ar L0 ls0 (Sg2 Λ μ p rd G own rS Tk ar L0 ls0 Dt Ab a ab) S0 E) (Q := Q)
    (fun J hJ L ls _ => SegWS.or_pre
      (segWS_startsN (W := fun L ls s c fs => W2 Λ μ p rd G own rS Tk ar (IN ar L0 ls0 J) Dt Ab L ls s c fs)
        (h0 J hJ) (h1 J hJ))
      (segWS_selfN (W := fun J L ls s c fs => W2 Λ μ p rd G own rS Tk ar (IN ar L0 ls0 J) Dt Ab L ls s c fs)
        (startsN_of_startsS hJ))) hμ
  exact ⟨inv, fun s c fs h => hP L0 ls0 .base s c fs (.inl (.inl ⟨rfl, rfl, h⟩)), hN⟩

/--
info: 'Spike.Lib.LowerA64.nodes2_of_startsS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms nodes2_of_startsS

end Spike.Lib.LowerA64
