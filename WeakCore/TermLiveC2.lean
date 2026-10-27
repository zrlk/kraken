import WeakCore.TermLiveC
/-!
# TermLiveC2 — item 15 C for protocol pairs

`HeldBy2` is `HeldBy` for a protocol pair `b`, `b.next`: under the same promise-free hypothesis (`PromFreeFrom`, a run
restriction, not a fairness condition), both words' latest values are constant from the hold on (`held2_latest_const`),
and `forced_wait_held` holds with `HeldBy2` as its hold predicate (`forced_wait_held2_thm`).

The pair C2 (`pair_new_holder`): a thread step appending at `b` or `b.next` (the pair being held) was made by the
holder.  By the op: a term addressing neither a word nor a pair carries `wd n` in its frame (`nonWdFootT_of`), which
memory also holds (`wd2_held`): two carriers; a word op writes at a non-ghost word, which cannot overlap a pair
(`AtOff_word_word2`); an `stp` writes at its own pair, which is `b`'s (`pair_overlap`), and consumes `tok2` of `rg n`;
a `casp` writes `b`, `b.next` in that order over the old latest values, which it compares against a holding state.

**Scope.**  `forced_wait_held2_thm` concludes `StuckOnW` at `b` (the pair's first word) for a thread that keeps
touching `b`; it says nothing about a thread whose target is only `b.next` (`held2_latest_const` does give the
constancy of `b.next`'s latest value, but `forced_wait_held`'s `TouchesW`/`StuckOnW` name a single address).  A
thread targeting `b.next` alone would need a word-typed `load`/`fetch`/`cas` there: for a non-ghost word this is
excluded by `word_pair_excl`; a ghost word's `load` is `NoWordRead`, so not `TouchesW`.  Covering `b.next` formally
would need a new statement (a pair variant of `forced_wait_held` with `TouchesW _ i b ∨ TouchesW _ i b.next`), which
is a G3 text.

Shared proof steps live in `TermLiveC` (`mstep_wit`, `wit_keep`, `thread_new_env`, `suffix_induct`) and
`TermLiveHeld` (`wd_held_core`, `tstep_casp_push`, and the `WdAt`/`WUnit` lemmas).
-/
namespace TermLiveC
open CoreLang CoreTerm TermRun TermSpawnStep TermExtStep TermLiveMach TermLiveL3
open WeakMem (Arch Address)

/-- `b` starts a protocol pair of `P` naming region `n` in `Eg` (`TermStep.Word2At` at the global store).  No ghost
conjunct: `Proto2` has no ghost flag, and `Word2At` (TermStep) has none. -/
def Word2AtG (Eg : TermCut.GEnv) (b : Address) (n : Nat) (P : Proto2) : Prop :=
  ∃ cl, Eg.sto b.label = some cl ∧ TermSound.AtOff cl.ty b.offset (.word2 (.lit n) P)

/-- **`HeldBy2 c b n P h`**: `HeldBy` for a protocol pair: ONE witness in which `b` starts a pair of `P` (region `n`),
`b`'s pair unit is initialised (as `HeldBy`'s word unit), the latest values of `b` and `b.next` form a held state of `P`, `h`'s bound carries `rg n`, and no promise owes it. -/
def HeldBy2 (p : Prog) (k : Promises.Knobs) (arch : Arch) (Init : TermSound.Res) (c : Cfg) (b : Address) (n : Nat)
    (P : Proto2) (h : Nat) : Prop :=
  ∃ Eg Tot HP HS cr db, TermMain.SysInvN p k arch Init (fun _ => True) c Eg Tot HP HS cr db ∧
    TermSpawn.OwnLive Eg c ∧ TermSpawn.ObsAll Eg c ∧
    Word2AtG Eg b n P ∧ (∀ cl, Eg.sto b.label = some cl → TermSound.IniAt Eg.ini cl b (.word2 (.lit n) P)) ∧
    pwf2 P = true ∧
    (∃ v0 v1, Latest c b v0 ∧ Latest c b.next v1 ∧ TermLiveHeld.HeldV2 P v0 v1) ∧
    h < c.ths.size ∧ 1 ≤ Tot h (.rg n) ∧ TermMain.Debt c db (.rg n) = 0

/-- The hold view of `HeldBy2`. -/
def hvH2 (p : Prog) (k : Promises.Knobs) (arch : Arch) (Init : TermSound.Res) : HoldView where
  heldAt c b n _ := ∃ P h, HeldBy2 p k arch Init c b n P h
  holder c b n h := ∃ P, HeldBy2 p k arch Init c b n P h

section pair
open CoreTyping TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain TermSpawn
open WeakMem (Msg Memory VState Ts AllocLabel)

/-! ### Layout -/

/-- `a` is `b` or `b.next`: same label, offset `b.offset` or `b.offset + 1`. -/
theorem near_next {a b : Address} (h : a = b ∨ a = b.next) :
    a.label = b.label ∧ @LE.le Nat _ b.offset a.offset ∧
      @LE.le Nat _ a.offset (@HAdd.hAdd Nat Nat Nat _ b.offset 1) := by
  rcases h with rfl | rfl
  · exact ⟨rfl, Nat.le_refl _, Nat.le_succ _⟩
  · exact ⟨rfl, Nat.le_succ _, Nat.le_refl _⟩

/-- `near_next` for `offs A 1`. -/
theorem near_offs {a b : Address} (h : a = b ∨ a = offs b 1) :
    a.label = b.label ∧ @LE.le Nat _ b.offset a.offset ∧
      @LE.le Nat _ a.offset (@HAdd.hAdd Nat Nat Nat _ b.offset 1) := by
  rcases h with rfl | rfl
  · exact ⟨rfl, Nat.le_refl _, Nat.le_succ _⟩
  · exact ⟨rfl, Nat.le_succ _, Nat.le_refl _⟩

/-- Two pairs of one cell that share a word are the same pair. -/
theorem pair_overlap {η : TEnv} {A b : Address} {cA : Cell} {n n' : Nat} {P P' : Proto2}
    (hsA : η.sto A.label = some cA) (hatA : AtOff cA.ty A.offset (.word2 (.lit n') P'))
    (hb : Word2At (CE η) b n P) (hl : A.label = b.label) (h1 : @LE.le Nat _ A.offset (@HAdd.hAdd Nat Nat Nat _ b.offset 1))
    (h2 : @LE.le Nat _ b.offset (@HAdd.hAdd Nat Nat Nat _ A.offset 1)) : A = b ∧ n' = n ∧ P' = P := by
  obtain ⟨cb, hcb, hatb⟩ := hb
  change η.sto b.label = some cb at hcb
  rw [← hl, hsA] at hcb
  cases hcb
  rcases AtOff_word2_word2 hatA hatb with ⟨ho, hr, hP⟩ | h | h
  · cases hr
    refine ⟨?_, rfl, hP⟩
    cases A
    cases b
    simp only at hl ho
    subst hl
    subst ho
    rfl
  · omega
  · omega

/-- A non-ghost word does not overlap a pair. -/
theorem word_pair_excl {η : TEnv} {A b : Address} {k n : Nat} {P0 : Proto} {P : Proto2}
    (hg : P0.ghost = false) (hc : ∃ c, η.sto A.label = some c ∧ AtOff c.ty A.offset (.word (.lit k) P0))
    (hloc : A = b ∨ A = b.next) (hw : Word2At (CE η) b n P) : False := by
  obtain ⟨c, hc, hat⟩ := hc
  obtain ⟨c', hc', hat'⟩ := hw
  change η.sto b.label = some c' at hc'
  obtain ⟨hl, h1, h2⟩ := near_next hloc
  rw [hl, hc'] at hc
  cases hc
  rcases AtOff_word_word2 hg hat hat' with h | h <;> omega

/-! ### The word key of a pair -/

/-- **(W1, memory half, pairs)** Memory's held part holds the word key of every initialised pair. -/
theorem wd2_held {η : TEnv} {s : St} {H : Res} {b : Address} {n : Nat} {P : Proto2}
    (hH : MemHeld (CE η) s H) (hw : Word2At (CE η) b n P)
    (hini : ∀ c, η.sto b.label = some c → IniAt η.ini c b (.word2 (.lit n) P)) :
    1 ≤ H (.wd n) := by
  obtain ⟨c, hsto, hat⟩ := hw
  exact TermLiveHeld.wd_held_core hH hsto hat (hini c hsto) (fun N e h => by cases h)
    ⟨_, accs_word2, by simp [nWords, Acc.size]⟩ (fun _ _ _ _ h => wd_le_VRR_word2 h)

/-! ### The pair C2 -/

/-- A `casp` that appends pushes its pair's two words, `A` then `A.next`, at the end of memory. -/
theorem tstep_casp_shape {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {E : TEnv}
    {acq rel : Bool} {w e0 e1 v0 v1 : At} {x : String} {ok fail : Expr}
    (hterm : th.term = .casp acq rel w e0 e1 v0 v1 x ok fail) (hm : MemInv g E (stOf mem pairs th))
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : TermLiveHeld.NewAt mem r.1 t m) :
    ∃ tw pw A m0 m1, evalAt th.env w = some (tw, [pw]) ∧ addrOf pw = some A ∧ r.1 = (mem.push m0).push m1 ∧
      m0.loc = A ∧ m1.loc = A.next ∧ (m.loc = A ∨ m.loc = A.next) := by
  obtain ⟨tw, pw, -, -, -, -, A, -, -, -, -, u0, u1, mv, hw, -, -, hA, hr1, -, -, -, -, -, -, -, -, hnew⟩ :=
    TermLiveHeld.tstep_casp_push hterm hm hr hn
  refine ⟨tw, pw, A, _, _, hw, hA, hr1, rfl, rfl, ?_⟩
  rcases hnew with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **Pair C2.**  A thread step that appends at `b` or `b.next`, where `b` starts an initialised pair whose latest
values form a held state, was made by the holder `h` (sum form, as `held_word_changes_only_by_holder_sum_noFoot`). -/
theorem pair_new_holder {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx}
    {ρ : Nat → Nat} {η : TEnv} {Rf Rs : Res} {Tot : Nat → Res} {N : Nat} {Hm : Res} {h j n : Nat}
    (hs : TermLiveHeld.TokSum Tot N Hm n) (hhN : h < N) (hjN : j < N)
    (hh : 1 ≤ Tot h (.rg n)) (hTot : Rf + Rs = Tot j)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term)
    (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf) (hE : EnvOK p η)
    (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hsc : StepScope cx th.term)
    (hH : MemHeld (CE η) (stOf mem pairs th) Hm)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) {t : Ts} {m : Msg}
    (hn : TermLiveHeld.NewAt mem r.1 t m) {b : Address} {P : Proto2} (hloc : m.loc = b ∨ m.loc = b.next)
    (hw : Word2At (CE η) b n P) (hwd : Rf (.wd n) + Hm (.wd n) ≤ 1)
    (hini : ∀ c, η.sto b.label = some c → IniAt η.ini c b (.word2 (.lit n) P)) (hpwf : pwf2 P = true)
    {u0 u1 : WeakMem.Val} (hext : Promises.Sim.MemExt mem r.1) (hL0 : Promises.LatestIs mem b u0)
    (hL1 : Promises.LatestIs mem b.next u1) (hheld : TermLiveHeld.HeldV2 P u0 u1) :
    j = h := by
  by_cases hwo : TermLiveHeld.WordOp cx th.term
  · -- a word op writes at a non-ghost word: no overlap with the pair
    exfalso
    generalize ht : th.term = t0 at hT hsc hwo
    cases t0 with
    | let_ x op e =>
      cases op with
      | store rel a v tok =>
        obtain ⟨tw, ⟨r0, P0⟩, hpk, hwd'⟩ := hwo
        obtain ⟨rt, pw, A, hea, hA, hg, hlA⟩ := TermLiveHeld.store_word_loc ht hpk hwd' hi hE htv hr hn
        rw [hlA] at hloc
        exact word_pair_excl hg (TermLiveHeld.word_cell hi.1.2.1 hpk hwd' hg hea hA) hloc hw
      | fetch o acq rel a v =>
        obtain ⟨tw, ⟨r0, P0⟩, hpk, hwd'⟩ := hwo
        cases hT with
        | let_ hop _ =>
          obtain ⟨hg, -⟩ := TermLiveHeld.fetch_word_facts hop hpk hwd' hi.1 hE htv hm hsc
          obtain ⟨rt, pw, hea, hA⟩ := TermLiveHeld.tstep_fetch_new ht hr hn
          exact word_pair_excl hg (TermLiveHeld.word_cell hi.1.2.1 hpk hwd' hg hea hA) hloc hw
      | _ => exact hwo.elim
    | cas acq rel w e v x ok fail =>
      obtain ⟨tw, ⟨r0, P0⟩, hpk, hwd'⟩ := hwo
      have hg : P0.ghost = false := by
        have hci := TermLiveHeld.cas_word_inv hT hpk hwd'
        obtain ⟨_, _, _, _, _, _, _, _, _, _, hsrc⟩ := hci
        rcases hsrc with ⟨-, -, -, hg⟩ | hep
        · exact hg
        · exact (TermLiveHeld.cas_word_epoch hpk hwd' hi.1 hE htv hm hsc hep).1
      obtain ⟨tw', pw, te, ew, tv, nw, hea, -, -, hA, -⟩ := TermLiveHeld.tstep_cas_new ht hr hn
      exact word_pair_excl hg (TermLiveHeld.word_cell hi.1.2.1 hpk hwd' hg hea hA) hloc hw
    | _ => exact hwo.elim
  by_cases hwo2 : TermLiveHeld.Word2Op cx th.term
  · generalize ht : th.term = t0 at hT hwo2
    cases t0 with
    | let_ x op e =>
      cases op with
      | stp rel a w0 w1 tk =>
        -- an `stp` writes at its own pair, which is `b`'s, and consumes `tok2` of its region
        obtain ⟨tw, ⟨r0, P0⟩, hpk, hwd'⟩ := hwo2
        cases hT with
        | let_ hop _ =>
          obtain ⟨r', i0, i1, c₁, hu, hrr⟩ := TermLiveHeld.stp_word2_tok hop hpk hwd'
          obtain ⟨hle, hsat⟩ := TermLiveHeld.tok2_frame hi hE.2.2 hu
          have he : ev ρ r0 = ev ρ r' := hrr ρ hsat
          obtain ⟨rt, pw, A, hea, hA, hlA⟩ := TermLiveHeld.tstep_stp_new ht hr hn
          obtain ⟨cA, hsA, hatA⟩ := TermLiveHeld.word2_link hi.1.2.1 hpk hwd' hea hA
          obtain ⟨la, a1, a2⟩ := near_offs hlA
          obtain ⟨lb, b1, b2⟩ := near_next hloc
          obtain ⟨-, hn', -⟩ := pair_overlap hsA hatA hw (la.symm.trans lb) (by omega) (by omega)
          have h2 : 1 ≤ Tot j (.rg n) := by
            rw [← hTot, Res.add_apply, ← hn', he]
            omega
          exact TermLiveHeld.tokUniq_of_sum hs hjN hhN h2 hh
      | _ => exact hwo2.elim
    | casp acq rel w e0 e1 w0 w1 x ok fail =>
      -- a `casp` writes `b` then `b.next` over the old latest values, compared against a holding state
      exfalso
      obtain ⟨tw, ⟨r0, P0⟩, hpk, hwd'⟩ := hwo2
      obtain ⟨tw', pw, A, x0, x1, hea, hA, hshape, hx0, hx1, hmA⟩ := tstep_casp_shape ht hm hr hn
      obtain ⟨cA, hsA, hatA⟩ := TermLiveHeld.word2_link hi.1.2.1 hpk hwd' hea hA
      obtain ⟨la, a1, a2⟩ := near_next hmA
      obtain ⟨lb, b1, b2⟩ := near_next hloc
      obtain ⟨hAb, -, -⟩ := pair_overlap hsA hatA hw (la.symm.trans lb) (by omega) (by omega)
      subst hAb
      have hx0m : r.1[mem.size]? = some x0 := by rw [hshape]; simp [Array.getElem?_push]
      have hn0 : TermLiveHeld.NewAt mem r.1 mem.size x0 := ⟨Array.getElem?_eq_none (Nat.le_refl _), hx0m⟩
      have hw0 : Word2At (CE η) x0.loc n P := by rw [hx0]; exact hw
      obtain ⟨wd0, wd1, hp0, hp1, hhold⟩ := TermLiveHeld.casp_word2_step ht hT hpk hwd' hi.1 hm hr hn0 hw0
      rw [hx0] at hp0 hp1
      obtain ⟨wa, hpa, hva⟩ := pred_of_first hext hL0 (fun t' m' h1 h2 _ => absurd h2 (by omega)) (Nat.le_refl _)
      obtain ⟨wb, hpb, hvb⟩ := pred_of_first hext hL1 (fun t' m' h1 h2 h3 => by
        have e : t' = mem.size := by omega
        subst e
        rw [hx0m] at h3
        cases h3
        rw [hx0]
        exact fun h => WeakMem.Address.next_ne _ h.symm) (Nat.le_succ _)
      rw [PredAt_uniq hp0 hpa, PredAt_uniq hp1 hpb, hva, hvb] at hhold
      exact TermLiveHeld.holds_not_heldV2 hpwf hhold hheld
    | _ => exact hwo2.elim
  · -- neither: the frame carries `wd n` (the footprint), and so does memory
    exfalso
    obtain ⟨cb, hcb, hatb⟩ := hw
    obtain ⟨hl, h1, h2⟩ := near_next hloc
    have hpu : TermLiveHeld.WdAt (CE η) m.loc n := Or.inr ⟨cb, b.offset, P, by rw [hl]; exact hcb, hatb, h1, Nat.lt_of_le_of_lt h2 (by omega)⟩
    have hf := TermLiveHeld.nonWdFootT_of hT hCk hi hE htv hm (.inl hsc) hwo hwo2 r hr t m hn n hpu
    have hmh := wd2_held hH ⟨cb, hcb, hatb⟩ hini
    omega

variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}

/-- A thread step by `j ≠ h` on a promise-free pair keeps the latest values of `b` and `b.next` (pair). -/
theorem thread_latest_keep2 {c₀ c c' : Cfg} (S : Setting p k arch Init c₀) (hrun : StepsE p k arch c₀.cap c₀ c)
    {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (hN : SysInvN p k arch Init (fun _ => True) c Eg Tot HP HS cr db)
    {b : Address} {n : Nat} {P : Proto2} {h : Nat} {v0 v1 : WeakMem.Val}
    (hW : Word2AtG Eg b n P) (hI : ∀ cl, Eg.sto b.label = some cl → IniAt Eg.ini cl b (.word2 (.lit n) P))
    (hpwf : pwf2 P = true) (hL0 : Latest c b v0) (hL1 : Latest c b.next v1) (hV : TermLiveHeld.HeldV2 P v0 v1)
    (hh : h < c.ths.size) (hT1 : 1 ≤ Tot h (.rg n)) (hA : AllNoProm c) (hA' : AllNoProm c')
    {j : Nat} (hjh : j ≠ h) (hc' : c' ∈ threadSteps p k arch c j) (hcert : Certified p k arch c' j)
    (hCN : CutNew c c' j Eg) :
    Latest c' b v0 ∧ Latest c' b.next v1 := by
  have hext : Promises.Sim.MemExt c.mem c'.mem := TermLiveProps.threadSteps_ext hc'
  obtain ⟨cl, hcl, hat⟩ := hW
  show Promises.LatestIs c'.mem b v0 ∧ Promises.LatestIs c'.mem b.next v1
  rcases thread_new_env S hrun hN hcl hA' hc' hcert hCN with hmem | ⟨th, r, ρ, η, cx, Rf, Rs, hr, e1, hj, hsum, hT, hFI,
      hE, htv, hm, hsc, hH, hini', hsub, hcut⟩
  · rw [hmem]; exact ⟨hL0, hL1⟩
  · -- a new message at `b` or `b.next` would be a pair write by `j ≠ h`
    have hno : ∀ t (m : Msg), c.mem.size ≤ t → c'.mem[t]? = some m → m.loc = b ∨ m.loc = b.next → False := by
      intro t m ht hm0 hloc
      have hw : Word2At (CE η) b n P := ⟨cl, hcut t m ht hm0 (near_next hloc).1, hat⟩
      have hini : ∀ c1, η.sto b.label = some c1 → IniAt η.ini c1 b (.word2 (.lit n) P) := fun c1 hc1 => by
        rw [hini']; exact hI c1 (hsub c1 hc1)
      have hn : TermLiveHeld.NewAt c.mem r.1 t m := ⟨Array.getElem?_eq_none ht, by rw [← e1]; exact hm0⟩
      have hext' : Promises.Sim.MemExt c.mem r.1 := by rw [← e1]; exact hext
      have W := hN.toW hA
      exact hjh (pair_new_holder (W.tokSum_thread hj n) hh hj hT1 hsum hT.1 hT.2 hFI hE htv hm hsc hH hr hn hloc
        hw (W.hwd hj hsum n) hini hpwf hext' hL0 hL1 hV)
    exact ⟨latest_ext_noNew hext (fun t m ht hm0 hl => hno t m ht hm0 (.inl hl)) hL0,
      latest_ext_noNew hext (fun t m ht hm0 hl => hno t m ht hm0 (.inr hl)) hL1⟩

/-- `HeldBy2` at fixed latest values `v0`, `v1`, without the `Debt` clause (implied on a promise-free suffix). -/
def HeldAt2 (p : Prog) (k : Promises.Knobs) (arch : Arch) (Init : Res) (c : Cfg) (b : Address) (n : Nat)
    (P : Proto2) (h : Nat) (v0 v1 : WeakMem.Val) : Prop :=
  ∃ Eg Tot HP HS cr db, SysInvN p k arch Init (fun _ => True) c Eg Tot HP HS cr db ∧
    OwnLive Eg c ∧ ObsAll Eg c ∧
    Word2AtG Eg b n P ∧ (∀ cl, Eg.sto b.label = some cl → IniAt Eg.ini cl b (.word2 (.lit n) P)) ∧
    pwf2 P = true ∧ Latest c b v0 ∧ Latest c b.next v1 ∧ TermLiveHeld.HeldV2 P v0 v1 ∧ h < c.ths.size ∧
    1 ≤ Tot h (.rg n)

/-- **One step of the held invariant, pairs** (a move by `j ≠ h` between promise-free configurations). -/
theorem heldAt2_step {c₀ c c' : Cfg} (S : Setting p k arch Init c₀) (hrun : StepsE p k arch c₀.cap c₀ c)
    {b : Address} {n : Nat} {P : Proto2} {h : Nat} {v0 v1 : WeakMem.Val}
    (hH : HeldAt2 p k arch Init c b n P h v0 v1) (hA : AllNoProm c) (hA' : AllNoProm c') {l : Nat × Lbl}
    (hlh : l.1 ≠ h) (hs : mstepE p k arch c l c') : HeldAt2 p k arch Init c' b n P h v0 v1 := by
  obtain ⟨Eg, Tot, HP, HS, cr, db, hN, hOL, hObs, ⟨cl, hcl, hat⟩, hI, hpwf, hL0, hL1, hV, hh, hT1⟩ := hH
  obtain ⟨Eg', Tot', HP', HS', cr', db', h1, h2, h3, hX, hsz, hmem⟩ := mstep_wit S hrun hN hOL hObs hA' hs
  obtain ⟨hcl', hI', hT'⟩ := wit_keep hX hcl hI hlh hh
  have hL' : Latest c' b v0 ∧ Latest c' b.next v1 := by
    rcases hmem with hm | ⟨hc', hcert, hCN⟩
    · show Promises.LatestIs c'.mem b v0 ∧ Promises.LatestIs c'.mem b.next v1
      rw [hm]; exact ⟨hL0, hL1⟩
    · exact thread_latest_keep2 S hrun hN ⟨cl, hcl, hat⟩ hI hpwf hL0 hL1 hV hh hT1 hA hA' hlh hc' hcert hCN
  exact ⟨Eg', Tot', HP', HS', cr', db', h1, h2, h3, ⟨cl, hcl', hat⟩, hI', hpwf, hL'.1, hL'.2, hV,
    Nat.lt_of_lt_of_le hh hsz, by rw [hT']; exact hT1⟩

end pair

/-- The core, pairs: both words' latest values are constant from `n₀` on. -/
theorem held2_latest_const {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : TermSound.Res} {c₀ : Cfg}
    (S : Setting p k arch Init c₀) {r : LRun (machineE p k arch).L} {D : Nat → Option Nat}
    (hr : (machineE p k arch).Run r) (h0 : r.cfg 0 = c₀) (hD : CrashOK (machineE p k arch) r D)
    {b : Address} {n : Nat} {P : Proto2} {h m n₀ : Nat} (hm : D h = some m) (hmn : m ≤ n₀)
    (hH : HeldBy2 p k arch Init (r.cfg n₀) b n P h) (hpf : PromFreeFrom r n₀) :
    ∃ v0 v1, ∀ m', n₀ ≤ m' → Latest (r.cfg m') b v0 ∧ Latest (r.cfg m') b.next v1 := by
  obtain ⟨Eg, Tot, HP, HS, cr, db, hN, hOL, hObs, hW, hI, hpwf, ⟨v0, v1, hL0, hL1, hV⟩, hh, hT1, -⟩ := hH
  have base : HeldAt2 p k arch Init (r.cfg n₀) b n P h v0 v1 :=
    ⟨Eg, Tot, HP, HS, cr, db, hN, hOL, hObs, hW, hI, hpwf, hL0, hL1, hV, hh, hT1⟩
  have hall := suffix_induct hr h0 hD hm hmn hpf (fun c => HeldAt2 p k arch Init c b n P h v0 v1) base
    (fun _ _ _ hrun hH hA hA' hlh hs => heldAt2_step S hrun hH hA hA' hlh hs)
  refine ⟨v0, v1, fun m' hm' => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hL0', hL1', -⟩ := hall m' hm'
  exact ⟨hL0', hL1'⟩

/-- The pair instance of `forced_wait_held`; its `Proto` argument is unused (sound: `HB` may ignore it). -/
theorem forced_wait_held2_thm (p : Prog) (k : Promises.Knobs) (arch : Arch) (Init : TermSound.Res) :
    forced_wait_held (machineE p k arch) (Setting p k arch Init)
      (fun c b n _ h => ∃ P2, HeldBy2 p k arch Init c b n P2 h) := by
  intro c₀ S r D i b n P h m n₀ hr h0 hD hm hmn hH hpf hs ht
  obtain ⟨P2, hH2⟩ := hH
  obtain ⟨v0, v1, hv⟩ := held2_latest_const S hr h0 hD hm hmn hH2 hpf
  exact ⟨⟨n₀, v0, fun m' hm' => (hv m' hm').1⟩, hs, ht⟩

end TermLiveC

#print axioms TermLiveC.near_next
#print axioms TermLiveC.near_offs
#print axioms TermLiveC.pair_overlap
#print axioms TermLiveC.word_pair_excl
#print axioms TermLiveC.wd2_held
#print axioms TermLiveC.tstep_casp_shape
#print axioms TermLiveC.pair_new_holder
#print axioms TermLiveC.thread_latest_keep2
#print axioms TermLiveC.heldAt2_step
#print axioms TermLiveC.held2_latest_const
#print axioms TermLiveC.forced_wait_held2_thm
