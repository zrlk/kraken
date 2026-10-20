import WeakCore.TermStoreNI

/-!
# TermSeenHid: `SeenHid` from the memory invariant

`TermStoreNI.SeenHid` (every protocol-word unit `b` a plain store writes is
hidden at the store's bound `Bnd`) from the stepper's `MemInv` at its cut,
`PromNotUndef` (`SysInvN.promNU`), scope (no region references), and two
named state facts:

* `EnvVR th`: every word of the frame's environment has view at most its read
  timestamp (so a frontier below the pointer's view is below `dep pw`);
* `UndefAt E mem`: every protocol-word unit of a cell of the cut has an `undef` message (its
  allocation placeholder; a protocol word is never zeroed).  Where a frontier hides the unit's
  placeholders (`PubDefP`, `OwnHidP.2`), the placeholder's hider is a message at or below the
  frontier (`msg_of_undef`).

Cases, on the stored unit's cell `cl` (at the reference's target, `cell_target`):

* `cl` foreign (so published, `SeenOwn`: not seen, so `f ≤ pw.view`): `PubDefP`
  hides its placeholders below the frontier `f`;
* `cl` own, the slot below the real count: `OwnOKSF`/`LatestSF` at `coh b`;
* `cl` own, the slot past the real count (a `pub` reference only, `modeIni`):
  `OwnHidP.2` hides them below the frontier, not seen, so `f ≤ pw.view`.

(H) The store's other guarded units, designated starts of predicted units (`PredU ∧ DStart`), are
in own all-`.one` buffers past the real count: the `pub` case above, with the unit's message at `coh`
(`LatestSF`, the unit lies in the buffer).

Own outstanding promises are not `undef` (`PromNotUndef`), and typed words at a
protocol-word unit, or anywhere in an all-`.one` buffer, are not `undef` (`undef_not_wordOK`,
`undef_not_wordOK_buf`).
-/

namespace TermSeenHid
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermTyped TermStoreNI
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- (named state fact) Every word of the frame's environment has view at most its read timestamp. -/
def EnvVR (th : TTh) : Prop :=
  ∀ (a : At) (rt : Ty) (ws : List Word) (w : Word), evalAt th.env a = some (rt, ws) → w ∈ ws → w.view ≤ w.rts

/-- (named state fact) Every protocol-word unit of a cell of `E` has a message, at or below the
cell's frontier when it has one. -/
def FrontW (E : TEnv) (mem : Memory) : Prop :=
  ∀ (b : Address) (n : Nat) (P : Proto), WordAt E b n P →
    ∃ (t : Nat) (m : Msg), mem[t]? = some m ∧ m.loc = b ∧ ∀ f, E.pfr b.label = some f → t ≤ f

/-- (named state fact) Every protocol-word unit of a cell of `E` has an `undef` message. -/
def UndefAt (E : TEnv) (mem : Memory) : Prop :=
  ∀ (b : Address) (n : Nat) (P : Proto), WordAt E b n P →
    ∃ (t : Nat) (m : Msg), mem[t]? = some m ∧ m.loc = b ∧ m.val = .undef

/-! ## Value facts at a protocol-word unit -/

theorem oneAt_mid : ∀ (pre post : List Acc), TermFul.OneAt (pre ++ [Acc.one] ++ post) (nWords pre)
  | [], post => by simpa [nWords] using TermFul.OneAt.here post
  | u :: pre, post => by
      have h := TermFul.OneAt.cons u (oneAt_mid pre post)
      have e : nWords (u :: pre) = nWords pre + u.size := by simp [nWords]; omega
      rw [e]; simpa using h

theorem accs_word {n : Nat} {P : Proto} (hg : P.ghost = false) :
    accs (.word (.lit n) P) = some [Acc.one] := by simp [accs, hg]

/-- A typed word at a protocol-word unit is not `undef`. -/
theorem undef_not_wordOK {E : TEnv} {T : Ty} {o n : Nat} {P : Proto} (hat : AtOff T o (.word (.lit n) P))
    (hg : P.ghost = false) {w : Word} (hw : w.val = .undef) : ¬ WordOK E T o w := by
  intro h
  obtain ⟨w0, hvr, hle⟩ := wordOK_one h hat (accs_word hg)
  have hnu := VR_one_nundef _ hvr (accs_word hg)
  exact hnu 0 w0 (TermFul.OneAt.here []) rfl (hle.1.trans hw)

/-- A value's word at a protocol-word unit is not `undef`. -/
theorem valOf_nundef {E : TEnv} {T : Ty} {L : List Acc} {ws : List Word} {o n : Nat} {P : Proto}
    (hv : ValOf E T ws) (hL : accs T = some L) (hat : AtOff T o (.word (.lit n) P)) (hg : P.ghost = false)
    {w : Word} (hw : ws[o]? = some w) : w.val ≠ .undef := by
  have hnu := VR_one_nundef T hv.1 hL
  obtain ⟨pre, post, e, hn⟩ := AtOff_embed hat hL (accs_word hg)
  subst e
  exact hnu o w (hn ▸ oneAt_mid pre post) hw

/-- The cell words of an own cell below its real count are not `undef` at a protocol-word unit. -/
theorem own_val {E : TEnv} {l : AllocLabel} {cl : Cell} {vals : List Word} {o n : Nat} {P : Proto}
    (hcell : CellOK E (E.rc l) cl.ty vals) (hat : AtOff cl.ty o (.word (.lit n) P)) (hg : P.ghost = false)
    (hr : ∀ N e us, cl.ty = .array (.lit N) e → accs e = some us → o < E.rc l * nWords us) :
    ∃ w, vals[o]? = some w ∧ w.val ≠ .undef := by
  rcases hcell with ⟨hwc, hv⟩ | ⟨N, e, us, hty, hus, -, hlen, hsl⟩
  · obtain ⟨L, hL⟩ : ∃ L, accs cl.ty = some L := by
      cases h : accs cl.ty with
      | none => simp [wc, h] at hwc
      | some L => exact ⟨L, rfl⟩
    have hlenL : vals.length = nWords L := by
      simp only [wc, hL, Option.map_some, Option.some.injEq] at hwc; exact hwc.symm
    have hb := AtOff_bound hat hL (accs_word hg)
    have h1 : nWords [Acc.one] = 1 := rfl
    have hlt : o < vals.length := by rw [hlenL]; omega
    exact ⟨vals[o], List.getElem?_eq_getElem hlt, valOf_nundef hv hL hat hg (List.getElem?_eq_getElem hlt)⟩
  · rcases AtOff_arr_elem hat hty with h | ⟨us', j', o', hus', hj', ho, hat'⟩
    · rw [hty] at h; cases h
    · rw [hus] at hus'; cases hus'
      have hb := AtOff_bound hat' hus (accs_word hg)
      have h1 : nWords [Acc.one] = 1 := rfl
      have hrl := hr N e us hty hus
      have hjr : j' < E.rc l := by
        refine Nat.lt_of_not_le fun hle => ?_
        have := Nat.mul_le_mul_right (nWords us) hle
        omega
      have hv := hsl j' hjr
      have hN : (j' + 1) * nWords us ≤ N * nWords us := Nat.mul_le_mul_right _ hj'
      rw [Nat.succ_mul] at hN
      have hlt : o < vals.length := by rw [hlen]; omega
      have hw : ((vals.drop (j' * nWords us)).take (nWords us))[o']? = vals[o]? := by
        rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop]
        congr 1; omega
      exact ⟨vals[o], List.getElem?_eq_getElem hlt,
        valOf_nundef hv hus hat' hg (by rw [hw]; exact List.getElem?_eq_getElem hlt)⟩

/-- Every position below a slot's width is a `.one` unit, when all the slot's units are. -/
theorem oneAt_all_one : ∀ {us : List Acc}, (∀ u ∈ us, u = .one) → ∀ {o : Nat}, o < nWords us →
    TermFul.OneAt us o
  | [], _, o, h => by simp [nWords] at h
  | u :: us, h1, o, h => by
      have hu : u = .one := h1 u (by simp)
      subst hu
      have hs : Acc.one.size = 1 := rfl
      have e : nWords (Acc.one :: us) = nWords us + Acc.one.size := by simp [nWords]; omega
      cases o with
      | zero => exact TermFul.OneAt.here us
      | succ o =>
          have ih := oneAt_all_one (us := us) (fun v hv => h1 v (List.mem_cons_of_mem _ hv)) (o := o) (by omega)
          have h2 := TermFul.OneAt.cons Acc.one ih
          rw [hs] at h2; exact h2

/-- (H) A typed word of a buffer whose element units are all `.one` is not `undef`, at any offset. -/
theorem undef_not_wordOK_buf {E : TEnv} {T e : Ty} {N o : Nat} {us : List Acc}
    (hty : T = .array (.lit N) e) (he : accs e = some us) (h1 : ∀ u ∈ us, u = .one)
    {w : Word} (hw : w.val = .undef) : ¬ WordOK E T o w := by
  intro hW
  obtain ⟨b, S, ws, o', w0, hseg, ⟨⟨hvr, -⟩, hsh⟩, hw0, hle, -⟩ := hW
  rcases hseg with ⟨-, -, hT⟩ | ⟨N', us', j', hT', hus', -, -⟩
  · rw [hty] at hT; simp [accs] at hT
  · rw [hty] at hT'
    simp only [Ty.array.injEq, Idx.lit.injEq] at hT'
    obtain ⟨-, hSe⟩ := hT'
    rw [← hSe] at hvr hsh
    have hlt : o' < ws.length := (List.getElem?_eq_some_iff.1 hw0).1
    rw [hsh us he] at hlt
    exact VR_one_nundef _ hvr he o' w0 (oneAt_all_one h1 hlt) hw0 (hle.1.trans hw)

/-- A unit of a reference into a buffer lies inside the buffer. -/
theorem off_lt_buf {T U e : Ty} {N o j : Nat} {us us' : List Acc} (hat : AtOff T o U)
    (hty : T = .array (.lit N) e) (he : accs e = some us') (hU : accs U = some us) (hj : j < nWords us) :
    o + j < N * nWords us' := by
  rcases AtOff_arr_elem hat hty with h | ⟨us0, j0, o0, h0, hj0, ho, hat0⟩
  · rw [h, hty] at hU; simp [accs] at hU
  · have hb := AtOff_bound hat0 h0 hU
    have e0 : us0 = us' := Option.some.inj (h0.symm.trans he)
    rw [e0] at hb ho
    have h2 : (j0 + 1) * nWords us' ≤ N * nWords us' := Nat.mul_le_mul_right _ hj0
    rw [Nat.succ_mul] at h2
    omega

/-! ## The store's target -/

theorem cellOf_of_wordOf {t : Ty} {r : Idx} {P : Proto} (h : wordOf t = some (r, P)) :
    ∃ μ, cellOf t = some (μ, .word r P) := by
  unfold wordOf at h
  split at h
  · cases h; exact ⟨_, rfl⟩
  · cases h; exact ⟨_, rfl⟩
  · cases h

/-- A typed, in-scope store's reference: a non-region reference type whose pointee passes `opaqueOK`. -/
theorem store_target {p : Prog} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → Nat → List Word → Res → Prop}
    {cx : Cx} {env : Env} {Rf : Res} {x : String} {rel : Bool} {a v : At} {tok : Option At} {e : Expr}
    (hT : Typed p cx (.let_ x (.store rel a v tok) e)) (hi : FInvR ρ η σs K cx env Rf) (htv : TvOK cx)
    (hsc : StepScope cx (.let_ x (.store rel a v tok) e) ∨ StepScopeR σs cx (.let_ x (.store rel a v tok) e)) :
    ∃ t μ u, cx.peek a = .ok t ∧ cellOf t = some (μ, u) ∧ cx.opaqueOK u = true ∧ ∀ r, μ ≠ .rgn r := by
  have hns : ∀ t, cx.peek a = .ok t → ∀ r u, cellOf t ≠ some (.rgn r, u) := by
    rcases hsc with h | h
    · exact h
    · exact h.elim
  have _ := hi
  cases hT with
  | let_ hop he =>
  cases hop with
  | storeWordGive hp hw =>
    obtain ⟨μ, hc⟩ := cellOf_of_wordOf hw
    exact ⟨_, μ, _, hp, hc, by simp [Cx.opaqueOK, Ty.guardT], fun r e => hns _ hp r _ (e ▸ hc)⟩
  | storeWordKeep hp hw =>
    obtain ⟨μ, hc⟩ := cellOf_of_wordOf hw
    exact ⟨_, μ, _, hp, hc, by simp [Cx.opaqueOK, Ty.guardT], fun r e => hns _ hp r _ (e ▸ hc)⟩
  | storeWordHand hp hw =>
    obtain ⟨μ, hc⟩ := cellOf_of_wordOf hw
    exact ⟨_, μ, _, hp, hc, by simp [Cx.opaqueOK, Ty.guardT], fun r e => hns _ hp r _ (e ▸ hc)⟩
  | storeOwn hp _ hc _ hu hsub =>
    exact ⟨_, _, _, hp, hc, sub_opaqueOK hsub
      (peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu).1), fun r e => by cases e⟩
  | storePub hp _ hc _ hu hsub =>
    exact ⟨_, _, _, hp, hc, sub_opaqueOK hsub
      (peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu).1), fun r e => by cases e⟩
  | storeRgn hp _ hc => exact (hns _ hp _ _ hc).elim
  | storeCap hp _ hc => exact (hns _ hp _ _ hc).elim

/-- A unit of an `IniAt` target lies in an initialised slot. -/
theorem slot_lt {ini : AllocLabel → Nat} {cl : Cell} {ad : Address} {U : Ty} {us : List Acc} {j : Nat}
    (hini : IniAt ini cl ad U) (hus : accs U = some us) (hj : j < nWords us) :
    ∀ N e us', cl.ty = .array (.lit N) e → accs e = some us' → ad.offset + j < ini ad.label * nWords us' := by
  intro N e us' hty he
  rcases hini N e hty with ⟨hU, -⟩ | ⟨us0, j0, o, h0, hj0, ho, hat⟩
  · rw [hU, hty] at hus; simp [accs] at hus
  · rw [he] at h0; cases h0
    have hb := AtOff_bound hat he hus
    have h2 : (j0 + 1) * nWords us' ≤ ini ad.label * nWords us' := Nat.mul_le_mul_right _ hj0
    rw [Nat.succ_mul] at h2
    show @LT.lt Nat _ (ad.offset + j) (ini ad.label * nWords us')
    omega

/-! ## Hiding from the invariant's clauses -/

/-- Placeholders hidden below a frontier `f ≤ V` (`HiddenP`), with a message at `b` below `V`, where no
`undef` word is typed: `HidBy` at `V`. -/
theorem hid_of_hidden {E : TEnv} {T : Ty} {mem : Memory} {P : List Ts} {b : Address} {V f : Nat}
    (hnw : ∀ w : Word, w.val = .undef → ¬ WordOK E T b.offset w)
    (hh : HiddenP E T mem P b.label b.offset f) (hfV : f ≤ V)
    (hnp : ∀ (t : Nat) (m : Msg), t ∈ P → mem[t]? = some m → m.val ≠ .undef)
    (hU : ∃ (t : Nat) (m : Msg), t ≤ V ∧ mem[t]? = some m ∧ m.loc = b) : HidBy mem b V := by
  refine ⟨hU, ?_⟩
  intro t0 m0 hm hl hu
  have hnp0 : t0 ∉ P := fun ht => hnp t0 m0 ht hm hu
  have hl' : m0.loc = ⟨b.label, b.offset⟩ := by rw [hl]
  obtain ⟨t', m', h1, h3, h4, h5⟩ := hh t0 m0 hnp0 hm hl' (hnw (mw m0) hu)
  exact ⟨t', m', h1, Nat.le_trans h3 hfV, h4, by rw [h5]⟩

/-- Placeholders hidden below `f ≤ V`, with an `undef` message at `b` (not a promise, not typed):
a message at `b` at or below `V`. -/
theorem msg_of_undef {E : TEnv} {T : Ty} {mem : Memory} {P : List Ts} {b : Address} {V f : Nat}
    (hnw : ∀ w : Word, w.val = .undef → ¬ WordOK E T b.offset w)
    (hh : HiddenP E T mem P b.label b.offset f) (hfV : f ≤ V)
    (hnp : ∀ (t : Nat) (m : Msg), t ∈ P → mem[t]? = some m → m.val ≠ .undef)
    (hu : ∃ (t : Nat) (m : Msg), mem[t]? = some m ∧ m.loc = b ∧ m.val = .undef) :
    ∃ (t : Nat) (m : Msg), t ≤ V ∧ mem[t]? = some m ∧ m.loc = b := by
  obtain ⟨t0, m0, hm, hl, hu⟩ := hu
  have hl' : m0.loc = ⟨b.label, b.offset⟩ := by rw [hl]
  obtain ⟨t', m', -, h3, h4, h5⟩ := hh t0 m0 (fun ht => hnp t0 m0 ht hm hu) hm hl' (hnw (mw m0) hu)
  exact ⟨t', m', Nat.le_trans h3 hfV, h4, by rw [h5]⟩

/-- An own unit at its latest word (`LatestSF`), not `undef`, coherence at most `V`, where no `undef`
word is typed: `HidBy` at `V`. -/
theorem hid_of_latest {E : TEnv} {cl : Cell} {fr : Option Ts} {mem : Memory} {P : List Ts} {coh : Address → Ts}
    {b : Address} {w : Word} {V : Nat}
    (hnw : ∀ w : Word, w.val = .undef → ¬ WordOK E cl.ty b.offset w)
    (hl : LatestSF E cl fr mem (· ∈ P) coh b w) (hw : w.val ≠ .undef) (hcV : coh b ≤ V)
    (hnp : ∀ (t : Nat) (m : Msg), t ∈ P → mem[t]? = some m → m.val ≠ .undef) : HidBy mem b V := by
  obtain ⟨⟨mc, hmc, hml, hv⟩, -, hafter⟩ := hl
  have h2 : ∀ (t0 : Nat) (m0 : Msg), mem[t0]? = some m0 → m0.loc = b → m0.val = .undef →
      ∃ (t' : Nat) (m' : Msg), t0 < t' ∧ t' ≤ V ∧ mem[t']? = some m' ∧ m'.loc = b := by
    intro t0 m0 hm hloc hu
    rcases Nat.lt_trichotomy t0 (coh b) with hlt | heq | hgt
    · exact ⟨coh b, mc, hlt, hcV, hmc, hml⟩
    · subst heq
      rw [hm] at hmc; cases hmc
      rcases hv with ⟨hv1, -⟩ | ⟨-, hty⟩
      · exact absurd (hv1.symm.trans hu) hw
      · unfold TypedAt at hty; rw [hloc] at hty
        exact absurd hty (hnw _ hu)
    · rcases hafter t0 m0 hgt hm hloc with hp | ⟨-, hty⟩
      · exact absurd hu (hnp t0 m0 hp hm)
      · unfold TypedAt at hty; rw [hloc] at hty
        exact absurd hty (hnw (mw m0) hu)
  exact ⟨⟨coh b, mc, hcV, hmc, hml⟩, h2⟩

/-! ## `SeenHid` -/

/-- **`SeenHid` at every reachable store**, from the stepper's `MemInv` at its cut (`ThSys.env`),
`PromNotUndef`, scope, `EnvVR` and `UndefAt`.  `E'` is any environment with the cut's cells,
frontiers, counts and thread.

(H) At a designated start of a predicted unit (`PredU ∧ DStart`): the cell is own (`DStart`), the
slot is at or past the real count (`¬ IniWr`), so the reference is `pub` (`modeIni`) and
`OwnHidP.2` hides the unit's placeholders below the frontier `f ≤ pw.view`; the unit lies in the
buffer (`off_lt_buf`), so `LatestSF` gives its message at `coh`; no `undef` word of the buffer is
typed (`undef_not_wordOK_buf`: its element units are all `.one`). -/
theorem seenHid_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r)
    (hsc : ∀ {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res},
      EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs → StepScope cx th.term ∨ StepScopeR th.σs cx th.term)
    (hvr : EnvVR th) {E' : TEnv}
    (hE' : E'.sto = cutSto Eg i ∧ E'.pfr = Eg.pfr ∧ E'.ini = Eg.ini ∧ E'.rini = Eg.rini ∧ E'.tid = i)
    (hall : UndefAt E' c.mem) :
    SeenHid k arch E' c.mem th := by
  intro x rel a v tok e hterm rt pw ad μ ru us j hev had hc hus hj hguard
  obtain ⟨S, ρ, η, cx, Rf, Rs, hCE, htid, hE, hT, htv, hFI, hsum, -, hm, -, -⟩ :=
    (X.inv.thr i th X.hth).env X.inv.clo
  have hsto : (CE η).sto = cutSto Eg i := by rw [hCE]; rfl
  have hsto' : ∀ l, E'.sto l = η.sto l := fun l => by
    show E'.sto l = (CE η).sto l
    rw [hsto, hE'.1]
  have hrc' : ∀ l, E'.rc l = (CE η).rc l := fun l => by
    have e1 : (CE η).ini = Eg.ini := by rw [hCE]; rfl
    have e2 : (CE η).rini = Eg.rini := by rw [hCE]; rfl
    simp only [TEnv.rc, hE'.2.2.1, hE'.2.2.2.1, e1, e2]
  have hs := hsc ⟨hCE, htid, hE, hT, htv, hFI, hsum⟩
  rw [hterm] at hs hT
  obtain ⟨t, μs, u, hpk, hcu, ho, hnr⟩ := store_target hT.1 hFI htv hs
  have hi0 := hFI.1
  obtain ⟨rt', ws, hea, hvr', -⟩ := peek_VR hi0.2.1 hpk
  have hea' := hea
  rw [hev] at hea'
  simp only [Option.some.injEq, Prod.mk.injEq] at hea'
  obtain ⟨rfl, rfl⟩ := hea'
  have hacc : accs ru = accs (cl ρ η.wit 0 0 u) :=
    pub_accs hi0.2.2.2.1 hi0.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi0.2.1 htv hpk hcu ho hev hc
  have husU : accs (cl ρ η.wit 0 0 u) = some us := hacc ▸ hus
  have hnb : ∀ n e, ¬ Fd (.array (.lit n) e) (cl ρ η.wit 0 0 u) := fun n e hF => by
    have h := Fd_accs hF
    rw [husU] at h; simp [accs] at h
  obtain ⟨ad', cl0, hws, hcl, hatU, hmode, hini⟩ := cell_target hcu hnb hvr'
  have hpw : pw.val = .loc ad' 0 := by simpa using hws
  have had' : ad' = ad := by simp only [addrOf, hpw, Option.some.injEq] at had; exact had
  rw [had'] at hcl hatU hmode hini
  have hcohV : th.vs.coh (offs ad j) ≤ Bnd k arch pw th.vs (offs ad j) :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hfV : ∀ f, f ≤ pw.view → f ≤ Bnd k arch pw th.vs (offs ad j) := by
    intro f hf
    have hd : f ≤ dep k pw := by
      have hvr0 := hvr a rt [pw] pw hev (List.mem_singleton_self _)
      unfold dep; split
      · exact Nat.le_trans hf hvr0
      · exact hf
    exact Nat.le_trans hd (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
  have hnp : ∀ (t : Nat) (m : Msg), t ∈ (stOf c.mem c.pairs th).promises → c.mem[t]? = some m →
      m.val ≠ .undef :=
    fun t m ht hm => X.inv.promNU i th t m X.hth ht hm
  obtain ⟨-, hOwn, -, -, -, hHid, hPub, -, hPI, -, -⟩ := hm
  rcases hguard with ⟨n, P, hW⟩ | ⟨hPU, hDS⟩
  · -- a protocol-word unit
    have hU := hall _ n P hW
    obtain ⟨cW, hcW, hatW, hgW⟩ := hW
    have hcW0 : η.sto ad.label = some cW := (hsto' _).symm.trans hcW
    have hcc : cW = cl0 := by rw [hcl] at hcW0; exact (Option.some.inj hcW0).symm
    rw [hcc] at hatW
    have hnw : ∀ w : Word, w.val = .undef → ¬ WordOK (CE η) cl0.ty (offs ad j).offset w :=
      fun w hw => undef_not_wordOK hatW hgW hw
    by_cases hown : cl0.owner = some η.tid
    · by_cases hrc : ∀ N e us', cl0.ty = .array (.lit N) e → accs e = some us' →
          ad.offset + j < (CE η).rc ad.label * nWords us'
      · obtain ⟨vals, hcell, hlat, -⟩ := hOwn ad.label cl0 hcl hown
        obtain ⟨w, hw, hwu⟩ := own_val hcell hatW hgW hrc
        exact hid_of_latest hnw (hlat _ w hw) hwu hcohV hnp
      · obtain ⟨N, e, us', hty, he, hge⟩ : ∃ N e us', cl0.ty = .array (.lit N) e ∧ accs e = some us' ∧
            ¬ (ad.offset + j < (CE η).rc ad.label * nWords us') :=
          Classical.byContradiction fun hx => hrc fun N e us' h1 h2 =>
            Classical.byContradiction fun h3 => hx ⟨N, e, us', h1, h2, h3⟩
        cases μs with
        | own => exact absurd (slot_lt hini husU hj N e us' hty he) hge
        | rgn r0 => exact absurd rfl (hnr r0)
        | pub =>
          have hI := slot_lt hini husU hj
          have hlt : (CE η).rc ad.label < (CE η).ini ad.label := by
            refine Nat.lt_of_not_le fun hle => hge ?_
            exact Nat.lt_of_lt_of_le (hI N e us' hty he) (Nat.mul_le_mul_right _ hle)
          obtain ⟨f, hf, hns, hh⟩ := hHid.2 ad.label cl0 hcl hown hlt
          obtain ⟨f', hf', hsv⟩ := hmode
          have hff : f' = f := Option.some.inj (hf'.symm.trans hf)
          rcases hsv with hsn | hv
          · exact absurd hsn (hns (ZW.not_of_initR hcl hI))
          · have hfB := hfV f (hff ▸ hv pw (List.mem_singleton_self _))
            exact hid_of_hidden hnw (hh _ hI) hfB hnp (msg_of_undef hnw (hh _ hI) hfB hnp hU)
    · cases μs with
      | own => exact absurd hmode hown
      | rgn r0 => exact absurd rfl (hnr r0)
      | pub =>
        obtain ⟨f, hf, hsv⟩ := hmode
        rcases hsv with hsn | hv
        · rcases hPI.1 ad.label hsn with ⟨c2, h2, h3⟩ | ⟨h2, -⟩
          · have h2' : η.sto ad.label = some c2 := h2
            rw [hcl] at h2'; cases h2'; exact absurd h3 hown
          · have h2' : η.sto ad.label = none := h2
            rw [hcl] at h2'; cases h2'
        · have hfB := hfV f (hv pw (List.mem_singleton_self _))
          exact hid_of_hidden hnw (hPub ad.label cl0 f hcl hown hf _ (slot_lt hini husU hj)) hfB hnp
            (msg_of_undef hnw (hPub ad.label cl0 f hcl hown hf _ (slot_lt hini husU hj)) hfB hnp hU)
  · -- (H) a designated start of a predicted unit: an own all-`.one` buffer, past the real count
    obtain ⟨⟨c1, hc1, hown1⟩, hds⟩ := hDS
    have hcc : c1 = cl0 := Option.some.inj (((hsto' _).symm.trans hc1).symm.trans hcl)
    rw [hcc] at hown1
    have hown : cl0.owner = some η.tid := by rw [hown1, hE'.2.2.2.2, htid]; rfl
    obtain ⟨N, e, us', hty, he, h1⟩ : ∃ N e us', cl0.ty = .array (.lit N) e ∧ accs e = some us' ∧
        ∀ u ∈ us', u = .one := by
      rcases hds with ⟨U, c2, N, e, us', j', o', w', h2, h3, h4, h5, -⟩ | ⟨c2, N, e, us', h2, h3, h4, -, h5, -⟩
      · have hc2 : c2 = cl0 := Option.some.inj (((hsto' _).symm.trans h2).symm.trans hcl)
        rw [hc2] at h3
        exact ⟨N, e, us', h3, h4, h5⟩
      · have hc2 : c2 = cl0 := Option.some.inj (((hsto' _).symm.trans h2).symm.trans hcl)
        rw [hc2] at h3
        exact ⟨N, e, us', h3, h4, h5⟩
    have hge : ¬ (ad.offset + j < (CE η).rc ad.label * nWords us') := by
      intro hlt
      apply hPU.2.2
      intro c2 N2 e2 us2 h2 h3 h4
      have hc2 : c2 = cl0 := Option.some.inj (((hsto' _).symm.trans h2).symm.trans hcl)
      rw [hc2, hty] at h3
      simp only [Ty.array.injEq, Idx.lit.injEq] at h3
      obtain ⟨-, he2⟩ := h3
      rw [← he2, he] at h4
      cases h4
      rw [hrc']
      exact hlt
    have hnw : ∀ w : Word, w.val = .undef → ¬ WordOK (CE η) cl0.ty (offs ad j).offset w :=
      fun w hw => undef_not_wordOK_buf hty he h1 hw
    have hU : ∃ (t : Nat) (m : Msg), t ≤ Bnd k arch pw th.vs (offs ad j) ∧ c.mem[t]? = some m ∧
        m.loc = offs ad j := by
      obtain ⟨vals, hcell, hlat, -⟩ := hOwn ad.label cl0 hcl hown
      have hlt := off_lt_buf hatU hty he husU hj
      have hlen : vals.length = N * nWords us' := by
        rcases hcell with ⟨hwc, -⟩ | ⟨N2, e2, us2, hty2, hus2, -, hlen, -⟩
        · rw [hty] at hwc; simp [wc, accs] at hwc
        · rw [hty] at hty2
          simp only [Ty.array.injEq, Idx.lit.injEq] at hty2
          obtain ⟨hN2, he2⟩ := hty2
          rw [← he2, he] at hus2
          cases hus2
          rw [hlen, hN2]
      have hlt' : ad.offset + j < vals.length := by rw [hlen]; exact hlt
      obtain ⟨⟨mc, hmc, hml, -⟩, -, -⟩ := hlat _ _ (List.getElem?_eq_getElem hlt')
      exact ⟨_, mc, hcohV, hmc, hml⟩
    cases μs with
    | own => exact absurd (slot_lt hini husU hj N e us' hty he) hge
    | rgn r0 => exact absurd rfl (hnr r0)
    | pub =>
      have hI := slot_lt hini husU hj
      have hlt : (CE η).rc ad.label < (CE η).ini ad.label := by
        refine Nat.lt_of_not_le fun hle => hge ?_
        exact Nat.lt_of_lt_of_le (hI N e us' hty he) (Nat.mul_le_mul_right _ hle)
      obtain ⟨f, hf, hns, hh⟩ := hHid.2 ad.label cl0 hcl hown hlt
      obtain ⟨f', hf', hsv⟩ := hmode
      have hff : f' = f := Option.some.inj (hf'.symm.trans hf)
      rcases hsv with hsn | hv
      · exact absurd hsn (hns (ZW.not_of_initR hcl hI))
      · have hfB := hfV f (hff ▸ hv pw (List.mem_singleton_self _))
        exact hid_of_hidden hnw (hh _ hI) hfB hnp hU

#print axioms undef_not_wordOK
#print axioms oneAt_all_one
#print axioms undef_not_wordOK_buf
#print axioms off_lt_buf
#print axioms valOf_nundef
#print axioms own_val
#print axioms store_target
#print axioms slot_lt
#print axioms hid_of_hidden
#print axioms msg_of_undef
#print axioms hid_of_latest
#print axioms seenHid_of

end TermSeenHid
