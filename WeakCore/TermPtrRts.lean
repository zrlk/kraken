import WeakCore.TermPtrRtsDefs
import WeakCore.TermTyped
import WeakCore.TermOwnG0Defs
import WeakCore.TermOwnG0
import WeakCore.TermStoreNI
import WeakCore.TermMainDefs
import WeakCore.TermCut
import WeakCore.TermScope

/-!
# TermPtrRts: the pointer-rts invariant `(M)+(R)` and the no-fulfil lemmas

The definitions read by `SysInvN` are in `TermPtrRtsDefs`.
-/

namespace TermPtrRts
open CoreLang CoreTerm CoreTyping TermRun TermTv TermSound TermMem TermStep TermCert TermGlob TermTyped
open TermOwnG0Defs TermCut
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- `PlantEdge` grows with the store typing. -/
theorem PlantEdge_mono {sto sto2 : Sto} {m : Msg} {a : AllocLabel}
    (hs : ∀ l c, sto l = some c → sto2 l = some c) (h : PlantEdge sto m a) : PlantEdge sto2 m a := by
  obtain ⟨⟨ca, h1, h2, h3⟩, h4⟩ := h
  exact ⟨⟨ca, hs _ _ h1, h2, h3⟩, h4⟩

/-- A cut's store typing is part of the global one. -/
theorem cut_sto_le (Eg : GEnv) (j : Nat) (S : AllocLabel → Prop) :
    ∀ l c, (Cut Eg j S).sto l = some c → Eg.sto l = some c :=
  fun _ _ h => (cutSto_some.1 h).1

/-- **The bridge** ((1)): the global clause gives the owner's form at `Eg.sto`. -/
theorem ptrRtsE_of_G {Eg : GEnv} {Tot HP : Nat → Res} {c : Cfg} {j : Nat} {th : TTh} {a : AllocLabel}
    {cl : Cell} {f : Ts}
    (hG : PtrRtsG Eg Tot HP c) (hth : c.ths[j]? = some th) (hsto : Eg.sto a = some cl)
    (hown : cl.owner = some j) (hpf : Eg.pfr a = some f) (hkey : 0 < (Tot j + HP j) (.own a)) :
    PtrRtsE Eg.sto (stOf c.mem c.pairs th) th a := by
  intro t ht
  rw [← tminG_eq hth] at ht
  obtain ⟨hM, hR⟩ := hG j th a cl f hth hsto hown hpf hkey t ht
  exact ⟨hM, hR⟩

/-! ## K-5: the window, re-rooted -/

section win
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {j : Nat} {a : AllocLabel}

/-- **K-5** (`winLe_cert` re-rooted at an arbitrary `c1`, same proof): along a run to no promises,
from a configuration reached by `SoloNP a` from `c1` with `t` (message `m`) outstanding, the
thread meets a `publish a` with `t` outstanding first, so `vWr ≤ m.view`. -/
theorem winLe_gen {c1 : Cfg} {t : Nat} {m : Msg}
    (hNo : ∀ c th, SoloNP p k arch j a c1 c → Certified p k arch c j → c.ths[j]? = some th → t ∈ th.promises)
    (hmB : ∀ c, SoloNP p k arch j a c1 c → c.mem[t]? = some m)
    {c c2 : Cfg} (h : Solo p k arch j c c2) :
    noPromises c2 j = true → SoloNP p k arch j a c1 c → ∀ th, c.ths[j]? = some th →
      t ∈ th.promises → th.vs.vWr ≤ m.view := by
  induction h with
  | refl c =>
    intro hn _ th hth hB
    simp only [noPromises, hth, Option.map_some, Option.getD_some, List.isEmpty_iff] at hn
    rw [hn] at hB; cases hB
  | thread hs hrest ih =>
    rename_i c c3 c4
    intro hn hP th hth hB
    have hc1 : Certified p k arch c3 j := ⟨_, hrest, hn⟩
    by_cases hpub : PubAt th a
    · obtain ⟨y, a2, e, -, -, -, hterm, -⟩ := hpub
      exact certified_pub_vWrLe hs hc1 hth hterm hB (hmB c hP)
    · have hP1 := TermOwnG0.soloNP_snoc_thread hP c3 hs (fun th2 h2 => by rw [hth] at h2; cases h2; exact hpub)
      obtain ⟨th0, th1, h0, h1, hv, -⟩ := winInv_thread (winInv_refl hth) hs
      rw [hth] at h0; cases h0
      exact Nat.le_trans hv (ih hn hP1 th1 h1 (hNo c3 th1 hP1 hc1 h1))
  | prom a3 v w3 hw hrest ih =>
    rename_i c c4
    intro hn hP th hth hB
    have hP1 := TermOwnG0.soloNP_snoc_prom hP a3 v w3 hw
    have h2 := ih hn hP1 _ (promise_inv (a := a3) (v := v) (w := w3) hth).2.1 (List.mem_append_left _ hB)
    exact h2
  | ext hs hrest ih =>
    rename_i c c3 c4
    intro hn hP th hth hB
    have hP1 := TermOwnG0.soloNP_snoc_ext hP c3 hs
    obtain ⟨x1, a1, e1, evs, hterm, rfl⟩ := extSteps_thread hs hth
    exact ih hn hP1 { th with term := e1, env := (x1, .unit, []) :: th.env } (set_self hth) hB

end win

/-! ## K-2 / K-3 / K-4 statements (named, for consumers; proofs follow)

`sto` is any store typing extending the thread's (`E.sto`); consumers take `Eg.sto`. -/

/-- The K-2a statement (the `PtrRtsThreadP`, verbatim up to namespace): an owner thread step, not
a `publish a`, keeps `(M)+(R)` and `tmin`, edges read against `sto` before and `sto'` after. -/
def PtrRtsThreadP (p : Prog) : Prop :=
  ∀ (g : G) (E E' : TEnv) (sto sto' : Sto) (mem : Memory) (pairs : List Ts) (th : TTh)
    (a : AllocLabel) (r : Memory × List Ts × TTh),
    g.k.storeDepRts = true →
    (∀ l c, E.sto l = some c → sto l = some c) → (∀ l c, E'.sto l = some c → sto' l = some c) →
    (∀ l c, sto l = some c → sto' l = some c) →
    (∀ l c, sto' l = some c → sto l = none → E.sto l = none ∧ E'.sto l = some c) →
    ThInvE p E th → MemInv g E (stOf mem pairs th) →
    PtrRtsE sto (stOf mem pairs th) th a → ¬ PubAt th a →
    r ∈ tstep g mem pairs th → Foot g E E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) →
    ThInvE p E' r.2.2 → PromAbove (stOf r.1 r.2.1 r.2.2) →
    PtrRtsE sto' (stOf r.1 r.2.1 r.2.2) r.2.2 a ∧
      ∀ t, tminOf sto (stOf mem pairs th) a = some t →
        tminOf sto' (stOf r.1 r.2.1 r.2.2) a = some t

/-- `EnvLbl` for a thread's frame and stack environments (`LblSto` at one thread). -/
def ThLbl (Eg : GEnv) (th : TTh) : Prop := EnvLbl Eg th.env ∧ ∀ f ∈ th.stack, EnvLbl Eg f.env

/-- (B′) `GranuleW` with clause 2 restricted to messages outside `P` (the owner's
outstanding promises): the Solo/`PtrRtsThreadGL` form of granW. -/
def GranuleWP (sto : Sto) (mem : Memory) (pairs : List Ts) (P : List Ts) : Prop :=
  (∀ q ∈ pairs, ∃ m0 m1, mem[q]? = some m0 ∧ mem[q + 1]? = some m1 ∧ m1.loc = m0.loc.next) ∧
  (∀ q ∈ pairs, ∀ (v : Nat) (m0 mv : Msg), mem[q]? = some m0 → mem[v]? = some mv → mv.loc = m0.loc → q < v →
    v ∉ P → v ∈ pairs) ∧
  (∀ q ∈ pairs, ∀ (m0 : Msg) (cl : Cell), mem[q]? = some m0 → sto m0.loc.label = some cl →
    TwoAtT cl.ty m0.loc.offset) ∧
  (∀ (v : Nat) (mv : Msg) (cl : Cell) (o : Nat), mem[v]? = some mv → v ∉ P → sto mv.loc.label = some cl →
    mv.loc.offset = o + 1 → TwoAtT cl.ty o → (∀ a g, mv.val ≠ .loc a g) ∨ ∃ q ∈ pairs, v = q + 1)

/-- **PtrRtsThreadGL**: `PtrRtsThreadP` over the staging package, `ThLbl` both as
hypothesis (at `Eg`) and as conclusion (at `Eg'`).  `E`'s frontiers and boxes lie in `Eg`'s, `E'`'s in
`Eg'`'s, and `Eg`'s grow into `Eg'`'s.  `ptrRtsThreadGL_proj` recovers the old conclusion.
(`hNF`) An outstanding promise of the result does not lie at a label new to `sto'`
(supplied as `PromAllocF`'s location half, `tminG_thread`'s `hfr`).  ((a′)) `MemRtsC`, the
counted-slot (M), as hypothesis and conclusion; the scope and `drf` facts of the stepper
(`ScopeOK`, `ThScope`, `ProgScopeOK`; RGN-NAMES-OWN drf route).  `GranuleWP` (granW, B′,
restated) at `sto`, as hypothesis and conclusion.  The step's fresh labels are
outside `sto` (`hfr`), every cell of `sto` is laid out (`hLay`), and a pair store at a label new to
`sto'` starts a two-word unit there (`hNC`), and a non-promise message at the second word of a two-word
unit there holds no pointer or is a pair store's second half (`hNC4`; both from `FootNC`).
(v3d, /) The program (`g.p = p`, `ProgT p`); the step's fresh labels are not `a`; `a` is
no box of `E`; the stepper export `FootBP` (fresh labels named by a new binding are boxes of `E'`, or the
binding is old; a published label has a frontier in `E'`); the `ret` frame link (staging, sig form,
until RetPw); and `BoxSep` at the old `tmin` (the `boxPlantSep` field's per-thread projection). -/
def PtrRtsThreadGL (p : Prog) : Prop :=
  ∀ (g : G) (E E' : TEnv) (Eg Eg' : GEnv) (sto sto' : Sto) (mem : Memory) (pairs : List Ts) (th : TTh)
    (a : AllocLabel) (r : Memory × List Ts × TTh),
    g.k.storeDepRts = true →
    (∀ l c, E.sto l = some c → sto l = some c) → (∀ l c, E'.sto l = some c → sto' l = some c) →
    (∀ l c, sto l = some c → sto' l = some c) →
    (∀ l c, sto' l = some c → sto l = none → E.sto l = none ∧ E'.sto l = some c) →
    (∀ l f, E.pfr l = some f → Eg.pfr l ≠ none) → (∀ l B, E.box l = some B → Eg.box l ≠ none) →
    (∀ l f, E'.pfr l = some f → Eg'.pfr l ≠ none) → (∀ l B, E'.box l = some B → Eg'.box l ≠ none) →
    (∀ l f, Eg.pfr l = some f → Eg'.pfr l = some f) → (∀ l B, Eg.box l = some B → Eg'.box l = some B) →
    ThInvE p E th → MemInv g E (stOf mem pairs th) →
    PtrRtsE sto (stOf mem pairs th) th a → ¬ PubAt th a →
    r ∈ tstep g mem pairs th → Foot g E E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) →
    ThInvE p E' r.2.2 → PromAbove (stOf r.1 r.2.1 r.2.2) →
    (∀ u ∈ r.2.2.promises, ∀ m, r.1[u]? = some m → sto m.loc.label = none → sto' m.loc.label = none) →
    ThLbl Eg th →
    TermTyped.ScopeOK p th → TermScope.ThScope th → TermScope.ProgScopeOK g.p = true →
    (∀ t, tminOf sto (stOf mem pairs th) a = some t → MemRtsC sto t a mem pairs th.promises) →
    GranuleWP sto mem pairs th.promises →
    (∀ l, FreshIn g th.nalloc r.2.2.nalloc l → sto l = none) → (∀ l c, sto l = some c → LayT c.ty) →
    (∀ q ∈ r.2.1, ∀ (m0 : Msg) (cl : Cell), r.1[q]? = some m0 → sto' m0.loc.label = some cl →
      sto m0.loc.label = none → TwoAtT cl.ty m0.loc.offset) →
    (∀ (v : Nat) (mv : Msg) (cl : Cell) (o : Nat), r.1[v]? = some mv → v ∉ r.2.2.promises →
      sto' mv.loc.label = some cl → sto mv.loc.label = none → mv.loc.offset = o + 1 → TwoAtT cl.ty o →
      (∀ a g, mv.val ≠ .loc a g) ∨ ∃ q ∈ r.2.1, v = q + 1) →
    g.p = p → ProgT p → (∀ l, FreshIn g th.nalloc r.2.2.nalloc l → l ≠ a) → E.box a = none →
    (∀ l, FreshIn g th.nalloc r.2.2.nalloc l → ∀ b ∈ r.2.2.env, ∀ w ∈ pubWords b.2.1 b.2.2, Names l w →
      E'.box l ≠ none ∨ b ∈ th.env) →
    (∀ l, PubAt th l → E'.pfr l ≠ none) →
    (∀ a0, th.term = .ret a0 → ∃ ρ η cx, CE η = E ∧ EnvOK p η ∧ Typed p cx th.term ∧ TvOK cx ∧
      FInv ρ η th.σs (Resume p th.stack) cx th.env ∧
      ∀ (f : Frame) (rest : List Frame), th.stack = f :: rest → ∀ ws, pubWords f.ty ws = pubWords (close th.σs cx.ret) ws) →
    (∀ t, tminOf sto (stOf mem pairs th) a = some t → BoxSep E t a mem) →
    (PtrRtsE sto' (stOf r.1 r.2.1 r.2.2) r.2.2 a ∧
      ∀ t, tminOf sto (stOf mem pairs th) a = some t →
        tminOf sto' (stOf r.1 r.2.1 r.2.2) a = some t) ∧ ThLbl Eg' r.2.2 ∧
      (∀ t, tminOf sto' (stOf r.1 r.2.1 r.2.2) a = some t → MemRtsC sto' t a r.1 r.2.1 r.2.2.promises) ∧
      GranuleWP sto' r.1 r.2.1 r.2.2.promises

/-- The projection of `PtrRtsThreadGL` to the `PtrRtsThreadP` conclusion (extra hypotheses:
the `Eg`/`Eg'` frontier and box inclusions, `hNF`, `ThLbl Eg th`, scope/`drf`, `MemRtsC`, `GranuleWP`,
`hfrS`, `hLay`, `hNC`, `hNC4` and the v3d binders). -/
theorem ptrRtsThreadGL_proj {p : Prog} (h : PtrRtsThreadGL p) (g : G) (E E' : TEnv) (Eg Eg' : GEnv)
    (sto sto' : Sto) (mem : Memory) (pairs : List Ts) (th : TTh) (a : AllocLabel) (r : Memory × List Ts × TTh)
    (hk : g.k.storeDepRts = true) (h1 : ∀ l c, E.sto l = some c → sto l = some c)
    (h2 : ∀ l c, E'.sto l = some c → sto' l = some c) (h3 : ∀ l c, sto l = some c → sto' l = some c)
    (h4 : ∀ l c, sto' l = some c → sto l = none → E.sto l = none ∧ E'.sto l = some c)
    (p1 : ∀ l f, E.pfr l = some f → Eg.pfr l ≠ none) (p2 : ∀ l B, E.box l = some B → Eg.box l ≠ none)
    (p3 : ∀ l f, E'.pfr l = some f → Eg'.pfr l ≠ none) (p4 : ∀ l B, E'.box l = some B → Eg'.box l ≠ none)
    (p5 : ∀ l f, Eg.pfr l = some f → Eg'.pfr l = some f) (p6 : ∀ l B, Eg.box l = some B → Eg'.box l = some B)
    (hI : ThInvE p E th) (hM : MemInv g E (stOf mem pairs th)) (hP : PtrRtsE sto (stOf mem pairs th) th a)
    (hnp : ¬ PubAt th a) (hr : r ∈ tstep g mem pairs th) (hF : Foot g E E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2))
    (hI' : ThInvE p E' r.2.2) (hA : PromAbove (stOf r.1 r.2.1 r.2.2))
    (hNF : ∀ u ∈ r.2.2.promises, ∀ m, r.1[u]? = some m → sto m.loc.label = none → sto' m.loc.label = none)
    (hL : ThLbl Eg th) (hsc : TermTyped.ScopeOK p th) (hdrf : TermScope.ThScope th)
    (hps : TermScope.ProgScopeOK g.p = true)
    (hC : ∀ t, tminOf sto (stOf mem pairs th) a = some t → MemRtsC sto t a mem pairs th.promises)
    (hgw : GranuleWP sto mem pairs th.promises) (hfrS : ∀ l, FreshIn g th.nalloc r.2.2.nalloc l → sto l = none)
    (hLay : ∀ l c, sto l = some c → LayT c.ty)
    (hNC : ∀ q ∈ r.2.1, ∀ (m0 : Msg) (cl : Cell), r.1[q]? = some m0 → sto' m0.loc.label = some cl →
      sto m0.loc.label = none → TwoAtT cl.ty m0.loc.offset)
    (hNC4 : ∀ (v : Nat) (mv : Msg) (cl : Cell) (o : Nat), r.1[v]? = some mv → v ∉ r.2.2.promises →
      sto' mv.loc.label = some cl → sto mv.loc.label = none → mv.loc.offset = o + 1 → TwoAtT cl.ty o →
      (∀ a g, mv.val ≠ .loc a g) ∨ ∃ q ∈ r.2.1, v = q + 1)
    (hp : g.p = p) (hPT : ProgT p) (hfa : ∀ l, FreshIn g th.nalloc r.2.2.nalloc l → l ≠ a) (hBN : E.box a = none)
    (hB1 : ∀ l, FreshIn g th.nalloc r.2.2.nalloc l → ∀ b ∈ r.2.2.env, ∀ w ∈ pubWords b.2.1 b.2.2, Names l w →
      E'.box l ≠ none ∨ b ∈ th.env)
    (hB2 : ∀ l, PubAt th l → E'.pfr l ≠ none)
    (hRL : ∀ a0, th.term = .ret a0 → ∃ ρ η cx, CE η = E ∧ EnvOK p η ∧ Typed p cx th.term ∧ TvOK cx ∧
      FInv ρ η th.σs (Resume p th.stack) cx th.env ∧
      ∀ (f : Frame) (rest : List Frame), th.stack = f :: rest → ∀ ws, pubWords f.ty ws = pubWords (close th.σs cx.ret) ws)
    (hBS : ∀ t, tminOf sto (stOf mem pairs th) a = some t → BoxSep E t a mem) :
    PtrRtsE sto' (stOf r.1 r.2.1 r.2.2) r.2.2 a ∧
      ∀ t, tminOf sto (stOf mem pairs th) a = some t → tminOf sto' (stOf r.1 r.2.1 r.2.2) a = some t :=
  (h g E E' Eg Eg' sto sto' mem pairs th a r hk h1 h2 h3 h4 p1 p2 p3 p4 p5 p6 hI hM hP hnp hr hF hI' hA hNF hL hsc hdrf hps hC hgw hfrS hLay hNC hNC4
    hp hPT hfa hBN hB1 hB2 hRL hBS).1

/-- `LblSto` at a thread. -/
theorem thLbl_of_lblSto {Eg : GEnv} {c : Cfg} {i : Nat} {th : TTh} (h : LblSto Eg c) (hth : c.ths[i]? = some th) :
    ThLbl Eg th := h i th hth

/-- The K-3 statement: a thread step of the owner, not a `publish a`, keeps `tmin` outstanding. -/
def NoFulStep (p : Prog) : Prop :=
  ∀ (E : TEnv) (sto : Sto) (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) (a : AllocLabel) (t : Ts) r,
    g.k.storeDepRts = true → (∀ l c, E.sto l = some c → sto l = some c) →
    ThInvE p E th → MemInv g E (stOf mem pairs th) →
    PtrRtsE sto (stOf mem pairs th) th a → tminOf sto (stOf mem pairs th) a = some t →
    r ∈ tstep g mem pairs th → ¬ PubAt th a → t ∈ r.2.2.promises

/-- The K-4 statement: along `SoloNP j a` from a typed start carrying `PtrRtsE`, `tmin` stays
outstanding at every certified configuration. -/
def NoFulPlRun (p : Prog) (k : Promises.Knobs) (arch : Arch) : Prop :=
  ∀ (j : Nat) (a : AllocLabel) (c1 : Cfg) (th1 : TTh) (E1 : TEnv) (sto : Sto) (t : Ts),
    k.storeDepRts = true → (∀ l c, E1.sto l = some c → sto l = some c) →
    (∀ c0, Solo p k arch j c1 c0 → Certified p k arch c0 j → ScopeAt p j c0) →
    (∀ c0, Solo p k arch j c1 c0 → Certified p k arch c0 j → NoHoldPub p k arch j c0) →
    c1.ths[j]? = some th1 → ThInvE p E1 th1 → MemInv (gOf p k arch c1 j) E1 (stOf c1.mem c1.pairs th1) →
    PtrRtsE sto (stOf c1.mem c1.pairs th1) th1 a → tminOf sto (stOf c1.mem c1.pairs th1) a = some t →
    ∀ c2 th2, SoloNP p k arch j a c1 c2 → Certified p k arch c2 j → c2.ths[j]? = some th2 →
      t ∈ th2.promises



/-- Every label a word of `ws'` names is named by a word of `ws`. -/
def LblSub (ws' ws : List Word) : Prop := ∀ w ∈ ws', ∀ l, Names l w → ∃ w0 ∈ ws, Names l w0

theorem lblSub_refl (ws : List Word) : LblSub ws ws := fun w hw _ hn => ⟨w, hw, hn⟩

theorem lblSub_nil (ws : List Word) : LblSub [] ws := fun _ hw => by cases hw

theorem lblSub_trans {a b c : List Word} (h1 : LblSub a b) (h2 : LblSub b c) : LblSub a c := by
  intro w hw l hn
  obtain ⟨w1, hw1, hn1⟩ := h1 w hw l hn
  exact h2 w1 hw1 l hn1

theorem lblSub_of_sub {a b : List Word} (h : ∀ w ∈ a, w ∈ b) : LblSub a b := fun w hw _ hn => ⟨w, h w hw, hn⟩

theorem lblSub_append {a b c : List Word} (h1 : LblSub a c) (h2 : LblSub b c) : LblSub (a ++ b) c := by
  intro w hw
  rcases List.mem_append.1 hw with hw | hw
  · exact h1 w hw
  · exact h2 w hw

/-- A decoded arm payload names only labels of the encoded words. -/
theorem decodeArm_lblSub {tr : Tier} {as : List Ty} {ws p : List Word} {j : Nat}
    (h : decodeArm tr as ws = some (j, p)) : LblSub p ws := by
  unfold decodeArm at h
  split at h
  · rename_i w
    split at h
    · rename_i a g hv
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨_, _, h⟩ := h
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      intro w' hw' l hn
      simp only [List.mem_singleton] at hw'
      subst hw'
      obtain ⟨a', g', hv', hl⟩ := hn
      simp only at hv'
      cases hv'
      exact ⟨w, List.mem_singleton_self _, a, g, hv, hl⟩
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨arm, -, h⟩ := h
      split at h <;> simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
      · obtain ⟨-, rfl⟩ := h; exact lblSub_nil _
      · obtain ⟨-, rfl⟩ := h
        intro w' hw' l hn
        simp only [List.mem_singleton] at hw'
        subst hw'
        obtain ⟨a', g', hv', -⟩ := hn
        have e : (cst .null).val = WeakMem.Val.null := rfl
        rw [e] at hv'; cases hv'
    · cases h
  · rename_i t w
    split at h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨arm, -, h⟩ := h
      split at h <;> simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      · obtain ⟨-, rfl⟩ := h; exact lblSub_nil _
      · obtain ⟨-, rfl⟩ := h
        exact lblSub_of_sub (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; simp)
    · cases h
  · cases h

theorem lblSub_take (ws : List Word) (n : Nat) : LblSub (ws.take n) ws :=
  lblSub_of_sub (fun _ h => List.mem_of_mem_take h)

theorem lblSub_drop (ws : List Word) (n : Nat) : LblSub (ws.drop n) ws :=
  lblSub_of_sub (fun _ h => List.mem_of_mem_drop h)

/-- Counted words name only labels of the value's words (a niche sum's decoded payload re-encodes
the slot, keeping the label). -/
theorem pubWords_lblSub : ∀ (t : Ty),
    (∀ ws, LblSub (pubWords t ws) ws) ∧ (∀ j p, LblSub (pubArm t j p) p) := by
  intro t
  induction t with
  | prod a b iha ihb =>
      refine ⟨fun ws => ?_, fun j p => ?_⟩
      · rw [pubWords.eq_def]; simp only
        split
        · exact lblSub_refl _
        · split
          · exact lblSub_append (lblSub_trans ((iha).1 _) (lblSub_take _ _))
              (lblSub_trans ((ihb).1 _) (lblSub_drop _ _))
          · exact lblSub_nil _
      · rw [pubArm.eq_def]; simp only
        rw [pubWords.eq_def]; simp only
        split
        · exact lblSub_refl _
        · split
          · exact lblSub_append (lblSub_trans ((iha).1 _) (lblSub_take _ _))
              (lblSub_trans ((ihb).1 _) (lblSub_drop _ _))
          · exact lblSub_nil _
  | sum a b iha ihb =>
      refine ⟨fun ws => ?_, fun j p => ?_⟩
      · rw [pubWords.eq_def]; simp only
        split
        · exact lblSub_refl _
        · split
          · exact lblSub_refl _
          · split
            · rename_i j p hd
              split
              · exact lblSub_trans ((iha).2 _ _) (decodeArm_lblSub hd)
              · exact lblSub_trans ((ihb).2 _ _) (decodeArm_lblSub hd)
            · exact lblSub_nil _
      · rw [pubArm.eq_def]; simp only
        split
        · exact (iha).2 _ _
        · exact (ihb).2 _ _
  | refine t ψ ih =>
      refine ⟨fun ws => ?_, fun j p => ?_⟩
      · rw [pubWords.eq_def]; simp only; split
        · exact lblSub_refl _
        · exact ih.1 _
      · rw [pubArm.eq_def]; exact ih.2 _ _
  | iall t ih =>
      refine ⟨fun ws => ?_, fun j p => ?_⟩
      · rw [pubWords.eq_def]; simp only; split
        · exact lblSub_refl _
        · exact ih.1 _
      · rw [pubArm.eq_def]; exact ih.2 _ _
  | iex t ih =>
      refine ⟨fun ws => ?_, fun j p => ?_⟩
      · rw [pubWords.eq_def]; simp only; split
        · exact lblSub_refl _
        · exact ih.1 _
      · rw [pubArm.eq_def]; exact ih.2 _ _
  | mu t ih =>
      refine ⟨fun ws => ?_, fun j p => ?_⟩
      · rw [pubWords.eq_def]; simp only; split
        · exact lblSub_refl _
        · exact ih.1 _
      · rw [pubArm.eq_def]; exact ih.2 _ _
  | tex κ t ih =>
      refine ⟨fun ws => ?_, fun j p => ?_⟩
      · rw [pubWords.eq_def]; simp only; split
        · exact lblSub_refl _
        · exact ih.1 _
      · rw [pubArm.eq_def]; exact ih.2 _ _
  | array i e ih =>
      have hA : ∀ ws, LblSub (pubWords (.array i e) ws) ws := by
        intro ws
        rw [pubWords.eq_def]; simp only; split
        · exact lblSub_refl _
        · exact lblSub_nil _
      exact ⟨hA, fun j p => by rw [pubArm.eq_def]; exact hA p⟩
  | _ =>
      refine ⟨fun ws => ?_, fun j p => ?_⟩
      all_goals first
        | (rw [pubWords.eq_def]; simp only; split
           · exact lblSub_refl _
           · exact lblSub_nil _)
        | (rw [pubArm.eq_def]; simp only; rw [pubWords.eq_def]; simp only; split
           · exact lblSub_refl _
           · exact lblSub_nil _)

/-! ## (I2) The alloc case: a fresh label is named by no frame or stack word -/

/-- `EnvLbl` grows with the frontiers and the boxes. -/
theorem envLbl_mono {Eg Eg2 : GEnv} {env : Env} (hs : ∀ l f, Eg.pfr l = some f → Eg2.pfr l = some f)
    (hb : ∀ l B, Eg.box l = some B → Eg2.box l = some B) (h : EnvLbl Eg env) : EnvLbl Eg2 env := by
  intro x rt ws hm w hw l hn
  rcases h x rt ws hm w hw l hn with h1 | h1
  · left; intro h2
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 h1
    rw [hs l c hc] at h2; cases h2
  · right; intro h2
    obtain ⟨B, hB⟩ := Option.ne_none_iff_exists'.1 h1
    rw [hb l B hB] at h2; cases h2

/-- A binding whose words name only planted/published cells or boxes extends `EnvLbl`. -/
theorem envLbl_cons {Eg : GEnv} {env : Env} {x : String} {rt : Ty} {ws : List Word} (h : EnvLbl Eg env)
    (hw : ∀ w ∈ pubWords rt ws, ∀ l, Names l w → Eg.pfr l ≠ none ∨ Eg.box l ≠ none) :
    EnvLbl Eg ((x, rt, ws) :: env) := by
  intro y ry wy hm
  rcases List.mem_cons.1 hm with e | hm
  · cases e; exact hw
  · exact h y ry wy hm

/-- A label with no frontier and no box is named by no word of an `EnvLbl` environment, so (R) at
it holds at every `t`. -/
theorem envRts_of_unnamed {Eg : GEnv} {env : Env} {L : AllocLabel} (h : EnvLbl Eg env)
    (hs : Eg.pfr L = none) (hb : Eg.box L = none) (t : Ts) : EnvRts t L env := by
  intro x rt ws hm w hw hn
  rcases h x rt ws hm w hw L hn with h1 | h1
  · exact absurd hs h1
  · exact absurd hb h1

/-- An `own` reference binding counts no word. -/
theorem pubWords_ptr_own (u : Ty) (ws : List Word) : pubWords (.ptr .own u) ws = [] := by
  simp only [pubWords, sNo, mPub]; rfl

/-- (R) survives binding a value none of whose counted words names `L`. -/
theorem envRts_cons {t : Ts} {L : AllocLabel} {env : Env} {x : String} {rt : Ty} {ws : List Word}
    (h : EnvRts t L env) (hw : ∀ w ∈ pubWords rt ws, Names L w → t ≤ w.rts) :
    EnvRts t L ((x, rt, ws) :: env) := by
  intro y ry wy hm
  rcases List.mem_cons.1 hm with e | hm
  · cases e; exact hw
  · exact h y ry wy hm

/-- **The alloc case** (I2): at a label the step allocates (`FreshIn`, blank in `E_g` by
`GFreshE` = `SysInvN.gfresh`), every thread's frame and stack satisfy (R) at every `t` before the
step; and the allocating thread's post-frame, which binds only the new `own` reference, too. -/
theorem thRts_fresh {Eg : GEnv} {c : Cfg} {g : G} {n n' : Nat} {L : AllocLabel} (hL : LblSto Eg c)
    (hfr : GFreshE g Eg n n') (hin : FreshIn g n n' L) {i : Nat} {th : TTh} (hth : c.ths[i]? = some th)
    (t : Ts) : ThRts t L th := by
  obtain ⟨-, hb, hs⟩ := hfr L hin
  obtain ⟨he, hst⟩ := hL i th hth
  exact ⟨envRts_of_unnamed he hs hb t, fun f hf => envRts_of_unnamed (hst f hf) hs hb t⟩

theorem thRts_alloc {Eg : GEnv} {c : Cfg} {g : G} {n n' : Nat} {L : AllocLabel} (hL : LblSto Eg c)
    (hfr : GFreshE g Eg n n') (hin : FreshIn g n n' L) {i : Nat} {th th' : TTh} (hth : c.ths[i]? = some th)
    {x : String} {u : Ty} {ws : List Word} (he : th'.env = (x, .ptr .own u, ws) :: th.env)
    (hst : th'.stack = th.stack) (t : Ts) : ThRts t L th' := by
  obtain ⟨h1, h2⟩ := thRts_fresh hL hfr hin hth t
  refine ⟨?_, ?_⟩
  · rw [he]; exact envRts_cons h1 (by rw [pubWords_ptr_own]; intro w hw; cases hw)
  · rw [hst]; exact h2


/-! ## K-2a I1: the Lay bridge — counted words depend only on the layout form -/

theorem mPub_modeC (d : Nat) (μ : Mode) : mPub (modeC d μ) = mPub μ := by
  cases μ <;> rfl

theorem sNo_lyt : ∀ (t : Ty) (d : Nat), sNo (lyt d t) = sNo t := by
  intro t
  induction t with
  | prod a b iha ihb => intro d; simp only [lyt, sNo, iha, ihb]
  | sum a b iha ihb => intro d; simp only [lyt, sNo, iha, ihb]
  | array i t ih => intro d; simp only [lyt, sNo, ih]
  | ptr μ t _ => intro d; simp only [lyt, sNo, mPub_modeC]
  | ptrOpt μ t _ => intro d; simp only [lyt, sNo, mPub_modeC]
  | loc μ t _ => intro d; simp only [lyt, sNo, mPub_modeC]
  | mu t ih => intro d; simp only [lyt, sNo, ih]
  | tex κ t ih => intro d; simp only [lyt, sNo, ih]
  | iall t ih => intro d; simp only [lyt, sNo, ih]
  | iex t ih => intro d; simp only [lyt, sNo, ih]
  | refine t ψ ih => intro d; simp only [lyt]; split <;> simp only [sNo, ih]
  | _ => intro d; rfl

theorem sNo_etok : ∀ (t : Ty), sNo (etok t) = sNo t := by
  intro t
  induction t with
  | prod a b iha ihb => simp only [etok, sNo, iha, ihb]
  | sum a b iha ihb => simp only [etok, sNo, iha, ihb]
  | array i t ih => simp only [etok, sNo, ih]
  | ptr μ t _ => rfl
  | ptrOpt μ t _ => rfl
  | loc μ t _ => rfl
  | refine t ψ ih => simp only [etok, sNo, ih]
  | _ => rfl

theorem lnorm_lyt : ∀ (t : Ty) (d : Nat), lnorm (lyt d t) = lnorm t := by
  intro t
  induction t with
  | prod a b iha ihb => intro d; simp only [lyt, lnorm, iha, ihb]
  | sum a b iha ihb => intro d; simp only [lyt, lnorm, iha, ihb]
  | mu t ih => intro d; simp only [lyt, lnorm, ih]
  | tex κ t ih => intro d; simp only [lyt, lnorm, ih]
  | iall t ih => intro d; simp only [lyt, lnorm, ih]
  | iex t ih => intro d; simp only [lyt, lnorm, ih]
  | refine t ψ ih => intro d; simp only [lyt]; split <;> simp only [lnorm, ih]
  | _ => intro d; rfl

theorem armsOf_len_lyt : ∀ (t : Ty) (d : Nat), (armsOf (lyt d t)).length = (armsOf t).length := by
  intro t
  induction t with
  | sum a b iha ihb => intro d; simp only [lyt, armsOf, List.length_append, iha, ihb]
  | mu t ih => intro d; exact ih d
  | tex κ t ih => intro d; exact ih d
  | iall t ih => intro d; exact ih (d + 1)
  | iex t ih => intro d; exact ih (d + 1)
  | refine t ψ ih => intro d; simp only [lyt]; split <;> simp only [armsOf, ih]
  | _ => intro d; rfl

theorem armsOf_len_etok : ∀ (t : Ty), (armsOf (etok t)).length = (armsOf t).length := by
  intro t
  induction t with
  | sum a b iha ihb => simp only [etok, armsOf, List.length_append, iha, ihb]
  | refine t ψ ih => simp only [etok, armsOf, ih]
  | _ => rfl

/-- A refinement counts its body's words. -/
theorem pubWords_refine (t : Ty) (ψ : Pred) (ws : List Word) : pubWords (.refine t ψ) ws = pubWords t ws := by
  by_cases h : sNo t = true
  · have h' : sNo (.refine t ψ) = true := h
    rw [pubWords_of_sNo h', pubWords_of_sNo h]
  · have h' : ¬ sNo (.refine t ψ) = true := h
    rw [pubWords.eq_def]; simp only [h', Bool.false_eq_true, ite_false]

theorem pubWords_lyt : ∀ (t : Ty) (d : Nat),
    (∀ ws, pubWords (lyt d t) ws = pubWords t ws) ∧ (∀ j p, pubArm (lyt d t) j p = pubArm t j p) := by
  intro t
  induction t with
  | prod a b iha ihb =>
      intro d
      have hs := sNo_lyt (.prod a b) d
      have hw := accs_lyt a d
      simp only [lyt] at hs ⊢
      have h1 : ∀ ws, pubWords (.prod (lyt d a) (lyt d b)) ws = pubWords (.prod a b) ws := by
        intro ws; simp only [pubWords, hs, wc, hw, (iha d).1, (ihb d).1]
      exact ⟨h1, fun j p => by simp only [pubArm]; exact h1 p⟩
  | sum a b iha ihb =>
      intro d
      have hs := sNo_lyt (.sum a b) d
      have ht := lyt_tier (.sum a b) d
      have hl := lnorm_lyt (.sum a b) d
      simp only [lyt] at hs ht hl ⊢
      have hal := armsOf_len_lyt a d
      refine ⟨fun ws => ?_, fun j p => ?_⟩
      · simp only [pubWords, hs, ht, hl, hal, (iha d).2, (ihb d).2]
      · simp only [pubArm, hal, (iha d).2, (ihb d).2]
  | refine t ψ ih =>
      intro d
      simp only [lyt]
      split
      · exact ⟨fun ws => by rw [pubWords_refine, pubWords_refine, (ih d).1],
          fun j p => by simp only [pubArm, (ih d).2]⟩
      · exact ⟨fun ws => by rw [pubWords_refine, (ih d).1],
          fun j p => by simp only [pubArm, (ih d).2]⟩
  | iall t ih =>
      intro d
      have hs := sNo_lyt (.iall t) d
      simp only [lyt] at hs ⊢
      exact ⟨fun ws => by simp only [pubWords, hs, (ih (d + 1)).1],
        fun j p => by simp only [pubArm, (ih (d + 1)).2]⟩
  | iex t ih =>
      intro d
      have hs := sNo_lyt (.iex t) d
      simp only [lyt] at hs ⊢
      exact ⟨fun ws => by simp only [pubWords, hs, (ih (d + 1)).1],
        fun j p => by simp only [pubArm, (ih (d + 1)).2]⟩
  | mu t ih =>
      intro d
      have hs := sNo_lyt (.mu t) d
      simp only [lyt] at hs ⊢
      exact ⟨fun ws => by simp only [pubWords, hs, (ih d).1],
        fun j p => by simp only [pubArm, (ih d).2]⟩
  | tex κ t ih =>
      intro d
      have hs := sNo_lyt (.tex κ t) d
      simp only [lyt] at hs ⊢
      exact ⟨fun ws => by simp only [pubWords, hs, (ih d).1],
        fun j p => by simp only [pubArm, (ih d).2]⟩
  | array i e _ =>
      intro d
      have hs := sNo_lyt (.array i e) d
      simp only [lyt] at hs ⊢
      have h1 : ∀ ws, pubWords (.array (idxC d i) (lyt d e)) ws = pubWords (.array i e) ws := by
        intro ws; rw [pubWords.eq_def, pubWords.eq_def]; simp only [hs]
      exact ⟨h1, fun j p => by simp only [pubArm]; exact h1 p⟩
  | ptr μ u _ =>
      intro d
      exact ⟨fun ws => by simp only [lyt, pubWords, sNo, mPub_modeC]; rfl,
        fun j p => by simp only [lyt, pubArm, pubWords, sNo, mPub_modeC]; rfl⟩
  | ptrOpt μ u _ =>
      intro d
      exact ⟨fun ws => by simp only [lyt, pubWords, sNo, mPub_modeC]; rfl,
        fun j p => by simp only [lyt, pubArm, pubWords, sNo, mPub_modeC]; rfl⟩
  | loc μ u _ =>
      intro d
      exact ⟨fun ws => by simp only [lyt, pubWords, sNo, mPub_modeC]; rfl,
        fun j p => by simp only [lyt, pubArm, pubWords, sNo, mPub_modeC]; rfl⟩
  | _ =>
      intro d
      exact ⟨fun ws => by simp [lyt, pubWords, sNo], fun j p => by simp [lyt, pubArm, pubWords, sNo]⟩

theorem pubWords_etok : ∀ (t : Ty),
    (∀ ws, pubWords (etok t) ws = pubWords t ws) ∧ (∀ j p, pubArm (etok t) j p = pubArm t j p) := by
  intro t
  induction t with
  | prod a b iha ihb =>
      have hs := sNo_etok (.prod a b)
      have hw := accs_etok a
      simp only [etok] at hs ⊢
      have h1 : ∀ ws, pubWords (.prod (etok a) (etok b)) ws = pubWords (.prod a b) ws := by
        intro ws; simp only [pubWords, hs, wc, hw, iha.1, ihb.1]
      exact ⟨h1, fun j p => by simp only [pubArm]; exact h1 p⟩
  | sum a b iha ihb =>
      have hs := sNo_etok (.sum a b)
      have ht := tier_etok (.sum a b)
      have hl := lnorm_etok (.sum a b)
      simp only [etok] at hs ht hl ⊢
      have hal := armsOf_len_etok a
      refine ⟨fun ws => ?_, fun j p => ?_⟩
      · simp only [pubWords, hs, ht, hl, hal, iha.2, ihb.2]
      · simp only [pubArm, hal, iha.2, ihb.2]
  | refine t ψ ih =>
      exact ⟨fun ws => by simp only [etok]; rw [pubWords_refine, pubWords_refine, ih.1],
        fun j p => by simp only [etok, pubArm, ih.2]⟩
  | array i e _ =>
      have hs := sNo_etok (.array i e)
      simp only [etok] at hs ⊢
      have h1 : ∀ ws, pubWords (.array i (etok e)) ws = pubWords (.array i e) ws := by
        intro ws; rw [pubWords.eq_def, pubWords.eq_def]; simp only [hs]
      exact ⟨h1, fun j p => by simp only [pubArm]; exact h1 p⟩
  | ptr μ u _ => exact ⟨fun ws => by simp only [etok, pubWords, sNo]; rfl, fun j p => by simp only [etok, pubArm, pubWords, sNo]; rfl⟩
  | ptrOpt μ u _ => exact ⟨fun ws => by simp only [etok, pubWords, sNo]; rfl, fun j p => by simp only [etok, pubArm, pubWords, sNo]; rfl⟩
  | loc μ u _ => exact ⟨fun ws => by simp only [etok, pubWords, sNo]; rfl, fun j p => by simp only [etok, pubArm, pubWords, sNo]; rfl⟩
  | code a b _ _ => exact ⟨fun ws => by simp only [etok, pubWords, sNo], fun j p => by simp only [etok, pubArm, pubWords, sNo]⟩
  | _ => exact ⟨fun ws => by simp [etok, pubWords, sNo], fun j p => by simp [etok, pubArm, pubWords, sNo]⟩

/-- Two types with the same layout form count the same words. -/
theorem pubWords_elyt {a b : Ty} {d : Nat} (h : etok (lyt d a) = etok (lyt d b)) (ws : List Word) :
    pubWords a ws = pubWords b ws := by
  rw [← (pubWords_lyt a d).1, ← (pubWords_etok (lyt d a)).1, h, (pubWords_etok _).1, (pubWords_lyt b d).1]

/-- **I1, the Lay bridge**: a binding laid out as its static type says counts the words its closed
static type counts. -/
theorem pubWords_Lay {σs : List Ty} {t rt : Ty} {ws : List Word} (h : Lay σs t rt ws) :
    pubWords rt ws = pubWords (close σs t) ws :=
  pubWords_elyt h.2.2.2.2 ws

/-! ## (I2) Counted words name only allocated labels -/

/-- The counted words name only labels the words name. -/
theorem labsIn_pubWords {G : AllocLabel → Prop} : ∀ (R : Ty),
    (∀ ws, LabsIn G ws → LabsIn G (pubWords R ws)) ∧ (∀ j p, LabsIn G p → LabsIn G (pubArm R j p)) := by
  intro R
  induction R with
  | prod a b iha ihb =>
      have h1 : ∀ ws, LabsIn G ws → LabsIn G (pubWords (.prod a b) ws) := by
        intro ws h
        by_cases hs : sNo (.prod a b) = true
        · rw [pubWords_of_sNo hs]; exact h
        · simp only [pubWords, hs, Bool.false_eq_true, ite_false]
          split
          · intro w hw
            rcases List.mem_append.1 hw with hw | hw
            · exact iha.1 _ (LabsIn_sub h (fun _ hx => List.mem_of_mem_take hx)) w hw
            · exact ihb.1 _ (LabsIn_sub h (fun _ hx => List.mem_of_mem_drop hx)) w hw
          · intro w hw; cases hw
      exact ⟨h1, fun j p hp => by simp only [pubArm]; exact h1 p hp⟩
  | sum a b iha ihb =>
      have h2 : ∀ j p, LabsIn G p → LabsIn G (pubArm (.sum a b) j p) := by
        intro j p hp
        simp only [pubArm]
        split
        · exact iha.2 _ _ hp
        · exact ihb.2 _ _ hp
      refine ⟨fun ws h => ?_, h2⟩
      by_cases hs : sNo (.sum a b) = true
      · rw [pubWords_of_sNo hs]; exact h
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]
        split
        · exact h
        · split
          · rename_i j p hd
            have hp := decodeArm_labs hd h
            split
            · exact iha.2 _ _ hp
            · exact ihb.2 _ _ hp
          · intro w hw; cases hw
  | refine t ψ ih =>
      exact ⟨fun ws h => by rw [pubWords_refine]; exact ih.1 ws h, fun j p hp => by simp only [pubArm]; exact ih.2 j p hp⟩
  | iall t ih =>
      refine ⟨fun ws h => ?_, fun j p hp => by simp only [pubArm]; exact ih.2 j p hp⟩
      by_cases hs : sNo (.iall t) = true
      · rw [pubWords_of_sNo hs]; exact h
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 ws h
  | iex t ih =>
      refine ⟨fun ws h => ?_, fun j p hp => by simp only [pubArm]; exact ih.2 j p hp⟩
      by_cases hs : sNo (.iex t) = true
      · rw [pubWords_of_sNo hs]; exact h
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 ws h
  | mu t ih =>
      refine ⟨fun ws h => ?_, fun j p hp => by simp only [pubArm]; exact ih.2 j p hp⟩
      by_cases hs : sNo (.mu t) = true
      · rw [pubWords_of_sNo hs]; exact h
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 ws h
  | tex κ t ih =>
      refine ⟨fun ws h => ?_, fun j p hp => by simp only [pubArm]; exact ih.2 j p hp⟩
      by_cases hs : sNo (.tex κ t) = true
      · rw [pubWords_of_sNo hs]; exact h
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 ws h
  | _ =>
      refine ⟨fun ws h => ?_, fun j p hp => ?_⟩
      · rw [pubWords.eq_def]; simp only []
        split
        · exact h
        · intro w hw; cases hw
      · simp only [pubArm]; rw [pubWords.eq_def]; simp only []
        split
        · exact hp
        · intro w hw; cases hw

/-- Strip the shape-transparent wrappers (`refine`, `μ`, `∀`) off a runtime type. -/
theorem unwrapR : ∀ (R : Ty) (ws : List Word), ∃ R0, shp R0 = shp R ∧ wc R0 = wc R ∧ (Valid R ws → Valid R0 ws) ∧
    (∀ t ψ, R0 ≠ .refine t ψ) ∧ (∀ t, R0 ≠ .mu t) ∧ (∀ t, R0 ≠ .iall t) := by
  intro R ws
  induction R with
  | refine t ψ ih =>
      obtain ⟨R0, h1, h2, h3, h4⟩ := ih
      exact ⟨R0, h1, by rw [h2]; simp only [wc, accs], h3, h4⟩
  | mu t ih =>
      obtain ⟨R0, h1, h2, h3, h4⟩ := ih
      exact ⟨R0, h1, by rw [h2]; simp only [wc, accs], h3, h4⟩
  | iall t ih =>
      obtain ⟨R0, h1, h2, h3, h4⟩ := ih
      exact ⟨R0, h1, by rw [h2]; simp only [wc, accs], h3, h4⟩
  | _ => refine ⟨_, rfl, rfl, id, ?_, ?_, ?_⟩ <;> simp

/-- **Inversion, at an agreeing runtime type.**  In an env with no type-variable values, every
`loc` word of a value of `T` (at the shape of a runtime type `R` agreeing with `T`, valid at `R`,
of its word count) names a cell of Σ or a box.  (`locPub_VR` with the runtime type apart from the
static one and every mode allowed: `VR` at a reference of any mode reads `η.sto`.) -/
theorem labsIn_VR {G : AllocLabel → Prop} : ∀ (T : Ty) (ρ : Nat → Nat) (η : TEnv) (R : Ty) (ws : List Word),
    (∀ k r vs, ¬ η.rels k r vs) → (∀ l c, η.sto l = some c → G l) → (∀ l B, η.box l = some B → G l) →
    shp R = shp T → wc R = some ws.length → Valid R ws → VR ρ η T (shp R) ws → LabsIn G ws := by
  intro T
  induction T with
  | prod a b iha ihb =>
    intro ρ η R ws hrel hS hB hshp hwc hval hv
    obtain ⟨R0, e1, e2, e3, n1, n2, n3⟩ := unwrapR R ws
    have hval0 := e3 hval
    rw [hshp] at e1 hv
    rw [← e2] at hwc
    obtain ⟨ra, rb, hr, hv⟩ := hv
    simp only [shp, Shp.prod.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    cases R0 with
    | prod Ra Rb =>
      simp only [shp, Shp.prod.injEq] at e1
      obtain ⟨ea, eb⟩ := e1
      rw [wc_prod] at hwc
      cases ha : wc Ra with
      | none => simp [ha] at hwc
      | some na =>
        cases hb : wc Rb with
        | none => simp [ha, hb] at hwc
        | some nb =>
          simp [ha, hb] at hwc
          obtain ⟨hle, hva, hvb⟩ := hv na (by rw [← ea, shp_wc]; exact ha)
          obtain ⟨Va, Vb⟩ := hval0 na ha
          intro w hw
          rw [← List.take_append_drop na ws] at hw
          rcases List.mem_append.1 hw with h | h
          · exact iha ρ η Ra _ hrel hS hB ea (by rw [ha, List.length_take]; congr 1; omega) Va
              (by rw [ea]; exact hva) w h
          · exact ihb ρ η Rb _ hrel hS hB eb (by rw [hb, List.length_drop]; congr 1; omega) Vb
              (by rw [eb]; exact hvb) w h
    | refine t ψ => exact absurd rfl (n1 t ψ)
    | mu t => exact absurd rfl (n2 t)
    | iall t => exact absurd rfl (n3 t)
    | _ => simp [shp] at e1
  | sum a b iha ihb =>
    intro ρ η R ws hrel hS hB hshp hwc hval hv
    obtain ⟨R0, e1, e2, e3, n1, n2, n3⟩ := unwrapR R ws
    have hval0 := e3 hval
    rw [hshp] at e1 hv
    rw [← e2] at hwc
    obtain ⟨n, Ra, Rb, hr, hcase⟩ := hv
    simp only [shp, lnorm, Shp.sum.injEq, Ty.sum.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    cases R0 with
    | sum A B =>
      simp only [shp, lnorm, Shp.sum.injEq, Ty.sum.injEq] at e1
      obtain ⟨-, eA, eB⟩ := e1
      rw [← eA, ← eB] at hcase
      have hsA : shp A = shp a := by rw [← shp_lnorm A, eA, shp_lnorm]
      have hsB : shp B = shp b := by rw [← shp_lnorm B, eB, shp_lnorm]
      have hlenA : (armsOf (lnorm A)).length = (armsOf A).length := by
        rw [armsOf_lnorm, List.length_map]
      have htl : (Ty.sum (lnorm A) (lnorm B)).tier = (Ty.sum A B).tier := tier_lnorm (.sum A B)
      intro w hw y g hx
      rcases hcase with ⟨-, x, s, Bx, hvals, -, hbox, -⟩ | ⟨j, p, hd, hA, hB2⟩
      · have hm := locPub_mem_val hvals hw
        rw [hx] at hm
        simp at hm
        obtain ⟨rfl, -⟩ := hm
        exact hB _ _ hbox
      · rcases hval0 with htb | ⟨j', p', arm, hd', -, -, ⟨q0, he, hveq⟩, hA', hB'⟩
        · rw [htl, htb] at hd; simp [decodeArm] at hd
        · have hd2 := decodeArm_mono (arms_lnorm (.sum A B)) hd'
          rw [htl] at hd
          have hjp : (j, p) = (j', p') := Option.some.inj (hd.symm.trans hd2)
          simp only [Prod.mk.injEq] at hjp
          obtain ⟨rfl, rfl⟩ := hjp
          have hm : w.val ∈ q0.map (·.val) := hveq ▸ List.mem_map_of_mem hw
          obtain ⟨w0, hw0, hv0⟩ := List.mem_map.1 hm
          obtain ⟨w1, hw1, g1, hv1⟩ := locPub_encFwd he w0 hw0 y g (hv0.trans hx)
          by_cases hj : j < (armsOf A).length
          · obtain ⟨q, hq, hvq⟩ := hA (by rw [hlenA]; exact hj)
            obtain ⟨q', hq', hsq, hwq, hvalq⟩ := hA' hj
            have hqq : q' = q := Option.some.inj ((ofArm_lnorm hq').symm.trans hq)
            subst hqq
            obtain ⟨w2, hw2, g2, hv2⟩ := locPub_ofArmRev hq' w1 hw1 y g1 hv1
            have hwcq : wc A = some q'.length := by
              cases hu : accs A with
              | none => simp [wc, hu] at hwq
              | some us => simp only [wc, hu, Option.map_some]; rw [hsq us hu]
            rw [shp_lnorm] at hvq
            exact iha ρ η A q' hrel hS hB hsA hwcq hvalq hvq w2 hw2 y g2 hv2
          · have hj2 : (armsOf A).length ≤ j := Nat.le_of_not_lt hj
            obtain ⟨q, hq, hvq⟩ := hB2 (by rw [hlenA]; exact hj2)
            obtain ⟨q', hq', hsq, hwq, hvalq⟩ := hB' hj2
            rw [hlenA] at hq
            have hqq : q' = q := Option.some.inj ((ofArm_lnorm hq').symm.trans hq)
            subst hqq
            obtain ⟨w2, hw2, g2, hv2⟩ := locPub_ofArmRev hq' w1 hw1 y g1 hv1
            have hwcq : wc B = some q'.length := by
              cases hu : accs B with
              | none => simp [wc, hu] at hwq
              | some us => simp only [wc, hu, Option.map_some]; rw [hsq us hu]
            rw [shp_lnorm] at hvq
            exact ihb ρ η B q' hrel hS hB hsB hwcq hvalq hvq w2 hw2 y g2 hv2
    | refine t ψ => exact absurd rfl (n1 t ψ)
    | mu t => exact absurd rfl (n2 t)
    | iall t => exact absurd rfl (n3 t)
    | _ => simp [shp] at e1
  | refine t ψ ih =>
    intro ρ η R ws hrel hS hB hshp hwc hval hv
    exact ih ρ η R ws hrel hS hB hshp hwc hval hv.1
  | iall t ih =>
    intro ρ η R ws hrel hS hB hshp hwc hval hv
    exact ih (vcons 0 ρ) η R ws hrel hS hB hshp hwc hval (hv 0)
  | mu t ih =>
    intro ρ η R ws hrel hS hB hshp hwc hval hv
    exact ih ρ (η.push0 (TermClose.cl ρ η.wit 0 0 (.mu t))) R ws (locPub_push0_rels hrel _) hS hB hshp hwc hval hv
  | iex t ih =>
    intro ρ η R ws hrel hS hB hshp hwc hval hv
    obtain ⟨R0, e1, e2, e3, n1, n2, n3⟩ := unwrapR R ws
    have hval0 := e3 hval
    rw [hshp] at e1 hv
    rw [← e2] at hwc
    obtain ⟨n, rb, w, hr, hv⟩ := hv
    simp only [shp, Shp.iex.injEq] at hr
    obtain ⟨-, rfl⟩ := hr
    cases R0 with
    | iex Rb =>
      simp only [shp, Shp.iex.injEq] at e1
      rw [wc_iex] at hwc
      exact ih (vcons w ρ) η Rb ws hrel hS hB e1.2 hwc hval0 (by rw [e1.2]; exact hv)
    | refine t ψ => exact absurd rfl (n1 t ψ)
    | mu t => exact absurd rfl (n2 t)
    | iall t => exact absurd rfl (n3 t)
    | _ => simp [shp] at e1
  | tex κ t ih =>
    intro ρ η R ws hrel hS hB hshp hwc hval hv
    obtain ⟨R0, e1, e2, e3, n1, n2, n3⟩ := unwrapR R ws
    have hval0 := e3 hval
    rw [hshp] at e1 hv
    rw [← e2] at hwc
    obtain ⟨n, rb, s, hr, -, -, hv⟩ := hv
    simp only [shp, Shp.tex.injEq] at hr
    obtain ⟨-, rfl⟩ := hr
    cases R0 with
    | tex κ' Rb =>
      simp only [shp, Shp.tex.injEq] at e1
      rw [wc_tex] at hwc
      exact ih ρ (η.push0 s) Rb ws (locPub_push0_rels hrel s) hS hB e1.2 hwc hval0 (by rw [e1.2]; exact hv)
    | refine t ψ => exact absurd rfl (n1 t ψ)
    | mu t => exact absurd rfl (n2 t)
    | iall t => exact absurd rfl (n3 t)
    | _ => simp [shp] at e1
  | tvar k =>
    intro ρ η R ws hrel hS hB hshp hwc hval hv
    obtain ⟨ws', -, hg⟩ := hv
    exact absurd hg (hrel _ _ _)
  | ptr μ u =>
    intro ρ η R ws hrel hS hB hshp hwc hval hv w hw x g hx
    obtain ⟨a, c, h1, -, h3, -⟩ := hv
    have hm := locPub_mem_val h1 hw
    rw [hx] at hm; simp at hm; obtain ⟨rfl, -⟩ := hm
    exact hS _ _ h3
  | ptrOpt μ u =>
    intro ρ η R ws hrel hS hB hshp hwc hval hv w hw x g hx
    rcases hv with h0 | ⟨a, c, h1, -, h3, -⟩
    · have hm := locPub_mem_val h0 hw
      rw [hx] at hm; simp at hm
    · have hm := locPub_mem_val h1 hw
      rw [hx] at hm; simp at hm; obtain ⟨rfl, -⟩ := hm
      exact hS _ _ h3
  | loc μ u =>
    intro ρ η R ws hrel hS hB hshp hwc hval hv w hw x g hx
    rcases hv with ⟨h0, -⟩ | ⟨a, c, U, h1, h3, -⟩
    · have hm := locPub_mem_val h0 hw
      rw [hx] at hm; simp at hm
    · have hm := locPub_mem_val h1 hw
      rw [hx] at hm; simp at hm; obtain ⟨rfl, -⟩ := hm
      exact hS _ _ h3
  | void =>
    intro ρ η R ws hrel hS hB hshp hwc hval hv
    simp [VR] at hv
  | intS i =>
    intro ρ η R ws hrel hS hB hshp hwc hval hv w hw x g hx
    have hm := locPub_mem_val hv hw
    rw [hx] at hm; simp at hm
  | int =>
    intro ρ η R ws hrel hS hB hshp hwc hval hv w hw x g hx
    obtain ⟨n, hn⟩ := hv
    have hm := locPub_mem_val hn hw
    rw [hx] at hm; simp at hm
  | tid =>
    intro ρ η R ws hrel hS hB hshp hwc hval hv w hw x g hx
    obtain ⟨n, c, hn, h3, -⟩ := hv
    have hm := locPub_mem_val hn hw
    rw [hx] at hm; simp at hm; obtain ⟨rfl, -⟩ := hm
    exact hS _ _ h3
  | fix sg wd =>
    intro ρ η R ws hrel hS hB hshp hwc hval hv w hw x g hx
    obtain ⟨-, n, hn, -⟩ := hv
    have hm := locPub_mem_val hn hw
    rw [hx] at hm; simp at hm
  | lanes sg wd =>
    intro ρ η R ws hrel hS hB hshp hwc hval hv w hw x g hx
    obtain ⟨-, n, hn⟩ := hv
    have hm := locPub_mem_val hn hw
    rw [hx] at hm; simp at hm
  | code a b _ _ =>
    intro ρ η R ws hrel hS hB hshp hwc hval hv w hw x g hx
    obtain ⟨i, d, hn, -⟩ := hv
    have hm := locPub_mem_val hn hw
    rw [hx] at hm; simp at hm
  | word r P =>
    intro ρ η R ws hrel hS hB hshp hwc hval hv w hw x g hx
    have hlen : wc (.word r P) = some ws.length := by rw [← shp_wc, ← hshp, shp_wc]; exact hwc
    cases hg : P.ghost with
    | true =>
      simp [wc, accs, hg, nWords] at hlen
      rw [List.eq_nil_of_length_eq_zero hlen.symm] at hw; simp at hw
    | false =>
      obtain ⟨n, hn, -⟩ := hv.2 hg
      have hm := locPub_mem_val hn hw
      rw [hx] at hm; simp at hm
  | word2 r P =>
    intro ρ η R ws hrel hS hB hshp hwc hval hv w hw x g hx
    obtain ⟨-, n0, n1, hn, -⟩ := hv
    have hm := locPub_mem_val hn hw
    rw [hx] at hm; simp at hm
  | epair r P =>
    intro ρ η R ws hrel hS hB hshp hwc hval hv w hw x g hx
    obtain ⟨-, n0, n1, hn⟩ := hv
    have hm := locPub_mem_val hn hw
    rw [hx] at hm; simp at hm
  | array i t _ =>
    intro ρ η R ws hrel hS hB hshp hwc
    have hlen : wc (.array i t) = some ws.length := by rw [← shp_wc, ← hshp, shp_wc]; exact hwc
    simp [wc, accs] at hlen
  | unit | share _ | cap _ _ | tok _ _ | tok2 _ _ _ _ | tokE _ _ _ =>
    intro ρ η R ws hrel hS hB hshp hwc hval hv w hw
    have hlen := hwc
    rw [← shp_wc, hshp, shp_wc] at hlen
    simp [wc, accs, nWords] at hlen
    rw [List.eq_nil_of_length_eq_zero hlen.symm] at hw; simp at hw


/-- **names_of_VR** (I2): a typed binding — `VR` at its static type `t`, laid out (`Lay`) at its
runtime type `rt` — counts only words naming cells of Σ or boxes.  The binding's value is read at
the closure `cl ρ η.wit 0 0 t` (`VR_close`), whose shape is `rt`'s (`Lay`'s skeleton equation and
`hsig`, which `sig_WitL` gives). -/
theorem labsIn_binding {G : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {t rt : Ty}
    {ws : List Word} (hc : Coh η) (hS : ∀ l c, η.sto l = some c → G l) (hB : ∀ l B, η.box l = some B → G l)
    (hsig : sig (close σs t) = sig (TermClose.cl ρ η.wit 0 0 t)) (hv : VR ρ η t (shp rt) ws)
    (hL : Lay σs t rt ws) : LabsIn G (pubWords rt ws) := by
  have hv' : VR ρ (CE η) (TermClose.cl ρ η.wit 0 0 t) (shp rt) ws :=
    (VR_close hc ρ t [] 0 ρ ρ (shp rt) ws (fun _ => rfl) (fun _ h => absurd h (Nat.not_lt_zero _))).1 hv
  have hshp : shp rt = shp (TermClose.cl ρ η.wit 0 0 t) := (shp_of_eskel hL.2.1).trans (shp_of_sig hsig)
  have hwc : wc rt = some ws.length := by
    have h1 := hL.2.2.1
    cases hu : accs rt with
    | none => simp [wc, hu] at h1
    | some us => simp only [wc, hu, Option.map_some]; rw [hL.1 us hu]
  have hws := labsIn_VR (TermClose.cl ρ η.wit 0 0 t) ρ (CE η) rt ws (fun _ _ _ h => h) hS hB hshp hwc hL.2.2.2.1 hv'
  exact (labsIn_pubWords rt).1 ws hws

/-- `names_of_VR` with the closure's signature from the frame's witness list (`sig_WitL`). -/
theorem labsIn_binding_WitL {G : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {opq : List Nat}
    {t rt : Ty} {ws : List Word} (hc : Coh η) (hS : ∀ l c, η.sto l = some c → G l)
    (hB : ∀ l B, η.box l = some B → G l) (hW : WitL σs η.wit opq) (hg : opq.all (fun k => t.guardT k) = true)
    (hr : ∀ k, t.guardT k = false → k < σs.length) (hv : VR ρ η t (shp rt) ws) (hL : Lay σs t rt ws) :
    LabsIn G (pubWords rt ws) :=
  labsIn_binding hc hS hB (sig_WitL hW ρ hg hr) hv hL

/-! ## The chunked reference reading: `pubWords` before (D1) -/

mutual
/-- `pubWords` as it was before (D1) dropped the array case: each element of a literal-length array
counted at its own chunk.  A reference definition only: nothing reads it but `pubWords_arrFree`. -/
def pubWordsC : Ty → List Word → List Word
  | .prod a b, ws =>
      if sNo (.prod a b) then ws else
      match wc a with
      | some n => pubWordsC a (ws.take n) ++ pubWordsC b (ws.drop n)
      | none => []
  | .sum a b, ws =>
      if sNo (.sum a b) then ws else
      if (Ty.sum a b).tier = .boxed then ws
      else
        match decodeArm (Ty.sum a b).tier (armsOf (lnorm (.sum a b))) ws with
        | some (j, p) => if j < (armsOf a).length then pubArmC a j p else pubArmC b (j - (armsOf a).length) p
        | none => []
  | .refine t ψ, ws => if sNo (.refine t ψ) then ws else pubWordsC t ws
  | .iall t, ws => if sNo (.iall t) then ws else pubWordsC t ws
  | .iex t, ws => if sNo (.iex t) then ws else pubWordsC t ws
  | .mu t, ws => if sNo (.mu t) then ws else pubWordsC t ws
  | .tex κ t, ws => if sNo (.tex κ t) then ws else pubWordsC t ws
  | .array i e, ws =>
      if sNo (.array i e) then ws else
      match i, wc e with
      | .lit n, some m => (List.range n).flatMap fun j => pubWordsC e ((ws.drop (j * m)).take m)
      | _, _ => []
  | t, ws => if sNo t then ws else []

/-- `pubArm`, chunked. -/
def pubArmC : Ty → Nat → List Word → List Word
  | .sum a b, j, p => if j < (armsOf a).length then pubArmC a j p else pubArmC b (j - (armsOf a).length) p
  | .refine t _, j, p => pubArmC t j p
  | .iall t, j, p => pubArmC t j p
  | .iex t, j, p => pubArmC t j p
  | .mu t, j, p => pubArmC t j p
  | .tex _ t, j, p => pubArmC t j p
  | t, _, p => pubWordsC t p
end

/-- On array-free types (every value type: `arrFree`) dropping the array case changes
nothing: `pubWords` is the chunked reading. -/
theorem pubWords_arrFree : ∀ (t : Ty), t.arrFree = true →
    (∀ ws, pubWords t ws = pubWordsC t ws) ∧ (∀ j p, pubArm t j p = pubArmC t j p) := by
  intro t
  induction t with
  | prod a b iha ihb =>
      intro h
      simp only [Ty.arrFree, Bool.and_eq_true] at h
      have h1 : ∀ ws, pubWords (.prod a b) ws = pubWordsC (.prod a b) ws := by
        intro ws; simp only [pubWords, pubWordsC, (iha h.1).1, (ihb h.2).1]; rfl
      exact ⟨h1, fun j p => by simp only [pubArm, pubArmC]; exact h1 p⟩
  | sum a b iha ihb =>
      intro h
      simp only [Ty.arrFree, Bool.and_eq_true] at h
      exact ⟨fun ws => by simp only [pubWords, pubWordsC, (iha h.1).2, (ihb h.2).2]; rfl,
        fun j p => by simp only [pubArm, pubArmC, (iha h.1).2, (ihb h.2).2]⟩
  | refine t ψ ih =>
      intro h
      exact ⟨fun ws => by simp only [pubWords, pubWordsC, (ih h).1],
        fun j p => by simp only [pubArm, pubArmC, (ih h).2]⟩
  | iall t ih =>
      intro h
      exact ⟨fun ws => by simp only [pubWords, pubWordsC, (ih h).1],
        fun j p => by simp only [pubArm, pubArmC, (ih h).2]⟩
  | iex t ih =>
      intro h
      exact ⟨fun ws => by simp only [pubWords, pubWordsC, (ih h).1],
        fun j p => by simp only [pubArm, pubArmC, (ih h).2]⟩
  | mu t ih =>
      intro h
      exact ⟨fun ws => by simp only [pubWords, pubWordsC, (ih h).1],
        fun j p => by simp only [pubArm, pubArmC, (ih h).2]⟩
  | tex κ t ih =>
      intro h
      exact ⟨fun ws => by simp only [pubWords, pubWordsC, (ih h).1],
        fun j p => by simp only [pubArm, pubArmC, (ih h).2]⟩
  | array i e _ => intro h; simp [Ty.arrFree] at h
  | _ =>
      intro _
      exact ⟨fun ws => by rw [pubWords.eq_def, pubWordsC.eq_def],
        fun j p => by simp only [pubArm, pubArmC]; rw [pubWords.eq_def, pubWordsC.eq_def]⟩


/-! ## (EnvPub) Counted words name only published/planted cells or boxes -/

theorem sNo_rf (t : Ty) : sNo (rf t) = sNo t := by cases t <;> rfl

theorem mPub_skelM (μ : Mode) : mPub (skelM μ) = mPub μ := by cases μ <;> rfl

theorem sNo_skel : ∀ t : Ty, sNo (skel t) = sNo t := by
  intro t
  induction t with
  | prod a b iha ihb => simp only [skel, sNo, iha, ihb]
  | sum a b iha ihb => simp only [skel, sNo, iha, ihb]
  | array i t ih => simp only [skel, sNo, ih]
  | ptr μ t _ => simp only [skel, sNo, mPub_skelM]
  | ptrOpt μ t _ => simp only [skel, sNo, mPub_skelM]
  | loc μ t _ => simp only [skel, sNo, mPub_skelM]
  | mu t ih => simp only [skel, sNo, ih]
  | tex κ t ih => simp only [skel, sNo, ih]
  | iall t ih => simp only [skel, sNo, ih]
  | iex t ih => simp only [skel, sNo, ih]
  | refine t ψ ih => simp only [skel, sNo_rf, sNo, ih]
  | _ => rfl

theorem sNo_er : ∀ t : Ty, sNo (er t) = sNo t := by
  intro t
  induction t with
  | prod a b iha ihb => simp only [er, sNo, iha, ihb]
  | sum a b iha ihb => simp only [er, sNo, iha, ihb]
  | array i t ih => simp only [er, sNo, ih]
  | mu t ih => simp only [er, sNo, ih]
  | tex κ t ih => simp only [er, sNo, ih]
  | iall t ih => simp only [er, sNo, ih]
  | iex t ih => simp only [er, sNo, ih]
  | refine t ψ ih => simp only [er, sNo, ih]
  | _ => rfl

theorem sNo_sig (t : Ty) : sNo (sig t) = sNo t := by simp only [sig, sNo_er, sNo_skel]

theorem sig_refine (t : Ty) (ψ : Pred) : sig (.refine t ψ) = rf (sig t) := er_rf (skel t)

theorem rf_eq_refine {x u : Ty} {ψ : Pred} (h : rf x = .refine u ψ) : u = x := by
  cases x <;> simp [rf] at h <;> exact h.1.symm

/-- A head the counted words descend through. -/
def IsStruct : Ty → Bool
  | .prod _ _ | .sum _ _ | .refine _ _ | .iall _ | .iex _ | .mu _ | .tex _ _ => true
  | _ => false

theorem sig_inv_prod {R x y : Ty} (h : sig R = .prod x y) : ∃ Ra Rb, R = .prod Ra Rb ∧ sig Ra = x ∧ sig Rb = y := by
  cases R with
  | prod a b => simp only [sig, skel, er, Ty.prod.injEq] at h; exact ⟨a, b, rfl, h.1, h.2⟩
  | refine t ψ => rw [sig_refine] at h; rcases rf_cases (sig t) with e | ⟨u, e⟩ <;> rw [e] at h <;> cases h
  | _ => simp [sig, skel, er] at h

theorem sig_inv_sum {R x y : Ty} (h : sig R = .sum x y) : ∃ Ra Rb, R = .sum Ra Rb ∧ sig Ra = x ∧ sig Rb = y := by
  cases R with
  | sum a b => simp only [sig, skel, er, Ty.sum.injEq] at h; exact ⟨a, b, rfl, h.1, h.2⟩
  | refine t ψ => rw [sig_refine] at h; rcases rf_cases (sig t) with e | ⟨u, e⟩ <;> rw [e] at h <;> cases h
  | _ => simp [sig, skel, er] at h

theorem sig_inv_iall {R x : Ty} (h : sig R = .iall x) : ∃ R', R = .iall R' ∧ sig R' = x := by
  cases R with
  | iall a => simp only [sig, skel, er, Ty.iall.injEq] at h; exact ⟨a, rfl, h⟩
  | refine t ψ => rw [sig_refine] at h; rcases rf_cases (sig t) with e | ⟨u, e⟩ <;> rw [e] at h <;> cases h
  | _ => simp [sig, skel, er] at h

theorem sig_inv_iex {R x : Ty} (h : sig R = .iex x) : ∃ R', R = .iex R' ∧ sig R' = x := by
  cases R with
  | iex a => simp only [sig, skel, er, Ty.iex.injEq] at h; exact ⟨a, rfl, h⟩
  | refine t ψ => rw [sig_refine] at h; rcases rf_cases (sig t) with e | ⟨u, e⟩ <;> rw [e] at h <;> cases h
  | _ => simp [sig, skel, er] at h

theorem sig_inv_mu {R x : Ty} (h : sig R = .mu x) : ∃ R', R = .mu R' ∧ sig R' = x := by
  cases R with
  | mu a => simp only [sig, skel, er, Ty.mu.injEq] at h; exact ⟨a, rfl, h⟩
  | refine t ψ => rw [sig_refine] at h; rcases rf_cases (sig t) with e | ⟨u, e⟩ <;> rw [e] at h <;> cases h
  | _ => simp [sig, skel, er] at h

theorem sig_inv_tex {R x : Ty} {κ : Kind} (h : sig R = .tex κ x) : ∃ R', R = .tex κ R' ∧ sig R' = x := by
  cases R with
  | tex κ' a => simp only [sig, skel, er, Ty.tex.injEq] at h; obtain ⟨rfl, h⟩ := h; exact ⟨a, rfl, h⟩
  | refine t ψ => rw [sig_refine] at h; rcases rf_cases (sig t) with e | ⟨u, e⟩ <;> rw [e] at h <;> cases h
  | _ => simp [sig, skel, er] at h

theorem sig_inv_refine {R x : Ty} {ψ : Pred} (h : sig R = .refine x ψ) : ∃ R' ψ', R = .refine R' ψ' ∧ sig R' = x := by
  cases R with
  | refine t ψ' => rw [sig_refine] at h; exact ⟨t, ψ', rfl, (rf_eq_refine h).symm⟩
  | _ => simp [sig, skel, er] at h

/-- Off the structural heads, a non-shallow-pub runtime type counts nothing. -/
theorem pubWords_nonstruct {R : Ty} (hs : sNo R = false) (hn : IsStruct (sig R) = false) (ws : List Word) :
    pubWords R ws = [] := by
  cases R with
  | prod a b => simp [sig, skel, er, IsStruct] at hn
  | sum a b => simp [sig, skel, er, IsStruct] at hn
  | iall a => simp [sig, skel, er, IsStruct] at hn
  | iex a => simp [sig, skel, er, IsStruct] at hn
  | mu a => simp [sig, skel, er, IsStruct] at hn
  | tex κ a => simp [sig, skel, er, IsStruct] at hn
  | refine t ψ =>
      rw [sig_refine] at hn
      rcases rf_cases (sig t) with e | ⟨u, e⟩
      · have : sig t = .int := by cases ht : sig t <;> simp_all [rf]
        have h1 : sNo t = true := by rw [← sNo_sig, this]; rfl
        simp only [sNo] at hs; rw [h1] at hs; cases hs
      · rw [e] at hn; simp [IsStruct] at hn
  | _ =>
      rw [pubWords.eq_def]; simp only []
      split
      · rename_i h; rw [hs] at h; cases h
      · rfl

/-- `labsIn_VR` at a shallow-pub type: every `loc` word names a cell with a frontier or a box
(`VR` at a `pub` reference reads `η.pfr`, `ModeOK`). -/
theorem labsIn_VR_sNo {G : AllocLabel → Prop} : ∀ (T : Ty) (ρ : Nat → Nat) (η : TEnv) (R : Ty) (ws : List Word),
    (∀ k r vs, ¬ η.rels k r vs) → (∀ l f, η.pfr l = some f → G l) → (∀ l B, η.box l = some B → G l) →
    shp R = shp T → sNo T = true → wc R = some ws.length → Valid R ws → VR ρ η T (shp R) ws → LabsIn G ws := by
  intro T
  induction T with
  | prod a b iha ihb =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv
    simp only [sNo, Bool.and_eq_true] at hsn
    obtain ⟨R0, e1, e2, e3, n1, n2, n3⟩ := unwrapR R ws
    have hval0 := e3 hval
    rw [hshp] at e1 hv
    rw [← e2] at hwc
    obtain ⟨ra, rb, hr, hv⟩ := hv
    simp only [shp, Shp.prod.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    cases R0 with
    | prod Ra Rb =>
      simp only [shp, Shp.prod.injEq] at e1
      obtain ⟨ea, eb⟩ := e1
      rw [wc_prod] at hwc
      cases ha : wc Ra with
      | none => simp [ha] at hwc
      | some na =>
        cases hb : wc Rb with
        | none => simp [ha, hb] at hwc
        | some nb =>
          simp [ha, hb] at hwc
          obtain ⟨hle, hva, hvb⟩ := hv na (by rw [← ea, shp_wc]; exact ha)
          obtain ⟨Va, Vb⟩ := hval0 na ha
          intro w hw
          rw [← List.take_append_drop na ws] at hw
          rcases List.mem_append.1 hw with h | h
          · exact iha ρ η Ra _ hrel hS hB ea hsn.1 (by rw [ha, List.length_take]; congr 1; omega) Va
              (by rw [ea]; exact hva) w h
          · exact ihb ρ η Rb _ hrel hS hB eb hsn.2 (by rw [hb, List.length_drop]; congr 1; omega) Vb
              (by rw [eb]; exact hvb) w h
    | refine t ψ => exact absurd rfl (n1 t ψ)
    | mu t => exact absurd rfl (n2 t)
    | iall t => exact absurd rfl (n3 t)
    | _ => simp [shp] at e1
  | sum a b iha ihb =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv
    simp only [sNo, Bool.and_eq_true] at hsn
    obtain ⟨R0, e1, e2, e3, n1, n2, n3⟩ := unwrapR R ws
    have hval0 := e3 hval
    rw [hshp] at e1 hv
    rw [← e2] at hwc
    obtain ⟨n, Ra, Rb, hr, hcase⟩ := hv
    simp only [shp, lnorm, Shp.sum.injEq, Ty.sum.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    cases R0 with
    | sum A B =>
      simp only [shp, lnorm, Shp.sum.injEq, Ty.sum.injEq] at e1
      obtain ⟨-, eA, eB⟩ := e1
      rw [← eA, ← eB] at hcase
      have hsA : shp A = shp a := by rw [← shp_lnorm A, eA, shp_lnorm]
      have hsB : shp B = shp b := by rw [← shp_lnorm B, eB, shp_lnorm]
      have hlenA : (armsOf (lnorm A)).length = (armsOf A).length := by
        rw [armsOf_lnorm, List.length_map]
      have htl : (Ty.sum (lnorm A) (lnorm B)).tier = (Ty.sum A B).tier := tier_lnorm (.sum A B)
      intro w hw y g hx
      rcases hcase with ⟨-, x, s, Bx, hvals, -, hbox, -⟩ | ⟨j, p, hd, hA, hB2⟩
      · have hm := locPub_mem_val hvals hw
        rw [hx] at hm
        simp at hm
        obtain ⟨rfl, -⟩ := hm
        exact hB _ _ hbox
      · rcases hval0 with htb | ⟨j', p', arm, hd', -, -, ⟨q0, he, hveq⟩, hA', hB'⟩
        · rw [htl, htb] at hd; simp [decodeArm] at hd
        · have hd2 := decodeArm_mono (arms_lnorm (.sum A B)) hd'
          rw [htl] at hd
          have hjp : (j, p) = (j', p') := Option.some.inj (hd.symm.trans hd2)
          simp only [Prod.mk.injEq] at hjp
          obtain ⟨rfl, rfl⟩ := hjp
          have hm : w.val ∈ q0.map (·.val) := hveq ▸ List.mem_map_of_mem hw
          obtain ⟨w0, hw0, hv0⟩ := List.mem_map.1 hm
          obtain ⟨w1, hw1, g1, hv1⟩ := locPub_encFwd he w0 hw0 y g (hv0.trans hx)
          by_cases hj : j < (armsOf A).length
          · obtain ⟨q, hq, hvq⟩ := hA (by rw [hlenA]; exact hj)
            obtain ⟨q', hq', hsq, hwq, hvalq⟩ := hA' hj
            have hqq : q' = q := Option.some.inj ((ofArm_lnorm hq').symm.trans hq)
            subst hqq
            obtain ⟨w2, hw2, g2, hv2⟩ := locPub_ofArmRev hq' w1 hw1 y g1 hv1
            have hwcq : wc A = some q'.length := by
              cases hu : accs A with
              | none => simp [wc, hu] at hwq
              | some us => simp only [wc, hu, Option.map_some]; rw [hsq us hu]
            rw [shp_lnorm] at hvq
            exact iha ρ η A q' hrel hS hB hsA hsn.1 hwcq hvalq hvq w2 hw2 y g2 hv2
          · have hj2 : (armsOf A).length ≤ j := Nat.le_of_not_lt hj
            obtain ⟨q, hq, hvq⟩ := hB2 (by rw [hlenA]; exact hj2)
            obtain ⟨q', hq', hsq, hwq, hvalq⟩ := hB' hj2
            rw [hlenA] at hq
            have hqq : q' = q := Option.some.inj ((ofArm_lnorm hq').symm.trans hq)
            subst hqq
            obtain ⟨w2, hw2, g2, hv2⟩ := locPub_ofArmRev hq' w1 hw1 y g1 hv1
            have hwcq : wc B = some q'.length := by
              cases hu : accs B with
              | none => simp [wc, hu] at hwq
              | some us => simp only [wc, hu, Option.map_some]; rw [hsq us hu]
            rw [shp_lnorm] at hvq
            exact ihb ρ η B q' hrel hS hB hsB hsn.2 hwcq hvalq hvq w2 hw2 y g2 hv2
    | refine t ψ => exact absurd rfl (n1 t ψ)
    | mu t => exact absurd rfl (n2 t)
    | iall t => exact absurd rfl (n3 t)
    | _ => simp [shp] at e1
  | refine t ψ ih =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv
    exact ih ρ η R ws hrel hS hB hshp hsn hwc hval hv.1
  | iall t ih =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv
    exact ih (vcons 0 ρ) η R ws hrel hS hB hshp hsn hwc hval (hv 0)
  | mu t ih =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv
    exact ih ρ (η.push0 (TermClose.cl ρ η.wit 0 0 (.mu t))) R ws (locPub_push0_rels hrel _) hS hB hshp hsn hwc hval hv
  | iex t ih =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv
    obtain ⟨R0, e1, e2, e3, n1, n2, n3⟩ := unwrapR R ws
    have hval0 := e3 hval
    rw [hshp] at e1 hv
    rw [← e2] at hwc
    obtain ⟨n, rb, w, hr, hv⟩ := hv
    simp only [shp, Shp.iex.injEq] at hr
    obtain ⟨-, rfl⟩ := hr
    cases R0 with
    | iex Rb =>
      simp only [shp, Shp.iex.injEq] at e1
      rw [wc_iex] at hwc
      exact ih (vcons w ρ) η Rb ws hrel hS hB e1.2 hsn hwc hval0 (by rw [e1.2]; exact hv)
    | refine t ψ => exact absurd rfl (n1 t ψ)
    | mu t => exact absurd rfl (n2 t)
    | iall t => exact absurd rfl (n3 t)
    | _ => simp [shp] at e1
  | tex κ t ih =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv
    simp only [sNo, Bool.and_eq_true] at hsn
    obtain ⟨R0, e1, e2, e3, n1, n2, n3⟩ := unwrapR R ws
    have hval0 := e3 hval
    rw [hshp] at e1 hv
    rw [← e2] at hwc
    obtain ⟨n, rb, s, hr, -, -, hv⟩ := hv
    simp only [shp, Shp.tex.injEq] at hr
    obtain ⟨-, rfl⟩ := hr
    cases R0 with
    | tex κ' Rb =>
      simp only [shp, Shp.tex.injEq] at e1
      rw [wc_tex] at hwc
      exact ih ρ (η.push0 s) Rb ws (locPub_push0_rels hrel s) hS hB e1.2 hsn.2 hwc hval0 (by rw [e1.2]; exact hv)
    | refine t ψ => exact absurd rfl (n1 t ψ)
    | mu t => exact absurd rfl (n2 t)
    | iall t => exact absurd rfl (n3 t)
    | _ => simp [shp] at e1
  | tvar k =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv
    obtain ⟨ws', -, hg⟩ := hv
    exact absurd hg (hrel _ _ _)
  | ptr μ u =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv w hw x g hx
    cases μ with
    | pub =>
      obtain ⟨a, c, h1, -, -, -, ⟨f, hf, -⟩, -⟩ := hv
      have hm := locPub_mem_val h1 hw
      rw [hx] at hm; simp at hm; obtain ⟨rfl, -⟩ := hm
      exact hS _ _ hf
    | _ => simp [sNo, mPub] at hsn
  | ptrOpt μ u =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv w hw x g hx
    cases μ with
    | pub =>
      rcases hv with h0 | ⟨a, c, h1, -, -, -, ⟨f, hf, -⟩, -⟩
      · have hm := locPub_mem_val h0 hw
        rw [hx] at hm; simp at hm
      · have hm := locPub_mem_val h1 hw
        rw [hx] at hm; simp at hm; obtain ⟨rfl, -⟩ := hm
        exact hS _ _ hf
    | _ => simp [sNo, mPub] at hsn
  | loc μ u =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv w hw x g hx
    cases μ with
    | pub =>
      rcases hv with ⟨h0, -⟩ | ⟨a, c, U, h1, -, -, -, ⟨f, hf, -⟩, -⟩
      · have hm := locPub_mem_val h0 hw
        rw [hx] at hm; simp at hm
      · have hm := locPub_mem_val h1 hw
        rw [hx] at hm; simp at hm; obtain ⟨rfl, -⟩ := hm
        exact hS _ _ hf
    | _ => simp [sNo, mPub] at hsn
  | void =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv
    simp [VR] at hv
  | intS i =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv w hw x g hx
    have hm := locPub_mem_val hv hw
    rw [hx] at hm; simp at hm
  | int =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv w hw x g hx
    obtain ⟨n, hn⟩ := hv
    have hm := locPub_mem_val hn hw
    rw [hx] at hm; simp at hm
  | tid =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv w hw x g hx
    obtain ⟨n, c, hn, -, -, f, hf, -⟩ := hv
    have hm := locPub_mem_val hn hw
    rw [hx] at hm; simp at hm; obtain ⟨rfl, -⟩ := hm
    exact hS _ _ hf
  | fix sg wd =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv w hw x g hx
    obtain ⟨-, n, hn, -⟩ := hv
    have hm := locPub_mem_val hn hw
    rw [hx] at hm; simp at hm
  | lanes sg wd =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv w hw x g hx
    obtain ⟨-, n, hn⟩ := hv
    have hm := locPub_mem_val hn hw
    rw [hx] at hm; simp at hm
  | code a b _ _ =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv w hw x g hx
    obtain ⟨i, d, hn, -⟩ := hv
    have hm := locPub_mem_val hn hw
    rw [hx] at hm; simp at hm
  | word r P =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv w hw x g hx
    have hlen : wc (.word r P) = some ws.length := by rw [← shp_wc, ← hshp, shp_wc]; exact hwc
    cases hg : P.ghost with
    | true =>
      simp [wc, accs, hg, nWords] at hlen
      rw [List.eq_nil_of_length_eq_zero hlen.symm] at hw; simp at hw
    | false =>
      obtain ⟨n, hn, -⟩ := hv.2 hg
      have hm := locPub_mem_val hn hw
      rw [hx] at hm; simp at hm
  | word2 r P =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv w hw x g hx
    obtain ⟨-, n0, n1, hn, -⟩ := hv
    have hm := locPub_mem_val hn hw
    rw [hx] at hm; simp at hm
  | epair r P =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv w hw x g hx
    obtain ⟨-, n0, n1, hn⟩ := hv
    have hm := locPub_mem_val hn hw
    rw [hx] at hm; simp at hm
  | array i t _ =>
    intro ρ η R ws hrel hS hB hshp hsn hwc
    have hlen : wc (.array i t) = some ws.length := by rw [← shp_wc, ← hshp, shp_wc]; exact hwc
    simp [wc, accs] at hlen
  | unit | share _ | cap _ _ | tok _ _ | tok2 _ _ _ _ | tokE _ _ _ =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv w hw
    have hlen := hwc
    rw [← shp_wc, hshp, shp_wc] at hlen
    simp [wc, accs, nWords] at hlen
    rw [List.eq_nil_of_length_eq_zero hlen.symm] at hw; simp at hw



theorem labsIn_veq {G : AllocLabel → Prop} {ws ws' : List Word} (h : LabsIn G ws) (e : VEq ws ws') : LabsIn G ws' := by
  intro w' hw' a g hv
  have hm : w'.val ∈ ws.map (·.val) := by rw [e]; exact List.mem_map_of_mem hw'
  obtain ⟨w, hw, hwv⟩ := List.mem_map.1 hm
  exact h w hw a g (hwv.trans hv)

theorem veq_take {ws ws' : List Word} (e : VEq ws ws') (n : Nat) : VEq (ws.take n) (ws'.take n) := by
  simp only [VEq, List.map_take]; rw [e]

theorem veq_drop {ws ws' : List Word} (e : VEq ws ws') (n : Nat) : VEq (ws.drop n) (ws'.drop n) := by
  simp only [VEq, List.map_drop]; rw [e]

theorem veq_append {a b a' b' : List Word} (h1 : VEq a a') (h2 : VEq b b') : VEq (a ++ b) (a' ++ b') := by
  simp only [VEq, List.map_append]; rw [h1, h2]

/-- The counted words read only values. -/
theorem pubWords_veq : ∀ (R : Ty),
    (∀ ws ws', VEq ws ws' → VEq (pubWords R ws) (pubWords R ws')) ∧
    (∀ j p p', VEq p p' → VEq (pubArm R j p) (pubArm R j p')) := by
  intro R
  induction R with
  | prod a b iha ihb =>
      have h1 : ∀ ws ws', VEq ws ws' → VEq (pubWords (.prod a b) ws) (pubWords (.prod a b) ws') := by
        intro ws ws' e
        by_cases hs : sNo (.prod a b) = true
        · rw [pubWords_of_sNo hs, pubWords_of_sNo hs]; exact e
        · simp only [pubWords, hs, Bool.false_eq_true, ite_false]
          split
          · exact veq_append (iha.1 _ _ (veq_take e _)) (ihb.1 _ _ (veq_drop e _))
          · rfl
      exact ⟨h1, fun j p p' e => by simp only [pubArm]; exact h1 p p' e⟩
  | sum a b iha ihb =>
      have h2 : ∀ j p p', VEq p p' → VEq (pubArm (.sum a b) j p) (pubArm (.sum a b) j p') := by
        intro j p p' e
        simp only [pubArm]
        split
        · exact iha.2 _ _ _ e
        · exact ihb.2 _ _ _ e
      refine ⟨fun ws ws' e => ?_, h2⟩
      by_cases hs : sNo (.sum a b) = true
      · rw [pubWords_of_sNo hs, pubWords_of_sNo hs]; exact e
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]
        split
        · exact e
        · cases hd : decodeArm (Ty.sum a b).tier (armsOf (lnorm (.sum a b))) ws with
          | none =>
            cases hd' : decodeArm (Ty.sum a b).tier (armsOf (lnorm (.sum a b))) ws' with
            | none => rfl
            | some x =>
              obtain ⟨j, p⟩ := x
              obtain ⟨p', hp', -⟩ := decodeArm_vals e.symm hd'
              rw [hd] at hp'; cases hp'
          | some x =>
            obtain ⟨j, p⟩ := x
            obtain ⟨p', hp', ep⟩ := decodeArm_vals e hd
            simp only [hp']
            split
            · exact iha.2 _ _ _ ep
            · exact ihb.2 _ _ _ ep
  | refine t ψ ih =>
      exact ⟨fun ws ws' e => by rw [pubWords_refine, pubWords_refine]; exact ih.1 _ _ e,
        fun j p p' e => by simp only [pubArm]; exact ih.2 _ _ _ e⟩
  | iall t ih =>
      refine ⟨fun ws ws' e => ?_, fun j p p' e => by simp only [pubArm]; exact ih.2 _ _ _ e⟩
      by_cases hs : sNo (.iall t) = true
      · rw [pubWords_of_sNo hs, pubWords_of_sNo hs]; exact e
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 _ _ e
  | iex t ih =>
      refine ⟨fun ws ws' e => ?_, fun j p p' e => by simp only [pubArm]; exact ih.2 _ _ _ e⟩
      by_cases hs : sNo (.iex t) = true
      · rw [pubWords_of_sNo hs, pubWords_of_sNo hs]; exact e
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 _ _ e
  | mu t ih =>
      refine ⟨fun ws ws' e => ?_, fun j p p' e => by simp only [pubArm]; exact ih.2 _ _ _ e⟩
      by_cases hs : sNo (.mu t) = true
      · rw [pubWords_of_sNo hs, pubWords_of_sNo hs]; exact e
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 _ _ e
  | tex κ t ih =>
      refine ⟨fun ws ws' e => ?_, fun j p p' e => by simp only [pubArm]; exact ih.2 _ _ _ e⟩
      by_cases hs : sNo (.tex κ t) = true
      · rw [pubWords_of_sNo hs, pubWords_of_sNo hs]; exact e
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 _ _ e
  | _ =>
      refine ⟨fun ws ws' e => ?_, fun j p p' e => ?_⟩
      · rw [pubWords.eq_def, pubWords.eq_def]; simp only []
        split
        · exact e
        · rfl
      · simp only [pubArm]; rw [pubWords.eq_def, pubWords.eq_def]; simp only []
        split
        · exact e
        · rfl

/-- Through a shallow-pub type: the payload's labels are the value's (`locPub_ofArmRev`). -/
theorem labsIn_pubArm_sNo {G : AllocLabel → Prop} {A : Ty} {j : Nat} {p q : List Word} (h : ofArm A j p = some q)
    (hs : sNo A = true) (hl : LabsIn G (pubWords A q)) : LabsIn G (pubArm A j p) := by
  rw [pubWords_of_sNo hs] at hl
  refine (labsIn_pubWords A).2 j p fun w hw y g hv => ?_
  obtain ⟨w', hw', g', hv'⟩ := locPub_ofArmRev h w hw y g hv
  exact hl w' hw' y g' hv'

theorem ofArm_refine (t : Ty) (ψ : Pred) (j : Nat) (p : List Word) : ofArm (.refine t ψ) j p = ofArm t j p := by
  simp only [ofArm, sumHead, armsOf, tier_refine]
theorem ofArm_iall (t : Ty) (j : Nat) (p : List Word) : ofArm (.iall t) j p = ofArm t j p := by
  simp only [ofArm, sumHead, armsOf, tier_iall]
theorem ofArm_iex (t : Ty) (j : Nat) (p : List Word) : ofArm (.iex t) j p = ofArm t j p := by
  simp only [ofArm, sumHead, armsOf, tier_iex]
theorem ofArm_mu (t : Ty) (j : Nat) (p : List Word) : ofArm (.mu t) j p = ofArm t j p := by
  simp only [ofArm, sumHead, armsOf, tier_mu]
theorem ofArm_tex (κ : Kind) (t : Ty) (j : Nat) (p : List Word) : ofArm (.tex κ t) j p = ofArm t j p := by
  simp only [ofArm, sumHead, armsOf, tier_tex]

/-- **Arm payloads**: what a payload counts at its arm is what its injection counts (decoding an
encoded fitting payload gives back the arm and the payload's values, `roundtrip`). -/
theorem labsIn_pubArm {G : AllocLabel → Prop} : ∀ (A : Ty) (j : Nat) (p q : List Word), ofArm A j p = some q →
    (sumHead A = true → ∃ arm, (armsOf A)[j]? = some arm ∧ PayOK arm p) →
    LabsIn G (pubWords A q) → LabsIn G (pubArm A j p) := by
  intro A
  induction A with
  | sum a b _ _ =>
      intro j p q h hpay hl
      by_cases hs : sNo (.sum a b) = true
      · exact labsIn_pubArm_sNo h hs hl
      · obtain ⟨arm, ha, hp⟩ := hpay rfl
        have he : encodeArm (Ty.sum a b).tier (armsOf (.sum a b)) j p = some q := by
          simpa only [ofArm, sumHead, ite_true] using h
        have ht : (Ty.sum a b).tier ≠ .boxed := fun hb => by rw [hb] at he; simp [encodeArm] at he
        obtain ⟨p', hd, ep⟩ := roundtrip ht ha hp he
        have hd2 := decodeArm_mono (arms_lnorm (.sum a b)) hd
        have hl2 : LabsIn G (pubArm (.sum a b) j p') := by
          have e1 : pubWords (.sum a b) q = pubArm (.sum a b) j p' := by
            simp only [pubWords, hs, Bool.false_eq_true, ite_false, ht, hd2, pubArm]
          rw [← e1]; exact hl
        exact labsIn_veq hl2 ((pubWords_veq _).2 j p' p ep.symm)
  | refine t ψ ih =>
      intro j p q h hpay hl
      rw [ofArm_refine] at h; rw [pubWords_refine] at hl
      simp only [pubArm]; exact ih j p q h hpay hl
  | iall t ih =>
      intro j p q h hpay hl
      by_cases hs : sNo (.iall t) = true
      · exact labsIn_pubArm_sNo h hs hl
      · rw [ofArm_iall] at h; simp only [pubWords, hs, Bool.false_eq_true, ite_false] at hl
        simp only [pubArm]; exact ih j p q h hpay hl
  | iex t ih =>
      intro j p q h hpay hl
      by_cases hs : sNo (.iex t) = true
      · exact labsIn_pubArm_sNo h hs hl
      · rw [ofArm_iex] at h; simp only [pubWords, hs, Bool.false_eq_true, ite_false] at hl
        simp only [pubArm]; exact ih j p q h hpay hl
  | mu t ih =>
      intro j p q h hpay hl
      by_cases hs : sNo (.mu t) = true
      · exact labsIn_pubArm_sNo h hs hl
      · rw [ofArm_mu] at h; simp only [pubWords, hs, Bool.false_eq_true, ite_false] at hl
        simp only [pubArm]; exact ih j p q h hpay hl
  | tex κ t ih =>
      intro j p q h hpay hl
      by_cases hs : sNo (.tex κ t) = true
      · exact labsIn_pubArm_sNo h hs hl
      · rw [ofArm_tex] at h; simp only [pubWords, hs, Bool.false_eq_true, ite_false] at hl
        simp only [pubArm]; exact ih j p q h hpay hl
  | _ =>
      intro j p q h _ hl
      unfold ofArm at h
      simp only [sumHead, Bool.false_eq_true, ite_false] at h
      split at h
      · cases h; simp only [pubArm]; exact hl
      · cases h

/-- The shallow-pub case of `labsIn_pubVR`. -/
theorem labsIn_pub_sNo {G : AllocLabel → Prop} {T : Ty} {ρ : Nat → Nat} {η : TEnv} {R : Ty} {ws : List Word}
    (hrel : ∀ k r vs, ¬ η.rels k r vs) (hP : ∀ l f, η.pfr l = some f → G l) (hB : ∀ l B, η.box l = some B → G l)
    (hsig : sig R = sig T) (hs : sNo R = true) (hwc : wc R = some ws.length) (hval : Valid R ws)
    (hv : VR ρ η T (shp R) ws) : LabsIn G (pubWords R ws) := by
  rw [pubWords_of_sNo hs]
  exact labsIn_VR_sNo T ρ η R ws hrel hP hB (shp_of_sig hsig) (by rw [← sNo_sig T, ← hsig, sNo_sig]; exact hs)
    hwc hval hv

/-- **EnvPub names**: in an env with no type-variable values, the counted words of a
value of `T` held at a runtime type `R` of `T`'s signature (valid, of its word count) name only cells
with a frontier or boxes: a counted reference is `pub` (`ModeOK` reads `η.pfr`), a boxed sum reads
`η.box`; `own`/region references are not counted. -/
theorem labsIn_pubVR {G : AllocLabel → Prop} : ∀ (T : Ty) (ρ : Nat → Nat) (η : TEnv) (R : Ty) (ws : List Word),
    (∀ k r vs, ¬ η.rels k r vs) → (∀ l f, η.pfr l = some f → G l) → (∀ l B, η.box l = some B → G l) →
    sig R = sig T → wc R = some ws.length → Valid R ws → VR ρ η T (shp R) ws → LabsIn G (pubWords R ws) := by
  intro T
  induction T with
  | prod a b iha ihb =>
    intro ρ η R ws hrel hP hB hsig hwc hval hv
    by_cases hs : sNo R = true
    · exact labsIn_pub_sNo hrel hP hB hsig hs hwc hval hv
    have hs' : sNo R = false := by simpa using hs
    obtain ⟨Ra, Rb, rfl, ha, hb⟩ := sig_inv_prod hsig
    obtain ⟨ra, rb, hr, hv⟩ := hv
    simp only [shp, Shp.prod.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    rw [wc_prod] at hwc
    cases hwa : wc Ra with
    | none => simp [hwa] at hwc
    | some na =>
      cases hwb : wc Rb with
      | none => simp [hwa, hwb] at hwc
      | some nb =>
        simp [hwa, hwb] at hwc
        obtain ⟨hle, hva, hvb⟩ := hv na (by rw [shp_wc]; exact hwa)
        obtain ⟨Va, Vb⟩ := hval na hwa
        simp only [pubWords, hs', Bool.false_eq_true, ite_false, hwa]
        intro w hw
        rcases List.mem_append.1 hw with h | h
        · exact iha ρ η Ra _ hrel hP hB ha (by rw [hwa, List.length_take]; congr 1; omega) Va hva w h
        · exact ihb ρ η Rb _ hrel hP hB hb (by rw [hwb, List.length_drop]; congr 1; omega) Vb hvb w h
  | sum a b iha ihb =>
    intro ρ η R ws hrel hP hB hsig hwc hval hv
    by_cases hs : sNo R = true
    · exact labsIn_pub_sNo hrel hP hB hsig hs hwc hval hv
    have hs' : sNo R = false := by simpa using hs
    obtain ⟨A, B, rfl, hA, hB'⟩ := sig_inv_sum hsig
    obtain ⟨n, Ra, Rb, hr, hcase⟩ := hv
    simp only [shp, lnorm, Shp.sum.injEq, Ty.sum.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    have htl : (Ty.sum (lnorm A) (lnorm B)).tier = (Ty.sum A B).tier := tier_lnorm (.sum A B)
    have hlenA : (armsOf (lnorm A)).length = (armsOf A).length := by rw [armsOf_lnorm, List.length_map]
    by_cases hbx : (Ty.sum A B).tier = .boxed
    · simp only [pubWords, hs', Bool.false_eq_true, ite_false, hbx, ite_true]
      rcases hcase with ⟨-, x, s, Bx, hvals, -, hbox, -⟩ | ⟨j, p, hd, -, -⟩
      · intro w hw y g hx
        have hm := locPub_mem_val hvals hw
        rw [hx] at hm; simp at hm; obtain ⟨rfl, -⟩ := hm
        exact hB _ _ hbox
      · rw [htl, hbx] at hd; simp [decodeArm] at hd
    · rcases hcase with ⟨htb, -⟩ | ⟨j, p, hd, hA2, hB2⟩
      · rw [htl] at htb; exact absurd htb hbx
      rcases hval with htb | ⟨j', p', arm, hd', harm, hpay, -, hA', hB''⟩
      · exact absurd htb hbx
      have hd2 := decodeArm_mono (arms_lnorm (.sum A B)) hd'
      rw [htl] at hd
      have hjp : (j, p) = (j', p') := Option.some.inj (hd.symm.trans hd2)
      simp only [Prod.mk.injEq] at hjp
      obtain ⟨rfl, rfl⟩ := hjp
      have hd3 : decodeArm (Ty.sum A B).tier (armsOf (lnorm (.sum A B))) ws = some (j, p) := hd2
      simp only [pubWords, hs', Bool.false_eq_true, ite_false, hbx, hd3]
      by_cases hj : j < (armsOf A).length
      · simp only [hj, ite_true]
        obtain ⟨q, hq, hvq⟩ := hA2 (by rw [hlenA]; exact hj)
        obtain ⟨q', hq', hsq, hwq, hvalq⟩ := hA' hj
        have hqq : q' = q := Option.some.inj ((ofArm_lnorm hq').symm.trans hq)
        subst hqq
        have hwcq : wc A = some q'.length := by
          cases hu : accs A with
          | none => simp [wc, hu] at hwq
          | some us => simp only [wc, hu, Option.map_some]; rw [hsq us hu]
        rw [shp_lnorm] at hvq
        have hl := iha ρ η A q' hrel hP hB hA hwcq hvalq hvq
        refine labsIn_pubArm A j p q' hq' (fun _ => ⟨arm, ?_, hpay⟩) hl
        rw [← List.getElem?_append_left hj]; exact harm
      · simp only [hj, ite_false]
        have hj2 : (armsOf A).length ≤ j := Nat.le_of_not_lt hj
        obtain ⟨q, hq, hvq⟩ := hB2 (by rw [hlenA]; exact hj2)
        obtain ⟨q', hq', hsq, hwq, hvalq⟩ := hB'' hj2
        rw [hlenA] at hq
        have hqq : q' = q := Option.some.inj ((ofArm_lnorm hq').symm.trans hq)
        subst hqq
        have hwcq : wc B = some q'.length := by
          cases hu : accs B with
          | none => simp [wc, hu] at hwq
          | some us => simp only [wc, hu, Option.map_some]; rw [hsq us hu]
        rw [shp_lnorm] at hvq
        have hl := ihb ρ η B q' hrel hP hB hB' hwcq hvalq hvq
        refine labsIn_pubArm B _ p q' hq' (fun _ => ⟨arm, ?_, hpay⟩) hl
        rw [← List.getElem?_append_right hj2]; exact harm
  | refine t ψ ih =>
    intro ρ η R ws hrel hP hB hsig hwc hval hv
    by_cases hs : sNo R = true
    · exact labsIn_pub_sNo hrel hP hB hsig hs hwc hval hv
    rw [sig_refine] at hsig
    rcases rf_cases (sig t) with e | ⟨u, e⟩
    · exfalso; apply hs
      have h1 : sig t = .int := by cases ht : sig t <;> simp_all [rf]
      rw [← sNo_sig, hsig, e]; rfl
    · rw [e] at hsig
      have hu : u = sig t := rf_eq_refine e
      subst hu
      obtain ⟨R', ψ', rfl, hR'⟩ := sig_inv_refine hsig
      rw [pubWords_refine]
      exact ih ρ η R' ws hrel hP hB hR' (by rw [← hwc]; simp only [wc, accs]) hval hv.1
  | iall t ih =>
    intro ρ η R ws hrel hP hB hsig hwc hval hv
    by_cases hs : sNo R = true
    · exact labsIn_pub_sNo hrel hP hB hsig hs hwc hval hv
    have hs' : sNo R = false := by simpa using hs
    obtain ⟨R', rfl, hR'⟩ := sig_inv_iall hsig
    simp only [pubWords, hs', Bool.false_eq_true, ite_false]
    exact ih (vcons 0 ρ) η R' ws hrel hP hB hR' (by rw [← hwc]; simp only [wc, accs]) hval (hv 0)
  | iex t ih =>
    intro ρ η R ws hrel hP hB hsig hwc hval hv
    by_cases hs : sNo R = true
    · exact labsIn_pub_sNo hrel hP hB hsig hs hwc hval hv
    have hs' : sNo R = false := by simpa using hs
    obtain ⟨R', rfl, hR'⟩ := sig_inv_iex hsig
    obtain ⟨n, rb, w, hr, hv⟩ := hv
    simp only [shp, Shp.iex.injEq] at hr
    obtain ⟨-, rfl⟩ := hr
    simp only [pubWords, hs', Bool.false_eq_true, ite_false]
    rw [wc_iex] at hwc
    exact ih (vcons w ρ) η R' ws hrel hP hB hR' hwc hval hv
  | mu t ih =>
    intro ρ η R ws hrel hP hB hsig hwc hval hv
    by_cases hs : sNo R = true
    · exact labsIn_pub_sNo hrel hP hB hsig hs hwc hval hv
    have hs' : sNo R = false := by simpa using hs
    obtain ⟨R', rfl, hR'⟩ := sig_inv_mu hsig
    simp only [pubWords, hs', Bool.false_eq_true, ite_false]
    exact ih ρ _ R' ws (locPub_push0_rels hrel _) hP hB hR' (by rw [← hwc]; simp only [wc, accs]) hval hv
  | tex κ t ih =>
    intro ρ η R ws hrel hP hB hsig hwc hval hv
    by_cases hs : sNo R = true
    · exact labsIn_pub_sNo hrel hP hB hsig hs hwc hval hv
    have hs' : sNo R = false := by simpa using hs
    obtain ⟨R', rfl, hR'⟩ := sig_inv_tex hsig
    obtain ⟨n, rb, s, hr, -, -, hv⟩ := hv
    simp only [shp, Shp.tex.injEq] at hr
    obtain ⟨-, rfl⟩ := hr
    simp only [pubWords, hs', Bool.false_eq_true, ite_false]
    rw [wc_tex] at hwc
    exact ih ρ (η.push0 s) R' ws (locPub_push0_rels hrel s) hP hB hR' hwc hval hv
  | _ =>
    intro ρ η R ws hrel hP hB hsig hwc hval hv
    by_cases hs : sNo R = true
    · exact labsIn_pub_sNo hrel hP hB hsig hs hwc hval hv
    have hs' : sNo R = false := by simpa using hs
    rw [pubWords_nonstruct hs' (by rw [hsig]; rfl)]
    intro w hw; cases hw

/-! ## (EnvPub) A typed binding extends `EnvLbl` -/

/-- A typed binding extends `EnvLbl` (the frontiers and boxes of `η` within `Eg`'s): the value is
read at the closure `cl ρ η.wit 0 0 t` (`VR_close`), of `rt`'s signature (`Lay`'s skeleton equation
and `hsig`), and `labsIn_pubVR` names only `pfr`/`box` labels. -/
theorem envLbl_cons_VR {Eg : GEnv} {env : Env} {x : String} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {t rt : Ty} {ws : List Word} (h : EnvLbl Eg env) (hc : Coh η)
    (hP : ∀ l f, η.pfr l = some f → Eg.pfr l ≠ none) (hB : ∀ l B, η.box l = some B → Eg.box l ≠ none)
    (hsig : sig (close σs t) = sig (TermClose.cl ρ η.wit 0 0 t)) (hv : VR ρ η t (shp rt) ws)
    (hL : Lay σs t rt ws) : EnvLbl Eg ((x, rt, ws) :: env) := by
  have hv' : VR ρ (CE η) (TermClose.cl ρ η.wit 0 0 t) (shp rt) ws :=
    (VR_close hc ρ t [] 0 ρ ρ (shp rt) ws (fun _ => rfl) (fun _ h => absurd h (Nat.not_lt_zero _))).1 hv
  have hsg : sig rt = sig (TermClose.cl ρ η.wit 0 0 t) := (sig_of_eskel hL.2.1).trans hsig
  have hwc : wc rt = some ws.length := by
    have h1 := hL.2.2.1
    cases hu : accs rt with
    | none => simp [wc, hu] at h1
    | some us => simp only [wc, hu, Option.map_some]; rw [hL.1 us hu]
  have hl := labsIn_pubVR (G := fun l => Eg.pfr l ≠ none ∨ Eg.box l ≠ none)
    (TermClose.cl ρ η.wit 0 0 t) ρ (CE η) rt ws (fun _ _ _ h => h)
    (fun l f h => Or.inl (hP l f h)) (fun l B h => Or.inr (hB l B h)) hsg hwc hL.2.2.2.1 hv'
  refine envLbl_cons h (fun w hw l hn => ?_)
  obtain ⟨a, g, hva, rfl⟩ := hn
  exact hl w hw a g hva

/-! ## (M) at unplanted labels: non-promise edges name planted/published cells or boxes -/

/-- `MemOKP` types every non-promise message: one at a noOwn, rgnFree cell naming a label names a
planted/published cell or a box (`wordOK_locPub`). -/
theorem names_of_memOKP {η : TEnv} {mem : Memory} {pairs P : List Ts} {u : Ts} {m : Msg} {cl : Cell}
    {a : Address} {g : Nat} (hm : MemOKP η mem pairs P) (hu : u ∉ P) (hmu : mem[u]? = some m)
    (hc : η.sto m.loc.label = some cl) (hno : Ty.noOwnIn [] cl.ty = true) (hrf : rgnFree cl.ty = true)
    (hv : m.val = .loc a g) : η.pfr a.label ≠ none ∨ η.box a.label ≠ none := by
  rcases hm.1 u m cl hu hmu hc with h | h
  · rw [hv] at h; cases h
  · rcases wordOK_locPub h hno hrf (show (mw m).val = .loc a g from hv) with ⟨_, f, -, hf⟩ | ⟨B, hB⟩
    · left; rw [hf]; exact fun h => by cases h
    · right; rw [hB]; exact fun h => by cases h

/-- The cut form: a plant edge (at `Eg.sto`) carried by a message that is no promise of a thread
whose cut holds the cell names a planted/published label or a box. -/
theorem plantEdge_lbl_of_thSys {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {Eg : GEnv}
    {Tot HP HS : Res} {cr db : Ts → Res} {u : Ts} {m : Msg} {L : AllocLabel}
    (hT : TermSys.ThSys p g mem pairs th Eg Tot HP HS cr db) (hu : u ∉ th.promises) (hmu : mem[u]? = some m)
    (hE : PlantEdge Eg.sto m L)
    (hin : ∀ ca, Eg.sto m.loc.label = some ca → ca.owner = some g.i ∨ Eg.Shared m.loc.label) :
    Eg.pfr L ≠ none ∨ Eg.box L ≠ none := by
  obtain ⟨S, -, -, hm, -⟩ := hT
  obtain ⟨⟨ca, hca, hno, hrf⟩, a, gg, hv, rfl⟩ := hE
  have hc : (Cut Eg g.i S).sto m.loc.label = some ca := by
    rw [Cut_sto]; exact cutSto_some.2 ⟨hca, hin ca hca⟩
  exact names_of_memOKP hm.1 hu hmu hc hno hrf hv

/-- **NewPfr at a thread step** (route B's `PfrG` at `pf := PubAt th`): a cell of `Eg` whose
frontier the step of `g.i` sets from none is the label of the step's `publish`.  Other owners' cells keep
their frontiers (`GFoot`); `g.i`'s are in its cut, where `PfrG` (`hpf`) applies.
Every thread step, the RMW ops (`xchg`/`cas`/`fetch`) included, is covered by the footprint theorem
(`TermPlant.tstepMCF_stepTKA_zf` at `pf := PubAt th`, whence `hFp.pfrG` in `sysInv_thread`), not by
any probe: the only frontier-changing `EFoot` constructors of thread steps are `EFoot_pub` (the
published label) and `EFoot_seeBox` (a fresh box label, outside Σ). -/
theorem pfrNew_pub {g : G} {Eg Eg' : GEnv} {n n' : Nat} {v : Ts} {E' : TEnv} {S : AllocLabel → Prop}
    {th : TTh} (hG : GFoot g Eg Eg' n n' v) (hpe : ∀ l, Eg'.pfr l = E'.pfr l)
    (hpf : ∀ l, (Cut Eg g.i S).sto l ≠ none → E'.pfr l ≠ (Cut Eg g.i S).pfr l → TermOwnG0Defs.PubAt th l)
    {l : AllocLabel} {cl : Cell} (hs : Eg.sto l = some cl) (hn : Eg.pfr l = none) (h' : Eg'.pfr l ≠ none) :
    TermOwnG0Defs.PubAt th l := by
  rcases hG.2.2.2.2.1 l with e | ⟨-, f, -, -, ⟨c, hc, ho⟩⟩ | ⟨-, -, hs'⟩
  · exact absurd (e.trans hn) h'
  · rw [hs] at hc; cases hc
    refine hpf l (by rw [Cut_sto, cutSto_some.2 ⟨hs, Or.inl ho⟩]; exact fun h => by cases h) ?_
    rw [Cut_pfr, hn, ← hpe]; exact h'
  · have := (hG.2.1 l)
    rcases this with e | ⟨-, e, -⟩
    · rw [e, hs] at hs'; cases hs'
    · rw [hs] at e; cases e

end TermPtrRts
