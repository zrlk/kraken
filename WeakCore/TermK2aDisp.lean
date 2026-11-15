import WeakCore.TermK2aMain
import WeakCore.TermK2aLdW
import WeakCore.TermK2aRmw
import WeakCore.TermK2aSum
import WeakCore.TermK2aLink
import WeakCore.TermLocal

/-!
# TermK2aDisp: the K-2a dispatch

Every in-scope thread step other than `ret` meets the step contract `StepOK` (`stepOK_disp`),
by cases on the typing derivation, in the shape of `TermStep.tstepMF_step`.  Pure, store and
allocation ops go through `A2`'s `valB_*` at the empty store typing (`stepOK_op`); loads and
read-modify-writes through the per-op load contracts; sums, `publish` and regions through
`TermK2aSum`.
-/

namespace TermK2aDisp

open CoreLang CoreTerm CoreTyping TermRun TermTv TermSound TermMem TermStep TermCert TermGlob TermTyped
open TermPtrRts TermOwnG0Defs TermK2a TermK2aLd TermK2aMain
open TermCut (GEnv)
open TermClose (cl tb arrFree_cl)
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- A tested package's slot type: a published reference, alone or last in a pair. -/
theorem slotOK_shape {b : Ty} (h : slotOK b = true) :
    b = .ptr .pub (.tvar 0) ∨ ∃ V, b = .prod V (.ptr .pub (.tvar 0)) := by
  unfold slotOK at h
  split at h <;> simp_all

/-- The last word of a package with a slot is one of its published words. -/
theorem slot_mem_pubWords {σs : List Ty} {κ : Kind} {b rt : Ty} {ws : List Word} {pw : Word}
    (hs : slotOK b = true) (hl : Lay σs (.tex κ b) rt ws) (hlast : ws.getLast? = some pw) :
    pw ∈ pubWords rt ws := by
  have hmem : pw ∈ ws := List.mem_of_getLast? hlast
  rw [pubWords_Lay hl]
  have hwc : wc rt = wc (close σs (.tex κ b)) := by
    have h := hl.2.1
    have := congrArg wc h
    rwa [wc_etok, wc_etok, wc_skel, wc_skel] at this
  rcases slotOK_shape hs with rfl | ⟨V, rfl⟩
  · simp [close, substTs, pubWords, sNo, mPub]
    exact hmem
  · simp [close, substTs, pubWords, sNo, mPub]
    have hw1 : wc (Ty.ptr Mode.pub (Ty.tvar 0)) = some 1 := by first | rfl | decide | simp [wc, accs, nWords, Acc.size]
    have hrt : wc rt = (do pure ((← wc (substTs σs 1 0 V)) + 1)) := by
      rw [hwc]; simp [close, substTs, wc_tex, wc_prod, hw1]
    split
    · exact hmem
    split
    · exact hmem
    split
    · rename_i n hn
      refine List.mem_append_right _ ?_
      rw [hn] at hrt
      have hlen : ws.length = n + 1 := ShapeC_len hl.1 (by simpa using hrt)
      have hne : List.drop n ws ≠ [] := by
        intro h; have := congrArg List.length h; simp [hlen] at this
      have hd : (List.drop n ws).getLast? = some pw := by
        rw [← hlast, List.getLast?_drop]; simp [hlen]; omega
      exact List.mem_of_getLast? hd
    · rename_i hn
      exact absurd (by rw [hrt]; simp [hn]) hl.2.2.1

/-- **`isTy`'s result** is the package's slot word or `null`, so it names nothing new. -/
theorem valB_isTy {p : Prog} {E : TEnv} {g : G} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {y : String} {a : At} {τ : Ty} {e : Expr}
    (hT : ThInvE p E th) (hterm : th.term = .let_ y (.isTy a τ) e)
    (h : r ∈ evalOp g th.env th.σs s (.isTy a τ)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  obtain ⟨ρ, η, cx, -, -, ⟨hTy, -⟩, -, hF, -⟩ := hT
  rw [hterm] at hTy
  cases hTy with
  | let_ hop _ =>
    cases hop with
    | isTy hpk hsl _ _ _ _ =>
      obtain ⟨rt, ws, he, -, hl⟩ := peek_VR hF.2.1 hpk
      simp only [evalOp, ol, Option.mem_toList, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨t0, ws0⟩, he0, pw, hpw, h⟩ := h
      rw [he] at he0
      simp only [Option.some.injEq, Prod.mk.injEq] at he0
      obtain ⟨rfl, rfl⟩ := he0
      have hnull : ValB sto s1 lb N th (.ptrOpt .pub (close th.σs τ)) [cst .null] :=
        valB_of_cntOld (cntOld_pub_noNames fun w hw l => by
          rw [List.mem_singleton] at hw; subst hw; exact not_names_null l)
      have hfound : ValB sto s1 lb N th (.ptrOpt .pub (close th.σs τ)) [pw] := by
        refine valB_of_cntOld (cntOld_of_rtsSub ?_ (cntOld_evalAt he))
        intro w hw l hn
        have hw' : w = pw := by simpa [pubWords, sNo, mPub] using hw
        subst hw'
        exact ⟨w, slot_mem_pubWords hsl hl hpw, hn, Nat.le_refl _⟩
      repeat' split at h
      all_goals (simp only [pure, Option.some.injEq] at h; subst h; first | exact hfound | exact hnull)

/-- **A `let` of a non-call op** whose every result is fine at the empty store typing meets the
step contract. -/
theorem stepOK_op {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {x : String} {op : Op} {e : Expr}
    {sto : Sto} {ga : AllocLabel} {Gl : AllocLabel → Prop}
    (hterm : th.term = .let_ x op e) (hc : Robust.isCallOp op = false)
    (hv : ∀ r ∈ evalOp g th.env th.σs (stOf mem pairs th) op,
      ValB (fun _ => none) (stOf mem pairs th) ga Gl th r.2.1 r.2.2) :
    ∀ r ∈ tstep g mem pairs th, StepOK sto (stOf mem pairs th) ga Gl Gl th r.2.2 := by
  intro r hr
  by_cases hN : ∃ a T, op = .new a T
  · obtain ⟨a, T, rfl⟩ := hN
    obtain ⟨s1, t1, ws1, hm1, tys, rfl⟩ := TermRun.tstep_new_mem hterm hr
    exact stepOK_of_stepB_nil (stepB_let (x := x) rfl rfl (hv _ hm1))
  rw [TermLocal.tstep_let_gen hterm hc (fun a T h => hN ⟨a, T, h⟩)] at hr
  obtain ⟨⟨s', t, ws⟩, hm, rfl⟩ := List.mem_map.1 hr
  exact stepOK_of_stepB_nil (stepB_let (x := x) rfl rfl (hv _ hm))

/-- A non-capability term in the run scope is in the plain scope. -/
theorem scope_of {σs : List Ty} {cx : Cx} {t : Expr} (h : ScopeD σs cx t) (hn : ¬ CapT t) :
    StepScope cx t :=
  h.elim id fun h => (hn h.2).elim

theorem notCap_let {x : String} {op : Op} {e : Expr}
    (h : ∀ a b, op ≠ .borrow a b) (h2 : ∀ a, op ≠ .freeze a) (h3 : ∀ a, op ≠ .endBorrow a) :
    ¬ CapT (.let_ x op e) := by
  rintro ⟨x', e', ⟨a, b, he⟩ | ⟨a, he⟩ | ⟨a, he⟩⟩ <;> cases he
  · exact h a b rfl
  · exact h2 a rfl
  · exact h3 a rfl

/-! ## (k2a v5) Loads and fetches under the widened `OpScope` (c1, LDST)

A pair or word load and a fetch reach a reference of any mode; a region cell is loaded (`loadRgn`,
`loadCap`) as a `pub` one.  `TermK2aLdW` / `TermK2aRmw` keep their own/`pub` lemmas unchanged. -/

section V5
open TermK2aLdW TermK2aRmw TermPtrRts

/-- **`ldp` through a locative of any mode** (`ld_pLoc` without its mode premise, unused there). -/
theorem ld_pLocAny {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x w n0 n1 : String} {acq : Bool} {μ : Mode} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.ldp acq (.var w) n0 n1) e)
    (hu : (∃ r P, u = .word2 r P) ∨ (∃ r P, u = .epair r P))
    (hpk : cx.peek (.var w) = .ok (.loc μ u))
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    {sto : Sto} (_hsto1 : ∀ l c, η.sto l = some c → sto l = some c) (_hLay : ∀ l c, sto l = some c → LayT c.ty)
    (_hG : GranuleWP sto mem pairs th.promises) {Gl : AllocLabel → Prop}
    (_hPf : ∀ l f, η.pfr l = some f → Gl l) (_hBx : ∀ l B, η.box l = some B → Gl l)
    (ga : AllocLabel) (N : AllocLabel → Prop) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      LdOK sto (stOf mem pairs th) ga N Gl th r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  cases hop with
  | ldp hp _ hb =>
  rw [hpk] at hp; cases hp
  have hoq : cx.opaqueOK u = true := by
    rcases hu with ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩ <;> simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨ad, pw, μr, ru, hea, haddr, -, hsku, -, -, hld, -, -⟩ :=
    locCell (acq := acq) (rel := false) (g := g) (mem := mem) (pairs := pairs) hpk hoq
      (pair_accs_cl hu) hi hE htv hm
  obtain ⟨-, hpr⟩ := pair_ru_loc μr hu hsku
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ad acq [.two] 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .prod .int .int, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hpr, haddr, ↓reduceIte, List.map_map]; rfl
  rw [key]
  intro r0 hr hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, -⟩ := hld s' wsr hl hpr0
  exact ldOK_num rfl rfl rfl (pair_nums hu hvr)


/-- **`load` of a protocol word through a locative of any mode** (`ld_wordLoc` without its mode
premise, unused there). -/
theorem ld_wordLocAny {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {μ : Mode} {r : Idx} {P : Proto}
    {e : Expr} (hterm : th.term = .let_ x (.load acq a) e)
    (hpk : cx.peek a = .ok (.loc μ (.word r P)))
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    {sto : Sto} (_hsto1 : ∀ l c, η.sto l = some c → sto l = some c) (_hLay : ∀ l c, sto l = some c → LayT c.ty)
    (_hG : GranuleWP sto mem pairs th.promises) {Gl : AllocLabel → Prop}
    (_hPf : ∀ l f, η.pfr l = some f → Gl l) (_hBx : ∀ l B, η.box l = some B → Gl l)
    (ga : AllocLabel) (N : AllocLabel → Prop) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      LdOK sto (stOf mem pairs th) ga N Gl th r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  cases hop with
  | loadOwn hp hnw _ _ _ | loadPub hp hnw _ _ _ _ | loadRgn hp hnw _ _ _ _ | loadCap hp hnw _ _ _ _ _
  | loadTorn hp hnw _ _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [wordOf] at hnw
  | loadWord hp hw hg hb =>
  rw [hpk] at hp; cases hp
  simp only [wordOf, Option.some.injEq] at hw; subst hw
  have hg' : P.ghost = false := hg
  have hus1 : accs (cl ρ η.wit 0 0 (.word r P)) = some [.one] := by simp [cl, accs, hg']
  obtain ⟨ad, pw, μr, ru, hea, haddr, hus, hsku, -, -, hld, -, -⟩ :=
    locCell (acq := acq) (rel := false) (g := g) (mem := mem) (pairs := pairs) hpk
      (by simp [Cx.opaqueOK, Ty.guardT]) hus1 hi hE htv hm
  obtain ⟨r', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ad acq [.one] 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .int, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, cellOf, haddr, wordOf, Option.isSome_some,
      ↓reduceIte, hus, List.map_map]; rfl
  rw [key]
  intro r0 hr hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, -⟩ := hld s' wsr hl hpr0
  exact ldOK_num rfl rfl rfl (word_nums hg' hvr)


/-- **`ldp` through a reference of a non-`own` mode** (`pub` or `rgn`; `loadNO_core`). -/
theorem ld_pNO {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x w n0 n1 : String} {acq : Bool} {μ : Mode} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.ldp acq (.var w) n0 n1) e)
    (hu : (∃ r P, u = .word2 r P) ∨ (∃ r P, u = .epair r P))
    (hpk : cx.peek (.var w) = .ok (.ptr μ u)) (hμ : μ ≠ .own)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    {sto : Sto} (_hsto1 : ∀ l c, η.sto l = some c → sto l = some c) (_hLay : ∀ l c, sto l = some c → LayT c.ty)
    (_hG : GranuleWP sto mem pairs th.promises) {Gl : AllocLabel → Prop}
    (_hPf : ∀ l f, η.pfr l = some f → Gl l) (_hBx : ∀ l B, η.box l = some B → Gl l)
    (ga : AllocLabel) (N : AllocLabel → Prop) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      LdOK sto (stOf mem pairs th) ga N Gl th r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  cases hop with
  | ldp hp _ hb =>
  rw [hpk] at hp; cases hp
  have hoq : cx.opaqueOK u = true := by
    rcases hu with ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩ <;> simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨μr, ru, pw, lab, us, hea, hpw, hus, hsku, -, hld, -⟩ :=
    loadNO_core (acq := acq) (g := g) (mem := mem) (pairs := pairs) hpk hμ hoq hi hE htv hm
  obtain ⟨hru, hpr⟩ := pair_ru μr hu hsku
  rw [hru] at hus; cases hus
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ⟨lab, 0⟩ acq [.two] 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .prod .int .int, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hpr, addrOf, hpw, ↓reduceIte, List.map_map]; rfl
  rw [key]
  intro r0 hr hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, -⟩ := hld s' wsr hl hpr0
  exact ldOK_num rfl rfl rfl (pair_nums hu hvr)


/-- **`load` of a protocol word through a pointer of a non-`own` mode** (`pub` or `rgn`;
`loadNO_core`). -/
theorem ld_wordNO {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {μ : Mode} {r : Idx} {P : Proto}
    {e : Expr} (hterm : th.term = .let_ x (.load acq a) e)
    (hpk : cx.peek a = .ok (.ptr μ (.word r P))) (hμ : μ ≠ .own)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    {sto : Sto} (_hsto1 : ∀ l c, η.sto l = some c → sto l = some c) (_hLay : ∀ l c, sto l = some c → LayT c.ty)
    (_hG : GranuleWP sto mem pairs th.promises) {Gl : AllocLabel → Prop}
    (_hPf : ∀ l f, η.pfr l = some f → Gl l) (_hBx : ∀ l B, η.box l = some B → Gl l)
    (ga : AllocLabel) (N : AllocLabel → Prop) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      LdOK sto (stOf mem pairs th) ga N Gl th r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  cases hop with
  | loadOwn hp hnw _ _ _ | loadPub hp hnw _ _ _ _ | loadRgn hp hnw _ _ _ _ | loadCap hp hnw _ _ _ _ _
  | loadTorn hp hnw _ _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [wordOf] at hnw
  | loadWord hp hw hg hb =>
  rw [hpk] at hp; cases hp
  simp only [wordOf, Option.some.injEq] at hw; subst hw
  obtain ⟨μr, ru, pw, lab, us, hea, hpw, hus, hsku, -, hld, -⟩ :=
    loadNO_core (acq := acq) (g := g) (mem := mem) (pairs := pairs) hpk hμ
      (by simp [Cx.opaqueOK, Ty.guardT]) hi hE htv hm
  obtain ⟨r', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ⟨lab, 0⟩ acq us 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .int, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, cellOf, addrOf, hpw, wordOf, Option.isSome_some,
      ↓reduceIte, hus, List.map_map]; rfl
  rw [key]
  intro r0 hr hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, -⟩ := hld s' wsr hl hpr0
  exact ldOK_num rfl rfl rfl (word_nums hg hvr)


/-- **`fetch` through a pointer of any mode**: the old value bound is a number (a region cell: a
non-`own` `int` cell, `pubIntCellNO`). -/
theorem rmw_fetchAny {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {o : FetchOp} {acq rel : Bool} {a v : At}
    {e : Expr} {μ : Mode} {u : Ty}
    (hterm : th.term = .let_ x (.fetch o acq rel a v) e)
    (hpk : cx.peek a = .ok (.ptr μ u))
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    {sto : Sto} {Gl : AllocLabel → Prop} (ga : AllocLabel) (N : AllocLabel → Prop) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      LdOK sto (stOf mem pairs th) ga N Gl th r.2.2 := by
  have hT0 := hT
  rw [hterm] at hT0
  cases hT0 with
  | let_ hop _ =>
  cases hop with
  | fetchCell hp _ hc hu hsub _hb =>
    rw [hpk] at hp; cases hp
    rcases hc with hc | ⟨r, hc, -⟩
    · simp only [cellOf, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨lab, pw, ru, hea, hpw, -, -, hcell⟩ :=
        pubIntCell (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk hi hE htv hm
      obtain ⟨hi1, rv, wsv, hev, hvv, -⟩ := use_FInv hu hi
      have hvi := VR_sub hi1.1 hsub _ _ hvv
      simp only [VR] at hvi
      obtain ⟨dd, hdd⟩ := hvi
      obtain ⟨nw, rfl, hnwv⟩ := map_singleton hdd
      exact fetch_coreK (ad := ⟨lab, 0⟩) hterm hea (by simp [addrOf, hpw]) hev hnwv
        (fun s1 ws hl hp1 => (hcell s1 ws hl hp1).2.1) ga N
    · simp only [cellOf, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨lab, pw, μr, ru, hea, hpw, -, -, hcell⟩ :=
        pubIntCellNO (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk (fun h => by cases h)
          hi hE htv hm
      obtain ⟨hi1, rv, wsv, hev, hvv, -⟩ := use_FInv hu hi
      have hvi := VR_sub hi1.1 hsub _ _ hvv
      simp only [VR] at hvi
      obtain ⟨dd, hdd⟩ := hvi
      obtain ⟨nw, rfl, hnwv⟩ := map_singleton hdd
      exact fetch_coreK (ad := ⟨lab, 0⟩) hterm hea (by simp [addrOf, hpw]) hev hnwv
        (fun s1 ws hl hp1 => (hcell s1 ws hl hp1).2.1) ga N
  | fetchEpoch hp hw hep _ hj heq _hb =>
    rw [hpk] at hp; cases hp
    cases u <;> simp [wordOf] at hw
    obtain ⟨rfl, rfl⟩ := hw
    rename_i r P
    have hpwf := wordRef_pwf hpk (.inl rfl) hi hE htv hm
    have hg : P.ghost = false := by
      have := pwf_epochOK hpwf hep
      unfold epochOK at this; simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
      exact this.1.2
    obtain ⟨lab, pw, μQ, rQ, hea, hpw, -, hcell⟩ :=
      wordCellF (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk hg hi hE htv hm
    obtain ⟨tv, htvk, hjo⟩ := hj
    obtain ⟨rtv, nw, hev, hnwv, -⟩ := atom_num hi.2.1 htvk hjo
    have hj1 := heq ρ hi.1
    simp only [ev] at hj1
    rw [hj1] at hnwv
    refine fetch_coreK (ad := ⟨lab, 0⟩) hterm hea (by simp [addrOf, hpw]) hev hnwv (fun s1 ws hl hp1 => ?_) ga N
    have hq := (hcell s1 ws hl hp1).2.1
    simp only [VR] at hq
    obtain ⟨n, hn, -⟩ := hq.2 hg
    exact ⟨n, hn⟩
  | fetchShare hp hw hep hj heq hok _hb =>
    rw [hpk] at hp; cases hp
    cases u <;> simp [wordOf] at hw
    obtain ⟨rfl, rfl⟩ := hw
    rename_i r P
    have hg : P.ghost = false := by
      unfold fetchOK at hok; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
      exact hok.1.1.1.1
    obtain ⟨lab, pw, μQ, rQ, hea, hpw, -, hcell⟩ :=
      wordCellF (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk hg hi hE htv hm
    obtain ⟨tv, htvk, hjo⟩ := hj
    obtain ⟨rtv, nw, hev, hnwv, -⟩ := atom_num hi.2.1 htvk hjo
    have hjd := heq ρ hi.1
    simp only [ev] at hjd
    rw [hjd] at hnwv
    refine fetch_coreK (ad := ⟨lab, 0⟩) hterm hea (by simp [addrOf, hpw]) hev hnwv (fun s1 ws hl hp1 => ?_) ga N
    have hq := (hcell s1 ws hl hp1).2.1
    simp only [VR] at hq
    obtain ⟨n, hn, -⟩ := hq.2 hg
    exact ⟨n, hn⟩


/-- **`fetch` through a locative of any mode**: the old value bound is a number (a region cell as a
`pub` one: `locCell` holds at any mode). -/
theorem rmw_fetchLocAny {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {o : FetchOp} {acq rel : Bool} {a v : At}
    {e : Expr} {μ : Mode} {u : Ty}
    (hterm : th.term = .let_ x (.fetch o acq rel a v) e)
    (hpk : cx.peek a = .ok (.loc μ u))
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    {sto : Sto} {Gl : AllocLabel → Prop} (ga : AllocLabel) (N : AllocLabel → Prop) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      LdOK sto (stOf mem pairs th) ga N Gl th r.2.2 := by
  have hT0 := hT
  rw [hterm] at hT0
  cases hT0 with
  | let_ hop _ =>
  cases hop with
  | fetchCell hp _ hc hu hsub _hb =>
    rw [hpk] at hp; cases hp
    rcases hc with hc | ⟨r, hc, -⟩
    · simp only [cellOf, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      have hus1 : accs (cl ρ η.wit 0 0 .int) = some [.one] := by simp [cl, accs]
      obtain ⟨ad, pw, μr, ru, hea, haddr, -, -, -, -, hld, -, -⟩ :=
        locCell (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk
          (by simp [Cx.opaqueOK, Ty.guardT]) hus1 hi hE htv hm
      obtain ⟨hi1, rv, wsv, hev, hvv, -⟩ := use_FInv hu hi
      have hvi := VR_sub hi1.1 hsub _ _ hvv
      simp only [VR] at hvi
      obtain ⟨dd, hdd⟩ := hvi
      obtain ⟨nw, rfl, hnwv⟩ := map_singleton hdd
      refine fetch_coreK hterm hea haddr hev hnwv (fun s1 ws hl hp1 => ?_) ga N
      obtain ⟨hvr, -, -⟩ := hld s1 ws hl hp1
      simpa [VR] using hvr
    · simp only [cellOf, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      have hus1 : accs (cl ρ η.wit 0 0 .int) = some [.one] := by simp [cl, accs]
      obtain ⟨ad, pw, μr, ru, hea, haddr, -, -, -, -, hld, -, -⟩ :=
        locCell (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk
          (by simp [Cx.opaqueOK, Ty.guardT]) hus1 hi hE htv hm
      obtain ⟨hi1, rv, wsv, hev, hvv, -⟩ := use_FInv hu hi
      have hvi := VR_sub hi1.1 hsub _ _ hvv
      simp only [VR] at hvi
      obtain ⟨dd, hdd⟩ := hvi
      obtain ⟨nw, rfl, hnwv⟩ := map_singleton hdd
      refine fetch_coreK hterm hea haddr hev hnwv (fun s1 ws hl hp1 => ?_) ga N
      obtain ⟨hvr, -, -⟩ := hld s1 ws hl hp1
      simpa [VR] using hvr
  | fetchEpoch hp hw hep _ hj heq _hb =>
    rw [hpk] at hp; cases hp
    cases u <;> simp [wordOf] at hw
    obtain ⟨rfl, rfl⟩ := hw
    rename_i r P
    have hpwf := wordRef_pwf hpk (.inr rfl) hi hE htv hm
    have hg : P.ghost = false := by
      have := pwf_epochOK hpwf hep
      unfold epochOK at this; simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
      exact this.1.2
    have hus1 : accs (cl ρ η.wit 0 0 (.word r P)) = some [.one] := by simp [cl, accs, hg]
    obtain ⟨ad, pw, μr, ru, hea, haddr, -, hsku, -, -, hld, -, -⟩ :=
      locCell (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk
        (by simp [Cx.opaqueOK, Ty.guardT]) hus1 hi hE htv hm
    obtain ⟨rQ, rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
    obtain ⟨tv, htvk, hjo⟩ := hj
    obtain ⟨rtv, nw, hev, hnwv, -⟩ := atom_num hi.2.1 htvk hjo
    have hj1 := heq ρ hi.1
    simp only [ev] at hj1
    rw [hj1] at hnwv
    refine fetch_coreK hterm hea haddr hev hnwv (fun s1 ws hl hp1 => ?_) ga N
    have hq := (hld s1 ws hl hp1).1
    simp only [VR] at hq
    obtain ⟨n, hn, -⟩ := hq.2 hg
    exact ⟨n, hn⟩
  | fetchShare hp hw hep hj heq hok _hb =>
    rw [hpk] at hp; cases hp
    cases u <;> simp [wordOf] at hw
    obtain ⟨rfl, rfl⟩ := hw
    rename_i r P
    have hg : P.ghost = false := by
      unfold fetchOK at hok; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
      exact hok.1.1.1.1
    have hus1 : accs (cl ρ η.wit 0 0 (.word r P)) = some [.one] := by simp [cl, accs, hg]
    obtain ⟨ad, pw, μr, ru, hea, haddr, -, hsku, -, -, hld, -, -⟩ :=
      locCell (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk
        (by simp [Cx.opaqueOK, Ty.guardT]) hus1 hi hE htv hm
    obtain ⟨rQ, rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
    obtain ⟨tv, htvk, hjo⟩ := hj
    obtain ⟨rtv, nw, hev, hnwv, -⟩ := atom_num hi.2.1 htvk hjo
    have hjd := heq ρ hi.1
    simp only [ev] at hjd
    rw [hjd] at hnwv
    refine fetch_coreK hterm hea haddr hev hnwv (fun s1 ws hl hp1 => ?_) ga N
    have hq := (hld s1 ws hl hp1).1
    simp only [VR] at hq
    obtain ⟨n, hn, -⟩ := hq.2 hg
    exact ⟨n, hn⟩


/-- **`load` through a region pointer** (`loadRgn`, `loadCap`, `loadTorn`), as through a `pub` one
(`ld_pub`): the cell is a non-`own` one (`loadNO_core`, `pubPtr_viewNO`; the payload is `opaqueOK` by
`ruleA`, `TermC1.rgnLoad_ruleA`).  (G2 fix) The runtime binds `.int` at a word payload, else the
payload's runtime type; the counted words are the same (`pubWords_of_sNo`), so a torn load is no
different here. -/
theorem ld_rgn {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {rg : Idx} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.load acq a) e)
    (hpk : cx.peek a = .ok (.ptr (.rgn rg) u)) (hnw : wordOf (Ty.ptr (.rgn rg) u) = none)
    (hT : Typed p cx th.term) {w0 : Nat → Ty} (hck : TermA4.CkW p w0 cx th.term)
    (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    {sto : Sto} (hsto1 : ∀ l c, η.sto l = some c → sto l = some c) (hLay : ∀ l c, sto l = some c → LayT c.ty)
    (hG : GranuleWP sto mem pairs th.promises) {Gl : AllocLabel → Prop}
    (hPf : ∀ l f, η.pfr l = some f → Gl l) (hBx : ∀ l B, η.box l = some B → Gl l)
    (ga : AllocLabel) (N : AllocLabel → Prop) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      LdOK sto (stOf mem pairs th) ga N Gl th r.2.2 := by
  rw [hterm] at hT hck
  obtain ⟨hoq, -⟩ := TermC1.rgnLoad_ruleA hck.1 hpk hnw rfl
  obtain ⟨μr, ru, pw, lab, us, hea, hpw, hus, hsku, -, hld, -⟩ :=
    loadNO_core (acq := acq) (g := g) (mem := mem) (pairs := pairs) hpk (fun h => by cases h) hoq
      hi hE htv hm
  obtain ⟨lab2, c, pw2, μr2, ru2, f, hea2, hpw2, hsto, hcty, -, -, hacc, -, hsig⟩ :=
    pubPtr_viewNO hi hpk (fun h => by cases h) htv hoq
  rw [hea] at hea2
  simp only [Option.some.injEq, Prod.mk.injEq, Ty.ptr.injEq, List.cons.injEq, and_true, and_assoc] at hea2
  obtain ⟨rfl, rfl, rfl⟩ := hea2
  rw [hpw] at hpw2
  simp only [WeakMem.Val.loc.injEq, WeakMem.Address.mk.injEq, and_true] at hpw2
  subst hpw2
  have hpwE : ∀ ws, pubWords (if (wordOf (Ty.ptr μr ru)).isSome then Ty.int else ru) ws = pubWords ru ws := by
    intro ws
    cases ru with
    | word r P =>
        show pubWords Ty.int ws = pubWords (Ty.word r P) ws
        rw [pubWords_of_sNo rfl, pubWords_of_sNo rfl]
    | _ => rfl
  have hacr : accs ru = accs (cl ρ η.wit 0 0 u) :=
    pub_accs hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl hoq hea rfl
  have hna : ∀ N e', c.ty ≠ .array (.lit N) e' := fun N e' h => hacc (by rw [h]; simp [accs])
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ⟨lab, 0⟩ acq us 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, if (wordOf (Ty.ptr μr ru)).isSome then Ty.int else ru, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, cellOf, addrOf, hpw, hus, List.map_map]; rfl
  rw [key]
  intro r hr hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, hlay, -⟩ := hld s' wsr hl hpr0
  have hUa : accs (cl ρ η.wit 0 0 u) = some us := by rw [← hacr]; exact hus
  have hU : ∀ N e', cl ρ η.wit 0 0 u ≠ .array (.lit N) e' := fun N e' h => by
    rw [h] at hUa; simp [accs] at hUa
  have hc1 := hsto1 _ _ hsto
  obtain ⟨hwc, hval⟩ := wc_valid_of_lay hlay
  refine ⟨x, _, wsr, rfl, rfl, fun w hw => ?_, fun w hw => ?_⟩
  · rw [hpwE] at hw
    exact valB_load (ad := ⟨lab, 0⟩) hc1 (hLay _ _ hc1) (Fd_AtOff hcty hacc) (IniAt_of_ne (ini := η.rc) hna) hU hUa
      hG hsig hl hpr0 ga N w hw
  · rw [hpwE] at hw
    exact lbl_load hE.2.1 hPf hBx hsig hvr hwc hval w hw


/-- **`load` through a region locative** (`loadRgn`, `loadCap`, `loadTorn`), as through a `pub` one
(`ld_pubLoc`): `ModeOK (.rgn _)` and `modeIni (.rgn _)` are the `pub` ones; the payload is `opaqueOK`
and `arrFree` by `ruleA` (`TermC1.rgnLoad_ruleA`).  (G2 fix) The bound runtime type is `.int` at a
word payload, with the same counted words (`pubWords_of_sNo`), so a torn load is no different here. -/
theorem ld_rgnLoc {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {rg : Idx} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.load acq a) e)
    (hpk : cx.peek a = .ok (.loc (.rgn rg) u)) (hnw : wordOf (Ty.loc (.rgn rg) u) = none)
    (hT : Typed p cx th.term) {w0 : Nat → Ty} (hck : TermA4.CkW p w0 cx th.term)
    (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    {sto : Sto} (hsto1 : ∀ l c, η.sto l = some c → sto l = some c) (hLay : ∀ l c, sto l = some c → LayT c.ty)
    (hG : GranuleWP sto mem pairs th.promises) {Gl : AllocLabel → Prop}
    (hPf : ∀ l f, η.pfr l = some f → Gl l) (hBx : ∀ l B, η.box l = some B → Gl l)
    (ga : AllocLabel) (N : AllocLabel → Prop) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      LdOK sto (stOf mem pairs th) ga N Gl th r.2.2 := by
  rw [hterm] at hT hck
  obtain ⟨hoq, harr⟩ := TermC1.rgnLoad_ruleA hck.1 hpk hnw rfl
  obtain ⟨rt, ws, hea, hv, hl⟩ := peek_VR hi.2.1 hpk
  have haf' : (cl ρ η.wit 0 0 u).arrFree = true := arrFree_cl hi.2.2.2.2.2.2.1.af u 0 0 harr
  have hnb : ∀ n e, ¬ Fd (.array (.lit n) e) (cl ρ η.wit 0 0 u) := fun n e hF => by
    have := Fd_arrFree hF haf'; simp [Ty.arrFree] at this
  obtain ⟨ad, c, hws, hsto, hat, hmode, hini⟩ :=
    cell_target (rfl : cellOf (.loc (.rgn rg) u) = some (.rgn rg, u)) hnb hv
  obtain ⟨pw, rfl, hpw⟩ := map_singleton hws
  have hsk := hl.2.1
  obtain ⟨μr, ru, rfl, -, hsku⟩ : ∃ μr ru, rt = .loc μr ru ∧ skelM μr = skelM (.rgn rg) ∧
      etok (skel ru) = etok (skel (close th.σs u)) := by
    simp only [close, substTs, skel, etok] at hsk
    obtain ⟨μr, ru, rfl, h1, h2⟩ := eskel_eq_loc hsk
    exact ⟨μr, ru, rfl, h1, h2⟩
  have hpwE : ∀ ws, pubWords (if (wordOf (Ty.loc μr ru)).isSome then Ty.int else ru) ws = pubWords ru ws := by
    intro ws
    cases ru with
    | word r P =>
        show pubWords Ty.int ws = pubWords (Ty.word r P) ws
        rw [pubWords_of_sNo rfl, pubWords_of_sNo rfl]
    | _ => rfl
  have htb : tb cx.ke.length u = true :=
    tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.loc (.rgn rg) u) = some (.rgn rg, u))
  have hsig : sig ru = sig (cl ρ η.wit 0 0 u) := by
    have h1 : sig ru = sig (close th.σs u) := sig_of_eskel hsku
    rw [h1]; exact sig_WitL hi.2.2.2.1 ρ hoq (lt_of_guardT htb hi.2.2.2.2.1)
  have hna : ∀ N e', cl ρ η.wit 0 0 u ≠ .array (.lit N) e' := fun N e' h => by
    rw [h] at haf'; simp [Ty.arrFree] at haf'
  have hlr := pub_accs hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl hoq hea rfl
  have hc1 := hsto1 _ _ hsto
  -- the common finish, from the loaded value's `VR` and `Lay`
  have fin : ∀ us, accs ru = some us →
      (∀ s' wsr, (s', wsr) ∈ loadUnits g.arch pw ad acq us 0 (stOf mem pairs th) → PromAbove s' →
        VR ρ η u (shp ru) wsr ∧ Lay th.σs u ru wsr) →
      ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
        LdOK sto (stOf mem pairs th) ga N Gl th r.2.2 := by
    intro us hus hld
    have key : tstep g mem pairs th =
        (loadUnits g.arch pw ad acq us 0 (stOf mem pairs th)).map fun (s', ws) =>
          (s'.mem, s'.pairs, withS { th with term := e, env := (x, if (wordOf (Ty.loc μr ru)).isSome then Ty.int else ru, ws) :: th.env } s') := by
      simp only [tstep, hterm, evalOp, hea, cellOf, addrOf, hpw, hus, List.map_map]; rfl
    rw [key]
    intro r hr hpr0
    rw [List.mem_map] at hr
    obtain ⟨⟨s', wsr⟩, hl', rfl⟩ := hr
    obtain ⟨hvr, hlay⟩ := hld s' wsr hl' hpr0
    have hUa : accs (cl ρ η.wit 0 0 u) = some us := by rw [← hlr]; exact hus
    obtain ⟨hwc, hval⟩ := wc_valid_of_lay hlay
    refine ⟨x, _, wsr, rfl, rfl, fun w hw => ?_, fun w hw => ?_⟩
    · rw [hpwE] at hw
      exact valB_load hc1 (hLay _ _ hc1) hat hini hna hUa hG hsig hl' hpr0 ga N w hw
    · rw [hpwE] at hw
      exact lbl_load hE.2.1 hPf hBx hsig hvr hwc hval w hw
  by_cases hown : c.owner = some η.tid
  · obtain ⟨us, hus, -, hld, -⟩ := locLoadI (arch := g.arch) (pw := pw) (acq := acq)
      (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hm.2.2.2.2.2.1 hsto hown hat hini hna
      (fun _ f hf hns => by
        simp only [ModeOK] at hmode
        obtain ⟨f0, hf0, hsf⟩ := hmode
        obtain rfl : f0 = f := Option.some.inj (hf0.symm.trans hf)
        rcases hsf with hs | hs
        · exact absurd hs hns
        · exact hs pw (by simp)) hsku hsig
        (cell_lyt hl.2.2.2.2 rfl rfl).2
          (accs_rtW hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hoq htb (cell_lyt hl.2.2.2.2 rfl rfl).2)
    exact fin us hus fun s' wsr hl' hpa => by
      obtain ⟨hvr, hlay, -⟩ := hld (s', wsr) hl' hpa
      exact ⟨hvr, hlay⟩
  · simp only [ModeOK] at hmode
    obtain ⟨f, hf, hsf⟩ := hmode
    have hfv : f ≤ pw.view := by
      rcases hsf with hs | hs
      · rcases hm.2.2.2.2.2.2.2.2.1.1 ad.label hs with ⟨c0, h1, h2⟩ | ⟨h1, -⟩
        · refine absurd ?_ hown
          have h1' : η.sto ad.label = some c0 := h1
          rw [hsto] at h1'
          rw [Option.some.inj h1']; exact h2
        · have h1' : η.sto ad.label = none := h1
          rw [hsto] at h1'; cases h1'
      · exact hs pw (by simp)
    have hlU : accs (cl ρ η.wit 0 0 u) ≠ none := by
      rcases AtOff_lay hat with h | ⟨N, e', h, -⟩
      · exact h
      · exact absurd h (hna N e')
    obtain ⟨us, hus⟩ : ∃ us, accs ru = some us := Option.ne_none_iff_exists'.1 (by rw [hlr]; exact hlU)
    have husU : accs (cl ρ η.wit 0 0 u) = some us := by rw [← hlr, hus]
    obtain ⟨-, hval, -⟩ := pubLoadAt (arch := g.arch) (pw := pw) (acq := acq)
      hm.2.2.2.2.2.2.2.2.1 hm.2.2.2.2.2.2.1 hsto hown hf hfv hat hini hna husU
    refine fin us hus fun s' wsr hl' hpr0 => ?_
    obtain ⟨q, hq, hle⟩ := hval (s', wsr) hl' (hpr0)
    have hrl : wsr.length = nWords us :=
      (Reads_unit us 0 wsr (loadUnits_reads us 0 _ (s', wsr) hl' [] (fun _ _ h => by cases h))).1
    obtain ⟨hvr0, hV0⟩ := ValOf.env hq
    have hvr : VR ρ η u (shp ru) wsr := by
      rw [shp_of_sig hsig]
      exact (VR_close hE.2.1 ρ u [] 0 ρ (fun _ => 0) (shp (cl ρ η.wit 0 0 u)) wsr (fun k => rfl)
        (fun k hk => absurd hk (Nat.not_lt_zero _))).2 (VR_up _ _ q wsr hle hvr0)
    exact ⟨hvr, ⟨fun us' h => by rw [hus] at h; cases h; exact hrl, hsku, by simp [wc, hus],
      Valid_of_sig hsig.symm (Valid_vals _ q wsr hle.vals hV0), (cell_lyt hl.2.2.2.2 rfl rfl).2⟩⟩


/-- (G2 fix) **`xchg` through a region pointer**: the old value bound is what the read half read
(`loadCell_core`, a `pub`-like frontier by `TermC1.rgnV`); the bound type is the payload
(`TermC1.rgn_adapt`).  The read half is COPIED from the `TermC1.tstepM_xchgRgn1` (TermStep), the
finish from `TermK2aRmw.rmw_xchgOwn`. -/
theorem rmw_xchgRgnD4 {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a v : At} {rg : Idx} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.xchg a v) e)
    (hpk : cx.peek a = .ok (.ptr (.rgn rg) u))
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    {sto : Sto} (hsto1 : ∀ l c, η.sto l = some c → sto l = some c) (hLay : ∀ l c, sto l = some c → LayT c.ty)
    (hG : GranuleWP sto mem pairs th.promises) {Gl : AllocLabel → Prop}
    (hPf : ∀ l f, η.pfr l = some f → Gl l) (hBx : ∀ l B, η.box l = some B → Gl l)
    (ga : AllocLabel) (N : AllocLabel → Prop) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      LdOK sto (stOf mem pairs th) ga N Gl th r.2.2 := by
  have hmo := TermC1.hmo_of_vars hi.2.1 hpk rfl
  have had : adapt rg u = u := TermC1.rgn_adapt hi hpk hm hmo
  rw [hterm] at hT
  cases hT with
  | let_ hop _ =>
  cases hop with
  | xchg hp hx hu hsub hb =>
  obtain ⟨t, uQ, o, tv, c₁, hp, hx, hu, hsub, hb⟩ : ∃ t uQ o tv c₁, cx.peek a = .ok t ∧
      XchgCell cx t uQ o ∧ cx.use v = .ok (tv, c₁) ∧ (SubS c₁ tv uQ ∨ SubS c₁ tv o) ∧
      c₁.bind x o = .ok _ := ⟨_, _, _, _, _, hp, hx, hu, hsub, hb⟩
  rw [hpk] at hp; cases hp
  cases hx with
  | own _ hc _ => simp [cellOf] at hc
  | rgn _ hc _ _ _ =>
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, Mode.rgn.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  rw [had] at hsub hb
  have hsub : SubS c₁ tv u := hsub.elim id id
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  obtain ⟨lab, c, pw, μr, ru, hea, hpw, hsto, hcty, -, hacc, -, hsku, hsig⟩ := ptr_view hi hpk htv ho
  obtain ⟨hi1, rv, wsv, hev, hvv, hlv⟩ := use_FInv hu hi
  have hna : ∀ N e', c.ty ≠ .array (.lit N) e' := fun N e' h =>
    hacc (by rw [h]; simp [accs])
  obtain ⟨μr', ru', pw', lab', us, hea', -, hpw', hus, -, hne, hld, -⟩ :=
    loadCell_core (acq := false) (g := g) (mem := mem) (pairs := pairs) hpk ho hi hE htv hm (TermC1.rgnV hmo)
  have e1 := Option.some.inj (hea.symm.trans hea')
  simp only [Prod.mk.injEq, List.cons.injEq, and_true, Ty.ptr.injEq] at e1
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e1
  obtain rfl : lab = lab' := by
    rw [hpw] at hpw'; simp only [WeakMem.Val.loc.injEq, WeakMem.Address.mk.injEq] at hpw'; exact hpw'.1.1
  have husA : accs c.ty = some us := ((Fd_lay hcty).2.2.1.trans (pub_accs hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl ho hea rfl).symm).trans hus
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw ⟨lab, 0⟩ false us 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        (storeUnits g.k g.arch pw ⟨lab, 0⟩ false us wsv 0 s1).map fun s2 => (s2, ru, old)).map
        fun (sQ, t, ws) => (sQ.mem, sQ.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } sQ) := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus]
  rw [key]
  intro r hr hpr0
  obtain ⟨s1, old, h1, hp1, henv, hst⟩ := xchg_out hr hpr0
  obtain ⟨hvr, hlay, -⟩ := hld s1 old h1 hp1
  have hUa : accs (cl ρ η.wit 0 0 u) = some us := by rw [← (Fd_lay hcty).2.2.1]; exact husA
  have hU : ∀ N eQ, cl ρ η.wit 0 0 u ≠ .array (.lit N) eQ := fun N eQ h => by
    rw [h] at hUa; simp [accs] at hUa
  have hc1 := hsto1 _ _ hsto
  obtain ⟨hwc, hval⟩ := wc_valid_of_lay hlay
  refine ⟨x, ru, old, henv, hst, ?_, lbl_load hE.2.1 hPf hBx hsig hvr hwc hval⟩
  exact valB_load (ad := ⟨lab, 0⟩) hc1 (hLay _ _ hc1) (Fd_AtOff hcty hacc) (IniAt_of_ne (ini := η.rc) hna) hU hUa
    hG hsig h1 hp1 ga N

/-- (G2 fix) **`xchg` through a region locative**: the old component value bound is what the read
half read.  COPIED from the `TermC1.tstepM_xchgRgnLoc1` (TermStep: `adapt` collapse, cell target, read
half `hL` with its classical `by_cases` on `c.owner`), finished like `TermK2aRmw.rmw_xchgLoc`. -/
theorem rmw_xchgRgnLocD4 {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a v : At} {r : Idx} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.xchg a v) e)
    (hpk : cx.peek a = .ok (.loc (.rgn r) u))
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    {sto : Sto} (hsto1 : ∀ l c, η.sto l = some c → sto l = some c) (hLay : ∀ l c, sto l = some c → LayT c.ty)
    (hG : GranuleWP sto mem pairs th.promises) {Gl : AllocLabel → Prop}
    (hPf : ∀ l f, η.pfr l = some f → Gl l) (hBx : ∀ l B, η.box l = some B → Gl l)
    (ga : AllocLabel) (N : AllocLabel → Prop) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      LdOK sto (stOf mem pairs th) ga N Gl th r.2.2 := by
  have hmo := TermC1.hmo_of_varsL hi.2.1 hpk
  rw [hterm] at hT
  cases hT with
  | let_ hop _ =>
  cases hop with
  | xchg hp hx hu hsub hb =>
  obtain ⟨t, u', o, tv, c₁, hp, hx, hu, hsub, hb⟩ : ∃ t u' o tv c₁, cx.peek a = .ok t ∧
      XchgCell cx t u' o ∧ cx.use v = .ok (tv, c₁) ∧ (SubS c₁ tv u' ∨ SubS c₁ tv o) ∧
      c₁.bind x o = .ok _ := ⟨_, _, _, _, _, hp, hx, hu, hsub, hb⟩
  rw [hpk] at hp; cases hp
  cases hx with
  | own _ hc _ => simp [cellOf] at hc
  | rgn _ hc _ _ _ =>
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, Mode.rgn.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  have had : adapt r u = u := by
    rcases hsub with hs | hs
    · have hotv : cx.opaqueOK tv = true :=
        peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
      have ho : cx.opaqueOK u = true := sub_opaqueOK hs hotv
      have htb : tb cx.ke.length u = true :=
        tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.loc (.rgn r) u) = some (.rgn r, u))
      obtain ⟨_, _, _, _, _, hlv⟩ := use_FInv hu hi
      have hw : wc (close th.σs u) ≠ none := (Lay_canon hs hlv).2.2.2.1
      rw [wc_of_sig (sig_WitL hi.2.2.2.1 ρ ho (lt_of_guardT htb hi.2.2.2.2.1))] at hw
      exact TermC1.rgn_adaptT hi hpk rfl hm hmo (Fd_noarr fun h => hw (by simp [wc, h]))
    · exact TermC1.rgnLoc_adaptS hi htv hpk hm hmo _ _ hu hs
  rw [had] at hsub hb
  have hsub : SubS c₁ tv u := hsub.elim id id
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length u = true :=
    tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.loc (.rgn r) u) = some (.rgn r, u))
  obtain ⟨hi1, rv, wsv, hev, hvv, hlv⟩ := use_FInv hu hi
  have hsigu : sig (close th.σs u) = sig (cl ρ η.wit 0 0 u) :=
    sig_WitL hi.2.2.2.1 ρ ho (lt_of_guardT htb hi.2.2.2.2.1)
  have hwcu : wc (cl ρ η.wit 0 0 u) ≠ none := by
    rw [← wc_of_sig hsigu]; exact (Lay_canon hsub hlv).2.2.2.1
  have hna : ∀ n e, cl ρ η.wit 0 0 u ≠ .array (.lit n) e := fun n e h => hwcu (by rw [h]; simp [wc, accs])
  obtain ⟨rt, ws, hea, hv, hl⟩ := peek_VR hi.2.1 hpk
  obtain ⟨ad, c, hws, hsto, hat, hmode, hini⟩ :=
    cell_target (rfl : cellOf (.loc (.rgn r) u) = some (.rgn r, u)) (Fd_noarr fun h => hwcu (by simp [wc, h])) hv
  obtain ⟨pw, rfl, hpw⟩ := map_singleton hws
  replace hmode := TermC1.rgnV hmo _ pw ad c hea hpw hsto hmode
  rw [modeIni_ne_own (show Mode.rgn r ≠ .own from fun h => by cases h)] at hini
  have hsk := hl.2.1
  obtain ⟨μr, ru, rfl, -, hsku⟩ : ∃ μr ru, rt = .loc μr ru ∧ skelM μr = skelM (Mode.rgn r) ∧
      etok (skel ru) = etok (skel (close th.σs u)) := by
    simp only [close, substTs, skel, etok] at hsk
    obtain ⟨μr, ru, rfl, h1, h2⟩ := eskel_eq_loc hsk
    exact ⟨μr, ru, rfl, h1, h2⟩
  have hsig : sig ru = sig (cl ρ η.wit 0 0 u) := by
    have h1 : sig ru = sig (close th.σs u) := sig_of_eskel hsku
    rw [h1]; exact hsigu
  have hlr := pub_accs hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl ho hea rfl
  obtain ⟨us, hus⟩ : ∃ us, accs ru = some us := by
    have : wc ru ≠ none := by rw [wc_of_sig hsig]; exact hwcu
    cases h : accs ru with
    | none => simp [wc, h] at this
    | some us => exact ⟨us, rfl⟩
  have husU : accs (cl ρ η.wit 0 0 u) = some us := by rw [← hlr, hus]
  -- the read half (`tstepM_loadCellLoc`)
  have hL : loadUnits g.arch pw ad false us 0 (stOf mem pairs th) ≠ [] ∧
      ∀ s1 old, (s1, old) ∈ loadUnits g.arch pw ad false us 0 (stOf mem pairs th) → PromAbove s1 →
        VR ρ η u (shp ru) old ∧ Lay th.σs u ru old ∧ MemInv g (CE η) s1 := by
    by_cases hown : c.owner = some η.tid
    · obtain ⟨us', hus', ⟨r0, hr0⟩, hld, -⟩ := locLoadI (arch := g.arch) (pw := pw) (acq := false)
        (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hm.2.2.2.2.2.1 hsto hown hat hini hna
        (fun _ f hf hns => by
          simp only [ModeOK] at hmode
          obtain ⟨f0, hf0, hsf⟩ := hmode
          obtain rfl : f0 = f := Option.some.inj (hf0.symm.trans hf)
          rcases hsf with hs | hs
          · exact absurd hs hns
          · exact hs pw (by simp)) hsku hsig
          (cell_lyt hl.2.2.2.2 rfl rfl).2
            (accs_rtW hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 ho htb (cell_lyt hl.2.2.2.2 rfl rfl).2)
      obtain rfl : us' = us := Option.some.inj (hus'.symm.trans hus)
      refine ⟨List.ne_nil_of_mem hr0, fun s1 old h hp => ?_⟩
      obtain ⟨hvr, hlay', f1, f2, f3, f4, f5⟩ := hld (s1, old) h hp
      exact ⟨hvr, hlay', MemInv_load hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h) (loadUnits_vWr _ _ _ _ h)⟩
    · simp only [ModeOK] at hmode
      obtain ⟨f, hf, hsf⟩ := hmode
      have hfv : f ≤ pw.view := by
        rcases hsf with hs | hs
        · rcases hm.2.2.2.2.2.2.2.2.1.1 ad.label hs with ⟨c0, h1, h2⟩ | ⟨h1, -⟩
          · refine absurd ?_ hown
            have h1' : η.sto ad.label = some c0 := h1
            rw [hsto] at h1'
            rw [Option.some.inj h1']; exact h2
          · have h1' : η.sto ad.label = none := h1
            rw [hsto] at h1'; cases h1'
        · exact hs pw (by simp)
      obtain ⟨⟨r0, hr0⟩, hval0, -⟩ := pubLoadAt (arch := g.arch) (pw := pw) (acq := false)
        hm.2.2.2.2.2.2.2.2.1 hm.2.2.2.2.2.2.1 hsto hown hf hfv hat hini hna husU
      refine ⟨List.ne_nil_of_mem hr0, fun s' wsr hl' hpr0 => ?_⟩
      obtain ⟨q, hq, hle⟩ := hval0 (s', wsr) hl' hpr0
      have hrl : wsr.length = nWords us := (Reads_unit us 0 wsr (loadUnits_reads us 0 _ (s', wsr) hl' [] (fun _ _ h => by cases h))).1
      obtain ⟨f1, f2, f3, f4⟩ := loadUnits_frame us 0 _ (s', wsr) hl'
      obtain ⟨hvr0, hV0⟩ := ValOf.env hq
      have hvr : VR ρ η u (shp ru) wsr := by
        rw [shp_of_sig hsig]
        exact (VR_close hE.2.1 ρ u [] 0 ρ (fun _ => 0) (shp (cl ρ η.wit 0 0 u)) wsr (fun k => rfl)
          (fun k hk => absurd hk (Nat.not_lt_zero _))).2 (VR_up _ _ q wsr hle hvr0)
      have hlay' : Lay th.σs u ru wsr :=
        ⟨fun us' h => by rw [hus] at h; cases h; exact hrl, hsku, by simp [wc, hus],
          Valid_of_sig hsig.symm (Valid_vals _ q wsr hle.vals hV0), (cell_lyt hl.2.2.2.2 rfl rfl).2⟩
      refine ⟨hvr, hlay', ?_⟩
      refine MemInv_loadF hm f1 f2 (fun l c1 hc1 ho1 o => loadUnits_cohF us 0 _ (s', wsr) hl' ⟨l, o⟩ ?_)
        f3 f4 (loadUnits_relSt _ _ _ _ hl') (loadUnits_vWr _ _ _ _ hl')
        (fun l B hB o => loadUnits_cohF us 0 _ (s', wsr) hl' ⟨l, o⟩ (fun he => by
          have h0 := (hm.2.2.2.2.2.2.2.2.2.1.2.2 l B hB).1
          have hl0 : l = ad.label := he
          rw [hl0] at h0; have h1 : η.sto ad.label = none := h0; rw [hsto] at h1; cases h1))
      intro hle'
      have hl'' : l = ad.label := hle'
      have h1 : η.sto l = some c1 := hc1
      rw [hl'', hsto] at h1
      exact hown (by rw [Option.some.inj h1]; exact ho1)
  obtain ⟨-, hld⟩ := hL
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw ad false us 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        (storeUnits g.k g.arch pw ad false us wsv 0 s1).map fun s2 => (s2, ru, old)).map
        fun (sQ, t, ws) => (sQ.mem, sQ.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } sQ) := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus]
  rw [key]
  intro r0 hr hpr0
  obtain ⟨s1, old, h1, hp1, henv, hst⟩ := xchg_out hr hpr0
  obtain ⟨hvr, hlay, -⟩ := hld s1 old h1 hp1
  have hc1 := hsto1 _ _ hsto
  obtain ⟨hwc, hval⟩ := wc_valid_of_lay hlay
  refine ⟨x, ru, old, henv, hst, ?_, lbl_load hE.2.1 hPf hBx hsig hvr hwc hval⟩
  exact valB_load hc1 (hLay _ _ hc1) hat hini hna husU hG hsig h1 hp1 ga N

end V5

/-- **The K-2a dispatch** (all terms but `ret`). -/
theorem stepOK_disp {p : Prog} {g : G} {E : TEnv} {sto : Sto} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ga : AllocLabel} {r : Memory × List Ts × TTh} {Gl : AllocLabel → Prop}
    (hp : g.p = p) (hP : ProgT p) (hI : ThInvE p E th) (hM : MemInv g E (stOf mem pairs th))
    (h1 : ∀ l c, E.sto l = some c → sto l = some c) (hLay : ∀ l c, sto l = some c → LayT c.ty)
    (hG : GranuleWP sto mem pairs th.promises)
    (hPf : ∀ l f, E.pfr l = some f → Gl l) (hBx : ∀ l B, E.box l = some B → Gl l)
    (hsc : ScopeOK p th) (hnr : ∀ a, th.term ≠ .ret a)
    (hfa : ∀ l, FreshIn g th.nalloc r.2.2.nalloc l → l ≠ ga)
    (hGf : ∀ l, FreshIn g th.nalloc r.2.2.nalloc l →
      (∃ b ∈ r.2.2.env, ∃ w ∈ pubWords b.2.1 b.2.2, Names l w) → Gl l)
    (hnp : ¬ PubAt th ga) (hGp : ∀ l, PubAt th l → Gl l)
    (hArm : ∀ a x e₁ y e₂, th.term = .case a x e₁ y e₂ → ∀ ra rb ws, evalAt th.env a = some (.sum ra rb, ws) →
      (Ty.sum ra rb).tier = .boxed → TermK2aSum.BoxArmOK g (stOf mem pairs th) sto ga Gl Gl th (.sum ra rb) ws)
    (hr : r ∈ tstep g mem pairs th) (hA : PromAbove (stOf r.1 r.2.1 r.2.2)) :
    StepOK sto (stOf mem pairs th) ga Gl Gl th r.2.2 := by
  have hI0 := hI
  obtain ⟨ρ, η, cx, rfl, hE, hTK, htv, hi, -⟩ := hI
  have hT := hTK.1
  have hsd := hsc ρ η cx hE hTK htv hi
  have hT0 := hT
  generalize ht : th.term = t0 at hT0 hsd
  cases hT0 with
  | let_ hop _ =>
    cases hop with
    | atom => exact stepOK_op ht rfl (fun _ h => valB_atom h) r hr
    | pair => exact stepOK_op ht rfl (fun _ h => valB_pair hI0 ht h) r hr
    | addS => exact stepOK_op ht rfl (fun _ h => valB_add h) r hr
    | addI => exact stepOK_op ht rfl (fun _ h => valB_add h) r hr
    | subS => exact stepOK_op ht rfl (fun _ h => valB_sub h) r hr
    | pack => exact stepOK_op ht rfl (fun _ h => valB_pack hI0 ht h) r hr
    | packT => exact stepOK_op ht rfl (fun _ h => valB_packT hI0 ht h) r hr
    | rem => exact stepOK_op ht rfl (fun _ h => valB_rem h) r hr
    | nameI => exact stepOK_op ht rfl (fun _ h => valB_nameI h) r hr
    | bits => exact stepOK_op ht rfl (fun _ h => valB_bits h) r hr
    | bit1 => exact stepOK_op ht rfl (fun _ h => valB_bit1 h) r hr
    | vmatch => exact stepOK_op ht rfl (fun _ h => valB_vmatch h) r hr
    | band => exact stepOK_op ht rfl (fun _ h => valB_band h) r hr
    | cvt => exact stepOK_op ht rfl (fun _ h => valB_cvt h) r hr
    | toInt => exact stepOK_op ht rfl (fun _ h => valB_toInt h) r hr
    | asLanes => exact stepOK_op ht rfl (fun _ h => valB_asLanes h) r hr
    | fop => exact stepOK_op ht rfl (fun _ h => valB_fop h) r hr
    | fcmp => exact stepOK_op ht rfl (fun _ h => valB_fcmp h) r hr
    | fop1 => exact stepOK_op ht rfl (fun _ h => valB_fop1 h) r hr
    | lane => exact stepOK_op ht rfl (fun _ h => valB_lane h) r hr
    | setLane => exact stepOK_op ht rfl (fun _ h => valB_setLane h) r hr
    | inl => exact TermK2aSum.sum_inlTR ht hT hi sto hr hfa hGf hGf
    | inr => exact TermK2aSum.sum_inrTR ht hT hi sto hr hfa hGf hGf
    | new => exact stepOK_op ht rfl (fun _ h => valB_new h) r hr
    | publish | publishBuf => exact TermK2aSum.pub_publish ht hT hi sto hnp hGp hGp r hr
    | intoRgn | intoRgnBuf => exact TermK2aSum.pub_intoRgn ht hT hi sto hnp hGp hGp r hr
    | newBuf => exact stepOK_op ht rfl (fun _ h => valB_newBuf h) r hr
    | idxOwn | idxShared => exact stepOK_op ht rfl (fun _ h => valB_idx h) r hr
    | bufInit => exact stepOK_op ht rfl (fun _ h => valB_bufInit h) r hr
    | null => exact stepOK_op ht rfl (fun _ h => valB_null h) r hr
    | fldOwn | fldShared => exact stepOK_op ht rfl (fun _ h => valB_fld h) r hr
    | fence => exact stepOK_op ht rfl (fun _ h => valB_fence h) r hr
    | zero => exact stepOK_op ht rfl (fun _ h => valB_zero h) r hr
    | spawn => exact stepOK_op ht rfl (fun _ h => by simp [evalOp] at h) r hr
    | spawnI => exact stepOK_op ht rfl (fun _ h => by simp [evalOp] at h) r hr
    | ext => exact stepOK_op ht rfl (fun _ h => by simp [evalOp] at h) r hr
    | isTy => exact stepOK_op ht rfl (fun _ h => valB_isTy hI0 ht h) r hr
    | call => exact stepOK_of_stepB_nil (stepB_call hp hP hI0 ht hr)
    | fnptr => exact stepOK_op ht rfl (fun _ h => valB_fnptr h) r hr
    | callc => exact stepOK_of_stepB_nil (stepB_callc hp hP hI0 ht hr)
    | xchgAt => exact stepOK_of_ldOK (TermK2aRmw.rmw_xchgAt ht hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
    | loadAt => exact stepOK_of_ldOK (TermK2aLdW.ld_at ht hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
    | xchgAtF => exact stepOK_of_ldOK (TermK2aRmw.rmw_xchgAtF ht hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
    | loadAtF => exact stepOK_of_ldOK (TermK2aLdW.ld_atF ht hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
    | ldlw => exact stepOK_of_ldOK (TermK2aLdW.ld_lw ht hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
    | ldl => exact stepOK_of_ldOK (TermK2aLdW.ld_l ht hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
    | stlw => exact stepOK_op ht rfl (fun _ h => valB_stlw h) r hr
    | stl => exact stepOK_op ht rfl (fun _ h => valB_stl h) r hr
    | fold => exact stepOK_op ht rfl (fun _ h => valB_fold hI0 ht h) r hr
    | mkWord => exact stepOK_op ht rfl (fun _ h => valB_mkWord hI0 ht h) r hr
    | mkWordGhost => exact stepOK_op ht rfl (fun _ h => valB_mkWord hI0 ht h) r hr
    | validate => exact stepOK_op ht rfl (fun _ h => valB_validate h) r hr
    | borrow => exact stepOK_op ht rfl (fun _ h => valB_borrow h) r hr
    | freeze => exact stepOK_op ht rfl (fun _ h => valB_freeze h) r hr
    | endBorrow => exact stepOK_op ht rfl (fun _ h => valB_endBorrow h) r hr
    | mkWord2 => exact stepOK_op ht rfl (fun _ h => valB_mkWord2 hI0 ht h) r hr
    | mkEPair => exact stepOK_op ht rfl (fun _ h => valB_mkEPair hI0 ht h) r hr
    | mkTicket => exact stepOK_op ht rfl (fun _ h => valB_mkTicket hI0 ht h) r hr
    | claim => exact stepOK_op ht rfl (fun _ h => valB_claim h) r hr
    | stpGive | stpKeep => exact stepOK_op ht rfl (fun _ h => valB_stp h) r hr
    | storeWordGive | storeWordKeep | storeWordHand | storeOwn | storePub | storeRgn | storeCap =>
        exact stepOK_op ht rfl (fun _ h => valB_store h) r hr
    | ldp hpk =>
        have hs := scope_of hsd (notCap_let (by intros; simp) (by intros; simp) (by intros; simp))
        obtain ⟨μ, u, hteq | hteq, hu⟩ := hs _ hpk
        · rw [hteq] at hpk
          rcases mode_own_or μ with rfl | hμ
          · exact stepOK_of_ldOK
              (TermK2aLdW.ld_pOwn ht hu hpk hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
          · exact stepOK_of_ldOK
              (ld_pNO ht hu hpk hμ hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
        · rw [hteq] at hpk
          exact stepOK_of_ldOK
            (ld_pLocAny ht hu hpk hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
    | fetchCell hpk | fetchEpoch hpk | fetchShare hpk =>
        have hs := scope_of hsd (notCap_let (by intros; simp) (by intros; simp) (by intros; simp))
        obtain ⟨μ, u, hteq | hteq⟩ := hs _ hpk
        · rw [hteq] at hpk
          exact stepOK_of_ldOK (rmw_fetchAny ht hpk hT hi hE htv hM ga Gl r hr hA)
        · rw [hteq] at hpk
          exact stepOK_of_ldOK (rmw_fetchLocAny ht hpk hT hi hE htv hM ga Gl r hr hA)
    | loadWord hpk hw =>
        obtain ⟨μ, hteq | hteq⟩ := wordOf_cases hw <;> subst hteq
        · cases μ with
          | own => exact stepOK_of_ldOK
                    (TermK2aLdW.ld_wordOwn ht hpk hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
          | pub => exact stepOK_of_ldOK
                    (TermK2aLdW.ld_wordPub ht hpk hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
          | rgn r' => exact stepOK_of_ldOK
                        (ld_wordNO ht hpk (fun h => by cases h) hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
        · exact stepOK_of_ldOK
            (ld_wordLocAny ht hpk hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
    | loadRgn hpk hnw hc | loadCap hpk hnw hc | loadTorn hpk hnw hc =>
        rcases cell_cases hc with rfl | rfl
        · exact stepOK_of_ldOK (ld_rgn ht hpk hnw hT hTK.2 hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
        · exact stepOK_of_ldOK (ld_rgnLoc ht hpk hnw hT hTK.2 hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
    | loadOwn hpk hnw hc =>
        rcases cell_cases hc with rfl | rfl
        · exact stepOK_of_ldOK (ld_own ht hpk hnw hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
        · exact stepOK_of_ldOK (ld_loc ht hpk hnw hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
    | loadPub hpk hnw hc =>
        rcases cell_cases hc with rfl | rfl
        · exact stepOK_of_ldOK (ld_pub ht hpk hnw hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
        · exact stepOK_of_ldOK (ld_pubLoc ht hpk hnw hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
    | xchg hpk hx =>
        have hs := scope_of hsd (notCap_let (by intros; simp) (by intros; simp) (by intros; simp))
        cases hx with
        | own _ hc =>
            rcases cell_cases hc with rfl | rfl
            · exact stepOK_of_ldOK
                (TermK2aRmw.rmw_xchgOwn ht hpk hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
            · exact stepOK_of_ldOK
                (TermK2aRmw.rmw_xchgLoc ht hpk hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
        | rgn _ hc =>
            rcases cell_cases hc with rfl | rfl
            · exact stepOK_of_ldOK (rmw_xchgRgnD4 ht hpk hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
            · exact stepOK_of_ldOK (rmw_xchgRgnLocD4 ht hpk hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
  | split => exact stepOK_of_stepB_nil (stepB_split ht hr)
  | unpack => exact stepOK_of_stepB_nil (stepB_unpack ht hr)
  | unpackT => exact stepOK_of_stepB_nil (stepB_unpackT hI0 ht hr)
  | ifnull => exact stepOK_of_stepB_nil (stepB_ifnull ht hr)
  | parity => exact stepOK_of_stepB_nil (stepB_parity ht hr)
  | ifeqPlain | ifeq | ifeqRec | ifeqZero => exact stepOK_of_stepB_nil (stepB_ifeq ht hr)
  | case => exact TermK2aSum.sum_caseTR ht hT hi htv sto (hArm _ _ _ _ _ ht) hr hfa hGf hGf
  | region | regionBuf => exact TermK2aSum.rgn_region ht hT hi sto Gl ga Gl hnp hGp hGp r hr
  | openPub => exact TermK2aSum.rgn_openPub ht hT hi sto Gl ga Gl r hr
  | casCell | casShare | casTake | casEpoch => exact TermK2aRmw.rmw_casWord ht ga Gl r hr hA
  | caspMove | caspTake | caspE | caspBump => exact TermK2aRmw.rmw_casp ht ga Gl r hr hA
  | ret => exact (hnr _ ht).elim
  | tail => exact stepOK_of_stepB_nil (stepB_tail hp hP hI0 ht hr)

end TermK2aDisp
