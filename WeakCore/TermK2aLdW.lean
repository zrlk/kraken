import WeakCore.TermK2aLd

/-!
# K-2a loads: word, pair, lane and buffer loads

Per-operation load contracts (`TermK2aLd.LdOK`) mirroring `TermStep.tstepM_loadWord*`,
`tstepM_ldp*`, `tstepM_ldlw`/`tstepM_ldl` and `tstepM_loadAt`/`tstepM_loadAtF`.  Word, pair and lane
loads bind numbers (shallow-pub types whose words name no label); buffer loads bind a value read
at a component of an own buffer cell (`valB_load`, `lbl_load`).
-/

namespace TermK2aLdW

open CoreLang CoreTerm CoreTyping TermRun TermTv TermSound TermMem TermStep TermPtrRts TermK2aLd
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermClose (cl tb arrFree_cl)

/-! ## 1. Number bindings -/

theorem noName_of_num {w : Word} {n : Nat} (h : w.val = .num n) : ∀ l, ¬ Names l w := by
  intro l hn
  obtain ⟨a', g0, hv, -⟩ := hn
  rw [h] at hv; cases hv

/-- A load binding numbers at a shallow-pub type satisfies the contract. -/
theorem ldOK_num {sto : Sto} {s : St} {a : AllocLabel} {N G : AllocLabel → Prop} {th th' : TTh}
    {x : String} {rt : Ty} {ws : List Word}
    (he : th'.env = (x, rt, ws) :: th.env) (hst : th'.stack = th.stack) (hs : sNo rt = true)
    (h : ∀ w ∈ ws, ∃ n, w.val = .num n) : LdOK sto s a N G th th' := by
  refine ⟨x, rt, ws, he, hst, fun w hw => ?_, fun w hw l hn => ?_⟩
  · rw [pubWords_of_sNo hs] at hw
    obtain ⟨n, hn⟩ := h w hw
    exact TermK2a.newW_of_noName (noName_of_num hn)
  · rw [pubWords_of_sNo hs] at hw
    obtain ⟨n, hn0⟩ := h w hw
    exact absurd hn (noName_of_num hn0 l)

theorem word_nums {ρ : Nat → Nat} {η : TEnv} {r : Idx} {P : Proto} {R : Shp} {ws : List Word}
    (hg : P.ghost = false) (h : VR ρ η (.word r P) R ws) : ∀ w ∈ ws, ∃ n, w.val = .num n := by
  simp only [VR] at h
  obtain ⟨n, hn, -⟩ := h.2 hg
  obtain ⟨w, rfl, hw⟩ := map_singleton hn
  intro w0 h0
  exact ⟨n, by rw [List.mem_singleton.1 h0]; exact hw⟩

theorem pair_nums {ρ : Nat → Nat} {η : TEnv} {t : Ty} {R : Shp} {ws : List Word}
    (ht : (∃ r P, t = .word2 r P) ∨ (∃ r P, t = .epair r P)) (h : VR ρ η t R ws) :
    ∀ w ∈ ws, ∃ n, w.val = .num n := by
  have hn : ∃ n0 n1, ws.map (·.val) = [.num n0, .num n1] := by
    rcases ht with ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩
    · simp only [VR] at h; obtain ⟨-, n0, n1, hn, -⟩ := h; exact ⟨n0, n1, hn⟩
    · simp only [VR] at h; obtain ⟨-, n0, n1, hn⟩ := h; exact ⟨n0, n1, hn⟩
  obtain ⟨n0, n1, hn⟩ := hn
  obtain ⟨w0, l, rfl, h0, hl⟩ := List.map_eq_cons_iff.1 hn
  obtain ⟨w1, rfl, h1⟩ := map_singleton hl
  intro w hw
  rcases List.mem_cons.1 hw with rfl | hw
  · exact ⟨n0, h0⟩
  · exact ⟨n1, by rw [List.mem_singleton.1 hw]; exact h1⟩

/-! ## 2. Protocol word loads -/

/-- **`load` of a protocol word through an own pointer.** -/
theorem ld_wordOwn {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {r : Idx} {P : Proto}
    {e : Expr} (hterm : th.term = .let_ x (.load acq a) e)
    (hpk : cx.peek a = .ok (.ptr .own (.word r P)))
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
  obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, hacc, hown, hsku, hsig⟩ :=
    ownPtr_view hi hpk htv (by simp [Cx.opaqueOK, Ty.guardT])
  have hna : ∀ N e', c.ty ≠ .array (.lit N) e' := fun N e' h => hacc (by rw [h]; simp [accs])
  obtain ⟨us, hus, -, hld, -⟩ := ownLoad (arch := g.arch) (pw := pw) (acq := acq) (s := stOf mem pairs th)
    hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown (Fd_lay hcty).1 (Fd_lay hcty).2.1
    (fun ws => ((Fd_lay hcty).2.2.2 ws).1) (fun R ws => (Fd_VR η hcty).1) hna hsku
    (peek_cell_lyt hi.2.1 hpk hea rfl rfl).2 hsig
    (by rw [(Fd_lay hcty).2.2.1]; exact pub_accs hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl (by simp [Cx.opaqueOK, Ty.guardT]) hea rfl)
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
  obtain ⟨hvr, -⟩ := hld (s', wsr) hl hpr0
  exact ldOK_num rfl rfl rfl (word_nums hg hvr)

/-- **`load` of a protocol word through a `pub` pointer.** -/
theorem ld_wordPub {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {r : Idx} {P : Proto}
    {e : Expr} (hterm : th.term = .let_ x (.load acq a) e)
    (hpk : cx.peek a = .ok (.ptr .pub (.word r P)))
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
  obtain ⟨ru, pw, lab, us, hea, hpw, hus, hsku, -, hld, -⟩ :=
    loadPub_core (acq := acq) (g := g) (mem := mem) (pairs := pairs) hpk
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

/-- **`load` of a protocol word through an own or `pub` locative.** -/
theorem ld_wordLoc {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {μ : Mode} {r : Idx} {P : Proto}
    {e : Expr} (hterm : th.term = .let_ x (.load acq a) e)
    (hpk : cx.peek a = .ok (.loc μ (.word r P))) (hμ : μ = .own ∨ μ = .pub)
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
    locCell (acq := acq) (rel := false) (g := g) (mem := mem) (pairs := pairs) hpk hμ
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

/-! ## 3. Pair loads -/

/-- **`ldp` through an own reference.** -/
theorem ld_pOwn {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x w n0 n1 : String} {acq : Bool} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.ldp acq (.var w) n0 n1) e)
    (hu : (∃ r P, u = .word2 r P) ∨ (∃ r P, u = .epair r P))
    (hpk : cx.peek (.var w) = .ok (.ptr .own u))
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
  obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, hacc, hown, hsku, hsig⟩ := ownPtr_view hi hpk htv hoq
  have hna : ∀ N e', c.ty ≠ .array (.lit N) e' := fun N e' h => hacc (by rw [h]; simp [accs])
  obtain ⟨us, hus, -, hld, -⟩ := ownLoad (arch := g.arch) (pw := pw) (acq := acq) (s := stOf mem pairs th)
    hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown (Fd_lay hcty).1 (Fd_lay hcty).2.1
    (fun ws => ((Fd_lay hcty).2.2.2 ws).1) (fun R ws => (Fd_VR η hcty).1) hna hsku
    (peek_cell_lyt hi.2.1 hpk hea rfl rfl).2 hsig
    (by rw [(Fd_lay hcty).2.2.1]; exact pub_accs hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl hoq hea rfl)
  obtain ⟨hru, hpr⟩ := pair_ru .own hu hsku
  rw [hru] at hus; cases hus
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ⟨lab, 0⟩ acq [.two] 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .prod .int .int, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hpr, addrOf, hpw, ↓reduceIte, List.map_map]; rfl
  rw [key]
  intro r0 hr hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, -⟩ := hld (s', wsr) hl hpr0
  exact ldOK_num rfl rfl rfl (pair_nums hu hvr)

/-- **`ldp` through a `pub` reference.** -/
theorem ld_pPub {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x w n0 n1 : String} {acq : Bool} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.ldp acq (.var w) n0 n1) e)
    (hu : (∃ r P, u = .word2 r P) ∨ (∃ r P, u = .epair r P))
    (hpk : cx.peek (.var w) = .ok (.ptr .pub u))
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
  obtain ⟨ru, pw, lab, us, hea, hpw, hus, hsku, -, hld, -⟩ :=
    loadPub_core (acq := acq) (g := g) (mem := mem) (pairs := pairs) hpk hoq hi hE htv hm
  obtain ⟨hru, hpr⟩ := pair_ru .pub hu hsku
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

/-- **`ldp` through an own or `pub` locative.** -/
theorem ld_pLoc {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x w n0 n1 : String} {acq : Bool} {μ : Mode} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.ldp acq (.var w) n0 n1) e)
    (hu : (∃ r P, u = .word2 r P) ∨ (∃ r P, u = .epair r P))
    (hpk : cx.peek (.var w) = .ok (.loc μ u)) (hμ : μ = .own ∨ μ = .pub)
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
    locCell (acq := acq) (rel := false) (g := g) (mem := mem) (pairs := pairs) hpk hμ hoq
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

/-! ## 4. Lane loads -/

/-- **`ldlw`**: a lane of a word of an own `lanes` buffer, a `fix` number. -/
theorem ld_lw {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b wi jl : At} {e : Expr}
    (hterm : th.term = .let_ x (.ldlw b wi jl) e)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (_hE : EnvOK p η) (htv : TvOK cx) (_hm : MemInv g (CE η) (stOf mem pairs th))
    {sto : Sto} (_hsto1 : ∀ l c, η.sto l = some c → sto l = some c) (_hLay : ∀ l c, sto l = some c → LayT c.ty)
    (_hG : GranuleWP sto mem pairs th.promises) {Gl : AllocLabel → Prop}
    (_hPf : ∀ l f, η.pfr l = some f → Gl l) (_hBx : ∀ l B, η.box l = some B → Gl l)
    (ga : AllocLabel) (N : AllocLabel → Prop) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      LdOK sto (stOf mem pairs th) ga N Gl th r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  cases hop with
  | ldlw hp hbuf hlo hint hlt hltk hpj hij hb =>
  obtain ⟨t, u, n, k, jw, tj, q, hp, hbuf, hlo, hint, hlt, hltk, hpj, hij, hb⟩ : ∃ t u n k jw tj q,
      cx.peek b = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧ IntIdx cx wi jw ∧
      LtI cx jw n ∧ LtI cx jw k ∧ cx.peek jl = .ok tj ∧ (intOf tj).isSome = true ∧
      cx.bind x (.fix q.1 q.2) = .ok c' :=
    ⟨_, _, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk, hpj, hij, hb⟩
  obtain ⟨sg, w⟩ := q
  have hu := lanes_of hlo
  simp only at hu hb
  subst hu
  have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨ti, hpi, hti⟩ := hint
  obtain ⟨rti, wwi, hei, hwi, -⟩ := atom_num hi.2.1 hpi hti
  obtain ⟨oj, hoj⟩ := Option.isSome_iff_exists.1 hij
  obtain ⟨rtj, wj, m, hej, hwj⟩ := atom_int hi.2.1 hpj hoj
  have hJ := hlt ρ hi.1
  have hJk := hltk ρ hi.1
  obtain ⟨rt, pw, ad, c, μr, ur, us, hea, hwv, hbe, hus, -, -, -, -, hsku, -⟩ :=
    slot_viewN (ev ρ jw) hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hJ hJk ho
  obtain ⟨rfl, rfl⟩ := lane_rt hsku hus
  have hni : numOf [wwi] = some (ev ρ jw) := by simp [numOf, hwi]
  have hnj : numOf [wj] = some m := by simp [numOf, hwj]
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw (offs ad (ev ρ jw)) false [.one] 0 (stOf mem pairs th)).filterMap fun (s1, old) =>
        (numOf old).map fun y => (s1, Ty.fix sg w, [cst (.num (laneN w y (m % w.lanes)))])).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hej, hni, hnj, addrOf, hwv, hbe, lanesOf]
  rw [key]
  intro r hr _
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_filterMap] at hr
  obtain ⟨⟨s1, old⟩, -, h2⟩ := hr
  simp only at h2
  obtain ⟨y, hy⟩ : ∃ y, numOf old = some y := by
    cases hn : numOf old with
    | none => simp [hn] at h2
    | some y => exact ⟨y, rfl⟩
  rw [hy, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl, rfl⟩ := h2
  exact ldOK_num rfl rfl rfl (fun w0 h0 => by rw [List.mem_singleton] at h0; subst h0; exact ⟨_, rfl⟩)

/-- **`ldl`**: `ldlw` at word `j / lanes`, lane `j % lanes`. -/
theorem ld_l {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i : At} {e : Expr}
    (hterm : th.term = .let_ x (.ldl b i) e)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (_hE : EnvOK p η) (htv : TvOK cx) (_hm : MemInv g (CE η) (stOf mem pairs th))
    {sto : Sto} (_hsto1 : ∀ l c, η.sto l = some c → sto l = some c) (_hLay : ∀ l c, sto l = some c → LayT c.ty)
    (_hG : GranuleWP sto mem pairs th.promises) {Gl : AllocLabel → Prop}
    (_hPf : ∀ l f, η.pfr l = some f → Gl l) (_hBx : ∀ l B, η.box l = some B → Gl l)
    (ga : AllocLabel) (N : AllocLabel → Prop) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      LdOK sto (stOf mem pairs th) ga N Gl th r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  cases hop with
  | ldl hp hbuf hlo hint hlt hltk hb =>
  obtain ⟨t, u, n, k, j, q, hp, hbuf, hlo, hint, hlt, hltk, hb⟩ : ∃ t u n k j q,
      cx.peek b = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧ IntIdx cx i j ∧
      LtI cx j (.smul q.2.lanes n) ∧ LtI cx j (.smul q.2.lanes k) ∧ cx.bind x (.fix q.1 q.2) = .ok c' :=
    ⟨_, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk, hb⟩
  obtain ⟨sg, w⟩ := q
  have hu := lanes_of hlo
  simp only at hu hb hlt hltk
  subst hu
  have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨ti, hpi, hti⟩ := hint
  obtain ⟨rti, wwi, hei, hwi, -⟩ := atom_num hi.2.1 hpi hti
  have hJ0 : ev ρ j < w.lanes * ev ρ n := by simpa [ev] using hlt ρ hi.1
  have hJk0 : ev ρ j < w.lanes * ev ρ k := by simpa [ev] using hltk ρ hi.1
  have hJ : ev ρ j / w.lanes < ev ρ n :=
    (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJ0)
  have hJk : ev ρ j / w.lanes < ev ρ k :=
    (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJk0)
  obtain ⟨rt, pw, ad, c, μr, ur, us, hea, hwv, hbe, hus, -, -, -, -, hsku, -⟩ :=
    slot_viewN (ev ρ j / w.lanes) hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hJ hJk ho
  obtain ⟨rfl, rfl⟩ := lane_rt hsku hus
  have hni : numOf [wwi] = some (ev ρ j) := by simp [numOf, hwi]
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw (offs ad (ev ρ j / w.lanes)) false [.one] 0 (stOf mem pairs th)).filterMap
        fun (s1, old) => (numOf old).map fun y => (s1, Ty.fix sg w, [cst (.num (laneN w y (ev ρ j % w.lanes)))])).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hni, addrOf, hwv, hbe, lanesOf]
  rw [key]
  intro r hr _
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_filterMap] at hr
  obtain ⟨⟨s1, old⟩, -, h2⟩ := hr
  simp only at h2
  obtain ⟨y, hy⟩ : ∃ y, numOf old = some y := by
    cases hn : numOf old with
    | none => simp [hn] at h2
    | some y => exact ⟨y, rfl⟩
  rw [hy, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl, rfl⟩ := h2
  exact ldOK_num rfl rfl rfl (fun w0 h0 => by rw [List.mem_singleton] at h0; subst h0; exact ⟨_, rfl⟩)

/-! ## 5. Buffer loads -/

/-- **`loadAt`**: a load at slot `j` of an own buffer. -/
theorem ld_at {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i : At} {e : Expr}
    (hterm : th.term = .let_ x (.loadAt b i) e)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    {sto : Sto} (hsto1 : ∀ l c, η.sto l = some c → sto l = some c) (hLay : ∀ l c, sto l = some c → LayT c.ty)
    (hG : GranuleWP sto mem pairs th.promises) {Gl : AllocLabel → Prop}
    (hPf : ∀ l f, η.pfr l = some f → Gl l) (hBx : ∀ l B, η.box l = some B → Gl l)
    (ga : AllocLabel) (N : AllocLabel → Prop) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      LdOK sto (stOf mem pairs th) ga N Gl th r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  cases hop with
  | loadAt hp hbuf hint hlt hltk _ hb =>
  obtain ⟨t, u, n, k, j, hp, hbuf, hint, hlt, hltk, hb⟩ : ∃ t u n k j, cx.peek b = .ok t ∧
      bufOf t = some (.own, n, u, k) ∧ IntIdx cx i j ∧ LtI cx j n ∧ LtI cx j k ∧ cx.bind x u = .ok c' :=
    ⟨_, _, _, _, _, hp, hbuf, hint, hlt, hltk, hb⟩
  obtain ⟨rt, w, ad, c, μr, ur, us, rti, wi, hea, hwv, hei, hj, hbe, hus, hsto, hat, hmode, hini, hsku, hsig, htbS, -⟩ :=
    slot_view hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk (bind_opaqueOK hb)
  have haf' : (cl ρ η.wit 0 0 u).arrFree = true := arrFree_cl hi.2.2.2.2.2.2.1.af u 0 0 (bind_arrFree hb)
  have hna : ∀ N e', cl ρ η.wit 0 0 u ≠ .array (.lit N) e' := fun N e' h => by
    rw [h] at haf'; simp [Ty.arrFree] at haf'
  have hacr : accs ur = accs (cl ρ η.wit 0 0 u) :=
    accs_rtW hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 (bind_opaqueOK hb) htbS (peek_buf_lyt hi.2.1 hp hbuf hea hbe).2
  obtain ⟨us', hus', -, hld, -⟩ := locLoad (ad := offs ad (ev ρ j * nWords us)) (arch := g.arch) (pw := w) (acq := false)
    (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hmode hat hini hna hsku hsig
      (peek_buf_lyt hi.2.1 hp hbuf hea hbe).2 hacr
  rw [hus] at hus'; cases hus'
  have key : tstep g mem pairs th =
      (loadUnits g.arch w (offs ad (ev ρ j * nWords us)) false us 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, ur, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hj, addrOf, hwv, hbe, hus, List.map_map]; rfl
  rw [key]
  intro r hr hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl', rfl⟩ := hr
  obtain ⟨hvr, hlay, -⟩ := hld (s', wsr) hl' hpr0
  have hUa : accs (cl ρ η.wit 0 0 u) = some us := by rw [← hacr]; exact hus
  have hc1 := hsto1 _ _ hsto
  obtain ⟨hwc, hval⟩ := wc_valid_of_lay hlay
  refine ⟨x, ur, wsr, rfl, rfl, ?_, lbl_load hE.2.1 hPf hBx hsig hvr hwc hval⟩
  exact valB_load (ad := offs ad (ev ρ j * nWords us)) hc1 (hLay _ _ hc1) hat hini hna hUa hG hsig hl' hpr0 ga N

/-- **`loadAtF`**: a load at field path `q` of slot `j` of an own buffer. -/
theorem ld_atF {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i : At} {q : List Nat} {e : Expr}
    (hterm : th.term = .let_ x (.loadAtF b i q) e)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    {sto : Sto} (hsto1 : ∀ l c, η.sto l = some c → sto l = some c) (hLay : ∀ l c, sto l = some c → LayT c.ty)
    (hG : GranuleWP sto mem pairs th.promises) {Gl : AllocLabel → Prop}
    (hPf : ∀ l f, η.pfr l = some f → Gl l) (hBx : ∀ l B, η.box l = some B → Gl l)
    (ga : AllocLabel) (N : AllocLabel → Prop) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      LdOK sto (stOf mem pairs th) ga N Gl th r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  cases hop with
  | loadAtF hp hbuf hct hop hint hlt hltk _ hb =>
  obtain ⟨t, u, c, n, k, j, hp, hbuf, hct, hop, hint, hlt, hltk, hb⟩ : ∃ t u c n k j, cx.peek b = .ok t ∧
      bufOf t = some (.own, n, u, k) ∧ compTy u q = some c ∧ cx.opaqueOK u = true ∧ IntIdx cx i j ∧
      LtI cx j n ∧ LtI cx j k ∧ cx.bind x c = .ok c' :=
    ⟨_, _, _, _, _, _, hp, hbuf, hct, hop, hint, hlt, hltk, hb⟩
  obtain ⟨rt, w, ad, cc, μr, ur, us, rti, wi, hea, hwv, hei, hj, hbe, hus, hsto, hat, hmode, -, hsku, hsig, htbS, hiniF⟩ :=
    slot_view hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk hop
  obtain ⟨cR, o, hco, hskc, hsgc, -, hato⟩ := compOff_rt q u c ur us hct hsku hsig hus
  have haf' : (cl ρ η.wit 0 0 c).arrFree = true := arrFree_cl hi.2.2.2.2.2.2.1.af c 0 0 (bind_arrFree hb)
  have hna : ∀ N e', cl ρ η.wit 0 0 c ≠ .array (.lit N) e' := fun N e' h => by
    rw [h] at haf'; simp [Ty.arrFree] at haf'
  have hat' : AtOff cc.ty (offs ad (ev ρ j * nWords us + o)).offset (cl ρ η.wit 0 0 c) := by
    have h2 := AtOff_trans hat hato
    simpa [offs, Nat.add_assoc] using h2
  have hlc := compOff_lyt q u c ur cR o hct hsku (peek_buf_lyt hi.2.1 hp hbuf hea hbe).2 hco
  have hacr : accs cR = accs (cl ρ η.wit 0 0 c) :=
    accs_rtW hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 (bind_opaqueOK hb) (tb_compTy q u c hct htbS) hlc
  have hiniC := hiniF o _ hato
  obtain ⟨cs, hcs, -, hld, -⟩ := locLoad (ad := offs ad (ev ρ j * nWords us + o)) (arch := g.arch) (pw := w)
    (acq := false) (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hmode hat'
      hiniC hna hskc hsgc hlc hacr
  have key : tstep g mem pairs th =
      (loadUnits g.arch w (offs ad (ev ρ j * nWords us + o)) false cs 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, cR, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hj, addrOf, hwv, hbe, hus, hco, hcs, List.map_map]; rfl
  rw [key]
  intro r hr hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl', rfl⟩ := hr
  obtain ⟨hvr, hlay, -⟩ := hld (s', wsr) hl' hpr0
  have hUa : accs (cl ρ η.wit 0 0 c) = some cs := by rw [← hacr]; exact hcs
  have hc1 := hsto1 _ _ hsto
  obtain ⟨hwc, hval⟩ := wc_valid_of_lay hlay
  refine ⟨x, cR, wsr, rfl, rfl, ?_, lbl_load hE.2.1 hPf hBx hsgc hvr hwc hval⟩
  exact valB_load (ad := offs ad (ev ρ j * nWords us + o)) hc1 (hLay _ _ hc1) hat' hiniC hna hUa hG hsgc hl' hpr0 ga N

end TermK2aLdW

#print axioms TermK2aLdW.ld_wordOwn
#print axioms TermK2aLdW.ld_wordPub
#print axioms TermK2aLdW.ld_wordLoc
#print axioms TermK2aLdW.ld_pOwn
#print axioms TermK2aLdW.ld_pPub
#print axioms TermK2aLdW.ld_pLoc
#print axioms TermK2aLdW.ld_lw
#print axioms TermK2aLdW.ld_l
#print axioms TermK2aLdW.ld_at
#print axioms TermK2aLdW.ld_atF
