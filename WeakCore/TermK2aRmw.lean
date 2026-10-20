import WeakCore.TermK2aLd

/-!
# K-2a read-modify-writes: per-operation binding contracts

`xchg` (own pointer, own locative, slot, slot field) binds the old component value it read:
its plain load is `TermK2aLd.valB_load` at the state after the load (`PromAbove` there from the
step's, `storeUnits_promAbove`).  `fetch` binds the number it read (no label).  `cas`/`casp`
bind `Unit` with no words on success and nothing on failure: their contract holds of every
outcome, typed or not (`cas_shape`, `casp_shape`).
-/

namespace TermK2aRmw

open CoreLang CoreTerm CoreTyping TermRun TermTv TermSound TermMem TermStep TermPtrRts TermK2aLd
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermClose (cl tb arrFree_cl)

/-! ## 1. Generic contracts -/

/-- Words naming nothing count only words naming nothing. -/
theorem noName_pub {R : Ty} {ws : List Word} (h : ∀ w ∈ ws, ∀ l, ¬ Names l w) :
    ∀ w ∈ pubWords R ws, ∀ l, ¬ Names l w := by
  intro w hw l hn
  obtain ⟨i, w0, -, hi, hn0, -⟩ := TermPubPos.pubWords_pos hw hn
  exact h w0 (List.mem_of_getElem? hi) l hn0

/-- A step binding one value of words naming nothing. -/
theorem ldOK_noName {sto : Sto} {s : St} {a : AllocLabel} {N G : AllocLabel → Prop} {th thQ : TTh}
    {x : String} {rt : Ty} {ws : List Word}
    (he : thQ.env = (x, rt, ws) :: th.env) (hst : thQ.stack = th.stack) (h : ∀ w ∈ ws, ∀ l, ¬ Names l w) :
    LdOK sto s a N G th thQ :=
  ⟨x, rt, ws, he, hst, fun w hw => TermK2a.newW_of_noName (noName_pub h w hw),
    fun w hw l hn => absurd hn (noName_pub h w hw l)⟩

/-- A step binding nothing new. -/
theorem stepOK_same {sto : Sto} {s : St} {a : AllocLabel} {N Gl : AllocLabel → Prop} {th thQ : TTh}
    (he : thQ.env = th.env) (hst : thQ.stack = th.stack) : StepOK sto s a N Gl th thQ := by
  have hb : TermK2a.Binds thQ = TermK2a.Binds th := by unfold TermK2a.Binds; rw [he, hst]
  exact ⟨fun b h => .inl (hb ▸ h), fun b h => .inl (hb ▸ h)⟩

/-- A number word names nothing. -/
theorem noName_num {ws : List Word} {n : Nat} (h : ws.map (·.val) = [.num n]) :
    ∀ w ∈ ws, ∀ l, ¬ Names l w := by
  intro w hw l hn
  obtain ⟨aQ, g, e, -⟩ := hn
  cases ws with
  | nil => cases hw
  | cons w0 rest =>
    cases rest with
    | cons _ _ => simp at h
    | nil =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
      rw [List.mem_singleton] at hw
      subst hw
      rw [h] at e
      cases e

/-! ## 2. `cas` / `casp` -/

/-- **What a `cas` step does to the bindings**: failure keeps them, success binds `Unit`. -/
theorem cas_shape {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {acq rel : Bool} {w e v : At}
    {t : String} {ok fail : Expr} (hterm : th.term = .cas acq rel w e v t ok fail) :
    ∀ r ∈ tstep g mem pairs th,
      (r.2.2.env = th.env ∨ r.2.2.env = (t, .unit, []) :: th.env) ∧ r.2.2.stack = th.stack := by
  intro r hr
  unfold tstep at hr
  rw [hterm] at hr
  simp only at hr
  split at hr
  · split at hr
    · rw [List.mem_map] at hr
      obtain ⟨⟨memQ, thQ⟩, -, rfl⟩ := hr
      simp only
      split
      · exact ⟨.inr rfl, rfl⟩
      · exact ⟨.inl rfl, rfl⟩
    · simp at hr
  · simp at hr

/-- **What a `casp` step does to the bindings**: failure keeps them, success binds `Unit`. -/
theorem casp_shape {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {acq rel : Bool}
    {w e0 e1 v0 v1 : At} {t : String} {ok fail : Expr}
    (hterm : th.term = .casp acq rel w e0 e1 v0 v1 t ok fail) :
    ∀ r ∈ tstep g mem pairs th,
      (r.2.2.env = th.env ∨ r.2.2.env = (t, .unit, []) :: th.env) ∧ r.2.2.stack = th.stack := by
  intro r hr
  unfold tstep at hr
  rw [hterm] at hr
  simp only at hr
  split at hr
  · split at hr
    · rw [List.mem_map] at hr
      obtain ⟨⟨memQ, pairsQ, thQ⟩, -, rfl⟩ := hr
      simp only
      split
      · exact ⟨.inr rfl, rfl⟩
      · exact ⟨.inl rfl, rfl⟩
    · simp at hr
  · simp at hr

/-- The contract of a step of the `cas`/`casp` shape. -/
theorem stepOK_casLike {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {t : String}
    (hsh : ∀ r ∈ tstep g mem pairs th,
      (r.2.2.env = th.env ∨ r.2.2.env = (t, .unit, []) :: th.env) ∧ r.2.2.stack = th.stack)
    {sto : Sto} {Gl : AllocLabel → Prop} (ga : AllocLabel) (N : AllocLabel → Prop) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      StepOK sto (stOf mem pairs th) ga N Gl th r.2.2 := by
  intro r hr _
  obtain ⟨he | he, hst⟩ := hsh r hr
  · exact stepOK_same he hst
  · exact stepOK_of_ldOK (ldOK_noName he hst (fun w hw => by cases hw))

/-- **`cas` on a protocol word** (own or `pub` pointer). -/
theorem rmw_casWord {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {acq rel : Bool} {w e v : At}
    {t : String} {ok fail : Expr} (hterm : th.term = .cas acq rel w e v t ok fail)
    {sto : Sto} {Gl : AllocLabel → Prop} (ga : AllocLabel) (N : AllocLabel → Prop) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      StepOK sto (stOf mem pairs th) ga N Gl th r.2.2 :=
  stepOK_casLike (cas_shape hterm) ga N

/-- **`cas` on a `pub` one-word cell.** -/
theorem rmw_casCell {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {acq rel : Bool} {w e v : At}
    {t : String} {ok fail : Expr} (hterm : th.term = .cas acq rel w e v t ok fail)
    {sto : Sto} {Gl : AllocLabel → Prop} (ga : AllocLabel) (N : AllocLabel → Prop) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      StepOK sto (stOf mem pairs th) ga N Gl th r.2.2 :=
  stepOK_casLike (cas_shape hterm) ga N

/-- **`cas` on a protocol word through a locative.** -/
theorem rmw_casWordLoc {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {acq rel : Bool} {w e v : At}
    {t : String} {ok fail : Expr} (hterm : th.term = .cas acq rel w e v t ok fail)
    {sto : Sto} {Gl : AllocLabel → Prop} (ga : AllocLabel) (N : AllocLabel → Prop) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      StepOK sto (stOf mem pairs th) ga N Gl th r.2.2 :=
  stepOK_casLike (cas_shape hterm) ga N

/-- **`cas` on a `pub` one-word cell through a locative.** -/
theorem rmw_casCellLoc {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {acq rel : Bool} {w e v : At}
    {t : String} {ok fail : Expr} (hterm : th.term = .cas acq rel w e v t ok fail)
    {sto : Sto} {Gl : AllocLabel → Prop} (ga : AllocLabel) (N : AllocLabel → Prop) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      StepOK sto (stOf mem pairs th) ga N Gl th r.2.2 :=
  stepOK_casLike (cas_shape hterm) ga N

/-- **`casp`** (pointer). -/
theorem rmw_casp {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {acq rel : Bool}
    {w e0 e1 v0 v1 : At} {t : String} {ok fail : Expr}
    (hterm : th.term = .casp acq rel w e0 e1 v0 v1 t ok fail)
    {sto : Sto} {Gl : AllocLabel → Prop} (ga : AllocLabel) (N : AllocLabel → Prop) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      StepOK sto (stOf mem pairs th) ga N Gl th r.2.2 :=
  stepOK_casLike (casp_shape hterm) ga N

/-- **`casp`** (locative). -/
theorem rmw_caspLoc {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {acq rel : Bool}
    {w e0 e1 v0 v1 : At} {t : String} {ok fail : Expr}
    (hterm : th.term = .casp acq rel w e0 e1 v0 v1 t ok fail)
    {sto : Sto} {Gl : AllocLabel → Prop} (ga : AllocLabel) (N : AllocLabel → Prop) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      StepOK sto (stOf mem pairs th) ga N Gl th r.2.2 :=
  stepOK_casLike (casp_shape hterm) ga N

/-! ## 3. `fetch` -/

/-- **A fetch-op binds the number it read** (`fetch_core`'s step, with `PromAbove` after the load
from the step's). -/
theorem fetch_coreK {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {x : String} {o : FetchOp} {acq rel : Bool} {a v : At} {e : Expr}
    {ad : Address} {pw nw : Word} {rt rv : Ty} {dd : Nat}
    (hterm : th.term = .let_ x (.fetch o acq rel a v) e)
    (hea : evalAt th.env a = some (rt, [pw])) (haddr : addrOf pw = some ad)
    (hev : evalAt th.env v = some (rv, [nw])) (hnw : nw.val = .num dd)
    (hQ : ∀ s1 ws, (s1, ws) ∈ loadUnits g.arch pw ad acq [.one] 0 (stOf mem pairs th) → PromAbove s1 →
      ∃ n, ws.map (·.val) = [.num n])
    {sto : Sto} {G0 : AllocLabel → Prop} (ga : AllocLabel) (N : AllocLabel → Prop) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      LdOK sto (stOf mem pairs th) ga N G0 th r.2.2 := by
  have hd : dataE 1 nw = .const nw.val := by simp [dataE, hnw]
  have key : tstep g mem pairs th =
      (Promises.stepRmw g.k g.arch mem pairs (mth (stOf mem pairs th) pw nw nw) 1 ad o.kind
          (dataE 1 nw) [0] acq rel).map fun (memQ, thQ) =>
        (memQ, pairs, withS { th with term := e, env := (x, fetchRtTy rt, [thQ.regs 1]) :: th.env }
          ⟨memQ, pairs, thQ.vs, thQ.promises, th.nalloc, th.undefs + countUndef [thQ.regs 1]⟩) := by
    simp only [tstep, hterm, evalOp, hea, hev, haddr, List.map_map]; rfl
  rw [key]
  intro r hr hpr
  rw [List.mem_map] at hr
  obtain ⟨⟨memQ, thQ⟩, hin, rfl⟩ := hr
  obtain ⟨s1, rd, hl1, hrd, s2, hs2, hsame⟩ :=
    stepRmw_splitF (s := stOf mem pairs th) (FetchOp.kind_isFetch o) hd hin
  have hp2 : PromAbove s2 :=
    PromAbove_lockS (s := setRel s2 (lockR g.arch (stOf mem pairs th) s1).vs) (PromAbove_same hsame (fun t ht m hm => hpr t ht m hm))
  have hp1Q : PromAbove (bumpRel (lockR g.arch (stOf mem pairs th) s1) _) := storeUnits_promAbove hs2 hp2
  have hp1 : PromAbove s1 := fun t ht m hm => hp1Q t ht m hm
  obtain ⟨n, hn⟩ := hQ s1 [rd] hl1 hp1
  rw [← hrd] at hn
  exact ldOK_noName rfl rfl (noName_num hn)

/-- **`fetch` through an own or `pub` pointer**: the old value bound is a number. -/
theorem rmw_fetch {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {o : FetchOp} {acq rel : Bool} {a v : At}
    {e : Expr} {μ : Mode} {u : Ty}
    (hterm : th.term = .let_ x (.fetch o acq rel a v) e)
    (hpk : cx.peek a = .ok (.ptr μ u)) (hμ : μ = .own ∨ μ = .pub)
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
      obtain ⟨rfl, -⟩ := hc
      rcases hμ with h | h <;> cases h
  | fetchEpoch hp hw hep _ hj heq _hb =>
    rw [hpk] at hp; cases hp
    cases u <;> simp [wordOf] at hw
    obtain ⟨rfl, rfl⟩ := hw
    rename_i r P
    have hpwf := wordRef_pwf hpk (.inl rfl) hμ hi hE htv hm
    have hg : P.ghost = false := by
      have := pwf_epochOK hpwf hep
      unfold epochOK at this; simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
      exact this.1.2
    obtain ⟨lab, pw, μQ, rQ, hea, hpw, -, hcell⟩ :=
      wordCellF (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk hμ hg hi hE htv hm
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
      wordCellF (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk hμ hg hi hE htv hm
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

/-- **`fetch` through an own or `pub` locative**: the old value bound is a number. -/
theorem rmw_fetchLoc {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {o : FetchOp} {acq rel : Bool} {a v : At}
    {e : Expr} {μ : Mode} {u : Ty}
    (hterm : th.term = .let_ x (.fetch o acq rel a v) e)
    (hpk : cx.peek a = .ok (.loc μ u)) (hμ : μ = .own ∨ μ = .pub)
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
        locCell (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk hμ
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
      obtain ⟨rfl, -⟩ := hc
      rcases hμ with h | h <;> cases h
  | fetchEpoch hp hw hep _ hj heq _hb =>
    rw [hpk] at hp; cases hp
    cases u <;> simp [wordOf] at hw
    obtain ⟨rfl, rfl⟩ := hw
    rename_i r P
    have hpwf := wordRef_pwf hpk (.inr rfl) hμ hi hE htv hm
    have hg : P.ghost = false := by
      have := pwf_epochOK hpwf hep
      unfold epochOK at this; simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
      exact this.1.2
    have hus1 : accs (cl ρ η.wit 0 0 (.word r P)) = some [.one] := by simp [cl, accs, hg]
    obtain ⟨ad, pw, μr, ru, hea, haddr, -, hsku, -, -, hld, -, -⟩ :=
      locCell (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk hμ
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
      locCell (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk hμ
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

/-! ## 4. `xchg` -/

/-- An outcome of a load-then-store step: the state after the load, the value read, and
`PromAbove` after the load from the step's (`storeUnits_promAbove`). -/
theorem xchg_out {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {pw : Word} {ad : Address}
    {us : List Acc} {wsv : List Word} {ru : Ty} {x : String} {e : Expr}
    {r : Memory × List Ts × TTh}
    (hr : r ∈ ((loadUnits g.arch pw ad false us 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        (storeUnits g.k g.arch pw ad false us wsv 0 s1).map fun s2 => (s2, ru, old)).map
        fun (sQ, t, ws) => (sQ.mem, sQ.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } sQ))
    (hpa : PromAbove (stOf r.1 r.2.1 r.2.2)) :
    ∃ s1 old, (s1, old) ∈ loadUnits g.arch pw ad false us 0 (stOf mem pairs th) ∧ PromAbove s1 ∧
      r.2.2.env = (x, ru, old) :: th.env ∧ r.2.2.stack = th.stack := by
  rw [List.mem_map] at hr
  obtain ⟨⟨sQ, tQ, wsQ⟩, hr, rfl⟩ := hr
  rw [List.mem_flatMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  rw [List.mem_map] at h2
  obtain ⟨s2, hs2, he2⟩ := h2
  simp only [Prod.mk.injEq] at he2
  obtain ⟨rfl, rfl, rfl⟩ := he2
  exact ⟨s1, old, h1, storeUnits_promAbove hs2 hpa, rfl, rfl⟩

/-- **`xchg` at an own pointer**: the old value bound is what the plain load read. -/
theorem rmw_xchgOwn {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a v : At} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.xchg a v) e)
    (hpk : cx.peek a = .ok (.ptr .own u))
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
  | let_ hop _ =>
  cases hop with
  | xchg hp hx hu hsub hb =>
  obtain ⟨t, uQ, o, tv, c₁, hp, hx, hu, hsub, hb⟩ : ∃ t uQ o tv c₁, cx.peek a = .ok t ∧
      XchgCell cx t uQ o ∧ cx.use v = .ok (tv, c₁) ∧ (SubS c₁ tv uQ ∨ SubS c₁ tv o) ∧
      c₁.bind x o = .ok _ := ⟨_, _, _, _, _, hp, hx, hu, hsub, hb⟩
  rw [hpk] at hp; cases hp
  cases hx with
  | rgn _ hc _ _ _ => simp [cellOf] at hc
  | own _ hc _ =>
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hsub : SubS c₁ tv u := hsub.elim id id
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length u = true := tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.ptr .own u) = some (.own, u))
  obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, hacc, hown, hsku, hsig⟩ := ownPtr_view hi hpk htv ho
  obtain ⟨hi1, rv, wsv, hev, hvv, hlv⟩ := use_FInv hu hi
  have hna : ∀ N eQ, c.ty ≠ .array (.lit N) eQ := fun N eQ h =>
    hacc (by rw [h]; simp [accs])
  obtain ⟨us, hus, -, hld, -⟩ := ownLoad (arch := g.arch) (pw := pw) (acq := false) (s := stOf mem pairs th)
    hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown (Fd_lay hcty).1 (Fd_lay hcty).2.1
    (fun ws => ((Fd_lay hcty).2.2.2 ws).1) (fun R ws => (Fd_VR η hcty).1) hna hsku (peek_cell_lyt hi.2.1 hpk hea rfl rfl).2 hsig
    (by rw [(Fd_lay hcty).2.2.1]; exact pub_accs hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl ho hea rfl)
  have husA : accs c.ty = some us := ((Fd_lay hcty).2.2.1.trans (pub_accs hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl ho hea rfl).symm).trans hus
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw ⟨lab, 0⟩ false us 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        (storeUnits g.k g.arch pw ⟨lab, 0⟩ false us wsv 0 s1).map fun s2 => (s2, ru, old)).map
        fun (sQ, t, ws) => (sQ.mem, sQ.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } sQ) := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus]
  rw [key]
  intro r hr hpr0
  obtain ⟨s1, old, h1, hp1, henv, hst⟩ := xchg_out hr hpr0
  obtain ⟨hvr, hlay, -⟩ := hld (s1, old) h1 hp1
  have hUa : accs (cl ρ η.wit 0 0 u) = some us := by rw [← (Fd_lay hcty).2.2.1]; exact husA
  have hU : ∀ N eQ, cl ρ η.wit 0 0 u ≠ .array (.lit N) eQ := fun N eQ h => by
    rw [h] at hUa; simp [accs] at hUa
  have hc1 := hsto1 _ _ hsto
  obtain ⟨hwc, hval⟩ := wc_valid_of_lay hlay
  refine ⟨x, ru, old, henv, hst, ?_, lbl_load hE.2.1 hPf hBx hsig hvr hwc hval⟩
  exact valB_load (ad := ⟨lab, 0⟩) hc1 (hLay _ _ hc1) (Fd_AtOff hcty hacc) (IniAt_of_ne (ini := η.rc) hna) hU hUa
    hG hsig h1 hp1 ga N

/-- **`xchg` at an own locative**: the old component value bound is what the plain load read. -/
theorem rmw_xchgLoc {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a v : At} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.xchg a v) e)
    (hpk : cx.peek a = .ok (.loc .own u))
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
  | let_ hop _ =>
  cases hop with
  | xchg hp hx hu hsub hb =>
  obtain ⟨t, uQ, o, tv, c₁, hp, hx, hu, hsub, hb⟩ : ∃ t uQ o tv c₁, cx.peek a = .ok t ∧
      XchgCell cx t uQ o ∧ cx.use v = .ok (tv, c₁) ∧ (SubS c₁ tv uQ ∨ SubS c₁ tv o) ∧
      c₁.bind x o = .ok _ := ⟨_, _, _, _, _, hp, hx, hu, hsub, hb⟩
  rw [hpk] at hp; cases hp
  cases hx with
  | rgn _ hc _ _ _ => simp [cellOf] at hc
  | own _ hc _ =>
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hsub : SubS c₁ tv u := hsub.elim id id
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length u = true :=
    tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.loc .own u) = some (.own, u))
  have hafQ : (cl ρ η.wit 0 0 u).arrFree = true := arrFree_cl hi.2.2.2.2.2.2.1.af u 0 0 (bind_arrFree hb)
  have hna : ∀ n e, cl ρ η.wit 0 0 u ≠ .array (.lit n) e := fun n e h => by
    rw [h] at hafQ; simp [Ty.arrFree] at hafQ
  obtain ⟨hi1, rv, wsv, hev, hvv, hlv⟩ := use_FInv hu hi
  have hwcu : wc (cl ρ η.wit 0 0 u) ≠ none := by
    rw [← wc_of_sig (sig_WitL hi.2.2.2.1 ρ ho (lt_of_guardT htb hi.2.2.2.2.1))]
    exact (Lay_canon hsub hlv).2.2.2.1
  obtain ⟨ad, c, pw, μr, ru, hea, hpw, hsto, hat, hini, hown, hsku, hsig⟩ := locView hi hpk htv ho hwcu
  obtain ⟨us, hus, -, hld, -⟩ := locLoad (arch := g.arch) (pw := pw) (acq := false)
    (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown hat hini hna hsku hsig
      (peek_cell_lyt hi.2.1 hpk hea rfl rfl).2
        (accs_rtW hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 ho htb (peek_cell_lyt hi.2.1 hpk hea rfl rfl).2)
  have hwUA : accs (cl ρ η.wit 0 0 u) = some us := (accs_rtW hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 ho htb (peek_cell_lyt hi.2.1 hpk hea rfl rfl).2).symm.trans hus
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw ad false us 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        (storeUnits g.k g.arch pw ad false us wsv 0 s1).map fun s2 => (s2, ru, old)).map
        fun (sQ, t, ws) => (sQ.mem, sQ.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } sQ) := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus]
  rw [key]
  intro r hr hpr0
  obtain ⟨s1, old, h1, hp1, henv, hst⟩ := xchg_out hr hpr0
  obtain ⟨hvr, hlay, -⟩ := hld (s1, old) h1 hp1
  have hc1 := hsto1 _ _ hsto
  obtain ⟨hwc, hval⟩ := wc_valid_of_lay hlay
  refine ⟨x, ru, old, henv, hst, ?_, lbl_load hE.2.1 hPf hBx hsig hvr hwc hval⟩
  exact valB_load hc1 (hLay _ _ hc1) hat hini hna hwUA hG hsig h1 hp1 ga N

/-- **`xchgAt`**: at the slot's locative, the old element bound is what the plain load read. -/
theorem rmw_xchgAt {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i v : At} {e : Expr}
    (hterm : th.term = .let_ x (.xchgAt b i v) e)
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
  | let_ hop _ =>
  cases hop with
  | xchgAt hp hbuf _ hint hlt hltk hu hsub hb =>
  obtain ⟨t, u, n, k, j, tv, c₁, hp, hbuf, hint, hlt, hltk, hu, hsub, hb⟩ : ∃ t u n k j tv c₁,
      cx.peek b = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ IntIdx cx i j ∧ LtI cx j n ∧ LtI cx j k ∧
      cx.use v = .ok (tv, c₁) ∧ SubS c₁ tv u ∧ c₁.bind x u = .ok _ :=
    ⟨_, _, _, _, _, _, _, hp, hbuf, hint, hlt, hltk, hu, hsub, hb⟩
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  obtain ⟨rt, w, ad, c, μr, ur, us, rti, wi, hea, hwv, hei, hj, hbe, hus, hsto, hat, hown, hini, hsku, hsig, htb, -⟩ :=
    slot_view hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk ho
  have hafQ : (cl ρ η.wit 0 0 u).arrFree = true := arrFree_cl hi.2.2.2.2.2.2.1.af u 0 0 (bind_arrFree hb)
  have hna : ∀ N eQ, cl ρ η.wit 0 0 u ≠ .array (.lit N) eQ := fun N eQ h => by
    rw [h] at hafQ; simp [Ty.arrFree] at hafQ
  obtain ⟨hi1, rv, wsv, hev, hvv, hlv⟩ := use_FInv hu hi
  obtain ⟨usQ, husQ, -, hld, -⟩ := locLoad (ad := offs ad (ev ρ j * nWords us)) (arch := g.arch) (pw := w) (acq := false)
    (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown hat hini hna hsku hsig
      (peek_buf_lyt hi.2.1 hp hbuf hea hbe).2
        (accs_rtW hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 ho htb (peek_buf_lyt hi.2.1 hp hbuf hea hbe).2)
  rw [hus] at husQ; cases husQ
  have hwUA : accs (cl ρ η.wit 0 0 u) = some us := (accs_rtW hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 ho htb (peek_buf_lyt hi.2.1 hp hbuf hea hbe).2).symm.trans hus
  have key : tstep g mem pairs th =
      ((loadUnits g.arch w (offs ad (ev ρ j * nWords us)) false us 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        (storeUnits g.k g.arch w (offs ad (ev ρ j * nWords us)) false us wsv 0 s1).map fun s2 => (s2, ur, old)).map
        fun (sQ, t, ws) => (sQ.mem, sQ.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } sQ) := by
    simp only [tstep, hterm, evalOp, hea, hei, hev, hj, addrOf, hwv, hbe, hus]
  rw [key]
  intro r hr hpr0
  obtain ⟨s1, old, h1, hp1, henv, hst⟩ := xchg_out hr hpr0
  obtain ⟨hvr, hlay, -⟩ := hld (s1, old) h1 hp1
  have hc1 := hsto1 _ _ hsto
  obtain ⟨hwc, hval⟩ := wc_valid_of_lay hlay
  refine ⟨x, ur, old, henv, hst, ?_, lbl_load hE.2.1 hPf hBx hsig hvr hwc hval⟩
  exact valB_load (ad := offs ad (ev ρ j * nWords us)) hc1 (hLay _ _ hc1) hat hini hna hwUA hG hsig h1 hp1 ga N

/-- **`xchgAtF`**: at the field path's component of the slot, the old component value bound is
what the plain load read. -/
theorem rmw_xchgAtF {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i v : At} {q : List Nat} {e : Expr}
    (hterm : th.term = .let_ x (.xchgAtF b i q v) e)
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
  | let_ hop _ =>
  cases hop with
  | xchgAtF hp hbuf hct hop _ hint hlt hltk hu hsub hb =>
  obtain ⟨t, u, c, n, k, j, tv, c₁, hp, hbuf, hct, hop, hint, hlt, hltk, hu, hsub, hb⟩ : ∃ t u c n k j tv c₁,
      cx.peek b = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ compTy u q = some c ∧ cx.opaqueOK u = true ∧
      IntIdx cx i j ∧ LtI cx j n ∧ LtI cx j k ∧
      cx.use v = .ok (tv, c₁) ∧ SubS c₁ tv c ∧ c₁.bind x c = .ok _ :=
    ⟨_, _, _, _, _, _, _, _, hp, hbuf, hct, hop, hint, hlt, hltk, hu, hsub, hb⟩
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK c = true := sub_opaqueOK hsub hotv
  obtain ⟨rt, w, ad, cc, μr, ur, us, rti, wi, hea, hwv, hei, hj, hbe, hus, hsto, hat, hown, -, hsku, hsig, htbu, hiniF⟩ :=
    slot_view hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk hop
  have htb : tb cx.ke.length c = true := tb_compTy q u c hct htbu
  obtain ⟨cR, o, hco, hskc, hsgc, -, hato⟩ := compOff_rt q u c ur us hct hsku hsig hus
  have hafQ : (cl ρ η.wit 0 0 c).arrFree = true := arrFree_cl hi.2.2.2.2.2.2.1.af c 0 0 (bind_arrFree hb)
  have hna : ∀ N eQ, cl ρ η.wit 0 0 c ≠ .array (.lit N) eQ := fun N eQ h => by
    rw [h] at hafQ; simp [Ty.arrFree] at hafQ
  have hatQ : AtOff cc.ty (offs ad (ev ρ j * nWords us + o)).offset (cl ρ η.wit 0 0 c) := by
    have h2 := AtOff_trans hat hato
    simpa [offs, Nat.add_assoc] using h2
  have hiniC := hiniF o _ hato
  obtain ⟨hi1, rv, wsv, hev, hvv, hlv⟩ := use_FInv hu hi
  obtain ⟨cs, hcs, -, hld, -⟩ := locLoad (ad := offs ad (ev ρ j * nWords us + o)) (arch := g.arch) (pw := w)
    (acq := false) (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown hatQ hiniC hna hskc hsgc
      (compOff_lyt q u c ur cR o hct hsku (peek_buf_lyt hi.2.1 hp hbuf hea hbe).2 hco)
        (accs_rtW hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 ho htb (compOff_lyt q u c ur cR o hct hsku (peek_buf_lyt hi.2.1 hp hbuf hea hbe).2 hco))
  have hwUA : accs (cl ρ η.wit 0 0 c) = some cs := (accs_rtW hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 ho htb (compOff_lyt q u c ur cR o hct hsku (peek_buf_lyt hi.2.1 hp hbuf hea hbe).2 hco)).symm.trans hcs
  have key : tstep g mem pairs th =
      ((loadUnits g.arch w (offs ad (ev ρ j * nWords us + o)) false cs 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        (storeUnits g.k g.arch w (offs ad (ev ρ j * nWords us + o)) false cs wsv 0 s1).map fun s2 => (s2, cR, old)).map
        fun (sQ, t, ws) => (sQ.mem, sQ.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } sQ) := by
    simp only [tstep, hterm, evalOp, hea, hei, hev, hj, addrOf, hwv, hbe, hus, hco, hcs]
  rw [key]
  intro r hr hpr0
  obtain ⟨s1, old, h1, hp1, henv, hst⟩ := xchg_out hr hpr0
  obtain ⟨hvr, hlay, -⟩ := hld (s1, old) h1 hp1
  have hc1 := hsto1 _ _ hsto
  obtain ⟨hwc, hval⟩ := wc_valid_of_lay hlay
  refine ⟨x, cR, old, henv, hst, ?_, lbl_load hE.2.1 hPf hBx hsgc hvr hwc hval⟩
  exact valB_load (ad := offs ad (ev ρ j * nWords us + o)) hc1 (hLay _ _ hc1) hatQ hiniC hna hwUA hG hsgc h1 hp1 ga N

end TermK2aRmw

#print axioms TermK2aRmw.cas_shape
#print axioms TermK2aRmw.casp_shape
#print axioms TermK2aRmw.rmw_casWord
#print axioms TermK2aRmw.rmw_casCell
#print axioms TermK2aRmw.rmw_casWordLoc
#print axioms TermK2aRmw.rmw_casCellLoc
#print axioms TermK2aRmw.rmw_casp
#print axioms TermK2aRmw.rmw_caspLoc
#print axioms TermK2aRmw.fetch_coreK
#print axioms TermK2aRmw.noName_pub
#print axioms TermK2aRmw.ldOK_noName
#print axioms TermK2aRmw.stepOK_same
#print axioms TermK2aRmw.noName_num
#print axioms TermK2aRmw.stepOK_casLike
#print axioms TermK2aRmw.rmw_fetch
#print axioms TermK2aRmw.rmw_fetchLoc
#print axioms TermK2aRmw.xchg_out
#print axioms TermK2aRmw.rmw_xchgOwn
#print axioms TermK2aRmw.rmw_xchgLoc
#print axioms TermK2aRmw.rmw_xchgAt
#print axioms TermK2aRmw.rmw_xchgAtF
