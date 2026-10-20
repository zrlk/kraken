import WeakCore.TermUndefLow

namespace TermUndefLow
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermCert
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-! ## §4 A fetch-op appends a number -/

open TermTyped in
theorem fetch_new_core {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {x : String} {o : FetchOp} {acq rel : Bool} {a v : At} {e : Expr}
    {ad : Address} {pw nw : Word} {rt rv : Ty} {dd : Nat} {Q : List Word → Prop}
    (hterm : th.term = .let_ x (.fetch o acq rel a v) e)
    (hea : evalAt th.env a = some (rt, [pw])) (haddr : addrOf pw = some ad)
    (hev : evalAt th.env v = some (rv, [nw])) (hnw : nw.val = .num dd)
    (hcell : ∀ s1 ws, (s1, ws) ∈ loadUnits g.arch pw ad acq [.one] 0 (stOf mem pairs th) →
      PromAbove s1 → Q ws)
    (hq : ∀ rd, Q [rd] → ∃ n, rd.val = .num n)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) (hpr : PromAbove (stOf r.1 r.2.1 r.2.2))
    (t : Ts) (m : Msg) (ht : mem.size ≤ t) (hmt : r.1[t]? = some m) :
    ∃ n, m.val = .num n := by
  have hd : dataE 1 nw = .const nw.val := by simp [dataE, hnw]
  have key : tstep g mem pairs th =
      (Promises.stepRmw g.k g.arch mem pairs (mth (stOf mem pairs th) pw nw nw) 1 ad o.kind
          (dataE 1 nw) [0] acq rel).map fun (mem', th') =>
        (mem', pairs, withS { th with term := e, env := (x, fetchRtTy rt, [th'.regs 1]) :: th.env }
          ⟨mem', pairs, th'.vs, th'.promises, th.nalloc, th.undefs + countUndef [th'.regs 1]⟩) := by
    simp only [tstep, hterm, evalOp, hea, hev, haddr, List.map_map]; rfl
  rw [key, List.mem_map] at hr
  obtain ⟨⟨mem', th'⟩, hin, rfl⟩ := hr
  obtain ⟨s1, rd, hl1, hrd, s2, hs2, hsame⟩ :=
    stepRmw_splitF (s := stOf mem pairs th) (FetchOp.kind_isFetch o) hd hin
  have hp2 : PromAbove s2 :=
    PromAbove_lockS (s := setRel s2 (lockR g.arch (stOf mem pairs th) s1).vs) (PromAbove_same hsame (fun t ht m hm => hpr t ht m hm))
  have hp1' : PromAbove (bumpRel (lockR g.arch (stOf mem pairs th) s1) _) := storeUnits_promAbove hs2 hp2
  have hp1 : PromAbove s1 := fun t ht m hm => hp1' t ht m hm
  obtain ⟨n, hn1⟩ := hq rd (hcell s1 [rd] hl1 hp1)
  dsimp only at hmt
  obtain ⟨t0, m0, -, -, hreg, h⟩ := stepRmw_mem hin
  rcases h with ⟨-, rfl, -⟩ | ⟨-, ⟨mv, rfl, -⟩ | ⟨_, _, _, rfl, -⟩⟩
  · exact absurd (TermMem.lt_of_get hmt) (by omega)
  · rw [Array.getElem?_push] at hmt
    split at hmt
    · cases hmt
      obtain ⟨k, hk⟩ := FetchOp.apply_num o n dd
      refine ⟨k, ?_⟩
      show o.kind.apply m0.val (Promises.rmwNewVal (mth (stOf mem pairs th) pw nw nw).regs (dataE 1 nw)) = _
      rw [TermFul.rmwNewVal_dataE, ← hreg, hrd, hn1, hnw, hk]
    · exact absurd (TermMem.lt_of_get hmt) (by omega)
  · exact absurd (TermMem.lt_of_get hmt) (by omega)

open TermTyped in
/-- A fetch-op through a pointer (`tstepM_fetch`'s cases). -/
theorem fetch_new_numP {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {o : FetchOp} {acq rel : Bool} {a v : At}
    {e : Expr} {μ : Mode} {u : Ty}
    (hterm : th.term = .let_ x (.fetch o acq rel a v) e) (_hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr μ u)) (hμ : μ = .own ∨ μ = .pub)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) (hpr : PromAbove (stOf r.1 r.2.1 r.2.2))
    (t : Ts) (m : Msg) (ht : mem.size ≤ t) (hmt : r.1[t]? = some m) :
    ∃ n, m.val = .num n := by
  have hT0 := hT
  rw [hterm] at hT0
  cases hT0 with
  | let_ hop he =>
  cases hop with
  | fetchCell hp _ hc hu hsub hb =>
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
      refine fetch_new_core (Q := fun ws => ∃ n, ws.map (·.val) = [.num n]) hterm hea
        (by simp [addrOf, hpw]) hev hnwv (fun s1 ws hl hp1 => (hcell s1 ws hl hp1).2.1)
        (fun rd hq => ?_) hr hpr t m ht hmt
      obtain ⟨n, hn'⟩ := hq
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hn'
      exact ⟨n, hn'⟩
    · simp only [cellOf, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, -⟩ := hc
      rcases hμ with h | h <;> cases h
  | fetchEpoch hp hw hep _ hj heq hb =>
    rw [hpk] at hp; cases hp
    cases u <;> simp [wordOf] at hw
    obtain ⟨rfl, rfl⟩ := hw
    rename_i r P
    have hpwf := wordRef_pwf hpk (.inl rfl) hμ hi hE htv hm
    have hg : P.ghost = false := by
      have := pwf_epochOK hpwf hep
      unfold epochOK at this; simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
      exact this.1.2
    obtain ⟨lab, pw, μ', r', hea, hpw, -, hcell⟩ :=
      wordCellF (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk hμ hg hi hE htv hm
    obtain ⟨tv, htvk, hjo⟩ := hj
    obtain ⟨rtv, nw, hev, hnwv, -⟩ := atom_num hi.2.1 htvk hjo
    have hj1 := heq ρ hi.1
    simp only [ev] at hj1
    rw [hj1] at hnwv
    refine fetch_new_core (Q := fun ws => VR ρ η (.word r P) (shp (.word r' P)) ws) hterm hea
      (by simp [addrOf, hpw]) hev hnwv (fun s1 ws hl hp1 => (hcell s1 ws hl hp1).2.1)
      (fun rd hq => ?_) hr hpr t m ht hmt
    simp only [VR] at hq
    obtain ⟨n, hn', -⟩ := hq.2 hg
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hn'
    exact ⟨n, hn'⟩
  | fetchShare hp hw hep hj heq hok hb =>
    rw [hpk] at hp; cases hp
    cases u <;> simp [wordOf] at hw
    obtain ⟨rfl, rfl⟩ := hw
    rename_i r P
    have hpwf := wordRef_pwf hpk (.inl rfl) hμ hi hE htv hm
    have hg : P.ghost = false := by
      unfold fetchOK at hok; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
      exact hok.1.1.1.1
    obtain ⟨lab, pw, μ', r', hea, hpw, -, hcell⟩ :=
      wordCellF (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk hμ hg hi hE htv hm
    obtain ⟨tv, htvk, hjo⟩ := hj
    obtain ⟨rtv, nw, hev, hnwv, -⟩ := atom_num hi.2.1 htvk hjo
    rename_i d
    have hjd := heq ρ hi.1
    simp only [ev] at hjd
    rw [hjd] at hnwv
    refine fetch_new_core (Q := fun ws => VR ρ η (.word r P) (shp (.word r' P)) ws) hterm hea
      (by simp [addrOf, hpw]) hev hnwv (fun s1 ws hl hp1 => (hcell s1 ws hl hp1).2.1)
      (fun rd hq => ?_) hr hpr t m ht hmt
    simp only [VR] at hq
    obtain ⟨n, hn', -⟩ := hq.2 hg
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hn'
    exact ⟨n, hn'⟩

open TermTyped in
/-- A fetch-op through a locative (`tstepM_fetchLoc`'s cases). -/
theorem fetch_new_numL {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {o : FetchOp} {acq rel : Bool} {a v : At}
    {e : Expr} {μ : Mode} {u : Ty}
    (hterm : th.term = .let_ x (.fetch o acq rel a v) e) (_hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc μ u)) (hμ : μ = .own ∨ μ = .pub)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) (hpr : PromAbove (stOf r.1 r.2.1 r.2.2))
    (t : Ts) (m : Msg) (ht : mem.size ≤ t) (hmt : r.1[t]? = some m) :
    ∃ n, m.val = .num n := by
  have hT0 := hT
  rw [hterm] at hT0
  cases hT0 with
  | let_ hop he =>
  cases hop with
  | fetchCell hp _ hc hu hsub hb =>
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
      refine fetch_new_core (Q := fun ws => ∃ n, ws.map (·.val) = [.num n]) hterm hea haddr hev hnwv
        (fun s1 ws hl hp1 => by simpa [VR] using (hld s1 ws hl hp1).1) (fun rd hq => ?_) hr hpr t m ht hmt
      obtain ⟨n, hn'⟩ := hq
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hn'
      exact ⟨n, hn'⟩
    · simp only [cellOf, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, -⟩ := hc
      rcases hμ with h | h <;> cases h
  | fetchEpoch hp hw hep _ hj heq hb =>
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
    obtain ⟨r', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
    obtain ⟨tv, htvk, hjo⟩ := hj
    obtain ⟨rtv, nw, hev, hnwv, -⟩ := atom_num hi.2.1 htvk hjo
    have hj1 := heq ρ hi.1
    simp only [ev] at hj1
    rw [hj1] at hnwv
    refine fetch_new_core (Q := fun ws => VR ρ η (.word r P) (shp (.word r' P)) ws) hterm hea haddr hev
      hnwv (fun s1 ws hl hp1 => (hld s1 ws hl hp1).1) (fun rd hq => ?_) hr hpr t m ht hmt
    simp only [VR] at hq
    obtain ⟨n, hn', -⟩ := hq.2 hg
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hn'
    exact ⟨n, hn'⟩
  | fetchShare hp hw hep hj heq hok hb =>
    rw [hpk] at hp; cases hp
    cases u <;> simp [wordOf] at hw
    obtain ⟨rfl, rfl⟩ := hw
    rename_i r P
    have hpwf := wordRef_pwf hpk (.inr rfl) hμ hi hE htv hm
    have hg : P.ghost = false := by
      unfold fetchOK at hok; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
      exact hok.1.1.1.1
    have hus1 : accs (cl ρ η.wit 0 0 (.word r P)) = some [.one] := by simp [cl, accs, hg]
    obtain ⟨ad, pw, μr, ru, hea, haddr, -, hsku, -, -, hld, -, -⟩ :=
      locCell (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk hμ
        (by simp [Cx.opaqueOK, Ty.guardT]) hus1 hi hE htv hm
    obtain ⟨r', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
    obtain ⟨tv, htvk, hjo⟩ := hj
    obtain ⟨rtv, nw, hev, hnwv, -⟩ := atom_num hi.2.1 htvk hjo
    rename_i d
    have hjd := heq ρ hi.1
    simp only [ev] at hjd
    rw [hjd] at hnwv
    refine fetch_new_core (Q := fun ws => VR ρ η (.word r P) (shp (.word r' P)) ws) hterm hea haddr hev
      hnwv (fun s1 ws hl hp1 => (hld s1 ws hl hp1).1) (fun rd hq => ?_) hr hpr t m ht hmt
    simp only [VR] at hq
    obtain ⟨n, hn', -⟩ := hq.2 hg
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hn'
    exact ⟨n, hn'⟩

open TermTyped in
/-- **(B4 §3.3, fix (a)) A fetch-op's fulfils hold numbers**, at a typed,
in-scope state, for every step whose result keeps `PromAbove`. -/
theorem fetch_new_num {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {o : FetchOp} {acq rel : Bool} {a v : At}
    {e : Expr} (hterm : th.term = .let_ x (.fetch o acq rel a v) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hsc : StepScope cx th.term)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) (hpr : PromAbove (stOf r.1 r.2.1 r.2.2))
    (t : Ts) (m : Msg) (ht : mem.size ≤ t) (hmt : r.1[t]? = some m) :
    ∃ n, m.val = .num n := by
  have hs : OpScope cx (.fetch o acq rel a v) := by
    have h := hsc; rw [hterm] at h; exact h
  have hT0 := hT
  rw [hterm] at hT0
  obtain ⟨tA, hpkA⟩ : ∃ tA, cx.peek a = .ok tA := by
    cases hT0 with
    | let_ hop _ =>
      cases hop with
      | fetchCell hp => exact ⟨_, hp⟩
      | fetchEpoch hp => exact ⟨_, hp⟩
      | fetchShare hp => exact ⟨_, hp⟩
  obtain ⟨μ, u, hteq | hteq, hμ⟩ := hs tA hpkA
  · rw [hteq] at hpkA
    exact fetch_new_numP hterm hP hpkA hμ hT hi hE htv hm hr hpr t m ht hmt
  · rw [hteq] at hpkA
    exact fetch_new_numL hterm hP hpkA hμ hT hi hE htv hm hr hpr t m ht hmt

#print axioms fetch_new_core
#print axioms fetch_new_num

end TermUndefLow
