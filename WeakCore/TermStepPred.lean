import WeakCore.TermNoHold
import WeakCore.TermCohLe
import WeakCore.TermSeenHid
import WeakCore.TermPlantF

/-!
# TermStepPred: the stage-A one-step fact `StepPredNumX` (`TermNoHold.StepPredNum` with run facts)

A typed step that fulfils an own promise `t` at an initialised epoch-counter
unit `a` finds the latest message at `a` below `t` numeric.

* The step's fulfils are coherence points (`tstep_fulC`), and the result keeps
  `PromAbove`; so no own promise at `a` lies below `t` and at or above the
  latest message there (`notOwn`).
* RMW fulfils (`fetch`, `cas`): the read is adjacent below `t`
  (`stepRmw_ful`); a fetch-op's read is a number since its write is
  (`fetch_ful_num`); a `cas` read is no own promise, so `undef` (excluded: it
  equals the typed expected operand) or `WordOK` (a number at a non-ghost word).
* A plain (units) store at an own cell: the latest message below `t` is the
  coherence point (`own_num`) or, past it, a typed foreign message (`LatestSF`).
* A plain (units) store at a cell not owned by the stepper: buffer writes are at
  own cells (`xchgAt_own`, …), so it is a `store`/`xchg` through a `pub` address
  whose frontier is below the address word's view (not `seen`: `SeenOwn`), below
  the message's, below `t` (`foreign_frontier`); the cell's allocation `undef`
  is then hidden below `t` and the latest message is a number (`foreign_pred`).
  This needs two run facts, `m.view < t` and the allocation `undef`, so the
  one-step fact is `StepPredNumX` (`stepPredNumX_of`), lifted by `promPredTX`
  from a promise-free initial configuration.
-/

namespace TermStepPred
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermStepper TermCert TermFul TermGlob TermTyped TermMain TermInterf TermNoHold
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-! ## §1 Generic facts -/

/-- **No own promise at the fulfilled address below `t`**: the step's fulfils
are coherence points of the result (`FulC`), which keeps `PromAbove`. -/
theorem notOwn {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh}
    (hfc : FulC (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2)) (hext : MemExt mem r.1)
    (hpa : PromAbove (stOf r.1 r.2.1 r.2.2)) {t : Ts} {m : Msg} (ht : t ∈ th.promises)
    (hn : t ∉ r.2.2.promises) (hm : mem[t]? = some m) {L : Ts} {mL : Msg} (hL : L < t)
    (hmL : mem[L]? = some mL) (hloc : mL.loc = m.loc) : L ∉ th.promises := by
  intro hLp
  obtain ⟨m1, hm1, hc1⟩ := hfc t ht hn
  change mem[t]? = some m1 at hm1
  rw [hm] at hm1
  cases hm1
  by_cases hLr : L ∈ r.2.2.promises
  · have h := hpa L hLr mL (hext _ _ hmL)
    change r.2.2.vs.coh mL.loc < L at h
    change r.2.2.vs.coh m.loc = t at hc1
    rw [hloc, hc1] at h
    unfold WeakMem.Ts at *
    omega
  · obtain ⟨m2, hm2, hc2⟩ := hfc L hLp hLr
    change mem[L]? = some m2 at hm2
    rw [hmL] at hm2
    cases hm2
    change r.2.2.vs.coh mL.loc = L at hc2
    change r.2.2.vs.coh m.loc = t at hc1
    rw [hloc, hc1] at hc2
    unfold WeakMem.Ts at *
    omega

/-- The predecessor from an adjacent read. -/
theorem pred_of_adj {mem : Memory} {a : Address} {tr t : Ts} {mr : Msg} (hmr : mem[tr]? = some mr)
    (hl : mr.loc = a) (hadj : WeakMem.rmwAdjacent mem a tr t = true) : PredAt mem a t (mw mr) := by
  obtain ⟨hlt, hb⟩ := rmwAdjacent_spec hadj
  exact ⟨tr, mr, hlt, hmr, hl, rfl, hb⟩

/-- **The latest message at `a` below `t`**, from any one. -/
theorem latest_below (mem : Memory) (a : Address) (t : Ts) :
    ∀ (d : Nat) (t0 : Ts) (m0 : Msg), t0 < t → t - t0 ≤ d → mem[t0]? = some m0 → m0.loc = a →
      ∃ L mL, t0 ≤ L ∧ L < t ∧ mem[L]? = some mL ∧ mL.loc = a ∧
        ∀ (t' : Ts) (m' : Msg), L < t' → t' < t → mem[t']? = some m' → m'.loc ≠ a := by
  intro d
  induction d with
  | zero => intro t0 m0 h1 h2; unfold WeakMem.Ts at *; omega
  | succ d ih =>
    intro t0 m0 h1 h2 hm0 hl0
    by_cases hx : ∃ (t1 : Ts) (m1 : Msg), t0 < t1 ∧ t1 < t ∧ mem[t1]? = some m1 ∧ m1.loc = a
    · obtain ⟨t1, m1, a1, a2, a3, a4⟩ := hx
      obtain ⟨L, mL, b1, b2, b3, b4, b5⟩ := ih t1 m1 a2 (by unfold WeakMem.Ts at *; omega) a3 a4
      exact ⟨L, mL, Nat.le_trans (Nat.le_of_lt a1) b1, b2, b3, b4, b5⟩
    · refine ⟨t0, m0, Nat.le_refl _, h1, hm0, hl0, fun t' m' c1 c2 c3 c4 => hx ⟨t', m', c1, c2, c3, c4⟩⟩

/-- A fetch-op's write is a number only if its read is. -/
theorem apply_num_read {kind : WeakMem.RmwKind} (hk : kind.isFetch = true) {x y : WeakMem.Val} {k : Nat}
    (h : kind.apply x y = .num k) : ∃ n, x = .num n := by
  cases kind <;> simp [WeakMem.RmwKind.isFetch] at hk <;> cases x <;> cases y <;>
    simp [WeakMem.RmwKind.apply] at h <;> exact ⟨_, rfl⟩

#print axioms notOwn
#print axioms pred_of_adj
#print axioms latest_below
#print axioms apply_num_read

/-- `IniWr` at a word unit gives `IniAt` at the real count (`IniAt_of_IniW` at `rc`). -/
theorem IniAt_of_IniWr {E : TEnv} {a : Address} {c : Cell} {r : Idx} {P : Proto} (hsto : E.sto a.label = some c)
    (hat : AtOff c.ty a.offset (.word r P)) (hw : IniWr E a) : IniAt E.rc c a (.word r P) := by
  intro N e hT
  refine Or.inr ?_
  have hat2 := hat
  rw [hT] at hat2
  rcases AtOff_array_inv (fun t h => by cases h) hat2 with ⟨-, h⟩ | ⟨n', j, o2, us, hn, hus, -, ho, hat'⟩
  · cases h
  · obtain rfl : N = n' := by cases hn; rfl
    have hlt := hw c N e us hsto hT hus
    refine ⟨us, j, o2, hus, Nat.lt_of_not_le fun hle => ?_, ho.symm, hat'⟩
    have hm : E.rc a.label * nWords us ≤ j * nWords us := Nat.mul_le_mul_right _ hle
    exact absurd (Nat.lt_of_lt_of_le hlt hm) (by rw [ho]; exact Nat.not_lt.2 (Nat.le_add_right _ _))

/-- The expected operand of a `cas`, through `peek`, is a value of the closed cell type
(`useVal_cl` for a peeked atom). -/
theorem peekVal_cl {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop} {cx c₁ : Cx}
    {env : Env} {e v : At} {te tv u re : Ty} {ws : List Word}
    (hi : FInv ρ η σs K cx env) (hco : Coh η) (htv : TvOK cx) (hu : cx.use v = .ok (tv, c₁))
    (hpe : cx.peek e = .ok te) (hsub : SubS c₁ te u) (htb : tb cx.ke.length u = true)
    (hev : evalAt env e = some (re, ws)) :
    VR (fun _ => 0) (CE η) (cl ρ η.wit 0 0 u) (shp (cl ρ η.wit 0 0 u)) ws := by
  obtain ⟨-, hf, -, -⟩ := use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub (peek_opaqueOK htv hpe)
  obtain ⟨rv', ws', hev', hvv, hlv⟩ := peek_VR hi.2.1 hpe
  rw [hev] at hev'
  simp only [Option.some.injEq, Prod.mk.injEq] at hev'
  obtain ⟨rfl, rfl⟩ := hev'
  have hsat : Sat c₁.facts ρ := by rw [hf]; exact hi.1
  obtain ⟨hs, -⟩ := Lay_canon hsub hlv
  have hvu : VR ρ η u (shp (close σs u)) ws := by rw [← hs]; exact VR_sub hsat hsub _ _ hvv
  have hsigu : sig (close σs u) = sig (cl ρ η.wit 0 0 u) :=
    sig_WitL hi.2.2.2.1 ρ ho (lt_of_guardT htb hi.2.2.2.2.1)
  rw [← shp_of_sig hsigu]
  exact (VR_close hco ρ u [] 0 ρ (fun _ => 0) (shp (close σs u)) ws (fun k => rfl)
    (fun k hk => absurd hk (Nat.not_lt_zero _))).1 hvu

/-- A `cas`'s expected operand is not `undef` (`cas_nu` for `e`). -/
theorem cas_e_nu {p : Prog} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx : Cx} {env : Env} {acq rel : Bool} {w e v : At} {tn : String} {ok fail : Expr} {t2 : Ty} {ew : Word}
    (hT : Typed p cx (.cas acq rel w e v tn ok fail))
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hee : evalAt env e = some (t2, [ew])) : ew.val ≠ .undef := by
  cases hT with
  | casCell hp _ hc hraw _ hpe hu hsube _ =>
      rcases hc with hc | ⟨r, hc, -⟩
      · exact VR_one_nundef _ (peekVal_cl hi hE.2.1 htv hu hpe hsube (tb_cellOf (peek_tb htv hp) hc) hee)
          (accs_cl_one hraw) 0 ew (.here _) rfl
      · exact VR_one_nundef _ (peekVal_cl hi hE.2.1 htv hu hpe hsube (tb_cellOf (peek_tb htv hp) hc) hee)
          (accs_cl_one hraw) 0 ew (.here _) rfl
  | casShare _ _ _ hie _ | casTake _ _ _ hie _ | casEpoch _ _ _ _ hie _ =>
      obtain ⟨ti, hpi, hti⟩ := hie
      obtain ⟨rt', w', hev', hw, -⟩ := atom_num hi.2.1 hpi hti
      rw [hee] at hev'
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hev'
      obtain ⟨-, rfl⟩ := hev'
      rw [hw]; simp

#print axioms IniAt_of_IniWr
#print axioms peekVal_cl
#print axioms cas_e_nu

/-! ## §2 RMW fulfils -/

/-- **A fetch-op's fulfil**: the read is adjacent below `t` (`stepRmw_ful`), and a
number, since the write is (`fetch_ful_num`) and a fetch-op of a non-number is
`undef`. -/
theorem fetch_pred {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {o : FetchOp} {acq rel : Bool} {a v : At}
    {e : Expr} (hterm : th.term = .let_ x (.fetch o acq rel a v) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hsc : StepScope cx th.term)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) (hpr : PromAbove (stOf r.1 r.2.1 r.2.2))
    {t : Ts} {m : Msg} (ht : t ∈ th.promises) (hn : t ∉ r.2.2.promises) (hmt : mem[t]? = some m)
    {loc : Address} {ta tv : Ty} {pw nw : Word} (hea : evalAt th.env a = some (ta, [pw]))
    (hev : evalAt th.env v = some (tv, [nw])) (haddr : addrOf pw = some loc) :
    ∃ w, PredAt mem m.loc t w ∧ ∃ k, w.val = .num k := by
  obtain ⟨k, hk⟩ := fetch_ful_num hterm hP hT hi hE htv hm hsc hr hpr ht hn hmt
  simp only [tstep, hterm, evalOp, hea, hev, haddr, List.map_map, List.mem_map] at hr
  obtain ⟨⟨mem', th'⟩, hin, rfl⟩ := hr
  obtain ⟨-, -, rem⟩ := stepRmw_ful hin
  obtain ⟨-, m', tr, mr, hm', hmr, -, hl, hv, -, -, -, hadj, hrl⟩ := rem t ht hn
  change mem[t]? = some m' at hm'
  rw [hmt] at hm'
  cases hm'
  rw [hk] at hv
  obtain ⟨n0, hn0⟩ := apply_num_read (FetchOp.kind_isFetch o) hv.symm
  refine ⟨mw mr, pred_of_adj hmr (hrl.trans hl.symm) (by rw [hl]; exact hadj), n0, hn0⟩

/-- **A `cas`'s fulfil**: the read is adjacent below `t`, no own promise
(`notOwn`), so `undef` or `WordOK` (`MemOKP`); `undef` would be the expected
operand (`cas_e_nu`), and a `WordOK` word at a non-ghost word is a number. -/
theorem cas_pred {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {acq rel : Bool} {w e v : At} {tn : String} {ok fail : Expr}
    (hterm : th.term = .cas acq rel w e v tn ok fail)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) (hpr : PromAbove (stOf r.1 r.2.1 r.2.2))
    (hfc : FulC (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2)) (hext : MemExt mem r.1)
    {t : Ts} {m : Msg} (ht : t ∈ th.promises) (hn : t ∉ r.2.2.promises) (hmt : mem[t]? = some m)
    {loc : Address} {t1 t2 t3 : Ty} {pw ew nw : Word} (hea : evalAt th.env w = some (t1, [pw]))
    (hee : evalAt th.env e = some (t2, [ew])) (hev : evalAt th.env v = some (t3, [nw]))
    (hb : addrOf pw = some loc) {n : Nat} {P : Proto} (hW : WordAt (CE η) m.loc n P) :
    ∃ w, PredAt mem m.loc t w ∧ ∃ k, w.val = .num k := by
  obtain ⟨c, hc, hat, hg⟩ := hW
  have hnu : ew.val ≠ .undef := by
    have hT0 := hT
    rw [hterm] at hT0
    exact cas_e_nu hT0 hi hE htv hee
  have hr0 := hr
  simp only [tstep, hterm, hea, hee, hev, hb, List.mem_map] at hr0
  obtain ⟨⟨mem', th'⟩, hin, rfl⟩ := hr0
  obtain ⟨-, -, rem⟩ := stepRmw_ful hin
  obtain ⟨-, m', tr, mr, hm', hmr, hsucc, hl, -, -, -, htr, hadj, hrl⟩ := rem t ht hn
  change mem[t]? = some m' at hm'
  rw [hmt] at hm'
  cases hm'
  have hloc : mr.loc = m.loc := hrl.trans hl.symm
  have hno : tr ∉ th.promises := notOwn hfc hext hpr ht hn hmt htr hmr hloc
  have hsto : (CE η).sto mr.loc.label = some c := by rw [hloc]; exact hc
  rcases hm.1.1 tr mr c hno hmr hsto with hu | hok
  · exfalso
    simp only [WeakMem.rmwSucceeds, WeakMem.RmwKind.succeeds, decide_eq_true_eq] at hsucc
    rw [hu] at hsucc
    exact hnu hsucc.symm
  · obtain ⟨k, hk, -⟩ := wordOK_good hok (by rw [hloc]; exact hat) hg
    exact ⟨mw mr, pred_of_adj hmr hloc (by rw [hl]; exact hadj), k, hk⟩

#print axioms fetch_pred
#print axioms cas_pred

/-! ## §3 Any fulfil at an own cell -/

/-- **At an own cell**: the latest message at `a` below `t` is the coherence
point (a number, `own_num`) or, past it, a foreign typed message (`LatestSF`,
a number at a non-ghost word); an own promise there is excluded (`notOwn`). -/
theorem own_pred {g : G} {E : TEnv} {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh}
    (hm : MemInv g E (stOf mem pairs th))
    (hfc : FulC (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2)) (hext : MemExt mem r.1)
    (hpa : PromAbove (stOf r.1 r.2.1 r.2.2)) {t : Ts} {m : Msg} (ht : t ∈ th.promises)
    (hn : t ∉ r.2.2.promises) (hmt : mem[t]? = some m) (hcoh : th.vs.coh m.loc < t)
    {c : Cell} {n : Nat} {P : Proto} (hsto : E.sto m.loc.label = some c) (hown : c.owner = some E.tid)
    (hat : AtOff c.ty m.loc.offset (.word (.lit n) P)) (hg : P.ghost = false) (hIW : IniWr E m.loc) :
    ∃ w, PredAt mem m.loc t w ∧ ∃ k, w.val = .num k := by
  have hini : IniAt E.rc c m.loc (.word (.lit n) P) := IniAt_of_IniWr hsto hat hIW
  obtain ⟨vals, hcell, hlat, -⟩ := hm.2.1 _ c hsto hown
  obtain ⟨b, o, S, wS, -, hbo, hatS, hwS, hbw, -⟩ := own_seg hcell hat hini (fun N e h => by cases h)
  obtain ⟨L, hL, hn'⟩ := wc_some hwS
  have hb := AtOff_bound hatS hL (accs_word hg)
  rw [show nWords [Acc.one] = 1 from rfl] at hb
  have hlt : m.loc.offset < vals.length := by
    rw [← hbo]
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left (show o < wS by rw [← hn']; exact hb) b) hbw
  obtain ⟨⟨m0, hm0, hl0, -⟩, -, hlater⟩ := hlat m.loc.offset _ (List.getElem?_eq_getElem hlt)
  have ea : (⟨m.loc.label, m.loc.offset⟩ : Address) = m.loc := rfl
  rw [ea] at hm0 hl0 hlater
  change mem[th.vs.coh m.loc]? = some m0 at hm0
  obtain ⟨L, mL, h1, h2, h3, h4, h5⟩ :=
    latest_below mem m.loc t (t - th.vs.coh m.loc) (th.vs.coh m.loc) m0 hcoh (Nat.le_refl _) hm0 hl0
  refine ⟨mw mL, ⟨L, mL, h2, h3, h4, rfl, h5⟩, ?_⟩
  rcases Nat.eq_or_lt_of_le h1 with e | hgt
  · obtain ⟨k, hk⟩ := own_num (m := mL) (t := L) hm (by rw [h4]; exact hsto) hown h3
      (by show th.vs.coh mL.loc = L; rw [h4]; exact e) (by rw [h4]; exact hat) hg (by rw [h4]; exact hini)
    exact ⟨k, hk⟩
  · rcases hlater L mL hgt h3 h4 with hp | ⟨-, hty⟩
    · exact absurd hp (notOwn hfc hext hpa ht hn hmt h2 h3 h4)
    · obtain ⟨k, hk, -⟩ := wordOK_good hty (by rw [h4]; exact hat) hg
      exact ⟨k, hk⟩

#print axioms own_pred

/-- **At a foreign cell with a frontier below `t`**: an `undef` message at `a`
(not an own promise) is hidden by a later message at or below the frontier
`f < t` (`PubDefP`); the latest message at `a` below `t` is then past it, no
own promise (`notOwn`), so `WordOK` (a number) or `undef` (again hidden,
contradicting latestness). -/
theorem foreign_pred {g : G} {E : TEnv} {mem : Memory} {pairs : List Ts} {th : TTh}
    {r : Memory × List Ts × TTh} (hm : MemInv g E (stOf mem pairs th))
    (hfc : FulC (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2)) (hext : MemExt mem r.1)
    (hpa : PromAbove (stOf r.1 r.2.1 r.2.2)) {t : Ts} {m : Msg} (ht : t ∈ th.promises)
    (hn : t ∉ r.2.2.promises) (hmt : mem[t]? = some m)
    {c : Cell} {n : Nat} {P : Proto} (hsto : E.sto m.loc.label = some c) (hown : c.owner ≠ some E.tid)
    (hat : AtOff c.ty m.loc.offset (.word (.lit n) P)) (hg : P.ghost = false) (hIW : IniWr E m.loc)
    {f : Ts} (hf : E.pfr m.loc.label = some f) (hft : f < t)
    (hu : ∃ t0 m0, mem[t0]? = some m0 ∧ m0.loc = m.loc ∧ m0.val = .undef ∧ t0 ∉ th.promises) :
    ∃ w, PredAt mem m.loc t w ∧ ∃ k, w.val = .num k := by
  obtain ⟨hOK, -, -, -, -, -, hPub, -, -, -, -⟩ := hm
  have hIR : InitR E c m.loc.label m.loc.offset := fun N e us h1 h2 =>
    Nat.lt_of_lt_of_le (hIW c N e us hsto h1 h2) (Nat.mul_le_mul_right _ (TEnv.rc_le_ini _ _))
  have hh := hPub _ c f hsto hown hf _ hIR
  have ea : (⟨m.loc.label, m.loc.offset⟩ : Address) = m.loc := rfl
  obtain ⟨t0, m0, hm0, hl0, hv0, hp0⟩ := hu
  obtain ⟨t1, m1, h01, h1f, hm1, hl1⟩ :=
    hh t0 m0 hp0 hm0 (by rw [hl0]) (TermSeenHid.undef_not_wordOK hat hg hv0)
  rw [ea] at hl1
  obtain ⟨L, mL, h1, h2, h3, h4, h5⟩ :=
    latest_below mem m.loc t (t - t1) t1 m1 (Nat.lt_of_le_of_lt h1f hft) (Nat.le_refl _) hm1 hl1
  refine ⟨mw mL, ⟨L, mL, h2, h3, h4, rfl, h5⟩, ?_⟩
  have hLp := notOwn hfc hext hpa ht hn hmt h2 h3 h4
  have hatL : AtOff c.ty mL.loc.offset (.word (.lit n) P) := by rw [h4]; exact hat
  rcases hOK.1 L mL c hLp h3 (by rw [h4]; exact hsto) with hund | hty
  · obtain ⟨t2, m2, hL2, h2f, hm2, hl2⟩ :=
      hh L mL hLp h3 (by rw [h4]) (TermSeenHid.undef_not_wordOK hat hg hund)
    rw [ea] at hl2
    exact absurd hl2 (h5 t2 m2 hL2 (Nat.lt_of_le_of_lt h2f hft) hm2)
  · obtain ⟨k, hk, -⟩ := wordOK_good hty hatL hg
    exact ⟨k, hk⟩

#print axioms foreign_pred

theorem xchgAt_own {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb i v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.xchgAt bb i v) c')
    (hi : FInv ρ η σs K cx env) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.xchgAt bb i v) pw b rel us ws) :
    ∃ c, η.sto b.label = some c ∧ c.owner = some η.tid := by
  obtain ⟨-, rt, t1, t2, iws, μ, u0, j0, a0, hea, hei, -, hbe, hnj, hb, hus, rfl⟩ := hu
  cases hop with
  | xchgAt hp hbuf _ hint hlt hltk hu' hsub _ =>
      have ho := sub_opaqueOK hsub
        (peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu').1)
      obtain ⟨rt', w, ad, c, μr, ur, us', rti, wi, hea', hwv, hei', hnj', hbe', hus', hsto, hat, hmo, -, -, -,
        htb, -⟩ := slot_view hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk ho
      rw [hea] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      rw [hei] at hei'
      simp only [Option.some.injEq, Prod.mk.injEq] at hei'
      obtain ⟨rfl, rfl⟩ := hei'
      rw [hbe] at hbe'
      simp only [Option.some.injEq, Prod.mk.injEq] at hbe'
      obtain ⟨rfl, rfl⟩ := hbe'
      rw [hnj] at hnj'
      simp only [Option.some.injEq] at hnj'
      subst hnj'
      rw [hus] at hus'
      simp only [Option.some.injEq] at hus'
      subst hus'
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst e
      exact ⟨_, hsto, hmo⟩

#print axioms xchgAt_own

theorem xchgAtF_own {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb i v : At} {q : List Nat}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.xchgAtF bb i q v) c')
    (hi : FInv ρ η σs K cx env) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.xchgAtF bb i q v) pw b rel us ws) :
    ∃ c, η.sto b.label = some c ∧ c.owner = some η.tid := by
  obtain ⟨-, rt, t1, t2, iws, μ, u0, j0, a0, us0, c0, o0, hea, hei, -, hbe, hnj, hb, hus0, hco0, hus, rfl⟩ :=
    hu
  cases hop with
  | xchgAtF hp hbuf hct hopu _ hint hlt hltk hu' hsub _ =>
      have ho := sub_opaqueOK hsub
        (peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu').1)
      obtain ⟨rt', w, ad, cc, μr, ur, us', rti, wi, hea', hwv, hei', hnj', hbe', hus', hsto, hat, hmo, -,
        hsku, hsig, htbu, -⟩ := slot_view hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk hopu
      rw [hea] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      rw [hei] at hei'
      simp only [Option.some.injEq, Prod.mk.injEq] at hei'
      obtain ⟨rfl, rfl⟩ := hei'
      rw [hbe] at hbe'
      simp only [Option.some.injEq, Prod.mk.injEq] at hbe'
      obtain ⟨rfl, rfl⟩ := hbe'
      rw [hnj] at hnj'
      simp only [Option.some.injEq] at hnj'
      subst hnj'
      rw [hus0] at hus'
      simp only [Option.some.injEq] at hus'
      subst hus'
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst e
      exact ⟨_, hsto, hmo⟩

#print axioms xchgAtF_own

theorem bufInit_own {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb i v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.bufInit bb i v) c')
    (hi : FInv ρ η σs K cx env) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.bufInit bb i v) pw b rel us ws) :
    ∃ c, η.sto b.label = some c ∧ c.owner = some η.tid := by
  obtain ⟨-, rt, t1, t2, iws, μ0, u0, j0, a0, μ', n', e', ψ, hea, hei, -, hbe, hnj, hb, hus, -, rfl⟩ := hu
  cases hop with
  | bufInit hu' hbuf hint heq hlt hu2 hsub _ =>
      obtain ⟨t, u, n, k, jj, c₁, tv, c₂, hu', hbuf, hint, heq, hlt, hu2, hsub⟩ :
          ∃ t u n k jj c₁ tv c₂, cx.use bb = .ok (t, c₁) ∧ bufOf t = some (.own, n, u, k) ∧
            IntIdx c₁ i jj ∧ EqI c₁ jj k ∧ LtI c₁ k n ∧ c₁.use v = .ok (tv, c₂) ∧ SubS c₂ tv u :=
        ⟨_, _, _, _, _, _, _, _, hu', hbuf, hint, heq, hlt, hu2, hsub⟩
      have ht : t = .refine (.loc .own (.array n u)) (.ini k) := by
        unfold bufOf at hbuf; split at hbuf
        · simp only [Option.some.injEq, Prod.mk.injEq] at hbuf
          obtain ⟨h1, rfl, rfl, rfl⟩ := hbuf; subst h1; rfl
        · simp at hbuf
      subst ht
      have htu := use_TvOK hu' htv
      obtain ⟨hi1, rb, wsb, hea', hvb, hlb⟩ := use_FInv hu' hi
      have hJK : ev ρ jj = ev ρ k := heq ρ hi1.1
      have hKN : ev ρ k < ev ρ n := hlt ρ hi1.1
      obtain ⟨ti, hpi, hti⟩ := hint
      obtain ⟨rti, wsi, hei', hvi, -⟩ := peek_VR hi1.2.1 hpi
      obtain ⟨wi, rfl, hwi⟩ := map_singleton (VR_intS hti hvi)
      rw [hea] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      rw [hei] at hei'
      simp only [Option.some.injEq, Prod.mk.injEq] at hei'
      obtain ⟨rfl, rfl⟩ := hei'
      have hj0 : j0 = ev ρ jj := by simp [numOf, hwi] at hnj; exact hnj.symm
      subst hj0
      simp only [VR] at hvb
      obtain ⟨hv, -⟩ := hvb
      rcases hv with ⟨-, e0, he0⟩ | ⟨ad, c, U, hws, hsto, hat0, hFU, hmo, -⟩
      · have he0 := Fd_nonmu he0 (fun b => by simp [cl])
        simp only [cl, clI_zero, Ty.array.injEq, Idx.lit.injEq] at he0
        omega
      obtain rfl := Fd_nonmu hFU (fun b => by simp [cl])
      have hwv : pw.val = .loc ad 0 := by simpa using hws
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst e
      simp only [cl, clI_zero] at hat0
      exact ⟨_, hsto, hmo⟩

#print axioms bufInit_own

theorem stl_own {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb i v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.stl bb i v) c')
    (hi : FInv ρ η σs K cx env) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.stl bb i v) pw b rel us ws) :
    ∃ c, η.sto b.label = some c ∧ c.owner = some η.tid := by
  obtain ⟨-, rfl, rt, t1, t2, iws, vs, μ0, u0, j0, y, a0, sg0, w0, s1, old, x0, hea, hei, -, hbe, hnj, -,
    hb, hlo0, rfl, -⟩ := hu
  cases hop with
  | stl hp hbuf hlo hint hlt hltk _ _ _ =>
      obtain ⟨t, u, n, k, jj, q, hp, hbuf, hlo, hint, hlt, hltk⟩ : ∃ t u n k jj q,
          cx.peek bb = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧ IntIdx cx i jj ∧
          LtI cx jj (.smul q.2.lanes n) ∧ LtI cx jj (.smul q.2.lanes k) :=
        ⟨_, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk⟩
      obtain ⟨sg, w⟩ := q
      have hu := lanes_of hlo
      simp only at hu hlt hltk
      subst hu
      have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
      obtain ⟨ti, hpi, hti⟩ := hint
      obtain ⟨rti, wwi, hei', hwi, -⟩ := atom_num hi.2.1 hpi hti
      have hJ0 : ev ρ jj < w.lanes * ev ρ n := by simpa [ev] using hlt ρ hi.1
      have hJk0 : ev ρ jj < w.lanes * ev ρ k := by simpa [ev] using hltk ρ hi.1
      have hJ : ev ρ jj / w.lanes < ev ρ n :=
        (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJ0)
      have hJk : ev ρ jj / w.lanes < ev ρ k :=
        (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJk0)
      obtain ⟨rt', pw', ad, c, μr, ur, us', hea', hwv, hbe', hus', hsto, hat, hmo, -, hsku, -⟩ :=
        slot_viewN (ev ρ jj / w.lanes) hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hJ hJk ho
      obtain ⟨rfl, rfl⟩ := lane_rt hsku hus'
      rw [hea] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      rw [hbe] at hbe'
      simp only [Option.some.injEq, Prod.mk.injEq] at hbe'
      obtain ⟨rfl, rfl⟩ := hbe'
      rw [hei] at hei'
      simp only [Option.some.injEq, Prod.mk.injEq] at hei'
      obtain ⟨rfl, rfl⟩ := hei'
      have hj0 : j0 = ev ρ jj := by simp [numOf, hwi] at hnj; exact hnj.symm
      subst hj0
      simp only [lanesOf, Option.some.injEq, Prod.mk.injEq] at hlo0
      obtain ⟨rfl, rfl⟩ := hlo0
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst e
      have e1 : ev ρ jj / w.lanes * nWords [Acc.one] = ev ρ jj / w.lanes := by simp [nWords, Acc.size]
      rw [e1] at hat
      exact ⟨_, hsto, hmo⟩

#print axioms stl_own

theorem stlw_own {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb wi jl v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.stlw bb wi jl v) c')
    (hi : FInv ρ η σs K cx env) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.stlw bb wi jl v) pw b rel us ws) :
    ∃ c, η.sto b.label = some c ∧ c.owner = some η.tid := by
  obtain ⟨-, rfl, rt, t1, t2, t3, iws, jws, vs, μ0, u0, i0, j0, y, a0, sg0, w0, s1, old, x0, hea, hei, -, -,
    hbe, hni, -, -, hb, hlo0, rfl, -⟩ := hu
  cases hop with
  | stlw hp hbuf hlo hint hlt hltk _ _ _ _ _ =>
      obtain ⟨t, u, n, k, jw, q, hp, hbuf, hlo, hint, hlt, hltk⟩ : ∃ t u n k jw q,
          cx.peek bb = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧ IntIdx cx wi jw ∧
          LtI cx jw n ∧ LtI cx jw k :=
        ⟨_, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk⟩
      obtain ⟨sg, w⟩ := q
      have hu := lanes_of hlo
      simp only at hu
      subst hu
      have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
      obtain ⟨rt', w', ad, c, μr, ur, us', rti, wwi, hea', hwv, hei', hni', hbe', hus', hsto, hat, hmo, -,
        hsku, -, -, -⟩ := slot_view hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk ho
      obtain ⟨rfl, rfl⟩ := lane_rt hsku hus'
      rw [hea] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      rw [hei] at hei'
      simp only [Option.some.injEq, Prod.mk.injEq] at hei'
      obtain ⟨rfl, rfl⟩ := hei'
      rw [hni] at hni'
      simp only [Option.some.injEq] at hni'
      subst hni'
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst e
      have e1 : ev ρ jw * nWords [Acc.one] = ev ρ jw := by simp [nWords, Acc.size]
      rw [e1] at hat
      exact ⟨_, hsto, hmo⟩

#print axioms stlw_own

/-- A plain store's message view is at least its address word's: the address
register `0` is a dependency of the store (`storeMview`). -/
theorem pw_le_storeMview (s : St) (pw w : Word) (e : WeakMem.Expr) (rel : Bool) :
    pw.view ≤ Promises.storeMview (mth s pw w w) e [0] rel := by
  have hm : ∀ a b : Nat, b ≤ max a b := fun a b => Nat.le_max_right a b
  have hl : ∀ a b : Nat, a ≤ max a b := fun a b => Nat.le_max_left a b
  cases rel <;> cases e <;> simp [Promises.storeMview, Promises.depView, mth, regsOf]
  · exact hm _ _
  · exact Nat.le_trans (hl _ _) (hm _ _)
  · exact Nat.le_trans (hm _ _) (Nat.le_trans (hm _ _) (hm _ _))
  · exact Nat.le_trans (hl _ _) (Nat.le_trans (hm _ _) (Nat.le_trans (hm _ _) (hm _ _)))

#print axioms pw_le_storeMview

/-- A promise `t` a `storeUnits` call fulfils carries a view at least the
address word's. -/
theorem units_view {k : Promises.Knobs} {arch : Arch} {pw : Word} {b : Address} {rel : Bool}
    {us : List Acc} {ws : List Word} {s s1 s' : St}
    (hlt : ∀ t, t ∈ s.promises → t < s.mem.size) (hm1 : s1.mem = s.mem) (hp1 : s1.promises = s.promises)
    (hs : s' ∈ storeUnits k arch pw b rel us ws 0 s1) {t : Ts} {m : Msg} (ht : t ∈ s.promises)
    (hn : t ∉ s'.promises) (hm : s.mem[t]? = some m) : pw.view ≤ m.view := by
  obtain ⟨-, -, rem⟩ := storeUnits_ful _ _ _ _ _ hs
  obtain ⟨j, w, s0, m0, -, -, he, -, hm0, -, -, hmv, -⟩ := rem t (hp1 ▸ ht) hn
  have e := memExt_back (hm1 ▸ he) (hlt t ht) hm0
  rw [hm] at e
  cases e
  exact Nat.le_trans (pw_le_storeMview _ _ _ _ _) hmv

#print axioms units_view

theorem store_view {g : G} {env : Env} {σs : List Ty} {s : St} {rl : Bool} {a v : At} {o : Option At}
    {r : St × Ty × List Word} {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (h : r ∈ evalOp g env σs s (.store rl a v o))
    (hu : TermFul.UnitsOp g env s (.store rl a v o) pw b rel us ws)
    (hlt : ∀ t, t ∈ s.promises → t < s.mem.size) {t : Ts} {m : Msg} (ht : t ∈ s.promises)
    (hn : t ∉ r.1.promises) (hm : s.mem[t]? = some m) : pw.view ≤ m.view := by
  obtain ⟨rfl, t0, t1, μ, u, hea, hev, hc, hb, hus⟩ := hu
  simp only [evalOp, hea, hev, hc, hb, hus, List.mem_map] at h
  obtain ⟨s'', hs, rfl⟩ := h
  exact units_view hlt rfl rfl hs ht hn hm

#print axioms store_view

theorem xchg_view {g : G} {env : Env} {σs : List Ty} {s : St} {a v : At}
    {r : St × Ty × List Word} {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (h : r ∈ evalOp g env σs s (.xchg a v))
    (hu : TermFul.UnitsOp g env s (.xchg a v) pw b rel us ws)
    (hlt : ∀ t, t ∈ s.promises → t < s.mem.size) {t : Ts} {m : Msg} (ht : t ∈ s.promises)
    (hn : t ∉ r.1.promises) (hm : s.mem[t]? = some m) : pw.view ≤ m.view := by
  obtain ⟨rfl, t0, t1, μ, u, hea, hev, hc, hb, hus⟩ := hu
  simp only [evalOp, hea, hev, hc, hb, hus, List.mem_flatMap, List.mem_map] at h
  obtain ⟨⟨s1, old⟩, hx, s2, hy, rfl⟩ := h
  obtain ⟨k1, -, k3⟩ := loadUnits_keep _ _ _ _ hx
  exact units_view hlt k1 k3 hy ht hn hm

#print axioms xchg_view

/-- The cell type a plain store's address is typed at. -/
theorem store_cell {p : Prog} {cx c' : Cx} {x : String} {rl : Bool} {a v : At} {tok : Option At}
    (hop : OpT p cx x (.store rl a v tok) c') : ∃ t μ u, cx.peek a = .ok t ∧ cellOf t = some (μ, u) := by
  cases hop with
  | storeOwn hp _ hc => exact ⟨_, _, _, hp, hc⟩
  | storePub hp _ hc => exact ⟨_, _, _, hp, hc⟩
  | storeRgn hp _ hc => exact ⟨_, _, _, hp, hc⟩
  | storeCap hp _ hc => exact ⟨_, _, _, hp, hc⟩
  | storeWordGive hp hw | storeWordKeep hp hw | storeWordHand hp hw =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      rcases ht with rfl | rfl
      · exact ⟨_, _, _, hp, rfl⟩
      · exact ⟨_, _, _, hp, rfl⟩

#print axioms store_cell

theorem xchg_cell {p : Prog} {cx c' : Cx} {x : String} {a v : At}
    (hop : OpT p cx x (.xchg a v) c') : ∃ t μ u, cx.peek a = .ok t ∧ cellOf t = some (μ, u) := by
  cases hop with
  | xchg hp hx =>
      cases hx with
      | rgn _ hc => exact ⟨_, _, _, hp, hc⟩
      | own _ hc => exact ⟨_, _, _, hp, hc⟩

#print axioms xchg_cell

/-- The mode condition at a cell address's target. -/
theorem cell_mode {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} {a : At} {t : Ty}
    {μ : Mode} {u rt : Ty} {pw : Word} {b : Address} (hvars : VarsOK ρ η σs cx.vars env)
    (hp : cx.peek a = .ok t) (hc : cellOf t = some (μ, u))
    (hea : evalAt env a = some (rt, [pw])) (hb : addrOf pw = some b) :
    ∃ c, η.sto b.label = some c ∧ ModeOK η.tid η.pfr η.seen μ b.label c [pw] := by
  obtain ⟨rt', ws, hea', hv, -⟩ := peek_VR hvars hp
  rw [hea] at hea'
  simp only [Option.some.injEq, Prod.mk.injEq] at hea'
  obtain ⟨rfl, rfl⟩ := hea'
  rcases cell_cases hc with rfl | rfl
  · simp only [VR] at hv
    obtain ⟨a', c, hws, -, hsto, -, hmo, -⟩ := hv
    have hpw : pw.val = .loc a' 0 := by simpa using hws
    have e : b = a' := by simp [addrOf, hpw] at hb; exact hb.symm
    subst e
    exact ⟨c, hsto, hmo⟩
  · simp only [VR] at hv
    rcases hv with ⟨hws, -⟩ | ⟨a', c, U, hws, hsto, -, -, hmo, -⟩
    · have hpw : pw.val = .null := by simpa using hws
      simp [addrOf, hpw] at hb
    · have hpw : pw.val = .loc a' 0 := by simpa using hws
      have e : b = a' := by simp [addrOf, hpw] at hb; exact hb.symm
      subst e
      exact ⟨c, hsto, hmo⟩

#print axioms cell_mode

/-- A foreign target's mode gives a frontier below `t`: not `own` (foreign),
not `rgn` (scope), so `pub`; not seen (`SeenOwn`), so below the address
word's view, below the message's, below `t`. -/
theorem mode_frontier {g : G} {η : TEnv} {mem : Memory} {pairs : List Ts} {th : TTh} {μ : Mode}
    {b : Address} {c : Cell} {pw : Word} {m : Msg} {t : Ts} (hm : MemInv g (CE η) (stOf mem pairs th))
    (hsto : η.sto b.label = some c) (hown : c.owner ≠ some η.tid) (hnr : ∀ r, μ ≠ .rgn r)
    (hmo : ModeOK η.tid η.pfr η.seen μ b.label c [pw]) (hpv : pw.view ≤ m.view) (hv : m.view < t) :
    ∃ f, η.pfr b.label = some f ∧ f < t := by
  cases μ with
  | own => exact absurd hmo hown
  | rgn r => exact absurd rfl (hnr r)
  | pub =>
      obtain ⟨f, hf, hS | hle⟩ := hmo
      · obtain ⟨-, -, -, -, -, -, -, -, hPI, -, -⟩ := hm
        rcases hPI.1 b.label hS with ⟨c', hc', ho'⟩ | ⟨hn0, -⟩
        · change η.sto b.label = some c' at hc'
          rw [hsto] at hc'
          cases hc'
          exact absurd ho' hown
        · change η.sto b.label = none at hn0
          rw [hsto] at hn0
          cases hn0
      · exact ⟨f, hf, Nat.lt_of_le_of_lt (Nat.le_trans (hle pw (List.mem_singleton_self _)) hpv) hv⟩

#print axioms mode_frontier

/-- **A foreign cell's frontier is below the fulfilled promise**: a units
write fulfilling `t` (message `m`, view below `t`) at a cell not the thread's
is a `pub` store or exchange (buffer writes are at own cells), whose frontier
is below `m.view`. -/
theorem foreign_frontier {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat}
    {η : TEnv} {cx : Cx} {r : Memory × List Ts × TTh} (hT : Typed p cx th.term) (htv : TvOK cx)
    (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hsc : StepScope cx th.term) (hr : r ∈ tstep g mem pairs th) {x : String} {op : Op} {e : Expr}
    (hterm : th.term = .let_ x op e) {pw : Word} {b : Address} {rel : Bool} {us : List Acc}
    {ws : List Word} {j : Nat} (hu : TermFul.UnitsOp g th.env (stOf mem pairs th) op pw b rel us ws)
    {t : Ts} {m : Msg} (ht : t ∈ th.promises) (hn : t ∉ r.2.2.promises) (hmt : mem[t]? = some m)
    (hloc : m.loc = offs b j) {c : Cell} (hc : (CE η).sto m.loc.label = some c)
    (hown : c.owner ≠ some (CE η).tid) (hv : m.view < t) :
    ∃ f, (CE η).pfr m.loc.label = some f ∧ f < t := by
  have hlt : ∀ t, t ∈ th.promises → t < mem.size := MemInv_promLt hm
  have hlb : m.loc.label = b.label := by rw [hloc]; rfl
  rw [hlb] at hc ⊢
  have hT' := hT
  rw [hterm] at hT' hsc
  cases op
  case store rl a v tok =>
    have hsc' : OpScope cx (.store rl a v tok) := hsc
    cases hT' with
    | let_ hop _ =>
        have hu0 := hu
        obtain ⟨-, t0, t1, μr, ru, hea, -, -, hb, -⟩ := hu0
        obtain ⟨ty, μ, u, hp, hcy⟩ := store_cell hop
        obtain ⟨c', hsto', hmo⟩ := cell_mode hi.2.1 hp hcy hea hb
        have e : c' = c := Option.some.inj (hsto'.symm.trans hc)
        subst e
        simp only [tstep, hterm] at hr
        rw [List.mem_map] at hr
        obtain ⟨⟨s', t', ws'⟩, hin, hr⟩ := hr
        have hn' : t ∉ s'.promises := by rw [← hr] at hn; exact hn
        exact mode_frontier hm hsto' hown (fun r0 h => by subst h; exact hsc' _ hp _ _ hcy) hmo
          (store_view hin hu hlt ht hn' hmt) hv
  case xchg a v =>
    have hsc' : OpScope cx (.xchg a v) := hsc
    cases hT' with
    | let_ hop _ =>
        have hu0 := hu
        obtain ⟨-, t0, t1, μr, ru, hea, -, -, hb, -⟩ := hu0
        obtain ⟨ty, μ, u, hp, hcy⟩ := xchg_cell hop
        obtain ⟨c', hsto', hmo⟩ := cell_mode hi.2.1 hp hcy hea hb
        have e : c' = c := Option.some.inj (hsto'.symm.trans hc)
        subst e
        simp only [tstep, hterm] at hr
        rw [List.mem_map] at hr
        obtain ⟨⟨s', t', ws'⟩, hin, hr⟩ := hr
        have hn' : t ∉ s'.promises := by rw [← hr] at hn; exact hn
        exact mode_frontier hm hsto' hown (fun r0 h => by subst h; exact hsc' _ hp _ _ hcy) hmo
          (xchg_view hin hu hlt ht hn' hmt) hv
  case xchgAt =>
    cases hT' with
    | let_ hop _ =>
        obtain ⟨c', hsto', hmo⟩ := xchgAt_own hop hi htv hu
        have e : c' = c := Option.some.inj (hsto'.symm.trans hc)
        subst e
        exact absurd hmo hown
  case xchgAtF =>
    cases hT' with
    | let_ hop _ =>
        obtain ⟨c', hsto', hmo⟩ := xchgAtF_own hop hi htv hu
        have e : c' = c := Option.some.inj (hsto'.symm.trans hc)
        subst e
        exact absurd hmo hown
  case bufInit =>
    cases hT' with
    | let_ hop _ =>
        obtain ⟨c', hsto', hmo⟩ := bufInit_own hop hi htv hu
        have e : c' = c := Option.some.inj (hsto'.symm.trans hc)
        subst e
        exact absurd hmo hown
  case stl =>
    cases hT' with
    | let_ hop _ =>
        obtain ⟨c', hsto', hmo⟩ := stl_own hop hi htv hu
        have e : c' = c := Option.some.inj (hsto'.symm.trans hc)
        subst e
        exact absurd hmo hown
  case stlw =>
    cases hT' with
    | let_ hop _ =>
        obtain ⟨c', hsto', hmo⟩ := stlw_own hop hi htv hu
        have e : c' = c := Option.some.inj (hsto'.symm.trans hc)
        subst e
        exact absurd hmo hown
  all_goals simp [TermFul.UnitsOp] at hu

#print axioms foreign_frontier

/-! ## §4 `StepPredNumX` -/

/-- `TermNoHold.StepPredNum` with two further premises on the fulfilled promise
`t` (message `m`): its view is below `t`, and `m.loc` has an `undef` message
that is not one of the thread's promises (its allocation placeholder). -/
def StepPredNumX (p : Prog) : Prop :=
  ∀ (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) (ρ : Nat → Nat) (η : TEnv) (cx : Cx), g.p = p →
    EnvOK p η → Typed p cx th.term → TvOK cx → FInv ρ η th.σs (Resume p th.stack) cx th.env →
    MemInv g (CE η) (stOf mem pairs th) → StepScope cx th.term → PromAbove (stOf mem pairs th) →
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
    ∀ t m, t ∈ th.promises → t ∉ r.2.2.promises → mem[t]? = some m → IniWr (CE η) m.loc →
      ∀ n P, WordAt (CE η) m.loc n P → P.epoch = true → m.view < t →
      (∃ t0 m0, mem[t0]? = some m0 ∧ m0.loc = m.loc ∧ m0.val = .undef ∧ t0 ∉ th.promises) →
      ∃ w, PredAt mem m.loc t w ∧ ∃ k, w.val = .num k

/-- **`StepPredNumX` from `ProgT`.**  `tstep_fulfil` gives the fulfilling write
(`SW`) and `coh a < t`: a fetch-op (`fetch_pred`), a `cas` (`cas_pred`), or a
units store, at an own cell (`own_pred`) or a foreign one (`foreign_frontier`,
`foreign_pred`). -/
theorem stepPredNumX_of {p : Prog} (hP : ProgT p) : StepPredNumX p := by
  intro g mem pairs th ρ η cx hgp hE hT htv hi hm hsc hpa0 r hr hpa t m ht hn hmt hIW n P hW hep hv hund
  have hlt : ∀ t, t ∈ th.promises → t < mem.size := MemInv_promLt hm
  have hpp : ∀ t, t ∈ th.promises → t ∉ pairs := MemInv_nopair hm
  have hfc := tstep_fulC hlt hpp hr
  have hext : MemExt mem r.1 := (tstep_appUp hr).2.1
  obtain ⟨-, hrem⟩ := tstep_fulfil hlt hpp hr
  obtain ⟨m', hm', hsw, hcoh, -⟩ := hrem t ht hn
  rw [hmt] at hm'
  cases hm'
  have hW0 := hW
  obtain ⟨c, hc, hat, hgh⟩ := hW0
  rcases hsw with ⟨x, op, e, hterm, hw⟩ |
      ⟨acq, rel, w, e, v, tn, ok, fail, t1, t2, t3, pw, ew, nw, tr, mr, hterm, hea, hee, hev, hb, -⟩
  · rcases hw with ⟨pw, b, rel, us, ws, j, w, hu, hj, hwj, hloc, hval⟩ |
        ⟨o, acq, rel, a, v, ta, tv, pw, nw, tr, mr, hop, hea, hev, haddr, -⟩
    · by_cases hown : c.owner = some (CE η).tid
      · exact own_pred hm hfc hext hpa ht hn hmt hcoh hc hown hat hgh hIW
      · obtain ⟨f, hf, hft⟩ := foreign_frontier hT htv hi hm hsc hr hterm hu ht hn hmt hloc hc hown hv
        exact foreign_pred hm hfc hext hpa ht hn hmt hc hown hat hgh hIW hf hft hund
    · subst hop
      exact fetch_pred hterm hP hT hi hE htv hm hsc hr hpa ht hn hmt hea hev haddr
  · exact cas_pred hterm hT hi hE htv hm hr hpa hfc hext ht hn hmt hea hee hev hb hW

#print axioms stepPredNumX_of

/-- `TermNoHold.certified_promPredE` from `StepPredNumX`, given the promise's
view below it and an `undef` message at its location not among the thread's
promises (both carried to the fulfilling step's configuration). -/
theorem certified_promPredEX {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat} {E0 : TEnv}
    {n0 v0 na0 : Nat} [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hstep : StepPredNumX p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPubA p k arch E0 E0 i c0)
    (h0 : InvAtXF p k arch i E0 n0 v0 na0 c) (hTA : TermTyped.TidAt i c E0) (hc : Certified p k arch c i)
    {t : Ts} {m : Msg} (ht : t ∈ TermFul.promsOf c i) (hm : c.mem[t]? = some m) (hIW : IniWr E0 m.loc)
    {n : Nat} {P : Proto} (hW : WordAt E0 m.loc n P) (hep : P.epoch = true) (hv : m.view < t)
    (hund : ∃ t0 m0, c.mem[t0]? = some m0 ∧ m0.loc = m.loc ∧ m0.val = .undef ∧ t0 ∉ TermFul.promsOf c i) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∃ w, PredAt c.mem m.loc t w ∧ ∃ k, w.val = .num k := by
  have hpwf := pwf_of_inv h0.toInvAt
  obtain ⟨m', hm', c1, c2, th1, h1, h2, hc2, hth1, hm1, ht1, hn2, -⟩ := certified_fulfilC hc hpwf ht
  rw [hm] at hm'
  cases hm'
  have hc1 : Certified p k arch c1 i := certified_back (.thread h2 (.refl _)) hc2
  obtain ⟨th1', E1, hth1', hx1, ⟨ρ, η, cx, rfl, hE, hT, htv, hi, hrp, hDy⟩, hmi1, -⟩ := solo_typedXF (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hsc hvI hwin h0 hTA h1 hc1
  rw [hth1] at hth1'
  cases hth1'
  have hscope := hsc c1 h1 hc1 th1 hth1 (TermTyped.not_spawnT_of_steps hth1 h2) ρ η cx hE hT htv hi
  obtain ⟨th', r, hth', hr, e1, e2, e3, -⟩ := threadSteps_inv h2
  rw [hth1] at hth'
  cases hth'
  have hpa : PromAbove (stOf r.1 r.2.1 r.2.2) := by
    have h := certified_promAboveSt hc2 e3
    rw [e1, e2] at h
    exact h
  have hn : t ∉ r.2.2.promises := by rw [TermFul.promsOf_some e3] at hn2; exact hn2
  replace hscope : StepScope cx th1.term := by
    rcases hscope with h | ⟨-, hcap⟩
    · exact h
    · have e := ((tstep_cap (hDy := hDy) (hPS := hPS) hP hcap hT hi hE htv hrp).2 r hr).2.2.2.2.1
      simp only [stOf] at e
      exact absurd (e ▸ ht1) hn
  obtain ⟨th0, -, hth0, -⟩ := h0
  obtain ⟨th0', th1', e0, e1', -, hme, hpr, -⟩ := solo_winInv h1 (winInv_refl hth0)
  rw [hth0] at e0
  cases e0
  rw [hth1] at e1'
  cases e1'
  have hund1 : ∃ t0 m0, c1.mem[t0]? = some m0 ∧ m0.loc = m.loc ∧ m0.val = .undef ∧ t0 ∉ th1.promises := by
    obtain ⟨t0, m0, h1m, h2m, h3m, h4m⟩ := hund
    refine ⟨t0, m0, hme t0 m0 h1m, h2m, h3m, fun h5 => ?_⟩
    rcases hpr t0 h5 with h6 | h6
    · rw [TermFul.promsOf_some hth0] at h4m
      exact h4m h6
    · exact absurd (TermMem.lt_of_get h1m) (Nat.not_lt.2 h6)
  obtain ⟨c0, hc0, -⟩ := id hW
  obtain ⟨w, hpw, hnum⟩ := hstep (gOf p k arch c1 i) c1.mem c1.pairs th1 ρ η cx rfl hE hT htv hi hmi1 hscope
    (certified_promAboveSt hc1 hth1) r hr hpa t m ht1 hn hm1 (IniWr_ext hx1 hc0 hIW) n P (WordAt_ext hx1 hW) hep
    hv hund1
  have htlt : t < c.mem.size := (hpwf.2 t ht).1
  have hp : ∀ t', t' < c.mem.size → c1.mem[t']? = c.mem[t']? := fun t' h' => by
    have e : c.mem[t']? = some c.mem[t'] := by simp [h']
    rw [e]; exact hme t' _ e
  exact ⟨w, (PredAt_prefix hp (Nat.le_of_lt htlt)).2 hpw, hnum⟩

#print axioms certified_promPredEX

/-- `TermNoHold.promPredT` from `StepPredNumX` along a run from a
promise-free configuration: the promise's view is below it
(`TermPlantF.promViewLt_run`), and its location's allocation `undef`
(`UndefAtG`) is no promise (`PromNotUndef`). -/
theorem promPredTX {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0)
    [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hstep : StepPredNumX p) (hz : TermPlantF.PromViewLtR p k arch Sp c0)
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r)
    (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (hrun : ∀ S', ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S' →
      ∀ c1, Solo p k arch i c c1 → Certified p k arch c1 i → ScopeAt p i c1 ∧ NoHoldPubA p k arch (Cut Eg i S') (Cut Eg i S') i c1) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    TermNoHold.PromPredE (CE η) (stOf c.mem c.pairs th) := by
  intro t m ht hm hIW n P hW hep
  change c.mem[t]? = some m at hm
  rw [Y.1] at hIW hW
  obtain ⟨S', hS'⟩ := X.inv.thr i th X.hth
  obtain ⟨-, hTE, hmi, -⟩ := id hS'
  have hSC : StoClo (Cut Eg i S') := fun l cl hl => X.inv.clo l cl (cutSto_sub hl)
  have h0 := InvAtXF_of (hTy := (X.inv.tyRec X.hth S').1) (hRc := (X.inv.tyRec X.hth S').2) (p := p) (k := k) (arch := arch) X.hth hTE hmi hSC X.inv.bf (X.inv.riniCoh _ _ _ X.hth)
    (fun l cl f hs hp => X.inv.frlt l cl f (cutSto_sub hs) hp)
  have hc : Certified p k arch c i := by
    obtain ⟨c'', hs, hn⟩ := X.cert
    exact ⟨c'', .thread X.hc' hs, hn⟩
  have hv : m.view < t := by
    obtain ⟨m1, hm1, hv1⟩ := TermPlantF.promViewLt_run hz X.run i th t X.hth ht
    rw [hm] at hm1
    cases hm1
    exact hv1
  have hund : ∃ t0 m0, c.mem[t0]? = some m0 ∧ m0.loc = m.loc ∧ m0.val = .undef ∧
      t0 ∉ TermFul.promsOf c i := by
    obtain ⟨cc, hcc, hat, hg⟩ := hW
    obtain ⟨t0, m0, h1m, h2m, h3m⟩ := X.inv.undefAt _ cc (cutSto_sub hcc) _ n P hat hg
    refine ⟨t0, m0, h1m, h2m, h3m, fun h4 => ?_⟩
    rw [TermFul.promsOf_some X.hth] at h4
    exact X.inv.promNU i th t0 m0 X.hth h4 h1m h3m
  exact certified_promPredEX (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hstep (fun c1 h1 h2 => (hrun S' hS' c1 h1 h2).1) (by first | exact TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw | exact TermViewInv.viewInv_run hV0 X.run | exact TermViewInv.viewInv_thread (TermViewInv.viewInv_run hV0 X.run) X.hc') (fun c1 h1 h2 => (hrun S' hS' c1 h1 h2).2)
    h0 (TermMain.tidAt_cut X.inv i S') hc (by rw [TermFul.promsOf_some X.hth]; exact ht) hm hIW hW hep hv hund

#print axioms promPredTX

/-! ## §5 The `promPred` obligation field -/

/-- **`TermMain`'s `promPred` field** from `ProgT`, a promise-free initial
configuration and the run premise `TermCohLe.CertRunC` (scope and `NoHoldPub`
along solo runs from the pre-step configuration), via `promPredTX`. -/
theorem promPred_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0)
    [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hz : TermPlantF.PromViewLtR p k arch Sp c0)
    (hrun : TermCohLe.CertRunC p k arch Sp Init MintOK c0) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
      {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
      {Rf Rs : Res},
      TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
      TermNoHold.PromPredE (CE η) (stOf c.mem c.pairs th) :=
  fun X Y => promPredTX (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP (stepPredNumX_of hP) hz X Y (hrun X)

#print axioms promPred_of

end TermStepPred
