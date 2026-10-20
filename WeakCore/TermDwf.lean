import WeakCore.TermScope

/-!
# TermDwf: the run-level discharge of `StoreCrZ` (T3, route c′; PIN option 3)

`StoreCrZ` (TermStep) is what the pub-store lemmas use in place of `StoreDwf`.
Under PIN option 3 it is `StoreNI ∧ StoreLeafPayAll`: the leaf-pay half holds for
every environment (`TermPiece.storeLeafPay_of`), so `storeCrZ_of` needs only
`StoreNI`.

The former first conjunct, `StoreCrZ0` (every own promise inside the stored
units carries no resources, or it lies at an epoch-counter unit and has a
predecessor), is kept as library (`storeCrZ0_of`, `dwf0_of`): its non-epoch half
follows from the word key: a plain whole-value store over an initialised
non-epoch word unit of region `n` would put two carriers of `wd n` in the system
(the stored value and memory's unit), against `KeyNet`.
-/

namespace TermDwf
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermLiveHeld
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

theorem storePub_wd_at {p : Prog} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → Nat → List Word → Res → Prop} {Rf : Res}
    {x : String} {rel : Bool} {a v : At} {tok : Option At} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.store rel a v tok) e)
    (hpk : cx.peek a = .ok (.ptr .pub u)) (hnw : wordOf (Ty.ptr .pub u) = none)
    (hT : Typed p cx th.term) (hi : FInvR ρ η th.σs K cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx)
    {rt : Ty} {pw0 : Word} {ad : Address} (hev0 : evalAt th.env a = some (rt, [pw0]))
    (had : addrOf pw0 = some ad) {j : Nat}
    {n : Nat} {P : Proto} (hw : WordAt (CE η) (offs ad j) n P) (hep : P.epoch = false) :
    1 ≤ Rf (.wd n) := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  cases hop with
  | storeWordGive hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordKeep hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordHand hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeOwn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeRgn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeCap hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storePub hp _ hc hwf hu hsub _ hb =>
  obtain ⟨t0, u', tv, c₁, hp, hc, hu, hsub⟩ : ∃ t0 u' tv c₁, cx.peek a = .ok t0 ∧
      cellOf t0 = some (.pub, u') ∧ cx.use v = .ok (tv, c₁) ∧ SubS c₁ tv u' :=
    ⟨_, _, _, _, hp, hc, hu, hsub⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hi0 := hi.1
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length u = true := tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.ptr .pub u) = some (.pub, u))
  obtain ⟨lab, c, pw, ru, f, hea, hpw, hsto, hcty, hf, -, hacc, hsku, hsig⟩ := pubPtr_view hi0 hpk htv ho
  obtain ⟨rv, wsv, Rv, Rr, hev, hvv, hlv, hvrv, hi1, hle⟩ := useR hu hi hE.2.2
  have hsat : Sat c₁.facts ρ := hi1.1.1
  have hlr : accs ru = accs c.ty := by
    rw [(Fd_lay hcty).2.2.1]
    exact pub_accs hi0.2.2.2.1 hi0.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi0.2.1 htv hpk rfl ho hea rfl
  obtain ⟨us, hus⟩ : ∃ us, accs ru = some us := by
    cases h : accs ru with
    | none => rw [h] at hlr; exact absurd hlr.symm hacc
    | some us => exact ⟨us, rfl⟩
  have husc : accs c.ty = some us := by rw [← hlr, hus]
  have hus' : wc c.ty = some (nWords us) := by simp [wc, husc]
  obtain ⟨hval, hlen⟩ := ownStoreVal hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvv hlv hsig hus
  have hsigu : sig (close th.σs u) = sig (cl ρ η.wit 0 0 u) :=
    sig_WitL hi0.2.2.2.1 ρ ho (lt_of_guardT htb hi0.2.2.2.2.1)
  have hvR : VRR (fun _ => 0) (CE (CE η)) c.ty (shp c.ty) wsv Rv := by
    obtain ⟨hs, -⟩ := Lay_canon hsub hlv
    have hvu : VRR ρ η u (shp (close th.σs u)) wsv Rv := by rw [← hs]; exact VRR_sub hsat hsub _ _ _ hvrv
    have hvc : VRR (fun _ => 0) (CE η) (cl ρ η.wit 0 0 u) (shp (cl ρ η.wit 0 0 u)) wsv Rv := by
      rw [← shp_of_sig hsigu]
      exact (VRR_close hE.2.1 hE.2.2 ρ u [] 0 ρ (fun _ => 0) (shp (close th.σs u)) wsv Rv (fun k => rfl)
        (fun k hk => absurd hk (Nat.not_lt_zero _))).1 hvu
    rw [(Fd_lay hcty).1]
    exact (Fd_VRR η hcty).2 hvc
  rw [hea] at hev0
  simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hev0
  obtain ⟨-, rfl⟩ := hev0
  simp only [addrOf, hpw, Option.some.injEq] at had
  subst had
  exact wd_frame_whole (A := offs ⟨lab, 0⟩ j) hsto hvR (by rw [hus', hlen]) hle hw hep

theorem storePubLoc_wd_at {p : Prog} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → Nat → List Word → Res → Prop} {Rf : Res}
    {x : String} {rel : Bool} {a v : At} {tok : Option At} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.store rel a v tok) e)
    (hpk : cx.peek a = .ok (.loc .pub u)) (hnw : wordOf (Ty.loc .pub u) = none)
    (hT : Typed p cx th.term) (hi : FInvR ρ η th.σs K cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx)
    {rt : Ty} {pw0 : Word} {ad0 : Address} (hev0 : evalAt th.env a = some (rt, [pw0]))
    (had : addrOf pw0 = some ad0) {μ0 : Mode} {ru0 : Ty} (hc0 : cellOf rt = some (μ0, ru0))
    {us0 : List Acc} (hus0 : accs ru0 = some us0) {j : Nat} (hj : j < nWords us0)
    {n : Nat} {P : Proto} (hw : WordAt (CE η) (offs ad0 j) n P) (hep : P.epoch = false) :
    1 ≤ Rf (.wd n) := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  cases hop with
  | storeWordGive hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordKeep hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordHand hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeOwn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeRgn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeCap hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storePub hp _ hc hwf hu hsub _ hb =>
  obtain ⟨t0, u', tv, c₁, hp, hc, hu, hsub⟩ : ∃ t0 u' tv c₁, cx.peek a = .ok t0 ∧
      cellOf t0 = some (.pub, u') ∧ cx.use v = .ok (tv, c₁) ∧ SubS c₁ tv u' :=
    ⟨_, _, _, _, hp, hc, hu, hsub⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hi0 := hi.1
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length u = true :=
    tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.loc .pub u) = some (.pub, u))
  obtain ⟨rv, wsv, Rv, Rr, hev, hvv, hlv, hvrv, hi1, hle⟩ := useR hu hi hE.2.2
  have hsat : Sat c₁.facts ρ := hi1.1.1
  have hsigu : sig (close th.σs u) = sig (cl ρ η.wit 0 0 u) :=
    sig_WitL hi0.2.2.2.1 ρ ho (lt_of_guardT htb hi0.2.2.2.2.1)
  have hwcu : wc (cl ρ η.wit 0 0 u) ≠ none := by
    rw [← wc_of_sig hsigu]; exact (Lay_canon hsub hlv).2.2.2.1
  obtain ⟨rt, ws, hea, hv, hl⟩ := peek_VR hi0.2.1 hpk
  obtain ⟨ad, c, hws, hsto, hat, hmode, hini⟩ :=
    cell_target (rfl : cellOf (.loc .pub u) = some (.pub, u)) (Fd_noarr fun h => hwcu (by simp [wc, h])) hv
  obtain ⟨pw, rfl, hpw⟩ := map_singleton hws
  have hsk := hl.2.1
  obtain ⟨μr, ru, rfl, -, hsku⟩ : ∃ μr ru, rt = .loc μr ru ∧ skelM μr = skelM .pub ∧
      etok (skel ru) = etok (skel (close th.σs u)) := by
    simp only [close, substTs, skel, etok] at hsk
    obtain ⟨μr, ru, rfl, h1, h2⟩ := eskel_eq_loc hsk
    exact ⟨μr, ru, rfl, h1, h2⟩
  have hsig : sig ru = sig (cl ρ η.wit 0 0 u) := by
    have h1 : sig ru = sig (close th.σs u) := sig_of_eskel hsku
    rw [h1]; exact hsigu
  obtain ⟨us, hus⟩ : ∃ us, accs ru = some us := by
    have : wc ru ≠ none := by rw [wc_of_sig hsig]; exact hwcu
    cases h : accs ru with
    | none => simp [wc, h] at this
    | some us => exact ⟨us, rfl⟩
  obtain ⟨hval, hlen⟩ := ownStoreVal hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvv hlv hsig hus
  have hwU : wc (cl ρ η.wit 0 0 u) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  have hvalR := storeValR hE.2.1 hE.2.2 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvrv hlv hval.2
  rw [hea] at hev0
  simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hev0
  obtain ⟨rfl, rfl⟩ := hev0
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq] at hc0
  obtain ⟨-, rfl⟩ := hc0
  rw [hus] at hus0
  cases hus0
  simp only [addrOf, hpw, Option.some.injEq] at had
  subst had
  exact wd_frame_comp (A := offs ad j) (j := j) hsto hat hvalR.1 (by rw [hwU, hlen]) hle rfl (by simp [offs])
    (by rw [hlen]; exact hj) hw hep


/-! ## `StoreCrZ` and its discharge -/

/-- (T3, epoch half; the `certified_promLoc` variant) An own promise at
a word unit initialised in the owner's real count has a numeric predecessor. -/
def PromPred (E : TEnv) (s : St) : Prop :=
  ∀ t m, t ∈ s.promises → s.mem[t]? = some m → IniWr E m.loc → (∃ n P, WordAt E m.loc n P) →
    ∃ w, PredAt s.mem m.loc t w ∧ ∃ k, w.val = .num k

theorem VRes_wd {E : TEnv} {a : Address} {w : Word} {R : Res} (h : VRes E a w R) (n : Nat) : R (.wd n) = 0 := by
  rcases h with ⟨-, -, ⟨n', P, -, -, rfl⟩ | ⟨-, rfl⟩⟩ | ⟨-, rfl⟩ <;> simp

theorem sum_map_wd {L : List Ts} {f : Ts → Res} {n : Nat} (h : ∀ t ∈ L, f t (.wd n) = 0) :
    Res.sum (L.map f) (.wd n) = 0 := by
  induction L with
  | nil => rfl
  | cons t L ih =>
    simp only [List.map_cons, Res.sum_cons, Res.add_apply]
    rw [h t (List.mem_cons_self ..), ih (fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))]

/-- (U3, fix b; named fact, D2 probing) **`wd` debits are covered.** (1) Each
idle thread's outstanding `wd n` debits are covered by its frame (an outstanding
init holder still holds the region's one word, consumed only by the `bufInit`
fulfilling it). (2) At a plain store to a unit holding an initialised visible
non-epoch word of region `n`, the storer's own promises elsewhere carry no
`wd n` debit (one `mkWord` per region, NID2Probe; at the stored unit itself
`StoreNI` excludes it). -/
def WdCover (c : Cfg) (Eg : GEnv) (Tot : Nat → Res) (db : Nat → Ts → Res) (i : Nat) (th : TTh) : Prop :=
  (∀ n j thj, j ≠ i → c.ths[j]? = some thj → pSum (stOf c.mem c.pairs thj) (db j) (.wd n) ≤ Tot j (.wd n)) ∧
  ∀ x rel a v tok e, th.term = .let_ x (.store rel a v tok) e →
    ∀ (S : AllocLabel → Prop) a' n P, WordAt (CE (Cut Eg i S)) a' n P → IniU (Cut Eg i S) a' n P →
      P.epoch = false →
      (∃ rt pw ad μ ru us j, evalAt th.env a = some (rt, [pw]) ∧ addrOf pw = some ad ∧
        cellOf rt = some (μ, ru) ∧ accs ru = some us ∧ j < nWords us ∧ a' = offs ad j) →
      ∀ t m, t ∈ th.promises → c.mem[t]? = some m → m.loc ≠ a' → db i t (.wd n) = 0

theorem sum_range_le {f g : Nat → Nat} : ∀ {N : Nat}, (∀ j, j < N → f j ≤ g j) →
    ((List.range N).map f).sum ≤ ((List.range N).map g).sum
  | 0, _ => Nat.le_refl _
  | N + 1, h => by
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    exact Nat.add_le_add (sum_range_le fun j hj => h j (by omega)) (h N (by omega))

theorem sum_range_skip {h : Nat → Nat} {i : Nat} : ∀ {N : Nat}, N ≤ i →
    ((List.range N).map fun j => if j = i then 0 else h j).sum = ((List.range N).map h).sum
  | 0, _ => rfl
  | N + 1, hN => by
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    rw [sum_range_skip (by omega)]
    simp only [show N ≠ i by omega, ↓reduceIte]

theorem sum_range_split {h : Nat → Nat} {i : Nat} : ∀ {N : Nat}, i < N →
    ((List.range N).map h).sum = ((List.range N).map fun j => if j = i then 0 else h j).sum + h i
  | N + 1, hi => by
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h' | rfl
    · rw [sum_range_split h']
      simp only [show N ≠ i by omega, ↓reduceIte]
      omega
    · rw [sum_range_skip (Nat.le_refl _)]
      simp only [↓reduceIte]
      omega

theorem le_sum_range {f : Nat → Nat} : ∀ {N i : Nat}, i < N → f i ≤ ((List.range N).map f).sum
  | N + 1, i, h => by
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · exact Nat.le_trans (le_sum_range h) (Nat.le_add_right _ _)
    · exact Nat.le_add_left _ _

theorem sum_range_congr_zero {f : Nat → Nat} : ∀ {N : Nat}, (∀ i, i < N → f i = 0) → ((List.range N).map f).sum = 0
  | 0, _ => rfl
  | N + 1, h => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_range_congr_zero (fun i hi => h i (by omega))]
    simp [h N (by omega)]

/-- (T3, open) No own promise of the storing thread sits at an epoch-counter
unit of a predicted slot (`IniW ∧ ¬ IniWr`, an own planted buffer): the
accounting has no credit for it (db = rg n, cr = 0).  Caveat: false under F2′'s
predicted `ini` (a holder promise at a planted epoch-word slot, fulfilled by the
owner's pub store); needs F2′ §4 holder-credit accounting; a named hypothesis. -/
def NoPredEpoch (E : TEnv) (s : St) : Prop :=
  ∀ t m, t ∈ s.promises → s.mem[t]? = some m → IniW E m.loc → ¬ IniWr E m.loc →
    ∀ n P, WordAt E m.loc n P → P.epoch = true → False

/-- **`StoreCrZ0`** (library; no longer part of `StoreCrZ`): at a reachable thread step, a plain
pub store's units hold no initialised visible non-epoch word unit of the stored cell
carrying a word of a region, so an own promise there has a zero `VRes`; at an
epoch-counter unit, `PromPred` gives the predecessor. -/
theorem storeCrZ0_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat}
    {η : TEnv} {cx : Cx} {Rf Rs : Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (hpred : PromPred (CE η) (stOf c.mem c.pairs th)) (hpe : NoPredEpoch (CE η) (stOf c.mem c.pairs th))
    (hni : StoreNI (CE η) (stOf c.mem c.pairs th) th) (hwc : WdCover c Eg Tot db i th) :
    StoreCrZ0 η cx (stOf c.mem c.pairs th) th := by
  obtain ⟨hCE, -, hE, hT, htv, hFI, hsum⟩ := Y
  intro x rel a v tok e u hterm hpk rt pw ad μ ru us j hev had hc hus hj t m ht hm hloc
  by_cases hz : ∀ w R, VRes (CE η) m.loc w R → R = .zero
  · exact .inl hz
  simp only [Classical.not_forall] at hz
  obtain ⟨w, R, hv, hR⟩ := hz
  rcases hv with ⟨-, hini, ⟨n, P, hw, -, rfl⟩ | ⟨-, rfl⟩⟩ | ⟨-, rfl⟩
  rotate_left
  · exact absurd rfl hR
  · exact absurd rfl hR
  cases hep : P.epoch
  rotate_left
  · by_cases hr : IniWr (CE η) m.loc
    · exact .inr ⟨⟨n, P, hw, hep⟩, hpred t m ht hm hr ⟨n, P, hw⟩⟩
    · exact (hpe t m ht hm hini hr n P hw hep).elim
  exfalso
  -- the frame carries `wd n`
  have hfr : 1 ≤ Rf (.wd n) := by
    rw [hloc] at hw
    rcases hpk with ⟨hpk, hnw⟩ | ⟨hpk, hnw⟩
    · exact storePub_wd_at hterm hpk hnw hT.1 hFI hE htv hev had hw hep
    · exact storePubLoc_wd_at hterm hpk hnw hT.1 hFI hE htv hev had hc hus hj hw hep
  -- memory carries `wd n`
  obtain ⟨S', -, -, -, hP, hSh, -⟩ := X.inv.thr i th X.hth
  have hH := MemHeld_join (fun _ _ hc hp => Cut_cov hc hp) hP hSh
  obtain ⟨cl, hsto, hat, hg⟩ := hw
  have hw' : WordAt (CE (Cut Eg i S')) m.loc n P := by
    refine ⟨cl, ?_, hat, hg⟩
    have : (CE η).sto = cutSto Eg i := by rw [hCE]; rfl
    rw [this] at hsto
    exact hsto
  have hini' : IniU (Cut Eg i S') m.loc n P := by
    intro c2 hc2
    have : (CE η).sto = cutSto Eg i := by rw [hCE]; rfl
    have hs2 : (CE η).sto m.loc.label = some c2 := by rw [this]; exact hc2
    have hini2 := IniAt_of_IniW hs2 (by rw [hsto] at hs2; cases hs2; exact hat) hini
    have hi : (CE η).ini = Eg.ini := by rw [hCE]; rfl
    rw [hi] at hini2
    exact hini2
  have hmem : 1 ≤ (HP i + HS) (.wd n) := wd_held (η := Cut Eg i S') hH hw' hini' hep
  -- the net key bound
  have hk := X.inv.knet (.wd n) trivial
  unfold KeyNet at hk
  have hiN : i < c.ths.size := by
    rcases Nat.lt_or_ge i c.ths.size with h | h
    · exact h
    · have := X.hth; simp [h] at this
  -- the storer's own `wd n` debits are zero: at the stored unit by `StoreNI`, elsewhere by `WdCover`
  have hwE : WordAt (CE η) (offs ad j) n P := hloc ▸ ⟨cl, hsto, hat, hg⟩
  have hnoI := hni x rel a v tok e hterm rt pw ad μ ru us j hev had hc hus hj
  have hz : pSum (stOf c.mem c.pairs th) (db i) (.wd n) = 0 := by
    obtain ⟨_, -, -, -, -, -, hCi⟩ := X.inv.thr i th X.hth
    refine sum_map_wd fun t ht => ?_
    obtain ⟨m', hm', hd', -⟩ := hCi t ht
    by_cases hl : m'.loc = m.loc
    · have hl' : m'.loc = offs ad j := hl.trans hloc
      have hnI := hnoI t m' ht hm' hl' (Or.inl ⟨n, P, hwE⟩)
      rw [← hl'] at hnI
      exact DbRes_wd_nInit hd' hnI n
    · exact hwc.2 x rel a v tok e hterm S' m.loc n P hw' hini' hep
        ⟨rt, pw, ad, μ, ru, us, j, hev, had, hc, hus, hj, hloc⟩ t m' ht hm' hl
  have hdb : ((List.range c.ths.size).map fun j => pSumAt c j (db j) (.wd n)).sum ≤
      ((List.range c.ths.size).map fun j =>
        if j = i then 0 else (Tot j + HP j + pSumAt c j (cr j)) (.wd n)).sum := by
    refine sum_range_le fun j _ => ?_
    by_cases hji : j = i
    · subst hji
      unfold pSumAt
      rw [X.hth]
      simp only
      rw [hz]
      exact Nat.zero_le _
    · simp only [hji, ↓reduceIte, Res.add_apply]
      unfold pSumAt
      cases hj' : c.ths[j]? with
      | none => exact Nat.zero_le _
      | some thj =>
        have := hwc.1 n j thj hji hj'
        simp only
        omega
  have hsplit := sum_range_split (h := fun j => (Tot j + HP j + pSumAt c j (cr j)) (.wd n)) hiN
  simp only [Res.add_apply] at hsplit hdb hmem hk
  have htot : Tot i (.wd n) = Rf (.wd n) + Rs (.wd n) := by rw [← hsum]; rfl
  omega

/-- **`StoreCrZ0`** (library) at every reachable thread step, given the
predecessor fact. -/
theorem dwf0_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
    (hpred : ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
      {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
      {Rf Rs : Res},
      TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
      PromPred (CE η) (stOf c.mem c.pairs th))
    (hpe : ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
      {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
      {Rf Rs : Res},
      TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
      NoPredEpoch (CE η) (stOf c.mem c.pairs th))
    (hni : ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
      {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
      {Rf Rs : Res},
      TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
      StoreNI (CE η) (stOf c.mem c.pairs th) th)
    (hwc : ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
      {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
      {Rf Rs : Res},
      TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
      WdCover c Eg Tot db i th) :
    ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
      {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
      {Rf Rs : Res},
      TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
      StoreCrZ0 η cx (stOf c.mem c.pairs th) th :=
  fun X Y => storeCrZ0_of X Y (hpred X Y) (hpe X Y) (hni X Y) (hwc X Y)

/-- **T3 (`StoreCrZ`, PIN option 3)** at a thread step: `StoreNI` and the leaf pay, which holds
for every environment (`TermPiece.storeLeafPay_of`, read at `CE (CE η).unsee`). -/
theorem storeCrZ_of {η : TEnv} {cx : Cx} {s : St} {th : TTh} (hni : StoreNI (CE η) s th) :
    StoreCrZ η cx s th :=
  ⟨hni, TermPiece.storeLeafPay_of (η := (CE η).unsee)⟩

/-- **T3 restated (`StoreCrZ`)** at every reachable thread step, given `StoreNI` there. -/
theorem dwf_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
    (hni : ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
      {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
      {Rf Rs : Res},
      TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
      StoreNI (CE η) (stOf c.mem c.pairs th) th) :
    ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
      {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
      {Rf Rs : Res},
      TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
      StoreCrZ η cx (stOf c.mem c.pairs th) th :=
  fun X Y => storeCrZ_of (hni X Y)

#print axioms storePub_wd_at
#print axioms storePubLoc_wd_at
#print axioms sum_range_le
#print axioms sum_range_skip
#print axioms sum_range_split
#print axioms storeCrZ0_of
#print axioms dwf0_of
#print axioms storeCrZ_of
#print axioms dwf_of

end TermDwf
